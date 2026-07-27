import Datapath.ByteRefine
import Reactor.Stage.IpFilter

/-!
# Datapath.FlatStage.IpFilter — the `ipfilter` GATE proven flat + byte-identical

The representative header stage (`Datapath.FlatStage`, `securityheaders`) folds a
fixed header set onto the flat `HdrBlock`. `ipfilter` is the OTHER shape the scope
named: a **gate**. It does not transform the header spine — it decides on the
REQUEST (the client address carried in the context) and, on a rejected client,
SHORT-CIRCUITS the whole pipeline with a fixed `403 Forbidden` response, skipping
the handler and every later stage. So the flat obligation is different from a
header fold and matches the gate recipe the exemplar named for `ipfilter`:

* **the DECISION is on the request** — `deployAdmits (ctxAddr c)`, i.e. the REAL
  `IpFilter.permits` over the deployed allow/deny CIDR ruleset; and
* **the RESPONSE is a fixed byte-identical form** — the gate's `403` serialized
  *flat* (`Datapath.ByteRefine.flatSerialize`, the derived flat serializer),
  byte-identical to `Reactor.serialize` of the response the REAL deployed pipeline
  emits for a blocked client.

## What is proven here (equality-transfer, NOT a re-spec)

* `stage_onRequest` — the deployed stage's request-phase effect, read straight off
  `Reactor.Stage.IpFilter.ipfilterStage` (its `onRequest` is exactly a match on
  `deployAdmits (ctxAddr c)`). This grounds the flat gate in the ACTUAL deployed
  decision; we do not re-specify it.
* `flatIpfilterServe` + `flatIpfilterServe_denies_iff_stage_responds` — the flat
  gate runs the SAME real decision and, on a denial, emits the `403` serialized by
  the flat serializer (`Array.push` fold, no cons-spine); its short-circuit fires
  on EXACTLY the contexts the real `ipfilterStage.onRequest` `.respond`s on. The
  decision matches the real stage, proven, not assumed.
* `deployed_blocked_build` — the response the REAL deployed pipeline builds for a
  blocked client is exactly `forbidden403` (read off `ipfilterStage_blocked_emits_403`),
  the response the flat gate serializes. Grounds the byte side in the real fold.
* `flatIpfilter_serialize_refines_deployed` — **THE BYTE-IDENTITY.** The flat gate's
  emitted bytes (`flatSerialize forbidden403`) are byte-identical to
  `Reactor.serialize` of the REAL deployed pipeline's built response for a blocked
  client, via `flatSerialize_refines`. Non-vacuous: `flatSerialize` computes the
  bytes by a genuine flat fold, proven equal to the deployed serializer.
* `flatIpfilterServe_blocked_byte_identical` — the end-to-end: on a blocked client
  the flat gate emits `some` bytes AND those bytes are byte-identical to the real
  deployed serialized output. `flatIpfilterServe_clean_passes` is the pass-through
  arm (an admitted client short-circuits nothing — the handler serves).

The DECISION grain here is the ctx client address (`ctxAddr`, the `attrs`-bag
`client.ip` the accept path stashes), grounded in `deployAdmits`/`IpFilter.permits`
— the honest read of the real stage, not the raw request byte-span. The RESPONSE
grain is the flat serializer, exactly the exemplar's `flatSerialize_refines` seam.
-/

namespace Datapath.FlatStage.IpFilter

open Proto (Bytes)
open Reactor (Response)
open Reactor.Pipeline (Ctx Stage StageStep ResponseBuilder runPipeline runResp)
open Reactor.Stage.IpFilter
  (ipfilterStage deployAdmits ctxAddr forbidden403 blockedCtx cleanCtx
   blockedClient cleanClient deployAdmits_blocked deployAdmits_clean
   ipfilterStage_gates_blocked ipfilterStage_passes_clean
   ipfilterStage_blocked_emits_403 ipfilterStage_clean_emits_handler)
open Datapath.Refinement (flatSerialize flatSerialize_refines)

/-! ## 1. The deployed gate's decision, read off the REAL stage -/

/-- **The deployed `ipfilter` stage's request-phase effect — grounded, not
re-specified.** For any context, the real `ipfilterStage.onRequest` is exactly a
match on the REAL admission decision `deployAdmits (ctxAddr c)`
(`IpFilter.permits` over the deploy CIDR ruleset): admit ⟹ `.continue`, deny ⟹
`.respond forbidden403`. This is the function the flat gate must compute; it is
`rfl` on the deployed stage's definition. -/
theorem stage_onRequest (c : Ctx) :
    ipfilterStage.onRequest c
      = (match deployAdmits (ctxAddr c) with
         | true  => .continue c
         | false => .respond forbidden403) := rfl

/-! ## 2. The flat gate and its decision refinement -/

/-- **The flat `ipfilter` gate.** Runs the REAL admission decision on the context's
client address; on a denial it emits the `403` serialized *flat* by the derived
serializer `flatSerialize` (`Array.push`/`foldAppend`, no per-join cons-spine), and
on an admit it emits `none` (the gate short-circuits nothing — the handler serves).
This is the flat sibling of the deployed gate's `.respond forbidden403 / .continue`:
the decision is the deployed `deployAdmits`, the short-circuit response is
serialized by the flat calculus. -/
def flatIpfilterServe (c : Ctx) : Option ByteArray :=
  match deployAdmits (ctxAddr c) with
  | true  => none
  | false => some (flatSerialize forbidden403)

/-- **The flat gate's decision matches the deployed stage's.** The flat gate emits
its short-circuit bytes on EXACTLY the contexts the real `ipfilterStage.onRequest`
`.respond`s the `403` on — both are `deployAdmits (ctxAddr c) = false`. Proven by
case on the real decision, so the flat gate is the real gate (not a re-spec). -/
theorem flatIpfilterServe_denies_iff_stage_responds (c : Ctx) :
    flatIpfilterServe c = some (flatSerialize forbidden403)
      ↔ ipfilterStage.onRequest c = .respond forbidden403 := by
  rw [stage_onRequest]
  unfold flatIpfilterServe
  cases hd : deployAdmits (ctxAddr c) <;> simp [hd]

/-- The gate fires on the blocked client: it emits the flat-serialized `403`. -/
theorem flatIpfilterServe_blockedCtx :
    flatIpfilterServe blockedCtx = some (flatSerialize forbidden403) := by
  unfold flatIpfilterServe
  rw [show deployAdmits (ctxAddr blockedCtx) = false from by
        rw [show ctxAddr blockedCtx = blockedClient from rfl]; exact deployAdmits_blocked]

/-- The gate passes the clean (loopback) client: it emits nothing (the handler
serves). -/
theorem flatIpfilterServe_cleanCtx :
    flatIpfilterServe cleanCtx = none := by
  unfold flatIpfilterServe
  rw [show deployAdmits (ctxAddr cleanCtx) = true from by
        rw [show ctxAddr cleanCtx = cleanClient from rfl]; exact deployAdmits_clean]

/-! ## 3. Byte-identity: the flat gate's `403` = the deployed pipeline's, byte-for-byte -/

/-- The response the REAL deployed pipeline builds for a blocked client IS
`forbidden403` — the response the flat gate serializes. Read straight off the
deployed stage's `ipfilterStage_blocked_emits_403` (with the empty tail): the
short-circuit seeds `ofResponse forbidden403`, and `build ∘ ofResponse = id`. This
grounds the byte side in the actual deployed fold. -/
theorem deployed_blocked_build (h : Ctx → Response) :
    (runPipeline [ipfilterStage] h blockedCtx).build = forbidden403 := by
  rw [ipfilterStage_blocked_emits_403 [] h, Reactor.Pipeline.runResp_nil,
    Reactor.Pipeline.build_ofResponse]

/-- **THE BYTE-IDENTITY.** The flat gate's emitted bytes for a blocked client
(`flatSerialize forbidden403` — the derived flat serializer) are byte-identical to
`Reactor.serialize` of the response the REAL deployed pipeline builds for that
blocked client. Chains `deployed_blocked_build` (the deployed built response is the
`403`) into the byte-grain serialize equality `flatSerialize_refines`. Non-vacuous:
`flatSerialize` computes the `403` bytes by a genuine flat fold, proven equal to the
deployed `List`-typed serializer. -/
theorem flatIpfilter_serialize_refines_deployed (h : Ctx → Response) :
    Datapath.Refinement.Refines
      (Reactor.serialize ((runPipeline [ipfilterStage] h blockedCtx).build))
      (flatSerialize forbidden403) := by
  rw [deployed_blocked_build h]
  exact flatSerialize_refines forbidden403

/-! ## 4. End-to-end: decision + response together -/

/-- **The gate arm, end-to-end.** On a blocked client the flat gate emits `some`
bytes, and those bytes are byte-identical to `Reactor.serialize` of the REAL
deployed pipeline's built response — the decision (short-circuit) and the response
(byte-identical `403`) proven together. -/
theorem flatIpfilterServe_blocked_byte_identical (h : Ctx → Response) :
    flatIpfilterServe blockedCtx = some (flatSerialize forbidden403)
    ∧ Datapath.Refinement.Refines
        (Reactor.serialize ((runPipeline [ipfilterStage] h blockedCtx).build))
        (flatSerialize forbidden403) :=
  ⟨flatIpfilterServe_blockedCtx, flatIpfilter_serialize_refines_deployed h⟩

/-- **The pass-through arm, end-to-end.** On a clean (admitted) client the flat gate
short-circuits nothing (`none`), and the deployed pipeline emits the HANDLER's own
response — the gate does not perturb an admitted request. -/
theorem flatIpfilterServe_clean_passes (h : Ctx → Response) :
    flatIpfilterServe cleanCtx = none
    ∧ (runPipeline [ipfilterStage] h cleanCtx).build = h cleanCtx :=
  ⟨flatIpfilterServe_cleanCtx, ipfilterStage_clean_emits_handler h⟩

/-! ## Non-vacuity — the flat gate genuinely computes the deployed effect, evaluated -/

-- The flat gate runs the REAL deployed decision: deny on the blocked client,
-- admit on the clean (loopback) client — evaluated by the kernel.
#guard deployAdmits (ctxAddr blockedCtx) == false
#guard deployAdmits (ctxAddr cleanCtx) == true

-- The flat gate short-circuits (some bytes) exactly on the blocked client, and
-- passes (none) on the clean client.
#guard (flatIpfilterServe blockedCtx).isSome
#guard (flatIpfilterServe cleanCtx).isNone

-- The flat-serialized 403 is byte-identical to the deployed serializer's — the
-- byte-identity, evaluated (not just proven).
#guard (flatSerialize forbidden403).data.toList == Reactor.serialize forbidden403

-- Genuine dependence: the flat 403 bytes differ from the same response served with
-- a 200 status — the flat serializer is not a constant.
#guard (flatSerialize forbidden403).data.toList
        != (flatSerialize { forbidden403 with status := 200 }).data.toList

/-! ## Axiom audit -/

#print axioms stage_onRequest
#print axioms flatIpfilterServe_denies_iff_stage_responds
#print axioms flatIpfilterServe_blockedCtx
#print axioms flatIpfilterServe_cleanCtx
#print axioms deployed_blocked_build
#print axioms flatIpfilter_serialize_refines_deployed
#print axioms flatIpfilterServe_blocked_byte_identical
#print axioms flatIpfilterServe_clean_passes

end Datapath.FlatStage.IpFilter
