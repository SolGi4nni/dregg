import Reactor.Contract
import Reactor.ServeStep

/-!
# Reactor.DriveCache — the Phase-1 effect-scheduler proof (`drive_cache_refines`)

The serve **effect program** is proven ONCE, in tree: `Reactor.ServeStep.serveStep` /
`resumeStep` decide the whole fabric (whether to cache, which key, what lifetime,
what to serve on a hit vs. a miss) and the cache-arm theorems
(`serveStep_cacheable`, `cacheResume_hit`/`_miss`, `resumeStep_cache_hit`/`_miss`)
fix its meaning; `Reactor.ServeStream.serveTrace_refines` fixes that the sans-IO
streaming serve reproduces the batch spec on any recv split.

The **per-scheduler** obligation — the one thing a concrete effect scheduler (the
io_uring reactor) adds — is a REFINEMENT: the reactor's effect-driving loop feeds the
semantically-correct result bytes into the serve continuation. This file discharges
it for the CACHE effect.

## The seam the driver crosses

`Reactor.Contract` is the copy-once WIRE reactor: its `RingEvent` ingress alphabet
drives the `Proto` connection FSM. Its Phase-0 gap — named in the design — was that
`RingEvent` had no effect-COMPLETION edge: you could submit `connectUpstream` /
`sendUpstream`, but the model could not thread a cache read/write completion back
into the serve. `Reactor.Contract.RingEvent.effectComplete` (added additively) is
that edge. But the effect RESULT does NOT belong to the `Proto` wire FSM — the serve
effect program is a layer ABOVE it — so `effectComplete` is inert at the wire
reactor and is instead consumed HERE, threaded into `resumeStep`.

## What `drive_cache_refines` proves (and does not)

`drive_cache_refines` proves the MODEL — the Contract reactor threading
`effectComplete` CQEs into the proven serve — drives the cache effect faithfully:

* the reactor submits `.cacheLookup key` with the PROVEN key
  (`serveStep_cacheable`);
* an `effectComplete hit` with the store's answer `hit ≠ []` drives to the stored
  bytes REVALIDATED against the request's preconditions (verbatim for a plain GET,
  the proven `304`/`412` for a conditional one), the HIT served WITHOUT re-running
  the handler (`resumeStep_cache_hit`);
* an `effectComplete []` (MISS) followed by the store-ack `effectComplete ack`
  drives to the revalidated deployed fold bytes (the store holds the plain `200`
  of the precondition-stripped fold), having yielded `.cacheStore key …
  cacheLifetime` with the PROVEN key + lifetime in between (`resumeStep_cache_miss`).

The result bytes fed into the continuation are exactly the effect payloads carried by
the ingress events (`resultsOf`), so this is a real refinement — the reactor feeds the
store's actual answer, not an invented one. Composing the miss drive with the sans-IO
streaming refinement (`serveTrace_refines`) is now a NAMED RESIDUAL: the seam's miss
`.done`-s the consolidated conformant serve, which by construction is not the plain
streaming batch spec `serveTrace_refines` reproduces (see the composing-section note
below).

**The realization boundary (honest).** This proves the MODEL. The Rust io_uring
`on_step_reply` cache dispatch (Phase 0) REALIZES this model — it submits the SQEs and
delivers the CQE result bytes to `drorb_serve_resume`. That realization is the SAME
named gap as reactor-model ↔ `uring.rs` (it is NOT proven here; it is the model's
realization boundary). The Rust is not claimed proven.
-/

namespace Reactor.DriveCache

open Proto (Bytes)
open Reactor (RingEvent)
open Reactor.ServeStep
open Reactor.ServeConformant (hasConditional injectDate)

/-- **Extract the effect-result payloads from a reactor ingress-event trace, in
order.** Only the `effectComplete` edges carry an effect result (a cache read/write
answer or an upstream reply); the wire events carry none. This is the list of result
bytes the reactor threads back into the serve continuation. -/
def resultsOf : List RingEvent → List Bytes
  | [] => []
  | .effectComplete r :: es => r :: resultsOf es
  | _ :: es => resultsOf es

/-- **The reactor's effect-driving loop over the serve program.** The reactor submits
the serve's yielded effects and, on each `effectComplete` CQE, feeds the result bytes
into the continuation. Because the continuation replay is pure (`resumeStep` re-runs
`serveStep` and feeds the recorded results, the defunctionalization-by-replay the FFI
uses), the reactor-driven outcome is exactly `resumeStep mask input (resultsOf events)`.
This is the design's `run_uring_interp` at the model altitude — the effect results are
read off the ingress trace, nothing opaque crosses. -/
def driveServe (mask : Nat) (input : Bytes) (events : List RingEvent) : Step :=
  resumeStep mask input (resultsOf events)

/-- A lone lookup completion contributes exactly its result. -/
@[simp] theorem resultsOf_lookup (hit : Bytes) :
    resultsOf [RingEvent.effectComplete hit] = [hit] := rfl

/-- A miss completion (`[]`) then a store-ack completion contribute `[[], ack]`. -/
@[simp] theorem resultsOf_miss_store (ack : Bytes) :
    resultsOf [RingEvent.effectComplete [], RingEvent.effectComplete ack] = [[], ack] := rfl

/-! ## The cache drive, arm by arm (reusing the proven serve program verbatim) -/

/-- **HIT.** The reactor submits `.cacheLookup key`, receives `effectComplete hit`
with the store's non-empty answer, feeds it in, and drives to the stored bytes —
served WITHOUT re-running the handler, REVALIDATED against the request's
preconditions (`resumeStep_cache_hit`: verbatim for a plain GET —
`drive_cache_hit_plain` — the proven `304`/`412` for a conditional one). -/
theorem drive_cache_hit (mask : Nat) (input key hit : Bytes)
    (hapi : isApiPath input = false) (hc : cacheableKey input = some key)
    (hg : gateAdmits input = true) (hne : hit ≠ []) :
    driveServe mask input [RingEvent.effectComplete hit]
      = .done (revalidate (reqOf input) hit) := by
  unfold driveServe
  rw [resultsOf_lookup]
  exact resumeStep_cache_hit mask input key hit hapi hc hg hne

/-- **HIT, precondition-free** — the stored bytes served through the default's
non-conditional accept (`Date`-spliced, `injectDate`). -/
theorem drive_cache_hit_plain (mask : Nat) (input key hit : Bytes)
    (hapi : isApiPath input = false) (hc : cacheableKey input = some key)
    (hg : gateAdmits input = true) (hne : hit ≠ [])
    (hp : hasConditional (reqOf input) = false) :
    driveServe mask input [RingEvent.effectComplete hit] = .done (injectDate hit) := by
  rw [drive_cache_hit mask input key hit hapi hc hg hne, revalidate_plain _ _ hp]

/-- **MISS.** The reactor submits `.cacheLookup key`, receives `effectComplete []`
(the MISS sentinel), runs the deployed fold on the precondition-stripped input
(so the STORE always holds the plain `200`, never a `304`), yields
`.cacheStore key resp cacheLifetime` with the PROVEN key + lifetime, receives the
store-ack `effectComplete ack`, and drives to the revalidated fold bytes
(`resumeStep_cache_miss`). -/
theorem drive_cache_miss (mask : Nat) (input key ack : Bytes)
    (hapi : isApiPath input = false) (hc : cacheableKey input = some key)
    (hg : gateAdmits input = true) :
    driveServe mask input [RingEvent.effectComplete [], RingEvent.effectComplete ack]
      = .done (revalidate (reqOf input)
          (seamInner (cacheFoldInput input))) := by
  unfold driveServe
  rw [resultsOf_miss_store]
  exact resumeStep_cache_miss mask input key ack hapi hc hg

/-- **MISS, precondition-free** — the consolidated fold bytes on `input` served
through the default's non-conditional accept (`Date`-spliced, `injectDate`). -/
theorem drive_cache_miss_plain (mask : Nat) (input key ack : Bytes)
    (hapi : isApiPath input = false) (hc : cacheableKey input = some key)
    (hg : gateAdmits input = true) (hp : hasConditional (reqOf input) = false) :
    driveServe mask input [RingEvent.effectComplete [], RingEvent.effectComplete ack]
      = .done (injectDate (seamInner input)) := by
  unfold driveServe
  rw [resultsOf_miss_store]
  exact resumeStep_cache_miss_plain mask input key ack hapi hc hg hp

/-- **THE PHASE-1 THEOREM — `drive_cache_refines`.** For a gate-admitted cacheable
request, the reactor threading `effectComplete` CQEs into the proven serve drives the
cache effect faithfully, all three obligations at once:

1. it first submits `.cacheLookup key` with the PROVEN key (`serveStep_cacheable`);
2. a lookup whose store HOLDS the key (`effectComplete hit`, `hit ≠ []`) drives to
   the stored bytes REVALIDATED against the request's preconditions — verbatim for
   a plain GET, the proven `304`/`412` for a conditional one — the HIT served
   without the handler;
3. a lookup MISS (`effectComplete []`) then the store-ack (`effectComplete ack`)
   drives to the revalidated deployed fold bytes (the STORE holds the plain `200`
   of the precondition-stripped fold).

The bytes fed into the continuation are the effect payloads carried by the ingress
events (`resultsOf`), and the outputs are the proven cache semantics — so the io_uring
cache dispatch (modelled here) is a faithful interpreter of the proven serve program.
Not vacuous: each conjunct equates the reactor-driven result with a specific,
distinct, semantically-correct value (the proven key; the revalidated stored bytes;
the revalidated fold bytes), reusing the cache-arm theorems verbatim. -/
theorem drive_cache_refines (mask : Nat) (input key : Bytes)
    (hapi : isApiPath input = false) (hc : cacheableKey input = some key)
    (hg : gateAdmits input = true) :
    serveStep mask input = .yield (.cacheLookup key) (cacheResume key input)
    ∧ (∀ hit : Bytes, hit ≠ [] →
        driveServe mask input [RingEvent.effectComplete hit]
          = .done (revalidate (reqOf input) hit))
    ∧ (∀ ack : Bytes,
        driveServe mask input [RingEvent.effectComplete [], RingEvent.effectComplete ack]
          = .done (revalidate (reqOf input)
              (seamInner (cacheFoldInput input)))) :=
  ⟨serveStep_cacheable mask input key hapi hc hg,
   fun hit hne => drive_cache_hit mask input key hit hapi hc hg hne,
   fun ack => drive_cache_miss mask input key ack hapi hc hg⟩

/-! ## Composing the drive refinement with the sans-IO serve refinement

**Named residual (the path-unification consequence).** Before the effect seam was
routed through the consolidated conformant pipeline, the reactor-driven cache miss
`.done`-d the plain fourteen-stage fold (`Reactor.Deploy.servePipelineFull2 input`),
so it composed byte-for-byte with the sans-IO streaming refinement
(`ServeStream.serveTrace_refines`, which reproduces that same batch spec on any recv
split). The seam now `.done`-s the consolidated conformant serve
(`injectDate (seamInner input)` — the full deployed stage registry plus the `Date` /
`Content-Location` / conditional finisher the bare `conformantServe` default carries),
so the reactor miss is deliberately NOT the plain streaming batch: they differ by
exactly the stages the divergence fix added. The sans-IO streaming refinement remains
a property of the batch spec itself (`ServeStream.serveTrace_refines`, unchanged);
re-composing it with the conformant seam requires the SAME consolidation on the
streaming path (`ServeStream`) — a follow-up, tracked here honestly rather than
asserted. -/

/-! ## Runnable checks — `driveServe` / `resultsOf` are genuine (not constant) -/

-- With no completions the reactor has driven nothing: it is still the initial serve
-- decision (so an effect result is genuinely REQUIRED to reach `.done` on a yield).
example (mask : Nat) (input : Bytes) : driveServe mask input [] = serveStep mask input := by
  simp [driveServe, resumeStep, resultsOf]
-- Wire events carry NO effect result — `resultsOf` filters them out, keeping only the
-- `effectComplete` payloads (so the fed results are exactly the completions).
example (hit : Bytes) :
    resultsOf [RingEvent.writeReady, RingEvent.effectComplete hit, RingEvent.sendComplete]
      = [hit] := rfl
-- Two completions thread both payloads, in order.
example (a b : Bytes) :
    resultsOf [RingEvent.effectComplete a, RingEvent.effectComplete b] = [a, b] := rfl
-- The wire reactor is inert on an effect completion (no submission, no state change).
example (cfg : Proto.Config) (s : Proto.State) (r : Bytes) :
    Reactor.step cfg s (.effectComplete r) = (s, []) := rfl

/-! ## Axiom audit -/

#print axioms drive_cache_refines
#print axioms drive_cache_hit
#print axioms drive_cache_hit_plain
#print axioms drive_cache_miss
#print axioms drive_cache_miss_plain

end Reactor.DriveCache
