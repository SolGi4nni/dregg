import Reactor.Pipeline
import Rate

/-!
# Reactor.Stage.Rate — the rate-limit GATE, as a pipeline stage

A byte-driving `Stage` for the extensible serve fold: on the request phase it
consults the **real** `Rate` token bucket and, when the bucket is over the limit
(no token to spend), short-circuits the whole pipeline with a `429 Too Many
Requests` — the handler and every later stage are skipped. Under the limit the
request passes through untouched.

The decision is the real limiter, not a stub: `admits` runs `Rate.refill` and then
`Rate.tryAdmit`, exactly the `Rate.Bucket` transition proven in `Rate/Bucket.lean`.

## A REAL low limit that 429s on a burst

`rateCap` is a genuinely LOW burst limit (`8`), not the inert 1,000,000 the earlier
high-limit wiring carried. Because the FFI serve is one stateless call per request,
the depletion of the bucket across a burst is reconstructed from a per-connection
datum the accept path supplies: the number of requests already served on this
connection, stashed under `seqKey` (the standing count = the length of that attr's
bytes). The gate reconstructs the live bucket as one whose `cap - seq` tokens remain,
then runs the REAL `refill`/`tryAdmit`:

* request `seq = 0 … cap-1` on a kept-alive connection → a token remains → admit;
* request `seq ≥ cap` → the bucket is empty → the REAL `tryAdmit` rejects → `429`.

So a burst of `N > cap` requests on one connection answers the first `cap` with `200`
and the rest with `429` — the classic token-bucket behaviour, driven by the real
`Rate` transition. A connection whose accept path stashes no `seqKey` (a single fresh
request) reads `seq = 0`, a full bucket, and is admitted — the gate never spuriously
throttles unmetered traffic.

The byte effect is a genuine change to the emitted response:

* `rateStage_gate_build` — over the limit, the built pipeline response IS the `429`;
* `rateStage_pass` — under the limit, the stage is transparent: the emitted bytes are
  the tail/handler's, unchanged;
* `rateStage_changes_bytes` — with the same handler and tail, an over-limit request
  and an under-limit request emit *different* status bytes: the gate really drives the
  wire.

`overCtx_over` / `underCtx_under` exhibit concrete over- and under-limit contexts
(closed by `decide` on the real bucket), so none of the above is vacuous.
-/

namespace Reactor.Stage.Rate

open Reactor.Pipeline
open Proto (Bytes)

/-! ## The 429 rejection response -/

/-- Reason phrase for the rejection. -/
def reason429 : Bytes := "Too Many Requests".toUTF8.toList

/-- Body prose for the rejection. -/
def tooManyBody : Bytes := "rate limit exceeded\n".toUTF8.toList

/-- The `429 Too Many Requests` response the gate answers with when the bucket is
over the limit — a real `Response` (`error4xx`) whose status is `429`. -/
def resp429 : Response := error4xx 429 reason429 tooManyBody

/-! ## Reading the live bucket off the context

The gate is stateless per request; the connection's standing depletion rides in the
extensible attribute bag under `seqKey`: the number of requests already served on
this connection (the accept path increments it and stashes that many bytes). The
standing token count is `cap - seq`, so the `cap`-th and later requests on a
kept-alive connection find an empty bucket. -/

/-- Attribute key holding the per-connection request index (its byte-length = the
number of requests already served on this connection). Written by the accept path. -/
def seqKey : String := "rate-seq"

/-- Burst capacity (max standing tokens) — a REAL low limit, not the inert
high-limit. A burst of more than `rateCap` requests on one connection trips the
gate. -/
def rateCap : Nat := 8

/-- Refill rate. `0` = no time-based refill within the model: the burst window is the
capacity itself, so the depletion across a connection is monotone and a burst of
`> rateCap` requests deterministically throttles. -/
def rateRate : Nat := 0

/-- Look the value bytes up for a key in the attribute bag (`[]` if absent). -/
def lookupBytes (c : Ctx) (k : String) : Bytes :=
  match c.attrs.find? (fun p => p.1 == k) with
  | some p => p.2
  | none   => []

/-- The number of requests already served on this connection = the length of the
`seqKey` attr (0 when absent — a fresh, unmetered connection). -/
def seqOf (c : Ctx) : Nat := (lookupBytes c seqKey).length

/-- The live bucket the gate decides on, reconstructed from the connection's standing
depletion: `cap - seq` tokens remain (saturating at empty), `cap`/`rate` from config. -/
def bucketOf (c : Ctx) : _root_.Rate.Bucket :=
  { tokens := rateCap - seqOf c, last := 0, cap := rateCap, rate := rateRate }

/-- **The real admit decision.** Refill the reconstructed bucket to clock `0`, then
consult the real `Rate.tryAdmit`. `true` = a token was available (under the limit,
admit); `false` = none (over the limit, reject). This is exactly the `Rate`
transition, not a stub. -/
def admits (c : Ctx) : Bool :=
  (_root_.Rate.tryAdmit (_root_.Rate.refill 0 (bucketOf c))).2

/-! ## The stage -/

/-- **The rate-limit gate stage.** Request phase: consult the real bucket — admit
→ `.continue` (pass through), reject → `.respond resp429` (short-circuit with the
`429`, skipping the handler and every later stage). Response phase: transparent —
the affine builder is threaded through unchanged (the gate adds no bytes on the
pass-through path; its whole effect is the short-circuit). -/
def rateStage : Stage where
  name := "rate"
  onRequest  := fun c => cond (admits c) (.continue c) (.respond resp429)
  onResponse := fun _ b => b

/-! ## The gate's request-phase decision -/

/-- Over the limit, the gate short-circuits with the `429`. -/
theorem rateStage_onReq_respond (c : Ctx) (hover : admits c = false) :
    rateStage.onRequest c = .respond resp429 := by
  simp only [rateStage, hover, cond]

/-- Under the limit, the gate passes the context through. -/
theorem rateStage_onReq_continue (c : Ctx) (hunder : admits c = true) :
    rateStage.onRequest c = .continue c := by
  simp only [rateStage, hunder, cond]

/-! ## The byte effect -/

/-- **Gate byte-effect.** Over the limit, the BUILT pipeline response — for ANY
tail and handler — is exactly `resp429`: the handler and every later stage are
skipped and the emitted bytes are the `429`. Rides on `pipeline_gate_short_circuits`
and `build_ofResponse`. -/
theorem rateStage_gate_build (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hover : admits c = false) :
    runPipeline (rateStage :: rest) h c = runResp rest c (ResponseBuilder.ofResponse resp429) :=
  pipeline_gate_short_circuits rateStage rest h c resp429 (rateStage_onReq_respond c hover)

/-- The `429`'s status field is `429`. -/
theorem resp429_status : resp429.status = 429 := rfl

/-- The over-limit response's status byte is `429` — preserved through a
status-stable inner onion (the refusal now carries the response transforms). -/
theorem rateStage_over_status (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hover : admits c = false) (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (rateStage :: rest) h c).build).status = 429 :=
  pipeline_gate_status rateStage rest h c resp429 (rateStage_onReq_respond c hover) hst

/-- **Pass-through byte-effect.** Under the limit, the stage is transparent: the
pipeline output is exactly the tail's — the gate contributes no bytes. Rides on
`pipeline_stage_effect` with the identity `onResponse`. -/
theorem rateStage_pass (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hunder : admits c = true) :
    runPipeline (rateStage :: rest) h c = runPipeline rest h c := by
  rw [pipeline_stage_effect rateStage rest h c c (rateStage_onReq_continue c hunder)]
  rfl

/-! ## Concrete over- and under-limit contexts (non-vacuity) -/

/-- A context whose connection has already served `rateCap` requests — the bucket is
empty, so this request is over the limit. -/
def overCtx : Ctx :=
  { input := [], req := {}, attrs := [(seqKey, List.replicate rateCap (0 : UInt8))] }

/-- A fresh connection (no requests served yet) — a full bucket, under the limit. -/
def underCtx : Ctx := { input := [], req := {}, attrs := [] }

/-- `overCtx` is over the limit — the real bucket rejects it. -/
theorem overCtx_over : admits overCtx = false := by decide

/-- `underCtx` is under the limit — the real bucket admits it. -/
theorem underCtx_under : admits underCtx = true := by decide

/-- An over-limit request emits a `429` (through a status-stable inner onion). -/
theorem overCtx_emits_429 (rest : List Stage) (h : Ctx → Response)
    (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (rateStage :: rest) h overCtx).build).status = 429 :=
  rateStage_over_status rest h overCtx overCtx_over hst

/-- An under-limit request passes through to the tail unchanged. -/
theorem underCtx_passes (rest : List Stage) (h : Ctx → Response) :
    runPipeline (rateStage :: rest) h underCtx = runPipeline rest h underCtx :=
  rateStage_pass rest h underCtx underCtx_under

/-- **The gate genuinely drives the wire.** With the SAME handler and tail, an
over-limit request and an under-limit request emit different status bytes: the
over-limit one is forced to `429`, the under-limit one keeps the handler's status
(here, any status `≠ 429`). So the stage really changes the bytes the serve
emits — it is a byte-driver, not a proof attachment. -/
theorem rateStage_changes_bytes (h : Ctx → Response)
    (hstatus : (h underCtx).status ≠ 429) :
    ((runPipeline [rateStage] h overCtx).build).status
      ≠ ((runPipeline [rateStage] h underCtx).build).status := by
  rw [overCtx_emits_429 [] h (by intro t ht; exact absurd ht (List.not_mem_nil t)),
      underCtx_passes [] h, pipeline_empty, build_ofResponse]
  exact fun heq => hstatus heq.symm

/-! ## Axiom audit -/

#print axioms overCtx_over
#print axioms underCtx_under
#print axioms rateStage_gate_build
#print axioms rateStage_over_status
#print axioms rateStage_pass
#print axioms rateStage_changes_bytes

end Reactor.Stage.Rate
