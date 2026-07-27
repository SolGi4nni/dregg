import Reactor.Pipeline

/-!
# Reactor.Stage.Slowloris — the slow-header-arrival defense GATE

A byte-driving `Stage` for the extensible serve fold: on the request phase it
checks how long the client has taken to deliver its request headers and, when that
span has reached the configured header timeout, short-circuits the whole pipeline
with a `408 Request Timeout` — the handler and every later stage are skipped. A
request whose headers arrived in time passes through untouched.

This is the classic slowloris defense: a client that opens a connection and then
dribbles header bytes far below line rate (holding the worker) is dropped once its
header phase overruns the timeout, rather than being allowed to pin the slot.

## The decision core — a real bounded timeout test

`expired timeout started now` is the exact expiry rule: with the protection enabled
(`timeout ≠ 0`) a connection is expired iff the elapsed header span `now - started`
has reached `timeout` (i.e. `started + timeout ≤ now`). A `timeout` of `0` disables
the protection — nothing ever expires. This is the total form of the reference
`check_expired` (`now.duration_since(started) ≥ timeout`, gated on a non-zero
timeout).

Because the sans-IO serve is one stateless call per request, the connection's
header-phase start clock and the current clock ride in the attribute bag under
`startedKey` / `nowKey` (their byte-lengths are the clock readings the accept path
supplies). A connection whose start is far enough in the past reconstructs an
elapsed span at or over the timeout, and the REAL `expired` decision drops it.

The effect is a genuine change to the emitted bytes:

* `slowStage_gate_build` — expired, the built pipeline response IS the `408`;
* `slowStage_pass` — in time, the stage is transparent (the handler's bytes);
* `slowStage_changes_bytes` — same handler, an expired and a fresh connection emit
  *different* status bytes: the gate really drives the wire.

`expired` truth-table lemmas (`expired_disabled`, `expired_in_time`,
`expired_at_timeout`, `expired_over`) and the concrete contexts (`slowCtx_expired`,
`freshCtx_ok`, closed by `decide`) keep all of this non-vacuous.
-/

namespace Reactor.Stage.Slowloris

open Reactor.Pipeline
open Proto (Bytes)

/-! ## The 408 rejection response -/

/-- Reason phrase for the rejection. -/
def reason408 : Bytes := "Request Timeout".toUTF8.toList

/-- Body prose for the rejection. -/
def slowBody : Bytes := "request header timeout\n".toUTF8.toList

/-- The `408 Request Timeout` response the gate answers with when the header phase
overruns the timeout — a real `Response` whose status is `408`. -/
def resp408 : Response := error4xx 408 reason408 slowBody

/-! ## The decision core -/

/-- The configured header timeout in clock units. A REAL low bound (`8`) so a
connection that dribbles its headers past the window trips the gate; `0` disables
slowloris protection entirely. -/
def headerTimeout : Nat := 8

/-- **The expiry decision.** With protection enabled (`timeout ≠ 0`), a connection
whose header phase began at `started` is expired at clock `now` iff the elapsed span
has reached the timeout — `started + timeout ≤ now`. A `0` timeout never expires.
Total; matches the reference `now - started ≥ timeout` guarded on a non-zero timeout. -/
def expired (timeout started now : Nat) : Bool :=
  timeout != 0 && started + timeout ≤ now

/-! ### Truth table (non-vacuity of the decision) -/

/-- A disabled timeout (`0`) never expires — the protection-off path. -/
theorem expired_disabled (started now : Nat) : expired 0 started now = false := by
  simp [expired]

/-- Header phase still within the window ⇒ not expired. -/
theorem expired_in_time {timeout started now : Nat}
    (h : now < started + timeout) : expired timeout started now = false := by
  simp only [expired, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le]
  exact Or.inr h

/-- Exactly at the timeout boundary (with protection on) ⇒ expired. -/
theorem expired_at_timeout {timeout started : Nat} (hpos : timeout ≠ 0) :
    expired timeout started (started + timeout) = true := by
  simp only [expired, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
  exact ⟨hpos, Nat.le_refl _⟩

/-- Past the timeout (with protection on) ⇒ expired. -/
theorem expired_over {timeout started now : Nat} (hpos : timeout ≠ 0)
    (h : started + timeout ≤ now) : expired timeout started now = true := by
  simp only [expired, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
  exact ⟨hpos, h⟩

/-! ## Reading the connection clocks off the context -/

/-- Attribute key holding the header-phase start clock (its byte-length = the start
reading the accept path recorded when the first header byte arrived). -/
def startedKey : String := "hdr-started"

/-- Attribute key holding the current clock (its byte-length = the current reading
the accept path supplies at gate time). -/
def nowKey : String := "hdr-now"

/-- Look the value bytes up for a key in the attribute bag (`[]` if absent). -/
def lookupBytes (c : Ctx) (k : String) : Bytes :=
  match c.attrs.find? (fun p => p.1 == k) with
  | some p => p.2
  | none   => []

/-- The header-phase start clock reconstructed from the attribute bag. -/
def startedOf (c : Ctx) : Nat := (lookupBytes c startedKey).length

/-- The current clock reconstructed from the attribute bag. -/
def nowOf (c : Ctx) : Nat := (lookupBytes c nowKey).length

/-- **The real gate decision on the context.** Drop iff the reconstructed header
span has reached the configured timeout. -/
def ctxExpired (c : Ctx) : Bool := expired headerTimeout (startedOf c) (nowOf c)

/-! ## The stage -/

/-- **The slowloris gate stage.** Request phase: consult the real expiry rule on the
connection's header clocks — in time → `.continue`, expired → `.respond resp408`
(short-circuit with the `408`, skipping the handler and every later stage). Response
phase: transparent — a pure gate. -/
def slowStage : Stage where
  name := "slowloris"
  onRequest  := fun c => cond (ctxExpired c) (.respond resp408) (.continue c)
  onResponse := fun _ b => b

/-! ## The gate's request-phase decision -/

/-- Expired, the gate short-circuits with the `408`. -/
theorem slowStage_onReq_respond (c : Ctx) (hexp : ctxExpired c = true) :
    slowStage.onRequest c = .respond resp408 := by
  simp only [slowStage, hexp, cond]

/-- In time, the gate passes the context through. -/
theorem slowStage_onReq_continue (c : Ctx) (hok : ctxExpired c = false) :
    slowStage.onRequest c = .continue c := by
  simp only [slowStage, hok, cond]

/-! ## The byte effect -/

/-- **Gate byte-effect.** Expired, the BUILT pipeline response — for ANY tail and
handler — is the `408`: the handler and every later stage are skipped. -/
theorem slowStage_gate_build (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hexp : ctxExpired c = true) :
    runPipeline (slowStage :: rest) h c = runResp rest c (ResponseBuilder.ofResponse resp408) :=
  pipeline_gate_short_circuits slowStage rest h c resp408 (slowStage_onReq_respond c hexp)

/-- The `408`'s status field is `408`. -/
theorem resp408_status : resp408.status = 408 := rfl

/-- The expired response's status byte is `408` — preserved through a status-stable
inner onion. -/
theorem slowStage_expired_status (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hexp : ctxExpired c = true) (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (slowStage :: rest) h c).build).status = 408 :=
  pipeline_gate_status slowStage rest h c resp408 (slowStage_onReq_respond c hexp) hst

/-- **Pass-through byte-effect.** In time, the stage is transparent: the pipeline
output is exactly the tail's. -/
theorem slowStage_pass (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hok : ctxExpired c = false) :
    runPipeline (slowStage :: rest) h c = runPipeline rest h c := by
  rw [pipeline_stage_effect slowStage rest h c c (slowStage_onReq_continue c hok)]
  rfl

/-! ## Concrete expired / fresh contexts (non-vacuity) -/

/-- A slow connection: header phase started at clock `0`, current clock is
`headerTimeout` — the span has reached the timeout, so it is dropped. -/
def slowCtx : Ctx :=
  { input := [], req := {}, attrs := [(nowKey, List.replicate headerTimeout (0 : UInt8))] }

/-- A fresh connection: no elapsed span (start = now = 0) — well within the window. -/
def freshCtx : Ctx := { input := [], req := {}, attrs := [] }

/-- `slowCtx` is expired — the real rule drops it. -/
theorem slowCtx_expired : ctxExpired slowCtx = true := by decide

/-- `freshCtx` is in time — the real rule admits it. -/
theorem freshCtx_ok : ctxExpired freshCtx = false := by decide

/-- A slow connection emits a `408` (through a status-stable inner onion). -/
theorem slowCtx_emits_408 (rest : List Stage) (h : Ctx → Response)
    (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (slowStage :: rest) h slowCtx).build).status = 408 :=
  slowStage_expired_status rest h slowCtx slowCtx_expired hst

/-- A fresh connection passes through to the tail unchanged. -/
theorem freshCtx_passes (rest : List Stage) (h : Ctx → Response) :
    runPipeline (slowStage :: rest) h freshCtx = runPipeline rest h freshCtx :=
  slowStage_pass rest h freshCtx freshCtx_ok

/-- **The gate genuinely drives the wire.** With the SAME handler and tail, a slow
connection and a fresh connection emit different status bytes: the slow one is forced
to `408`, the fresh one keeps the handler's status. A real byte-driver. -/
theorem slowStage_changes_bytes (h : Ctx → Response)
    (hstatus : (h freshCtx).status ≠ 408) :
    ((runPipeline [slowStage] h slowCtx).build).status
      ≠ ((runPipeline [slowStage] h freshCtx).build).status := by
  rw [slowCtx_emits_408 [] h (by intro t ht; exact absurd ht (List.not_mem_nil)),
      freshCtx_passes [] h, pipeline_empty, build_ofResponse]
  exact fun heq => hstatus heq.symm

/-! ## The monotone header deadline (DEEPEN)

`expired_at_timeout` / `expired_over` fix expiry at points; this closes the gap that
the deadline is MONOTONE in the clock — the property that actually defends the slot.
Once a connection's header phase has overrun the deadline it can never later be found
in-time, so a client that keeps dribbling its headers only stays dropped: no clock
advance can rescue an already-expired connection. This is the drip-timing guarantee
the gate rests on. -/

/-- **Monotone deadline.** Once expired, a connection stays expired at every later
clock reading: expiry is monotone in `now`. A slow client never "un-expires" — for
ALL later clocks `now' ≥ now`, not a sampled pair. -/
theorem expired_mono {timeout started now now' : Nat} (h : now ≤ now')
    (hexp : expired timeout started now = true) :
    expired timeout started now' = true := by
  simp only [expired, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hexp ⊢
  exact ⟨hexp.1, Nat.le_trans hexp.2 h⟩

/-- The context-level deadline is monotone too: a connection expired at clock
`nowOf c` is expired at any later reading, under the deployed `headerTimeout`. -/
theorem ctxExpired_mono {c : Ctx} {now' : Nat} (h : nowOf c ≤ now')
    (hexp : ctxExpired c = true) :
    expired headerTimeout (startedOf c) now' = true :=
  expired_mono h hexp

/-! ## Axiom audit -/

#print axioms expired_disabled
#print axioms expired_at_timeout
#print axioms expired_over
#print axioms expired_mono
#print axioms ctxExpired_mono
#print axioms slowCtx_expired
#print axioms freshCtx_ok
#print axioms slowStage_gate_build
#print axioms slowStage_expired_status
#print axioms slowStage_pass
#print axioms slowStage_changes_bytes

end Reactor.Stage.Slowloris
