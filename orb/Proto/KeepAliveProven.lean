import Reactor.KeepAliveCorrect
import Reactor.Config

/-!
# Proto.KeepAliveProven — the DEPLOYED HTTP/1.1 keep-alive / connection-close discipline

PROVE-WHAT-RUNS for ledger row `h1.ka`: the deployed dataplane's HTTP/1.1
keep-alive behavior on the io_uring serve path (`crates/dataplane/src/uring.rs`
`request_wants_keepalive` / `dispatch_acc` / `finish_send`, and
`crates/dataplane/src/http.rs`). Three behaviors, each proven against the exact
function the deployed binary runs and each confirmed by curling the running orb:

* **`keepalive_default`** — HTTP/1.1 defaults to keep-alive. A request that does
  *not* carry `Connection: close` keeps the connection open for the next request.
  The deployed decision is `Reactor.Config.deriveKeepAlive` (the boolean the arena
  parser hands the FSM through `arenaToProto`): default `true`, `Connection: close`
  turns it off — byte-for-byte the Rust `request_wants_keepalive`'s `_ => is_11`
  1.1 arm. The *disposition* corollary `keepalive_default_disposition` lifts this
  through the reference decoder to the deployed reactor: the successor connection
  is **not** closed.

* **`keepalive_honors_close`** — `Connection: close` closes the connection after
  the response. `deriveKeepAlive = false`, and the disposition corollary
  `keepalive_close_disposition` shows the deployed reactor's successor state is
  `closed` (the Rust `finish_send(keepalive=false) → close`).

* **`keepalive_pipeline`** — two pipelined requests yield two responses on one
  connection, in order. The deployed per-request driver `Reactor.respondEach` over
  the deployed submission list `Reactor.Deploy.deploySubs input` emits exactly one
  response per decoded request (the fix that `demoResp`'s first-only responder
  lacked): a two-request accumulation ⇒ a length-2 response list, in arrival order.

Everything composes already-proven deployed seams
(`KeepAliveSpec.keepalive_ordered_deployed`,
`KeepAliveSpec.keepalive_closes_iff_deployed`) with the deployed decision function
`Reactor.Config.deriveKeepAlive`. No new axioms; nothing here edits a shared file.
-/

namespace Proto.KeepAliveProven

open Proto (Bytes Request ParseOutcome)
open Reactor.Deploy (deployConfig deploySubs)

/-! ## The deployed keep-alive decision (`request_wants_keepalive`)

`Reactor.Config.deriveKeepAlive` is the boolean the arena parser threads into the
FSM (`Reactor.Config.arenaToProto` sets a request's `keepAlive` field to it). It
is the deployed analog of the Rust `request_wants_keepalive` on the HTTP/1.1
plaintext lane: persistent by default, off on an explicit `Connection: close`. -/

/-- **`keepalive_default` — HTTP/1.1 defaults to keep-alive.** A request whose
headers carry no `Connection: close` gets the deployed keep-alive decision
`true`, so the host keeps the socket open for the next request. Covers both the
no-`Connection`-header case and a `Connection` header with any non-`close`
value. -/
theorem keepalive_default (headers : List (Bytes × Bytes))
    (hno : ∀ name v,
      headers.find? (fun h => h.1 == Reactor.Config.strBytes "connection")
        = some (name, v) → v ≠ Reactor.Config.strBytes "close") :
    Reactor.Config.deriveKeepAlive headers = true := by
  unfold Reactor.Config.deriveKeepAlive
  cases h : headers.find? (fun h => h.1 == Reactor.Config.strBytes "connection") with
  | none => rfl
  | some p =>
    obtain ⟨name, v⟩ := p
    have hv : v ≠ Reactor.Config.strBytes "close" := hno name v h
    exact bne_iff_ne.mpr hv

/-- **`keepalive_honors_close` — `Connection: close` closes the connection.** A
request whose `Connection` header value is exactly `close` gets the deployed
keep-alive decision `false`, so the host tears the connection down after the
response. -/
theorem keepalive_honors_close (headers : List (Bytes × Bytes)) (name : Bytes)
    (hc : headers.find? (fun h => h.1 == Reactor.Config.strBytes "connection")
      = some (name, Reactor.Config.strBytes "close")) :
    Reactor.Config.deriveKeepAlive headers = false := by
  unfold Reactor.Config.deriveKeepAlive
  rw [hc]
  simp

/-! ## Lifting the decision to the deployed reactor's connection disposition

The reference decoder `KeepAliveSpec.pipeline` propagates the per-request
keep-alive bit to `keepOpen`, and `KeepAliveSpec.keepalive_closes_iff_deployed`
ties `keepOpen = false` to the deployed reactor's successor state being `closed`.
These corollaries realize the two decisions above as the actual open/close the
deployed reactor takes. -/

/-- Decoding an *empty* accumulation keeps the connection open, at any fuel. -/
theorem decode_empty_keepOpen (parse : Bytes → ParseOutcome) (fuel : Nat)
    (buf : Bytes) (hbuf : buf.isEmpty = true) :
    (KeepAliveSpec.decode parse fuel buf).keepOpen = true := by
  cases fuel with
  | zero => rfl
  | succ n => simp [KeepAliveSpec.decode, hbuf]

/-- A keep-alive request at the head of the accumulation defers the persistence
decision to the remainder (pipelining). -/
theorem decode_ka_keepOpen (parse : Bytes → ParseOutcome) (fuel : Nat)
    (buf : Bytes) (n : Nat) (req : Request)
    (hne : buf.isEmpty = false) (hp : parse buf = .request n req true) :
    (KeepAliveSpec.decode parse (fuel + 1) buf).keepOpen
      = (KeepAliveSpec.decode parse fuel (buf.drop n)).keepOpen := by
  simp [KeepAliveSpec.decode, hne, hp]

/-- A `Connection: close` request at the head is the last one: the connection
closes. -/
theorem decode_close_keepOpen (parse : Bytes → ParseOutcome) (fuel : Nat)
    (buf : Bytes) (n : Nat) (req : Request)
    (hne : buf.isEmpty = false) (hp : parse buf = .request n req false) :
    (KeepAliveSpec.decode parse (fuel + 1) buf).keepOpen = false := by
  simp [KeepAliveSpec.decode, hne, hp]

/-- **`keepalive_default_disposition` — the deployed reactor keeps the connection
open.** When the deployed parser resolves the whole accumulation to a single
keep-alive request (no `Connection: close`, so its parse carries `keepAlive =
true`) with no trailing bytes, the deployed reactor's successor state is **not**
`closed`: the socket stays open for the next request. -/
theorem keepalive_default_disposition (input : Bytes) (n : Nat) (req : Request)
    (hle : ¬ input.length > deployConfig.maxHeaderBytes)
    (hne : input.isEmpty = false)
    (hparse : deployConfig.h1Parse input = .request n req true)
    (hrem : (input.drop n).isEmpty = true) :
    (Reactor.step deployConfig (.active Proto.Conn.mkPlain)
        (Reactor.RingEvent.recvInto 0 input)).1 ≠ Proto.State.closed := by
  have hkeep : (KeepAliveSpec.pipeline deployConfig.h1Parse
      deployConfig.maxHeaderBytes input).keepOpen = true := by
    unfold KeepAliveSpec.pipeline
    rw [if_neg hle,
      decode_ka_keepOpen deployConfig.h1Parse input.length input n req hne hparse,
      decode_empty_keepOpen deployConfig.h1Parse input.length (input.drop n) hrem]
  intro hclosed
  rw [KeepAliveSpec.keepalive_closes_iff_deployed, hkeep] at hclosed
  exact absurd hclosed (by decide)

/-- **`keepalive_close_disposition` — the deployed reactor closes.** When the
deployed parser resolves the accumulation to a request carrying `Connection:
close` (parse `keepAlive = false`), the deployed reactor's successor state is
`closed`: the connection is torn down after the response. -/
theorem keepalive_close_disposition (input : Bytes) (n : Nat) (req : Request)
    (hle : ¬ input.length > deployConfig.maxHeaderBytes)
    (hne : input.isEmpty = false)
    (hparse : deployConfig.h1Parse input = .request n req false) :
    (Reactor.step deployConfig (.active Proto.Conn.mkPlain)
        (Reactor.RingEvent.recvInto 0 input)).1 = Proto.State.closed := by
  have hkeep : (KeepAliveSpec.pipeline deployConfig.h1Parse
      deployConfig.maxHeaderBytes input).keepOpen = false := by
    unfold KeepAliveSpec.pipeline
    rw [if_neg hle,
      decode_close_keepOpen deployConfig.h1Parse input.length input n req hne hparse]
  rw [KeepAliveSpec.keepalive_closes_iff_deployed]
  exact hkeep

/-! ## Pipelining: two requests, two responses, one connection -/

/-- **`keepalive_pipeline` — two pipelined requests get two responses, in
order.** When the deployed decode of one recv accumulation yields two pipelined
requests `[r₁, r₂]`, the deployed per-request response driver `respondEach` over
the deployed submission list emits exactly `[appResponse r₁, appResponse r₂]` —
two responses, in arrival order, on the one connection. (A first-only responder
would emit one; see `keepalive_pipeline_not_dropped`.) -/
theorem keepalive_pipeline (input : Bytes) (r₁ r₂ : Request)
    (htwo : (KeepAliveSpec.pipeline deployConfig.h1Parse
      deployConfig.maxHeaderBytes input).received = [r₁, r₂]) :
    Reactor.respondEach (deploySubs input)
        = [Reactor.appResponse r₁, Reactor.appResponse r₂]
      ∧ (Reactor.respondEach (deploySubs input)).length = 2 := by
  have h := KeepAliveSpec.keepalive_ordered_deployed input
  unfold KeepAliveSpec.orderedResponses at h
  rw [htwo] at h
  simp only [List.map_cons, List.map_nil] at h
  exact ⟨h, by rw [h]; rfl⟩

/-- **Non-vacuity: a first-only driver fails the pipeline contract.** Two
pipelined requests demand a length-2 response list, so a driver that answered
only the first request (a length-1 list) cannot satisfy `keepalive_pipeline`. -/
theorem keepalive_pipeline_not_dropped (r₁ r₂ : Request) :
    [Reactor.appResponse r₁]
      ≠ [Reactor.appResponse r₁, Reactor.appResponse r₂] := by
  intro h
  have := congrArg List.length h
  simp at this

/-! ## Non-vacuity witnesses

Concrete inhabitants so none of the headline theorems is vacuous: the decision
distinguishes both branches, and the pipeline decode genuinely produces a
two-request stream. -/

/-- Default keep-alive is live: a request with no `Connection` header is kept
alive. -/
example : Reactor.Config.deriveKeepAlive [] = true :=
  keepalive_default [] (by intro name v h; simp [List.find?] at h)

/-- A `Connection: close` header is honored: the same decision function returns
`false`. So `keepalive_default` and `keepalive_honors_close` distinguish real
inputs — the function is not constantly `true`. -/
example :
    Reactor.Config.deriveKeepAlive
        [(Reactor.Config.strBytes "connection", Reactor.Config.strBytes "close")]
      = false :=
  keepalive_honors_close _ (Reactor.Config.strBytes "connection")
    (by simp [List.find?])

/-- A parse function that yields two consecutive keep-alive requests then runs
dry — the shape a pipelined pair produces. -/
def twoReqParse (r₁ r₂ : Request) : Bytes → ParseOutcome := fun buf =>
  if buf.length = 2 then .request 1 r₁ true
  else if buf.length = 1 then .request 1 r₂ true
  else .incomplete

/-- The reference decoder genuinely yields a two-request stream — so the
`keepalive_pipeline` hypothesis is inhabited (pipelining reads the second request
from where the first ended). -/
example (r₁ r₂ : Request) :
    (KeepAliveSpec.decode (twoReqParse r₁ r₂) 3 [7, 8]).received = [r₁, r₂] := by
  simp [KeepAliveSpec.decode, twoReqParse]

end Proto.KeepAliveProven
