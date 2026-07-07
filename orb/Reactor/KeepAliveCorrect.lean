import Reactor.KeepAlive

/-!
# Reactor.KeepAliveCorrect — RFC 9112 §9.3 ordered-response correctness

RFC 9112 (HTTP/1.1 Message Syntax and Routing) §9.3 (Pipelining) mandates:

> A client that supports persistent connections MAY "pipeline" its requests
> (i.e., send multiple requests without waiting for each response). A server
> **MUST** send its responses to those requests in the same order that the
> requests were received.

This file states that requirement as an **independent specification** and proves
the deployed HTTP/1.1 keep-alive driver **refines** it: on a persistent
connection, `N` pipelined requests produce **exactly `N`** responses, each the
image of the corresponding request under one fixed per-request responder, in the
**same order** the requests arrived — and the connection is kept open iff the
decoded request stream is persistent (no `Connection: close`, no malformed or
rejected request, RFC 9112 §9.3/§9.6/§11.2).

## The specification is written from the RFC, not from the code

`PipelineRun`, `decode`, `pipeline`, and `orderedResponses` below are defined
purely over the message-parsing vocabulary (`Proto.ParseOutcome`) and the header
cap — with **no reference** to the transition function `Proto.step`, the loop
`Proto.h1Loop`, the reactor `Reactor.step`, the `Output`/`RingSubmission`
vocabularies, or the responder `Reactor.respondEach`. `decode` reconstructs the
ordered request stream a conformant server receives; `orderedResponses` is the
§9.3 wire contract: **one response per request, in request order** — a
same-length, same-order map.

## Non-vacuity

The refinement is an equality that a wrong driver would violate:

* `spec_count` / `spec_rejects_dropping` — the specified response list has length
  equal to the request count, so a driver that **dropped** a response cannot
  satisfy it (`[…first…]` has the wrong length).
* `spec_order_sensitive` — whenever two requests have distinct responses,
  reordering them changes the specified list, so a driver that **reordered**
  responses cannot satisfy it.
* `keepalive_closes_iff_deployed` — the close bit is the decoded persistence
  decision, so a driver that **mis-decided close** cannot satisfy it.

The refined object is the deployed driver `Reactor.respondEach`/
`Reactor.driveKeepAlive` over the deployed reactor submissions
`Reactor.Deploy.deploySubs`, and the deployed successor state
`(Reactor.step Reactor.Deploy.deployConfig (active mkPlain) (recvInto 0 input)).1`
— the very submission list and state the deployed reactor path produces.
-/

namespace KeepAliveSpec

open Proto (Bytes Request ParseOutcome Config)

/-! ## The independent specification (RFC 9112 §9.3) -/

/-- The RFC 9112 §9.3 driving outcome for a persistent-connection receive
accumulation: the ordered stream of requests the server received, and whether
the connection remains persistent afterwards. A pure specification object —
it names no part of the implementation. -/
structure PipelineRun where
  /-- The requests received on the connection, in arrival order. -/
  received : List Request
  /-- Whether the connection is kept open (persistent) after this event. -/
  keepOpen : Bool
deriving Repr, DecidableEq

/-- **RFC 9112 §9.3 reference decoder.** Decode a persistent-connection
accumulation `buf` into the ordered request stream and the persistence decision,
using only the request-parsing function `parse`:

* a complete keep-alive request is **received**, and decoding continues on the
  remainder — this is pipelining (§9.3): the next request is read from where the
  previous one ended;
* a complete request carrying `Connection: close` (or HTTP/1.0 without
  keep-alive) is the **last** request received; the connection then **closes**
  (§9.3, §9.6);
* a malformed request (parse error) or a rejected request closes the connection
  and receives no further requests (§9.3, §11.2 — a server must not process a
  request past the point where framing became ambiguous);
* an incomplete or empty accumulation receives no further request this event and
  keeps the connection **open**, awaiting more bytes.

`fuel` bounds the number of requests decodable from `buf` — each consumes at
least one byte in the non-degenerate case, so `buf.length + 1` (used by
`pipeline`) never truncates a real pipeline. -/
def decode (parse : Bytes → ParseOutcome) : Nat → Bytes → PipelineRun
  | 0, _ => { received := [], keepOpen := true }
  | fuel + 1, buf =>
    if buf.isEmpty then { received := [], keepOpen := true }
    else match parse buf with
      | .incomplete => { received := [], keepOpen := true }
      | .error => { received := [], keepOpen := false }
      | .reject _ _ => { received := [], keepOpen := false }
      | .request n req true =>
          let r := decode parse fuel (buf.drop n)
          { received := req :: r.received, keepOpen := r.keepOpen }
      | .request _ req false => { received := [req], keepOpen := false }

/-- **The full §9.3 driving over a plaintext accumulation**, including the
oversized-header guard (RFC 9112 §3, and §11.2 defensively): an accumulation
exceeding the header cap receives no request and closes; otherwise the reference
decoder runs with the length-bounded fuel. -/
def pipeline (parse : Bytes → ParseOutcome) (maxHeaderBytes : Nat) (buf : Bytes) :
    PipelineRun :=
  if buf.length > maxHeaderBytes then { received := [], keepOpen := false }
  else decode parse (buf.length + 1) buf

/-- **The RFC 9112 §9.3 ordered-response contract.** The responses a conformant
server emits are exactly the received requests mapped, pointwise and in order,
through a single per-request responder: response `i` answers request `i`, and
there are exactly as many responses as requests. This is the whole §9.3
obligation ("send responses in the order requests were received"), stated
independently as a `List.map`. -/
def orderedResponses (responder : Request → Bytes) (run : PipelineRun) :
    List Bytes :=
  run.received.map responder

/-! ### The §9.3 contract is a same-length, same-order correspondence -/

/-- **Exactly one response per request.** -/
theorem spec_count (responder : Request → Bytes) (run : PipelineRun) :
    (orderedResponses responder run).length = run.received.length :=
  List.length_map _ _

/-- **Response `i` answers request `i`.** The `i`-th specified response is the
responder applied to the `i`-th received request — order is preserved
positionally. -/
theorem spec_order (responder : Request → Bytes) (run : PipelineRun) (i : Nat) :
    (orderedResponses responder run)[i]? = (run.received[i]?).map responder :=
  List.getElem?_map _ _ _

/-- **The contract rejects a dropped response.** A driver that answered only the
first of two received requests would emit a one-element list, but the §9.3
contract for a two-request stream has length two — so the two can never be
equal. (Non-vacuity: dropping fails.) -/
theorem spec_rejects_dropping (responder : Request → Bytes) (r₁ r₂ : Request) :
    [responder r₁] ≠ orderedResponses responder ⟨[r₁, r₂], true⟩ := by
  intro h
  have := congrArg List.length h
  simp [orderedResponses] at this

/-- **The contract is order-sensitive.** Whenever two received requests have
distinct responses, swapping their arrival order changes the specified response
list — so a driver that reordered responses cannot match the spec. (Non-vacuity:
reordering fails.) -/
theorem spec_order_sensitive (responder : Request → Bytes) (r₁ r₂ : Request)
    (h : responder r₁ ≠ responder r₂) :
    orderedResponses responder ⟨[r₁, r₂], true⟩
      ≠ orderedResponses responder ⟨[r₂, r₁], true⟩ := by
  simp only [orderedResponses, List.map_cons, List.map_nil]
  intro hc
  rw [List.cons.injEq] at hc
  exact h hc.1

end KeepAliveSpec

/-! ## The refinement: the deployed keep-alive driver matches the §9.3 spec -/

namespace KeepAliveSpec

open Proto (Bytes)

/-- `Reactor.dispatchOuts` distributes over concatenation. -/
theorem dispatchOuts_append (a b : List Proto.Output) :
    Reactor.dispatchOuts (a ++ b) = Reactor.dispatchOuts a ++ Reactor.dispatchOuts b := by
  induction a with
  | nil => rfl
  | cons x t ih => cases x <;> simp [Reactor.dispatchOuts, ih]

/-- **The loop's dispatched-request stream is the reference decoder's.** The
requests recovered from the pipelining loop's outputs are exactly the requests
`decode` reconstructs from the same buffer and fuel — proved by induction over
fuel, so a loop that dropped or reordered a dispatch would break it. -/
theorem decode_received_eq (cfg : Proto.Config) (fuel : Nat) (buf : Bytes) :
    Reactor.dispatchOuts (Proto.h1Loop cfg fuel buf).outs
      = (decode cfg.h1Parse fuel buf).received := by
  induction fuel generalizing buf with
  | zero => rfl
  | succ n ih =>
    by_cases hb : buf.isEmpty
    · simp [Proto.h1Loop, decode, hb, Reactor.dispatchOuts]
    · cases hp : cfg.h1Parse buf with
      | incomplete => simp [Proto.h1Loop, decode, hb, hp, Reactor.dispatchOuts]
      | error => simp [Proto.h1Loop, decode, hb, hp, Reactor.dispatchOuts]
      | reject m resp => simp [Proto.h1Loop, decode, hb, hp, Reactor.dispatchOuts]
      | request m req ka =>
        cases ka with
        | true =>
          simp [Proto.h1Loop, decode, hb, hp, Reactor.dispatchOuts, ih (buf.drop m)]
        | false => simp [Proto.h1Loop, decode, hb, hp, Reactor.dispatchOuts]

/-- **The loop's close decision is the reference decoder's persistence decision.**
The loop closes exactly when `decode` reports the connection non-persistent. -/
theorem decode_keepOpen_eq (cfg : Proto.Config) (fuel : Nat) (buf : Bytes) :
    (Proto.h1Loop cfg fuel buf).closing = !(decode cfg.h1Parse fuel buf).keepOpen := by
  induction fuel generalizing buf with
  | zero => rfl
  | succ n ih =>
    by_cases hb : buf.isEmpty
    · simp [Proto.h1Loop, decode, hb]
    · cases hp : cfg.h1Parse buf with
      | incomplete => simp [Proto.h1Loop, decode, hb, hp]
      | error => simp [Proto.h1Loop, decode, hb, hp]
      | reject m resp => simp [Proto.h1Loop, decode, hb, hp]
      | request m req ka =>
        cases ka with
        | true => simp [Proto.h1Loop, decode, hb, hp, ih (buf.drop m)]
        | false => simp [Proto.h1Loop, decode, hb, hp]

/-- `runH1`'s dispatched-request stream is the full `pipeline`'s request stream
(the oversize guard receives nothing, exactly as `pipeline`). -/
theorem runH1_dispatch_eq (cfg : Proto.Config) (frame : Bytes → Proto.ProtoState)
    (buf : Bytes) :
    Reactor.dispatchOuts (Proto.runH1 cfg frame buf []).outs
      = (pipeline cfg.h1Parse cfg.maxHeaderBytes buf).received := by
  unfold pipeline
  by_cases hover : buf.length > cfg.maxHeaderBytes
  · rw [if_pos hover]
    unfold Proto.runH1
    rw [if_pos hover]
    rfl
  · rw [if_neg hover, Proto.runH1_eq_of_not_over cfg frame buf [] hover]
    simp only [List.nil_append]
    exact decode_received_eq cfg (buf.length + 1) buf

/-- `runH1`'s close decision is the full `pipeline`'s persistence decision. -/
theorem runH1_close_eq (cfg : Proto.Config) (frame : Bytes → Proto.ProtoState)
    (buf : Bytes) :
    (Proto.runH1 cfg frame buf []).closeNow
      = !(pipeline cfg.h1Parse cfg.maxHeaderBytes buf).keepOpen := by
  unfold pipeline
  by_cases hover : buf.length > cfg.maxHeaderBytes
  · rw [if_pos hover]
    unfold Proto.runH1
    rw [if_pos hover]
    rfl
  · rw [if_neg hover, Proto.runH1_eq_of_not_over cfg frame buf [] hover]
    exact decode_keepOpen_eq cfg (buf.length + 1) buf

/-- An unblocked `finish` neither adds nor removes dispatch outputs: its emitted
outputs carry exactly the effect's dispatched requests (a trailing `close`, if
any, is not a dispatch). -/
theorem dispatchOuts_finish_unblocked (c : Proto.Conn) (e : Proto.Eff)
    (hb : c.sendBlocked = false) :
    Reactor.dispatchOuts (Proto.finish c e).2 = Reactor.dispatchOuts e.outs := by
  by_cases hcl : e.closeNow
  · have h2 : (Proto.finish c e).2 = e.outs ++ [Proto.Output.close] := by
      unfold Proto.finish; rw [hb]; simp [Proto.gate, hcl]
    rw [h2, dispatchOuts_append]; simp [Reactor.dispatchOuts]
  · have h2 : (Proto.finish c e).2 = e.outs := by
      unfold Proto.finish; rw [hb]; simp [Proto.gate, hcl]
    rw [h2]

/-- The dispatched-request stream of one recv step from a fresh plain connection
is the full `pipeline`'s request stream over the received bytes. -/
theorem step_mkPlain_dispatch_eq (cfg : Proto.Config) (input : Bytes) :
    Reactor.dispatchOuts
        (Proto.step cfg (.active Proto.Conn.mkPlain) (.bytesReceived input)).2
      = (pipeline cfg.h1Parse cfg.maxHeaderBytes input).received := by
  have hstep : Proto.step cfg (.active Proto.Conn.mkPlain) (.bytesReceived input)
      = Proto.finish Proto.Conn.mkPlain
          (Proto.runH1 cfg Proto.ProtoState.plainH1 input []) := rfl
  rw [hstep, dispatchOuts_finish_unblocked Proto.Conn.mkPlain _ rfl,
    runH1_dispatch_eq cfg Proto.ProtoState.plainH1 input]

/-- `finish` closes exactly when the effect requests close. -/
theorem finish_state_closed_iff (c : Proto.Conn) (e : Proto.Eff) :
    (Proto.finish c e).1 = Proto.State.closed ↔ e.closeNow = true := by
  by_cases hcl : e.closeNow <;> simp [Proto.finish, hcl]

/-! ### The deployed refinement -/

open Reactor.Deploy (deployConfig deploySubs)

/-- **`keepalive_ordered_deployed` — the deployed keep-alive driver answers every
pipelined request in RFC 9112 §9.3 order.** The deployed per-request responder
`Reactor.respondEach` over the deployed reactor submissions `deploySubs input`
equals the §9.3 ordered-response contract over the independently-decoded request
stream: one response per received request, in arrival order. Composes the
already-proven deployed dispatch fidelity
(`Reactor.keepalive_all_dispatched_deployed`) with the reference-decoder
refinement (`step_mkPlain_dispatch_eq`). -/
theorem keepalive_ordered_deployed (input : Bytes) :
    Reactor.respondEach (deploySubs input)
      = orderedResponses Reactor.appResponse
          (pipeline deployConfig.h1Parse deployConfig.maxHeaderBytes input) := by
  rw [Reactor.keepalive_all_dispatched_deployed input,
    step_mkPlain_dispatch_eq deployConfig input]
  rfl

/-- **The deployed wire form.** The concatenated response bytes the driver puts
on the wire (`Reactor.driveKeepAlive`) are the §9.3 ordered responses,
flattened — one response per request, in order. -/
theorem keepalive_wire_deployed (input : Bytes) :
    Reactor.driveKeepAlive (deploySubs input)
      = (orderedResponses Reactor.appResponse
          (pipeline deployConfig.h1Parse deployConfig.maxHeaderBytes input)).flatten := by
  unfold Reactor.driveKeepAlive
  rw [keepalive_ordered_deployed]

/-- **`keepalive_closes_iff_deployed` — the deployed connection closes iff the
decoded stream is non-persistent.** The deployed reactor's successor state is
`closed` exactly when the §9.3 reference decoder reports the connection not kept
open (a `Connection: close` / HTTP/1.0 request, a malformed or rejected request,
or an oversized accumulation). A driver that mis-decided close would violate
this. -/
theorem keepalive_closes_iff_deployed (input : Bytes) :
    (Reactor.step deployConfig (.active Proto.Conn.mkPlain)
        (Reactor.RingEvent.recvInto 0 input)).1 = Proto.State.closed
      ↔ (pipeline deployConfig.h1Parse deployConfig.maxHeaderBytes input).keepOpen
          = false := by
  have hr : (Reactor.step deployConfig (.active Proto.Conn.mkPlain)
        (Reactor.RingEvent.recvInto 0 input)).1
      = (Proto.step deployConfig (.active Proto.Conn.mkPlain)
          (.bytesReceived input)).1 := rfl
  have hstep : Proto.step deployConfig (.active Proto.Conn.mkPlain)
        (.bytesReceived input)
      = Proto.finish Proto.Conn.mkPlain
          (Proto.runH1 deployConfig Proto.ProtoState.plainH1 input []) := rfl
  rw [hr, hstep, finish_state_closed_iff,
    runH1_close_eq deployConfig Proto.ProtoState.plainH1 input]
  cases (pipeline deployConfig.h1Parse deployConfig.maxHeaderBytes input).keepOpen <;>
    simp

/-- **`keepalive_correct_deployed` — the deployed HTTP/1.1 keep-alive driver
refines the RFC 9112 §9.3 pipelining contract.** For any received bytes:

* **(a) ordering / count** — the deployed driver's responses are exactly the
  received requests mapped, in order, through one responder (same length, same
  order: `N` requests ↦ `N` responses, response `i` ↦ request `i`); and
* **(b) persistence** — the connection is closed iff the decoded request stream
  is non-persistent.

Both range over the deployed submission list `deploySubs input` and the deployed
successor state — the objects the deployed reactor path produces. -/
theorem keepalive_correct_deployed (input : Bytes) :
    Reactor.respondEach (deploySubs input)
        = orderedResponses Reactor.appResponse
            (pipeline deployConfig.h1Parse deployConfig.maxHeaderBytes input)
    ∧ ((Reactor.step deployConfig (.active Proto.Conn.mkPlain)
          (Reactor.RingEvent.recvInto 0 input)).1 = Proto.State.closed
        ↔ (pipeline deployConfig.h1Parse deployConfig.maxHeaderBytes input).keepOpen
            = false) :=
  ⟨keepalive_ordered_deployed input, keepalive_closes_iff_deployed input⟩

end KeepAliveSpec
