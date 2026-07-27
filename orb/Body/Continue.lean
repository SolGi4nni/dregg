import Body.Smuggling

/-!
# Expect / 100-continue handling (RFC 9110 §10.1.1)

The `Expect` request header lets a client announce a *behaviour it needs the
server to agree to before it commits work*. RFC 9110 defines exactly one such
expectation — `100-continue` — with this contract (§10.1.1):

* A client that intends to send a (possibly large) message body MAY send
  `Expect: 100-continue` in the request head and then **wait** before
  transmitting the body.
* A server that receives it and is willing to accept the request **MUST**
  respond with an interim `100 (Continue)` response *before* the body is read,
  so the client knows it is safe to proceed. The interim response is emitted on
  the request head alone; the body has not yet been consumed.
* A server that receives an `Expect` field-value it **cannot meet** (any
  expectation other than `100-continue`) responds with `417 (Expectation
  Failed)` and does **not** read the body.
* Absent an `Expect: 100-continue`, no interim `100` is emitted; the body (if
  any) is read and the request handled normally.

This file models the ordering that makes the mechanism correct: for a
`100-continue` request the interim `100` is emitted **strictly before** the body
is consumed, and normal handling (the handler's own final status) follows. The
serve action stream is explicit — `interim`, `consumeBody`, `final` — so the
"before the body is read" clause is a checkable statement about the *order of
events*, not prose.

The header vocabulary (`Header`, `Request`, case-insensitive `nameEq`, `trim`,
`asciiLower`, `splitComma`) is shared with `Body.Smuggling`; `Expect` is a
comma-list header (RFC 9110 §5.6.1) parsed the same way as `Transfer-Encoding`.

Headline theorems:

* `expect_100_then_read` — a request whose `Expect` is exactly `100-continue`,
  served with a body, emits the action stream split at a `100` interim such that
  **no body-consume precedes the interim** (`consumeBody ∉ pre`) and the body
  **is** consumed afterwards (`consumeBody ∈ post`), and the stream ends with the
  handler's final status. This is the "100 before body, then normal handling"
  contract as an ordering fact.
* `expect_417` — an `Expect` the server cannot meet yields exactly a single
  `417` final response, with **no** interim `100` and **no** body-consume: the
  body is never read.
* `no_expect_no_interim` — a request with no (met) `Expect: 100-continue` never
  emits a `100` interim.

Non-vacuity is discharged against concrete requests (`reqContinue`, `reqBogus`,
`reqPlain`) whose classification is decided by the kernel and fed back into the
headline theorems.
-/

namespace Body
namespace Continue

open Body.Smuggling

/-! ## The `Expect` header -/

/-- `expect` as lower-case octets — the header field name (RFC 9110 §10.1.1),
compared after `nameEq` folds the wire name to lower case. -/
def expectName : Bytes := [101, 120, 112, 101, 99, 116]

/-- `100-continue` as lower-case octets — the sole expectation this specification
defines (RFC 9110 §10.1.1). -/
def continueToken : Bytes :=
  [49, 48, 48, 45, 99, 111, 110, 116, 105, 110, 117, 101]

/-- The value of every `Expect` header field, in wire order (the field is
list-valued, so a client MAY split it across multiple lines). -/
def expectValues (req : Request) : List Bytes :=
  req.headers.filterMap (fun h => if nameEq h.name expectName then some h.value else none)

/-- Every expectation token the request carries: split each `Expect` field on
commas (RFC 9110 §5.6.1), trim linear whitespace, and fold to lower case
(expectation names are case-insensitive tokens). -/
def expectTokens (req : Request) : List Bytes :=
  (expectValues req).flatMap (fun v => (splitComma v).map (fun t => (trim t).map asciiLower))

/-- The three possibilities the serve path branches on. -/
inductive ExpectStatus where
  /-- No `Expect` header field at all. -/
  | none
  /-- Every expectation is `100-continue` — the server can meet it. -/
  | continue100
  /-- At least one expectation the server does not implement — 417. -/
  | unmet
deriving Repr, DecidableEq

/-- Classify the `Expect` header of a request. No field → `none`; a field whose
every token is `100-continue` → `continue100`; anything else (an unknown
expectation, or an empty/garbage token) → `unmet`. -/
def expectStatus (req : Request) : ExpectStatus :=
  match expectValues req with
  | [] => .none
  | _ => if (expectTokens req).all (· == continueToken) then .continue100 else .unmet

/-! ## The serve action stream -/

/-- One observable event on the serve path. The interim/final split is what
lets "the `100` is emitted before the body is read" be a statement about order:
`interim` carries the informational (1xx) status; `consumeBody` is the point at
which the request body is actually read; `final` is the single final (≥ 200)
response status. -/
inductive Action where
  /-- An interim (1xx) informational response, e.g. `100 Continue`. -/
  | interim (status : Nat)
  /-- The request body is read / consumed here. -/
  | consumeBody
  /-- The final (≥ 200) response with the given status. -/
  | final (status : Nat)
deriving Repr, DecidableEq

/-- The serve path over a parsed request head, whether a body is present, and the
status the request handler would return.

* `unmet` expectation → a lone `417`; the body is never read (no `consumeBody`).
* `100-continue` → emit the interim `100`, *then* consume the body, *then* the
  handler's final status. The interim is first, so it necessarily precedes the
  body read.
* no relevant `Expect` → consume the body if present, then the final status; no
  interim. -/
def serve (req : Request) (hasBody : Bool) (handlerStatus : Nat) : List Action :=
  match expectStatus req with
  | .unmet => [Action.final 417]
  | .continue100 => [Action.interim 100, Action.consumeBody, Action.final handlerStatus]
  | .none =>
    if hasBody then [Action.consumeBody, Action.final handlerStatus]
    else [Action.final handlerStatus]

/-! ## Headline theorems -/

/-- **`Expect: 100-continue` → interim `100` before the body, then normal
handling.** For a request whose expectation is exactly `100-continue`, served
with a body, the emitted action stream splits at a `100` interim response so
that:

* nothing before the interim consumes the body (`consumeBody ∉ pre`) — the `100`
  is genuinely emitted on the request head, before the body is read;
* the body **is** consumed after the interim (`consumeBody ∈ post`); and
* the stream ends with the handler's own final status (`final handlerStatus`) —
  normal handling resumes once the client is told to proceed.

This is RFC 9110 §10.1.1's ordering requirement stated as a fact about the order
of events. -/
theorem expect_100_then_read (req : Request) (st : Nat)
    (hx : expectStatus req = ExpectStatus.continue100) :
    ∃ pre post,
      serve req true st = pre ++ Action.interim 100 :: post ∧
      Action.consumeBody ∉ pre ∧
      Action.consumeBody ∈ post ∧
      (serve req true st).getLast? = some (Action.final st) := by
  refine ⟨[], [Action.consumeBody, Action.final st], ?_, ?_, ?_, ?_⟩
  · simp [serve, hx]
  · simp
  · simp
  · simp [serve, hx]

/-- **Unmeetable `Expect` → `417`, body never read.** An `Expect` the server
cannot meet yields exactly a single `417 (Expectation Failed)` final response:
no interim `100` is emitted and the body is never consumed — holds regardless of
whether a body was present. -/
theorem expect_417 (req : Request) (hasBody : Bool) (st : Nat)
    (hx : expectStatus req = ExpectStatus.unmet) :
    serve req hasBody st = [Action.final 417] ∧
    Action.consumeBody ∉ serve req hasBody st ∧
    Action.interim 100 ∉ serve req hasBody st := by
  have h : serve req hasBody st = [Action.final 417] := by simp [serve, hx]
  refine ⟨h, ?_, ?_⟩ <;> simp [h]

/-- **No `Expect: 100-continue` → no interim `100`.** A request without a met
`100-continue` expectation never emits a `100` interim response, whatever its
body or handler status. -/
theorem no_expect_no_interim (req : Request) (hasBody : Bool) (st : Nat)
    (hx : expectStatus req = ExpectStatus.none) :
    Action.interim 100 ∉ serve req hasBody st := by
  simp only [serve, hx]
  cases hasBody <;> simp

/-! ## Non-vacuity: concrete requests witness each hypothesis -/

/-- A header with a wire (mixed-case) name and a value, exercising the
case-insensitive `nameEq` match. -/
private def hdr (name value : Bytes) : Header := { name := name, value := value }

/-- `Expect: 100-continue` (wire name capitalised to exercise case folding). -/
def reqContinue : Request :=
  { headers := [hdr [69, 120, 112, 101, 99, 116] continueToken] }

/-- `Expect: bad` — an expectation the server does not implement. -/
def reqBogus : Request :=
  { headers := [hdr [69, 120, 112, 101, 99, 116] [98, 97, 100]] }

/-- A body-bearing request with no `Expect` header (`Content-Length: 5`). -/
def reqPlain : Request :=
  { headers := [hdr [67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103, 116, 104] [53]] }

/-- Non-vacuity: a real `100-continue` request classifies as `continue100`. -/
theorem reqContinue_status : expectStatus reqContinue = ExpectStatus.continue100 := by decide

/-- Non-vacuity: a `bad` expectation classifies as `unmet`. -/
theorem reqBogus_status : expectStatus reqBogus = ExpectStatus.unmet := by decide

/-- Non-vacuity: a plain body request classifies as `none`. -/
theorem reqPlain_status : expectStatus reqPlain = ExpectStatus.none := by decide

/-- The headline `expect_100_then_read` instantiated on a concrete request: the
served stream really does emit `100` before the body and end with the handler's
`200`. Witnesses the hypothesis of `expect_100_then_read` is inhabited. -/
theorem expect_100_then_read_witness :
    ∃ pre post,
      serve reqContinue true 200 = pre ++ Action.interim 100 :: post ∧
      Action.consumeBody ∉ pre ∧
      Action.consumeBody ∈ post ∧
      (serve reqContinue true 200).getLast? = some (Action.final 200) :=
  expect_100_then_read reqContinue 200 reqContinue_status

/-- The concrete `100-continue` serve stream, fully evaluated: `100`, then the
body, then the final `200` — the interim strictly precedes the body read. -/
theorem serve_reqContinue :
    serve reqContinue true 200
      = [Action.interim 100, Action.consumeBody, Action.final 200] := by decide

/-- The headline `expect_417` instantiated: a `bad` expectation yields a lone
`417` with no interim and no body read. -/
theorem expect_417_witness :
    serve reqBogus false 200 = [Action.final 417] ∧
    Action.consumeBody ∉ serve reqBogus false 200 ∧
    Action.interim 100 ∉ serve reqBogus false 200 :=
  expect_417 reqBogus false 200 reqBogus_status

/-- The headline `no_expect_no_interim` instantiated: a plain body request emits
no interim `100`. -/
theorem no_interim_witness : Action.interim 100 ∉ serve reqPlain true 200 :=
  no_expect_no_interim reqPlain true 200 reqPlain_status

end Continue
end Body
