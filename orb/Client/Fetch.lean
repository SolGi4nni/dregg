import Client.H1
import Client.Redirect
import Client.Session
import Client.CookieExpiry
import Client.Tls

/-!
# `Client.Fetch` — the composed verified HTTP client transaction

The proven client PARTS live in separate modules, each with its own vocabulary:

* `Client.H1` / `Client.H2` / `Client.H3` — the per-protocol request/response
  transaction (`transaction_faithful` / `client_server_agreement` /
  `request_faithful`), ALPN-selected;
* `Client.Redirect` — the RFC 9110 §15.4 redirect-follow decision
  (`redirect_follows_location`, `redirect_loop_bounded`);
* `Client.Session` — retry budget, per-host breaker, RFC 6265 cookie jar
  (`retry_budget_bounded`, `cookie_jar_match`);
* `Client.CookieExpiry` — the expiry-aware jar;
* `Client.Tls` — chain verification + SNI + ALPN (`client_verifies_chain`,
  `alpn_selects`).

This module is the **fetch** that composes them into one transaction:
`fetchLoop` threads a cookie jar and a redirect budget through
cookie-select → send/receive (the protocol transaction) → jar-update → redirect
decision → re-enter, and a retry driver (`retryDriver`) re-runs it under the
Session retry budget. The protocol transaction is a *parameter* (`Upstream`) —
the ALPN-selected send/receive — and `upH1` discharges it concretely as the
proven `Client.H1.transaction`; the H2/H3 transactions carry their own
faithfulness at their own layer (`client_server_agreement` / `request_faithful`).

## What is proven — the composition (each chains a component theorem)

* `fetch_faithful` — a single-hop fetch against a non-redirect (200) upstream
  delivers exactly the proven protocol transaction's response
  (chains `H1.transaction_faithful`) and attaches exactly the RFC 6265-sendable
  cookies (chains `Session.cookie_jar_match`).
* `fetch_follows_redirect` — a 3xx response with a `Location` drives a second
  request to the resolved target with the method rewritten per RFC 9110 §15.4
  (chains `Redirect.redirect_follows_location`).
* `fetch_cookie_roundtrip` — a `Set-Cookie` on response 1 is stored and, when it
  is RFC 6265-sendable to the follow-up origin, is attached to request 2
  (chains `Session.cookie_jar_match`).
* `fetch_retry_bounded` — the retry driver makes at most `maxRetries + 1`
  attempts, and a non-idempotent method is never retried
  (chains `Session.retry_budget_bounded`).
* `fetch_redirect_terminates` — the number of emitted requests is bounded by the
  redirect budget `maxRedirects + 1` (the loop analogue of
  `Redirect.redirect_loop_bounded`).

0 sorries; axioms ⊆ `{propext, Quot.sound, Classical.choice}`.
-/

namespace Proto
namespace Client
namespace Fetch

open Reactor (Response)
open Proto.Client.Redirect (Target Scheme FollowRequest FollowResult followStep
  resolveLocation findLocation isRedirectStatus redirectMethod)
open Client.Session (Method RetryPolicy retriesTaken attemptsMade retryableOutcome
  retry_budget_bounded retriesTaken_le jarSend RfcSendable cookieMatches cookieMatches_iff
  cookie_jar_match Cookie Req)

abbrev Bytes := List UInt8

/-- The negotiated upstream: the ALPN-selected send/receive transaction as seen
from the redirect/cookie policy layer — a target's request is answered with a
parsed `Reactor.Response`. `upH1` instantiates this with the proven
`Client.H1.transaction`; an H2/H3 instantiation plugs in the H2/H3 transactions. -/
abbrev Upstream := Target → Response

/-- One outbound request the fetch actually emitted: the target it went to, the
method used, and the cookies attached (the jar's `jarSend` at that hop). -/
structure Emitted where
  target : Target
  method : Bytes
  sent   : List Cookie
deriving Repr

/-- The transcript of a fetch: the outbound requests in order, the final response
delivered, and the resulting cookie jar. -/
structure FetchTrace where
  emitted : List Emitted
  final   : Response
  jar     : List Cookie
deriving Repr

/-! ## Client configuration and state -/

/-- The fetch policy knobs: the retry budget, the per-host breaker config, and
the redirect budget. -/
structure Config where
  retry        : RetryPolicy
  breaker      : Client.Session.Cfg
  maxRedirects : Nat

/-- The evolving client state: the cookie jar, the per-origin breaker, and the
policy config. -/
structure ClientState where
  jar     : List Cookie
  breaker : Client.Session.Breaker
  config  : Config

/-! ## The composed fetch loop -/

/-- **The composed fetch transaction (one attempt).** Bounded by the redirect
budget `fuel`: at each hop select the jar's sendable cookies (`Session.jarSend`),
run the protocol transaction (`up`), update the jar from `Set-Cookie` (`setC`),
then decide via `Redirect.followStep` — on a follow, re-enter against the resolved
target with one unit of budget spent; otherwise deliver the response. Structural
on `fuel`, so it always terminates. -/
def fetchLoop (up : Upstream) (setC : Response → List Cookie) (reqOf : Target → Req) :
    Nat → List Cookie → Target → Bytes → FetchTrace
  | 0, jar, cur, m =>
    let resp := up cur
    { emitted := [{ target := cur, method := m, sent := jarSend jar (reqOf cur) }],
      final := resp, jar := jar ++ setC resp }
  | fuel + 1, jar, cur, m =>
    let resp := up cur
    let sent := jarSend jar (reqOf cur)
    let jar' := jar ++ setC resp
    match followStep cur m resp.status resp.headers (fuel + 1) with
    | .followed fr _ =>
      let rest := fetchLoop up setC reqOf fuel jar' fr.target fr.method
      { rest with emitted := { target := cur, method := m, sent := sent } :: rest.emitted }
    | _ =>
      { emitted := [{ target := cur, method := m, sent := sent }],
        final := resp, jar := jar' }

/-- The fetch entry point: run the loop from the client state's jar under the
configured redirect budget. -/
def fetch (st : ClientState) (up : Upstream) (setC : Response → List Cookie)
    (reqOf : Target → Req) (origin : Target) (m : Bytes) : FetchTrace :=
  fetchLoop up setC reqOf st.config.maxRedirects st.jar origin m

/-! ## Structural lemmas about the loop transcript -/

/-- The first emitted request is always the origin request, carrying the jar's
sendable cookies at that hop. -/
theorem emitted_head (up : Upstream) (setC : Response → List Cookie) (reqOf : Target → Req)
    (fuel : Nat) (jar : List Cookie) (cur : Target) (m : Bytes) :
    (fetchLoop up setC reqOf fuel jar cur m).emitted.head?
      = some { target := cur, method := m, sent := jarSend jar (reqOf cur) } := by
  cases fuel with
  | zero => rfl
  | succ k =>
    simp only [fetchLoop]
    split <;> rfl

/-- On a non-followable (e.g. 200) response the loop stops at the origin and
delivers exactly that response. -/
theorem final_of_nonredirect (up : Upstream) (setC : Response → List Cookie)
    (reqOf : Target → Req) (fuel : Nat) (jar : List Cookie) (cur : Target) (m : Bytes)
    (h : isRedirectStatus (up cur).status = false) :
    (fetchLoop up setC reqOf fuel jar cur m).final = up cur := by
  cases fuel with
  | zero => rfl
  | succ k =>
    simp only [fetchLoop, followStep, h, Bool.false_eq_true, if_false]

/-! ## Theorem — the redirect budget bounds the request chain -/

/-- **The redirect chain terminates.** The number of requests a fetch emits is at
most `fuel + 1` — following redirects against *any* upstream, even one that
redirects on every hop, halts after at most `fuel` follows. The loop analogue of
`Redirect.redirect_loop_bounded`. -/
theorem fetch_redirect_terminates (up : Upstream) (setC : Response → List Cookie)
    (reqOf : Target → Req) (fuel : Nat) (jar : List Cookie) (cur : Target) (m : Bytes) :
    (fetchLoop up setC reqOf fuel jar cur m).emitted.length ≤ fuel + 1 := by
  induction fuel generalizing jar cur m with
  | zero => simp [fetchLoop]
  | succ k ih =>
    simp only [fetchLoop]
    split
    · rename_i fr rem heq
      simp only [List.length_cons]
      have := ih (jar ++ setC (up cur)) fr.target fr.method
      omega
    · simp

/-! ## Theorem — a 3xx redirect is followed to its Location -/

/-- The follow-up request's target and method (the second emitted request), if
any. -/
def followUp (t : FetchTrace) : Option (Target × Bytes × List Cookie) :=
  (t.emitted.drop 1).head?.map (fun e => (e.target, e.method, e.sent))

/-- **A followable redirect re-issues to its resolved `Location`.** When the
origin returns a 3xx status with a `Location`, under a live redirect budget and no
secure→insecure downgrade, the fetch emits a second request to
`resolveLocation cur loc` with the method rewritten per RFC 9110 §15.4 (preserved
for 307/308, `GET` for 301/302/303). Chains `Redirect.redirect_follows_location`. -/
theorem fetch_follows_redirect (up : Upstream) (setC : Response → List Cookie)
    (reqOf : Target → Req) (fuel : Nat) (jar : List Cookie) (cur : Target) (m : Bytes)
    (loc : Bytes)
    (hstat : isRedirectStatus (up cur).status = true)
    (hloc : findLocation (up cur).headers = some loc)
    (hnodown : ¬(cur.scheme = Scheme.https ∧ (resolveLocation cur loc).scheme = Scheme.http)) :
    followUp (fetchLoop up setC reqOf (fuel + 1) jar cur m)
      = some (resolveLocation cur loc, redirectMethod (up cur).status m,
              jarSend (jar ++ setC (up cur)) (reqOf (resolveLocation cur loc))) := by
  have hfollow := Redirect.redirect_follows_location cur m (up cur).status (up cur).headers loc
    (fuel + 1) hstat hloc (Nat.succ_pos fuel) hnodown
  simp only [fetchLoop, hfollow, followUp, List.drop_one, List.tail_cons]
  rw [emitted_head]
  rfl

/-! ## Theorem — a Set-Cookie roundtrips onto the follow-up request -/

/-- **The cookie roundtrip.** A `Set-Cookie` carried on the first (redirect)
response is stored in the jar and, when it is RFC 6265-sendable to the follow-up
origin, is attached to the second request. Chains `Session.cookie_jar_match`: the
stored cookie appears in the follow-up's `jarSend` exactly because it is sendable. -/
theorem fetch_cookie_roundtrip (up : Upstream) (setC : Response → List Cookie)
    (reqOf : Target → Req) (fuel : Nat) (jar : List Cookie) (cur : Target) (m : Bytes)
    (loc : Bytes) (c : Cookie)
    (hstat : isRedirectStatus (up cur).status = true)
    (hloc : findLocation (up cur).headers = some loc)
    (hnodown : ¬(cur.scheme = Scheme.https ∧ (resolveLocation cur loc).scheme = Scheme.http))
    (hset : c ∈ setC (up cur))
    (hsend : RfcSendable c (reqOf (resolveLocation cur loc))) :
    ∃ tgt mth sent, followUp (fetchLoop up setC reqOf (fuel + 1) jar cur m) = some (tgt, mth, sent)
      ∧ c ∈ sent := by
  refine ⟨_, _, _, fetch_follows_redirect up setC reqOf fuel jar cur m loc hstat hloc hnodown, ?_⟩
  rw [cookie_jar_match]
  exact ⟨List.mem_append_right _ hset, hsend⟩

/-! ## The protocol transaction discharged: H1 -/

/-- The H1 instantiation of the upstream: build the outbound `Proto.Request` from
the target with `mkReq`, run the proven `Client.H1.transaction`, and take the
parsed response (a bodyless `200` on the impossible failure branch, ruled out
under `WF`). -/
def upH1 (handler : Proto.Request → Response) (mkReq : Target → Proto.Request) : Upstream :=
  fun t => (Proto.Client.H1.transaction handler (mkReq t)).getD (Reactor.ok200 [])

/-- Under the request/response well-formedness the H1 round-trip needs, the H1
upstream delivers exactly the proven wire form of the handler's response — this is
`Client.H1.transaction_faithful` read through `upH1`. -/
theorem upH1_faithful (handler : Proto.Request → Response) (mkReq : Target → Proto.Request)
    (t : Target) (hreq : Proto.RequestSerialize.WF (mkReq t))
    (hresp : ∀ r, Proto.ResponseParse.WF (handler r)) :
    upH1 handler mkReq t = Proto.ResponseParse.wireForm (handler (mkReq t)) := by
  simp only [upH1, Proto.Client.H1.transaction_faithful handler (mkReq t) hreq hresp,
    Option.getD_some]

/-- **`fetch_faithful` — the composed base case.** A single-hop fetch against a
non-redirect (200-class) upstream delivers exactly the proven protocol
transaction's response (composing `H1.transaction_faithful` via `upH1_faithful`),
and the cookies the origin request carries are exactly the RFC 6265-sendable
cookies of the jar (composing `Session.cookie_jar_match`). The two proven
round-trips — the wire codec and the cookie policy — meet in one statement. -/
theorem fetch_faithful (handler : Proto.Request → Response) (mkReq : Target → Proto.Request)
    (setC : Response → List Cookie) (reqOf : Target → Req)
    (fuel : Nat) (jar : List Cookie) (origin : Target) (m : Bytes)
    (hreq : Proto.RequestSerialize.WF (mkReq origin))
    (hresp : ∀ r, Proto.ResponseParse.WF (handler r))
    (hstat : isRedirectStatus (handler (mkReq origin)).status = false) :
    (fetchLoop (upH1 handler mkReq) setC reqOf fuel jar origin m).final
        = Proto.ResponseParse.wireForm (handler (mkReq origin))
    ∧ (∃ e, (fetchLoop (upH1 handler mkReq) setC reqOf fuel jar origin m).emitted.head? = some e
        ∧ ∀ c, c ∈ e.sent ↔ (c ∈ jar ∧ RfcSendable c (reqOf origin))) := by
  have hup : upH1 handler mkReq origin = Proto.ResponseParse.wireForm (handler (mkReq origin)) :=
    upH1_faithful handler mkReq origin hreq hresp
  have hnr : isRedirectStatus (upH1 handler mkReq origin).status = false := by
    rw [hup]; exact hstat
  refine ⟨?_, ?_⟩
  · rw [final_of_nonredirect _ _ _ _ _ _ _ hnr, hup]
  · refine ⟨_, emitted_head _ _ _ _ _ _ _, ?_⟩
    intro c
    exact cookie_jar_match jar (reqOf origin) c

/-! ## The retry driver — bounded by the Session retry budget -/

/-- **The retry driver.** Re-run the single-shot fetch `run idx` against a stream
of observed attempt outcomes; a further retry is admitted only when the outcome is
`Session.retryableOutcome` (idempotent method on a transient status) and the retry
budget is not spent — exactly the `Session.retriesTaken` discipline, threading the
fetch traces. -/
def retryDriver (p : RetryPolicy) (m : Method) (run : Nat → FetchTrace) :
    Nat → Nat → List Nat → List FetchTrace
  | _, idx, [] => [run idx]
  | used, idx, s :: rest =>
    if retryableOutcome p m s = true ∧ used < p.maxRetries then
      run idx :: retryDriver p m run (used + 1) (idx + 1) rest
    else [run idx]

/-- The number of attempts the driver makes, threaded with `used`, equals the
Session retry count plus one — the bridge that lets the budget bound transfer. -/
theorem retryDriver_length (p : RetryPolicy) (m : Method) (run : Nat → FetchTrace) :
    ∀ (used idx : Nat) (statuses : List Nat),
      (retryDriver p m run used idx statuses).length + used
        = retriesTaken p m used statuses + 1 := by
  intro used idx statuses
  induction statuses generalizing used idx with
  | nil => simp only [retryDriver, retriesTaken, List.length_singleton]; omega
  | cons s rest ih =>
    unfold retryDriver retriesTaken
    by_cases hc : retryableOutcome p m s = true ∧ used < p.maxRetries
    · rw [if_pos hc, if_pos hc]
      have := ih (used + 1) (idx + 1)
      simp only [List.length_cons]
      omega
    · rw [if_neg hc, if_neg hc]
      simp only [List.length_singleton]; omega

/-- The total attempts the driver makes, from a fresh budget. -/
def fetchAttempts (p : RetryPolicy) (m : Method) (run : Nat → FetchTrace)
    (statuses : List Nat) : Nat :=
  (retryDriver p m run 0 0 statuses).length

/-- **`fetch_retry_bounded` — the retry driver respects the budget.** Across any
outcome stream, the fetch makes at most `maxRetries + 1` attempts; and a
non-idempotent method (POST/PATCH/CONNECT) is never retried — exactly one attempt.
Chains `Session.retry_budget_bounded` through the driver's length bridge. -/
theorem fetch_retry_bounded (p : RetryPolicy) (m : Method) (run : Nat → FetchTrace)
    (statuses : List Nat) :
    fetchAttempts p m run statuses ≤ p.maxRetries + 1
    ∧ (m.idempotent = false → fetchAttempts p m run statuses = 1) := by
  have hlen := retryDriver_length p m run 0 0 statuses
  simp only [Nat.add_zero] at hlen
  have hbudget := retry_budget_bounded p m statuses
  unfold fetchAttempts
  refine ⟨?_, ?_⟩
  · -- attempts = retriesTaken 0 + 1 ≤ maxRetries + 1
    rw [hlen]
    have := hbudget.1
    unfold attemptsMade at this
    omega
  · intro hidem
    have h1 := hbudget.2 hidem
    unfold attemptsMade at h1
    omega

/-! ## Grounding: a concrete redirect + cookie roundtrip (non-vacuity)

A real `https://ex/` origin returns `302 Location: /next` with a `Set-Cookie` for
`ex`; the fetch follows to `https://ex/next` and carries the cookie on request 2.
Every hypothesis of the general theorems is discharged by `decide` on real bytes,
so the composition is exercised, not vacuous. -/

section Witness

/-- Host `"ex"`. -/
def exHost : Bytes := [101, 120]
/-- `"/"`. -/
def rootPath : Bytes := [47]
/-- `"/next"` — a relative `Location`. -/
def nextLoc : Bytes := [47, 110, 101, 120, 116]
/-- `"GET"`. -/
def mGET : Bytes := [71, 69, 84]

/-- The `https://ex/` origin. -/
def exOrigin : Target := ⟨Scheme.https, exHost, rootPath⟩

/-- A host-only cookie for `ex`, matching any path over HTTPS. Its domain labels
are the host bytes as `Nat` tokens — the same bridge `reqOfTarget` uses. -/
def exCookie : Cookie :=
  { name := 1, value := 1, domain := exHost.map (·.toNat), path := [],
    secure := false, hostOnly := true }

/-- The bridge from a redirect `Target` to a Session cookie `Req`: host/path
bytes become label/segment token lists; HTTPS iff the scheme is `https`. -/
def reqOfTarget (t : Target) : Req :=
  { host := t.host.map (·.toNat), path := t.path.map (·.toNat),
    https := (t.scheme = Scheme.https), hostIsIp := false }

/-- The witness upstream: `https://ex/` answers `302 Location: /next`; everything
else answers `200 OK`. -/
def exUpstream : Upstream := fun t =>
  if t.path = rootPath then
    { status := 302, reason := [], headers := [(Redirect.locationName, nextLoc)], body := [] }
  else Reactor.ok200 []

/-- The witness `Set-Cookie` reader: the `302` sets `exCookie`. -/
def exSetC : Response → List Cookie := fun resp =>
  if resp.status = 302 then [exCookie] else []

/-- The resolved follow-up target is `https://ex/next` — same scheme and host, so
`exCookie` is still sendable. -/
theorem ex_resolves : resolveLocation exOrigin nextLoc = ⟨Scheme.https, exHost, nextLoc⟩ := by
  decide

/-- The fetch follows the redirect to `https://ex/next`, rewriting nothing (302 on
a GET already yields GET). -/
theorem ex_follows :
    followUp (fetchLoop exUpstream exSetC reqOfTarget 3 [] exOrigin mGET)
      = some (⟨Scheme.https, exHost, nextLoc⟩, mGET,
              jarSend ([] ++ exSetC (exUpstream exOrigin)) (reqOfTarget ⟨Scheme.https, exHost, nextLoc⟩)) := by
  have h := fetch_follows_redirect exUpstream exSetC reqOfTarget 2 [] exOrigin mGET nextLoc
    (by decide) (by decide) (by decide)
  rw [ex_resolves] at h
  -- the 302 upstream on exOrigin has status 302, and redirectMethod 302 GET = GET
  simpa [exUpstream, rootPath, redirectMethod] using h

/-- **The concrete roundtrip:** on the follow-up request `exCookie` is attached —
the `Set-Cookie` from response 1 rode onto request 2 to the same origin. -/
theorem ex_cookie_roundtrip :
    ∃ tgt mth sent, followUp (fetchLoop exUpstream exSetC reqOfTarget 3 [] exOrigin mGET)
      = some (tgt, mth, sent) ∧ exCookie ∈ sent :=
  fetch_cookie_roundtrip exUpstream exSetC reqOfTarget 2 [] exOrigin mGET nextLoc exCookie
    (by decide) (by decide) (by decide) (by decide)
    ((cookieMatches_iff exCookie (reqOfTarget (resolveLocation exOrigin nextLoc))).mp (by decide))

end Witness

/-! ## ALPN → protocol selection (the negotiated transaction) -/

/-- The application protocol a fetch speaks, once ALPN has resolved. The
`Upstream` the loop runs is the transaction for this protocol; `upH1` is the H1
instance, H2/H3 plug in `Client.H2` / `Client.H3`. -/
inductive NegProto where
  | h1 | h2 | h3
deriving Repr, DecidableEq

/-- Read the ALPN outcome (RFC 7301, via `Client.Tls.negotiateAlpn`) into the
protocol the fetch will use, defaulting to H1 when the server named nothing. Only
a protocol the client offered can be selected — that is `Client.Tls.alpn_selects`. -/
def protoOfAlpn : Client.Tls.AlpnOutcome → NegProto
  | .selected "h2" => .h2
  | .selected "h3" => .h3
  | _ => .h1

/-- A negotiated protocol was one the client offered — the ALPN safety property,
re-exported from `Client.Tls.alpn_selects` so protocol selection inherits it. -/
theorem fetch_alpn_offered {offered : List Client.Tls.Proto} {pick : Option Client.Tls.Proto}
    {p : Client.Tls.Proto} (h : Client.Tls.negotiateAlpn offered pick = .selected p) :
    p ∈ offered :=
  Client.Tls.alpn_selects h

end Fetch
end Client
end Proto
