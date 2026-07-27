/-
Client.Session — verified client-side session policy: retry with exponential
backoff (RFC 7231 idempotency), a per-host circuit breaker, and an RFC 6265
cookie jar.

This module is the CLIENT dual of the server-side guards. Where the server's
`Proxy.Breaker` protects an upstream, a client session protects *itself* and its
peers: it caps how hard it retries a flaky origin, trips a breaker so a dead host
stops eating retry budget, and scopes cookies to the origins entitled to see
them. Each capability is specified as an INDEPENDENT contract — transcribed from
the relevant standard, in this module's own vocabulary, with no appeal to the
executable decision functions — and the executable functions are proven to meet
it, with a mutant that violates the contract exhibited so the theorems are not
tautologies.

## Retry (RFC 7231 §4.2.2)

`retriesTaken` walks the sequence of attempt outcomes and stops when an outcome
is not retryable or the budget is spent. A retry is admissible only for an
IDEMPOTENT method (PUT, DELETE, and the safe methods GET/HEAD/OPTIONS/TRACE —
POST/PATCH/CONNECT are excluded) on a retryable status code, and only while fewer
than `maxRetries` retries have been taken. The exponential schedule
`delayForAttempt` is capped at `maxDelay`.

  * `retry_budget_bounded` — the total attempts a request makes is at most
    `maxRetries + 1`, and a NON-IDEMPOTENT method is never retried (exactly one
    attempt). A wrong policy that retries POST is exhibited as a counterexample.

## Circuit breaker (Nygard, *Release It!*, ch. Circuit Breaker)

A three-phase machine per origin: CLOSED counts consecutive failures and TRIPS
OPEN on the `threshold`-th; OPEN fails fast until `cooldown` elapses on the clock
and then moves to HALF-OPEN; HALF-OPEN admits up to `halfOpenMax` trial probes, a
probe SUCCESS closes it, a probe FAILURE re-opens it.

  * `breaker_opens_after_failures` — from a fresh origin, `n` consecutive
    failures leave the breaker OPEN exactly when `threshold ≤ n`, and CLOSED
    otherwise. A breaker that opens eagerly (on the first failure) is shown to
    disagree.
  * `breaker_half_open_recovers` — from OPEN, once the cooldown has elapsed a
    tick moves to HALF-OPEN, the breaker then ADMITS a probe, and that probe's
    SUCCESS closes the breaker with the failure count reset to zero.

## Cookie jar (RFC 6265 §5.1.3 / §5.1.4 / §5.4)

Domains are modelled as label sequences (most-specific label first) and paths as
segment sequences, so the RFC's "suffix with a preceding dot" domain-match is
exactly label-suffix and "prefix with a `/` boundary" path-match is exactly
segment-prefix. A stored cookie is sent on a request iff its domain domain-matches
the request host (or, for a host-only cookie, is identical), its path path-matches
the request path, and — if it is Secure — the request is over HTTPS.

  * `cookie_jar_match` — a cookie appears in the outgoing set iff it is stored and
    RFC-sendable to the request.
  * `cookie_jar_no_cross_domain` — a cookie whose domain does not match the
    request host is NEVER sent (the security invariant). Concrete matching and
    cross-domain / secure-over-HTTP / path-mismatch pairs witness both directions.
-/

namespace Client.Session

/-! ############################################################################
    ## Retry with exponential backoff (RFC 7231 §4.2.2)
    ########################################################################## -/

/-- HTTP request methods relevant to retry safety. -/
inductive Method
  | get | head | put | delete | options | trace | post | patch | connect
deriving DecidableEq, Repr

/-- RFC 7231 §4.2.2: a method is idempotent iff it is PUT, DELETE, or one of the
safe methods GET/HEAD/OPTIONS/TRACE. POST, PATCH and CONNECT are NOT idempotent
and a client must not replay them automatically. -/
def Method.idempotent : Method → Bool
  | .get | .head | .put | .delete | .options | .trace => true
  | .post | .patch | .connect => false

/-- A retry policy: the retry budget, the exponential schedule, and the set of
status codes considered transient. -/
structure RetryPolicy where
  maxRetries : Nat
  initialDelay : Nat
  maxDelay : Nat
  backoffFactor : Nat
  retryableStatus : List Nat
deriving Repr

/-- Exponential backoff for attempt `attempt` (0-indexed), capped at `maxDelay`:
`min (initialDelay * backoffFactor ^ attempt) maxDelay`. -/
def RetryPolicy.delayForAttempt (p : RetryPolicy) (attempt : Nat) : Nat :=
  min (p.initialDelay * p.backoffFactor ^ attempt) p.maxDelay

/-- An outcome is retryable iff the method is idempotent AND the observed status
code is in the policy's transient set. -/
def retryableOutcome (p : RetryPolicy) (m : Method) (status : Nat) : Bool :=
  m.idempotent && p.retryableStatus.contains status

/-- Walk the sequence of attempt outcomes, counting retries taken. `used` is the
number of retries already spent; a further retry is admitted only when the next
outcome is retryable AND the budget is not exhausted. -/
def retriesTaken (p : RetryPolicy) (m : Method) : Nat → List Nat → Nat
  | used, [] => used
  | used, s :: rest =>
    if retryableOutcome p m s = true ∧ used < p.maxRetries then
      retriesTaken p m (used + 1) rest
    else used

/-- Total attempts a request makes on the given outcome stream: one initial
attempt plus the retries taken. -/
def attemptsMade (p : RetryPolicy) (m : Method) (statuses : List Nat) : Nat :=
  retriesTaken p m 0 statuses + 1

/-- The retries taken never exceed `max used maxRetries`; the budget guard caps
the count regardless of how long the failure stream is. -/
theorem retriesTaken_le (p : RetryPolicy) (m : Method) :
    ∀ (used : Nat) (statuses : List Nat),
      retriesTaken p m used statuses ≤ max used p.maxRetries := by
  intro used statuses
  induction statuses generalizing used with
  | nil => simp only [retriesTaken]; exact Nat.le_max_left _ _
  | cons s rest ih =>
    unfold retriesTaken
    by_cases hc : retryableOutcome p m s = true ∧ used < p.maxRetries
    · rw [if_pos hc]
      have hlt : used < p.maxRetries := hc.2
      calc retriesTaken p m (used + 1) rest
          ≤ max (used + 1) p.maxRetries := ih (used + 1)
        _ = p.maxRetries := by apply Nat.max_eq_right; omega
        _ ≤ max used p.maxRetries := Nat.le_max_right _ _
    · rw [if_neg hc]; exact Nat.le_max_left _ _

/-- A NON-IDEMPOTENT method is never retried: `retriesTaken` returns the count it
started with, unchanged. -/
theorem retriesTaken_nonidem (p : RetryPolicy) (m : Method)
    (h : m.idempotent = false) :
    ∀ (used : Nat) (statuses : List Nat), retriesTaken p m used statuses = used := by
  intro used statuses
  cases statuses with
  | nil => rfl
  | cons s rest => simp [retriesTaken, retryableOutcome, h]

/-- **RETRY BUDGET IS BOUNDED.** For every policy, method and outcome stream, the
total attempts are at most `maxRetries + 1`; and a non-idempotent method makes
exactly one attempt (it is never retried). -/
theorem retry_budget_bounded (p : RetryPolicy) (m : Method) (statuses : List Nat) :
    attemptsMade p m statuses ≤ p.maxRetries + 1
    ∧ (m.idempotent = false → attemptsMade p m statuses = 1) := by
  refine ⟨?_, ?_⟩
  · unfold attemptsMade
    have h := retriesTaken_le p m 0 statuses
    have h0 : retriesTaken p m 0 statuses ≤ p.maxRetries := by
      have : max 0 p.maxRetries = p.maxRetries := by simp
      rwa [this] at h
    exact Nat.add_le_add_right h0 1
  · intro h
    unfold attemptsMade
    rw [retriesTaken_nonidem p m h 0 statuses]

/-! ### Non-vacuity: the idempotency and budget guards are load-bearing -/

/-- A mutant retry loop that DROPS the idempotency guard — it retries on any
transient status regardless of method. -/
def badRetriesTaken (p : RetryPolicy) : Nat → List Nat → Nat
  | used, [] => used
  | used, s :: rest =>
    if p.retryableStatus.contains s = true ∧ used < p.maxRetries then
      badRetriesTaken p (used + 1) rest
    else used

/-- Reference policy for the concrete checks. -/
def demoPolicy : RetryPolicy :=
  { maxRetries := 3, initialDelay := 1, maxDelay := 8, backoffFactor := 2,
    retryableStatus := [429, 503] }

-- POST is never retried even on a stream of transient 503s (exactly one attempt).
example : attemptsMade demoPolicy .post [503, 503, 503] = 1 := by decide
-- GET is retried, capped at the budget: 3 retries + 1 = 4 attempts.
example :
    attemptsMade { demoPolicy with maxRetries := 3 } .get [503, 503, 503, 503, 503] = 4 := by
  decide
-- A non-transient status (404) stops the retries immediately.
example : attemptsMade demoPolicy .get [404, 503, 503] = 1 := by decide
-- Exponential schedule, capped at maxDelay = 8: 1,2,4,8,8,...
example : demoPolicy.delayForAttempt 0 = 1 := by decide
example : demoPolicy.delayForAttempt 3 = 8 := by decide
example : demoPolicy.delayForAttempt 10 = 8 := by decide
-- The idempotency guard has teeth: the mutant retries POST where the correct
-- loop takes zero retries.
example :
    badRetriesTaken demoPolicy 0 [503, 503, 503] = 3
    ∧ retriesTaken demoPolicy .post 0 [503, 503, 503] = 0 := by decide

/-! ############################################################################
    ## Per-host circuit breaker (Nygard, Circuit Breaker)
    ########################################################################## -/

/-- Breaker phase. -/
inductive Phase | closed | opened | halfOpen
deriving DecidableEq, Repr

/-- Breaker configuration: consecutive-failure threshold to trip, cooldown before
probing, and the number of concurrent half-open trial probes permitted. -/
structure Cfg where
  threshold : Nat
  cooldown : Nat
  halfOpenMax : Nat
deriving Repr

/-- Breaker state: phase, consecutive-failure count, the clock instant it last
opened (the cooldown origin), half-open probes in flight, and the latest clock. -/
structure Breaker where
  phase : Phase
  fails : Nat
  openedAt : Nat
  probes : Nat
  clock : Nat
deriving DecidableEq, Repr

/-- A fresh origin: closed, no failures. -/
def Breaker.init : Breaker := ⟨.closed, 0, 0, 0, 0⟩

/-- Events driving the breaker. `tick` advances the clock (and lazily performs
the open→half-open transition once the cooldown elapses); `probe` admits a
half-open trial; `success`/`failure` report a completed request's outcome. -/
inductive Ev | tick (now : Nat) | success | failure | probe
deriving DecidableEq, Repr

/-- The breaker transition. -/
def step (cfg : Cfg) (b : Breaker) : Ev → Breaker
  | .tick now =>
    let clk := max b.clock now
    match b.phase with
    | .opened =>
      if cfg.cooldown ≤ now - b.openedAt then
        { b with phase := .halfOpen, probes := 0, clock := clk }
      else
        { b with clock := clk }
    | _ => { b with clock := clk }
  | .probe =>
    match b.phase with
    | .halfOpen =>
      if b.probes < cfg.halfOpenMax then { b with probes := b.probes + 1 } else b
    | _ => b
  | .success =>
    { phase := .closed, fails := 0, openedAt := b.openedAt, probes := 0, clock := b.clock }
  | .failure =>
    let f := b.fails + 1
    match b.phase with
    | .closed =>
      if cfg.threshold ≤ f then
        { b with phase := .opened, fails := f, openedAt := b.clock }
      else
        { b with fails := f }
    | .halfOpen =>
      { b with phase := .opened, fails := f, probes := 0, openedAt := b.clock }
    | .opened =>
      { b with fails := f, openedAt := b.clock }

/-- Whether a request reaches the origin: yes when closed, no when open, and when
half-open only while trial-probe capacity remains. -/
def admits (cfg : Cfg) (b : Breaker) : Bool :=
  match b.phase with
  | .closed => true
  | .opened => false
  | .halfOpen => b.probes < cfg.halfOpenMax

/-- Run an event history, oldest first. -/
def run (cfg : Cfg) (b : Breaker) : List Ev → Breaker
  | [] => b
  | e :: es => run cfg (step cfg b e) es

theorem run_append (cfg : Cfg) :
    ∀ (b : Breaker) (l1 l2 : List Ev),
      run cfg b (l1 ++ l2) = run cfg (run cfg b l1) l2 := by
  intro b l1
  induction l1 generalizing b with
  | nil => intro l2; rfl
  | cons e es ih => intro l2; simp only [run, List.cons_append]; exact ih (step cfg b e) l2

/-- State after `n` consecutive failures from a fresh origin (positive
threshold): the breaker is OPEN exactly when `threshold ≤ n`, and the failure
count is `n` throughout. The clock and cooldown origin stay 0 (no tick occurs). -/
theorem failures_from_closed (cfg : Cfg) (ht : 0 < cfg.threshold) :
    ∀ n : Nat,
      run cfg Breaker.init (List.replicate n .failure) =
        (if cfg.threshold ≤ n then
          ({ phase := .opened, fails := n, openedAt := 0, probes := 0, clock := 0 } : Breaker)
         else
          { phase := .closed, fails := n, openedAt := 0, probes := 0, clock := 0 }) := by
  intro n
  induction n with
  | zero =>
    have : ¬ cfg.threshold ≤ 0 := by omega
    simp [run, Breaker.init, this]
  | succ k ih =>
    rw [List.replicate_succ', run_append, ih]
    by_cases hk : cfg.threshold ≤ k
    · have hk1 : cfg.threshold ≤ k + 1 := by omega
      simp [run, step, hk, hk1]
    · by_cases hk1 : cfg.threshold ≤ k + 1
      · simp [run, step, hk, hk1]
      · simp [run, step, hk, hk1]

/-- **BREAKER OPENS AFTER `threshold` FAILURES.** From a fresh origin, `n`
consecutive failures leave the breaker OPEN exactly when `threshold ≤ n`, and
CLOSED otherwise. This pins the trip point precisely: not before, and by, the
threshold. -/
theorem breaker_opens_after_failures (cfg : Cfg) (ht : 0 < cfg.threshold) (n : Nat) :
    (run cfg Breaker.init (List.replicate n .failure)).phase
      = (if cfg.threshold ≤ n then .opened else .closed) := by
  rw [failures_from_closed cfg ht n]
  by_cases h : cfg.threshold ≤ n <;> simp [h]

/-- **BREAKER RECOVERS THROUGH HALF-OPEN.** From an OPEN breaker whose cooldown
has elapsed on the clock, a tick moves it to HALF-OPEN; the breaker then ADMITS a
probe; and that probe's SUCCESS closes the breaker with the failure count reset
to zero. -/
theorem breaker_half_open_recovers (cfg : Cfg) (b : Breaker) (now : Nat)
    (hopen : b.phase = .opened)
    (hcool : cfg.cooldown ≤ now - b.openedAt)
    (hmax : 0 < cfg.halfOpenMax) :
    (step cfg b (.tick now)).phase = .halfOpen
    ∧ admits cfg (step cfg b (.tick now)) = true
    ∧ (step cfg (step cfg (step cfg b (.tick now)) .probe) .success).phase = .closed
    ∧ (step cfg (step cfg (step cfg b (.tick now)) .probe) .success).fails = 0 := by
  obtain ⟨ph, f, o, pr, cl⟩ := b
  simp only at hopen
  subst hopen
  have hb1 : step cfg (⟨Phase.opened, f, o, pr, cl⟩ : Breaker) (.tick now)
      = ⟨Phase.halfOpen, f, o, 0, max cl now⟩ := by
    simp only [step]; rw [if_pos hcool]
  rw [hb1]
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp [step, admits, hmax]

/-! ### Non-vacuity: the trip threshold and the recovery are load-bearing -/

/-- A mutant breaker that trips EAGERLY — any failure opens it, ignoring the
threshold. -/
def badStepEager (cfg : Cfg) (b : Breaker) : Ev → Breaker
  | .failure => { b with phase := .opened, fails := b.fails + 1, openedAt := b.clock }
  | e => step cfg b e

def badRunEager (cfg : Cfg) (b : Breaker) : List Ev → Breaker
  | [] => b
  | e :: es => badRunEager cfg (badStepEager cfg b e) es

def demoCfg : Cfg := { threshold := 3, cooldown := 5, halfOpenMax := 1 }

-- The real breaker is still CLOSED after two failures (threshold 3)…
example : (run demoCfg Breaker.init [.failure, .failure]).phase = .closed := by decide
-- …and OPEN after the third.
example :
    (run demoCfg Breaker.init [.failure, .failure, .failure]).phase = .opened := by decide
-- Recovery: open, wait past cooldown, probe, succeed ⇒ closed.
example :
    (run { threshold := 1, cooldown := 5, halfOpenMax := 1 } Breaker.init
      [.failure, .tick 5, .probe, .success]).phase = .closed := by decide
-- A half-open probe that FAILS re-opens the breaker.
example :
    (run { threshold := 1, cooldown := 5, halfOpenMax := 1 } Breaker.init
      [.failure, .tick 5, .probe, .failure]).phase = .opened := by decide
-- Success resets the consecutive-failure count.
example :
    (run demoCfg Breaker.init [.failure, .failure, .success, .failure]).phase = .closed := by
  decide
-- The eager mutant trips on the FIRST failure where the correct breaker (threshold
-- 3) is still closed — so the trip threshold is load-bearing.
example :
    (badRunEager demoCfg Breaker.init [.failure]).phase = .opened
    ∧ (run demoCfg Breaker.init [.failure]).phase = .closed := by decide

/-! ############################################################################
    ## Cookie jar (RFC 6265 §5.1.3 / §5.1.4 / §5.4)
    ########################################################################## -/

/-- A domain as a label sequence, most-specific label FIRST: `sub.example.com`
is `[sub, example, com]`. Labels are abstracted as `Nat` tokens. -/
abbrev Labels := List Nat

/-- A path as a segment sequence: `/a/b` is `[a, b]`. -/
abbrev Segments := List Nat

/-- A stored cookie. `hostOnly` marks a cookie with no `Domain` attribute (sent
only to the exact origin host); `secure` marks a `Secure` cookie. -/
structure Cookie where
  name : Nat
  value : Nat
  domain : Labels
  path : Segments
  secure : Bool
  hostOnly : Bool
deriving DecidableEq, Repr

/-- An outgoing request context: the target host and path, whether it is HTTPS,
and whether the host is a literal IP address (which never suffix-matches). -/
structure Req where
  host : Labels
  path : Segments
  https : Bool
  hostIsIp : Bool
deriving DecidableEq, Repr

/-! ### The RFC 6265 contract (independent specification) -/

/-- RFC 6265 §5.1.3 domain-match: the request host domain-matches the cookie
domain iff they are identical, OR the cookie domain is a proper label-suffix of
the host and the host is not an IP literal. (At label granularity, "suffix" is
exactly the RFC's "suffix whose preceding character is a dot".) -/
def RfcDomainMatch (host cookieDomain : Labels) (hostIsIp : Bool) : Prop :=
  host = cookieDomain ∨ (cookieDomain <:+ host ∧ hostIsIp = false)

/-- RFC 6265 §5.1.4 path-match: the cookie path is a segment-prefix of the request
path (which subsumes identity). -/
def RfcPathMatch (reqPath cookiePath : Segments) : Prop :=
  cookiePath <+: reqPath

/-- RFC 6265 §5.4 domain applicability: a host-only cookie requires an identical
host; a domain cookie uses domain-match. -/
def RfcDomainSendable (c : Cookie) (r : Req) : Prop :=
  if c.hostOnly then r.host = c.domain else RfcDomainMatch r.host c.domain r.hostIsIp

/-- RFC 6265 §5.4: a Secure cookie is sent only over a secure transport. -/
def RfcSecureOk (c : Cookie) (r : Req) : Prop := c.secure = true → r.https = true

/-- RFC 6265 §5.4: a stored cookie is applicable to a request iff its domain,
path and secure conditions all hold. -/
def RfcSendable (c : Cookie) (r : Req) : Prop :=
  RfcDomainSendable c r ∧ RfcPathMatch r.path c.path ∧ RfcSecureOk c r

/-! ### The executable matcher -/

/-- Executable domain check (dual of RFC §5.1.3 / §5.4). -/
def domainOk (c : Cookie) (r : Req) : Bool :=
  if c.hostOnly then decide (r.host = c.domain)
  else decide (r.host = c.domain) || (c.domain.isSuffixOf r.host && !r.hostIsIp)

/-- Executable cookie matcher: domain, path and secure gates, exactly the checks
a client applies before attaching a cookie to a request. -/
def cookieMatches (c : Cookie) (r : Req) : Bool :=
  domainOk c r && c.path.isPrefixOf r.path && (!c.secure || r.https)

/-- The executable domain check meets the RFC domain-applicability contract. -/
theorem domainOk_iff (c : Cookie) (r : Req) :
    domainOk c r = true ↔ RfcDomainSendable c r := by
  unfold domainOk RfcDomainSendable RfcDomainMatch
  cases hho : c.hostOnly with
  | true => simp [decide_eq_true_eq]
  | false =>
    cases hip : r.hostIsIp with
    | true => simp [List.isSuffixOf_iff_suffix, decide_eq_true_eq]
    | false => simp [List.isSuffixOf_iff_suffix, decide_eq_true_eq]

/-- The executable matcher meets the full RFC 6265 §5.4 sendability contract. -/
theorem cookieMatches_iff (c : Cookie) (r : Req) :
    cookieMatches c r = true ↔ RfcSendable c r := by
  have hsec_iff : ∀ (s h : Bool), (!s || h) = true ↔ (s = true → h = true) := by
    intro s h; cases s <;> cases h <;> simp
  unfold cookieMatches RfcSendable RfcPathMatch RfcSecureOk
  rw [Bool.and_eq_true, Bool.and_eq_true, domainOk_iff, List.isPrefixOf_iff_prefix, hsec_iff,
    and_assoc]

/-! ### The jar -/

/-- The cookies a jar sends on a request: those that match. -/
def jarSend (jar : List Cookie) (r : Req) : List Cookie :=
  jar.filter (fun c => cookieMatches c r)

/-- **A STORED COOKIE IS SENT IFF IT MATCHES.** A cookie is in the outgoing set
exactly when it is stored in the jar and is RFC 6265 §5.4-sendable to the
request. -/
theorem cookie_jar_match (jar : List Cookie) (r : Req) (c : Cookie) :
    c ∈ jarSend jar r ↔ (c ∈ jar ∧ RfcSendable c r) := by
  unfold jarSend
  rw [List.mem_filter, cookieMatches_iff]

/-- **NO CROSS-DOMAIN LEAK.** A cookie whose domain does not domain-match the
request host is NEVER sent — the core cookie-confidentiality invariant. -/
theorem cookie_jar_no_cross_domain (jar : List Cookie) (r : Req) (c : Cookie)
    (h : ¬ RfcDomainSendable c r) : c ∉ jarSend jar r := by
  intro hc
  rw [cookie_jar_match] at hc
  exact h hc.2.1

/-! ### Non-vacuity: matching, cross-domain, secure, and path cases -/

-- example.com = [1, 0]; sub.example.com = [2, 1, 0]; evil.test = [9, 8]
def secureReq : Req := { host := [1, 0], path := [5, 6], https := true, hostIsIp := false }

-- A host-only cookie for the exact origin IS sent.
example :
    cookieMatches
      { name := 1, value := 1, domain := [1, 0], path := [], secure := false, hostOnly := true }
      secureReq = true := by decide
-- A DOMAIN cookie for example.com IS sent to sub.example.com.
example :
    cookieMatches
      { name := 1, value := 1, domain := [1, 0], path := [], secure := false, hostOnly := false }
      { host := [2, 1, 0], path := [5], https := true, hostIsIp := false } = true := by decide
-- A cookie for evil.test is NEVER sent to example.com (cross-domain).
example :
    cookieMatches
      { name := 1, value := 1, domain := [9, 8], path := [], secure := false, hostOnly := false }
      secureReq = false := by decide
-- A host-only cookie for example.com is NOT sent to sub.example.com.
example :
    cookieMatches
      { name := 1, value := 1, domain := [1, 0], path := [], secure := false, hostOnly := true }
      { host := [2, 1, 0], path := [], https := true, hostIsIp := false } = false := by decide
-- A Secure cookie is NOT sent over plain HTTP.
example :
    cookieMatches
      { name := 1, value := 1, domain := [1, 0], path := [], secure := true, hostOnly := true }
      { host := [1, 0], path := [], https := false, hostIsIp := false } = false := by decide
-- A path-scoped cookie for /a/b is NOT sent to /a (prefix must be the cookie's).
example :
    cookieMatches
      { name := 1, value := 1, domain := [1, 0], path := [5, 6], secure := false, hostOnly := true }
      { host := [1, 0], path := [5], https := true, hostIsIp := false } = false := by decide
-- A cookie whose domain is a suffix but the host is an IP literal is NOT sent.
example :
    cookieMatches
      { name := 1, value := 1, domain := [3, 4], path := [], secure := false, hostOnly := false }
      { host := [1, 2, 3, 4], path := [], https := true, hostIsIp := true } = false := by decide

end Client.Session
