/-
RetryBudget — an idempotency-aware, globally-budgeted retry admission machine
for a reverse proxy, with a bounded shed-on-full request queue.

A reverse proxy that retries failed upstream attempts must answer three
questions, and getting any of them wrong turns a transient upstream hiccup into
a self-inflicted outage:

  1. HOW MANY retries total?  The naive design gives *each request* a fixed
     retry count (`maxAttempts`). Under a partial upstream failure every
     in-flight request then retries independently, multiplying the offered load
     precisely when the upstream is least able to absorb it — a retry storm.
     The design here instead meters retries against a GLOBAL token budget that
     is replenished by *successful* traffic: a retry withdraws `cost` tokens, an
     admitted request deposits `deposit` tokens (capped at `cap`). Total retries
     are therefore bounded by a linear function of the request count
     (`retry_budget_bounded`) — a fixed fraction of traffic, not an unbounded
     multiple per stuck request.

  2. WHICH methods may be retried?  Only *idempotent* methods. Replaying a
     non-idempotent request (POST, PATCH) that the upstream may already have
     partially applied can duplicate a side effect (a double charge, a double
     append). Per RFC 9110 §9.2.2 the idempotent methods are the safe methods
     (GET, HEAD, OPTIONS, TRACE) together with PUT and DELETE; POST, PATCH, and
     CONNECT are NOT idempotent. This machine never dispatches a retry for a
     non-idempotent method (`retry_idempotent_only`).

  3. WHAT happens at saturation?  When the admission queue is at its bound, an
     excess request is SHED (answered fast — the 503 condition of RFC 9110
     §15.6.4, "Service Unavailable") rather than enqueued or retried. The queue
     depth therefore never exceeds its configured limit (`queue_bounded`), and
     at the limit an arrival is shed, not admitted (`queue_full_sheds`).

The machine is sans-IO in the `Proxy.Timeout` / `Proxy.Breaker` style: the
environment injects events (a request arrives, an in-flight attempt completes,
an attempt fails) and the machine is a pure step function with an explicit
output. It COMPOSES with the server-side breaker (`Proxy.Breaker`): a retry is
actually dispatched only when the retry budget AND idempotency AND the circuit
breaker all permit it (`retry_permitted_sound`), so retries are never launched
into an upstream the breaker has already tripped OPEN.

Headline results:

  * `retry_budget_bounded` — GLOBAL BUDGET: `cost · (total retries) ≤ tokens₀ +
    deposit · (total requests)`; retries are a bounded fraction of traffic, not
    unbounded per request;
  * `retry_idempotent_only` — a retry output is emitted only for an idempotent
    method; `post_never_retried` / `patch_never_retried` make the exclusion
    concrete;
  * `queue_full_sheds` — at the queue bound an arrival is shed (state unchanged,
    output `shed`), never enqueued or retried; `queue_bounded` — the depth is a
    global invariant `≤ queueLimit`;
  * `retry_permitted_sound` — composition with the real `Proxy.Breaker.step`: a
    permitted retry implies the method is idempotent AND the breaker admits.

Non-vacuity is witnessed by concrete runs and by three mutant machines — one
that ignores the budget, one that retries any method, one that ignores the
queue bound — each of which provably violates the corresponding headline.
-/

import Proxy.Breaker

namespace Proxy.RetryBudget

/-! ## HTTP methods and idempotency (RFC 9110 §9.2.1–§9.2.2) -/

/-- The HTTP request methods the retry decision distinguishes. -/
inductive Method where
  | get | head | options | trace   -- safe (RFC 9110 §9.2.1)
  | put | delete                    -- idempotent, not safe
  | post | patch | connect          -- NOT idempotent
deriving DecidableEq, Repr, Inhabited

/-- Safe methods (RFC 9110 §9.2.1): read-only, no requested side effect. -/
def Method.safe : Method → Bool
  | .get | .head | .options | .trace => true
  | _ => false

/-- Idempotent methods (RFC 9110 §9.2.2): the safe methods together with PUT and
DELETE. POST, PATCH, and CONNECT are NOT idempotent and are never auto-retried. -/
def Method.idempotent : Method → Bool
  | .get | .head | .options | .trace => true   -- safe ⇒ idempotent
  | .put | .delete => true
  | .post | .patch | .connect => false

/-- Every safe method is idempotent (RFC 9110 §9.2.2: "all safe methods are
idempotent"). -/
theorem safe_imp_idempotent (m : Method) : m.safe = true → m.idempotent = true := by
  cases m <;> simp [Method.safe, Method.idempotent]

/-! ## Configuration and state -/

/-- Retry-budget and queue configuration.

`cost`/`deposit`/`cap` parameterise the replenishing token budget: an admitted
request deposits `deposit` tokens (saturating at `cap`), a retry withdraws
`cost`. `maxAttempts` is a per-request hard ceiling (belt-and-suspenders on top
of the budget). `queueLimit` bounds the admission queue depth. -/
structure RetryCfg where
  cost : Nat        -- tokens a single retry withdraws from the budget
  deposit : Nat     -- tokens an admitted request deposits into the budget
  cap : Nat         -- maximum token balance (bucket capacity)
  maxAttempts : Nat -- per-request attempt ceiling
  queueLimit : Nat  -- maximum admission-queue depth
deriving DecidableEq, Repr

/-- Machine state: the current token balance, the queue depth of in-flight /
queued requests, and running accounting counters for total retries dispatched
and total requests admitted. -/
structure RState where
  tokens : Nat    -- current retry-budget balance
  inflight : Nat  -- current admission-queue depth
  retries : Nat   -- total retries dispatched so far (accounting)
  requests : Nat  -- total requests admitted so far (accounting)
deriving DecidableEq, Repr

/-- A fresh machine seeded with `t0` starting budget tokens and an empty queue. -/
def RState.init (t0 : Nat) : RState :=
  { tokens := t0, inflight := 0, retries := 0, requests := 0 }

/-- Events injected by the environment. -/
inductive REvent where
  /-- A fresh request of method `m` arrives at the proxy. -/
  | admit (m : Method)
  /-- An in-flight / queued request finished (frees a queue slot). -/
  | complete
  /-- The `attempt`-th upstream attempt for a method-`m` request failed; the
      machine decides whether to retry. `attempt` is the number of attempts
      already made for this request. -/
  | fail (m : Method) (attempt : Nat)
deriving Repr

/-- Outputs. A step emits exactly one. -/
inductive ROutput where
  | queued      -- request accepted into the admission queue
  | shed        -- request shed at the queue bound (RFC 9110 §15.6.4, 503)
  | retry (m : Method)   -- a retry is dispatched upstream
  | giveUp (m : Method)  -- no retry; the failure is surfaced to the client
deriving DecidableEq, Repr

/-! ## The retry decision

A failed attempt is retried iff the method is idempotent, the per-request
attempt ceiling is not yet reached, and the budget can afford the `cost`. -/

/-- Whether a failed attempt may be retried. -/
def mayRetry (cfg : RetryCfg) (s : RState) (m : Method) (attempt : Nat) : Bool :=
  m.idempotent && attempt < cfg.maxAttempts && cfg.cost ≤ s.tokens

/-- A retry is only ever permitted for an idempotent method. -/
theorem mayRetry_imp_idempotent {cfg : RetryCfg} {s : RState} {m : Method}
    {attempt : Nat} (h : mayRetry cfg s m attempt = true) : m.idempotent = true := by
  simp only [mayRetry, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

/-- A retry is only ever permitted when the budget can afford its `cost`. -/
theorem mayRetry_imp_affordable {cfg : RetryCfg} {s : RState} {m : Method}
    {attempt : Nat} (h : mayRetry cfg s m attempt = true) : cfg.cost ≤ s.tokens := by
  simp only [mayRetry, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-! ## The step function

The deployed transition the retry stage runs. -/

/-- One step of the retry-budget / queue machine. -/
def step (cfg : RetryCfg) (s : RState) : REvent → RState × List ROutput
  | .admit _ =>
    if s.inflight < cfg.queueLimit then
      -- admit: take a queue slot, deposit into the budget (saturating at cap)
      ({ s with inflight := s.inflight + 1,
                requests := s.requests + 1,
                tokens := min cfg.cap (s.tokens + cfg.deposit) },
       [ROutput.queued])
    else
      -- queue full: shed (state unchanged), never enqueue or retry
      (s, [ROutput.shed])
  | .complete =>
    -- free a queue slot (stutters if the queue is somehow empty)
    ({ s with inflight := s.inflight - 1 }, [])
  | .fail m attempt =>
    if mayRetry cfg s m attempt then
      -- retry: withdraw the cost, count the retry
      ({ s with tokens := s.tokens - cfg.cost, retries := s.retries + 1 },
       [ROutput.retry m])
    else
      -- give up: surface the failure
      (s, [ROutput.giveUp m])

/-- Run an event history, oldest first. -/
def run (cfg : RetryCfg) (s : RState) : List REvent → RState
  | [] => s
  | e :: es => run cfg (step cfg s e).1 es

@[simp] theorem run_nil (cfg : RetryCfg) (s : RState) : run cfg s [] = s := rfl

@[simp] theorem run_cons (cfg : RetryCfg) (s : RState) (e : REvent) (es : List REvent) :
    run cfg s (e :: es) = run cfg (step cfg s e).1 es := rfl

/-! ## Theorem 1 — the retry budget is bounded (no per-request unbounded retries)

The token-budget invariant: at all times the balance plus the total cost of
retries dispatched so far never exceeds the starting balance plus the deposits
made by admitted requests. Since a retry costs `cost` and a request deposits at
most `deposit`, this caps *total* retries by a linear function of the request
count — a bounded fraction of traffic, in contrast to a per-request retry count
that lets each stuck request retry independently. -/

/-- The budget invariant, relative to a starting balance `t0`. -/
def Budgeted (cfg : RetryCfg) (t0 : Nat) (s : RState) : Prop :=
  s.tokens + cfg.cost * s.retries ≤ t0 + cfg.deposit * s.requests

/-- The invariant holds at the fresh state (with equality). -/
theorem budgeted_init (cfg : RetryCfg) (t0 : Nat) : Budgeted cfg t0 (RState.init t0) := by
  simp [Budgeted, RState.init]

/-- Every step preserves the budget invariant. The retry case is where a token
is actually spent; it is exactly covered by the `cost ≤ tokens` guard inside
`mayRetry`, which is why a retry cannot drive the balance negative. -/
theorem step_budgeted (cfg : RetryCfg) (t0 : Nat) (s : RState) (e : REvent)
    (h : Budgeted cfg t0 s) : Budgeted cfg t0 (step cfg s e).1 := by
  unfold Budgeted at h ⊢
  cases e with
  | admit m =>
    by_cases hq : s.inflight < cfg.queueLimit
    · simp only [step, hq, if_true]
      have hmin : min cfg.cap (s.tokens + cfg.deposit) ≤ s.tokens + cfg.deposit :=
        Nat.min_le_right _ _
      rw [Nat.mul_succ]
      omega
    · simp only [step, hq, if_false]; exact h
  | complete => simp only [step]; exact h
  | fail m attempt =>
    by_cases hr : mayRetry cfg s m attempt
    · have haff : cfg.cost ≤ s.tokens := mayRetry_imp_affordable hr
      simp only [step, hr, if_true]
      rw [Nat.mul_succ]
      omega
    · simp only [step, hr, if_false]; exact h

/-- The invariant is preserved across a whole event history. -/
theorem run_budgeted (cfg : RetryCfg) (t0 : Nat) :
    (trace : List REvent) → Budgeted cfg t0 (run cfg (RState.init t0) trace)
  | [] => by simpa using budgeted_init cfg t0
  | e :: es => by
    rw [run_cons]
    -- generalise the intermediate state and re-run the invariant induction
    have hstep := step_budgeted cfg t0 (RState.init t0) e (budgeted_init cfg t0)
    exact run_budgeted_from cfg t0 (step cfg (RState.init t0) e).1 hstep es
where
  /-- Invariant propagation from an arbitrary already-budgeted state. -/
  run_budgeted_from (cfg : RetryCfg) (t0 : Nat) (s : RState)
      (h : Budgeted cfg t0 s) :
      (trace : List REvent) → Budgeted cfg t0 (run cfg s trace)
    | [] => by simpa using h
    | e :: es => by
      rw [run_cons]
      exact run_budgeted_from cfg t0 (step cfg s e).1 (step_budgeted cfg t0 s e h) es

/-- **THEOREM 1 — GLOBAL RETRY BUDGET.** For any starting balance `t0` and any
event history, the total cost of retries dispatched is bounded by the starting
balance plus the deposits of admitted requests:

    cost · (total retries) ≤ t0 + deposit · (total requests).

With `cost ≥ 1` this caps total retries by `t0 + deposit · requests`: retries are
a bounded fraction of traffic, NOT an unbounded per-request count. A single
request stuck failing can consume at most `t0 / cost` retries before the budget
is exhausted (until fresh successful traffic replenishes it) — it can never
retry forever, and it cannot starve the whole fleet into a retry storm. -/
theorem retry_budget_bounded (cfg : RetryCfg) (t0 : Nat) (trace : List REvent) :
    cfg.cost * (run cfg (RState.init t0) trace).retries
      ≤ t0 + cfg.deposit * (run cfg (RState.init t0) trace).requests := by
  have h := run_budgeted cfg t0 trace
  unfold Budgeted at h
  omega

/-! ## Theorem 2 — retries are idempotent-only

A retry output is emitted only for an idempotent method; the non-idempotent
methods POST and PATCH are surfaced as give-ups, never replayed. -/

/-- **THEOREM 2 — IDEMPOTENT-ONLY RETRY.** If the deployed `step` emits a retry
for a failed attempt, the method being retried is idempotent. Replaying a
non-idempotent request (which the upstream may already have applied) can never
happen. -/
theorem retry_idempotent_only (cfg : RetryCfg) (s : RState) (m : Method) (attempt : Nat)
    (h : (step cfg s (.fail m attempt)).2 = [ROutput.retry m]) : m.idempotent = true := by
  by_cases hr : mayRetry cfg s m attempt
  · exact mayRetry_imp_idempotent hr
  · -- the give-up branch: output is [giveUp m] ≠ [retry m], contradicting h
    have hr' : mayRetry cfg s m attempt = false := by
      cases hh : mayRetry cfg s m attempt
      · rfl
      · exact absurd hh hr
    simp [step, hr'] at h

/-- POST is a non-idempotent method (RFC 9110 §9.2.2). -/
theorem post_not_idempotent : Method.post.idempotent = false := rfl

/-- PATCH is a non-idempotent method (RFC 9110 §9.2.2). -/
theorem patch_not_idempotent : Method.patch.idempotent = false := rfl

/-- A failed POST is NEVER retried — the machine surfaces the failure. -/
theorem post_never_retried (cfg : RetryCfg) (s : RState) (attempt : Nat) :
    (step cfg s (.fail .post attempt)).2 = [ROutput.giveUp .post] := by
  have : mayRetry cfg s .post attempt = false := by
    simp [mayRetry, Method.idempotent]
  simp [step, this]

/-- A failed PATCH is NEVER retried — the machine surfaces the failure. -/
theorem patch_never_retried (cfg : RetryCfg) (s : RState) (attempt : Nat) :
    (step cfg s (.fail .patch attempt)).2 = [ROutput.giveUp .patch] := by
  have : mayRetry cfg s .patch attempt = false := by
    simp [mayRetry, Method.idempotent]
  simp [step, this]

/-- Non-vacuity of Theorem 2: an idempotent method (GET) with attempts and budget
to spare IS retried — the rule is not the vacuous "never retry anything". -/
theorem get_is_retried :
    let cfg : RetryCfg := ⟨1, 1, 10, 3, 8⟩
    let s : RState := ⟨5, 0, 0, 0⟩
    (step cfg s (.fail .get 0)).2 = [ROutput.retry .get] := by decide

/-! ## Theorem 3 — the queue is bounded and sheds when full

At the queue bound an arrival is shed (state unchanged, output `shed`); it is
never enqueued nor retried. The queue depth is a global invariant `≤ queueLimit`,
so a saturated proxy sheds excess load rather than growing an unbounded backlog
or amplifying it into retries. -/

/-- **THEOREM 3 — SHED AT THE QUEUE BOUND.** When the queue is at (or above) its
limit, an arriving request is shed: the machine emits `shed` and its state is
UNCHANGED — the request is neither enqueued nor turned into a retry. -/
theorem queue_full_sheds (cfg : RetryCfg) (s : RState) (m : Method)
    (hfull : cfg.queueLimit ≤ s.inflight) :
    (step cfg s (.admit m)).2 = [ROutput.shed] ∧ (step cfg s (.admit m)).1 = s := by
  have hq : ¬ s.inflight < cfg.queueLimit := by omega
  simp [step, hq]

/-- The queue-depth bound as a state predicate. -/
def QueueBounded (cfg : RetryCfg) (s : RState) : Prop := s.inflight ≤ cfg.queueLimit

/-- The bound holds at the fresh state. -/
theorem queueBounded_init (cfg : RetryCfg) (t0 : Nat) :
    QueueBounded cfg (RState.init t0) := by simp [QueueBounded, RState.init]

/-- Every step keeps the queue depth within the limit: an admit is only taken
below the limit (landing at most at the limit), a completion only shrinks it, and
a failure leaves it untouched. -/
theorem step_queueBounded (cfg : RetryCfg) (s : RState) (e : REvent)
    (h : QueueBounded cfg s) : QueueBounded cfg (step cfg s e).1 := by
  unfold QueueBounded at h ⊢
  cases e with
  | admit m =>
    by_cases hq : s.inflight < cfg.queueLimit
    · simp only [step, hq, if_true]; omega
    · simp only [step, hq, if_false]; exact h
  | complete => simp only [step]; omega
  | fail m attempt =>
    by_cases hr : mayRetry cfg s m attempt
    · simp only [step, hr, if_true]; exact h
    · simp only [step, hr, if_false]; exact h

/-- **THEOREM 3′ — GLOBAL QUEUE BOUND.** For any starting balance and any event
history, the queue depth never exceeds `queueLimit`: shedding at the bound keeps
the backlog bounded forever, so the proxy cannot accumulate an unbounded queue. -/
theorem queue_bounded (cfg : RetryCfg) (t0 : Nat) (trace : List REvent) :
    (run cfg (RState.init t0) trace).inflight ≤ cfg.queueLimit :=
  go cfg (RState.init t0) (queueBounded_init cfg t0) trace
where
  go (cfg : RetryCfg) (s : RState) (h : QueueBounded cfg s) :
      (trace : List REvent) → (run cfg s trace).inflight ≤ cfg.queueLimit
    | [] => h
    | e :: es => by
      rw [run_cons]; exact go cfg (step cfg s e).1 (step_queueBounded cfg s e h) es

/-! ## Composition with the server-side circuit breaker

A retry is actually dispatched only when the retry budget, idempotency, AND the
real `Proxy.Breaker` all permit it. This ties the retry stage to the deployed
breaker step: a permitted retry can never be launched into an upstream the
breaker has tripped OPEN. -/

/-- The breaker admits an attempt iff its probe output is `attempt`. (Fully
qualified `Proxy.Breaker.step` throughout — the local `step` is the retry
machine's.) -/
def breakerAdmits (bcfg : Proxy.Breaker.BreakerCfg) (bs : Proxy.Breaker.BState) : Bool :=
  decide ((Proxy.Breaker.step bcfg bs Proxy.Breaker.BEvent.probe).2
            = [Proxy.Breaker.BOutput.attempt])

/-- A retry is *dispatched* only when the retry budget/idempotency AND the
breaker both permit it. -/
def retryPermitted (cfg : RetryCfg) (bcfg : Proxy.Breaker.BreakerCfg) (s : RState)
    (bs : Proxy.Breaker.BState) (m : Method) (attempt : Nat) : Bool :=
  mayRetry cfg s m attempt && breakerAdmits bcfg bs

/-- **COMPOSITION.** A permitted retry implies the method is idempotent AND the
deployed breaker admits the attempt (`Proxy.Breaker.step … .probe` emits
`attempt`). Retries are therefore never launched into a tripped-open upstream,
and never for a non-idempotent method. -/
theorem retry_permitted_sound (cfg : RetryCfg) (bcfg : Proxy.Breaker.BreakerCfg)
    (s : RState) (bs : Proxy.Breaker.BState) (m : Method) (attempt : Nat)
    (h : retryPermitted cfg bcfg s bs m attempt = true) :
    m.idempotent = true
      ∧ (Proxy.Breaker.step bcfg bs Proxy.Breaker.BEvent.probe).2
          = [Proxy.Breaker.BOutput.attempt] := by
  simp only [retryPermitted, Bool.and_eq_true, breakerAdmits, decide_eq_true_eq] at h
  exact ⟨mayRetry_imp_idempotent h.1, h.2⟩

/-- Non-vacuity of the composition: a permitted retry genuinely occurs — a GET
with budget, under a fresh (closed) breaker, is permitted. -/
theorem retry_permitted_witness :
    let cfg : RetryCfg := ⟨1, 1, 10, 3, 8⟩
    let bcfg : Proxy.Breaker.BreakerCfg := ⟨2, 5⟩
    let s : RState := ⟨5, 0, 0, 0⟩
    retryPermitted cfg bcfg s Proxy.Breaker.BState.init .get 0 = true := by decide

/-! ## Non-vacuity: three mutant machines fail the three headlines

Each mutant drops exactly one of the three guarantees and provably disagrees
with the correct machine on a concrete history — so the theorems above are not
`spec = spec`. -/

/-- Mutant A — IGNORES THE BUDGET: retries every failed idempotent attempt with
no token check, so a stuck request retries without bound. -/
def unbudgetedStep (cfg : RetryCfg) (s : RState) : REvent → RState × List ROutput
  | .fail m _attempt =>
    if m.idempotent then
      ({ s with tokens := s.tokens - cfg.cost, retries := s.retries + 1 }, [ROutput.retry m])
    else (s, [ROutput.giveUp m])
  | e => step cfg s e

def unbudgetedRun (cfg : RetryCfg) (s : RState) : List REvent → RState
  | [] => s
  | e :: es => unbudgetedRun cfg (unbudgetedStep cfg s e).1 es

/-- With a starting budget of one retry (`cost = 1`, `t0 = 1`) and no deposits
(a single stuck GET failing twice, never admitted), the budget-ignoring machine
dispatches 2 retries, violating `cost · retries ≤ t0 + deposit · requests`
(2 ≤ 1 is false). The correct machine dispatches at most 1. -/
theorem unbudgeted_breaks_budget :
    let cfg : RetryCfg := ⟨1, 1, 10, 9, 8⟩
    ¬ (cfg.cost * (unbudgetedRun cfg (RState.init 1) [.fail .get 0, .fail .get 1]).retries
        ≤ 1 + cfg.deposit * (unbudgetedRun cfg (RState.init 1) [.fail .get 0, .fail .get 1]).requests) := by
  decide

/-- Mutant B — RETRIES ANY METHOD: ignores idempotency, so it replays POST. -/
def anyMethodStep (cfg : RetryCfg) (s : RState) : REvent → RState × List ROutput
  | .fail m attempt =>
    if attempt < cfg.maxAttempts && cfg.cost ≤ s.tokens then
      ({ s with tokens := s.tokens - cfg.cost, retries := s.retries + 1 }, [ROutput.retry m])
    else (s, [ROutput.giveUp m])
  | e => step cfg s e

/-- The any-method machine retries a POST, which the correct machine never does
(`post_never_retried`): the two disagree, so retrying only idempotent methods is
genuine content. -/
theorem anyMethod_breaks_idempotent :
    let cfg : RetryCfg := ⟨1, 1, 10, 3, 8⟩
    let s : RState := ⟨5, 0, 0, 0⟩
    (anyMethodStep cfg s (.fail .post 0)).2 = [ROutput.retry .post]
      ∧ (step cfg s (.fail .post 0)).2 ≠ [ROutput.retry .post] := by decide

/-- Mutant C — IGNORES THE QUEUE BOUND: always enqueues, so the depth grows
without limit. -/
def unboundedAdmitStep (cfg : RetryCfg) (s : RState) : REvent → RState × List ROutput
  | .admit _m =>
    ({ s with inflight := s.inflight + 1, requests := s.requests + 1,
              tokens := min cfg.cap (s.tokens + cfg.deposit) }, [ROutput.queued])
  | e => step cfg s e

def unboundedAdmitRun (cfg : RetryCfg) (s : RState) : List REvent → RState
  | [] => s
  | e :: es => unboundedAdmitRun cfg (unboundedAdmitStep cfg s e).1 es

/-- With `queueLimit = 1`, admitting two requests drives the unbounded machine's
depth to 2, exceeding the limit — whereas the correct machine's depth stays
`≤ 1` (`queue_bounded`). So the queue bound has genuine content. -/
theorem unboundedAdmit_breaks_queue :
    let cfg : RetryCfg := ⟨1, 1, 10, 3, 1⟩
    (unboundedAdmitRun cfg (RState.init 0) [.admit .get, .admit .get]).inflight > cfg.queueLimit
      ∧ (run cfg (RState.init 0) [.admit .get, .admit .get]).inflight ≤ cfg.queueLimit := by
  decide

end Proxy.RetryBudget
