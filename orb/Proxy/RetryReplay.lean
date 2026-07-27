/-
RetryReplay — safety of REPLAYING a failed upstream attempt onto another backend.

`Proxy.RetryBudget` answers *how many* retries the proxy may dispatch and *which
methods* are eligible. This module is the next depth: once the budget/idempotency
gate has said "a retry is allowed", the proxy must actually RE-SEND the request to
a different backend, and re-sending is where a reverse proxy silently corrupts a
request if it is careless. Three failure modes, three theorems:

  1. REPLAY TO ANOTHER BACKEND ONLY IF IDEMPOTENT.  A failed attempt is re-sent
     to the *next* backend only when the method is idempotent (RFC 9110 §9.2.2:
     GET/HEAD/OPTIONS/TRACE, plus PUT/DELETE). A POST or PATCH the first backend
     may already have partially applied is NEVER replayed onto a second backend —
     that would double the side effect on a different origin. This is
     `retry_replay_idempotent_only`: whenever the attempt history has length ≥ 2
     (a replay genuinely occurred), the method is idempotent.

  2. THE REPLAYED BODY IS THE SAME BOUNDED BYTES — NOT A CONSUMED STREAM.  To
     replay a request the proxy must resend its body, but the client body is a
     one-shot stream: once forwarded to the first backend it is gone. The only
     way to replay it is to have BUFFERED it. So a request is replay-eligible
     only if its body was fully captured within the buffer bound
     (`body.length ≤ limit`); a body larger than the bound was streamed through
     and cannot be replayed. Every attempt in the history therefore carries
     *exactly* the buffered bytes `r.body` (`retry_replay_body_bounded`, part 1 —
     same bytes, never re-read from a consumed stream), and whenever a replay
     occurred those bytes are within the bound (part 2 — bounded).

  3. THE CLIENT SEES THE LAST ATTEMPT'S STATUS.  A replay only makes sense if the
     client is answered with the FINAL attempt's status, not the first (failed)
     one — otherwise the retry is pointless. `retry_preserves_status`: the served
     status equals the status of the last attempt in the history. A GET that gets
     503 from backend A then 200 from backend B answers the client 200.

The engine is sans-IO in the `Proxy.RetryBudget` style: the environment is a pure
oracle `env : backend → body → status` (what each backend answers for a given
body), and `replayRun` is the pure dispatch history for a request against an
ordered list of candidate backends. The failing/succeeding distinction is the
5xx-server-failure condition of RFC 9110 §15.6 (a status ≥ 500 is retriable).

Non-vacuity: `replay_witness` exhibits a real 2-backend replay (503 then 200,
served 200, distinct backends); `post_never_replayed` shows the correct engine
makes a single attempt for a failing POST; and `post_replay_mutant` exhibits an
idempotency-blind engine that DOES replay the POST — so the idempotency guard is
genuine content, not `spec = spec`.
-/

import Proxy.RetryBudget

namespace Proxy.RetryReplay

open Proxy.RetryBudget (Method)

/-! ## Request, attempt, and the replay engine -/

/-- A request the proxy may need to replay: its HTTP method and its (buffered)
body bytes. The body carried here is what the proxy captured — see `replayable`
for when that capture is complete enough to permit a replay. -/
structure Request where
  method : Method
  body : List UInt8
deriving Repr

/-- One upstream dispatch: the backend it went to, the body bytes actually sent,
and the status the backend returned. -/
structure Attempt where
  backend : Nat
  body : List UInt8
  status : Nat
deriving Repr, DecidableEq

/-- A status is a retriable server failure iff it is ≥ 500 (RFC 9110 §15.6). -/
def isFailure (status : Nat) : Bool := decide (500 ≤ status)

/-- A request is replay-eligible iff (a) its method is idempotent (RFC 9110
§9.2.2 — replaying a non-idempotent method could duplicate a side effect on a
different backend) AND (b) its body was fully buffered within the bound
`limit`. A body longer than `limit` was streamed through to the first backend and
is gone; it cannot be re-sent, so it is not replayable. -/
def replayable (limit : Nat) (r : Request) : Bool :=
  r.method.idempotent && decide (r.body.length ≤ limit)

/-- The dispatch history for `r` against an ordered candidate-backend list.

Each candidate `b` is sent the SAME buffered bytes `r.body` (never re-read from a
consumed stream). If that attempt is a server failure, the request is replayable,
and there is a next backend, the failure is replayed onto it; otherwise the
history ends at this attempt (success, non-replayable, or backends exhausted). -/
def replayRun (limit : Nat) (env : Nat → List UInt8 → Nat) (r : Request) :
    List Nat → List Attempt
  | [] => []
  | b :: bs =>
    if isFailure (env b r.body) && replayable limit r && !bs.isEmpty then
      { backend := b, body := r.body, status := env b r.body }
        :: replayRun limit env r bs
    else
      [{ backend := b, body := r.body, status := env b r.body }]

/-- The status served to the client: the status of the terminal attempt, tracked
directly by the same recursion `replayRun` uses to decide when to stop. -/
def finalStatus (limit : Nat) (env : Nat → List UInt8 → Nat) (r : Request) :
    List Nat → Option Nat
  | [] => none
  | b :: bs =>
    if isFailure (env b r.body) && replayable limit r && !bs.isEmpty then
      finalStatus limit env r bs
    else
      some (env b r.body)

/-! ## Structural facts about the dispatch history -/

/-- A dispatch against a non-empty candidate list always makes at least one
attempt. -/
theorem replayRun_ne_nil (limit : Nat) (env : Nat → List UInt8 → Nat) (r : Request) :
    ∀ (plan : List Nat), plan ≠ [] → replayRun limit env r plan ≠ []
  | [], h => absurd rfl h
  | b :: bs, _ => by
    unfold replayRun
    split <;> simp

/-- The backends actually tried form a PREFIX of the candidate list: attempt `i`
goes to candidate `i`. Hence when the candidate list has distinct entries, every
replay goes to a genuinely different backend. -/
theorem replayRun_backends_prefix (limit : Nat) (env : Nat → List UInt8 → Nat)
    (r : Request) :
    ∀ (plan : List Nat), (replayRun limit env r plan).map (·.backend) <+: plan
  | [] => by simp [replayRun]
  | b :: bs => by
    unfold replayRun
    split
    · -- replayed: b :: (prefix of bs)
      obtain ⟨t, ht⟩ := replayRun_backends_prefix limit env r bs
      refine ⟨t, ?_⟩
      simp only [List.map_cons]
      rw [List.cons_append, ht]
    · -- single attempt onto b
      exact ⟨bs, rfl⟩

/-- Every attempt in the history carries exactly the buffered bytes `r.body`:
the body is never re-read from the (already consumed) client stream. -/
theorem replayRun_body (limit : Nat) (env : Nat → List UInt8 → Nat) (r : Request) :
    ∀ (plan : List Nat), ∀ x ∈ replayRun limit env r plan, x.body = r.body
  | [], x, hx => by simp [replayRun] at hx
  | b :: bs, x, hx => by
    unfold replayRun at hx
    split at hx
    · rcases List.mem_cons.1 hx with h | h
      · subst h; rfl
      · exact replayRun_body limit env r bs x h
    · rw [List.mem_singleton] at hx; subst hx; rfl

/-- A replay actually happened (≥ 2 attempts) only if the request was
replay-eligible. -/
theorem replay_needs_replayable (limit : Nat) (env : Nat → List UInt8 → Nat)
    (r : Request) (plan : List Nat)
    (h : 2 ≤ (replayRun limit env r plan).length) : replayable limit r = true := by
  cases plan with
  | nil => simp [replayRun] at h
  | cons b bs =>
    unfold replayRun at h
    split at h
    · rename_i hg
      simp only [Bool.and_eq_true] at hg
      exact hg.1.2
    · simp at h

/-! ## Headline 1 — replay to another backend only if idempotent -/

/-- **REPLAY IS IDEMPOTENT-ONLY.** If the proxy replayed a failed attempt onto a
further backend (the history has length ≥ 2), the method is idempotent. A POST or
PATCH — which the first backend may already have applied — is never replayed onto
a second backend. -/
theorem retry_replay_idempotent_only (limit : Nat) (env : Nat → List UInt8 → Nat)
    (r : Request) (plan : List Nat)
    (h : 2 ≤ (replayRun limit env r plan).length) : r.method.idempotent = true := by
  have hr := replay_needs_replayable limit env r plan h
  simp only [replayable, Bool.and_eq_true] at hr
  exact hr.1

/-! ## Headline 2 — the replayed body is the same bounded bytes -/

/-- **REPLAYED BODY IS THE SAME BOUNDED BYTES.** (1) Every attempt sends exactly
the buffered bytes `r.body`, never re-reading a consumed stream; (2) whenever a
replay occurred, those bytes were within the buffer bound `limit`. -/
theorem retry_replay_body_bounded (limit : Nat) (env : Nat → List UInt8 → Nat)
    (r : Request) (plan : List Nat) :
    (∀ x ∈ replayRun limit env r plan, x.body = r.body)
      ∧ (2 ≤ (replayRun limit env r plan).length → r.body.length ≤ limit) := by
  refine ⟨replayRun_body limit env r plan, ?_⟩
  intro h
  have hr := replay_needs_replayable limit env r plan h
  simp only [replayable, Bool.and_eq_true, decide_eq_true_eq] at hr
  exact hr.2

/-! ## Headline 3 — the client sees the last attempt's status -/

/-- Popping the head off a ≥ 1-length list does not change its last element. -/
theorem getLast?_cons_ne {α} (a : α) :
    ∀ (l : List α), l ≠ [] → (a :: l).getLast? = l.getLast?
  | [], h => absurd rfl h
  | _ :: _, _ => rfl

/-- **FINAL STATUS IS THE LAST ATTEMPT.** The status served to the client equals
the status of the last attempt in the dispatch history — the successful replay,
not the first failure. -/
theorem retry_preserves_status (limit : Nat) (env : Nat → List UInt8 → Nat)
    (r : Request) :
    ∀ (plan : List Nat),
      finalStatus limit env r plan
        = (replayRun limit env r plan).getLast?.map (·.status)
  | [] => by simp [finalStatus, replayRun]
  | b :: bs => by
    by_cases hg : (isFailure (env b r.body) && replayable limit r && !bs.isEmpty) = true
    · have hne : bs ≠ [] := by intro hb; subst hb; simp at hg
      have hfin : finalStatus limit env r (b :: bs) = finalStatus limit env r bs := by
        simp only [finalStatus]; rw [if_pos hg]
      have hrun : replayRun limit env r (b :: bs)
          = { backend := b, body := r.body, status := env b r.body } :: replayRun limit env r bs := by
        simp only [replayRun]; rw [if_pos hg]
      rw [hfin, hrun, getLast?_cons_ne _ _ (replayRun_ne_nil limit env r bs hne)]
      exact retry_preserves_status limit env r bs
    · have hg' : ¬ ((isFailure (env b r.body) && replayable limit r && !bs.isEmpty) = true) := hg
      have hfin : finalStatus limit env r (b :: bs) = some (env b r.body) := by
        simp only [finalStatus]; rw [if_neg hg']
      have hrun : replayRun limit env r (b :: bs)
          = [{ backend := b, body := r.body, status := env b r.body }] := by
        simp only [replayRun]; rw [if_neg hg']
      rw [hfin, hrun]; rfl

/-! ## Non-vacuity: a real replay, and the POST exclusion is genuine content

`witnessEnv`: backend 7 fails everything with 503, backend 9 succeeds with 200. -/

/-- Oracle used by the witnesses: backend 7 → 503 (fail), any other → 200 (ok). -/
def witnessEnv : Nat → List UInt8 → Nat := fun b _ => if b == 7 then 503 else 200

/-- **NON-VACUITY.** A GET whose body is buffered within bound is replayed off the
failing backend 7 onto backend 9: the history has two attempts to DISTINCT
backends, the first status is the 503 failure, and the client is served the
second attempt's 200. So the replay machinery genuinely fires. -/
theorem replay_witness :
    let r : Request := ⟨.get, [1, 2, 3]⟩
    let hist := replayRun 100 witnessEnv r [7, 9]
    hist.length = 2
      ∧ hist.map (·.backend) = [7, 9]
      ∧ (hist[0]?).map (·.status) = some 503
      ∧ finalStatus 100 witnessEnv r [7, 9] = some 200 := by
  decide

/-- **POST IS NOT REPLAYED.** The correct engine makes a SINGLE attempt for a
failing POST (backend 7 → 503) even though a second backend is available: the
failure is surfaced, not replayed. -/
theorem post_never_replayed :
    let r : Request := ⟨.post, [1, 2, 3]⟩
    (replayRun 100 witnessEnv r [7, 9]).length = 1
      ∧ finalStatus 100 witnessEnv r [7, 9] = some 503 := by
  decide

/-- Mutant engine that ignores idempotency: it replays on failure whenever the
body is buffered, regardless of method. -/
def replayRunAny (limit : Nat) (env : Nat → List UInt8 → Nat) (r : Request) :
    List Nat → List Attempt
  | [] => []
  | b :: bs =>
    if isFailure (env b r.body) && decide (r.body.length ≤ limit) && !bs.isEmpty then
      { backend := b, body := r.body, status := env b r.body }
        :: replayRunAny limit env r bs
    else
      [{ backend := b, body := r.body, status := env b r.body }]

/-- **MUTANT SEPARATION.** The idempotency-blind engine DOES replay the failing
POST onto backend 9 (two attempts), whereas the correct engine makes only one
(`post_never_replayed`). So `retry_replay_idempotent_only` has real content: the
idempotency guard is exactly what stops the POST from being duplicated onto a
second backend. -/
theorem post_replay_mutant :
    let r : Request := ⟨.post, [1, 2, 3]⟩
    (replayRunAny 100 witnessEnv r [7, 9]).length = 2
      ∧ (replayRun 100 witnessEnv r [7, 9]).length = 1 := by
  decide

end Proxy.RetryReplay
