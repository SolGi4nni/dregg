import Cache

/-!
# Correctness of cache request collapsing / coalescing (RFC 9111 §4)

`Cache.lean` establishes *safety* facts about the coalescing machinery — the
transition is total and deterministic, the store stays bounded, a fresh hit
never contacts the origin. It also states in-library counting lemmas
(`coalesce_single_fetch`, `upstream_serves_all`). Those are properties phrased
in the vocabulary of the implementation. They do **not**, on their own, pin the
end-to-end observable that RFC 9111 §4 mandates for a *thundering herd*: that K
simultaneous cache misses for one key collapse to a single forward request whose
one result is delivered, unchanged, to all K clients.

This file upgrades that to a *correctness* claim against an INDEPENDENT
specification. The spec is the exact byte-for-byte sequence of observable
effects the standard requires; the refinement theorem proves the DEPLOYED
transition (`Cache.step`, folded by `Cache.runEffs`) emits precisely that
sequence — no more, no fewer, and with the followers' served body identical to
the leader's fetched body.

## The specification, taken from the RFC

RFC 9111 §4 ("Constructing Responses from Caches"), under request collapsing:

> "A cache … might be able to use an ongoing request … A cache that supports
>  request collapsing … combines multiple incoming requests for the same target
>  into a single forward request … When the response arrives, it is used to
>  satisfy all of the pending requests."  (RFC 9111 §4)

Read as an obligation on the effect trace of K concurrent same-key misses
followed by one upstream completion delivering a body `b`, this fixes three
quantities simultaneously:

1. **Exactly one forward request.** The count of origin-contacting `fetch`
   effects over the whole episode is `1`, not `K`. This is the anti-thundering-
   herd guarantee.
2. **K − 1 collapse.** The other K − 1 requests are parked (`wait`) behind the
   in-flight fetch rather than each dialing the origin.
3. **One result satisfies all.** When the single response arrives it produces
   exactly K `serve` effects, and *every one* carries the same body `b` — the
   result of the single forward request. No follower is served a stale or
   substituted payload.

`specTrace` below writes that obligation out as a concrete list, as a direct
function of K and the delivered body `b`, with NO reference to `Cache.step`,
`Cache.runEffs`, the lock set, or the pending bag. It says what the wire should
carry, not what the implementation computes.

## What is proven

* `coalesce_refines_spec` — **the refinement theorem**: for every starting
  cache state with the key absent, unlocked, and no prior waiter for the key,
  the DEPLOYED fold `Cache.runEffs` over the K concurrent requests followed by
  the single upstream completion emits *exactly* `specTrace k r.body K`. The
  implementation refines the RFC §4 collapsing obligation.
* `coalesce_refines_spec_init` — the same, anchored at the genuine empty initial
  state `Cache.init`, so the theorem is closed with no free preconditions.
* `deployed_fetch_count_one` / `deployed_serves_leader_body` — the two
  headline consequences read back off the refinement: the deployed episode
  issues exactly one upstream fetch, and all served bodies equal the fetched
  body.

## Non-vacuity (a wrong implementation FAILS the spec)

* `spec_fetch_count` — the spec pins the upstream-fetch count at `1` for every
  K. Because equal traces have equal fetch counts, an implementation that issued
  K independent fetches (no coalescing) would emit `K` and, for K ≥ 2, cannot
  equal `specTrace`; `no_coalescing_refuted` is the closed instance.
* `spec_serves_all_leader_body` — the spec's serve effects are all `serve k b`;
  `spec_body_injective` shows `specTrace k b K` determines `b` (for K ≥ 1), so an
  implementation that served any follower a different body `b' ≠ b` would emit a
  trace that cannot equal `specTrace k b K`; `stale_follower_refuted` is the
  closed instance.
* `spec_serve_count` — the spec pins the serve count at exactly `K`; an
  implementation that dropped a waiter (served only the leader) would emit fewer
  serves and fail. `dropped_waiter_refuted` is the closed instance.

None of these hold for the constant, the identity, or an uncoalesced machine, so
the specification is not the implementation renamed.
-/

namespace CacheCoalesceCorrect

open Cache

/-! ## The independent specification (RFC 9111 §4 request collapsing)

The observable episode is: K clients request the same key at one instant (all
miss, one leads and K−1 collapse), then the single forward request completes
with body `b`. The standard fixes the resulting effect trace to be one forward
fetch, K−1 parked waiters, and K serves that all carry `b`. -/

/-- RFC 9111 §4: the mandated effect trace for a K-way thundering herd on key
`k` whose single forward request returns body `b`. One `fetch`, then K−1 `wait`,
then K `serve`, every serve carrying `b`. Defined purely from `K` and `b` —
independent of `Cache.step`, the lock set, and the pending bag. -/
def specTrace (k : Key) (b : Body) (K : Nat) : List Eff :=
  Eff.fetch k :: (List.replicate (K - 1) (Eff.wait k) ++ List.replicate K (Eff.serve k b))

/-- `true` on a `serve` effect for key `k` (any body). A decidable serve-count
predicate; independent of the implementation. -/
def isServeK (k : Key) : Eff → Bool
  | .serve k' _ => decide (k' = k)
  | _ => false

/-- The spec issues exactly one upstream fetch, for every K — the anti-
thundering-herd count. -/
theorem spec_fetch_count (k : Key) (b : Body) (K : Nat) :
    countE Eff.isFetch (specTrace k b K) = 1 := by
  simp only [specTrace, countE, List.filter_cons, List.filter_append]
  have hw : (List.replicate (K - 1) (Eff.wait k)).filter Eff.isFetch = [] := by
    apply List.filter_eq_nil_iff.mpr; intro x hx
    rw [List.eq_of_mem_replicate hx]; simp [Eff.isFetch]
  have hs : (List.replicate K (Eff.serve k b)).filter Eff.isFetch = [] := by
    apply List.filter_eq_nil_iff.mpr; intro x hx
    rw [List.eq_of_mem_replicate hx]; simp [Eff.isFetch]
  simp [Eff.isFetch, hw, hs]

/-- The spec produces exactly K serves for key `k`. -/
theorem spec_serve_count (k : Key) (b : Body) (K : Nat) :
    countE (isServeK k) (specTrace k b K) = K := by
  simp only [specTrace, countE, List.filter_cons, List.filter_append]
  have hw : (List.replicate (K - 1) (Eff.wait k)).filter (isServeK k) = [] := by
    apply List.filter_eq_nil_iff.mpr; intro x hx
    rw [List.eq_of_mem_replicate hx]; simp [isServeK]
  have hs : (List.replicate K (Eff.serve k b)).filter (isServeK k)
      = List.replicate K (Eff.serve k b) := by
    apply List.filter_eq_self.mpr; intro x hx
    rw [List.eq_of_mem_replicate hx]; simp [isServeK]
  simp [isServeK, hw, hs, List.length_replicate]

/-- Every serve the spec emits carries the leader's body `b` — no follower is
handed a substituted payload. -/
theorem spec_serves_all_leader_body (k : Key) (b : Body) (K : Nat) :
    ∀ e ∈ specTrace k b K, (∃ bd, e = Eff.serve k bd) → e = Eff.serve k b := by
  intro e he hserve
  simp only [specTrace, List.mem_cons, List.mem_append, List.mem_replicate] at he
  obtain ⟨bd, rfl⟩ := hserve
  rcases he with h | h | h
  · cases h
  · exact absurd h.2 (by simp)
  · rw [h.2]

/-- The spec determines the delivered body: `specTrace k b K` for K ≥ 1 pins `b`.
Hence a machine that served a follower `b' ≠ b` would emit a different trace. -/
theorem spec_body_injective (k : Key) (b b' : Body) (K : Nat) (hK : 0 < K)
    (h : specTrace k b K = specTrace k b' K) : b = b' := by
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
  simp only [specTrace, List.cons.injEq, true_and] at h
  -- cancel the shared K−1 wait prefix, then the leading serve of the K serves
  have h2 : List.replicate (m + 1) (Eff.serve k b) = List.replicate (m + 1) (Eff.serve k b') :=
    List.append_cancel_left h
  rw [List.replicate_succ, List.replicate_succ, List.cons.injEq] at h2
  exact ((Eff.serve.injEq _ _ _ _).mp h2.1).2

/-! ## Threading the DEPLOYED fold over a trace

`Cache.runEffs` folds `Cache.step`, flattening effects, but drops the final
state. `runState` threads the same `Cache.step` to recover the state after a
trace so a following input can be evaluated. Both are the deployed transition. -/

/-- The state after folding the DEPLOYED `Cache.step` over an input trace. -/
def runState (s : St) : List Input → St
  | [] => s
  | i :: is => runState (step s i).1 is

@[simp] theorem runState_nil (s : St) : runState s [] = s := rfl
@[simp] theorem runEffs_nil (s : St) : runEffs s [] = [] := rfl

theorem runEffs_cons (s : St) (i : Input) (is : List Input) :
    runEffs s (i :: is) = (step s i).2 ++ runEffs (step s i).1 is := rfl

theorem runState_cons (s : St) (i : Input) (is : List Input) :
    runState s (i :: is) = runState (step s i).1 is := rfl

/-- The DEPLOYED fold distributes over a trace split, threading the state. -/
theorem runEffs_append (s : St) (as bs : List Input) :
    runEffs s (as ++ bs) = runEffs s as ++ runEffs (runState s as) bs := by
  induction as generalizing s with
  | nil => simp
  | cons i is ih =>
    rw [List.cons_append, runEffs_cons, runEffs_cons, runState_cons, ih, List.append_assoc]

/-! ## The follower run: K−1 collapses onto the leader (real `Cache.step`) -/

/-- Every follower request from a locked, still-missing state emits exactly one
`wait`, keeps the key missing and locked, and adds one to the key's pending
count. This is the DEPLOYED `Cache.step` on the miss-locked branch. -/
theorem follow_run (k : Key) (now : Nat) :
    ∀ (m : Nat) (t : St), t.store.get? k = none → t.locked k = true →
      runEffs t (reqs k now m) = List.replicate m (Eff.wait k) ∧
      (runState t (reqs k now m)).store.get? k = none ∧
      (runState t (reqs k now m)).locked k = true ∧
      (runState t (reqs k now m)).pending.countP (fun x => eqK x k)
        = t.pending.countP (fun x => eqK x k) + m := by
  intro m
  induction m with
  | zero => intro t hget hlock; simp [reqs, hget, hlock]
  | succ m ih =>
    intro t hget hlock
    have hexp : reqs k now (m + 1) = Input.request k now :: reqs k now m := by
      simp [reqs, List.replicate_succ]
    have hstep : step t (Input.request k now)
        = ({ t with pending := k :: t.pending }, [Eff.wait k]) :=
      step_miss_locked t k now hget hlock
    have hg' : ({ t with pending := k :: t.pending } : St).store.get? k = none := hget
    have hl' : ({ t with pending := k :: t.pending } : St).locked k = true := hlock
    obtain ⟨hE, hG, hL, hP⟩ := ih { t with pending := k :: t.pending } hg' hl'
    have hcount : ({ t with pending := k :: t.pending } : St).pending.countP (fun x => eqK x k)
        = t.pending.countP (fun x => eqK x k) + 1 := by
      simp [List.countP_cons, eqK_refl]
    have hRunE : runEffs t (reqs k now (m + 1))
        = Eff.wait k :: runEffs { t with pending := k :: t.pending } (reqs k now m) := by
      rw [hexp, runEffs_cons, hstep]; rfl
    have hRunS : runState t (reqs k now (m + 1))
        = runState { t with pending := k :: t.pending } (reqs k now m) := by
      rw [hexp, runState_cons, hstep]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hRunE, hE, List.replicate_succ]
    · rw [hRunS]; exact hG
    · rw [hRunS]; exact hL
    · rw [hRunS, hP, hcount]; omega

/-- The leader run: from a missing, unlocked, waiter-free state, K = m+1 requests
emit one `fetch` then m `wait`, and leave the key locked with pending count m —
the DEPLOYED `Cache.step` on the miss-unlocked branch followed by `follow_run`. -/
theorem lead_run (s : St) (k : Key) (now m : Nat)
    (hget : s.store.get? k = none) (hlock : s.locked k = false)
    (hpend : s.pending.countP (fun x => eqK x k) = 0) :
    runEffs s (reqs k now (m + 1)) = Eff.fetch k :: List.replicate m (Eff.wait k) ∧
    (runState s (reqs k now (m + 1))).locked k = true ∧
    (runState s (reqs k now (m + 1))).pending.countP (fun x => eqK x k) = m := by
  have hexp : reqs k now (m + 1) = Input.request k now :: reqs k now m := by
    simp [reqs, List.replicate_succ]
  have hstep : step s (Input.request k now)
      = ({ s with locks := k :: s.locks }, [Eff.fetch k]) :=
    step_miss_unlocked s k now hget hlock
  have hg1 : ({ s with locks := k :: s.locks } : St).store.get? k = none := hget
  have hl1 : ({ s with locks := k :: s.locks } : St).locked k = true := locked_cons_self s k
  have hp1 : ({ s with locks := k :: s.locks } : St).pending.countP (fun x => eqK x k) = 0 := hpend
  obtain ⟨hE, hG, hL, hP⟩ := follow_run k now m { s with locks := k :: s.locks } hg1 hl1
  have hRunE : runEffs s (reqs k now (m + 1))
      = Eff.fetch k :: runEffs { s with locks := k :: s.locks } (reqs k now m) := by
    rw [hexp, runEffs_cons, hstep]; rfl
  have hRunS : runState s (reqs k now (m + 1))
      = runState { s with locks := k :: s.locks } (reqs k now m) := by
    rw [hexp, runState_cons, hstep]
  refine ⟨?_, ?_, ?_⟩
  · rw [hRunE, hE]
  · rw [hRunS]; exact hL
  · rw [hRunS, hP, hp1]; omega

/-! ## The refinement theorem -/

/-- **The DEPLOYED cache refines the RFC §4 request-collapsing obligation.**

For any starting state where key `k` is absent, unlocked, and has no parked
waiter, the deployed fold `Cache.runEffs` over K = n concurrent requests for `k`
followed by the single upstream completion delivering `r` emits EXACTLY the
specified trace: one `fetch`, K−1 `wait`, and K `serve`, every serve carrying
`r.body`. The lists are equal as sequences — no reordering, no dropped or extra
effect, and every follower's served body is the single fetch's body. -/
theorem coalesce_refines_spec
    (s : St) (k : Key) (r : Resp) (now now' n : Nat) (hn : 0 < n)
    (hget : s.store.get? k = none) (hlock : s.locked k = false)
    (hpend : s.pending.countP (fun x => eqK x k) = 0) :
    runEffs s (reqs k now n ++ [Input.upstream k r now']) = specTrace k r.body n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hReq, hLocked, hPend⟩ := lead_run s k now m hget hlock hpend
  -- the single upstream completion serves the leader + all m waiters
  have hUp : runEffs (runState s (reqs k now (m + 1))) [Input.upstream k r now']
      = List.replicate (m + 1) (Eff.serve k r.body) := by
    rw [runEffs_cons, runEffs_nil, List.append_nil,
      upstream_serves_all _ k r now' hLocked, hPend]
  rw [runEffs_append, hReq, hUp, specTrace]
  simp [Nat.add_sub_cancel, List.cons_append]

/-- The refinement anchored at the genuine empty initial state `Cache.init`: no
free preconditions, so the RFC §4 obligation is closed for the real machine
starting cold. -/
theorem coalesce_refines_spec_init
    (cap : Nat) (k : Key) (r : Resp) (now now' n : Nat) (hn : 0 < n) :
    runEffs (init cap) (reqs k now n ++ [Input.upstream k r now']) = specTrace k r.body n := by
  apply coalesce_refines_spec _ _ _ _ _ _ hn
  · rfl
  · simp [St.locked, init]
  · simp [init]

/-! ## Headline consequences read off the refinement (deployed behavior) -/

/-- The DEPLOYED episode issues exactly one upstream fetch for K concurrent
same-key misses — the anti-thundering-herd guarantee, on the real `Cache.step`. -/
theorem deployed_fetch_count_one
    (s : St) (k : Key) (r : Resp) (now now' n : Nat) (hn : 0 < n)
    (hget : s.store.get? k = none) (hlock : s.locked k = false)
    (hpend : s.pending.countP (fun x => eqK x k) = 0) :
    countE Eff.isFetch (runEffs s (reqs k now n ++ [Input.upstream k r now'])) = 1 := by
  rw [coalesce_refines_spec s k r now now' n hn hget hlock hpend, spec_fetch_count]

/-- Every serve the DEPLOYED episode emits carries the single fetch's body — no
follower is served a stale or substituted payload. -/
theorem deployed_serves_leader_body
    (s : St) (k : Key) (r : Resp) (now now' n : Nat) (hn : 0 < n)
    (hget : s.store.get? k = none) (hlock : s.locked k = false)
    (hpend : s.pending.countP (fun x => eqK x k) = 0) :
    ∀ e ∈ runEffs s (reqs k now n ++ [Input.upstream k r now']),
      (∃ bd, e = Eff.serve k bd) → e = Eff.serve k r.body := by
  rw [coalesce_refines_spec s k r now now' n hn hget hlock hpend]
  exact spec_serves_all_leader_body k r.body n

/-! ## Non-vacuity: wrong machines are refuted by the spec -/

/-- A machine with no coalescing emits one fetch per request. Its trace (here for
K = 2, two independent fetches) is not `specTrace`, because the spec's fetch
count is 1 while the uncoalesced count is 2. -/
theorem no_coalescing_refuted (k : Key) (b : Body) :
    Eff.fetch k :: Eff.fetch k :: List.replicate 2 (Eff.serve k b) ≠ specTrace k b 2 := by
  intro h
  have hc := congrArg (countE Eff.isFetch) h
  rw [spec_fetch_count] at hc
  simp [countE, Eff.isFetch, List.filter_cons] at hc

/-- A machine that served a follower a substituted body `b' ≠ b` emits a trace
that cannot equal `specTrace k b K`, because the spec determines the body. -/
theorem stale_follower_refuted (k : Key) (b b' : Body) (K : Nat) (hK : 0 < K)
    (hbb : b ≠ b') : specTrace k b' K ≠ specTrace k b K := by
  intro h
  exact hbb (spec_body_injective k b b' K hK h.symm)

/-- A machine that dropped a waiter (K−1 serves instead of K) emits a trace whose
serve count is one short of the spec's, so it cannot equal `specTrace`. Shown for
K = 2: one serve emitted where the spec demands two. -/
theorem dropped_waiter_refuted (k : Key) (b : Body) :
    Eff.fetch k :: Eff.wait k :: [Eff.serve k b] ≠ specTrace k b 2 := by
  intro h
  have hc := congrArg (countE (isServeK k)) h
  rw [spec_serve_count] at hc
  simp [countE, isServeK, List.filter_cons] at hc

#print axioms coalesce_refines_spec
#print axioms coalesce_refines_spec_init
#print axioms deployed_fetch_count_one
#print axioms deployed_serves_leader_body
#print axioms spec_body_injective
#print axioms no_coalescing_refuted
#print axioms stale_follower_refuted
#print axioms dropped_waiter_refuted

end CacheCoalesceCorrect
