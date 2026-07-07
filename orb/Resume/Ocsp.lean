/-
Resume — OCSP staple freshness and the atomic staple swap.

A stapled OCSP response certifies revocation status for a bounded window
`[thisUpdate, nextUpdate)`.  A front end must serve a staple only while it is
fresh (`now < nextUpdate`); a staple at or past `nextUpdate` is stale and must
never be handed out.  The current staple lives in a cache cell that a reload
(SIGHUP-style) swaps wholesale, so a concurrent request observes either the old
staple or the new one — never a field-torn mix.  This is the same atomic-swap
shape the config reload uses.

  * `Staple`   — the stapled response: its validity window, certificate status,
                 the `certID` of the certificate it speaks for, and an opaque body.
  * `fresh`    — the freshness predicate `now ∈ [thisUpdate, nextUpdate)`.
  * `accepts`  — the deployed acceptance decision: status `good`, fresh, and the
                 `certID` matches the served certificate (RFC 6960 §2.2/§3.2/§4.2.1).
  * `serve?`   — the single-staple serve decision (serve iff `accepts`).
  * `Cache`    — the current staple cell plus an append-only served log.
  * `request`  — serve the current staple iff present and fresh (else stutter).
  * `swap`     — replace the whole staple cell in one atomic step.
-/

namespace Resume

/-- The three OCSP certificate statuses (RFC 6960 §2.2 `CertStatus`): the
certificate is `good` (not revoked), `revoked`, or its status is `unknown` to
the responder. Only `good` certifies non-revocation. -/
inductive CertStatus where
  | good
  | revoked
  | unknown
deriving DecidableEq, Repr

/-- A stapled OCSP response: the validity window `[thisUpdate, nextUpdate)`, the
certificate `certStatus` (RFC 6960 §2.2), the `certId` naming the certificate the
response speaks for (RFC 6960 §4.2.1 `CertID`), and an opaque body identity. -/
structure Staple where
  thisUpdate : Nat
  nextUpdate : Nat
  /-- RFC 6960 §2.2 `CertStatus` — `good`, `revoked`, or `unknown`. -/
  certStatus : CertStatus
  /-- RFC 6960 §4.2.1 `CertID` — the identity of the certificate this response
  certifies, an opaque `Nat`; the deployed gate requires it to equal the served
  certificate's identity. -/
  certId : Nat
  body : Nat
deriving DecidableEq, Repr

/-- Freshness: the current time lies in the half-open validity window. -/
def Staple.fresh (s : Staple) (now : Nat) : Bool :=
  decide (s.thisUpdate ≤ now) && decide (now < s.nextUpdate)

/-- Freshness agrees with the window membership exactly. -/
theorem fresh_iff (s : Staple) (now : Nat) :
    s.fresh now = true ↔ s.thisUpdate ≤ now ∧ now < s.nextUpdate := by
  simp only [Staple.fresh, Bool.and_eq_true, decide_eq_true_eq]

/-- **A staple at or past `nextUpdate` is not fresh.** -/
theorem stale_not_fresh (s : Staple) (now : Nat) (h : s.nextUpdate ≤ now) :
    s.fresh now = false := by
  cases hb : s.fresh now with
  | false => rfl
  | true => have := (fresh_iff s now).mp hb; omega

/-- **The deployed staple-acceptance decision** (RFC 6960 §2.2/§3.2/§4.2.1): a
stapled response is accepted iff its certificate status is `good`, it is fresh
(`thisUpdate ≤ now < nextUpdate`), and its `certID` names the served certificate
(`servedCertId`). Total: every field is decided. Freshness alone is *not*
sufficient — a revoked or wrong-certificate staple is rejected. -/
def Staple.accepts (s : Staple) (now servedCertId : Nat) : Bool :=
  decide (s.certStatus = CertStatus.good) && s.fresh now && decide (s.certId = servedCertId)

/-- Acceptance agrees with the RFC-6960 conjunction exactly. -/
theorem accepts_iff (s : Staple) (now servedCertId : Nat) :
    s.accepts now servedCertId = true ↔
      s.certStatus = CertStatus.good
      ∧ (s.thisUpdate ≤ now ∧ now < s.nextUpdate)
      ∧ s.certId = servedCertId := by
  simp only [Staple.accepts, Bool.and_eq_true, decide_eq_true_eq, fresh_iff, and_assoc]

/-- A revoked (or unknown) staple is never accepted, however fresh. -/
theorem revoked_not_accepted (s : Staple) (now servedCertId : Nat)
    (h : s.certStatus ≠ CertStatus.good) : s.accepts now servedCertId = false := by
  cases hb : s.accepts now servedCertId with
  | false => rfl
  | true => exact absurd ((accepts_iff s now servedCertId).mp hb).1 h

/-- A staple whose `certID` does not name the served certificate is never
accepted, however fresh and `good`. -/
theorem mismatch_not_accepted (s : Staple) (now servedCertId : Nat)
    (h : s.certId ≠ servedCertId) : s.accepts now servedCertId = false := by
  cases hb : s.accepts now servedCertId with
  | false => rfl
  | true => exact absurd ((accepts_iff s now servedCertId).mp hb).2.2 h

/-- The single-staple serve decision: hand out the staple iff it is accepted —
`good`, fresh, and for the served certificate. -/
def serve? (s : Staple) (now servedCertId : Nat) : Option Staple :=
  if s.accepts now servedCertId = true then some s else none

/-- Whatever is served is the current staple, and it was accepted: `good`, fresh,
and naming the served certificate. -/
theorem served_is_valid {s r : Staple} {now servedCertId : Nat}
    (h : serve? s now servedCertId = some r) :
    r = s ∧ s.certStatus = CertStatus.good
      ∧ (s.thisUpdate ≤ now ∧ now < s.nextUpdate) ∧ s.certId = servedCertId := by
  unfold serve? at h
  by_cases hf : s.accepts now servedCertId = true
  · rw [if_pos hf] at h
    exact ⟨(Option.some.inj h).symm, (accepts_iff s now servedCertId).mp hf⟩
  · rw [if_neg hf] at h; exact absurd h (by simp)

/-- **Freshness invariant (point form).**  A staple at or past `nextUpdate` is
never served. -/
theorem stale_never_served (s : Staple) (now servedCertId : Nat)
    (h : s.nextUpdate ≤ now) : serve? s now servedCertId = none := by
  have hnf : ¬ (s.accepts now servedCertId = true) := by
    intro ha; have := ((accepts_iff s now servedCertId).mp ha).2.1; omega
  unfold serve?
  rw [if_neg hnf]

/-- **A revoked staple is never served**, however fresh — the deployed decision
refuses it. -/
theorem revoked_never_served (s : Staple) (now servedCertId : Nat)
    (h : s.certStatus ≠ CertStatus.good) : serve? s now servedCertId = none := by
  unfold serve?
  rw [if_neg (by rw [revoked_not_accepted s now servedCertId h]; simp)]

/-- **A wrong-certificate staple is never served**, however fresh and `good`. -/
theorem mismatch_never_served (s : Staple) (now servedCertId : Nat)
    (h : s.certId ≠ servedCertId) : serve? s now servedCertId = none := by
  unfold serve?
  rw [if_neg (by rw [mismatch_not_accepted s now servedCertId h]; simp)]

/-! ### The staple cache and its atomic swap -/

/-- One served observation: the staple handed out and the time it went out. -/
structure Served where
  staple : Staple
  time : Nat
deriving DecidableEq, Repr

/-- The staple cache: the current cell (a whole `Option Staple`) and an
append-only log of served responses. -/
structure Cache where
  cur : Option Staple
  served : List Served
deriving Repr

/-- Cold boot: no staple, nothing served. -/
def Cache.init : Cache := { cur := none, served := [] }

/-- Serve the current staple at time `now`: append it to the log iff present
and fresh; otherwise stutter. -/
def Cache.request (now : Nat) (c : Cache) : Cache :=
  match c.cur with
  | none => c
  | some s => if s.fresh now = true then { c with served := ⟨s, now⟩ :: c.served } else c

/-- Swap the whole staple cell in one atomic step (SIGHUP-style reload).  Only
the `cur` field is replaced; the served log is untouched. -/
def Cache.swap (n : Option Staple) (c : Cache) : Cache := { c with cur := n }

/-- **Swap atomicity.**  A swap replaces only the staple cell, as one whole
value: the served log is unchanged and the cell becomes exactly `n`. -/
theorem swap_atomic (n : Option Staple) (c : Cache) :
    (c.swap n).cur = n ∧ (c.swap n).served = c.served :=
  ⟨rfl, rfl⟩

/-- **Old-or-new, never torn.**  Across a swap the staple cell is observed as
exactly the old cell or the new one — there is no observable intermediate that
mixes fields from the two. -/
theorem swap_old_or_new (n : Option Staple) (c : Cache) (obs : Option Staple)
    (h : obs = c.cur ∨ obs = (c.swap n).cur) : obs = c.cur ∨ obs = n := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- On a stale current staple, a request appends nothing (it stutters). -/
theorem request_stale_noop (now : Nat) (c : Cache) (s : Staple)
    (hc : c.cur = some s) (h : s.nextUpdate ≤ now) :
    (c.request now).served = c.served := by
  have hf : s.fresh now = false := stale_not_fresh s now h
  simp [Cache.request, hc, hf]

/-- On a fresh current staple, a request serves exactly that staple. -/
theorem request_fresh_serves (now : Nat) (c : Cache) (s : Staple)
    (hc : c.cur = some s) (hf : s.fresh now = true) :
    (c.request now).served = ⟨s, now⟩ :: c.served := by
  simp [Cache.request, hc, hf]

namespace Cache

/-- One step of the cache: serve a request, or swap the staple cell. -/
inductive Step : Cache → Cache → Prop where
  | request (now : Nat) (c : Cache) : Step c (c.request now)
  | swap (n : Option Staple) (c : Cache) : Step c (c.swap n)

/-- States reachable from a cold boot by any sequence of steps. -/
inductive Reachable : Cache → Prop where
  | init : Reachable Cache.init
  | step {c c' : Cache} : Reachable c → Step c c' → Reachable c'

/-- Cache invariant: every served staple was fresh at the time it was served. -/
def Wf (c : Cache) : Prop := ∀ e ∈ c.served, e.staple.fresh e.time = true

theorem wf_init : Wf Cache.init := by
  intro e he
  simp [Cache.init] at he

theorem wf_request (now : Nat) {c : Cache} (h : Wf c) : Wf (c.request now) := by
  cases hc : c.cur with
  | none => simp only [Cache.request, hc]; exact h
  | some s =>
    simp only [Cache.request, hc]
    by_cases hf : s.fresh now = true
    · rw [if_pos hf]
      intro e he
      rcases List.mem_cons.mp he with h1 | h1
      · rw [h1]; exact hf
      · exact h e h1
    · rw [if_neg hf]; exact h

theorem wf_swap (n : Option Staple) {c : Cache} (h : Wf c) : Wf (c.swap n) := by
  intro e he
  exact h e he

theorem wf_step {c c' : Cache} (h : Wf c) (hstep : Step c c') : Wf c' := by
  cases hstep with
  | request now c => exact wf_request now h
  | swap n c => exact wf_swap n h

/-- **The invariant holds throughout every run.** -/
theorem reachable_wf {c : Cache} (h : Reachable c) : Wf c := by
  induction h with
  | init => exact wf_init
  | step _ hstep ih => exact wf_step ih hstep

/-- **Freshness invariant (log form).**  In every reachable cache, every served
staple was strictly before its `nextUpdate` when served — no stale staple is
ever in the served log, and the swap preserves this. -/
theorem served_within_next_update {c : Cache} (h : Reachable c) :
    ∀ e ∈ c.served, e.time < e.staple.nextUpdate := by
  intro e he
  have := (reachable_wf h) e he
  exact ((fresh_iff e.staple e.time).mp this).2

end Cache

end Resume
