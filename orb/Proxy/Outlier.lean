/-
Outlier — passive outlier detection: consecutive-error ejection with backoff,
under a pool-level ejection budget.

Active probing (`Proxy.Health`) asks backends how they feel; outlier detection
watches what actually happens to REAL requests. A backend that answers `n`
consecutive requests with server errors is EJECTED from the eligible set for a
while; each re-ejection lengthens the timeout (linear backoff on a lifetime
ejection counter). Two guardrails make this safe to run unattended:

  * an ejection BUDGET: at most `maxEjectPercent` of the pool may be ejected
    at once. When the pool is misbehaving collectively (upstream network
    partition, shared dependency down), evicting everyone would turn a partial
    outage into a total one — past the budget, ejection is refused and the
    streak keeps counting;
  * TIME-BOUNDED ejection: every ejection carries an explicit readmission
    deadline (`ejectedAt + baseEject * ejectCount`); ticks past the deadline
    readmit. No backend is ejected forever.

The verdict (`OMember.ejected`) feeds the `healthy` bit of the selection-time
`Backend` snapshot exactly as `Proxy.Health` verdicts do; the selection
algebra then guarantees an ejected backend is never chosen
(`select_eligible`).

Theorems:

  * `eject_requires_streak` — **ejection is earned**: a member flips to
    ejected only by a failure event completing its full consecutive-error
    streak (single anomalies never eject — the passive analogue of
    `Health.noFlap_fail`);
  * `eject_respects_budget` — a member flips to ejected only while the
    budget has headroom;
  * `ostep_capped` / `orun_capped` — **the budget is an invariant**: along
    ANY event trace from a clean start, the ejected count never exceeds the
    configured fraction of the pool — outlier detection can never eject its
    way into a full outage;
  * `readmit_iff_deadline` — **exact backoff semantics**: a tick readmits an
    ejected member exactly when its per-ejection deadline has elapsed;
  * `success_resets` / success never ejects — one good response clears the
    error streak;
  * `ostep_length` — the pool roster is never changed by the detector (it
    flags, it does not remove).
-/

import Proxy.Basic

namespace Proxy.Outlier

/-- Outlier-detection configuration. `consecutive` server errors eject;
an ejection lasts `baseEject * ejectCount` time units (linear backoff);
at most `maxEjectPercent` percent of the pool may be ejected at once. -/
structure OutlierCfg where
  consecutive : Nat
  baseEject : Nat
  maxEjectPercent : Nat
deriving DecidableEq, Repr

/-- Per-backend detector state. `streak` counts consecutive server errors;
`ejectCount` counts lifetime ejections (the backoff multiplier). -/
structure OMember where
  id : Nat
  streak : Nat
  ejected : Bool
  ejectedAt : Nat
  ejectCount : Nat
deriving DecidableEq, Repr

/-- A fresh member: in rotation, clean history. -/
def OMember.init (bid : Nat) : OMember :=
  { id := bid, streak := 0, ejected := false, ejectedAt := 0, ejectCount := 0 }

/-- Detector inputs: a request outcome attributed to a backend, or a clock
tick. `failure` is a server-error-class outcome (5xx / connect failure). -/
inductive OEvent where
  | success (bid : Nat)
  | failure (bid : Nat)
  | tick (now : Nat)
deriving DecidableEq, Repr

/-- Detector pool state: the members plus the last observed clock. -/
structure OState where
  members : List OMember
  clock : Nat
deriving DecidableEq, Repr

/-- A clean pool over the given backend ids. -/
def OState.init (bids : List Nat) : OState :=
  { members := bids.map OMember.init, clock := 0 }

/-- Currently ejected members. -/
def ejectedCount : List OMember → Nat
  | [] => 0
  | m :: ms => (if m.ejected then 1 else 0) + ejectedCount ms

/-- The ejection budget: how many members may be ejected at once. -/
def budget (cfg : OutlierCfg) (poolSize : Nat) : Nat :=
  poolSize * cfg.maxEjectPercent / 100

/-- Apply `f` to the first member carrying `bid` (ids are unique per the
config invariant; first-match makes single-touch a syntactic fact). -/
def updateFirst (bid : Nat) (f : OMember → OMember) : List OMember → List OMember
  | [] => []
  | m :: ms => if m.id = bid then f m :: ms else m :: updateFirst bid f ms

/-- The failure transition for one member. `count` is the pool's ejected
count at event time; the flip is allowed only under budget headroom. -/
def failUpdate (cfg : OutlierCfg) (clock count allowed : Nat)
    (m : OMember) : OMember :=
  if m.ejected then m
  else if cfg.consecutive ≤ m.streak + 1 ∧ count + 1 ≤ allowed then
    { m with ejected := true, ejectedAt := clock,
             ejectCount := m.ejectCount + 1, streak := 0 }
  else { m with streak := m.streak + 1 }

/-- The tick transition for one member: readmit exactly at the deadline. -/
def readmitAt (cfg : OutlierCfg) (now : Nat) (m : OMember) : OMember :=
  if m.ejected ∧ m.ejectedAt + cfg.baseEject * m.ejectCount ≤ now then
    { m with ejected := false, streak := 0 }
  else m

/-- One detector step. -/
def ostep (cfg : OutlierCfg) (s : OState) : OEvent → OState
  | .success bid =>
    { s with members := updateFirst bid (fun m => { m with streak := 0 }) s.members }
  | .failure bid =>
    { s with
      members := updateFirst bid
        (failUpdate cfg s.clock (ejectedCount s.members)
          (budget cfg s.members.length))
        s.members }
  | .tick now =>
    { members := s.members.map (readmitAt cfg now), clock := Nat.max s.clock now }

/-- Run an event trace, oldest first. -/
def orun (cfg : OutlierCfg) (s : OState) : List OEvent → OState
  | [] => s
  | e :: es => orun cfg (ostep cfg s e) es

/-! ### Per-member exactness -/

/-- **Ejection is earned.** A member flips to ejected only when the failure
completes its full consecutive-error streak: `consecutive − 1` errors and a
success in between never eject (`success_resets`). -/
theorem eject_requires_streak {cfg : OutlierCfg} {clock count allowed : Nat}
    {m : OMember} (hnot : m.ejected = false)
    (h : (failUpdate cfg clock count allowed m).ejected = true) :
    cfg.consecutive ≤ m.streak + 1 := by
  unfold failUpdate at h
  rw [if_neg (by simp [hnot])] at h
  split at h
  · rename_i hcond; exact hcond.1
  · simp [hnot] at h

/-- **Ejection respects the budget.** A member flips to ejected only while
the ejected count has headroom under the budget. -/
theorem eject_respects_budget {cfg : OutlierCfg} {clock count allowed : Nat}
    {m : OMember} (hnot : m.ejected = false)
    (h : (failUpdate cfg clock count allowed m).ejected = true) :
    count + 1 ≤ allowed := by
  unfold failUpdate at h
  rw [if_neg (by simp [hnot])] at h
  split at h
  · rename_i hcond; exact hcond.2
  · simp [hnot] at h

/-- Below the full streak, a failure only counts: no ejection, streak + 1. -/
theorem failure_below_streak {cfg : OutlierCfg} {clock count allowed : Nat}
    {m : OMember} (hnot : m.ejected = false)
    (hlt : m.streak + 1 < cfg.consecutive) :
    failUpdate cfg clock count allowed m = { m with streak := m.streak + 1 } := by
  unfold failUpdate
  rw [if_neg (by simp [hnot]), if_neg (by omega)]

/-- **Exact backoff semantics.** A tick readmits an ejected member iff its
deadline `ejectedAt + baseEject * ejectCount` has elapsed. -/
theorem readmit_iff_deadline {cfg : OutlierCfg} {now : Nat} {m : OMember}
    (hej : m.ejected = true) :
    (readmitAt cfg now m).ejected = false
      ↔ m.ejectedAt + cfg.baseEject * m.ejectCount ≤ now := by
  unfold readmitAt
  constructor
  · intro h
    by_cases hd : m.ejectedAt + cfg.baseEject * m.ejectCount ≤ now
    · exact hd
    · rw [if_neg (by simp [hd])] at h
      rw [hej] at h
      cases h
  · intro hd
    rw [if_pos ⟨hej, hd⟩]

/-- A success resets the streak and never changes the ejection flag. -/
theorem success_resets {cfg : OutlierCfg} {s : OState} {bid : Nat} :
    ∀ m ∈ (ostep cfg s (.success bid)).members,
      m.streak = 0 ∨ ∃ m' ∈ s.members, m = m' := by
  show ∀ m ∈ updateFirst bid _ s.members, _
  generalize s.members = ms
  induction ms with
  | nil => intro m hm; cases hm
  | cons a rest ih =>
    intro m hm
    simp only [updateFirst] at hm
    split at hm
    · rcases List.mem_cons.mp hm with hm' | hm'
      · rw [hm']; exact Or.inl rfl
      · exact Or.inr ⟨m, List.mem_cons_of_mem _ hm', rfl⟩
    · rcases List.mem_cons.mp hm with hm' | hm'
      · exact Or.inr ⟨a, List.mem_cons_self a rest, hm'⟩
      · rcases ih m hm' with h | ⟨m', hm'', he⟩
        · exact Or.inl h
        · exact Or.inr ⟨m', List.mem_cons_of_mem _ hm'', he⟩

/-! ### The budget invariant -/

/-- `updateFirst` with a flag-preserving `f` preserves the ejected count. -/
theorem ejectedCount_updateFirst_preserve {bid : Nat} {f : OMember → OMember}
    (hf : ∀ m, (f m).ejected = m.ejected) (ms : List OMember) :
    ejectedCount (updateFirst bid f ms) = ejectedCount ms := by
  induction ms with
  | nil => rfl
  | cons a rest ih =>
    simp only [updateFirst]
    split
    · simp only [ejectedCount, hf a]
    · simp only [ejectedCount, ih]

/-- One failure event grows the ejected count by at most one, and only under
budget headroom (`G` is the pool count snapshot the guard reads). -/
theorem ejectedCount_updateFirst_fail {cfg : OutlierCfg}
    {clock G allowed bid : Nat} (ms : List OMember) :
    ejectedCount (updateFirst bid (failUpdate cfg clock G allowed) ms)
      ≤ ejectedCount ms + (if G + 1 ≤ allowed then 1 else 0) := by
  induction ms with
  | nil => simp [updateFirst, ejectedCount]
  | cons a rest ih =>
    simp only [updateFirst]
    split
    · -- head is the target
      simp only [ejectedCount]
      by_cases haej : a.ejected
      · rw [show failUpdate cfg clock G allowed a = a from by
          unfold failUpdate; rw [if_pos haej]]
        split <;> omega
      · have haej' : a.ejected = false := by
          cases hae : a.ejected
          · rfl
          · exact absurd hae haej
        by_cases hflip : (failUpdate cfg clock G allowed a).ejected = true
        · have hbud : G + 1 ≤ allowed :=
            eject_respects_budget haej' hflip
          rw [if_pos hbud]
          simp only [if_pos hflip, if_neg haej]
          omega
        · simp only [if_neg hflip, if_neg haej]
          split <;> omega
    · -- head untouched, recurse
      simp only [ejectedCount]
      omega

/-- Readmission only shrinks the ejected count. -/
theorem ejectedCount_readmit_le (cfg : OutlierCfg) (now : Nat)
    (ms : List OMember) :
    ejectedCount (ms.map (readmitAt cfg now)) ≤ ejectedCount ms := by
  induction ms with
  | nil => exact Nat.le_refl _
  | cons a rest ih =>
    simp only [List.map_cons, ejectedCount]
    have : (if (readmitAt cfg now a).ejected then 1 else 0)
        ≤ (if a.ejected then 1 else 0) := by
      unfold readmitAt
      split
      · simp
      · exact Nat.le_refl _
    omega

/-- `updateFirst` never changes the roster size. -/
theorem updateFirst_length (bid : Nat) (f : OMember → OMember) :
    ∀ ms : List OMember, (updateFirst bid f ms).length = ms.length := by
  intro ms
  induction ms with
  | nil => rfl
  | cons a rest ih =>
    simp only [updateFirst]
    split <;> simp [List.length_cons, ih]

/-- Every step preserves the pool roster size (the detector flags, it never
adds or removes members). -/
theorem ostep_length (cfg : OutlierCfg) (s : OState) (e : OEvent) :
    (ostep cfg s e).members.length = s.members.length := by
  cases e with
  | success bid => exact updateFirst_length ..
  | failure bid => exact updateFirst_length ..
  | tick now => simp [ostep]

/-- **The budget is preserved by every step.** If the ejected count is within
budget, it stays within budget — failures eject only under headroom, ticks
and successes never eject. -/
theorem ostep_capped {cfg : OutlierCfg} {s : OState} {e : OEvent}
    (hcap : ejectedCount s.members ≤ budget cfg s.members.length) :
    ejectedCount (ostep cfg s e).members
      ≤ budget cfg (ostep cfg s e).members.length := by
  rw [ostep_length]
  cases e with
  | success bid =>
    show ejectedCount (updateFirst bid _ s.members) ≤ _
    rw [ejectedCount_updateFirst_preserve
      (f := fun m => { m with streak := 0 }) (fun m => rfl)]
    exact hcap
  | failure bid =>
    have h := ejectedCount_updateFirst_fail
      (cfg := cfg) (clock := s.clock) (G := ejectedCount s.members)
      (allowed := budget cfg s.members.length) (bid := bid) s.members
    show ejectedCount (updateFirst bid _ s.members) ≤ _
    split at h <;> omega
  | tick now =>
    show ejectedCount (s.members.map (readmitAt cfg now)) ≤ _
    exact Nat.le_trans (ejectedCount_readmit_le cfg now s.members) hcap

/-- **The budget is an invariant of every trace.** Along any event sequence
from a within-budget state, the ejected count never exceeds the configured
fraction of the pool: outlier detection cannot eject its way into a total
outage. -/
theorem orun_capped {cfg : OutlierCfg} {s : OState}
    (hcap : ejectedCount s.members ≤ budget cfg s.members.length) :
    ∀ es : List OEvent,
      ejectedCount (orun cfg s es).members
        ≤ budget cfg (orun cfg s es).members.length := by
  intro es
  induction es generalizing s with
  | nil => exact hcap
  | cons e rest ih => exact ih (ostep_capped hcap)

/-- A clean start is within budget. -/
theorem init_capped (cfg : OutlierCfg) (bids : List Nat) :
    ejectedCount (OState.init bids).members
      ≤ budget cfg (OState.init bids).members.length := by
  have h : ejectedCount (bids.map OMember.init) = 0 := by
    induction bids with
    | nil => rfl
    | cons b rest ih => simp [List.map_cons, ejectedCount, ih, OMember.init]
  show ejectedCount (bids.map OMember.init) ≤ _
  omega

end Proxy.Outlier
