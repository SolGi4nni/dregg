/-
LeastConn — least-connections balancing over verified active-connection
accounting, composed with the probe-driven health machine.

This closes the least-connections load-balancing policy end to end: the input
`conns` field that the plain least-connections pick minimises is given a
*provenance* — it is the live in-flight count read out of an active-connection
accounting table with genuine open/close transitions — and the input `healthy`
field is given a provenance too — it is the verdict of the rise/fall health
machine run over that backend's probe history. Selection then filters to
eligible (healthy ∧ administratively active) backends and takes the minimal
in-flight one, ties broken toward the earlier list position.

Two pieces of accounting the reference load balancer keeps only implicitly are
made explicit and verified here:

  * `ConnTable` — a per-backend-id in-flight counter with `openConn`
    (a new upstream connection is dialed) and `closeConn` (a connection is
    returned/torn down). Unlike a cumulative request counter this one goes
    *down* on close, so it tracks concurrency, not throughput: an open/close
    pair is a round trip (`active_open_close_roundtrip`). This is exactly the
    quantity least-connections must minimise, and here it has transitions and
    frame lemmas rather than being an opaque input.

  * the health verdict is the `Health` machine's `up` bit, so an ejected /
    down backend — one the probe machine took Down, e.g. by a `fall`-long
    failure burst — is provably excluded from selection even when it carries
    the fewest in-flight connections (the tempting minimum).

Headline theorems:

  * `leastconn_picks_min`   — the chosen backend has the fewest active
    connections among all healthy-and-active backends (stated directly against
    the `active` accounting read);
  * `leastconn_respects_health` — the chosen backend's node passed the health
    machine (verdict Up) and is administratively active; a backend the health
    FSM took Down is never chosen, even at zero in-flight connections
    (`leastconn_skips_ejected_min` exhibits the mutant);
  * `leastconn_ties_stable` — ties are broken deterministically toward the
    earlier list position: every eligible backend appearing before the pick
    carries strictly more connections, so the pick is the unique earliest
    minimiser.

The plain-pick minimality/membership lemmas (`leastConn_min`, `leastConn_mem`,
`leastConn_total`) and the eligibility algebra (`eligibleOf`) are reused from
`Proxy.Balance`; the health machine (`hrun`, `down_at_fall`) from
`Proxy.Health`. Everything is a pure function over explicit state.
-/

import Proxy.Balance
import Proxy.Health

namespace Proxy.LeastConn

open Proxy

/-! ### Active-connection accounting

An in-flight connection counter keyed by backend id. A `ConnTable` is an
association list `id ↦ live-count`; `openConn` bumps the count on a new dial,
`closeConn` decrements it (floored at zero) on teardown, and `active` reads it
back. This is the concurrency counter least-connections minimises. -/

/-- Per-backend-id in-flight connection counts. -/
abbrev ConnTable := List (Nat × Nat)

/-- The current in-flight count for `id` (`0` if the id is absent). -/
def active (id : Nat) : ConnTable → Nat
  | [] => 0
  | (k, n) :: rest => if k = id then n else active id rest

/-- **Open**: a new upstream connection is dialed — raise `id`'s in-flight
count by one, creating the entry at `1` if absent. -/
def openConn (id : Nat) : ConnTable → ConnTable
  | [] => [(id, 1)]
  | (k, n) :: rest => if k = id then (k, n + 1) :: rest else (k, n) :: openConn id rest

/-- **Close**: a connection is returned/torn down — lower `id`'s in-flight
count by one, floored at zero (a close against an absent/zero id is a no-op,
so the count never goes negative). -/
def closeConn (id : Nat) : ConnTable → ConnTable
  | [] => []
  | (k, n) :: rest => if k = id then (k, n - 1) :: rest else (k, n) :: closeConn id rest

/-- **Open increments the counted id.** -/
theorem active_openConn_self (id : Nat) (t : ConnTable) :
    active id (openConn id t) = active id t + 1 := by
  induction t with
  | nil => simp [openConn, active]
  | cons p rest ih =>
    obtain ⟨k, n⟩ := p
    by_cases hk : k = id
    · simp [openConn, active, hk]
    · simp only [openConn, active, if_neg hk]; exact ih

/-- **Open frames every other id.** -/
theorem active_openConn_other {id id' : Nat} (hne : id' ≠ id) (t : ConnTable) :
    active id' (openConn id t) = active id' t := by
  induction t with
  | nil =>
    show active id' [(id, 1)] = active id' []
    simp only [active]
    rw [if_neg (fun h => hne h.symm)]
  | cons p rest ih =>
    obtain ⟨k, n⟩ := p
    simp only [openConn]
    by_cases hk : k = id
    · rw [if_pos hk]; subst hk
      simp only [active]
      rw [if_neg (fun h => hne h.symm), if_neg (fun h => hne h.symm)]
    · rw [if_neg hk]
      simp only [active]
      by_cases hk' : k = id'
      · rw [if_pos hk', if_pos hk']
      · rw [if_neg hk', if_neg hk']; exact ih

/-- **Close decrements the counted id** (floored at zero). -/
theorem active_closeConn_self (id : Nat) (t : ConnTable) :
    active id (closeConn id t) = active id t - 1 := by
  induction t with
  | nil => simp [closeConn, active]
  | cons p rest ih =>
    obtain ⟨k, n⟩ := p
    by_cases hk : k = id
    · simp [closeConn, active, hk]
    · simp only [closeConn, active, if_neg hk]; exact ih

/-- **Close frames every other id.** -/
theorem active_closeConn_other {id id' : Nat} (hne : id' ≠ id) (t : ConnTable) :
    active id' (closeConn id t) = active id' t := by
  induction t with
  | nil => simp [closeConn]
  | cons p rest ih =>
    obtain ⟨k, n⟩ := p
    simp only [closeConn]
    by_cases hk : k = id
    · rw [if_pos hk]; subst hk
      simp only [active]
      rw [if_neg (fun h => hne h.symm), if_neg (fun h => hne h.symm)]
    · rw [if_neg hk]
      simp only [active]
      by_cases hk' : k = id'
      · rw [if_pos hk', if_pos hk']
      · rw [if_neg hk', if_neg hk']; exact ih

/-- **Round trip.** An open immediately followed by a close of the same id
returns the in-flight count to where it started — the defining property of a
concurrency counter (a cumulative counter would keep the `+1`). -/
theorem active_open_close_roundtrip (id : Nat) (t : ConnTable) :
    active id (closeConn id (openConn id t)) = active id t := by
  rw [active_closeConn_self, active_openConn_self, Nat.add_sub_cancel]

/-! ### Nodes and resolution

A `Node` is the raw configured upstream: identity, weight, tier, admin status,
plus the health machine's gate, its running state, and the probe history yet to
be folded in. `snapshot` resolves a node against the live `ConnTable` and its
probe history into a selection-time `Backend` — the `conns` field is the live
`active` read, the `healthy` field is the health machine's verdict. -/

/-- A configured upstream, before resolution against live state. -/
structure Node where
  /-- Stable identity (matches the `ConnTable` key). -/
  id : Nat
  /-- Configured relative weight. -/
  weight : Nat
  /-- Fallback tier (0 = primary). -/
  tier : Nat
  /-- Administrative status. -/
  status : Status
  /-- Health machine gate (rise/fall thresholds). -/
  gate : HealthGate
  /-- Health machine state entering this node's pending probe history. -/
  hstate : HealthState
  /-- Probe history to fold through the health machine, oldest first. -/
  probes : List Probe
deriving Repr

/-- The node's health verdict: run its probe history through the health
machine and read the `up` bit. This is the `Backend.healthy` provenance. -/
def healthOf (n : Node) : Bool := (hrun n.gate n.hstate n.probes).up

/-- Resolve one node against the live connection table into a selection-time
`Backend`: `conns` is the live in-flight read, `healthy` is the health verdict. -/
def snapshot (ct : ConnTable) (n : Node) : Backend :=
  { id := n.id, weight := n.weight, conns := active n.id ct, tier := n.tier,
    healthy := healthOf n, status := n.status }

@[simp] theorem snapshot_conns (ct : ConnTable) (n : Node) :
    (snapshot ct n).conns = active n.id ct := rfl

@[simp] theorem snapshot_healthy (ct : ConnTable) (n : Node) :
    (snapshot ct n).healthy = healthOf n := rfl

@[simp] theorem snapshot_status (ct : ConnTable) (n : Node) :
    (snapshot ct n).status = n.status := rfl

@[simp] theorem snapshot_id (ct : ConnTable) (n : Node) :
    (snapshot ct n).id = n.id := rfl

/-- Resolve every node against the live table. -/
def resolve (ct : ConnTable) (ns : List Node) : List Backend :=
  ns.map (snapshot ct)

/-- **The least-connections pick.** Resolve the nodes, keep the eligible
(healthy ∧ active) ones, and take the fewest-in-flight backend. -/
def pick (ct : ConnTable) (ns : List Node) : Option Backend :=
  leastConn (eligibleOf (resolve ct ns))

/-- A `snapshot` is eligible exactly when its node is healthy and active. -/
theorem snapshot_eligible (ct : ConnTable) (n : Node) :
    (snapshot ct n).eligible = (healthOf n && decide (n.status = .active)) := rfl

/-! ### Headline 1 — minimality against the active-connection accounting -/

/-- Membership form: the pick is an eligible resolved node. -/
theorem pick_mem_eligible {ct : ConnTable} {ns : List Node} {b : Backend}
    (h : pick ct ns = some b) : b ∈ eligibleOf (resolve ct ns) :=
  leastConn_mem h

/-- **Least-connections minimality (Backend form).** The chosen backend's
in-flight count is minimal over every eligible resolved backend. -/
theorem leastconn_min_backend {ct : ConnTable} {ns : List Node} {b : Backend}
    (h : pick ct ns = some b) :
    ∀ c ∈ resolve ct ns, c.eligible = true → b.conns ≤ c.conns := by
  intro c hc hce
  exact leastConn_min h c (mem_eligibleOf.mpr ⟨hc, hce⟩)

/-- **Headline 1 — `leastconn_picks_min`.** The chosen backend carries the
fewest *active connections* among all healthy-and-active nodes, stated directly
against the `active` accounting read: for every node that is health-machine Up
and administratively active, the pick's in-flight count is ≤ that node's live
in-flight count. This is the defining contract of least-connections, and the
quantity compared is the verified concurrency counter, not an opaque input. -/
theorem leastconn_picks_min {ct : ConnTable} {ns : List Node} {b : Backend}
    (h : pick ct ns = some b) :
    ∀ n ∈ ns, healthOf n = true → n.status = .active →
      b.conns ≤ active n.id ct := by
  intro n hn hhealthy hactive
  have hmem : snapshot ct n ∈ resolve ct ns := List.mem_map_of_mem hn
  have helig : (snapshot ct n).eligible = true := by
    rw [snapshot_eligible, hhealthy, hactive]; rfl
  have := leastconn_min_backend h (snapshot ct n) hmem helig
  rwa [snapshot_conns] at this

/-! ### Headline 2 — the pick respects the health machine -/

/-- Every resolved backend is a snapshot of some node. -/
theorem mem_resolve {ct : ConnTable} {ns : List Node} {b : Backend}
    (h : b ∈ resolve ct ns) : ∃ n ∈ ns, b = snapshot ct n := by
  obtain ⟨n, hn, he⟩ := List.mem_map.mp h
  exact ⟨n, hn, he.symm⟩

/-- **Headline 2 — `leastconn_respects_health`.** The chosen backend's node
passed the health machine (its probe history folds to verdict Up) and is
administratively active. Composing the health FSM: an ejected backend — one the
probe machine drove Down — cannot be the pick, because the pick's node is
provably Up. -/
theorem leastconn_respects_health {ct : ConnTable} {ns : List Node} {b : Backend}
    (h : pick ct ns = some b) :
    ∃ n ∈ ns, b = snapshot ct n ∧
      (hrun n.gate n.hstate n.probes).up = true ∧ n.status = .active := by
  have hmem := pick_mem_eligible h
  have hsplit := mem_eligibleOf.mp hmem
  obtain ⟨n, hn, hsnap⟩ := mem_resolve hsplit.1
  have helig := hsplit.2
  rw [hsnap, snapshot_eligible, Bool.and_eq_true, decide_eq_true_eq] at helig
  exact ⟨n, hn, hsnap, helig.1, helig.2⟩

/-! ### Headline 3 — deterministic tie-breaking (earliest position) -/

/-- The picked backend is the *earliest* minimiser: under distinct ids, every
backend appearing strictly before the pick carries strictly more connections.
So a tie in in-flight count is always resolved toward the earlier list
position. -/
theorem leastConn_earliest {b : Backend} :
    ∀ (pre suf : List Backend), idsNodup (pre ++ b :: suf) →
      leastConn (pre ++ b :: suf) = some b →
      ∀ c ∈ pre, b.conns < c.conns := by
  intro pre
  induction pre with
  | nil => intro suf _ _ c hc; cases hc
  | cons a pre' ih =>
    intro suf hnd h c hc
    -- (a :: pre') ++ b :: suf = a :: (pre' ++ b :: suf)
    rw [List.cons_append] at hnd h
    have hbrest : b ∈ pre' ++ b :: suf :=
      List.mem_append_right pre' (List.mem_cons_self)
    -- distinctness facts from nodup of the tail
    have hnd' : a.id ∉ (pre' ++ b :: suf).map Backend.id ∧
        idsNodup (pre' ++ b :: suf) := by
      have hn : (a.id :: (pre' ++ b :: suf).map Backend.id).Nodup := by
        have hh := hnd
        simp only [idsNodup, List.map_cons] at hh
        exact hh
      exact List.nodup_cons.mp hn
    have hbid : b.id ∈ (pre' ++ b :: suf).map Backend.id :=
      List.mem_map_of_mem hbrest
    -- the tail is nonempty ⇒ leastConn tail = some w
    have hne : pre' ++ b :: suf ≠ [] := by
      intro hnil; rw [hnil] at hbrest; cases hbrest
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (leastConn_total hne)
    -- evaluate the head step
    have hstep : leastConn (a :: (pre' ++ b :: suf)) =
        (if a.conns ≤ w.conns then some a else some w) := by
      simp only [leastConn, hw]
    rw [hstep] at h
    by_cases hcmp : a.conns ≤ w.conns
    · -- would force a = b, contradicting id-distinctness (b in the tail)
      rw [if_pos hcmp] at h
      have hab : a = b := by injection h
      exact absurd (hab ▸ hbid) hnd'.1
    · rw [if_neg hcmp] at h
      have hwb : w = b := by injection h
      have hlr : leastConn (pre' ++ b :: suf) = some b := by rw [hw, hwb]
      rcases List.mem_cons.mp hc with hca | hcpre
      · -- c = a : a.conns > w.conns = b.conns
        subst hca
        have hwc : w.conns = b.conns := by rw [hwb]
        omega
      · -- c ∈ pre' : induction on the tail split
        exact ih suf hnd'.2 hlr c hcpre

/-- **Headline 3 — `leastconn_ties_stable`.** Ties are broken deterministically
toward the earlier list position: with distinct backend ids, every eligible
resolved backend appearing before the pick carries strictly more connections.
Together with `leastconn_picks_min` this pins the pick as the *unique* earliest
minimiser — the selection is a total function of the inputs, so identical
inputs always yield the identical choice. -/
theorem leastconn_ties_stable {ct : ConnTable} {ns : List Node} {b : Backend}
    (hnd : idsNodup (eligibleOf (resolve ct ns)))
    {pre suf : List Backend}
    (hsplit : eligibleOf (resolve ct ns) = pre ++ b :: suf)
    (h : pick ct ns = some b) :
    ∀ c ∈ pre, b.conns < c.conns := by
  have h' : leastConn (eligibleOf (resolve ct ns)) = some b := h
  rw [hsplit] at hnd h'
  exact leastConn_earliest pre suf hnd h'

/-! ### Non-vacuity — real inputs and a health mutant

Concrete node lists exercised by `decide`, showing the pick is not trivially
`none` and that the health composition actually excludes an ejected backend. -/

/-- A healthy, active primary node (clean, no-pending-probe health history at
gate `⟨2,3⟩`). Its in-flight count is whatever the connection table records for
`id`; the node itself carries no count. -/
private def okNode (id : Nat) : Node :=
  ⟨id, 1, 0, .active, ⟨2, 3⟩, ⟨true, 0, 0⟩, []⟩

/-- Ground the accounting: three opens and one close on id 7 leave two live. -/
example : active 7 (closeConn 7 (openConn 7 (openConn 7 (openConn 7 [])))) = 2 := by
  decide

/-- Two healthy nodes: the one with fewer in-flight connections (node 2, at 2 <
5) wins, and the result is genuinely `some` (not a vacuous `none`). -/
example :
    pick [(1, 5), (2, 2)] [okNode 1, okNode 2] = some (snapshot [(1, 5), (2, 2)] (okNode 2)) := by
  decide

/-- **Health mutant.** Node 1 has ZERO in-flight connections — the tempting
least-connections minimum — but its probe history is three consecutive
failures, which at `fall = 3` drives the health machine Down
(`Proxy.down_at_fall`). Node 2 is healthy with FIVE in-flight connections. The
pick is node 2: the ejected minimum is provably skipped. Flipping node 1's
verdict Up (empty probe history) would make it win, so the health composition
is load-bearing, not decorative. -/
private def ejectedNode : Node :=
  ⟨1, 1, 0, .active, ⟨2, 3⟩, ⟨true, 0, 0⟩, [.fail, .fail, .fail]⟩

example : healthOf ejectedNode = false := by decide

example :
    pick [(1, 0), (2, 5)] [ejectedNode, okNode 2]
      = some (snapshot [(1, 0), (2, 5)] (okNode 2)) := by
  decide

/-- The ejected node, were it healthy (empty probe history), carries the min and
WOULD be picked — confirming the exclusion above is caused by health, not by
connection count. -/
example :
    pick [(1, 0), (2, 5)] [okNode 1, okNode 2]
      = some (snapshot [(1, 0), (2, 5)] (okNode 1)) := by
  decide

/-- **Tie mutant.** Two eligible nodes tied at 3 in-flight connections: the
pick is the earlier one, and swapping list order swaps the winner — the
tie-break is by position, deterministically. -/
example :
    pick [(1, 3), (2, 3)] [okNode 1, okNode 2]
      = some (snapshot [(1, 3), (2, 3)] (okNode 1)) := by
  decide

example :
    pick [(1, 3), (2, 3)] [okNode 2, okNode 1]
      = some (snapshot [(1, 3), (2, 3)] (okNode 2)) := by
  decide

end Proxy.LeastConn
