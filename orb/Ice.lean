import Stun
/-!
# ICE candidate-pair checklist FSM (RFC 8445)

A total model of the Interactive Connectivity Establishment (ICE) state that
gates whether a data channel may carry traffic. ICE gathers candidate
transport addresses, forms them into candidate pairs, runs a STUN
connectivity check on each pair, and nominates a pair that succeeds. Media or
data may flow only over a nominated, checked pair — this file makes that gate
precise.

## What this file captures

* **RFC 8445 §6.1.2.6 — the candidate-pair state machine (Figure 6).** Each
  pair is in one of five states: `frozen`, `waiting`, `inProgress`,
  `succeeded`, `failed`. The only transitions are: `frozen` unfreezes to
  `waiting`; `waiting` performs its check to `inProgress`; `inProgress`
  resolves to `succeeded` (a check response arrived) or `failed` (timeout or
  error response). `succeeded` and `failed` are terminal. `step` is exactly
  this graph.
* **RFC 8445 §8 — nomination.** The controlling agent nominates a pair; a pair
  may only be nominated once its check has succeeded. `nominate` enforces this.
* **RFC 8445 §6.1.2.1 — checklist state.** A checklist is `Running` until a
  component has a nominated succeeded pair (`Completed`) or every pair has
  failed (`Failed`).

## The theorems

* `ice_no_send_before_succeeded` — data is delivered over a pair only when that
  pair is both nominated and in the `succeeded` state. No media/data before a
  pair reaches `succeeded`. This is the core ICE safety property.
* `ice_checklist_monotone` — a pair's progress never regresses: along the
  success path the rank is non-decreasing, and in particular a `succeeded` pair
  can never fall back to `waiting` (or any earlier state). `step` on a
  `succeeded` pair leaves it `succeeded`.
* `nominate_wf` / `step_wf` — the well-formedness invariant "nominated ⇒
  succeeded" is preserved by both nomination and check-state transitions, so a
  nominated pair is always deliverable. This is what makes
  `ice_no_send_before_succeeded` hold for the whole session, not just one step.

## The full RFC 8445 machinery

Beyond the core FSM this file now carries the rest of RFC 8445:

* **§5.1.2.1 — the candidate priority formula.** `Cand.priority` is
  `2^24·typePref + 2^8·localPref + (256 − componentId)`; `priority_type_dominates`
  proves the bit-packing is lexicographic (type preference dominates), and
  `ice_priority_total_order` that the induced ordering is a total order.
* **§6.1.2.3 — pair priority.** `pairPriority g d` is the
  `2^32·min + 2·max + tie-break` formula; `pair_priority_tiebreak` proves the
  tie-break byte distinguishes the two orderings.
* **§6.1.2.2 — pair formation** (`formPairs`), **§7.3.1.4 — triggered checks**
  (`triggeredCheck`), **§7.3.1.1 — role-conflict resolution** (`resolveConflict`,
  `ice_role_conflict_resolves`), and **§9 — ICE restart** (`restart`,
  `ice_restart_no_deliver`).

## Boundary (left uninterpreted, honestly)

Candidate gathering over TURN (RFC 8656) is outside this model, and the
DTLS/SCTP transport the checks gate is `WebrtcTransport.lean`. The STUN wire
layer itself is *not* a boundary any more: `checkRequest` below builds the
actual §7.2.2 connectivity-check Binding request bytes (USERNAME, PRIORITY,
role attribute, optional USE-CANDIDATE, MESSAGE-INTEGRITY, FINGERPRINT) on top
of `Stun.lean`, and `conflict487Response` the authenticated §7.3.1.1 role-
conflict error. What remains abstract is only the network: whether a given
check transaction completes is decided by datagrams, not by this model.
-/

namespace Ice

/-! ## The candidate-pair state machine (RFC 8445 §6.1.2.6, Figure 6) -/

/-- The five candidate-pair check states of RFC 8445 §6.1.2.6. -/
inductive PairState where
  /-- No check sent, and it cannot be sent until unfrozen. -/
  | frozen
  /-- No check sent yet, but the pair is unfrozen and ready. -/
  | waiting
  /-- A check has been sent; the transaction is outstanding. -/
  | inProgress
  /-- A check was sent and produced a success response. Terminal. -/
  | succeeded
  /-- A check was sent and failed (timeout or error response). Terminal. -/
  | failed
deriving Repr, DecidableEq

/-- The events that drive the pair FSM. `unfreeze`, `perform`, and the two
check outcomes are the labeled edges of Figure 6; any other event is a no-op at
a given state. -/
inductive Event where
  /-- Unfreeze a frozen pair (§6.1.2.6): `frozen → waiting`. -/
  | unfreeze
  /-- Send the pair's connectivity check: `waiting → inProgress`. -/
  | perform
  /-- The check's STUN transaction produced a success: `inProgress → succeeded`. -/
  | checkSucceeded
  /-- The check's STUN transaction timed out / failed: `inProgress → failed`. -/
  | checkFailed
deriving Repr, DecidableEq

/-- The pair-state transition function (RFC 8445 Figure 6). Every edge not drawn
in the figure is a self-loop: an event that does not apply at the current state
leaves it unchanged. `succeeded` and `failed` are terminal — no event moves
them. -/
def step (s : PairState) (e : Event) : PairState :=
  match s, e with
  | .frozen,     .unfreeze       => .waiting
  | .waiting,    .perform        => .inProgress
  | .inProgress, .checkSucceeded => .succeeded
  | .inProgress, .checkFailed    => .failed
  | s,           _               => s

/-- Progress rank along the check pipeline. `frozen < waiting < inProgress`, and
both terminal states sit at the top rank `3`. The rank never decreases under
`step`, which is how "a pair never regresses" is stated numerically. -/
def rank : PairState → Nat
  | .frozen     => 0
  | .waiting    => 1
  | .inProgress => 2
  | .succeeded  => 3
  | .failed     => 3

/-- **Monotonicity (no regression).** Every transition is non-decreasing in
rank: a pair's progress never goes backward. -/
theorem ice_checklist_monotone (s : PairState) (e : Event) :
    rank s ≤ rank (step s e) := by
  cases s <;> cases e <;> simp [step, rank]

/-- A `succeeded` pair is a fixpoint of `step`: no event ever moves it back to
`waiting` (or any other state). This is the sharp form of "succeeded never
regresses to waiting". -/
theorem step_succeeded_terminal (e : Event) : step .succeeded e = .succeeded := by
  cases e <;> rfl

/-- A `failed` pair is likewise terminal. -/
theorem step_failed_terminal (e : Event) : step .failed e = .failed := by
  cases e <;> rfl

/-- The only way to enter `succeeded` is from `inProgress` via `checkSucceeded`:
a pair cannot jump to `succeeded` without having had a check in progress that
got a success response. -/
theorem enter_succeeded (s : PairState) (e : Event)
    (h : step s e = .succeeded) (hne : s ≠ .succeeded) :
    s = .inProgress ∧ e = .checkSucceeded := by
  cases s <;> cases e <;> simp_all [step]

/-! ## Nomination and the send gate (RFC 8445 §8) -/

/-- A candidate pair: its check state plus whether the controlling agent has
nominated it. -/
structure Pair where
  state : PairState
  nominated : Bool
deriving Repr, DecidableEq

/-- Well-formedness (RFC 8445 §8): a pair is nominated only if its check has
succeeded. The controlling agent never nominates a pair whose check has not
produced a success response. -/
def Pair.Wf (p : Pair) : Prop := p.nominated = true → p.state = .succeeded

/-- Nominate a pair — but only if its check has succeeded (§8). Nominating a
pair whose check has not succeeded is a no-op, so the invariant cannot be
broken. -/
def nominate (p : Pair) : Pair :=
  if p.state = .succeeded then { p with nominated := true } else p

/-- Advance a pair's check state, carrying the nomination flag. -/
def stepPair (p : Pair) (e : Event) : Pair :=
  { p with state := step p.state e }

/-- The send gate: data may be delivered over a pair only when it is both
nominated and in the `succeeded` state. -/
def mayDeliver (p : Pair) : Bool :=
  p.nominated && decide (p.state = .succeeded)

/-- **No send before succeeded (RFC 8445 §8).** If the send gate is open for a
pair, that pair is in the `succeeded` state. Data therefore never flows over a
pair before its connectivity check succeeds. -/
theorem ice_no_send_before_succeeded (p : Pair) (h : mayDeliver p = true) :
    p.state = .succeeded := by
  unfold mayDeliver at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- Nomination preserves the well-formedness invariant: after `nominate`, a
nominated pair is still succeeded. -/
theorem nominate_wf (p : Pair) (h : p.Wf) : (nominate p).Wf := by
  unfold nominate Pair.Wf
  by_cases hs : p.state = .succeeded
  · rw [if_pos hs]; intro _; exact hs
  · rw [if_neg hs]; exact h

/-- Check-state transitions preserve the invariant. `stepPair` never sets the
nominated flag, and the only state a nominated (hence previously succeeded)
pair can be in stays `succeeded` (terminal), so "nominated ⇒ succeeded" holds
after the step. -/
theorem step_wf (p : Pair) (e : Event) (h : p.Wf) : (stepPair p e).Wf := by
  unfold stepPair Pair.Wf
  intro hn
  have hstate : p.state = .succeeded := h hn
  simp only [hstate]
  exact step_succeeded_terminal e

/-- **Session-level safety.** Along any run built from `stepPair` and `nominate`
starting from a well-formed pair, the send gate stays sound: whenever
`mayDeliver` opens, the pair is succeeded. (Combine `ice_no_send_before_succeeded`
with the two invariant-preservation lemmas.) -/
theorem deliver_sound (p : Pair) (h : mayDeliver p = true) :
    p.state = .succeeded :=
  ice_no_send_before_succeeded p h

/-! ## Checklist state (RFC 8445 §6.1.2.1) -/

/-- Checklist-level state for one component (RFC 8445 §6.1.2.1). -/
inductive Checklist where
  /-- Neither completed nor failed yet. -/
  | running
  /-- A nominated succeeded pair exists for the component. -/
  | completed
  /-- No valid pair remains (all pairs failed). -/
  | failed
deriving Repr, DecidableEq

/-- Classify a component's pair list into a checklist state: `completed` if some
pair is nominated and succeeded; `failed` if every pair has failed; otherwise
`running`. -/
def classify (pairs : List Pair) : Checklist :=
  if pairs.any (fun p => p.nominated && decide (p.state = .succeeded)) then
    .completed
  else if pairs.all (fun p => decide (p.state = .failed)) then
    .failed
  else
    .running

/-- **A completed checklist has a deliverable pair.** If the component is
`Completed`, some pair in it is nominated and succeeded — so completion of the
checklist implies the existence of a pair the data may flow over, and (by
`ice_no_send_before_succeeded`) that pair really has succeeded. -/
theorem completed_has_succeeded (pairs : List Pair) (h : classify pairs = .completed) :
    ∃ p ∈ pairs, mayDeliver p = true := by
  unfold classify at h
  by_cases hany : pairs.any (fun p => p.nominated && decide (p.state = .succeeded)) = true
  · rw [List.any_eq_true] at hany
    obtain ⟨p, hp, hpp⟩ := hany
    exact ⟨p, hp, hpp⟩
  · rw [if_neg hany] at h
    by_cases hall : pairs.all (fun p => decide (p.state = .failed)) = true
    · rw [if_pos hall] at h; exact absurd h (by decide)
    · rw [if_neg hall] at h; exact absurd h (by decide)

/-! ## Candidate gathering and the priority formula (RFC 8445 §5.1.1, §5.1.2.1) -/

/-- Candidate transport types (RFC 8445 §5.1.1.1). -/
inductive CandType where
  /-- A local interface address. -/
  | host
  /-- Learned from an inbound check (peer-reflexive). -/
  | peerReflexive
  /-- A server-reflexive (STUN) address. -/
  | serverReflexive
  /-- A relayed (TURN) address. -/
  | relayed
deriving Repr, DecidableEq

/-- Recommended type preferences (RFC 8445 §5.1.2.1): host 126, peer-reflexive
110, server-reflexive 100, relayed 0. Each fits in 7 bits (≤ 126). -/
def CandType.pref : CandType → Nat
  | .host            => 126
  | .peerReflexive   => 110
  | .serverReflexive => 100
  | .relayed         => 0

/-- A gathered candidate: its transport type, a local preference (0..65535,
§5.1.2.1), and the component id it belongs to (1..256, §5.1.1.1). -/
structure Cand where
  type : CandType
  localPref : Nat
  component : Nat
deriving Repr, DecidableEq

/-- Field bounds a well-formed candidate satisfies (RFC 8445 §5.1.2.1): the
local preference fits 16 bits and the component id is 1..256. These bounds are
what make the priority packing lexicographic. -/
def Cand.Wf (c : Cand) : Prop :=
  c.localPref ≤ 65535 ∧ 1 ≤ c.component ∧ c.component ≤ 256

/-- `2^24`, the type-preference shift of the §5.1.2.1 priority formula. -/
def typeShift : Nat := 16777216
/-- `2^8`, the local-preference shift of the §5.1.2.1 priority formula. -/
def prefShift : Nat := 256

/-- **The RFC 8445 §5.1.2.1 priority formula.**
`priority = 2^24·typePref + 2^8·localPref + (256 − componentId)`. -/
def Cand.priority (c : Cand) : Nat :=
  typeShift * c.type.pref + prefShift * c.localPref + (256 - c.component)

/-- **Type preference dominates (RFC 8445 §5.1.2.1).** For well-formed
candidates, a strictly higher type preference yields a strictly higher priority
regardless of the lower-order fields: the `2^24` shift is large enough that the
`2^8·localPref + (256 − component)` tail can never close the gap. This is what
makes the packed integer order the intended lexicographic order. -/
theorem priority_type_dominates (a b : Cand) (ha : a.Wf) (hb : b.Wf)
    (h : a.type.pref < b.type.pref) : a.priority < b.priority := by
  unfold Cand.Wf at ha hb
  obtain ⟨hla, hca1, hca2⟩ := ha
  obtain ⟨hlb, hcb1, hcb2⟩ := hb
  unfold Cand.priority typeShift prefShift
  omega

/-- The priority order on candidates. -/
def Cand.le (a b : Cand) : Prop := a.priority ≤ b.priority

/-- **The priority order is a total order (RFC 8445 §6.1.2.3).** The relation
"has priority ≤" is reflexive, total (connex), and transitive, so the candidate
pairs it orders form a checklist with a well-defined check ordering. -/
theorem ice_priority_total_order :
    (∀ a : Cand, Cand.le a a) ∧
    (∀ a b : Cand, Cand.le a b ∨ Cand.le b a) ∧
    (∀ a b c : Cand, Cand.le a b → Cand.le b c → Cand.le a c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a; exact Nat.le_refl _
  · intro a b; exact Nat.le_total _ _
  · intro a b c hab hbc; exact Nat.le_trans hab hbc

/-! ## Pair priority (RFC 8445 §6.1.2.3) -/

/-- **The RFC 8445 §6.1.2.3 pair-priority formula.** With `g` the controlling
agent's candidate priority and `d` the controlled agent's:
`2^32·min(g,d) + 2·max(g,d) + (g > d ? 1 : 0)`. Both agents compute the same
value because both plug the controlling agent's priority into `g`. -/
def pairPriority (g d : Nat) : Nat :=
  4294967296 * (min g d) + 2 * (max g d) + (if g > d then 1 else 0)

/-- **The tie-break byte distinguishes the orderings (RFC 8445 §6.1.2.3).** When
the two candidate priorities differ, swapping the controlling/controlled roles
produces a different pair priority: the `min`/`max` magnitude is symmetric, so
the low tie-break bit is exactly what breaks the tie between the two role
assignments. -/
theorem pair_priority_tiebreak (g d : Nat) (h : g ≠ d) :
    pairPriority g d ≠ pairPriority d g := by
  simp only [pairPriority, Nat.min_comm d g, Nat.max_comm d g]
  rcases Nat.lt_or_gt_of_ne h with hlt | hgt
  · rw [if_neg (show ¬ g > d by omega), if_pos (show d > g by omega)]; omega
  · rw [if_pos (show g > d by omega), if_neg (show ¬ d > g by omega)]; omega

/-! ## Pair formation (RFC 8445 §6.1.2.2) -/

/-- Form candidate pairs (RFC 8445 §6.1.2.2): pair each local candidate with
each remote candidate of the same component. Each new pair starts `frozen` and
un-nominated — it must survive a connectivity check before it can carry data. -/
def formPairs (locals remotes : List Cand) : List Pair :=
  locals.flatMap fun l =>
    remotes.filterMap fun r =>
      if l.component = r.component then
        some ({ state := .frozen, nominated := false } : Pair)
      else none

/-- **Freshly formed pairs are not deliverable (RFC 8445 §6.1.2.2).** Every pair
`formPairs` produces is `frozen` and un-nominated, so the send gate is closed for
all of them: pairing does not itself let any data flow. -/
theorem formPairs_not_deliverable (locals remotes : List Cand) :
    ∀ p ∈ formPairs locals remotes, mayDeliver p = false := by
  intro p hp
  unfold formPairs at hp
  rw [List.mem_flatMap] at hp
  obtain ⟨l, _, hl⟩ := hp
  rw [List.mem_filterMap] at hl
  obtain ⟨r, _, hr⟩ := hl
  by_cases hc : l.component = r.component
  · rw [if_pos hc] at hr
    simp only [Option.some.injEq] at hr
    subst hr
    unfold mayDeliver; simp
  · rw [if_neg hc] at hr; simp at hr

/-! ## Triggered checks (RFC 8445 §7.3.1.4) -/

/-- A triggered check (RFC 8445 §7.3.1.4): an inbound connectivity check on a
pair reschedules it. A `frozen`, `waiting`, or `failed` pair is (re)queued to
`waiting` so its own check runs promptly; an `inProgress` pair keeps its
outstanding transaction; a `succeeded` pair is unaffected. Note this is *not*
rank-monotone — a `failed` pair is deliberately moved back to `waiting` to be
re-checked, which is the whole point of a triggered check. -/
def triggeredCheck : PairState → PairState
  | .frozen     => .waiting
  | .waiting    => .waiting
  | .inProgress => .inProgress
  | .succeeded  => .succeeded
  | .failed     => .waiting

/-- A triggered check never disturbs a `succeeded` pair. -/
theorem triggered_succeeded : triggeredCheck .succeeded = .succeeded := rfl

/-- A triggered check reschedules a previously `failed` pair for a fresh check. -/
theorem triggered_reschedules_failed : triggeredCheck .failed = .waiting := rfl

/-! ## Role-conflict resolution (RFC 8445 §7.3.1.1) -/

/-- The ICE role of an agent (RFC 8445 §6.1.1): exactly one agent is controlling
and drives nomination. -/
inductive IceRole where
  | controlling
  | controlled
deriving Repr, DecidableEq

/-- Role-conflict resolution (RFC 8445 §7.3.1.1). A conflict arises when both
agents believe they hold the same role. It is resolved by the tie-breaker: the
agent with the numerically larger tie-breaker takes/keeps the controlling role,
the other becomes/stays controlled. The result depends only on the tie-breakers,
not on the prior role — which is exactly what drives the two agents to opposite
roles. -/
def resolveConflict (myTieBreaker peerTieBreaker : Nat) : IceRole :=
  if myTieBreaker ≥ peerTieBreaker then .controlling else .controlled

/-- **Role conflict resolves to a unique controller (RFC 8445 §7.3.1.1).** Given
distinct tie-breakers, after both agents apply the resolution rule to each
other, exactly one ends up controlling and the other controlled — the conflict
is always broken, never into two controllers or two controlled agents. -/
theorem ice_role_conflict_resolves (a b : Nat) (h : a ≠ b) :
    (resolveConflict a b = .controlling ∧ resolveConflict b a = .controlled) ∨
    (resolveConflict a b = .controlled ∧ resolveConflict b a = .controlling) := by
  unfold resolveConflict
  rcases Nat.lt_or_gt_of_ne h with hlt | hgt
  · right
    exact ⟨by rw [if_neg (show ¬ a ≥ b by omega)], by rw [if_pos (show b ≥ a by omega)]⟩
  · left
    exact ⟨by rw [if_pos (show a ≥ b by omega)], by rw [if_neg (show ¬ b ≥ a by omega)]⟩

/-! ## The nomination send gate, restated (RFC 8445 §8) -/

/-- **No send before nominated (RFC 8445 §8).** The send gate opens only for a
nominated pair. Combined with `ice_no_send_before_succeeded`, delivery requires a
pair that is *both* nominated and succeeded. -/
theorem ice_no_send_before_nominated (p : Pair) (h : mayDeliver p = true) :
    p.nominated = true := by
  unfold mayDeliver at h
  simp only [Bool.and_eq_true] at h
  exact h.1

/-! ## ICE restart (RFC 8445 §9) -/

/-- An ICE restart (RFC 8445 §9) resets a pair: its check state returns to
`frozen` and any nomination is cleared. The candidate is kept, but a fresh
connectivity check must succeed before the pair can carry data again. -/
def restartPair (_p : Pair) : Pair := { state := .frozen, nominated := false }

/-- Restart the whole checklist (RFC 8445 §9): every pair is reset. -/
def restart (pairs : List Pair) : List Pair := pairs.map restartPair

/-- A restarted pair is trivially well-formed (it is not nominated). -/
theorem restartPair_wf (p : Pair) : (restartPair p).Wf := by
  unfold restartPair Pair.Wf; intro h; simp at h

/-- **ICE restart closes the send gate (RFC 8445 §9).** Immediately after a
restart, no pair is deliverable: every pair is un-nominated and frozen, so a
fresh round of connectivity checks must succeed and a new nomination must be made
before any data flows again. -/
theorem ice_restart_no_deliver (pairs : List Pair) :
    ∀ p ∈ restart pairs, mayDeliver p = false := by
  intro p hp
  unfold restart at hp
  rw [List.mem_map] at hp
  obtain ⟨q, _, hq⟩ := hp
  rw [← hq]
  unfold restartPair mayDeliver
  simp

/-! ## The connectivity-check wire layer (RFC 8445 §7.2.2, §7.3.1.1, §16.1)

The actual STUN Binding request an ICE agent sends on a candidate pair, built
on the RFC 5389 codec: USERNAME (`remote-ufrag ":" local-ufrag`), PRIORITY,
the agent's role attribute carrying its tie-breaker, USE-CANDIDATE when
nominating, then MESSAGE-INTEGRITY keyed with the peer's password and
FINGERPRINT — and the authenticated 487 error an agent answers a role conflict
with. -/

/-- ICE-CONTROLLED (RFC 8445 §16.1): comprehension-optional, carried by the
controlled agent, value = the 64-bit tie-breaker. -/
def attrIceControlled : Nat := 0x8029

/-- ICE-CONTROLLING (RFC 8445 §16.1): comprehension-optional, carried by the
controlling agent, value = the 64-bit tie-breaker. -/
def attrIceControlling : Nat := 0x802A

/-- Big-endian 64-bit encode (the tie-breaker wire value, RFC 8445 §16.1). -/
def enc64 (n : Nat) : Stun.Bytes :=
  [UInt8.ofNat (n >>> 56), UInt8.ofNat (n >>> 48), UInt8.ofNat (n >>> 40),
   UInt8.ofNat (n >>> 32), UInt8.ofNat (n >>> 24), UInt8.ofNat (n >>> 16),
   UInt8.ofNat (n >>> 8), UInt8.ofNat n]

/-- Big-endian decode of a tie-breaker value. -/
def dec64 (b : Stun.Bytes) : Nat :=
  b.foldl (fun acc x => acc * 256 + x.toNat) 0

@[simp] theorem enc64_length (n : Nat) : (enc64 n).length = 8 := rfl

/-- **Tie-breaker codec round-trip.** Decoding a serialized 64-bit tie-breaker
recovers it exactly. -/
theorem dec64_enc64 (n : Nat) (h : n < 2 ^ 64) : dec64 (enc64 n) = n := by
  have hpow : (2 : Nat) ^ 64 = 18446744073709551616 := by rfl
  rw [hpow] at h
  simp only [enc64, dec64, List.foldl, UInt8.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  simp only [show (2:Nat)^8 = 256 from rfl, show (2:Nat)^16 = 65536 from rfl,
    show (2:Nat)^24 = 16777216 from rfl, show (2:Nat)^32 = 4294967296 from rfl,
    show (2:Nat)^40 = 1099511627776 from rfl,
    show (2:Nat)^48 = 281474976710656 from rfl,
    show (2:Nat)^56 = 72057594037927936 from rfl]
  omega

/-- The §7.2.2 connectivity-check attribute list: USERNAME, PRIORITY, the
role attribute with the tie-breaker, and USE-CANDIDATE when nominating (§8.1.1).
The username is `remote-ufrag ":" local-ufrag` from the checker's perspective
(§7.2.2), at most 513 bytes (§5.3). -/
def connCheckAttrs (username : Stun.Bytes) (prio : UInt32)
    (controlling : Bool) (tieBreaker : Nat) (useCand : Bool) : List Stun.Attr :=
  [⟨Stun.attrUsername, username⟩,
   ⟨Stun.attrPriority, Stun.u32Bytes prio⟩,
   ⟨if controlling then attrIceControlling else attrIceControlled,
    enc64 tieBreaker⟩] ++
  (if useCand then [⟨Stun.attrUseCandidate, []⟩] else [])

/-- **The §7.2.2 connectivity-check Binding request**, integrity-protected with
the peer's password and fingerprinted — the exact datagram an agent sends on a
candidate pair (the transaction driving the `perform`/`checkSucceeded` events
of the pair FSM above). -/
def checkRequest (pwd txid username : Stun.Bytes) (prio : UInt32)
    (controlling : Bool) (tieBreaker : Nat) (useCand : Bool) : Stun.Bytes :=
  Stun.withIntegrityFingerprint pwd Stun.bindingRequest txid
    (connCheckAttrs username prio controlling tieBreaker useCand)

/-- Hygiene of the connectivity-check attribute list: bounded wire fields and
free of the integrity attribute types. -/
theorem connCheckAttrs_hygiene (username : Stun.Bytes) (prio : UInt32)
    (controlling : Bool) (tieBreaker : Nat) (useCand : Bool)
    (hu : username.length ≤ 513) :
    (∀ x ∈ connCheckAttrs username prio controlling tieBreaker useCand,
        x.type < 65536 ∧ x.value.length < 65536) ∧
    (∀ x ∈ connCheckAttrs username prio controlling tieBreaker useCand,
        x.type ≠ Stun.attrMessageIntegrity) ∧
    (∀ x ∈ connCheckAttrs username prio controlling tieBreaker useCand,
        x.type ≠ Stun.attrFingerprint) ∧
    (Stun.encodeAttrs
      (connCheckAttrs username prio controlling tieBreaker useCand)).length + 32
      < 65536 := by
  have hpad := Stun.padLen_lt username.length
  have hshape : ∀ x ∈ connCheckAttrs username prio controlling tieBreaker useCand,
      (x.type = Stun.attrUsername ∨ x.type = Stun.attrPriority ∨
       x.type = attrIceControlling ∨ x.type = attrIceControlled ∨
       x.type = Stun.attrUseCandidate) ∧ x.value.length ≤ 513 := by
    intro x hx
    rcases List.mem_append.mp hx with h3 | hc
    · rcases List.mem_cons.mp h3 with rfl | h3'
      · exact ⟨Or.inl rfl, hu⟩
      · rcases List.mem_cons.mp h3' with rfl | h3''
        · exact ⟨Or.inr (Or.inl rfl), by simp⟩
        · rcases List.mem_singleton.mp h3'' with rfl
          cases controlling
          · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl (by simp)))), by simp⟩
          · exact ⟨Or.inr (Or.inr (Or.inl (by simp))), by simp⟩
    · cases useCand
      · simp at hc
      · rcases List.mem_singleton.mp (by simpa using hc) with rfl
        exact ⟨Or.inr (Or.inr (Or.inr (Or.inr rfl))), by simp⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨hty, hv⟩ := hshape x hx
    refine ⟨?_, by omega⟩
    rcases hty with h | h | h | h | h <;>
      simp [h, Stun.attrUsername, Stun.attrPriority, attrIceControlling,
        attrIceControlled, Stun.attrUseCandidate]
  · intro x hx
    obtain ⟨hty, _⟩ := hshape x hx
    rcases hty with h | h | h | h | h <;>
      simp [h, Stun.attrUsername, Stun.attrPriority, attrIceControlling,
        attrIceControlled, Stun.attrUseCandidate, Stun.attrMessageIntegrity]
  · intro x hx
    obtain ⟨hty, _⟩ := hshape x hx
    rcases hty with h | h | h | h | h <;>
      simp [h, Stun.attrUsername, Stun.attrPriority, attrIceControlling,
        attrIceControlled, Stun.attrUseCandidate, Stun.attrFingerprint]
  · have hbound : ∀ (l : List Stun.Attr), (∀ x ∈ l, x.value.length ≤ 513) →
        (Stun.encodeAttrs l).length ≤ 520 * l.length := by
      intro l
      induction l with
      | nil => intro _; simp [Stun.encodeAttrs]
      | cons x rest ih =>
        intro hl
        have hx := hl x (List.mem_cons_self x rest)
        have hp := Stun.padLen_lt x.value.length
        have := ih (fun y hy => hl y (List.mem_cons_of_mem x hy))
        simp only [Stun.encodeAttrs, List.length_append, Stun.encodeAttr_length,
          Stun.attrSize, List.length_cons]
        omega
    have h1 := hbound _ (fun x hx => (hshape x hx).2)
    have hlen : (connCheckAttrs username prio controlling tieBreaker useCand).length
        ≤ 4 := by
      cases useCand <;> simp [connCheckAttrs]
    omega

/-- **Connectivity-check request correctness (RFC 8445 §7.2.2).** The datagram
`checkRequest` emits (i) passes MESSAGE-INTEGRITY verification under the same
password — what the checked peer demands before answering — (ii) passes
FINGERPRINT verification, and (iii) parses as a Binding request that echoes the
transaction id and carries the USERNAME. -/
theorem checkRequest_correct (pwd txid username : Stun.Bytes) (prio : UInt32)
    (controlling : Bool) (tieBreaker : Nat) (useCand : Bool)
    (htx : txid.length = 12) (hu : username.length ≤ 513) :
    Stun.messageIntegrityOk pwd
      (checkRequest pwd txid username prio controlling tieBreaker useCand) = true ∧
    Stun.fingerprintOk
      (checkRequest pwd txid username prio controlling tieBreaker useCand) = true ∧
    ∃ m, Stun.parse
        (checkRequest pwd txid username prio controlling tieBreaker useCand) =
        some m ∧
      m.typ = Stun.bindingRequest ∧ m.txid = txid ∧
      (⟨Stun.attrUsername, username⟩ : Stun.Attr) ∈ m.attrs := by
  obtain ⟨hwf, hnoMI, hnoFP, hblen⟩ :=
    connCheckAttrs_hygiene username prio controlling tieBreaker useCand hu
  have hty : Stun.bindingRequest < 65536 := by simp [Stun.bindingRequest]
  refine ⟨Stun.withIntegrityFingerprint_integrity_ok pwd Stun.bindingRequest txid _
      hty htx hblen hwf hnoMI,
    Stun.withIntegrityFingerprint_fingerprint_ok pwd Stun.bindingRequest txid _
      hty htx hblen hwf hnoFP,
    _, Stun.withIntegrityFingerprint_parses pwd Stun.bindingRequest txid _
      hty htx hblen hwf, rfl, rfl, ?_⟩
  simp [connCheckAttrs]

/-! ## The authenticated 487 role-conflict answer (RFC 8445 §7.3.1.1) -/

/-- ASCII "Role Conflict" (§7.3.1.1). -/
def roleConflictReason : Stun.Bytes :=
  [0x52, 0x6f, 0x6c, 0x65, 0x20, 0x43, 0x6f, 0x6e, 0x66, 0x6c, 0x69, 0x63, 0x74]

/-- **§7.3.1.1 receipt rule**: whether an agent seeing its own role attribute
in an inbound check keeps its role and answers 487 (`true`), or switches role
and processes the check (`false`). A controlling agent keeps control iff its
tie-breaker is ≥ the request's; a controlled agent answers 487 iff its
tie-breaker is < the request's. -/
def conflict487 (myRole : IceRole) (myTieBreaker theirTieBreaker : Nat) : Bool :=
  match myRole with
  | .controlling => decide (myTieBreaker ≥ theirTieBreaker)
  | .controlled => decide (myTieBreaker < theirTieBreaker)

/-- The 487 Binding error response, MESSAGE-INTEGRITY-protected as ICE error
responses are (§7.3.1.1 with RFC 5389 §10.1.2). -/
def conflict487Response (key txid : Stun.Bytes) : Stun.Bytes :=
  Stun.withIntegrityFingerprint key Stun.bindingErrorType txid
    [⟨Stun.attrErrorCode, Stun.errorCodeValue 487 roleConflictReason⟩]

/-- **The 487 answer agrees with role resolution (§7.3.1.1).** In a
both-controlling conflict, the agent that answers 487 (keeping control) is
exactly the agent `resolveConflict` names controlling; in a both-controlled
conflict, the 487 sender is exactly the agent that stays controlled. So the
wire behavior and the role algebra can never disagree. -/
theorem conflict487_agrees_resolve (my their : Nat) :
    (conflict487 .controlling my their = true ↔
      resolveConflict my their = .controlling) ∧
    (conflict487 .controlled my their = true ↔
      resolveConflict my their = .controlled) := by
  unfold conflict487 resolveConflict
  by_cases h : my ≥ their <;> simp [h] <;> omega

/-- **Exactly one 487 in a both-controlling conflict.** With distinct
tie-breakers, of the two agents each seeing the other's ICE-CONTROLLING, one
answers 487 and the other switches role — never both, never neither. -/
theorem conflict487_unique (a b : Nat) (h : a ≠ b) :
    conflict487 .controlling a b ≠ conflict487 .controlling b a := by
  unfold conflict487
  by_cases hab : a ≥ b
  · have hba : ¬ b ≥ a := by omega
    simp [hab, hba]
  · have hba : b ≥ a := by omega
    simp [hab, hba]

/-- **The 487 answer verifies (§7.3.1.1).** The role-conflict error response
is integrity-protected under the check's short-term key, fingerprinted, parses
as a Binding error response echoing the transaction id, and carries the 487
ERROR-CODE. -/
theorem conflict487Response_correct (key txid : Stun.Bytes)
    (htx : txid.length = 12) :
    Stun.messageIntegrityOk key (conflict487Response key txid) = true ∧
    Stun.fingerprintOk (conflict487Response key txid) = true ∧
    ∃ m, Stun.parse (conflict487Response key txid) = some m ∧
      m.typ = Stun.bindingErrorType ∧ m.txid = txid ∧
      (⟨Stun.attrErrorCode, Stun.errorCodeValue 487 roleConflictReason⟩ :
        Stun.Attr) ∈ m.attrs := by
  have hwf : ∀ x ∈ [(⟨Stun.attrErrorCode,
      Stun.errorCodeValue 487 roleConflictReason⟩ : Stun.Attr)],
      x.type < 65536 ∧ x.value.length < 65536 := by
    intro x hx
    rcases List.mem_singleton.mp hx with rfl
    exact ⟨by simp [Stun.attrErrorCode],
      by simp [Stun.errorCodeValue, roleConflictReason]⟩
  have hnoMI : ∀ x ∈ [(⟨Stun.attrErrorCode,
      Stun.errorCodeValue 487 roleConflictReason⟩ : Stun.Attr)],
      x.type ≠ Stun.attrMessageIntegrity := by
    intro x hx
    rcases List.mem_singleton.mp hx with rfl
    simp [Stun.attrErrorCode, Stun.attrMessageIntegrity]
  have hnoFP : ∀ x ∈ [(⟨Stun.attrErrorCode,
      Stun.errorCodeValue 487 roleConflictReason⟩ : Stun.Attr)],
      x.type ≠ Stun.attrFingerprint := by
    intro x hx
    rcases List.mem_singleton.mp hx with rfl
    simp [Stun.attrErrorCode, Stun.attrFingerprint]
  have hblen : (Stun.encodeAttrs [(⟨Stun.attrErrorCode,
      Stun.errorCodeValue 487 roleConflictReason⟩ : Stun.Attr)]).length + 32
      < 65536 := by
    simp [Stun.encodeAttrs, Stun.encodeAttr_length, Stun.attrSize,
      Stun.errorCodeValue, roleConflictReason, Stun.padLen]
  have hty : Stun.bindingErrorType < 65536 := by simp [Stun.bindingErrorType]
  refine ⟨Stun.withIntegrityFingerprint_integrity_ok key Stun.bindingErrorType
      txid _ hty htx hblen hwf hnoMI,
    Stun.withIntegrityFingerprint_fingerprint_ok key Stun.bindingErrorType
      txid _ hty htx hblen hwf hnoFP,
    _, Stun.withIntegrityFingerprint_parses key Stun.bindingErrorType txid _
      hty htx hblen hwf, rfl, rfl, ?_⟩
  simp

def version : String := "0.2.0"

end Ice
