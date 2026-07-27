import Mux.Scheduler
import Mux.RoundRobin

/-!
# Correctness of RFC 9218 stream scheduling (Extensible Priorities)

`Mux/Scheduler.lean` establishes *safety* facts about the stream picker `select`
— it never picks an idle stream, it is total, the chosen stream has minimal
urgency. Those are stated in terms of the implementation's own `Priority.rank`
encoding `rank ⟨u,i⟩ = 2*u + (if i then 1 else 0)`. They do not, on their own,
say that this arithmetic encoding *is* the order RFC 9218 mandates: that the
picker serves streams in the order the specification dictates and no other.

This file upgrades that to a *correctness* claim. It gives an **independent
specification** of the RFC 9218 scheduling order, transcribed *from the RFC's
prose*, as a strict relation `RfcServesBefore` that mentions no part of the
implementation — not `Priority.rank`, not `slt`/`sle`, not `bestOf`. The order
is written lexicographically over the three observable priority signals:

* **urgency** (RFC 9218 §4.1): an integer where *lower values are scheduled
  first*;
* **incremental class** (RFC 9218 §4.2, §10): within one urgency band a
  non-incremental resource is served before an incremental one, stated directly
  as the boolean relation "a is non-incremental and b is incremental" — no
  arithmetic;
* **stream id** (RFC 9218 §10 / RFC 9113 §5.1.1): within one urgency band and
  one class, the lower stream id is served first.

`RfcNext streams s` then names the RFC-mandated next stream: a pending member no
pending stream serves strictly before.

Then it proves the deployed picker **refines** that specification, and does so
non-vacuously:

* `slt_iff_rfc` — the implementation's arithmetic `rank`-order is *equivalent*
  to the independent RFC lexicographic order. This is the bridge that gives the
  refinement content: the `2*u + bit` encoding is proven to compute the RFC
  order, it is not assumed to.
* `select_refines_rfc` — the deployed `Mux.select` returns an `RfcNext` stream
  on every input. This binds the deployed function, not a wrapper.
* `select_is_rfc_next` — the productive converse: whenever a stream pends,
  `select` produces exactly an `RfcNext` stream.
* `rfc_next_prio_id` — `RfcNext` pins the priority and id uniquely, so `select`
  computes *the* RFC choice, not merely *an* admissible one.

Non-vacuity is witnessed concretely and against the deployed function:

* `deployed_serves_urgency` — a scheduler that ignored urgency and served the
  higher-urgency-value stream would falsify `select_refines_rfc`; `Mux.select`
  provably cannot return it.
* `deployed_serves_class` — the same for a scheduler that served an incremental
  stream ahead of a same-urgency non-incremental one.
* `rrServe_isRoundRobin` / `headServer_not_roundRobin` — the round-robin band
  fairness of RFC 9218 §10 is an independent spec `RfcRoundRobin` that
  `Mux.RoundRobin.rrServe` satisfies, and that a head-repeating (starving)
  server provably fails. A picker that violated round-robin within a band is
  rejected by the specification.

## The RFC text specified here

* **RFC 9218 §4.1 (urgency):** "The value is encoded as an integer between 0 and
  7 … a lower value indicates that the request should be treated as more
  important … A client SHOULD … Servers SHOULD … prioritize … in increasing
  order of urgency values."
* **RFC 9218 §4.2 (incremental):** a boolean; a non-incremental response
  "benefits from being transmitted in full before the next", an incremental one
  benefits from being interleaved.
* **RFC 9218 §10 (Scheduling):** "A server SHOULD respect the urgency … at the
  same urgency level, a server SHOULD distribute the bandwidth … non-incremental
  responses … in the order in which they arrive … incremental responses … by
  sharing bandwidth among them (round-robin)."
-/

namespace MuxPriorityCorrect

/-! ## The independent RFC 9218 scheduling order -/

/-- **RFC 9218 scheduling order (independent specification).** `a` is served
strictly before `b`, transcribed from RFC 9218 §4.1, §4.2, §10 as a lexicographic
comparison over the three priority signals — *no* reference to the
implementation's `Priority.rank` arithmetic:

1. lower urgency value is served first (§4.1);
2. at equal urgency, a non-incremental resource precedes an incremental one
   (§4.2, §10), stated as the boolean relation "`a` non-incremental, `b`
   incremental";
3. at equal urgency and equal class, the lower stream id is served first (§10). -/
def RfcServesBefore (a b : Mux.Stream) : Prop :=
  a.prio.urgency < b.prio.urgency
  ∨ (a.prio.urgency = b.prio.urgency
      ∧ a.prio.incremental = false ∧ b.prio.incremental = true)
  ∨ (a.prio.urgency = b.prio.urgency
      ∧ a.prio.incremental = b.prio.incremental ∧ a.id < b.id)

/-- **The RFC-mandated next stream.** `s` is a pending member of the connection
that no pending stream serves strictly before — the minimum of `RfcServesBefore`
over the pending streams. Defined purely from the specification order. -/
def RfcNext (streams : List Mux.Stream) (s : Mux.Stream) : Prop :=
  s ∈ streams ∧ s.hasPending = true ∧
    ∀ t ∈ streams, t.hasPending = true → ¬ RfcServesBefore t s

/-! ## The bridge: the `rank` encoding computes the RFC order -/

/-- **The implementation order equals the RFC order.** The deployed strict order
`Mux.slt` (built from the `2*u + bit` rank encoding) holds exactly when the
independent RFC lexicographic order does. This is the load-bearing step: it
proves the arithmetic encoding *is* the specified order rather than assuming it.
An encoding that ordered the bands differently would make one direction FALSE. -/
theorem slt_iff_rfc (a b : Mux.Stream) : Mux.slt a b ↔ RfcServesBefore a b := by
  obtain ⟨ai, ⟨au, ainc⟩, aq⟩ := a
  obtain ⟨bi, ⟨bu, binc⟩, bq⟩ := b
  simp only [Mux.slt, RfcServesBefore, Mux.Priority.rank]
  cases ainc <;> cases binc <;>
    simp only [Mux.StreamId] at ai bi ⊢ <;> simp <;> omega

/-! ## The refinement: `Mux.select` returns the RFC next stream -/

/-- If `a` is no later than `b` in the deployed order, then `b` does not serve
strictly before `a` in the RFC order. -/
theorem sle_not_rfc_before {a b : Mux.Stream} (h : Mux.sle a b) :
    ¬ RfcServesBefore b a := by
  rw [← slt_iff_rfc]
  unfold Mux.sle at h
  unfold Mux.slt
  simp only [Mux.StreamId] at h ⊢
  omega

/-- **Refinement (the headline).** The deployed picker `Mux.select` returns, on
every connection, a stream that is the RFC-mandated next stream. This binds the
deployed function directly. -/
theorem select_refines_rfc {streams : List Mux.Stream} {s : Mux.Stream}
    (h : Mux.select streams = some s) : RfcNext streams s := by
  obtain ⟨hp, hmem⟩ := Mux.select_pending_mem h
  refine ⟨hmem, hp, ?_⟩
  intro t ht htp
  have hmemf : t ∈ streams.filter Mux.Stream.hasPending :=
    List.mem_filter.mpr ⟨ht, htp⟩
  exact sle_not_rfc_before (Mux.bestOf_min h t hmemf)

/-- **Productive converse.** Whenever some stream pends, `Mux.select` produces a
stream and that stream is the RFC next. Together with `select_refines_rfc` this
says the picker computes the RFC next exactly. -/
theorem select_is_rfc_next {streams : List Mux.Stream}
    (h : ∃ s ∈ streams, s.hasPending = true) :
    ∃ s, Mux.select streams = some s ∧ RfcNext streams s := by
  have hsome := Mux.select_isSome_of_pending h
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hsome
  exact ⟨s, hs, select_refines_rfc hs⟩

/-- **Tightness / uniqueness.** Any two RFC-next streams share priority and id:
`RfcNext` determines the choice up to the observable scheduling signals, so
`select` computes *the* RFC next, not merely an admissible one. -/
theorem rfc_next_prio_id {streams : List Mux.Stream} {s s' : Mux.Stream}
    (h : RfcNext streams s) (h' : RfcNext streams s') :
    s.prio = s'.prio ∧ s.id = s'.id := by
  obtain ⟨hm, hpd, hmin⟩ := h
  obtain ⟨hm', hpd', hmin'⟩ := h'
  have n1 : ¬ RfcServesBefore s' s := hmin s' hm' hpd'
  have n2 : ¬ RfcServesBefore s s' := hmin' s hm hpd
  rw [← slt_iff_rfc] at n1 n2
  have e1 := Mux.not_slt_to_sle n1
  have e2 := Mux.not_slt_to_sle n2
  unfold Mux.sle at e1 e2
  have hrank : s.prio.rank = s'.prio.rank := by
    rcases e1 with h1 | ⟨h1, _⟩ <;> rcases e2 with h2 | ⟨h2, _⟩ <;> omega
  have hid : s.id = s'.id := by
    rcases e1 with h1 | ⟨_, h1⟩
    · exact absurd hrank (Nat.ne_of_lt h1)
    · rcases e2 with h2 | ⟨_, h2⟩
      · exact absurd hrank.symm (Nat.ne_of_lt h2)
      · exact Nat.le_antisymm h1 h2
  exact ⟨Mux.Priority.rank_inj hrank, hid⟩

/-! ## Non-vacuity — urgency and class, against the deployed function

Two pending streams, `urgent` (urgency 0) and `slack` (urgency 5). A scheduler
that ignored urgency would serve `slack`; the specification forbids it and
`Mux.select` provably cannot return it. -/

def urgent : Mux.Stream := ⟨3, ⟨0, true⟩, [2]⟩
def slack : Mux.Stream := ⟨7, ⟨5, false⟩, [1]⟩
def urgencyConn : List Mux.Stream := [slack, urgent]

/-- The high-urgency-value stream is not the RFC next: `urgent` serves before it. -/
theorem slack_not_rfc : ¬ RfcNext urgencyConn slack := by
  intro h
  obtain ⟨_, _, hmin⟩ := h
  have hb : RfcServesBefore urgent slack := by
    unfold RfcServesBefore; left; decide
  exact hmin urgent (by decide) (by decide) hb

/-- **A urgency-ignoring pick is rejected.** The deployed `Mux.select` cannot
return the higher-urgency-value stream: doing so would contradict the refinement
theorem. -/
theorem deployed_serves_urgency : Mux.select urgencyConn ≠ some slack := by
  intro h
  exact slack_not_rfc (select_refines_rfc h)

/-- And the picker does return the urgent stream. -/
theorem deployed_picks_urgent : Mux.select urgencyConn = some urgent := by decide

/-! Same urgency band, one non-incremental (`plain`) and one incremental
(`inc`). A scheduler violating "non-incremental before incremental" would serve
`inc`; the specification forbids it. -/

def plain : Mux.Stream := ⟨4, ⟨3, false⟩, [2]⟩
def inc : Mux.Stream := ⟨9, ⟨3, true⟩, [1]⟩
def bandConn : List Mux.Stream := [inc, plain]

/-- The incremental stream is not the RFC next within its band: the
non-incremental one serves first. -/
theorem inc_not_rfc : ¬ RfcNext bandConn inc := by
  intro h
  obtain ⟨_, _, hmin⟩ := h
  have hb : RfcServesBefore plain inc := by
    unfold RfcServesBefore; right; left; exact ⟨rfl, rfl, rfl⟩
  exact hmin plain (by decide) (by decide) hb

/-- **A class-order-violating pick is rejected.** The deployed `Mux.select`
cannot serve the incremental stream ahead of the same-urgency non-incremental
one. -/
theorem deployed_serves_class : Mux.select bandConn ≠ some inc := by
  intro h
  exact inc_not_rfc (select_refines_rfc h)

/-! ## Non-vacuity — round-robin within a band (RFC 9218 §10)

Within one urgency band the incremental streams are interleaved fairly
(round-robin). The deployed round-robin engine is `Mux.RoundRobin.rrServe`. We
specify fairness independently and prove `rrServe` satisfies it while a starving
server fails it. -/

/-- **RFC 9218 §10 band fairness (independent specification).** A round-robin
`serve` is fair when, over one full cycle (`active.length` steps) on any band of
distinct active ids, it serves each active id and serves no id twice. Stated
purely over the served/active id lists. -/
def RfcRoundRobin (serve : List Mux.StreamId → Nat → List Mux.StreamId) : Prop :=
  ∀ q : List Mux.StreamId, q.Nodup →
    (serve q q.length).Nodup ∧ ∀ x ∈ q, x ∈ serve q q.length

/-- **The deployed round-robin is fair.** `Mux.RoundRobin.rrServe` meets the RFC
§10 band-fairness specification. -/
theorem rrServe_isRoundRobin : RfcRoundRobin Mux.RoundRobin.rrServe :=
  fun q hq =>
    ⟨Mux.RoundRobin.rr_served_nodup q hq,
     fun x hx => Mux.RoundRobin.rr_fair q x hx⟩

/-- A server that keeps serving the band head (never rotating) — starving every
other stream. -/
def headServer : List Mux.StreamId → Nat → List Mux.StreamId
  | [], _ => []
  | x :: _, n => List.replicate n x

/-- **A round-robin-violating server is rejected.** The head-repeating server
fails the RFC §10 fairness specification: on `[1, 2]` it serves `[1, 1]`, which
is not duplicate-free. A picker that violated round-robin within a band is
therefore not admitted by the specification. -/
theorem headServer_not_roundRobin : ¬ RfcRoundRobin headServer := by
  intro h
  exact absurd (h [1, 2] (by decide)).1 (by decide)

end MuxPriorityCorrect
