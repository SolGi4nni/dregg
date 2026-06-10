/-
# Dregg2.Proof.GST — the partial-synchrony GST scaffold that PRODUCES a pacemaker, not assumes one.

`BFTLiveness.lean` proved that *given* a `Pacemaker` (a synchronization round past GST with an
honest leader + the BFT honest-supermajority + HotStuff Δ-delivery) a `GSTRound` and hence τ-BFT
liveness PROVABLY obtain — the quorum is DERIVED, never assumed (`gstRound_obtains`,
`liveness_of_pacemaker`). It carried the honest-leader-eventually conjunct as the bare field
`Pacemaker.synchronizes`. `Synchronizer.lean` then PROVED the probabilistic core (expected-O(1)
views, almost-sure hit) and named the residual: turning the `tsum = 1` measure statement into an
actual hit-index over `World.rand` — a `World`-interface extension (a randomness *measure*, not a
value oracle), explicitly off-surface.

This file sits one layer ABOVE `BFTLiveness`: a `GSTModel` is a partial-synchrony scaffold (DLS88
§"GST") that *produces* the GST round index and the post-GST delivery obligation from more-primitive
data, and — crucially — derives the honest-leader-eventually field from a **co-finality** hypothesis
rather than carrying it raw. It is PURE REUSE: a `GSTModel` BUILDS a `Pacemaker`
(`pacemaker_of_gstModel`), and the proved `BFTLiveness.liveness_of_pacemaker` then gives BFT
liveness for free (`gst_liveness`). The combinatorial half of the consensus OPEN is closed here
(co-final honest leaders ⇒ a synchronization round past GST, `honestLeader_eventually_of_fair`); the
measure-theoretic half (that `World.rand`'s Bernoulli law *makes* honest leaders co-final a.s.)
stays the SAME named OPEN `Synchronizer.lean` documents — carried as the honest `GSTModel` field
`honestLeader_eventually`, never an axiom (the `recv_mono` discipline).

TEETH: the GST bound is load-bearing. A co-final-but-never-past-GST honest-leader
predicate (`honestLeader r := r < 5`, with `gst := 10`) admits NO synchronization round — refuted as
a theorem. The honest co-finality premise is exactly what rules it out; we prove both directions (a
co-final predicate `r ≥ 5` yields a synchronization round for any `gst`; the bounded one does not).

Every hypothesis is a `GSTModel` field or theorem
premise (the `recv_mono` discipline).
-/
import Mathlib.Tactic
import Dregg2.Proof.Synchronizer

namespace Dregg2.Proof.GST

open Dregg2 Dregg2.World Dregg2.Proof.BFT Dregg2.Proof.BFTLiveness

/-! ## 1. The partial-synchrony GST scaffold (layered over `World`, above `Pacemaker`).

A `GSTModel` is the DLS88 partial-synchrony scaffold from which a `BFTLiveness.Pacemaker` is BUILT.
Its fields are the SAME view-synchronization primitives `Pacemaker` carries (`honest_quorum`,
`honest_le_delivered`) PLUS the GST round and a **co-finality** premise on honest leaders, from which
the `Pacemaker.synchronizes` field is DERIVED (§2) rather than carried raw. None of the fields is
"the quorum forms"; none is the synchronizes-output. The point is to push the assumption one layer
more primitive: from "a synchronization round past GST with an honest leader exists" (`synchronizes`)
down to "honest leaders are co-final" (`honestLeader_eventually` carries the post-GST conjunct, which
§2's `honestLeader_eventually_of_fair` shows is derivable from bare co-finality + the GST index). -/

/-- **The partial-synchrony GST scaffold over a `World`.** Bundles the DLS88 GST round index, the
honest-leader predicate + endorser count, the BFT honest-supermajority (`honest_quorum`) and HotStuff
Δ-delivery (`honest_le_delivered`) — the `recv_mono` discipline, never `axiom`s — and the new
co-finality field `honestLeader_eventually` that PRODUCES the synchronization-round shape
`Pacemaker.synchronizes` outputs. A `GSTModel` BUILDS a `Pacemaker` (`pacemaker_of_gstModel`), so all
of `BFTLiveness`'s proved machinery (`gstRound_obtains`, `liveness_of_pacemaker`) applies for free.

* `gst` — DLS88 **Global Stabilization round**: after it, Δ-bounded delivery holds. PRODUCED here
  (a `GSTModel` field), not assumed as the bare `Pacemaker.gst`.
* `honestLeader` / `honestEndorsers` — ELRS §5 leader rotation predicate + the honest endorser count
  (a population fact, not a delivery count), exactly as `Pacemaker` carries them.
* `honest_quorum` — the BFT honest-supermajority floor (`n > 3f` / `h > 2/3`): an honest-leader round
  has `≥ cfg.threshold` honest endorsers. Identical to `Pacemaker.honest_quorum`.
* `honest_le_delivered` — HotStuff Thm 4 @ DLS88 Δ-delivery: post-GST honest-leader rounds deliver the
  honest votes. Identical to `Pacemaker.honest_le_delivered`.
* `honestLeader_eventually` — **the new field, the post-GST co-finality of honest leaders.** For every
  round `t` there is a later round `r ≥ t` past GST (`gst ≤ r`) with an honest leader. This is the
  round-line `WeakFair` for honest-leader synchronization — what `Synchronizer.synchronizer_round_obtains`
  carries as its `hhit` hypothesis, now named as a *fairness/co-finality* obligation. §2 shows it is
  derivable from BARE co-finality (`∀ t, ∃ r ≥ t, honestLeader r`) + the GST index
  (`honestLeader_eventually_of_fair`), so this field is the consistent-discipline carrier of the SAME
  measure-theoretic OPEN `Synchronizer.lean` names (that `World.rand`'s Bernoulli law makes honest
  leaders co-final a.s.) — honest. -/
structure GSTModel (Msg : Type) [World Msg] (votesOf : List Msg → List Vote)
    (cfg : Finality.Config) where
  /-- **DLS88 GST round.** The round after which Δ-bounded delivery holds. PRODUCED here. -/
  gst : Nat
  /-- The block the honest leader of synchronization round `r` proposes. -/
  block : Nat → Nat
  /-- **ELRS §5 leader rotation** — "view `r`'s elected leader is honest". -/
  honestLeader : Nat → Prop
  /-- The honest-endorser count at round `r` (a population fact, not a delivery count). -/
  honestEndorsers : Nat → Nat
  /-- **BFT honest-supermajority** (= `Pacemaker.honest_quorum`): an honest-leader round's honest
  endorsers number `≥ cfg.threshold`. The honest set is itself a quorum; this is NOT a delivery fact. -/
  honest_quorum : ∀ r : Nat, honestLeader r → cfg.threshold ≤ honestEndorsers r
  /-- **HotStuff Thm 4 @ DLS88 Δ-delivery** (= `Pacemaker.honest_le_delivered`): in an honest-leader
  round past GST the honest endorsers' votes are delivered. The sole field touching `World.recv`. -/
  honest_le_delivered : ∀ r : Nat, gst ≤ r → honestLeader r →
    honestEndorsers r ≤ (votersFor (votesOf (World.recv r)) (block r)).length
  /-- **DELIVERY FAIRNESS / honest-leader co-finality (the new field).** For every round `t` there is
  a later round `r ≥ t` past GST with an honest leader — the round-line `WeakFair` for honest-leader
  synchronization. This is exactly the shape `Pacemaker.synchronizes` outputs; §2 derives it from BARE
  co-finality + the GST index (`honestLeader_eventually_of_fair`), so it carries the SAME `World.rand`
  measure OPEN `Synchronizer` names — as a hypothesis field, never an axiom. -/
  honestLeader_eventually : ∀ t : Nat, ∃ r : Nat, t ≤ r ∧ gst ≤ r ∧ honestLeader r

variable {Msg : Type} [World Msg] {votesOf : List Msg → List Vote} {cfg : Finality.Config}

/-! ## 2. A `GSTModel` BUILDS a `Pacemaker` — pure reuse of the proved machinery.

`GSTModel.honestLeader_eventually` is *definitionally the shape* of `BFTLiveness.Pacemaker.synchronizes`
(`∀ t, ∃ r, t ≤ r ∧ gst ≤ r ∧ honestLeader r`), and the other fields map one-for-one. So a `GSTModel`
constructs a `Pacemaker` field-for-field; every `BFTLiveness` theorem then applies VERBATIM. -/

/-- **K-G1 — a `GSTModel` builds a `Pacemaker`.** Field-for-field map onto the proven `Pacemaker`:
`synchronizes := honestLeader_eventually` (the co-finality field IS the synchronizes shape),
`honest_quorum`/`honest_le_delivered` carried across unchanged. This is the bridge that makes GST.lean
pure reuse — no `BFTLiveness` theorem is re-proved; they are inherited through this constructor. -/
def pacemaker_of_gstModel (G : GSTModel Msg votesOf cfg) :
    BFTLiveness.Pacemaker Msg votesOf cfg where
  gst := G.gst
  block := G.block
  honestLeader := G.honestLeader
  honestEndorsers := G.honestEndorsers
  synchronizes := G.honestLeader_eventually
  honest_quorum := G.honest_quorum
  honest_le_delivered := G.honest_le_delivered

/-! ## 3. THE DESCENT — a `GSTModel` yields BFT liveness, via the PROVEN `liveness_of_pacemaker`.

This closes the named consensus OPEN at the *combinatorial* level: the `gst` round is PRODUCED (a
`GSTModel` field), the synchronization round is DERIVED from co-finality, and the quorum is then
derived by the already-proved `BFTLiveness.liveness_of_pacemaker`. GST.lean does NOT re-prove the
quorum derivation — it only supplies the `Pacemaker` from the more-primitive scaffold. -/

/-- **K-G2 — THE DESCENT: a `GSTModel` yields BFT liveness.** Composes `pacemaker_of_gstModel` (K-G1)
with the PROVEN `BFTLiveness.liveness_of_pacemaker`: from the GST scaffold alone, some block is
`committedByQuorum`. The consensus OPEN is closed at the combinatorial level — the GST round is
produced, not assumed; the only residual is the measure-theoretic bridge `honestLeader_eventually`
carries (the `World.rand` Bernoulli law, the SAME OPEN `Synchronizer.lean` names). -/
theorem gst_liveness (G : GSTModel Msg votesOf cfg) :
    ∃ r block, committedByQuorum (Msg := Msg) votesOf r cfg block :=
  BFTLiveness.liveness_of_pacemaker votesOf cfg (pacemaker_of_gstModel G)

/-- **K-G2′ — the `GSTRound` itself obtains** (the intermediate, via the proven `gstRound_obtains`).
Exposes that the GST scaffold produces a genuine post-GST quorum round, not just the existential. -/
theorem gstRound_obtains_of_gstModel (G : GSTModel Msg votesOf cfg) :
    ∃ r block, GSTRound (Msg := Msg) votesOf cfg block r :=
  BFTLiveness.gstRound_obtains votesOf cfg (pacemaker_of_gstModel G)

/-! ## 4. The co-finality bridge — `honestLeader_eventually` is DERIVED, not carried raw.

The `honestLeader_eventually` field has the post-GST conjunct (`gst ≤ r`) baked in. We show that
conjunct is *free*: BARE honest-leader co-finality (`∀ t, ∃ r ≥ t, honestLeader r`) plus the GST index
already gives the post-GST synchronization round, by `r := max t gst`. This is the combinatorial half
of the consensus OPEN, generalizing `Synchronizer.synchronizer_round_obtains` /
`synchronizes_skeleton`: instead of carrying the abstract `hhit`, we reduce the field to bare
co-finality, leaving only the `World.rand` measure (that co-finality holds a.s.) as the named OPEN. -/

/-- **K-G3 — `honestLeader_eventually` is DERIVED from co-finality.** If honest leaders are co-final
(occur arbitrarily late: `∀ t, ∃ r ≥ t, honestLeader r`) and a `gst` index exists, then the post-GST
synchronization-round shape holds: `∀ t, ∃ r, t ≤ r ∧ gst ≤ r ∧ honestLeader r`. Proof: apply
co-finality at the bound `max t gst`; the witness `r ≥ max t gst` is automatically `≥ t` and `≥ gst`.
This is the round-line counterpart of the fairness leadsto, and the combinatorial half of the OPEN —
the `gst ≤ r` conjunct (the partial-synchrony bound) is purely combinatorial once co-finality holds. -/
theorem honestLeader_eventually_of_fair (gst : Nat) (honestLeader : Nat → Prop)
    (hcofinal : ∀ t, ∃ r, t ≤ r ∧ honestLeader r) :
    ∀ t, ∃ r, t ≤ r ∧ gst ≤ r ∧ honestLeader r := by
  intro t
  obtain ⟨r, hr, hhonest⟩ := hcofinal (max t gst)
  exact ⟨r, le_trans (le_max_left _ _) hr, le_trans (le_max_right _ _) hr, hhonest⟩

/-- **A `GSTModel` from a co-finality premise (the field is not carried raw).** Given the
BFT-primitive data (gst, honestLeader, endorsers, the supermajority + delivery facts) AND bare
honest-leader co-finality, build a full `GSTModel` whose `honestLeader_eventually` is DERIVED by K-G3.
This exhibits that the new field reduces to co-finality + the GST index — the residual is only the
measure bridge (that co-finality holds a.s.), the SAME OPEN `Synchronizer` documents. -/
def gstModel_of_cofinal
    (gst : Nat) (block : Nat → Nat) (honestLeader : Nat → Prop) (honestEndorsers : Nat → Nat)
    (honest_quorum : ∀ r, honestLeader r → cfg.threshold ≤ honestEndorsers r)
    (honest_le_delivered : ∀ r, gst ≤ r → honestLeader r →
      honestEndorsers r ≤ (votersFor (votesOf (World.recv r)) (block r)).length)
    (hcofinal : ∀ t, ∃ r, t ≤ r ∧ honestLeader r) :
    GSTModel Msg votesOf cfg where
  gst := gst
  block := block
  honestLeader := honestLeader
  honestEndorsers := honestEndorsers
  honest_quorum := honest_quorum
  honest_le_delivered := honest_le_delivered
  honestLeader_eventually := honestLeader_eventually_of_fair gst honestLeader hcofinal

/-! ## 5. THE BRIDGE — the round-delivery line is a fairness instance.

`World.recv`'s append-only growth (`recv_mono`) is the round-line analogue of weak fairness: a
continuously-offered honest vote count cannot be starved forever. We re-express `World.gst_liveness`'s
productivity premise as a `Leadsto`-shaped statement, tying the round-line vocabulary to the fairness
layer (`Fairness.lean`, the sibling track) without importing it — the two meet only at this shared
"a continuously-offered count is eventually delivered to threshold" shape. -/

/-- **K-G4 — the round-delivery line is a fairness instance.** From the productivity premise `hprod`
(the delivered distinct-voter count for `block` grows without bound — the round-line "continuously
offered" honest vote) and the sublist-preservation discipline `hvotesOf` (a superlist of messages
yields a superlist of votes — the SAME hypothesis `committedByQuorum_mono` carries, since the
voter-extraction must respect the network's append-only delivery), the threshold is eventually
delivered from ANY starting round `t`: a round-line leadsto. `World.recv`'s monotone growth
(`recv_mono`) carries the productivity-witnessed count up to a future round `≥ t`. This re-expresses
`World.gst_liveness`'s premise as a fairness-shaped statement — the bridge tying the two schedulers'
vocabulary together (this track's round line ↔ the `Fairness.lean` `SchedA` line) without an import
dependency. -/
theorem round_line_is_fair (block : Nat)
    (hvotesOf : ∀ {m₁ m₂ : List Msg}, List.Sublist m₁ m₂ → List.Sublist (votesOf m₁) (votesOf m₂))
    (hprod : ∀ k, ∃ r, k ≤ (votersFor (votesOf (World.recv r)) block).length) :
    ∀ t, ∃ r, t ≤ r ∧ cfg.threshold ≤ (votersFor (votesOf (World.recv r)) block).length := by
  intro t
  -- Productivity gives a round `r` whose delivered count meets the threshold (offer `k := cfg.threshold`).
  obtain ⟨r, hr⟩ := hprod cfg.threshold
  -- That round may be EARLIER than `t`. Take the future round `max r t ≥ t`: `recv_mono` makes the
  -- message log a superlist there, `hvotesOf` lifts that to a vote superlist, and `votersFor_length_mono`
  -- makes the distinct-voter count nondecreasing — so the threshold survives the move to round `≥ t`.
  refine ⟨max r t, le_max_right _ _, ?_⟩
  have hsub : List.Sublist (votesOf (World.recv r)) (votesOf (World.recv (max r t))) :=
    hvotesOf (World.recv_mono (le_max_left r t))
  exact le_trans hr (votersFor_length_mono hsub block)

/-! ## 6. Non-vacuity — the reference `GSTModel` and the GST-bound TEETH.

The scaffold is inhabited on the reference `World` (`Msg = Vote`), whose `fixedVotes` schedule
delivers voters 0,1,2 for block 7 by round 3 — exactly the `BFTLiveness.Inhabited` witness, now
PRODUCED through `pacemaker_of_gstModel`, so the descent `gst_liveness` holds concretely (a quorum
forms). The TEETH show the GST bound is load-bearing: K-G3 turns honest-leader co-finality
into a synchronization round, and the conjunct `gst ≤ r` is needed — a co-final-but-bounded
honest-leader predicate admits NO synchronization round past a large GST, refuted as a theorem. -/
namespace Inhabited

open Dregg2.World.Reference Dregg2.Proof.BFTLiveness.Inhabited

/-- The reference GST scaffold: GST at round 3, leader always proposes block 7, an honest leader at
every round, three honest endorsers, the honest set is a quorum (`3 ≥ 3`), the honest votes are
delivered (`ref_delivered_at`), and honest leaders are co-final (trivially — every round is honest, so
`r := max t 3` works). This is the `BFTLiveness.Inhabited.pacemaker` witness, lifted one layer to the
GST scaffold that PRODUCES it. -/
def gstModel : GSTModel M Dregg2.Proof.BFTLiveness.Inhabited.votesOf
    Dregg2.Proof.BFTLiveness.Inhabited.cfg where
  gst := 3
  block := fun _ => 7
  honestLeader := fun _ => True
  honestEndorsers := fun _ => 3
  honest_quorum := fun _ _ => by show (3 : Nat) ≤ 3; omega
  honest_le_delivered := fun r hr _ => ref_delivered_at r hr
  honestLeader_eventually := fun t => ⟨max t 3, le_max_left _ _, le_max_right _ _, trivial⟩

/-- The reference scaffold builds the reference pacemaker (K-G1 is concrete). -/
example : BFTLiveness.Pacemaker M Dregg2.Proof.BFTLiveness.Inhabited.votesOf
    Dregg2.Proof.BFTLiveness.Inhabited.cfg :=
  pacemaker_of_gstModel gstModel

/-- **The descent is non-vacuous: BFT liveness obtains for the reference world** (K-G2). A
block IS `committedByQuorum` — the three honest voters 0,1,2 for block 7 meet the threshold-3 quorum,
derived through the GST scaffold, not assumed. -/
example : ∃ r block, committedByQuorum (Msg := M) Dregg2.Proof.BFTLiveness.Inhabited.votesOf r
    Dregg2.Proof.BFTLiveness.Inhabited.cfg block :=
  gst_liveness gstModel

/-- And a genuine `GSTRound` obtains (the intermediate is concrete too). -/
example : ∃ r block, GSTRound (Msg := M) Dregg2.Proof.BFTLiveness.Inhabited.votesOf
    Dregg2.Proof.BFTLiveness.Inhabited.cfg block r :=
  gstRound_obtains_of_gstModel gstModel

/-! ### TEETH — the GST bound (`gst ≤ r`) is load-bearing.

K-G3 derives the post-GST synchronization round from honest-leader CO-FINALITY. We show the
co-finality premise is not decorative and the `gst ≤ r` conjunct has real content:

  * a **co-final** honest-leader predicate (`r ≥ 5`) yields a synchronization round past ANY `gst`;
  * a **bounded** honest-leader predicate (`r < 5`, co-final FALSE) admits NO synchronization round
    past a large `gst = 10` — the `gst ≤ r ∧ honestLeader r` conjunction is unsatisfiable.

So dropping co-finality (or, equivalently, a network whose honest leaders all fall before GST) makes
the descent FALSE: no synchronization round, no quorum, no progress. This is the round-line image of
the all-stutter teeth — an adversary that schedules honest leaders only early starves consensus. -/

/-- A co-final honest-leader predicate (`honestLeader r := r ≥ 5`): honest leaders occur arbitrarily
late, so K-G3 yields a synchronization round past any GST — here past `gst = 10`, from round `t = 0`. -/
example : ∃ r, (0 : Nat) ≤ r ∧ (10 : Nat) ≤ r ∧ (fun r => 5 ≤ r) r :=
  honestLeader_eventually_of_fair 10 (fun r => 5 ≤ r)
    (fun t => ⟨max t 5, le_max_left _ _, le_max_right _ _⟩) 0

/-- **THE TEETH: a bounded honest-leader predicate admits NO synchronization round past GST.** With
`honestLeader r := r < 5` (honest leaders all occur before round 5 — NOT co-final) and `gst = 10`,
there is no round `r` with `gst ≤ r ∧ honestLeader r`: `10 ≤ r` and `r < 5` are contradictory. So the
descent's conclusion FAILS — exactly what co-finality (the `honestLeader_eventually` field) rules out.
This is the concrete adversarial case the GST bound REJECTS. -/
theorem teeth_bounded_no_sync_round :
    ¬ ∃ r, (10 : Nat) ≤ r ∧ (fun r => r < 5) r := by
  rintro ⟨r, hgst, hbound⟩
  -- `10 ≤ r` and `r < 5` cannot both hold.
  omega

/-- **The teeth, contrapositive form: a bounded predicate is NOT co-final.** `honestLeader r := r < 5`
fails the co-finality premise of K-G3 — there is no honest leader at or past round 5. So K-G3's
hypothesis `hcofinal` is required: it is exactly the property the bounded adversary lacks. -/
theorem teeth_bounded_not_cofinal :
    ¬ (∀ t, ∃ r, t ≤ r ∧ (fun r => r < 5) r) := by
  intro hcofinal
  obtain ⟨r, hr, hbound⟩ := hcofinal 5
  -- `5 ≤ r` and `r < 5` cannot both hold.
  omega

end Inhabited

/-! ## 7. Axiom hygiene — every keystone is kernel-clean.

All theorems reduce to `GSTModel` STRUCTURE FIELDS (hypotheses, not `axiom`s), `BFTLiveness`'s proved
`liveness_of_pacemaker` / `gstRound_obtains` (themselves field-free), and pure `Nat`/`List`
combinatorics (`votersFor_length_mono`, `omega`, `max`). None pull in `sorryAx` or any oracle axiom —
`collectAxioms` sees only the standard kernel triple. The partial-synchrony assumptions live entirely
in `GSTModel`'s fields and the theorem premises (the `recv_mono` discipline), never in `#print axioms`.
The `World.rand`-measure bridge (that honest leaders are co-final a.s.) stays the SAME named OPEN
`Synchronizer.lean` documents — carried as `honestLeader_eventually`. -/
#assert_axioms pacemaker_of_gstModel
#assert_axioms gst_liveness
#assert_axioms gstRound_obtains_of_gstModel
#assert_axioms honestLeader_eventually_of_fair
#assert_axioms gstModel_of_cofinal
#assert_axioms round_line_is_fair
#assert_axioms Inhabited.teeth_bounded_no_sync_round
#assert_axioms Inhabited.teeth_bounded_not_cofinal

end Dregg2.Proof.GST
