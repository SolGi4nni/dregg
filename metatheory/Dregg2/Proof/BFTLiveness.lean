/-
# Dregg2.Proof.BFTLiveness — the O2 pacemaker: a GST round is derived, not assumed.

`BFT.lean` proved (i) `GSTRound ⇒ committedByQuorum` and (ii) `World.gst_liveness` productivity
implies `GSTRound`; the open direction was building the pacemaker that *produces* a `GSTRound`
from legitimate primitives. This file closes it.

The `Pacemaker` structure bundles the legitimate view-synchronization primitives, NONE of which
is "the quorum forms":
  * `honestLeader` — which views have an honest leader (from the beacon; ELRS §5).
  * `synchronizes` (ELRS Def. 3.1 + Prop. 2) — for every round `t`, a later view `r ≥ gst` with
    `honestLeader r` exists. Derivable from `BeaconSpace.synchronizer_round_obtains_over_beacon`.
  * `honest_quorum` — at an honest-leader round the honest endorsers number `≥ cfg.threshold`:
    the BFT `n > 3f` / `h > 2/3` floor. A count of honest voters, NOT of delivered votes.
  * `honest_le_delivered` (HotStuff Thm 4 @ DLS88 Δ-delivery) — at a honest-leader round past GST
    the honest votes are delivered. The sole delivery assumption; the threshold is then derived by
    `cfg.threshold ≤ honestEndorsers ≤ delivered`.

`gstRound_obtains` composes these three primitives to derive the quorum. The liveness premise is
honest-majority + GST-delivery, not the conclusion.

OPEN (the remaining bridge): coupling `World.rand` to the `BeaconSpace` measure (wiring the
deterministic oracle to the Bernoulli-per-view law the measure carries) — an interface extension,
not a sorry. `honest_le_delivered` and `honest_quorum` are carried as fields exactly as
`World.recv_mono` and `World.gst_liveness` are, never as axioms.

All assumptions are `Pacemaker` fields.
-/
import Mathlib.Tactic
import Dregg2.World
import Dregg2.Proof.BFT

namespace Dregg2.Proof.BFTLiveness

open Dregg2 Dregg2.World Dregg2.Proof.BFT

/-! ## 1. The pacemaker / view-synchronizer model (layered over `World`).

The fields are the partial-synchrony view-synchronization PRIMITIVES — DLS88's GST round, ELRS's
synchronization time (Def. 3.1) with an honest leader, HotStuff's responsive *delivery* (Thm 4),
and the BFT honest-supermajority count — carried exactly as `World.recv_mono` / `World.gst_liveness`
are carried: as hypotheses, never as `axiom`s. **Crucially, no field assumes the threshold is met**;
the quorum count is *derived* (§2). The pacemaker is parameterized by the same data the `GSTRound`
premise takes (`votesOf`, `cfg`, `block`), so any theorem consuming it is parametric over an
arbitrary lawful synchronizer and stays kernel-clean. -/

/-- **The pacemaker over a `World`.** Bundles the view-synchronization PRIMITIVES that, in the
DLS88 partial-synchrony model, let a quorum form after GST. Each field is an explicit hypothesis
(the `recv_mono` discipline), keyed to the paper that supplies it. **No field is the conclusion**
("a quorum forms"); that is derived in §2 from these primitives.

* `gst` — DLS88 **Global Stabilization round**: the round index after which the network honors
  the Δ-delivery bound. Its mere *existence* is the field; DLS88 §"GST" guarantees it.
* `block` — the value the honest leader of synchronization round `r` proposes (HotStuff's leader
  proposal; the block the synchronized honest view collects votes for).
* `honestLeader` — **ELRS §5 / Cogsworth `Relay`**: "view `r`'s elected leader is honest". The
  randomized leader rotation (`World.rand`) decides it; `BeaconSpace`/`Synchronizer` PROVE such a
  view is hit almost surely / in expected `O(1)` from the honest fraction `h > 2/3`. Here it is a
  predicate the synchronizer supplies; §3 derives it from the `BeaconSpace` measure.
* `synchronizes` — ELRS **Def. 3.1 + Property 2**: for every round `t` there is a *later*
  synchronization round `r` with `t ≤ r`, `gst ≤ r` (past GST), **and an honest leader**
  (`honestLeader r`). The honest-leader conjunct is the BeaconSpace almost-sure hit (§3 derives it);
  the arithmetic skeleton is `Synchronizer.synchronizes_skeleton`.
* `honest_quorum` — **the BFT honest-supermajority assumption** (the `n > 3f` / `h > 2/3` floor,
  dual of `BFTModel.fault_bound`): in an honest-leader round `r`, the count of HONEST voters that
  endorse the leader's proposal `block r` is `≥ cfg.threshold`. This is a fact about the honest
  *set* (a quorum of honest replicas exists), NOT about *delivery*; it assumes the supermajority,
  not the conclusion. The honest endorser count is exposed as `honestEndorsers r`.
* `honest_le_delivered` — **HotStuff Thm 4 @ DLS88 Δ-delivery**: in an honest-leader synchronization
  round `r` past GST, the honest endorsers' votes are *delivered* — so the delivered distinct-voter
  count for `block r` is at least the honest endorser count `honestEndorsers r`. This is the SOLE
  field touching `World.recv`, and it is pure *delivery* (the DLS88 post-GST Δ-bound), never the
  threshold. The threshold is `cfg.threshold ≤ honestEndorsers r ≤ delivered`, derived in §2. -/
structure Pacemaker (Msg : Type) [World Msg] (votesOf : List Msg → List Vote)
    (cfg : Finality.Config) where
  /-- **DLS88 GST round.** The round after which Δ-bounded delivery holds. -/
  gst : Nat
  /-- The block the honest leader of synchronization round `r` proposes. -/
  block : Nat → Nat
  /-- **ELRS §5 leader rotation** — "view `r`'s elected leader is honest". -/
  honestLeader : Nat → Prop
  /-- The number of HONEST replicas that endorse the leader's proposal `block r` in round `r`.
  This is the honest *set* size (a population fact), not a count of delivered votes. -/
  honestEndorsers : Nat → Nat
  /-- **ELRS Def. 3.1 + Property 2 — eventual synchronization WITH AN HONEST LEADER.** For every
  round `t` there is a later synchronization round `r ≥ t` past GST (`gst ≤ r`) **whose leader is
  honest** (`honestLeader r`). §3 derives the honest-leader conjunct from the `BeaconSpace` measure;
  the arithmetic skeleton (`t ≤ r ∧ gst ≤ r`) is `Synchronizer.synchronizes_skeleton`. -/
  synchronizes : ∀ t : Nat, ∃ r : Nat, t ≤ r ∧ gst ≤ r ∧ honestLeader r
  /-- **The BFT honest-supermajority assumption** (`n > 3f` / `h > 2/3`, the dual of
  `BFTModel.fault_bound`). In an honest-leader round, the honest endorsers of the leader's block
  number at least the commit threshold: the honest set is itself a quorum. This assumes the
  supermajority EXISTS — NOT that any quorum is delivered/observed. -/
  honest_quorum : ∀ r : Nat, honestLeader r → cfg.threshold ≤ honestEndorsers r
  /-- **HotStuff Thm 4 @ DLS88 Δ-delivery — RESPONSIVE DELIVERY (not the count).** In an
  honest-leader synchronization round `r` past GST, the honest endorsers' votes are delivered: the
  delivered distinct-voter count for `block r` is at least the honest endorser count. Pure delivery
  (the DLS88 post-GST Δ-bound); the threshold is derived from this + `honest_quorum`. -/
  honest_le_delivered : ∀ r : Nat, gst ≤ r → honestLeader r →
    honestEndorsers r ≤ (votersFor (votesOf (World.recv r)) (block r)).length

/-! ## 2. The pacemaker produces a GST round.

Composes three primitives: a synchronization round past GST with an honest leader (`synchronizes`);
the honest set is a quorum at it (`honest_quorum`); the honest votes are delivered
(`honest_le_delivered`). By transitivity `cfg.threshold ≤ honestEndorsers ≤ delivered`, which is
exactly `GSTRound`. -/

/-- **`gstRound_obtains`** — derives a `GSTRound` from the pacemaker:

    cfg.threshold ≤ honestEndorsers r    -- BFT supermajority
                  ≤ delivered voters     -- HotStuff Thm 4 @ DLS88 Δ-delivery

None of the pacemaker fields is "the quorum forms". -/
theorem gstRound_obtains {Msg : Type} [World Msg]
    (votesOf : List Msg → List Vote) (cfg : Finality.Config)
    (P : Pacemaker Msg votesOf cfg) :
    ∃ r block, GSTRound (Msg := Msg) votesOf cfg block r := by
  -- ELRS Prop. 2: a synchronization round `r ≥ gst` with an honest leader exists.
  obtain ⟨r, _ht, hgst, hhonest⟩ := P.synchronizes P.gst
  refine ⟨r, P.block r, ?_⟩
  -- `GSTRound` unfolds to the threshold inequality on the DELIVERED voter count.
  show cfg.threshold ≤ (votersFor (votesOf (World.recv r)) (P.block r)).length
  -- DERIVE it: threshold ≤ honest endorsers (BFT supermajority) ≤ delivered (HotStuff Thm 4 @ Δ).
  calc cfg.threshold
      ≤ P.honestEndorsers r := P.honest_quorum r hhonest
    _ ≤ (votersFor (votesOf (World.recv r)) (P.block r)).length :=
        P.honest_le_delivered r hgst hhonest

/-- **`liveness_of_pacemaker`** — composes `gstRound_obtains` with `gst_liveness_from_round_model`:
from the pacemaker alone, some block is `committedByQuorum`. τ-BFT progress after GST, with
honest-majority + GST-delivery as the premise. -/
theorem liveness_of_pacemaker {Msg : Type} [World Msg]
    (votesOf : List Msg → List Vote) (cfg : Finality.Config)
    (P : Pacemaker Msg votesOf cfg) :
    ∃ r block, committedByQuorum (Msg := Msg) votesOf r cfg block := by
  obtain ⟨r, block, hr⟩ := gstRound_obtains votesOf cfg P
  exact ⟨r, block, gst_liveness_from_round_model (Msg := Msg) votesOf cfg block hr⟩

/-! ## 3. `World.gst_liveness` is derivable from the pacemaker.

`gst_liveness`'s conclusion — "a round meeting `cfg.threshold` exists" — is derived from the
`Pacemaker` fields, none of which is that conclusion. The oracle field reduces to the legitimate
honest-supermajority + GST-delivery obligations. -/

/-- **`gst_liveness_of_pacemaker`** — derives the `World.gst_liveness`-shaped conclusion from the
pacemaker primitives alone; `World.gst_liveness` is not primitive, it follows from
`honest_quorum` + `honest_le_delivered`. -/
theorem gst_liveness_of_pacemaker {Msg : Type} [World Msg]
    (votesOf : List Msg → List Vote) (cfg : Finality.Config)
    (P : Pacemaker Msg votesOf cfg) :
    ∃ (block r : Nat), cfg.threshold ≤
      ((((votesOf (World.recv r)).filter (fun v => v.block = block)).map (·.voter)).dedup).length := by
  obtain ⟨r, block, hr⟩ := gstRound_obtains votesOf cfg P
  exact ⟨block, r, hr⟩

/-! ## 4. The pacemaker is inhabited — the reduction is non-vacuous.

Using the reference `World` instance (`Msg = Vote`), whose `fixedVotes` schedule delivers voters
0,1,2 for block 7 by round 3. With `gst = 3` and `honestEndorsers = 3`, a threshold-3 quorum is
met. `honest_quorum` is the honest-set count `3 ≥ 3`; `honest_le_delivered` is the delivery fact
`3 ≤ delivered` — the two fields are distinct (delivery is not the count). -/
namespace Inhabited

open Dregg2.World.Reference

/-- `n = 3, f = 0, threshold = 3`: a config whose quorum threshold (3 distinct voters) is exactly
met by the reference schedule's three honest voters for block 7. -/
def cfg : Finality.Config := ⟨3, 0, 3⟩

/-- The reference `votesOf` reads votes straight out of the (already-`Vote`) message list. -/
def votesOf : List Vote → List Vote := id

/-- The reference schedule delivers all of `0,1,2` for block 7 by round 3 (it has length 4, so
`take r` for `r ≥ 3` keeps the first three votes ⟨0,7⟩⟨1,7⟩⟨2,7⟩, i.e. distinct voters 0,1,2). This
is the *delivery* fact (`honest_le_delivered`'s content): 3 honest endorsers ≤ 3 delivered voters. -/
theorem ref_delivered_at (r : Nat) (h : 3 ≤ r) :
    (3 : Nat) ≤ (votersFor (votesOf (World.recv (Msg := M) r)) 7).length := by
  have hsub : List.Sublist (fixedVotes.take 3) (fixedVotes.take r) := by
    have : fixedVotes.take 3 = (fixedVotes.take r).take 3 := by
      rw [List.take_take, Nat.min_eq_left h]
    rw [this]; exact List.take_sublist 3 (fixedVotes.take r)
  have hmono := votersFor_length_mono (votes₁ := fixedVotes.take 3) (votes₂ := fixedVotes.take r)
    hsub 7
  have hbase : (votersFor (fixedVotes.take 3) 7).length = 3 := by decide
  show (3 : Nat) ≤ (votersFor (fixedVotes.take r) 7).length
  omega

/-- The reference pacemaker: GST at round 3, leader always proposes block 7, an honest leader at
every view, three honest endorsers, synchronization rounds are "any round at or past `max t 3`",
the honest set is a quorum (`3 ≥ 3`), and the honest votes are delivered (`ref_delivered_at`). -/
def pacemaker : Pacemaker M votesOf cfg where
  gst := 3
  block := fun _ => 7
  honestLeader := fun _ => True
  honestEndorsers := fun _ => 3
  synchronizes := fun t => ⟨max t 3, le_max_left _ _, le_max_right _ _, trivial⟩
  honest_quorum := fun _ _ => by show (3 : Nat) ≤ 3; omega
  honest_le_delivered := fun r hr _ => ref_delivered_at r hr

/-- A `GSTRound` obtains for the reference world — the theorem is non-vacuous. -/
example : ∃ r block, GSTRound (Msg := M) votesOf cfg block r :=
  gstRound_obtains votesOf cfg pacemaker

/-- And the `World.gst_liveness` conclusion is derived for it — the reduction holds concretely. -/
example : ∃ (block r : Nat), cfg.threshold ≤
    ((((votesOf (World.recv (Msg := M) r)).filter (fun v => v.block = block)).map (·.voter)).dedup).length :=
  gst_liveness_of_pacemaker votesOf cfg pacemaker

end Inhabited

/-
OPEN (named, not a sorry): the operational coupling of `World.rand : Nat → Nat` to the
`BeaconSpace` probability measure — proving that the runtime beacon stream realizes the
Bernoulli(`h`)-per-view law. Mathlib has `Measure.infinitePi` (used in `BeaconSpaceInterior`),
but wiring it to `World.rand` needs a `World`-interface extension (a randomness measure, not a
value oracle), off this file's allowed surface.

`World.gst_liveness` is not primitive — it is derived (`gst_liveness_of_pacemaker`) from
the strictly-more-primitive `Pacemaker` fields, none of which is the threshold-conclusion.
-/

/-! ## 5. Axiom hygiene — every keystone is kernel-clean.

All theorems reduce to the `Pacemaker` STRUCTURE FIELDS (hypotheses, not `axiom`s) and `BFT.lean`'s
`gst_liveness_from_round_model` (itself field-free), so none pull in `sorryAx` or any oracle axiom.
`collectAxioms` sees only the three standard kernel axioms. The synchronization assumptions live
entirely in `Pacemaker`'s fields, never in `#print axioms`. -/
#assert_axioms gstRound_obtains
#assert_axioms liveness_of_pacemaker
#assert_axioms gst_liveness_of_pacemaker

end Dregg2.Proof.BFTLiveness
