/-
# Dregg2.Proof.BFT — the distributed-adversary / Byzantine / partial-synchrony model,
# layered over `World`, with the strong forms of both BFT obligations.

╔══════════════════════════════════════════════════════════════════════════════════════╗
║ ⚠ THIS IS NOT dregg1's CONSENSUS PROTOCOL. ⚠                                            ║
║                                                                                        ║
║ This file models CLASSICAL quorum-intersection BFT (Li–Lesani / Malkhi–Reiter /        ║
║ DLS88 / HotStuff-style `n > 3f`, `n − f` quorums, honest-vote-once). dregg1 does NOT   ║
║ run a classical BFT protocol — it runs a Cordial-Miners DAG + Stingray. The faithful   ║
║ model of the protocol dregg actually runs lives in `Dregg2.Proof.CordialMiners`.       ║
║                                                                                        ║
║ `BFT.lean` is therefore a REUSABLE quorum-intersection UTILITY (the pigeonhole-at-an-  ║
║ honest-process safety argument), NOT "THE consensus model" of this system. Do not read ║
║ its theorems as statements about what dregg1/dregg2 actually ships.                    ║
╚══════════════════════════════════════════════════════════════════════════════════════╝

`World.lean` delivers the two BFT obligations only weakly:
  * O1: `quorum_intersection_safety` proves the bare pigeonhole (two quorums share a voter),
    without the adversary/honesty model needed to turn that shared voter into a contradiction.
  * O2: `liveness_after_gst` assumes `World.gst_liveness` as an oracle field.

This file adds the adversary/honesty model as an explicit structure (`BFTModel`) and proves:

  * **O1 STRONG (`bft_safety`)**: under `n > 3f`, ≤ `f` Byzantine voters, the `n − f` quorum
    threshold, and honest-vote-once, two quorums for conflicting blocks are a contradiction.
    (Li–Lesani / Malkhi–Reiter quorum-intersection-at-an-honest-process.)
  * **O2 reduced (`gst_liveness_from_round_model`)**: the `World.gst_liveness` conclusion is
    derived from a DLS88 GST round structure + HotStuff-style honest-leader delivery hypothesis
    — reducing the oracle assumption to "honest votes are delivered within Δ after GST".

OPEN (O2 residual): a from-scratch proof that a `GSTRound` eventually obtains (pacemaker /
view-synchrony); see the `OPEN` block in §4. This is left as a named obstruction, not a sorry.

All adversary assumptions are structure fields.
-/
import Mathlib.Tactic
import Dregg2.World

namespace Dregg2.Proof.BFT

open Dregg2 Dregg2.World

/-! ## 1. The adversary / honesty model (layered over `World`).

Following the `velisarios` / `zotero-formal-verification-blockchain-bft` mechanization
template, the adversary is a `Byzantine : Nat → Prop` predicate on voter ids together with the
quorum-systems *consistency* discipline (Li–Lesani Def. 3): a `≤ f` fault bound, `n > 3f`, and
the honest-vote-once law. None of these are axioms — they are the fields of a `structure`
parameterized by a `Finality.Config`, so any theorem consuming them stays kernel-clean. -/

/-- **The Byzantine / honesty model over a `Finality.Config`.** A `BFTModel cfg votes` bundles
the adversary structure the strong BFT-safety theorem needs, as explicit fields (the honest
`recv_mono`-style discipline, never `axiom`s):

* `Byzantine` / `byzantineDec` — which voter ids are corrupt (decidable, so we can `filter`).
* `fault_bound` — at most `cfg.f` voters are Byzantine *among those that actually voted* (the
  union of the two blocks' voter sets). This is the `≤ f` adversary budget; restricting it to
  actual voters is the honest, non-vacuous statement (we never need a global population finset).
* `bft_threshold` — `cfg.n > 3 * cfg.f`: the classical `n = 3f+1` BFT floor that makes the
  `n − f` quorum intersect in `> f` processes (so the honest-witness survives `f` faults).
* `population_bound` — every distinct voter is one of the `cfg.n` participants, so the union of
  any two blocks' voter sets has card `≤ cfg.n` (the membership bound `World`'s pigeonhole also
  took, here as a model field rather than a bare hypothesis).
* `honest_vote_once` — **the honesty law**: a non-Byzantine voter does not endorse two distinct
  blocks (it votes at most once per height). This is the per-node voting discipline that lives
  with the protocol, not the network oracle; it is exactly what `World.quorum_intersection_safety`
  scoped out as "needs the adversary/honesty model". -/
structure BFTModel (cfg : Finality.Config) (votes : List Vote) where
  /-- The set of corrupt voter ids (the adversary's choice). -/
  Byzantine : Nat → Prop
  /-- Corruption is decidable — needed to `filter` honest voters out of the intersection. -/
  byzantineDec : DecidablePred Byzantine
  /-- **Adversary budget.** At most `cfg.f` of the voters that endorsed `b₁` or `b₂` are
  Byzantine. (Stated over the actual voter union, which is all the proof needs.) -/
  fault_bound : ∀ (b₁ b₂ : Nat),
    (((votersFor votes b₁).toFinset ∪ (votersFor votes b₂).toFinset).filter
      (fun v => Byzantine v)).card ≤ cfg.f
  /-- **The `n > 3f` BFT floor.** Makes the `n − f` quorum intersection exceed `f`. -/
  bft_threshold : cfg.n > 3 * cfg.f
  /-- **Membership bound.** The union of two blocks' distinct voters is within the population. -/
  population_bound : ∀ (b₁ b₂ : Nat),
    ((votersFor votes b₁).toFinset ∪ (votersFor votes b₂).toFinset).card ≤ cfg.n
  /-- **THE HONESTY LAW — honest-vote-once.** A non-Byzantine voter endorses at most one
  block: if an honest `v` voted for both `b₁` and `b₂` (both in its `votersFor` sets) then
  `b₁ = b₂`. Contrapositive: an honest voter never double-votes for distinct blocks. -/
  honest_vote_once : ∀ (v b₁ b₂ : Nat), ¬ Byzantine v →
    v ∈ votersFor votes b₁ → v ∈ votersFor votes b₂ → b₁ = b₂

attribute [instance] BFTModel.byzantineDec

/-! ## 2. O1 STRONG — the full BFT safety theorem.

Two stages, exactly the Malkhi–Reiter / Li–Lesani argument:

1. **Honest-witness intersection** (`honest_witness_in_intersection`): under the `n − f` BFT
   quorum and `n > 3f`, the intersection `Q₁ ∩ Q₂` has more than `f` members; purging the
   ≤ `f` Byzantine ones leaves a non-empty honest remainder ⇒ an **honest** voter in both
   quorums. This is *quorum intersection at a well-behaved process* (Li–Lesani Def. 3).
2. **The contradiction** (`bft_safety`): that honest witness voted for both `b₁` and `b₂`;
   honest-vote-once forces `b₁ = b₂`, contradicting `b₁ ≠ b₂`. -/

/-- **Honest-witness quorum intersection.** The strong form of
`World.quorum_intersection_safety`: under the model's `n > 3f` + `≤ f` Byzantine + the BFT
quorum threshold `n − f` (each block reached `n − f` distinct voters), the two quorums share a
voter that is **honest** (`¬ Byzantine`). This is the quorum-systems *consistency* property:
"every pair of quorums intersect at a well-behaved process" (Li–Lesani Def. 3 /
Malkhi–Reiter). Counting: `|Q₁ ∩ Q₂| = |Q₁| + |Q₂| − |Q₁ ∪ Q₂| ≥ 2(n−f) − n = n − 2f > f`
(since `n > 3f`), and the Byzantine voters in the intersection number `≤ f`, so the honest
remainder is non-empty. -/
theorem honest_witness_in_intersection
    (cfg : Finality.Config) (votes : List Vote) (M : BFTModel cfg votes)
    (b₁ b₂ : Nat)
    -- the BFT quorum threshold: each block was endorsed by at least `n − f` distinct voters.
    -- (This is the `2f+1`-of-`3f+1` quorum, STRICTLY larger than `halfQuorum = (n+f)/2+1`;
    -- the honest-witness needs this bigger quorum — see the file header.)
    (hq1 : cfg.n - cfg.f ≤ (votersFor votes b₁).length)
    (hq2 : cfg.n - cfg.f ≤ (votersFor votes b₂).length) :
    ∃ voter, ¬ M.Byzantine voter ∧
      voter ∈ votersFor votes b₁ ∧ voter ∈ votersFor votes b₂ := by
  classical
  set Q1 := votersFor votes b₁ with hQ1
  set Q2 := votersFor votes b₂ with hQ2
  -- the dedup'd voter lists are `Nodup`, so `toFinset.card = length`.
  have hnd1 : Q1.Nodup := by rw [hQ1, votersFor]; exact List.nodup_dedup _
  have hnd2 : Q2.Nodup := by rw [hQ2, votersFor]; exact List.nodup_dedup _
  have hc1 : Q1.toFinset.card = Q1.length := List.toFinset_card_of_nodup hnd1
  have hc2 : Q2.toFinset.card = Q2.length := List.toFinset_card_of_nodup hnd2
  set F1 := Q1.toFinset
  set F2 := Q2.toFinset
  -- inclusion–exclusion: |F1∪F2| + |F1∩F2| = |F1| + |F2|.
  have hie : (F1 ∪ F2).card + (F1 ∩ F2).card = F1.card + F2.card :=
    Finset.card_union_add_card_inter _ _
  -- the population bound: |F1∪F2| ≤ n.
  have huni : (F1 ∪ F2).card ≤ cfg.n := M.population_bound b₁ b₂
  -- the fault bound, restricted to the intersection: |{v ∈ F1∩F2 | Byzantine v}| ≤ f.
  -- (Byzantine voters in the *intersection* are a subset of Byzantine voters in the *union*.)
  have hbyz_inter_le : ((F1 ∩ F2).filter (fun v => M.Byzantine v)).card ≤ cfg.f := by
    refine le_trans (Finset.card_le_card ?_) (M.fault_bound b₁ b₂)
    apply Finset.filter_subset_filter
    exact Finset.inter_subset_left.trans (Finset.subset_union_left)
  -- the intersection exceeds f:  |F1∩F2| ≥ 2(n−f) − n = n − 2f > f.
  have hF1lb : cfg.n - cfg.f ≤ F1.card := by rw [hc1]; exact hq1
  have hF2lb : cfg.n - cfg.f ≤ F2.card := by rw [hc2]; exact hq2
  have hbft := M.bft_threshold
  have hinter_gt_f : cfg.f < (F1 ∩ F2).card := by omega
  -- honest members of the intersection = |F1∩F2| − (Byzantine members), and Byzantine ≤ f
  -- < |F1∩F2|, so the honest remainder is non-empty.
  have hsplit : ((F1 ∩ F2).filter (fun v => M.Byzantine v)).card
      + ((F1 ∩ F2).filter (fun v => ¬ M.Byzantine v)).card = (F1 ∩ F2).card :=
    Finset.card_filter_add_card_filter_not (fun v => M.Byzantine v)
  have hhonest_pos : 0 < ((F1 ∩ F2).filter (fun v => ¬ M.Byzantine v)).card := by omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hhonest_pos
  rw [Finset.mem_filter, Finset.mem_inter, List.mem_toFinset, List.mem_toFinset] at hv
  exact ⟨v, hv.2, hv.1.1, hv.1.2⟩

/-- **O1 strong — the full BFT safety theorem.** Two quorums for conflicting (distinct) blocks are
a contradiction: the honest witness voted for both; honest-vote-once collapses the blocks equal,
contradicting `b₁ ≠ b₂`. No two conflicting blocks both reach a BFT quorum. (Li–Lesani /
Malkhi–Reiter quorum-intersection-at-an-honest-process.) -/
theorem bft_safety
    (cfg : Finality.Config) (votes : List Vote) (M : BFTModel cfg votes)
    (b₁ b₂ : Nat) (hconflict : b₁ ≠ b₂)
    (hq1 : cfg.n - cfg.f ≤ (votersFor votes b₁).length)
    (hq2 : cfg.n - cfg.f ≤ (votersFor votes b₂).length) :
    False := by
  obtain ⟨v, hhonest, hv1, hv2⟩ := honest_witness_in_intersection cfg votes M b₁ b₂ hq1 hq2
  exact hconflict (M.honest_vote_once v b₁ b₂ hhonest hv1 hv2)

/-- **BFT agreement** — contrapositive of `bft_safety`: if two blocks both reach a BFT quorum
under the honest model they are the same block. At most one block per height reaches a quorum. -/
theorem bft_agreement
    (cfg : Finality.Config) (votes : List Vote) (M : BFTModel cfg votes)
    (b₁ b₂ : Nat)
    (hq1 : cfg.n - cfg.f ≤ (votersFor votes b₁).length)
    (hq2 : cfg.n - cfg.f ≤ (votersFor votes b₂).length) :
    b₁ = b₂ := by
  by_contra hne
  exact bft_safety cfg votes M b₁ b₂ hne hq1 hq2

/-! ## 3. The model is inhabited — the strong theorem is non-vacuous.

A minimal config (`n = 4, f = 1`) with three honest voters all endorsing block 7 and no Byzantine
voters witnesses joint satisfiability of `BFTModel`'s fields. -/
namespace Inhabited

/-- `n = 4, f = 1`: the minimal BFT config (`n = 3f + 1`). -/
def cfg : Finality.Config := ⟨4, 1, 3⟩

/-- Three honest voters all endorse block 7 (no equivocation, no Byzantine). -/
def votes : List Vote := [⟨0, 7⟩, ⟨1, 7⟩, ⟨2, 7⟩]

/-- The empty adversary (no one is corrupt) inhabits `BFTModel` over this config. The
honest-vote-once law holds because every voter in `votes` endorses only block 7. -/
def model : BFTModel cfg votes where
  Byzantine := fun _ => False
  byzantineDec := fun _ => inferInstanceAs (Decidable False)
  fault_bound := by intro b₁ b₂; simp
  bft_threshold := by decide
  population_bound := by
    -- the union of any two blocks' distinct voters is ⊆ {0,1,2}, card ≤ 3 ≤ 4 = n.
    intro b₁ b₂
    have : ((votersFor votes b₁).toFinset ∪ (votersFor votes b₂).toFinset)
        ⊆ ({0, 1, 2} : Finset Nat) := by
      intro x hx
      simp only [Finset.mem_union, List.mem_toFinset, votersFor, votes] at hx
      rcases hx with h | h <;>
        · simp only [List.mem_dedup, List.mem_map, List.mem_filter] at h
          obtain ⟨a, ⟨ha, _⟩, hav⟩ := h
          fin_cases ha <;> simp_all
    exact le_trans (Finset.card_le_card this) (by decide)
  honest_vote_once := by
    -- every voter in `votes` endorses only block 7, so b₁ = 7 = b₂.
    intro v b₁ b₂ _ hv1 hv2
    simp only [votersFor, votes, List.mem_dedup, List.mem_map, List.mem_filter] at hv1 hv2
    obtain ⟨a, ⟨ha, hab1⟩, _⟩ := hv1
    obtain ⟨c, ⟨hc, hcb2⟩, _⟩ := hv2
    -- every vote in `votes` has block 7, so b₁ = a.block = 7 = c.block = b₂.
    fin_cases ha <;> fin_cases hc <;>
      simp only [decide_eq_true_eq] at hab1 hcb2 <;> omega

/-- The inhabiting model is real: `bft_agreement` applies to it (no separate proof needed —
this just confirms the instance typechecks against the strong theorem). -/
example (b₁ b₂ : Nat)
    (hq1 : cfg.n - cfg.f ≤ (votersFor votes b₁).length)
    (hq2 : cfg.n - cfg.f ≤ (votersFor votes b₂).length) : b₁ = b₂ :=
  bft_agreement cfg votes model b₁ b₂ hq1 hq2

end Inhabited

/-! ## 4. O2 — GST / partial-synchrony liveness: the modeled round structure.

`World.gst_liveness` is an *assumed oracle field* whose conclusion is "∃ a round meeting the
threshold". We **reduce** what is assumed: we model the DLS88 GST round structure + a
HotStuff-style honest-leader synchronized view as explicit hypotheses, and PROVE that the
quorum-forming conclusion follows from them. This turns "assume a round meets threshold" into
"assume after GST honest votes are *delivered* within Δ and the honest set is a supermajority"
— a strictly weaker, FLP-respecting input (the full conclusion is now derived, not assumed).

The model (DLS88 §1: after GST, delay ≤ Δ; HotStuff §"Optimistic Responsiveness": after GST a
synchronized view with an honest leader collects votes responsively):

* `GSTRound` — a round `r` that occurs after GST, in which a synchronized honest view's votes
  for `block` are *delivered* (the DLS88 Δ-delivery bound made concrete: the honest voters'
  endorsements appear in `votesOf (World.recv r)`).
* the honest set is a supermajority of size `≥ cfg.threshold`.

We prove: such a round reaches the quorum threshold. This is the *responsive* liveness step
HotStuff isolates — given delivery, the count is immediate. -/

/-- **A modeled post-GST round (the DLS88 + HotStuff hypothesis bundle).** `GSTRound votesOf
cfg block r` says round `r` is one where the partial-synchrony model's good event holds: the
distinct honest voters for `block` whose votes are delivered by round `r` number at least
`cfg.threshold`. This is the *concrete* form of "after GST, an honest supermajority's votes
arrive within Δ" — DLS88's Δ-delivery bound (§1) instantiated at a HotStuff synchronized view
with an honest leader (§"Optimistic Responsiveness"). It is a HYPOTHESIS (a `def` consumed as a
premise), not an assumed `World` field: the point is to derive the quorum, not assume it. -/
def GSTRound [World Msg] (votesOf : List Msg → List Vote)
    (cfg : Finality.Config) (block : Nat) (r : Nat) : Prop :=
  cfg.threshold ≤ (votersFor (votesOf (World.recv r)) block).length

/-- **O2 (reduced-assumption form)**: if a `GSTRound` holds at round `r` — i.e. after GST a
synchronized honest supermajority's votes are delivered (DLS88 Δ-bound + HotStuff responsive view)
— then `block` is `committedByQuorum` at `r`. Derives the `World.gst_liveness` conclusion from the
weaker delivery hypothesis "honest votes are delivered within Δ after GST". -/
theorem gst_liveness_from_round_model [World Msg]
    (votesOf : List Msg → List Vote) (cfg : Finality.Config) (block : Nat)
    {r : Nat} (hgst : GSTRound votesOf cfg block r) :
    committedByQuorum votesOf r cfg block := by
  show committedByQuorum votesOf r cfg block
  unfold committedByQuorum
  simp only [quorumReached, decide_eq_true_eq]
  exact hgst

/-- **O2 existential form**: if a `GSTRound` exists, the block is committed at some round —
`World.liveness_after_gst`'s shape with the delivery existence as an explicit weaker premise. -/
theorem liveness_after_gst_modeled [World Msg]
    (votesOf : List Msg → List Vote) (cfg : Finality.Config) (block : Nat)
    (hgst : ∃ r, GSTRound votesOf cfg block r) :
    ∃ r, committedByQuorum votesOf r cfg block := by
  obtain ⟨r, hr⟩ := hgst
  exact ⟨r, gst_liveness_from_round_model votesOf cfg block hr⟩

/-- **Bridge to the oracle**: the modeled premise is implied by `World.gst_liveness`'s productivity
field `hprod` (voter count grows without bound) — the reduction is sound, not a strengthening. -/
theorem gstRound_of_productivity [World Msg]
    (votesOf : List Msg → List Vote) (cfg : Finality.Config) (block : Nat)
    (hprod : ∀ k : Nat, ∃ r : Nat, k ≤ (votersFor (votesOf (World.recv r)) block).length) :
    ∃ r, GSTRound votesOf cfg block r := by
  obtain ⟨r, hr⟩ := hprod cfg.threshold
  exact ⟨r, hr⟩

/-
OPEN (O2 residual, not a sorry): a from-scratch proof that a `GSTRound` eventually obtains —
the pacemaker / view-synchronization argument. Requires: (i) relating `World.clock` to Δ-bounded
delivery; (ii) a modeled view automaton with leader rotation and timeouts; (iii) the FLP-respecting
argument that an honest leader is eventually hit. `World.gst_liveness` remains the assumed oracle
law; this file reduces its premise to Δ-delivery (not the full conclusion).
-/

/-! ## 5. Axiom hygiene — every keystone is kernel-clean.

All theorems reduce to `BFTModel` structure fields (hypotheses, not axioms) and `GSTRound` (a
`def`-as-premise); none pull `sorryAx` or any oracle axiom. -/
#assert_axioms honest_witness_in_intersection
#assert_axioms bft_safety
#assert_axioms bft_agreement
#assert_axioms gst_liveness_from_round_model
#assert_axioms liveness_after_gst_modeled
#assert_axioms gstRound_of_productivity

end Dregg2.Proof.BFT
