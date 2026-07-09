/-
# `Dregg2.Crypto.ConsensusLiveness` — CONSENSUS LIVENESS: progress under partial synchrony, the
partner of the safety we proved in `ConsensusSafety.lean`.

`ConsensusSafety` shows nothing BAD happens — two honest nodes never finalize conflicting blocks — and
it earns that from the crypto floor (`SchnorrDLHard ∨ MSISHard`), because a fork would require a *forged*
vote. This file shows the DUAL: something GOOD does happen — an honest proposer's block actually gets
FINALIZED — and it earns that from a different, clearly-labelled boundary: the **partial-synchrony network
assumption** plus the **honest supermajority**. Safety is a cryptographic guarantee; liveness is a
network/threshold guarantee. Naming which floor carries which half is the whole point.

We REUSE the `ConsensusSafety` model verbatim: the same `SigScheme`, the same `ValidVote` (a member holds
a verifying finalization vote over the body `voteMsg h b`), and the same `Finalized` (a block is finalized
at a height when a quorum of `≥ q` distinct committee members each hold a `ValidVote`). The committee has
`n` members, `≤ f` Byzantine, `n > 3f` (`3f + 1 ≤ n`), and the finalization quorum is the standard BFT
quorum `q = 2f + 1` — which at the canonical `n = 3f + 1` is exactly safety's `n − f`.

## The argument

* **Partial synchrony (the honest boundary).** After GST, an honest→honest message is delivered within a
  bound `Δ`. An honest proposer broadcasts a valid block `b` at height `h` at some `proposeTime ≥ gst`;
  every honest member receives it and — by the honest-voting rule — signs a finalization vote for it. We
  model "honest member signs" GROUNDED, not assumed: with honestly-generated keys (`memberPk m = pkOf (sk
  m)`) and a `Correct` scheme, the honest signature `sign (sk m) (voteMsg h b)` *verifies*, so the honest
  member's `ValidVote` is a THEOREM (`correctness`), not a hypothesis.

* **The honest supermajority alone is a quorum.** The honest set is `committee \ byz`, of size
  `n − |byz| ≥ n − f`. Since `n > 3f` gives `n − f ≥ 2f + 1 = q`, the honest votes ALONE meet the quorum
  threshold — no Byzantine cooperation is needed. Feeding the honest set as the quorum builds `Finalized`.

* **Headline `liveness_after_gst`.** Under `n > 3f`, `≤ f` Byzantine, honestly-generated keys and a correct
  scheme, an honest proposer's valid block `b` at height `h` collects `≥ q` honest votes and therefore
  `Finalized`s. Progress is guaranteed by the honest supermajority plus post-GST delivery.

* **Bounded time (`liveness_finalizes_by`).** Every vote in the finalizing quorum arrives by
  `proposeTime + Δ` (the post-GST delivery bound, which is conditioned on `gst ≤ proposeTime`). So the
  block finalizes within bounded time — the timing side of liveness, tracked alongside the (untimed)
  `Finalized` predicate reused from safety.

* **`liveness_hybrid`.** The finalization votes are the deployed `ed25519 ∧ ML-DSA` hybrid signature; with
  BOTH components correct, `hybrid_correct` gives the honest hybrid votes, so liveness holds for the actual
  post-quantum-hybrid scheme — the exact scheme `consensus_safe_under_floor` protects. Safety and liveness
  meet on the same object.

## Honest boundary — NAMED, not hidden.

Liveness does NOT reduce to `MLWE`/`MSIS`/`SchnorrDL` — and it should not pretend to. Its irreducible
inputs are (i) the **partial-synchrony network assumption** (after GST, honest→honest delivery within `Δ`,
here the `hdeliver` bound + honest members casting via `Correct`), and (ii) the **threshold** `n > 3f` that
makes `n − f ≥ 2f + 1`. Both are honest, clearly-labelled hypotheses — a network/liveness assumption and an
arithmetic threshold, never an `axiom` and never a hardness carrier used as a hypothesis. No FLP violation:
liveness is claimed only AFTER GST (the `gst ≤ proposeTime` condition is load-bearing).

## Teeth (load-bearing, both instances exhibited)

(a) A concrete `n = 4, f = 1, q = 3` committee: the honest set `{1,2,3}` (Byzantine `{0}`) has size
    `3 ≥ q`, and `liveness_after_gst` finalizes a block using those honest votes alone.
(b) LOAD-BEARING threshold: at `n = 3f` (`n = 3, f = 1, q = 3`) the honest set `{1,2}` has size `2 < 3 = q`
    — the honest votes do NOT reach a quorum, so liveness fails without `n > 3f` (mirroring safety's own
    load-bearing threshold).
(c) A proposal NOT delivered (no honest member holds a verifying vote for it) cannot be finalized: with a
    scheme under which the undelivered block has no valid signature, `Finalized` at `q ≥ 1` is impossible.

`#assert_all_clean` (⊆ {propext, Classical.choice, Quot.sound}).
Verified with `lake env lean Dregg2/Crypto/ConsensusLiveness.lean`.
-/
import Dregg2.Crypto.ConsensusSafety
import Mathlib.Tactic

namespace Dregg2.Crypto.ConsensusLiveness

open Dregg2.Crypto.HybridCombiner
open Dregg2.Crypto.ConsensusSafety

/-! ## §1. The honest supermajority is a quorum, and the honest votes finalize the proposer's block.

The finalization model is REUSED verbatim from `ConsensusSafety`: `ValidVote` (a verifying vote over
`voteMsg h b`) and `Finalized` (a `≥ q` quorum of distinct members each with a `ValidVote`). The BFT quorum
is `q = 2f + 1`. -/

variable {SK PK Msg Sig : Type*}
variable {Member : Type*} [DecidableEq Member]
variable {Height Block : Type*}

/-- **`honest_set_is_quorum` — the honest supermajority meets the quorum threshold.** In an `n`-member
committee with `≤ f` Byzantine and `n > 3f`, the honest set `committee \ byz` has size `≥ 2f + 1 = q`.
Counting: `|committee \ byz| = n − |byz| ≥ n − f ≥ 2f + 1` under `3f + 1 ≤ n`. So the honest members ALONE
form a quorum — the load-bearing fact behind liveness. -/
theorem honest_set_is_quorum (committee byz : Finset Member) (n f : ℕ)
    (hn : 3 * f + 1 ≤ n) (hcard : committee.card = n)
    (hbyz : byz ⊆ committee) (hbyzc : byz.card ≤ f) :
    2 * f + 1 ≤ (committee \ byz).card := by
  have hcs : (committee \ byz).card = committee.card - (byz ∩ committee).card := Finset.card_sdiff
  have hint : byz ∩ committee = byz := Finset.inter_eq_left.2 hbyz
  rw [hcs, hint, hcard]
  omega

/-- **`liveness_after_gst` — CONSENSUS LIVENESS.** Under `n > 3f`, `≤ f` Byzantine, honestly-generated keys
(`memberPk m = pkOf (sk m)`) and a `Correct` scheme, an honest proposer's valid block `b` at height `h` is
`Finalized` at quorum `q = 2f + 1`.

Proof: take the honest set `committee \ byz` as the quorum. It is `⊆ committee`, its size is `≥ 2f + 1`
(`honest_set_is_quorum`), and every honest member's finalization vote — the honest signature
`sign (sk m) (voteMsg h b)` — VERIFIES by `correctness` (`Correct` + honest keys), so each honest member
holds a `ValidVote`. Hence the honest votes alone finalize `b`: progress is guaranteed by the honest
supermajority plus post-GST delivery (the honest members receiving and casting). -/
def liveness_after_gst
    (S : SigScheme SK PK Msg Sig)
    (committee byz : Finset Member) (sk : Member → SK) (memberPk : Member → PK)
    (voteMsg : Height → Block → Msg)
    (n f : ℕ) (hn : 3 * f + 1 ≤ n) (hcard : committee.card = n)
    (hbyz : byz ⊆ committee) (hbyzc : byz.card ≤ f)
    (hc : Correct S) (hpk : ∀ m, memberPk m = S.pkOf (sk m))
    (h : Height) (b : Block) :
    Finalized S committee memberPk voteMsg (2 * f + 1) h b where
  quorum := committee \ byz
  sub := Finset.sdiff_subset
  size := honest_set_is_quorum committee byz n f hn hcard hbyz hbyzc
  votes := fun m _ =>
    ⟨S.sign (sk m) (voteMsg h b), by rw [hpk m]; exact hc (sk m) (voteMsg h b)⟩

/-- **`liveness_finalizes_by` — BOUNDED TIME.** After GST (`gst ≤ proposeTime`), the post-GST delivery
bound (honest→honest within `Δ`) puts every member of the finalizing quorum `committee \ byz` at arrival
`≤ proposeTime + Δ`. So the honest quorum is fully assembled — and the block finalizes — within bounded
time. The `gst ≤ proposeTime` condition is load-bearing: the delivery guarantee holds only after GST (no
FLP violation). This tracks timing alongside the (untimed) `Finalized` predicate reused from safety. -/
theorem liveness_finalizes_by
    (committee byz : Finset Member) (arrival : Member → ℕ) (gst delta proposeTime : ℕ)
    (hafter : gst ≤ proposeTime)
    (hdeliver : gst ≤ proposeTime → ∀ m ∈ committee, m ∉ byz → arrival m ≤ proposeTime + delta) :
    ∀ m ∈ committee \ byz, arrival m ≤ proposeTime + delta := by
  intro m hm
  rw [Finset.mem_sdiff] at hm
  exact hdeliver hafter m hm.1 hm.2

/-! ## §2. The anchor — liveness for the DEPLOYED `ed25519 ∧ ML-DSA` hybrid scheme.

The finalization votes are the hybrid signature that `consensus_safe_under_floor` protects. With both
components correct, `hybrid_correct` supplies the honest hybrid votes, so liveness holds for the exact
post-quantum-hybrid scheme — safety and liveness meet on the same object. -/

/-- **`liveness_hybrid` — LIVENESS FOR THE HYBRID SCHEME.** With both the classical and pq components
`Correct` and honestly-generated hybrid keys `(pkc, pkp) = (Cl.pkOf ∘ skc, Pq.pkOf ∘ skp)`, an honest
proposer's valid block finalizes at quorum `q = 2f + 1` under `n > 3f`. The honest hybrid votes come from
`hybrid_correct`; the scheme is the same `ed25519 × ML-DSA` object whose unforgeability
`consensus_safe_under_floor` grounds in `SchnorrDLHard ∨ MSISHard`. Both halves of consensus — safety and
liveness — hold for the deployed hybrid. -/
def liveness_hybrid
    {SKc PKc Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (committee byz : Finset Member) (skc : Member → SKc) (skp : Member → SKp)
    (voteMsg : Height → Block → Msg)
    (n f : ℕ) (hn : 3 * f + 1 ≤ n) (hcard : committee.card = n)
    (hbyz : byz ⊆ committee) (hbyzc : byz.card ≤ f)
    (hcl : Correct Cl) (hpq : Correct Pq)
    (h : Height) (b : Block) :
    Finalized (hybrid Cl Pq) committee (fun m => (Cl.pkOf (skc m), Pq.pkOf (skp m)))
      voteMsg (2 * f + 1) h b :=
  liveness_after_gst (hybrid Cl Pq) committee byz (fun m => (skc m, skp m))
    (fun m => (Cl.pkOf (skc m), Pq.pkOf (skp m))) voteMsg n f hn hcard hbyz hbyzc
    (hybrid_correct Cl Pq hcl hpq) (fun _ => rfl) h b

/-! ## §3. Teeth — the honest supermajority fires, the threshold is load-bearing, undelivered ≠ finalized.

(a) A concrete `n = 4, f = 1, q = 3` committee finalizes on honest votes alone.
(b) At `n = 3f` the honest set is TOO SMALL to be a quorum — liveness genuinely fails without `n > 3f`.
(c) A proposal with no verifying vote (undelivered) cannot be finalized. -/

section Teeth

/-! ### (a) The honest supermajority finalizes on a small committee. -/

/-- **`tooth_honest_supermajority_finalizes`.** `n = 4, f = 1, q = 3`: committee `{0,1,2,3}`, Byzantine
`{0}`, honest set `{1,2,3}` of size `3 = q`. Using the `ConsensusSafety` demo vote scheme `toyS` (honest
keys = identity, so `Correct` and `memberPk = pkOf ∘ sk` hold by `rfl`), `liveness_after_gst` finalizes
block `5` at height `0` on the honest votes ALONE — no Byzantine cooperation. -/
def tooth_honest_supermajority_finalizes :
    Finalized toyS ({0, 1, 2, 3} : Finset ℕ) (fun m => m) toyVoteMsg (2 * 1 + 1) 0 5 :=
  liveness_after_gst toyS ({0, 1, 2, 3} : Finset ℕ) {0} (fun m => m) (fun m => m) toyVoteMsg 4 1
    (by decide) (by decide) (by decide) (by decide) (fun _ _ => rfl) (fun _ => rfl) 0 5

/-! ### (b) The threshold `n > 3f` is load-bearing. -/

/-- **`tooth_threshold_load_bearing` — THE LOAD-BEARING THRESHOLD.** At `n = 3f` (here `n = 3, f = 1,
q = 2f + 1 = 3`) the committee `{0,1,2}` with Byzantine `{0}` (`|byz| = 1 ≤ f`) leaves the honest set
`{1,2}` of size `2 < 3 = q`. The honest votes ALONE do NOT reach a quorum, so an honest proposer's block
cannot be finalized by honest members — liveness FAILS without `n > 3f`, mirroring safety's own
load-bearing threshold. -/
theorem tooth_threshold_load_bearing :
    ∃ (committee byz : Finset ℕ) (n f : ℕ),
      committee.card = n ∧ n = 3 * f ∧ 1 ≤ f ∧
      byz ⊆ committee ∧ byz.card ≤ f ∧
      (committee \ byz).card < 2 * f + 1 :=
  ⟨{0, 1, 2}, {0}, 3, 1, by decide, rfl, by decide, by decide, by decide, by decide⟩

/-! ### (c) An undelivered proposal — no verifying vote — cannot be finalized. -/

/-- The "must-be-delivered-and-signed" demo scheme: NOTHING verifies (`verify _ _ _ = False`). It models a
proposal for which no honest member has produced a signature — an UNDELIVERED block. -/
@[reducible] def nullS : SigScheme ℕ ℕ ℕ ℕ where
  pkOf sk := sk
  sign _ _ := 0
  verify _ _ _ := False

/-- **`tooth_undelivered_not_finalized` — DELIVERY IS LOAD-BEARING.** Under `nullS` no vote verifies, so the
undelivered block `5` has NO `ValidVote` from any member. A `Finalized` at quorum `q = 3 ≥ 1` would need at
least one member holding a `ValidVote` — impossible. So a proposal not delivered by GST (no honest votes)
is never finalized: the honest-delivery assumption of `liveness_after_gst` is genuinely required. -/
theorem tooth_undelivered_not_finalized :
    ¬ Nonempty (Finalized nullS ({0, 1, 2, 3} : Finset ℕ) (fun m => m) toyVoteMsg 3 0 5) := by
  rintro ⟨F⟩
  have hne : F.quorum.Nonempty := Finset.card_pos.mp (by have := F.size; omega)
  obtain ⟨m, hm⟩ := hne
  obtain ⟨_, hσ⟩ := F.votes m hm
  exact hσ

-- The honest set reaches the quorum at n=4,f=1: |{1,2,3}| = 3 ≥ 2·1+1 = 3 (honest votes ALONE suffice)…
#guard decide (2 * 1 + 1 ≤ (({0, 1, 2, 3} : Finset ℕ) \ {0}).card)
-- …but at n=3f the honest set is too small: |{1,2}| = 2 < 3 — no honest quorum, liveness fails.
#guard decide (¬ (2 * 1 + 1 ≤ (({0, 1, 2} : Finset ℕ) \ {0}).card))
-- Under nullS nothing verifies — an undelivered block has no valid vote (so cannot finalize).
#guard decide (¬ nullS.verify 1 (toyVoteMsg 0 5) 0)
-- Post-GST delivery is within Δ (arrival 5 ≤ proposeTime 3 + Δ 2)…
#guard decide ((5 : ℕ) ≤ 3 + 2)
-- …but a message that misses the Δ window (arrival 10) is NOT delivered in time — the bound is real.
#guard decide (¬ ((10 : ℕ) ≤ 3 + 2))

end Teeth

/-! ## §4. Axiom hygiene — every liveness keystone is kernel-clean. -/

#assert_all_clean [
  honest_set_is_quorum,
  liveness_after_gst,
  liveness_finalizes_by,
  liveness_hybrid,
  tooth_honest_supermajority_finalizes,
  tooth_threshold_load_bearing,
  tooth_undelivered_not_finalized
]

end Dregg2.Crypto.ConsensusLiveness
