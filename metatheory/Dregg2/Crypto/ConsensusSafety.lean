/-
# `Dregg2.Crypto.ConsensusSafety` — CONSENSUS SAFETY as a CRYPTO game: the first step UP from
the crypto primitives to full protocol soundness.

`Consensus.Safety` already proves chain-level safety on the blocklace *algebra* — two honest nodes
never finalize conflicting histories — carried by an abstract honesty law (`honest_vote_once`) over
a `BFTModel`. This file supplies the *cryptographic* sibling that the algebra takes on faith: it
shows that the honesty law is not a free assumption but a CONSEQUENCE of two named objects —

* **(a) honest-supermajority quorum intersection**, a pure Finset-counting fact, and
* **(b) the unforgeability of finalization votes**, which are HYBRID-SIGNED, so a forged vote is a
  `HybridCombiner.Forgery` refuting `EufCma` — discharged all the way down to `SchnorrDLHard ∨ MSISHard`.

The protocol modelled is the node's finality gate: a block is FINALIZED at a height when a QUORUM of
`q = n − f` distinct committee members each cast a valid *finalization vote* — a `SigScheme` signature
by that member over the vote body `(height ‖ block)`. The committee has `n` members, of which `≤ f` are
Byzantine, and `n > 3f` (i.e. `n ≥ 3f + 1`, `q = 2f + 1`).

The argument, three theorems:

1. **`two_quorums_share_honest`** — any two quorums (each `≥ q = n − f` members of the same `n`-member
   committee) intersect in `≥ n − 2f` members; subtracting the `≤ f` Byzantine leaves `≥ n − 3f ≥ 1`
   HONEST members in BOTH. Pure counting: `|A ∩ B| ≥ |A| + |B| − |C|` (via `card_union_add_card_inter`),
   then `|(A ∩ B) \ byz| ≥ |A ∩ B| − |byz|`; `omega` closes it under `n ≥ 3f + 1`.

2. **`no_two_conflicting_finalized`** — if two CONFLICTING blocks `b ≠ b'` are both `Finalized` at one
   height, quorum intersection hands us an honest member in both quorums. That member holds a *valid
   finalization vote* for `b` AND for `b'`. Either it never actually cast one of them — then that vote is
   a fresh valid signature on an un-queried body, a `Forgery` refuting its `EufCma` — or it cast BOTH,
   which the honest-voting rule (an honest member signs `≤ 1` block per height) forbids. Contradiction
   either way. So `EufCma (each honest member) ∧ (n > 3f, ≤ f Byzantine) → no conflicting finalization`.

3. **`consensus_safe_under_floor`** — the finalization votes ARE the `ed25519 ∧ ML-DSA` hybrid signature,
   so each honest member's `EufCma` is not assumed but DISCHARGED by
   `HybridCombiner.hybrid_secure_if_either_floor` from `SchnorrDLHard ∨ MSISHard`. Finalization safety
   therefore holds under `(n > 3f) ∧ (SchnorrDLHard ∨ MSISHard)`: even a QUANTUM adversary that breaks
   the discrete-log half still faces Module-SIS, so the votes stay unforgeable and no two conflicting
   blocks finalize. This is the protocol-level payoff of the whole hybrid ("no-PQ-only") campaign.

## No named-carrier laundering.

The ONLY irreducible objects are the quorum-intersection *counting* (a theorem, not an assumption), the
honest-voting *rule* (a stated protocol invariant, a hypothesis — never an `axiom`), the `≤ f` / `n > 3f`
*threshold*, and the two cryptographic floors `SchnorrDLHard` / `MSISHard`. `EufCma` is reduced to those
floors through `HybridCombiner`; the forking reductions are hypotheses (theorems of the existing forking
machinery), never carriers.

Teeth: a concrete `n = 4, f = 1, q = 3` committee where two quorums share `≥ 2 ≥ 1` honest member; the
threshold is LOAD-BEARING (at `n = 3f` two quorums can meet only in a Byzantine member — safety fails);
a double-vote by a member that signed one block IS a `Forgery`; and WITHOUT `EufCma`/the honest-voting
rule, both conflicting blocks finalize (the crypto guarantee is what punishes the double vote).

`#assert_all_clean` (⊆ {propext, Classical.choice, Quot.sound}).
Verified with `lake env lean Dregg2/Crypto/ConsensusSafety.lean`.
-/
import Dregg2.Crypto.HybridCombiner
import Mathlib.Tactic

namespace Dregg2.Crypto.ConsensusSafety

open Dregg2.Crypto.HybridCombiner
open Dregg2.Crypto.Lattice
open Dregg2.Crypto.HermineSelfTargetMSIS
open Dregg2.Crypto.SchnorrCurveField

/-! ## §1. Quorum intersection — the honest-supermajority counting fact.

The committee is an `n`-member `Finset`; a quorum is any subset of `≥ q = n − f` members; `≤ f` are
Byzantine. Two quorums `A`, `B` intersect in `≥ n − 2f` members (`|A ∩ B| ≥ |A| + |B| − n`), and removing
the `≤ f` Byzantine leaves `≥ n − 3f ≥ 1` HONEST members in both — provided `n > 3f`. -/

/-- **`honest_overlap_iff`** — "a member honest in both quorums" is exactly the non-emptiness of the
honest overlap `(A ∩ B) \ byz`. Lets the counting bound (a `card`) speak about honest witnesses. -/
theorem honest_overlap_iff {M : Type*} [DecidableEq M] (A B byz : Finset M) :
    (∃ m, m ∈ A ∧ m ∈ B ∧ m ∉ byz) ↔ ((A ∩ B) \ byz).Nonempty := by
  constructor
  · rintro ⟨m, ha, hb, hnb⟩
    exact ⟨m, Finset.mem_sdiff.2 ⟨Finset.mem_inter.2 ⟨ha, hb⟩, hnb⟩⟩
  · rintro ⟨m, hm⟩
    rw [Finset.mem_sdiff, Finset.mem_inter] at hm
    exact ⟨m, hm.1.1, hm.1.2, hm.2⟩

/-- **`two_quorums_share_honest` — the quorum-intersection lemma.** In an `n`-member committee with
`≤ f` Byzantine and `n > 3f` (`3f + 1 ≤ n`), any two quorums `A`, `B` (each `≥ n − f` members of the
committee) share at least one HONEST member: some `m ∈ A ∩ B` with `m ∉ byz`.

The counting: `|A ∪ B| + |A ∩ B| = |A| + |B|` and `|A ∪ B| ≤ n` give `|A ∩ B| ≥ 2(n − f) − n = n − 2f`;
`|A ∩ B| ≤ |(A ∩ B) \ byz| + |byz|` with `|byz| ≤ f` gives `|(A ∩ B) \ byz| ≥ n − 3f ≥ 1`. -/
theorem two_quorums_share_honest {M : Type*} [DecidableEq M]
    (committee byz A B : Finset M) (n f : ℕ)
    (hn : 3 * f + 1 ≤ n) (hcard : committee.card = n)
    (hA : A ⊆ committee) (hB : B ⊆ committee)
    (_hbyz : byz ⊆ committee) (hbyzc : byz.card ≤ f)
    (hqA : n - f ≤ A.card) (hqB : n - f ≤ B.card) :
    ∃ m, m ∈ A ∧ m ∈ B ∧ m ∉ byz := by
  rw [honest_overlap_iff, ← Finset.card_pos]
  -- the counting facts, all fed to `omega`.
  have e1 : (A ∪ B).card + (A ∩ B).card = A.card + B.card :=
    Finset.card_union_add_card_inter A B
  have e2 : (A ∪ B).card ≤ n := by
    rw [← hcard]; exact Finset.card_le_card (Finset.union_subset hA hB)
  have hcover : (A ∩ B) ⊆ ((A ∩ B) \ byz) ∪ byz := by
    intro x hx
    by_cases hxb : x ∈ byz
    · exact Finset.mem_union_right _ hxb
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hx, hxb⟩)
  have e3 : (A ∩ B).card ≤ ((A ∩ B) \ byz).card + byz.card :=
    le_trans (Finset.card_le_card hcover) (Finset.card_union_le _ _)
  omega

/-! ## §2. The finalization model — hybrid-signed votes and the safety theorem.

A committee member's finalization vote for a block at a height is a `SigScheme` signature over the vote
body `voteMsg height block`, valid under that member's public key. A block is `Finalized` at a height when
a quorum of `≥ q` distinct members each hold a valid vote. -/

variable {SK PK Msg Sig : Type*}
variable {Member : Type*} [DecidableEq Member]
variable {Height Block : Type*}

/-- **`ValidVote S memberPk voteMsg m h b`** — member `m` holds a valid finalization vote for block `b`
at height `h`: some signature verifies under `m`'s key over the body `voteMsg h b`. (Existential over the
signature: what the finality gate observes is a *verifying* vote, whether or not `m` honestly cast it.) -/
def ValidVote (S : SigScheme SK PK Msg Sig) (memberPk : Member → PK)
    (voteMsg : Height → Block → Msg) (m : Member) (h : Height) (b : Block) : Prop :=
  ∃ σ : Sig, S.verify (memberPk m) (voteMsg h b) σ

/-- **`Finalized`** — block `b` is finalized at height `h`: a `quorum` of `≥ q` distinct committee
members, each with a `ValidVote` for `b`. The node's finality gate: `q = n − f` valid finalization
votes. -/
structure Finalized (S : SigScheme SK PK Msg Sig) (committee : Finset Member)
    (memberPk : Member → PK) (voteMsg : Height → Block → Msg) (q : ℕ)
    (h : Height) (b : Block) where
  /-- The set of members who voted to finalize `b` at height `h`. -/
  quorum : Finset Member
  /-- Voters are committee members. -/
  sub : quorum ⊆ committee
  /-- The quorum meets threshold `q` (distinct members: it is a `Finset`). -/
  size : q ≤ quorum.card
  /-- Every quorum member holds a valid finalization vote for `b` at `h`. -/
  votes : ∀ m ∈ quorum, ValidVote S memberPk voteMsg m h b

/-- **`HonestVotingRule`** — the honest-voting protocol invariant: an honest member's cast-set `Q m`
contains `≤ 1` block per height. If it signed both `voteMsg h b` and `voteMsg h b'`, then `b = b'`. This
is the ONE protocol rule the safety proof consumes (a hypothesis, never an `axiom`). -/
def HonestVotingRule (voteMsg : Height → Block → Msg) (Q : Member → Msg → Prop)
    (honest : Member → Prop) : Prop :=
  ∀ m, honest m → ∀ (h : Height) (b b' : Block),
    Q m (voteMsg h b) → Q m (voteMsg h b') → b = b'

/-- **`no_two_conflicting_finalized` — CONSENSUS SAFETY.** Under `n > 3f`, `≤ f` Byzantine, each honest
member's finalization-vote `EufCma`, and the honest-voting rule, two CONFLICTING blocks `b ≠ b'` cannot
both be finalized at one height.

Proof: quorum intersection (§1) gives an honest member `m` in both quorums, holding a valid vote for `b`
and for `b'`. If `m` never queried `voteMsg h b` (resp. `b'`), that verifying vote on an un-queried body
is a `Forgery` refuting `m`'s `EufCma`; if it queried BOTH, the honest-voting rule forces `b = b'`,
contradicting `b ≠ b'`. A double-finalization is thus a forged vote — impossible under `EufCma`. -/
theorem no_two_conflicting_finalized
    (S : SigScheme SK PK Msg Sig)
    (committee byz : Finset Member) (memberPk : Member → PK)
    (voteMsg : Height → Block → Msg) (Q : Member → Msg → Prop)
    (n f : ℕ) (hn : 3 * f + 1 ≤ n) (hcard : committee.card = n)
    (hbyz : byz ⊆ committee) (hbyzc : byz.card ≤ f)
    (heuf : ∀ m ∈ committee, m ∉ byz → EufCma S (memberPk m) (Q m))
    (hrule : HonestVotingRule voteMsg Q (fun m => m ∈ committee ∧ m ∉ byz))
    (height : Height) (b b' : Block) (hconf : b ≠ b')
    (F1 : Finalized S committee memberPk voteMsg (n - f) height b)
    (F2 : Finalized S committee memberPk voteMsg (n - f) height b') :
    False := by
  -- an HONEST member in both quorums.
  obtain ⟨m, hmA, hmB, hmnb⟩ :=
    two_quorums_share_honest committee byz F1.quorum F2.quorum n f hn hcard
      F1.sub F2.sub hbyz hbyzc F1.size F2.size
  have hmC : m ∈ committee := F1.sub hmA
  -- it holds a valid vote for BOTH conflicting blocks.
  obtain ⟨σ1, hv1⟩ := F1.votes m hmA
  obtain ⟨σ2, hv2⟩ := F2.votes m hmB
  -- did it actually cast each?  Any un-cast valid vote is a forgery.
  by_cases hq1 : Q m (voteMsg height b)
  · by_cases hq2 : Q m (voteMsg height b')
    · exact hconf (hrule m ⟨hmC, hmnb⟩ height b b' hq1 hq2)
    · exact heuf m hmC hmnb ⟨voteMsg height b', σ2, hq2, hv2⟩
  · exact heuf m hmC hmnb ⟨voteMsg height b, σ1, hq1, hv1⟩

/-! ## §3. The anchor — quantum-safe finality under `SchnorrDLHard ∨ MSISHard`.

The finalization votes are the `ed25519 ∧ ML-DSA` hybrid signature, so each honest member's `EufCma` is
discharged by `HybridCombiner.hybrid_secure_if_either_floor` from the discrete-log floor OR the
Module-SIS floor. Safety then holds under `(n > 3f) ∧ (SchnorrDLHard ∨ MSISHard)` — a quantum adversary
that breaks discrete log still faces MSIS, so the votes stay unforgeable and no fork finalizes. -/

/-- **`consensus_safe_under_floor` — QUANTUM-SAFE FINALITY.** With per-member forking reductions (a hybrid
forgery ⟹ a `DLSolver` classically, two SelfTargetMSIS solutions on the pq side — the `HybridCombiner`
reductions, not carriers), two conflicting blocks cannot both be finalized at a height provided `n > 3f`
AND `SchnorrDLHard C G ∨ MSISHard (augmented A t) …`. Each honest member's `EufCma` on its hybrid key
`(pkc m, pkp m)` is produced by `hybrid_secure_if_either_floor`; the ONLY irreducible objects are the two
cryptographic floors, the threshold, and the honest-voting rule. This is the protocol-level payoff of the
whole hybrid campaign: finalization safety survives a break of EITHER the classical OR the lattice half. -/
theorem consensus_safe_under_floor
    {SKc PKc Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (committee byz : Finset Member) (pkc : Member → PKc) (pkp : Member → PKp)
    (voteMsg : Height → Block → Msg) (Q : Member → Msg → Prop)
    (n f : ℕ) (hn : 3 * f + 1 ≤ n) (hcard : committee.card = n)
    (hbyz : byz ⊆ committee) (hbyzc : byz.card ≤ f)
    (C : CurveGroup) (G : C.Pt)
    {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
    {Mo : Type*} [AddCommGroup Mo] [Module Rq Mo] [ShortNorm Mo]
    {No : Type*} [AddCommGroup No] [Module Rq No] [ShortNorm No]
    (Amap : Mo →ₗ[Rq] No) (t : No) (β : ℕ)
    (dlFork : ∀ m : Member, Forgery Cl (pkc m) (Q m) → DLSolver C G)
    (msisFork : ∀ m : Member, Forgery Pq (pkp m) (Q m) →
      ∃ (w : No) (c c' : Rq) (z z' : Mo), c ≠ c' ∧
        IsSelfTargetMSISSolution Amap t β z c w ∧ IsSelfTargetMSISSolution Amap t β z' c' w)
    (hfloor : SchnorrDLHard C G ∨ MSISHard (augmented Amap t) ((β + β) + (β + β)))
    (hrule : HonestVotingRule voteMsg Q (fun m => m ∈ committee ∧ m ∉ byz))
    (height : Height) (b b' : Block) (hconf : b ≠ b')
    (F1 : Finalized (hybrid Cl Pq) committee (fun m => (pkc m, pkp m)) voteMsg (n - f) height b)
    (F2 : Finalized (hybrid Cl Pq) committee (fun m => (pkc m, pkp m)) voteMsg (n - f) height b') :
    False :=
  no_two_conflicting_finalized (hybrid Cl Pq) committee byz (fun m => (pkc m, pkp m))
    voteMsg Q n f hn hcard hbyz hbyzc
    (fun m _ _ =>
      hybrid_secure_if_either_floor Cl Pq (pkc m) (pkp m) (Q m)
        C G Amap t β (dlFork m) (msisFork m) hfloor)
    hrule height b b' hconf F1 F2

/-! ## §4. Teeth — the counting fires, the threshold is load-bearing, forgery punishes the double vote.

(a) A concrete `n = 4, f = 1, q = 3` committee: two quorums share `≥ 2 ≥ 1` honest member.
(b) LOAD-BEARING threshold: at `n = 3f` two quorums meet only in a Byzantine member — the honest overlap
    is EMPTY, so the quorum-intersection guarantee (hence safety) genuinely fails without `n > 3f`.
(c) A double-vote by a member that signed one block IS a `Forgery`; and WITHOUT `EufCma`/the honest rule,
    both conflicting blocks finalize — so the crypto unforgeability is what punishes the double vote. -/

section Teeth

/-! ### (a) The counting fires on a small committee. -/

/-- **Two quorums share an HONEST member.** `n = 4, f = 1, q = 3`: quorums `{0,1,2}` and `{1,2,3}` of the
committee `{0,1,2,3}`, Byzantine `{0}`, share the honest members `{1,2}` — the guarantee delivers. -/
theorem tooth_quorums_share_honest :
    ∃ m, m ∈ ({0, 1, 2} : Finset ℕ) ∧ m ∈ ({1, 2, 3} : Finset ℕ) ∧ m ∉ ({0} : Finset ℕ) :=
  two_quorums_share_honest ({0, 1, 2, 3} : Finset ℕ) {0} {0, 1, 2} {1, 2, 3} 4 1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ### (b) The threshold `n > 3f` is load-bearing. -/

/-- **THE LOAD-BEARING THRESHOLD.** At `n = 3f` (here `n = 3, f = 1, q = 2`) the quorums `{0,1}` and
`{1,2}` — each of size `q = 2`, valid — meet ONLY in member `1`, which is Byzantine (`byz = {1}`). The
honest overlap `(A ∩ B) \ byz` is EMPTY, so NO honest member is in both: the quorum-intersection
guarantee, and with it consensus safety, FAILS without the `n > 3f` bound. -/
theorem threshold_is_load_bearing :
    ∃ (committee byz A B : Finset ℕ) (n f : ℕ),
      committee.card = n ∧ n = 3 * f ∧ 1 ≤ f ∧
      A ⊆ committee ∧ B ⊆ committee ∧ byz ⊆ committee ∧ byz.card ≤ f ∧
      n - f ≤ A.card ∧ n - f ≤ B.card ∧
      ¬ ∃ m, m ∈ A ∧ m ∈ B ∧ m ∉ byz := by
  refine ⟨{0, 1, 2}, {1}, {0, 1}, {1, 2}, 3, 1, by decide, rfl, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, ?_⟩
  rw [honest_overlap_iff]
  have hempty : (({0, 1} : Finset ℕ) ∩ {1, 2}) \ {1} = ∅ := by decide
  rw [hempty]
  exact Finset.not_nonempty_empty

/-! ### (c) A double vote is a forgery; without `EufCma` both blocks finalize. -/

/-- The demo finalization-vote scheme: a vote is valid iff `sig = memberPk + body` (the oracle of
`CapabilityChain`/`RevocationSoundness`). Members are their own public keys. -/
@[reducible] def toyS : SigScheme ℕ ℕ ℕ ℕ where
  pkOf sk := sk
  sign sk m := sk + m
  verify pk m sig := sig = pk + m

/-- The demo vote body: `voteMsg h b = 100 * h + b` (height and block packed into one signed body). -/
@[reducible] def toyVoteMsg : ℕ → ℕ → ℕ := fun h b => 100 * h + b

/-- Honest member `1` cast exactly ONE vote: block `5` at height `0` (`Q = {voteMsg 0 5}`). -/
@[reducible] def toyQ : ℕ → Prop := fun msg => msg = toyVoteMsg 0 5

/-- **A DOUBLE VOTE IS A FORGERY.** Member `1` signed only block `5` at height `0`, but a valid vote for
the CONFLICTING block `7` at height `0` exists (`sig = 1 + voteMsg 0 7` verifies). Since `voteMsg 0 7`
was never in its cast-set, that vote is a fresh valid signature on an un-queried body — a `Forgery`
refuting member `1`'s `EufCma`. This is the object `no_two_conflicting_finalized` derives from a
conflicting finalization. -/
theorem tooth_double_vote_is_forgery : Forgery toyS 1 toyQ :=
  ⟨toyVoteMsg 0 7, 1 + toyVoteMsg 0 7, by decide, by decide⟩

/-- Block `5` finalizes at height `0` with quorum `{0,1,2}` (each member's vote `= member + voteMsg 0 5`
verifies) — the honest side, `q = 3`. -/
def toyFinalized5 :
    Finalized toyS ({0, 1, 2, 3} : Finset ℕ) (fun m => m) toyVoteMsg 3 0 5 where
  quorum := {0, 1, 2}
  sub := by decide
  size := by decide
  votes := fun m _ => ⟨m + toyVoteMsg 0 5, rfl⟩

/-- Block `7` ALSO finalizes at height `0` with quorum `{1,2,3}` — members `1,2` (in both quorums) cast a
second, conflicting vote. -/
def toyFinalized7 :
    Finalized toyS ({0, 1, 2, 3} : Finset ℕ) (fun m => m) toyVoteMsg 3 0 7 where
  quorum := {1, 2, 3}
  sub := by decide
  size := by decide
  votes := fun m _ => ⟨m + toyVoteMsg 0 7, rfl⟩

/-- **THE `EufCma` (unforgeability) IS LOAD-BEARING.** With `toyS` alone — no `EufCma`, no honest-voting
rule — BOTH conflicting blocks `5` and `7` finalize at height `0` (the shared members `1,2` double-vote
freely). So the `Finalized` structure by itself does NOT prevent a fork: it is exactly each honest
member's `EufCma` (§2/§3) that turns the double vote into a refuted `Forgery`. Drop it and safety fails. -/
theorem tooth_eufcma_is_load_bearing :
    Nonempty (Finalized toyS ({0, 1, 2, 3} : Finset ℕ) (fun m => m) toyVoteMsg 3 0 5) ∧
    Nonempty (Finalized toyS ({0, 1, 2, 3} : Finset ℕ) (fun m => m) toyVoteMsg 3 0 7) :=
  ⟨⟨toyFinalized5⟩, ⟨toyFinalized7⟩⟩

-- The n=4 committee's two quorums overlap in ≥ 2 honest members (Byzantine {0} removed).
#guard decide (2 ≤ ((({0, 1, 2} : Finset ℕ) ∩ {1, 2, 3}) \ {0}).card)
-- …but at n=3f the honest overlap is EMPTY (the only shared member is Byzantine) — safety fails.
#guard decide ((({0, 1} : Finset ℕ) ∩ {1, 2}) \ {1} = ∅)
-- A vote verifies iff sig = member + body; the double-vote body was never cast (the forgery witness).
#guard decide (toyS.verify 1 (toyVoteMsg 0 7) (1 + toyVoteMsg 0 7))
#guard decide (¬ toyQ (toyVoteMsg 0 7))

end Teeth

/-! ## §5. Axiom hygiene — every safety keystone is kernel-clean. -/

#assert_all_clean [
  honest_overlap_iff,
  two_quorums_share_honest,
  no_two_conflicting_finalized,
  consensus_safe_under_floor,
  tooth_quorums_share_honest,
  threshold_is_load_bearing,
  tooth_double_vote_is_forgery,
  tooth_eufcma_is_load_bearing
]

end Dregg2.Crypto.ConsensusSafety
