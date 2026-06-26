/-
# Dregg2.Consensus.Safety — CONSENSUS SAFETY at the CHAIN level: no two honest nodes
# finalize CONFLICTING histories.

**The gap this closes — the chain-level sibling of `lightclient_unfoolable`.**
`Circuit.CircuitSoundness.lightclient_unfoolable` proves a single accepted TURN witnesses a
genuine kernel transition — per-turn *validity*. It does NOT say WHICH chain is canonical.
Every consensus-safety theorem already in the tree fixes ONE lace / ONE state:

* `Proof.BFT.bft_safety` — over one `votes` pool: two conflicting blocks cannot both reach a
  BFT quorum (quorum-intersection at an honest process).
* `Proof.CordialMiners.cordial_agreement` / `…_from_lace` — over ONE `CordialState`: a wave
  anchors a single super-ratified leader (the quorum read off that lace).
* `Distributed.BlocklaceFinality.finalLeaders_one_per_wave` / `tauOrder_deterministic` — over
  ONE `Lace`: a wave has ≤ 1 final leader; the order is a function of (lace, participants).
* `Consensus.TauPrefixMonotone.tau_finalized_prefix_monotone` — over ONE lace's GROWTH: the
  finalized prefix is append-only *under* `FinalizedRegionStable` (and refuted unconditionally).

What NONE of them state is the property a LIGHT CLIENT'S CHAIN-CHOICE actually rests on:
**two honest nodes, holding DIFFERENT (partial) laces `S₁ ≠ S₂`, cannot finalize conflicting
leaders at the same wave — so their finalized HISTORIES never disagree.** A client that follows
either node's finalized chain lands on the SAME history; there is no fork it can be split across.

This module supplies that apex. The honest observation that makes it tractable: the proof of
`cordial_agreement` never uses that its two super-ratifications come from the *same* state — it
consumes only the two ratifier vote pools, the BFT honest-majority model over their union, the
honesty law, and id-determinism. So the cross-node lift is a genuine generalization, not a
re-proof: §1 isolates the pure two-pool quorum-intersection kernel (`quorum_pair_agreement`,
the generalization of `bft_safety` from one pool to two independent pools), §2 lifts it to two
`CordialState`s, §3 reads the quorum off each node's lace (`Committed`, via the existing
`SuperRatification.ofLace`), and §4 composes per-wave agreement into the chain-level
`no_conflicting_finalized_history`.

## CARRIERS (hypotheses, never `axiom`s — the honest floor).

* **Honest majority / `n > 3f`.** Carried by `BFT.BFTModel` over the UNION of the two nodes'
  ratification pools (its `bft_threshold`, `fault_bound`, `population_bound`, `honest_vote_once`
  fields). This is the standard BFT floor; deriving that the union actually meets it is the
  post-GST dissemination argument (the same residual `BFT.lean`'s O2 and
  `cordial_agreement_from_lace` name) — off the safety-critical path, NOT an open hole here.
* **Shared participant universe.** The two nodes count ratifiers over the same participant id
  set, so two `≥ n − f` pools intersect in an honest participant. Carried implicitly by the
  single `Finality.Config` both pools are read against.
* **id-determinism** (`hid_inj : l₁.id = l₂.id → l₁ = l₂`): content-addressing pins the block
  from its id (`Lace.Canonical` at the anchor). A hypothesis, met by the lace's content-address.

NAMED RESIDUAL (a closure lane, not faked): bridging `BlocklaceFinality.isSuperRatified` (the
`Bool` the node computes) to the `CordialMiners.Committed`/`superRatifiedFromLace` evidence this
module consumes is the `OPEN-CM-SUPERRATIFY-BRIDGE` — the two parallel finalization models
(`Proof.CordialMiners` = the BFT algebra, `Distributed.BlocklaceFinality` = the executable rule)
share the `n − f` ratifier-count shape; this module proves safety on the algebra side, where the
quorum is read off the lace via `SuperRatification.ofLace`. The bridge lands the same conclusion
on the executable rule; it is the next rung, not an assumed step.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
Verified with `lake build Dregg2.Consensus.Safety`.
-/
import Mathlib.Tactic
import Dregg2.Proof.CordialMiners

namespace Dregg2.Consensus.Safety

open Dregg2 Dregg2.World Dregg2.Authority.Blocklace
open Dregg2.Proof.BFT Dregg2.Proof.CordialMiners

/-! ## §1. The pure two-pool quorum-intersection kernel.

`BFT.bft_safety` lives over a SINGLE `votes` pool — it answers "can two conflicting blocks both
reach a quorum *in one node's view*?". The chain-level question is over TWO views: node 1's
ratifier pool `v1` for `b1`, node 2's pool `v2` for `b2`. We monotone-lift each quorum onto the
UNION pool `v1 ++ v2` and run the classical intersection there: the honest witness ratified
across the union, so the honesty law collapses `b1 = b2`. This is `bft_safety` generalized from
one pool to two independent pools — the genuinely new kernel the chain apex needs. -/

/-- A node's ratifier read over `v1` is preserved when its pool is appended to another node's
pool: every distinct voter for `b` in `v1` is still a distinct voter for `b` in `v1 ++ v2`. -/
theorem votersFor_subset_append_left (v1 v2 : List Vote) (b : Nat) :
    votersFor v1 b ⊆ votersFor (v1 ++ v2) b := by
  intro x hx
  have hxsrc : x ∈ ((v1.filter (fun v => v.block = b)).map (·.voter)) :=
    List.dedup_subset _ hx
  apply List.subset_dedup
  have hf : v1.filter (fun v => v.block = b) ⊆ (v1 ++ v2).filter (fun v => v.block = b) := by
    intro y hy
    rw [List.mem_filter] at hy ⊢
    exact ⟨List.mem_append_left _ hy.1, hy.2⟩
  exact List.map_subset _ hf hxsrc

/-- Symmetric to `votersFor_subset_append_left`, for the right (second node's) pool. -/
theorem votersFor_subset_append_right (v1 v2 : List Vote) (b : Nat) :
    votersFor v2 b ⊆ votersFor (v1 ++ v2) b := by
  intro x hx
  have hxsrc : x ∈ ((v2.filter (fun v => v.block = b)).map (·.voter)) :=
    List.dedup_subset _ hx
  apply List.subset_dedup
  have hf : v2.filter (fun v => v.block = b) ⊆ (v1 ++ v2).filter (fun v => v.block = b) := by
    intro y hy
    rw [List.mem_filter] at hy ⊢
    exact ⟨List.mem_append_right _ hy.1, hy.2⟩
  exact List.map_subset _ hf hxsrc

/-- The ratifier COUNT only grows when a pool is unioned with another (both sides are `Nodup`,
being `.dedup`s, so subset gives `length ≤`). The monotonicity that lifts each node's local
`≥ n − f` quorum onto the union pool. -/
theorem votersFor_length_le_append_left (v1 v2 : List Vote) (b : Nat) :
    (votersFor v1 b).length ≤ (votersFor (v1 ++ v2) b).length :=
  ((List.nodup_dedup _).subperm (votersFor_subset_append_left v1 v2 b)).length_le

theorem votersFor_length_le_append_right (v1 v2 : List Vote) (b : Nat) :
    (votersFor v2 b).length ≤ (votersFor (v1 ++ v2) b).length :=
  ((List.nodup_dedup _).subperm (votersFor_subset_append_right v1 v2 b)).length_le

/-- **`quorum_pair_agreement` — the chain-safety kernel.** Two INDEPENDENT ratifier pools (the
two honest nodes' views), `v1` endorsing `b1` and `v2` endorsing `b2`, each meeting the BFT
quorum `n − f`. Under a `BFTModel` over their UNION (the honest-majority floor, shared
participant universe) and the honesty law (an honest participant who ratified across the union
ratified a single block), the two pools cannot endorse distinct blocks: `b1 = b2`.

This is `BFT.bft_safety` lifted from one pool to two: the two `n − f` quorums, monotone-lifted
onto `v1 ++ v2`, still meet `n − f`, so `honest_witness_in_intersection` produces an honest
participant in both — who then ratified both blocks. The classical quorum-intersection floor
does ALL the work; what is new is that the two quorums are read from DIFFERENT nodes' views. -/
theorem quorum_pair_agreement
    (cfg : Finality.Config) (v1 v2 : List Vote) (b1 b2 : Nat)
    (hq1 : cfg.n - cfg.f ≤ (votersFor v1 b1).length)
    (hq2 : cfg.n - cfg.f ≤ (votersFor v2 b2).length)
    (M : BFTModel cfg (v1 ++ v2))
    (honest_one : ∀ v : Nat, ¬ M.Byzantine v →
        v ∈ votersFor (v1 ++ v2) b1 → v ∈ votersFor (v1 ++ v2) b2 → b1 = b2) :
    b1 = b2 := by
  -- lift each node-local quorum onto the union pool.
  have hq1' : cfg.n - cfg.f ≤ (votersFor (v1 ++ v2) b1).length :=
    le_trans hq1 (votersFor_length_le_append_left v1 v2 b1)
  have hq2' : cfg.n - cfg.f ≤ (votersFor (v1 ++ v2) b2).length :=
    le_trans hq2 (votersFor_length_le_append_right v1 v2 b2)
  -- the transferred BFT feeder: the two union-quorums share an HONEST participant.
  obtain ⟨v, hhonest, hv1, hv2⟩ :=
    honest_witness_in_intersection cfg (v1 ++ v2) M b1 b2 hq1' hq2'
  -- that honest participant ratified both blocks ⇒ the honesty law collapses them.
  exact honest_one v hhonest hv1 hv2

/-! ## §2. Cross-node leader agreement — two `CordialState`s, one wave, one leader.

The super-ratification level. `sr₁` is node 1's super-ratification of leader `l₁` (over its
lace `S₁`); `sr₂` is node 2's, over `S₂`. We feed their vote pools to the §1 kernel. -/

/-- **`cross_node_leader_agreement` — DAG-BFT safety ACROSS NODES.** Two super-ratifications of
leaders `l₁ l₂` held by DIFFERENT nodes (`S₁`, `S₂`), with a `BFTModel` over the union of their
ratifier pools and the honesty law, cannot anchor distinct blocks: `l₁ = l₂`. The two states are
genuinely independent — this is `cordial_agreement` with the single-state assumption removed. -/
theorem cross_node_leader_agreement
    (cfg : Finality.Config) (S₁ S₂ : CordialState) (l₁ l₂ : Block)
    (sr₁ : SuperRatification S₁ cfg l₁) (sr₂ : SuperRatification S₂ cfg l₂)
    (M : BFTModel cfg (sr₁.votes ++ sr₂.votes))
    (honest_one : ∀ v : Nat, ¬ M.Byzantine v →
        v ∈ votersFor (sr₁.votes ++ sr₂.votes) l₁.id →
        v ∈ votersFor (sr₁.votes ++ sr₂.votes) l₂.id → l₁.id = l₂.id)
    (hid_inj : l₁.id = l₂.id → l₁ = l₂) :
    l₁ = l₂ :=
  hid_inj
    (quorum_pair_agreement cfg sr₁.votes sr₂.votes l₁.id l₂.id sr₁.quorum sr₂.quorum M honest_one)

/-- **`no_conflicting_cross_node_leader` — the `False` / safety form.** Two DISTINCT blocks
cannot both be super-ratified by two different nodes for the same wave position. -/
theorem no_conflicting_cross_node_leader
    (cfg : Finality.Config) (S₁ S₂ : CordialState) (l₁ l₂ : Block) (hconflict : l₁ ≠ l₂)
    (sr₁ : SuperRatification S₁ cfg l₁) (sr₂ : SuperRatification S₂ cfg l₂)
    (M : BFTModel cfg (sr₁.votes ++ sr₂.votes))
    (honest_one : ∀ v : Nat, ¬ M.Byzantine v →
        v ∈ votersFor (sr₁.votes ++ sr₂.votes) l₁.id →
        v ∈ votersFor (sr₁.votes ++ sr₂.votes) l₂.id → l₁.id = l₂.id)
    (hid_inj : l₁.id = l₂.id → l₁ = l₂) :
    False :=
  hconflict (cross_node_leader_agreement cfg S₁ S₂ l₁ l₂ sr₁ sr₂ M honest_one hid_inj)

/-- The honesty law is discharged by the BFT model's own `honest_vote_once` over the union pool
— exactly as `cordial_agreement_via_bft` does single-state. So consuming the cross-node honesty
hypothesis costs nothing beyond the BFT model already granted. -/
theorem cross_node_honesty_of_bft
    (cfg : Finality.Config) (votes : List Vote) (M : BFTModel cfg votes)
    (l₁ l₂ : Block) (v : Nat) (hhonest : ¬ M.Byzantine v)
    (hv1 : v ∈ votersFor votes l₁.id) (hv2 : v ∈ votersFor votes l₂.id) :
    l₁.id = l₂.id :=
  M.honest_vote_once v l₁.id l₂.id hhonest hv1 hv2

/-- **`cross_node_leader_agreement_via_bft`** — the packaged cross-node safety theorem: the
honesty hypothesis is discharged by the BFT model, no separate oracle. -/
theorem cross_node_leader_agreement_via_bft
    (cfg : Finality.Config) (S₁ S₂ : CordialState) (l₁ l₂ : Block)
    (sr₁ : SuperRatification S₁ cfg l₁) (sr₂ : SuperRatification S₂ cfg l₂)
    (M : BFTModel cfg (sr₁.votes ++ sr₂.votes))
    (hid_inj : l₁.id = l₂.id → l₁ = l₂) :
    l₁ = l₂ :=
  cross_node_leader_agreement cfg S₁ S₂ l₁ l₂ sr₁ sr₂ M
    (cross_node_honesty_of_bft cfg (sr₁.votes ++ sr₂.votes) M l₁ l₂) hid_inj

/-! ## §3. The lace-derived cross-node agreement — quorum READ OFF EACH NODE'S LACE.

The form a node actually realizes: each node holds `Committed Sᵢ cfg lᵢ` (the lace exhibits the
`≥ n − f` ratifier read, `superRatifiedFromLace`). We materialize each lace's ratifier set into
the BFT feeder (`SuperRatification.ofLace`, count preserved) and run §2. The quorum the safety
argument consumes is `(ratifyingVoters …).length` over each REAL lace — not assumed data. -/

/-- **`cross_node_agreement_from_lace` — chain-safety with the quorum read off each lace.** Two
nodes whose laces each EXHIBIT a `≥ n − f` ratifier read for leaders `l₁ l₂` (their `Committed`
facts), under the honest BFT model over the materialized union pool and id-determinism, anchor
the SAME leader. The two nodes' laces `S₁`, `S₂` are independent. -/
theorem cross_node_agreement_from_lace
    (cfg : Finality.Config) (S₁ S₂ : CordialState) (l₁ l₂ : Block)
    (h₁ : Committed S₁ cfg l₁) (h₂ : Committed S₂ cfg l₂)
    (M : BFTModel cfg
      ((SuperRatification.ofLace h₁.some).votes ++ (SuperRatification.ofLace h₂.some).votes))
    (hid_inj : l₁.id = l₂.id → l₁ = l₂) :
    l₁ = l₂ :=
  cross_node_leader_agreement_via_bft cfg S₁ S₂ l₁ l₂
    (SuperRatification.ofLace h₁.some) (SuperRatification.ofLace h₂.some) M hid_inj

/-! ## §4. THE CHAIN-LEVEL APEX — no two honest nodes finalize conflicting histories.

A node's FINALIZED HISTORY is its wave-indexed sequence of committed leaders (the `tauOrder`
anchors, keyed by wave). Two histories CONFLICT iff they disagree on the leader of some common
wave. The apex: under the per-wave cross-node witness (each node committed its leader + the
cross-node honest-majority BFT model), the histories are CONSISTENT — never disagree. A light
client following either node's finalized chain lands on the same history. -/

/-- A node's finalized history: per wave index, the leader block it committed (the `tauOrder`
anchors of `findAllFinalLeaders`, keyed by wave). -/
abbrev FinalizedHistory := List (Nat × Block)

/-- The leader a history finalized at wave `w` (the first entry tagged `w`, if any). -/
def leaderAtWave (h : FinalizedHistory) (w : Nat) : Option Block :=
  (h.find? (fun e => e.1 == w)).map (·.2)

/-- **`Consistent h₁ h₂`** — two finalized histories never disagree at a common wave. This is
the chain-level "no fork": both nodes' canonical chains coincide wherever both have finalized. -/
def Consistent (h₁ h₂ : FinalizedHistory) : Prop :=
  ∀ w l₁ l₂, leaderAtWave h₁ w = some l₁ → leaderAtWave h₂ w = some l₂ → l₁ = l₂

/-- **`CrossNodeWitness`** — the per-wave evidence the chain apex consumes for a common wave:
both nodes committed their leader (`Committed`, quorum read off the lace), the cross-node BFT
honest-majority model over the materialized union pool, and id-determinism. This bundles exactly
the carriers named in the header — no `axiom`. -/
structure CrossNodeWitness (cfg : Finality.Config) (S₁ S₂ : CordialState) (l₁ l₂ : Block) where
  /-- Node 1's lace exhibits the ratifying quorum for `l₁`. -/
  committed₁ : Committed S₁ cfg l₁
  /-- Node 2's lace exhibits the ratifying quorum for `l₂`. -/
  committed₂ : Committed S₂ cfg l₂
  /-- The honest-majority `n > 3f` BFT model over the UNION of the two lace-derived ratifier
  pools (the carrier — its fields, not `axiom`s). -/
  bft : BFTModel cfg
    ((SuperRatification.ofLace committed₁.some).votes
      ++ (SuperRatification.ofLace committed₂.some).votes)
  /-- id-determinism: content-addressing pins the leader block from its id. -/
  hid_inj : l₁.id = l₂.id → l₁ = l₂

/-- A `CrossNodeWitness` forces the two nodes' leaders equal (it is §3 packaged). -/
theorem CrossNodeWitness.agree
    {cfg : Finality.Config} {S₁ S₂ : CordialState} {l₁ l₂ : Block}
    (W : CrossNodeWitness cfg S₁ S₂ l₁ l₂) : l₁ = l₂ :=
  cross_node_agreement_from_lace cfg S₁ S₂ l₁ l₂ W.committed₁ W.committed₂ W.bft W.hid_inj

/-- **`no_conflicting_finalized_history` — THE CHAIN-SAFETY APEX.** Two honest nodes with
laces `S₁`, `S₂` and finalized histories `h₁`, `h₂`. If, at every wave both finalized, the
cross-node witness holds (both committed + the union honest-majority BFT model + id-determinism),
then the two histories are CONSISTENT: they never disagree on a finalized wave's leader. No fork
exists for a light client to be split across — the chain-level sibling of per-turn
`lightclient_unfoolable`. -/
theorem no_conflicting_finalized_history
    (cfg : Finality.Config) (S₁ S₂ : CordialState) (h₁ h₂ : FinalizedHistory)
    (W : ∀ w l₁ l₂, leaderAtWave h₁ w = some l₁ → leaderAtWave h₂ w = some l₂ →
          CrossNodeWitness cfg S₁ S₂ l₁ l₂) :
    Consistent h₁ h₂ := by
  intro w l₁ l₂ hw1 hw2
  exact (W w l₁ l₂ hw1 hw2).agree

/-! ## §5. Non-vacuity — the kernel APPLIES, and `Consistent` is genuinely two-sided.

Per the "don't launder vacuity" discipline: we exhibit (i) the §1 kernel firing on the minimal
BFT config (so `quorum_pair_agreement`'s hypotheses are jointly satisfiable, the conclusion not
vacuous), and (ii) `Consistent` holding on agreeing histories AND FAILING on conflicting ones
(so the predicate is non-trivial — true and false). -/

namespace NonVacuity

/-- The minimal BFT config `n = 4, f = 1` (`n = 3f + 1`). -/
def cfg : Finality.Config := ⟨4, 1, 3⟩

/-- Node 1's pool and node 2's pool BOTH carry three honest ratifiers for block 7 (the agreeing
case: same participant universe `{0,1,2}`, no equivocation). -/
def v1 : List Vote := [⟨0, 7⟩, ⟨1, 7⟩, ⟨2, 7⟩]
def v2 : List Vote := [⟨0, 7⟩, ⟨1, 7⟩, ⟨2, 7⟩]

/-- The empty-adversary model over the UNION pool inhabits `BFTModel` — the §1 kernel's
hypotheses are jointly satisfiable, so `quorum_pair_agreement` is non-vacuous. -/
def unionModel : BFTModel cfg (v1 ++ v2) where
  Byzantine := fun _ => False
  byzantineDec := fun _ => inferInstanceAs (Decidable False)
  fault_bound := by intro b₁ b₂; simp
  bft_threshold := by decide
  population_bound := by
    intro b₁ b₂
    have : ((votersFor (v1 ++ v2) b₁).toFinset ∪ (votersFor (v1 ++ v2) b₂).toFinset)
        ⊆ ({0, 1, 2} : Finset Nat) := by
      intro x hx
      simp only [Finset.mem_union, List.mem_toFinset, votersFor, v1, v2] at hx
      rcases hx with h | h <;>
        · simp only [List.mem_dedup, List.mem_map, List.mem_filter] at h
          obtain ⟨a, ⟨ha, _⟩, hav⟩ := h
          fin_cases ha <;> simp_all
    exact le_trans (Finset.card_le_card this) (by decide)
  honest_vote_once := by
    intro v b₁ b₂ _ hv1 hv2
    simp only [votersFor, v1, v2, List.mem_dedup, List.mem_map, List.mem_filter] at hv1 hv2
    obtain ⟨a, ⟨ha, hab1⟩, _⟩ := hv1
    obtain ⟨c, ⟨hc, hcb2⟩, _⟩ := hv2
    fin_cases ha <;> fin_cases hc <;>
      simp only [decide_eq_true_eq] at hab1 hcb2 <;> omega

/-- The §1 kernel FIRES on the inhabited model: both pools' block ids agree. (Confirms the
hypotheses are jointly satisfiable; the conclusion `b1 = b2` is reached, not vacuous.) -/
example (b1 b2 : Nat)
    (hq1 : cfg.n - cfg.f ≤ (votersFor v1 b1).length)
    (hq2 : cfg.n - cfg.f ≤ (votersFor v2 b2).length)
    (honest_one : ∀ v : Nat, ¬ unionModel.Byzantine v →
        v ∈ votersFor (v1 ++ v2) b1 → v ∈ votersFor (v1 ++ v2) b2 → b1 = b2) :
    b1 = b2 :=
  quorum_pair_agreement cfg v1 v2 b1 b2 hq1 hq2 unionModel honest_one

/-- Two minimal leader blocks (distinct ids). -/
def blkA : Block := ⟨7, 1, 0, [], true⟩
def blkB : Block := ⟨8, 1, 0, [], true⟩

/-- `Consistent` holds on agreeing histories (the TRUE side): both reads hit the same list, so
the two leaders coincide. -/
example : Consistent [(0, blkA)] [(0, blkA)] := by
  intro w l₁ l₂ hw1 hw2
  exact Option.some_inj.mp (hw1.symm.trans hw2)

/-- `Consistent` FAILS on conflicting histories (the FALSE side — the predicate is non-trivial,
it genuinely detects a fork). -/
example : ¬ Consistent [(0, blkA)] [(0, blkB)] := by
  intro h
  have hc := h 0 blkA blkB rfl rfl
  simp [blkA, blkB] at hc

end NonVacuity

/-! ## §6. Axiom hygiene — every chain-safety keystone is kernel-clean.

All theorems reduce to `BFTModel` structure fields (carriers, not `axiom`s), the lace-read
`Committed`/`SuperRatification.ofLace` evidence, and `BFT.honest_witness_in_intersection`; none
pull any oracle axiom. -/
#assert_axioms quorum_pair_agreement
#assert_axioms cross_node_leader_agreement
#assert_axioms no_conflicting_cross_node_leader
#assert_axioms cross_node_leader_agreement_via_bft
#assert_axioms cross_node_agreement_from_lace
#assert_axioms CrossNodeWitness.agree
#assert_axioms no_conflicting_finalized_history

end Dregg2.Consensus.Safety
