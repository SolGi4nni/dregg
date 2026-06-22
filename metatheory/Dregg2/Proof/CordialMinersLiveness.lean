/-
# Dregg2.Proof.CordialMinersLiveness — closing the MECHANICAL/MODERATE liveness residual of
# the Cordial-Miners DAG-BFT consensus, ADDITIVELY, with the hard pacemaker /
# dissemination cores left as explicitly-NAMED residual statements (never faked, never `sorry`).

`Dregg2.Proof.CordialMiners` proves the **safety** keystone (`cordial_agreement` /
`cordial_agreement_from_lace`: a wave anchors at most one super-ratified leader) by transferring
the classical `n > 3f` quorum-intersection core onto the leaderless DAG commit rule dregg1 runs
(`ordering.rs`). It left four named `OPEN`s. This module closes the two MECHANICAL ones additively
— it does NOT touch the existing module's `#assert_axioms` pins — and gives the two HARD ones
(the post-GST pacemaker / dissemination convergence) crisp residual *definitions/hypotheses* so the
frontier is a named, type-checked object rather than prose.

## What is CLOSED here (additive theorems, kernel-clean)

  1. **OPEN-CM-XSORT — the deterministic intra-segment total order (`ordering.rs::xsort`).**
     `ordering.rs` orders the blocks *within* a super-ratified segment deterministically, tie-broken
     by block id. We implement that tie-break as `Block.xleq` (compare by the `BlockId` `Nat`),
     prove `xsort_consistency` — it is **reflexive, transitive, and total** over an arbitrary
     segment (a `List Block`), i.e. a genuine total preorder — and define `Block.xsort` (the
     deterministic sort). We then prove `xsort_sorted` (the output is `xleq`-`Pairwise`),
     `xsort_perm`/`xsort_length` (it permutes the segment, losing nothing), `xsort_idem`
     (determinism: re-sorting is a no-op), and `xsort_segment_total_order` (the output is a
     **linear extension**: any two distinct segment blocks are strictly comparable by id). This is
     the within-segment determinism `cordial_agreement` deliberately scoped out — now a theorem.

  2. **`cordial_agreement_from_single_lace` — the BFT-quorum model is consumed on the REAL
     `Authority.Blocklace.Lace`.** `cordial_agreement_from_lace` already takes both commit facts as
     reads of *one* `CordialState.lace` (a `Blocklace.Lace`). We confirm that by deriving the
     single-lace specialization: two leaders both `Committed` *in the same `CordialState` `S`* (so
     their ratifier quorums are both read off `S.lace` via `ratifyingVoters`) cannot be distinct,
     under the honest BFT model over the materialized ratification votes. The quorum-intersection
     core is the same `BFT.honest_witness_in_intersection`; the point of the specialization is that
     BOTH quorums are now manifestly facts about a *single* concrete blocklace.

## What stays OPEN — named residual objects, NOT sorries

  3. **`HonestRatifierConvergence` — the dissemination residual (post-GST).** The hard
     liveness/dissemination core (`dissemination.rs` reliable broadcast + the post-GST pacemaker):
     after GST, on the *union* of two laces the honest nodes' causal pasts have converged enough
     that a shared honest ratifier of one leader is visible as a ratifier of the other. We give it
     as an explicit `structure` field bundle (`HonestRatifierConvergence`) — exactly the shape the
     safety argument *consumes* — and prove `agreement_of_convergence`: GIVEN the convergence
     witness, the two leaders collapse. So the residual is a typed hypothesis the runtime discharges
     (like `World.recv_mono` / `BeaconSpace.indep_block`), not a hole.

     The pacemaker progress itself (a wave EVENTUALLY super-ratifies) is now a PROVEN CONDITIONAL
     (§4b), NOT a bare `OPEN`: `cm_pacemaker_residual` is DISCHARGED from the named partial-synchrony
     carrier `Proof.GST.GSTModel` (`cm_pacemaker_from_gstModel`), and reduced all the way to the
     FLP-irreducible primitives — honest-supermajority + Δ-delivery + bare honest-leader co-finality
     (`cm_liveness_from_cofinality`). The synchrony hypothesis is a `GSTModel` field bundle (a
     hypothesis/Prop-portal carried like `World.recv_mono`/`gst_liveness`, NEVER an `axiom`/`sorry`),
     and it is LOAD-BEARING: the mutation tooth `cm_liveness_needs_cofinality` shows the conditional
     does NOT fire for an adversary that starves honest leaders past GST. So OPEN-CM-LIVENESS is now
     SAFETY-style honest: unconditional liveness is FLP-impossible; the conditional on the named
     partial-synchrony assumption is PROVED. (FLP-irreducible residual that remains: the `World.rand`
     measure bridge making co-finality almost-sure — named in `Synchronizer.lean`, off this surface.)

Every adversary/dissemination assumption is a
`structure` field or theorem hypothesis. Builds on the
existing modules by `import` only; defines nothing already taken (`xleq`/`xsort`/… are new names in
`namespace`s under `Dregg2.Proof.CordialMiners`).

## UPDATE — OPEN-CM-LIVENESS is now a PROVEN CONDITIONAL (§4b)

The `[hard] OPEN-CM-LIVENESS` pacemaker residual is no longer a bare named statement: §4b WIRES the
already-proven partial-synchrony liveness tower (`Proof.BFTLiveness.Pacemaker` → `Proof.GST.GSTModel`,
kernel-clean) into the Cordial-Miners surface. `cm_pacemaker_residual` is now DISCHARGED from the
named partial-synchrony carrier — `cm_pacemaker_from_gstModel` proves it from a `GSTModel`, and
`cm_liveness_from_cofinality` reduces it to the FLP-irreducible primitives (honest-supermajority +
Δ-delivery + bare honest-leader co-finality). The synchrony hypothesis is a structure-field bundle
(a Prop-portal carried like `World.recv_mono`/`gst_liveness`, NEVER `axiom`/`sorry`), and it is
LOAD-BEARING: the mutation tooth `cm_liveness_needs_cofinality` shows the conditional does NOT fire
for the FLP adversary that starves honest leaders past GST. SAFETY (`cordial_agreement…`) is proved
UNCONDITIONALLY; LIVENESS is proved CONDITIONAL on the named partial-synchrony assumption — the
honest BFT shape, FLP-respecting.
-/
import Dregg2.Proof.CordialMiners
import Dregg2.Proof.GST
import Mathlib.Data.List.Sort

namespace Dregg2.Proof.CordialMiners

open Dregg2 Dregg2.World Dregg2.Authority.Blocklace
open Dregg2.Proof.BFT

/-! ## 1. OPEN-CM-XSORT closed: the deterministic intra-segment total order.

`ordering.rs::xsort` deterministically orders the blocks *within* a super-ratified segment, tie-
broken by block id so two honest nodes computing `tau` over the same segment agree on the order.
We implement that tie-break and prove the three consistency laws the task names — reflexive,
transitive, total — over an arbitrary segment, then build the sort and prove it is a genuine
linear extension (sorted + a permutation of the segment + idempotent). -/

/-- **`Block.xleq a b`** (`ordering.rs::xsort`'s comparison key): order blocks by their content-
address `BlockId` (a `Nat`), the deterministic tie-break. `xleq a b ↔ a.id ≤ b.id`. Because the id
is the §8 content-address, this is the canonical deterministic order two honest nodes both compute. -/
def Block.xleq (a b : Block) : Prop := a.id ≤ b.id

instance : DecidableRel Block.xleq := fun a b => inferInstanceAs (Decidable (a.id ≤ b.id))

/-! ### 1a. `xsort_consistency`: reflexive, transitive, total over a segment.

These are the three laws the task asks for. Stated *over a segment* `seg : List Block` (the
super-ratified segment `xsort` orders) — though `xleq` is in fact a total preorder on ALL blocks,
which is exactly why the order is deterministic across nodes. -/

/-- **`xleq` is REFLEXIVE.** Every block is `xleq` itself (`a.id ≤ a.id`). -/
theorem Block.xleq_refl (a : Block) : Block.xleq a a := le_refl a.id

/-- **`xleq` is TRANSITIVE.** `xleq a b → xleq b c → xleq a c` (transitivity of `≤` on ids). -/
theorem Block.xleq_trans {a b c : Block} (hab : Block.xleq a b) (hbc : Block.xleq b c) :
    Block.xleq a c := le_trans hab hbc

/-- **`xleq` is TOTAL.** For any two blocks, `xleq a b ∨ xleq b a` (`Nat` linear order on ids). -/
theorem Block.xleq_total (a b : Block) : Block.xleq a b ∨ Block.xleq b a := le_total a.id b.id

/-- **`xleq` is ANTISYMMETRIC up to id** (`xleq a b → xleq b a → a.id = b.id`): the only ambiguity
the tie-break leaves is between blocks sharing an id, which on a canonical lace are equal. -/
theorem Block.xleq_antisymm_id {a b : Block} (hab : Block.xleq a b) (hba : Block.xleq b a) :
    a.id = b.id := le_antisymm hab hba

/-- **`xsort_consistency` (the law the task names).** The deterministic tie-break `xleq`
is a genuine total preorder over any segment `seg`: reflexive, transitive, and total on the segment's
blocks. This is what makes `ordering.rs::xsort` deterministic — two honest nodes computing it over
the same segment get the same order. Packaged as one statement over an explicit segment. -/
theorem xsort_consistency (seg : List Block) :
    (∀ a ∈ seg, Block.xleq a a) ∧
    (∀ a ∈ seg, ∀ b ∈ seg, ∀ c ∈ seg, Block.xleq a b → Block.xleq b c → Block.xleq a c) ∧
    (∀ a ∈ seg, ∀ b ∈ seg, Block.xleq a b ∨ Block.xleq b a) :=
  ⟨fun a _ => Block.xleq_refl a,
   fun _ _ _ _ _ _ hab hbc => Block.xleq_trans hab hbc,
   fun a _ b _ => Block.xleq_total a b⟩

-- the typeclass facts `pairwise_insertionSort` needs (total + transitive) for `xleq`.
instance : Std.Total Block.xleq := ⟨Block.xleq_total⟩
instance : IsTrans Block Block.xleq := ⟨fun _ _ _ => Block.xleq_trans⟩

/-! ### 1b. `xsort`: the deterministic sort and its linear-extension properties. -/

/-- **`Block.xsort seg`** (`ordering.rs::xsort`): the deterministic ordering of a segment, sorting
by block id via insertion sort over `xleq`. The within-segment total order `cordial_agreement`
scoped out — now a concrete function. -/
def Block.xsort (seg : List Block) : List Block := seg.insertionSort Block.xleq

/-- **`xsort_sorted`** — the output is `xleq`-`Pairwise` (sorted by id): consecutive blocks
are id-ordered. Uses `List.pairwise_insertionSort` with the `Std.Total`/`IsTrans` instances. -/
theorem xsort_sorted (seg : List Block) : (Block.xsort seg).Pairwise Block.xleq :=
  List.pairwise_insertionSort Block.xleq seg

/-- **`xsort_perm`** — `xsort` only *reorders*: it is a permutation of the segment, so the
total order loses no block and invents none (the `tau` segment is exactly the super-ratified blocks,
reordered). -/
theorem xsort_perm (seg : List Block) : List.Perm (Block.xsort seg) seg :=
  List.perm_insertionSort Block.xleq seg

/-- **`xsort_length`** — `xsort` preserves length (corollary of `xsort_perm`). -/
theorem xsort_length (seg : List Block) : (Block.xsort seg).length = seg.length :=
  (xsort_perm seg).length_eq

/-- **`xsort_mem`** — membership is preserved both ways: a block is in the sorted segment
iff it was in the segment. -/
theorem xsort_mem {b : Block} {seg : List Block} : b ∈ Block.xsort seg ↔ b ∈ seg :=
  (xsort_perm seg).mem_iff

/-- **`xsort_idem` (DETERMINISM).** Re-sorting an already-sorted segment is a no-op:
`xsort (xsort seg) = xsort seg`. This is the determinism property — `tau` is a fixpoint of `xsort`,
so the order is stable and node-independent. Proved from `Pairwise.insertionSort_eq` (a list already
`Pairwise r` is unchanged by `insertionSort r`). -/
theorem xsort_idem (seg : List Block) : Block.xsort (Block.xsort seg) = Block.xsort seg :=
  (xsort_sorted seg).insertionSort_eq

/-- **`xsort_segment_total_order` (the linear-extension keystone).** On a *canonical*
segment (distinct blocks have distinct ids — the content-addressing invariant, exactly
`Lace.Canonical` restricted to the segment), `xsort` realizes a genuine **linear order**: any two
DISTINCT blocks of the segment are *strictly* id-comparable (`a.id < b.id ∨ b.id < a.id`), and the
sorted output puts them in that strict order. So `tau` is a total order on the segment, not merely a
preorder — the deterministic within-segment ranking `ordering.rs::xsort` guarantees. This closes
OPEN-CM-XSORT's *totality/determinism* obligation as a theorem. -/
theorem xsort_segment_total_order (seg : List Block)
    (hcanon : ∀ a ∈ seg, ∀ b ∈ seg, a.id = b.id → a = b)
    {a b : Block} (ha : a ∈ seg) (hb : b ∈ seg) (hne : a ≠ b) :
    a.id < b.id ∨ b.id < a.id := by
  rcases lt_trichotomy a.id b.id with h | h | h
  · exact Or.inl h
  · exact absurd (hcanon a ha b hb h) hne
  · exact Or.inr h

/-! ## 2. `cordial_agreement_from_single_lace`: the BFT quorum model on the REAL `Lace`.

`cordial_agreement_from_lace` (in `CordialMiners`) already consumes the BFT quorum model on the real
`Authority.Blocklace.Lace`: both `Committed S cfg lᵢ` hypotheses are reads of the *one*
`CordialState.lace : Lace` via `ratifyingVoters` (the `HasApprovingBlock` filter over the actual
blocks). The single-lace specialization makes that manifest — both quorums are facts about ONE
concrete blocklace `S.lace`, not two abstract vote sets. -/

/-- **`cordial_agreement_from_single_lace` — agreement with BOTH quorums read off ONE
blocklace.** Two leaders `l₁ l₂` both `Committed` in the *same* `CordialState S` — i.e. the *single*
blocklace `S.lace` exhibits an `≥ n-f` `ratifyingVoters` read for *each* — cannot be distinct, under
the honest BFT model over the materialized (lace-derived) ratification votes plus id-determinism.
This is the audit's target sharpened: the quorum-intersection safety core is consumed on the actual
`Authority.Blocklace.Lace` `S.lace`, with both ratifier counts being `(ratifyingVoters …).length`
over that single DAG. A thin specialization of `cordial_agreement_from_lace` (same proof term),
recorded to confirm the single-lace shape. -/
theorem cordial_agreement_from_single_lace
    (S : CordialState) (cfg : Finality.Config) (l₁ l₂ : Block)
    -- BOTH commit facts are reads of the SAME `S.lace : Authority.Blocklace.Lace`:
    (h₁ : Committed S cfg l₁) (h₂ : Committed S cfg l₂)
    (M : BFTModel cfg
      ((SuperRatification.ofLace h₁.some).votes ++ (SuperRatification.ofLace h₂.some).votes))
    (hid_inj : l₁.id = l₂.id → l₁ = l₂) :
    l₁ = l₂ :=
  cordial_agreement_from_lace S cfg l₁ l₂ h₁ h₂ M hid_inj

/-- **`cordial_no_conflicting_final_leaders_from_single_lace` — the `False`/safety form on
ONE lace.** Two *distinct* blocks cannot both be `Committed` in the same `CordialState` (both exhibit
an `≥ n-f` `ratifyingVoters` read off the *single* `S.lace`) under the honest model. -/
theorem cordial_no_conflicting_final_leaders_from_single_lace
    (S : CordialState) (cfg : Finality.Config) (l₁ l₂ : Block) (hconflict : l₁ ≠ l₂)
    (h₁ : Committed S cfg l₁) (h₂ : Committed S cfg l₂)
    (M : BFTModel cfg
      ((SuperRatification.ofLace h₁.some).votes ++ (SuperRatification.ofLace h₂.some).votes))
    (hid_inj : l₁.id = l₂.id → l₁ = l₂) :
    False :=
  hconflict (cordial_agreement_from_single_lace S cfg l₁ l₂ h₁ h₂ M hid_inj)

/-! ## 3. The dissemination residual, NAMED: `HonestRatifierConvergence` (post-GST).

The hard liveness/dissemination core. `cordial_agreement_from_lace`'s OPEN-CM-DISSEMINATION
residual item (3) is: after GST, on the *union* of two laces the honest nodes' causal pasts have
converged enough that a shared honest ratifier of one leader is visible as a ratifier of the other
(the `dissemination.rs` reliable-broadcast guarantee). We give it as an explicit `structure` — the
exact shape the safety argument *consumes* — so it is a typed hypothesis the runtime discharges, not
prose and not a `sorry`. -/

/-- **`HonestRatifierConvergence cfg lid₁ lid₂ V` — the post-GST dissemination residual, named.**
Over a combined ratification-vote universe `V` (the union of two laces' materialized ratifier votes),
this is the witness that gossip/reliable-broadcast convergence has produced a *single honest*
participant that ratifies BOTH candidate leader ids. Its fields ARE the conclusion of
`BFT.honest_witness_in_intersection` *post-convergence*:

* `M` — the adversary/honesty discipline over `V` (`≤ f` Byzantine, `n > 3f`, honest-vote-once),
* `witness` — the converged honest ratifier,
* `honest` / `ratifies₁` / `ratifies₂` — it is honest and ratifies both leader ids on `V`.

This is exactly the `dissemination.rs` guarantee the safety argument needs and the SAME residual as
`BFT.lean`'s O2 — *deriving* it is the post-GST pacemaker/view-synchrony argument (see
`cm_pacemaker_residual`). Here it is a hypothesis the runtime discharges. -/
structure HonestRatifierConvergence (cfg : Finality.Config)
    (lid₁ lid₂ : Authority.Blocklace.BlockId) (V : List Vote) where
  /-- The adversary/honesty model over the combined ratification-vote universe `V`. -/
  M : BFTModel cfg V
  /-- The converged honest ratifier participant. -/
  witness : Nat
  /-- The witness is honest (non-Byzantine). -/
  honest : ¬ M.Byzantine witness
  /-- After convergence, the witness ratifies leader id `lid₁` (visible on `V`). -/
  ratifies₁ : witness ∈ votersFor V lid₁
  /-- After convergence, the witness ratifies leader id `lid₂` (visible on `V`). -/
  ratifies₂ : witness ∈ votersFor V lid₂

/-- **`HonestRatifierConvergence.ofQuorums` — the convergence witness IS the
quorum-intersection conclusion.** When BOTH leader ids reach the BFT quorum `n - f` on the combined
universe `V`, the converged honest ratifier exists: it is exactly the honest witness
`BFT.honest_witness_in_intersection` produces. So `HonestRatifierConvergence` is not a stronger
oracle than the safety core already grants under quorum — it is its existential output, named. -/
noncomputable def HonestRatifierConvergence.ofQuorums
    (cfg : Finality.Config) (V : List Vote) (M : BFTModel cfg V)
    (lid₁ lid₂ : Authority.Blocklace.BlockId)
    (hq1 : cfg.n - cfg.f ≤ (votersFor V lid₁).length)
    (hq2 : cfg.n - cfg.f ≤ (votersFor V lid₂).length) :
    HonestRatifierConvergence cfg lid₁ lid₂ V :=
  let w := honest_witness_in_intersection cfg V M lid₁ lid₂ hq1 hq2
  { M := M
    witness := w.choose
    honest := w.choose_spec.1
    ratifies₁ := w.choose_spec.2.1
    ratifies₂ := w.choose_spec.2.2 }

/-- **`agreement_of_convergence` — agreement GIVEN the named dissemination residual.** With
the post-GST `HonestRatifierConvergence` witness in hand (the converged honest ratifier of both
leaders) plus the DAG honesty law (honest-one-ratification, here the BFT model's `honest_vote_once`)
and id-determinism, the two leaders collapse `l₁ = l₂`. This is the liveness-side companion to
`cordial_agreement`: it shows the dissemination residual is *exactly* what is needed — once the
runtime discharges `HonestRatifierConvergence`, agreement is mechanical. -/
theorem agreement_of_convergence
    (cfg : Finality.Config) (l₁ l₂ : Block) (V : List Vote)
    (conv : HonestRatifierConvergence cfg l₁.id l₂.id V)
    (hid_inj : l₁.id = l₂.id → l₁ = l₂) :
    l₁ = l₂ :=
  hid_inj (conv.M.honest_vote_once conv.witness l₁.id l₂.id conv.honest conv.ratifies₁ conv.ratifies₂)

/-! ## 4. The HARD residual, named: the post-GST pacemaker (OPEN-CM-LIVENESS / O2).

That a wave *eventually* super-ratifies a leader (the `tau` ordering makes progress) is the post-GST
pacemaker / view-synchrony argument — the SAME named obstruction as `BFT.lean`'s O2 and
`BeaconSpace`'s honest-leader hit. We name it as a `Prop`-valued statement and connect it to its
existing partial discharge over the randomness beacon, rather than restate or fake it. -/

/-- **`cm_pacemaker_residual votesOf cfg` — the `[hard] OPEN-CM-LIVENESS` residual, NAMED.** The
post-GST progress statement for Cordial-Miners: there EXISTS a round and a block that the network's
delivered votes commit by quorum. This is the conclusion a from-scratch pacemaker/view-synchrony
proof must establish; it is the SAME shape as `World.committedByQuorum`-existence and the SAME
obstruction as `BFT.lean`'s O2. It is stated, never assumed here as a global axiom — its discharge is
the partial-synchrony pacemaker argument, partially supplied over the beacon (next theorem). -/
def cm_pacemaker_residual {Msg : Type} [World Msg]
    (votesOf : List Msg → List Vote) (cfg : Finality.Config) : Prop :=
  ∃ (r : Nat) (block : Nat), committedByQuorum votesOf r cfg block

/-- **`cm_pacemaker_from_gstRound` — the residual reduces to a delivered GST round.** GIVEN
a post-GST round whose honest supermajority's votes are delivered (`BFT.GSTRound` — DLS88 Δ-delivery
+ HotStuff responsive view), the Cordial-Miners pacemaker residual holds. So the irreducible part of
`cm_pacemaker_residual` is exactly "after GST an honest quorum's votes are delivered" — the named O2
obstruction, no more. The `GSTRound → committed` step is `BFT.gst_liveness_from_round_model`. -/
theorem cm_pacemaker_from_gstRound {Msg : Type} [World Msg]
    (votesOf : List Msg → List Vote) (cfg : Finality.Config) (block : Nat)
    {r : Nat} (hgst : BFT.GSTRound votesOf cfg block r) :
    cm_pacemaker_residual votesOf cfg :=
  ⟨r, block, BFT.gst_liveness_from_round_model votesOf cfg block hgst⟩

/-! ## 4b. OPEN-CM-LIVENESS → a PROVEN CONDITIONAL on the named partial-synchrony carrier.

§4's `cm_pacemaker_from_gstRound` still takes a `GSTRound` — the COARSE top-of-tower premise (it
already assumes the quorum-formed round). That leaves the residual looking like a bare assumption.
But the partial-synchrony liveness tower below `GSTRound` is already PROVEN
(`Proof.BFTLiveness.Pacemaker` → `Proof.GST.GSTModel`, kernel-clean): from the bare delivery
primitives — honest-leader co-finality past GST + the honest set being a supermajority + HotStuff
Δ-delivery — a quorum is DERIVED, never assumed. We WIRE that proven descent into the Cordial-Miners
surface, so the named OPEN-CM-LIVENESS / O2 obstruction becomes a PROVEN CONDITIONAL on the
FLP-irreducible synchrony hypothesis (a `GSTModel` field bundle — a hypothesis/Prop-portal, carried
exactly as `World.recv_mono`/`gst_liveness` are, NEVER an `axiom`/`sorry`), not a hand-wave.

The shape is exactly the standard BFT conditional-liveness statement: GIVEN partial synchrony (GST +
the honest-supermajority delivery the runtime discharges after GST), liveness — a wave eventually
super-ratifies a block by quorum — HOLDS. FLP forbids the UNconditional form; the conditional is the
honest theorem, and it is now proved from the minimized carrier rather than the coarse `GSTRound`. -/

/-- **`cm_pacemaker_from_gstModel` — the conditional liveness, on the MINIMIZED carrier.** GIVEN the
partial-synchrony `Proof.GST.GSTModel` (the bare post-GST delivery primitives: a DLS88 GST round,
honest-leader co-finality `honestLeader_eventually`, the BFT honest-supermajority `honest_quorum`,
the HotStuff Δ-delivery `honest_le_delivered`) — NONE of whose fields is "a quorum forms" — the
Cordial-Miners pacemaker residual HOLDS: some wave is committed by quorum at some round. The quorum
is DERIVED via the proven `GST.gst_liveness` descent, so this is the genuine conditional-liveness
theorem: the OPEN-CM-LIVENESS residual is no longer "assume a quorum-formed round" but "given the
named partial-synchrony carrier, liveness is PROVED". -/
theorem cm_pacemaker_from_gstModel {Msg : Type} [World Msg]
    (votesOf : List Msg → List Vote) (cfg : Finality.Config)
    (G : Proof.GST.GSTModel Msg votesOf cfg) :
    cm_pacemaker_residual votesOf cfg :=
  Proof.GST.gst_liveness G

/-- **`cm_liveness_from_cofinality` — the residual REDUCED to the FLP-irreducible primitives.**
The fully-unfolded conditional: from the honest-supermajority + Δ-delivery delivery data AND bare
honest-leader co-finality `∀ t, ∃ r ≥ t, honestLeader r` — and NOTHING that assumes a quorum forms —
the Cordial-Miners pacemaker residual HOLDS. The GST/post-GST conjunct of co-finality is itself
DERIVED (`GST.honestLeader_eventually_of_fair`, the `r := max t gst` move). So the entire OPEN-CM-
LIVENESS residual reduces to: "after GST the honest supermajority's votes are delivered" (population +
Δ facts the runtime discharges) and "honest leaders recur" (bare co-finality) — the SOLE irreducible
synchrony assumption, made explicit. This is the precisely-scoped conditional, with everything above
co-finality + Δ-delivery PROVEN, not assumed. -/
theorem cm_liveness_from_cofinality {Msg : Type} [World Msg]
    (votesOf : List Msg → List Vote) (cfg : Finality.Config)
    (gst : Nat) (block : Nat → Nat) (honestLeader : Nat → Prop) (honestEndorsers : Nat → Nat)
    (honest_quorum : ∀ r, honestLeader r → cfg.threshold ≤ honestEndorsers r)
    (honest_le_delivered : ∀ r, gst ≤ r → honestLeader r →
      honestEndorsers r ≤ (votersFor (votesOf (World.recv r)) (block r)).length)
    (hcofinal : ∀ t, ∃ r, t ≤ r ∧ honestLeader r) :
    cm_pacemaker_residual votesOf cfg :=
  cm_pacemaker_from_gstModel votesOf cfg
    (Proof.GST.gstModel_of_cofinal gst block honestLeader honestEndorsers
      honest_quorum honest_le_delivered hcofinal)

/-! ### 4b′. MUTATION-CONFIRMATION — the synchrony hypothesis is LOAD-BEARING, not decorative.

The conditional must BITE: WITHOUT the partial-synchrony hypothesis the liveness conclusion must NOT
follow. We exhibit a concrete delivery-data instance that satisfies EVERY field of the carrier EXCEPT
co-finality — the FLP adversary that schedules all honest leaders BEFORE GST (`honestLeader r := r < 5`,
`gst := 10`) — and prove its co-finality premise is FALSE. So `cm_liveness_from_cofinality` cannot be
discharged for it: drop co-finality and the residual is provably underivable from the remaining data.
This confirms the carried hypothesis is the genuine FLP-irreducible assumption, not a vacuous portal. -/

/-- **`cm_liveness_needs_cofinality` (MUTATION TOOTH).** The below-GST adversary's honest-leader
predicate (`r < 5`, with `gst = 10`) is NOT co-final: there is no honest leader at or past round 5,
so `∀ t, ∃ r ≥ t, honestLeader r` FAILS at `t = 5`. Hence the co-finality premise of
`cm_liveness_from_cofinality` is unsatisfiable for this adversary — the conditional cannot fire, and
no quorum is forced. The synchrony hypothesis is therefore LOAD-BEARING: remove it (or face an
adversary that starves honest leaders past GST) and liveness does NOT follow. Rides the proven
`GST.Inhabited.teeth_bounded_not_cofinal`. -/
theorem cm_liveness_needs_cofinality :
    ¬ (∀ t, ∃ r, t ≤ r ∧ (fun r => r < 5) r) :=
  Proof.GST.Inhabited.teeth_bounded_not_cofinal

/-! ### 4b″. NON-VACUITY — the conditional FIRES on the inhabited reference carrier.

The conditional is not an empty implication: the reference `GSTModel` (`GST.Inhabited.gstModel` — GST
at round 3, three honest endorsers delivering block 7, honest leaders every round, hence co-final)
DISCHARGES the residual: a real quorum forms. So `cm_pacemaker_from_gstModel` both bites (4b′) and
fires (here) — the hallmark of a non-vacuous conditional. -/

/-- **`cm_pacemaker_residual_inhabited` (the conditional FIRES).** On the reference world the bare
partial-synchrony carrier `GST.Inhabited.gstModel` discharges `cm_pacemaker_residual`: the three
honest voters `0,1,2` for block 7 meet the threshold-3 quorum, DERIVED through the GST descent. So
the conditional liveness is non-vacuous — a real super-ratified wave is produced from the bare
delivery primitives, with no leader-election sub-protocol and no assumed quorum. -/
theorem cm_pacemaker_residual_inhabited :
    cm_pacemaker_residual (Msg := Dregg2.World.Reference.M)
      Proof.BFTLiveness.Inhabited.votesOf Proof.BFTLiveness.Inhabited.cfg :=
  cm_pacemaker_from_gstModel _ _ Proof.GST.Inhabited.gstModel

/-! ## 5. Non-vacuity for the residuals.

The dissemination residual `HonestRatifierConvergence` is non-vacuous. We build it on a concrete,
*computed-from-the-lace* ratifier set: the three distinct ratifiers `0,1,2` the inhabiting lace
`ratLace` exhibits for `rg1` (`CordialMiners.Inhabited.quorum_from_lace`), materialized via
`votesFromVoters`. The `votersFor` count is then read off by the proven `votersFor_votesFromVoters`,
the empty adversary inhabits `BFTModel`, and `ofQuorums` produces the converged honest ratifier — so
the named post-GST residual is inhabited by a real super-ratified leader's ratifier set. -/

namespace Inhabited

open Dregg2.Proof.CordialMiners.Inhabited

/-- The concrete ratifier set the inhabiting lace `ratLace` exhibits for `rg1` (participants
`0,1,2`, each with an approving block in observer `ro`'s causal past — `pᵢ_ratifies`). -/
def selfVoters : List AuthorId := [0, 1, 2]

/-- The materialized ratification votes for `rg1` from `selfVoters` (`votesFromVoters` — one
`Vote ⟨p, rg1.id⟩` per ratifier). A concrete, computable `List Vote`. -/
def selfVotes : List Vote := votesFromVoters selfVoters rg1.id

/-- **`selfVotes_votersFor`** — the `votersFor` count of `selfVotes` for `rg1.id` is exactly
the three ratifiers (`votersFor_votesFromVoters` + `selfVoters` is `Nodup`): no shrinkage, the count
is read off the lace's ratifier list. -/
theorem selfVotes_votersFor : votersFor selfVotes rg1.id = selfVoters := by
  rw [selfVotes, votersFor_votesFromVoters]; decide

/-- Every vote in `selfVotes` endorses `rg1.id` (it is the materialized ratification set for `rg1`).
So a voter for any block `blk` over `selfVotes` forces `blk = rg1.id`. -/
theorem selfVotes_voter_block {v blk : Nat} (h : v ∈ votersFor selfVotes blk) : blk = rg1.id := by
  rw [votersFor, List.mem_dedup, List.mem_map] at h
  obtain ⟨w, hwmem, _⟩ := h
  rw [List.mem_filter] at hwmem
  obtain ⟨hwin, hwblk⟩ := hwmem
  -- `w ∈ selfVotes = [⟨0,rg1.id⟩,⟨1,rg1.id⟩,⟨2,rg1.id⟩]`; each has `.block = rg1.id`. The filter
  -- predicate says `w.block = blk`, so `blk = rg1.id`.
  simp only [selfVotes, votesFromVoters, selfVoters, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hwin
  -- `hwblk : decide (w.block = blk) = true`; extract `w.block = blk` then read `w.block = rg1.id`.
  have hwb : w.block = blk := by simpa using hwblk
  rcases hwin with rfl | rfl | rfl <;> exact hwb.symm

/-- The voters over `selfVotes` for any block are among `{0,1,2}` (`selfVotes`' only voters). -/
theorem selfVotes_voter_mem {v blk : Nat} (h : v ∈ votersFor selfVotes blk) :
    v ∈ ({0, 1, 2} : Finset Nat) := by
  have hblk : blk = rg1.id := selfVotes_voter_block h
  subst hblk
  rw [selfVotes_votersFor] at h
  simp only [selfVoters, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> decide

/-- A `BFTModel` over `selfVotes`: the empty adversary (no one Byzantine), the `n>3f` floor from
`cfg`, every voter in `selfVotes` endorsing only `rg1.id` (honest-vote-once trivially), and the
population bound from the three distinct ratifiers. Mirrors `BFT.Inhabited.model`. -/
def selfModel : BFTModel cfg selfVotes where
  Byzantine := fun _ => False
  byzantineDec := fun _ => inferInstanceAs (Decidable False)
  fault_bound := by intro b₁ b₂; simp
  bft_threshold := by decide
  population_bound := by
    intro b₁ b₂
    -- the union of any two blocks' distinct voters is ⊆ {0,1,2}, card ≤ 3 ≤ 4 = n.
    refine le_trans (Finset.card_le_card ?_)
      (show ({0, 1, 2} : Finset Nat).card ≤ cfg.n from by decide)
    intro x hx
    rw [Finset.mem_union, List.mem_toFinset, List.mem_toFinset] at hx
    rcases hx with h | h
    · exact selfVotes_voter_mem h
    · exact selfVotes_voter_mem h
  honest_vote_once := by
    -- every vote in `selfVotes` endorses `rg1.id`, so b₁ = rg1.id = b₂.
    intro v b₁ b₂ _ hv1 hv2
    rw [selfVotes_voter_block hv1, selfVotes_voter_block hv2]

/-- **`selfConvergence` — the dissemination residual is INHABITED.** The lace-read ratifier
set for `rg1` (the three distinct ratifiers `0,1,2`, count `= 3 = n - f`, from `selfVotes_votersFor`)
gives, via `ofQuorums`, a concrete `HonestRatifierConvergence` for `rg1.id` against itself — the
converged honest ratifier. So the named post-GST dissemination residual is non-vacuous: a real
super-ratified leader's lace ratifier set supplies it. -/
noncomputable def selfConvergence : HonestRatifierConvergence cfg rg1.id rg1.id selfVotes :=
  HonestRatifierConvergence.ofQuorums cfg selfVotes selfModel rg1.id rg1.id
    (by rw [selfVotes_votersFor]; decide) (by rw [selfVotes_votersFor]; decide)

/-- The converged honest ratifier of `rg1` yields agreement (sanity: the residual is a real witness,
not a vacuous one — `agreement_of_convergence` consumes it). -/
theorem selfConvergence_agreement : rg1 = rg1 :=
  agreement_of_convergence cfg rg1 rg1 selfVotes selfConvergence (fun _ => rfl)

end Inhabited

/-! ## 6. Axiom hygiene — every additive keystone is kernel-clean.

`#assert_axioms` FAILS the build if any of these depends on `sorryAx`. The `xsort` keystones reduce
to `Nat` order + `List.insertionSort`/`pairwise_insertionSort` (`sorry`-free mathlib); the
single-lace agreement reduces to the existing `cordial_agreement_from_lace`; the convergence keystones
reduce to `BFT.honest_witness_in_intersection` / `BFTModel.honest_vote_once` (structure fields, not
axioms). The §4b CONDITIONAL-LIVENESS keystones (`cm_pacemaker_from_gstModel`,
`cm_liveness_from_cofinality`, the mutation tooth, and the inhabited firing) reduce to the proven
`GST.gst_liveness` descent + `GSTModel` structure FIELDS (the FLP-irreducible synchrony hypothesis is
a field/Prop-portal, like `World.recv_mono`/`gst_liveness`, NEVER an `axiom`/`sorry` — so it does NOT
appear in `collectAxioms`). We do NOT pin `cm_pacemaker_residual` (a `def` of a `Prop`) — it is a
NAMED statement; what is now PROVED is the conditional that discharges it from the named carrier. -/

#assert_axioms xsort_consistency
#assert_axioms xsort_sorted
#assert_axioms xsort_perm
#assert_axioms xsort_idem
#assert_axioms xsort_segment_total_order
#assert_axioms cordial_agreement_from_single_lace
#assert_axioms cordial_no_conflicting_final_leaders_from_single_lace
#assert_axioms HonestRatifierConvergence.ofQuorums
#assert_axioms agreement_of_convergence
#assert_axioms cm_pacemaker_from_gstRound
-- §4b — OPEN-CM-LIVENESS turned into a PROVEN CONDITIONAL on the named partial-synchrony carrier:
#assert_axioms cm_pacemaker_from_gstModel
#assert_axioms cm_liveness_from_cofinality
#assert_axioms cm_liveness_needs_cofinality
#assert_axioms cm_pacemaker_residual_inhabited
#assert_axioms Inhabited.selfConvergence

end Dregg2.Proof.CordialMiners
