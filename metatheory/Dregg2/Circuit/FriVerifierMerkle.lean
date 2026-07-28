/-
# `Dregg2.Circuit.FriVerifierMerkle` — STAGE 3: Merkle binding as EXTRACTION-AS-DATA + birthday,
and the DISCHARGE of Stage 2's freshness carrier.

`docs/reference/FRI-EXTRACTION-FLOOR-DESIGN.md` §5 Stage 3. Stage 1 (`FriVerifierO`) gave the
faithfulness bridge + the per-path query budget `permCallCount`; Stage 2 (`FriVerifierFS`) turned the
two Fiat–Shamir non-exceptionality conjuncts into PROVEN-except-with-ε, over the `RomCounting` counting
model, but LEFT the freshness facts (`fsPt i ∉ S`, `powPt j ∉ S`) as a SUPPLIED named carrier. This
file delivers the two Merkle-recompute conjuncts and advances that carrier.

## The three deliverables

  **1. `findCollisionZ` — extraction-as-data over the REAL `merkleRecomputeZ`.**
  A COMPUTABLE `… → Option (List ℤ × List ℤ)` that walks the deployed scalar-digest Merkle recompute
  (`OodCommitmentBinding.merkleRecomputeZ`, node hash `sponge [·,·]`) for two leaves over one
  index/sibling path and returns a genuine SPONGE COLLISION as DATA. This is VCVio's `findCollision`
  shape (`VCVio/CryptoFoundations/MerkleTree/Inductive/Binding.lean`,
  `getPutativeRootWithHash_binding`) ported to `merkleRecomputeZ`. There is NO adversary, NO
  probability, NOTHING to falsify — only:
    * `findCollisionZ_sound`    : `some (x,y) ⟹ x ≠ y ∧ sponge x = sponge y` (a genuine collision);
    * `findCollisionZ_complete` : two DISTINCT leaves recomputing to ONE root ⟹ `some _`;
  plus `findCollisionZ_none_binds` (the contrapositive: `none` + equal roots ⟹ the leaves are EQUAL —
  Merkle BINDING derived from PATH-collision-freeness, with NO `Poseidon2SpongeCR` hypothesis) and
  `equivocation_extracts_collisionZ` (the deployed `OodCommitmentBinding` equivocation extracted).

  **2. The Merkle ε via `birthday_cond`.** Over the finite two-argument node oracle
  `H : α × α → α` (the width-pinned sponge state; `Fintype α`), the collision-finder `collFinder`
  is a `QueryBounded (2·|path|)` `OracleComp` that READS the recompute path (a straight-line
  query-log extractor) and outputs a collision pair. `collFinder_equivocation_collWin` proves it wins
  the `collWin` event whenever two distinct leaves recompute to one root; `birthday_cond` then bounds
  the probability the query log contains any such collision by `(2L·|S| + (2L)² + 1)/|α|`
  (`merkle_path_collision_prob_le`, `merkle_equivocation_prob_le`). So the two Merkle conjuncts hold
  except-with-ε in the ROM, and `Poseidon2SpongeCR`'s USE in this leg is DERIVED (§1 above) — the CR
  class stays only for the concrete Poseidon2 instantiation (`sponge_pair_oracle_bridge` records the
  deployed `sponge [a,b] = H (a,b)` embedding, the §4.2/§4.5 named carrier).

  **3. ⚑ DISCHARGE Stage 2's freshness carrier — the QueryLog freshness interface (§4.5).**
  `queriedFinset M H` = the adversary's ACTUAL query set (read off `OracleComp.evalLog`/`queried`),
  with `queriedFinset_card_le : QueryBounded Q M → card ≤ Q` (counted against `permCallCount` on the
  verifier side, `verifier_queriedFinset_card_le_permCallCount`). `fs_epsilon_bound_of_log` re-bases
  Stage 2's `fs_epsilon_bound` with `S := queriedFinset A H`, `σ := H`: the supplied `fsPt i ∉ S`
  becomes `fsPt i ∉ queriedFinset A H` — "the challenge squeeze point was not queried by the
  adversary", a CONCRETE fact about the real log rather than an abstract hypothesis.

## Honest scope — what discharges, what remains NAMED

DISCHARGED here (sorry-free, axiom-clean):
  - Extraction-as-data over the real `merkleRecomputeZ` (deliverable 1) — COMPLETE, nothing to falsify.
  - The Merkle ε over the finite node oracle (deliverable 2) — `birthday_cond` applied to the
    log-reading extractor; the equivocation event is majorised by `collWin`.
  - The freshness INTERFACE (deliverable 3): `queriedFinset`, its `card ≤ Q` (permCallCount) bound,
    and `fs_epsilon_bound` re-based onto the real query log — the carrier is now phrased over the
    ADVERSARY'S ACTUAL QUERIES, `S.card ≤ permCallCount`, not an abstract `S`.

REMAINS a NAMED residual (precisely — not faked):
  - **The transcript-ordering non-membership** `fsPt i ∉ queriedFinset A H` for the SPECIFIC derived
    challenge points. Proving it needs the composed *adversary-then-verify* experiment and the
    argument that the squeeze point is DETERMINED by post-commitment sponge state the adversary
    cannot have queried before committing (Stage 2's §6 falsifier: were it false, the deployed FS
    transcript order would have a real bug). The interface reduces the carrier to EXACTLY this fact.
  - **The finite-oracle instantiation** (§4.2/§4.5): the deployed permutation `perm : List F → List F`
    / list sponge vs. the width-pinned finite oracle `α × α → α`. `sponge_pair_oracle_bridge`
    records the embedding; pinning `α`/width to BabyBear is the permanent industry-standard carrier.

## Discipline

ADDITIVE: modifies NO deployed spec/proof (`merkleRecomputeZ`, `Poseidon2SpongeCR`,
`commitmentOpening_binds_of_poseidon2CR`, `verifyAlgo`, `verifyAlgoO`, `FriVerifierFS`,
`FriLdtExtractV3`, `RomOracle`, `RomQueryFloor`, `RomQueryLog` all untouched). `#assert_all_clean`
over the keystones; no `sorry`, no fresh `axiom`, no `native_decide`.
-/
import Dregg2.Circuit.OodCommitmentBinding
import Dregg2.Circuit.FriVerifierFS
import Dregg2.Circuit.FriVerifierO
import Dregg2.Crypto.RomQueryFloor
import Dregg2.Crypto.RomQueryLog
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Circuit.FriVerifierMerkle

open Dregg2.Circuit.OodCommitmentBinding
  (merkleRecomputeZ merkleRecomputeZ_binds_of_noColl commitmentOpening_binds_of_noColl)
open Dregg2.Crypto.RomOracle
open Dregg2.Crypto.RomCounting
  (cyl mem_cyl condProb condProb_le_of_imp condProb_congr)
open Dregg2.Crypto.RomQueryFloor (collWin collWin_pure collWin_query birthday_cond birthday_bound)

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-! ## §1 — `findCollisionZ`: EXTRACTION-AS-DATA over the deployed `merkleRecomputeZ`.

`merkleRecomputeZ sponge idx acc (s :: rest)` folds the leaf `acc` up one level with the ordered node
hash `sponge [·,·]` (even index ⇒ `acc` on the left), branching on the index bit, then recurses on
`rest` with the halved index. `nodeInput` names the 2-felt hash preimage at a level; `merkleRecomputeZ_cons`
is the one equational fact the walk needs. -/

/-- The ordered two-felt hash preimage at a level: `[acc, s]` on even index, `[s, acc]` on odd — exactly
the list `merkleRecomputeZ` hands to `sponge`. -/
def nodeInput (idx : Nat) (acc s : ℤ) : List ℤ :=
  if idx % 2 = 0 then [acc, s] else [s, acc]

/-- One level of the recompute, factored through `nodeInput`: the new accumulator is `sponge` of the
level's preimage. -/
theorem merkleRecomputeZ_cons (sponge : List ℤ → ℤ) (idx : Nat) (acc s : ℤ) (rest : List ℤ) :
    merkleRecomputeZ sponge idx acc (s :: rest)
      = merkleRecomputeZ sponge (idx / 2) (sponge (nodeInput idx acc s)) rest := by
  show merkleRecomputeZ sponge (idx / 2)
      (if idx % 2 = 0 then sponge [acc, s] else sponge [s, acc]) rest = _
  unfold nodeInput
  split_ifs <;> rfl

/-- `nodeInput` is injective in the leaf slot (the sibling `s` and index bit are held fixed): distinct
leaves give distinct preimages. -/
theorem nodeInput_inj (idx : Nat) (a b s : ℤ) (h : nodeInput idx a s = nodeInput idx b s) : a = b := by
  unfold nodeInput at h
  split_ifs at h with hp
  · exact (List.cons.inj h).1
  · exact (List.cons.inj (List.cons.inj h).2).1

/-- **`findCollisionZ` (EXTRACTION-AS-DATA).** Walk the recompute of two leaves `l1`, `l2` up the same
index/sibling path; the FIRST level whose two distinct preimages hash to the SAME digest is returned as
a genuine `sponge` collision `(in1, in2)`. `none` means no collision was found along the path (whence, if
the roots agree, the leaves were already equal — `findCollisionZ_none_binds`). Structural recursion on
`siblings`; COMPUTABLE, no oracle, no probability — VCVio's `findCollision` shape ported to the deployed
`merkleRecomputeZ`. -/
def findCollisionZ (sponge : List ℤ → ℤ) :
    Nat → ℤ → ℤ → List ℤ → Option (List ℤ × List ℤ)
  | _,   _,  _,  []        => none
  | idx, l1, l2, s :: rest =>
      if nodeInput idx l1 s ≠ nodeInput idx l2 s
          ∧ sponge (nodeInput idx l1 s) = sponge (nodeInput idx l2 s) then
        some (nodeInput idx l1 s, nodeInput idx l2 s)
      else
        findCollisionZ sponge (idx / 2)
          (sponge (nodeInput idx l1 s)) (sponge (nodeInput idx l2 s)) rest

/-- **SOUNDNESS — `some` yields a GENUINE collision.** Whenever `findCollisionZ` returns `some (x, y)`,
the pair is a real `sponge` collision: `x ≠ y` and `sponge x = sponge y`. The only emit site is the
`if`-guard that literally asserts both facts, so soundness is immediate by induction. NOTHING TO
FALSIFY — this is a statement about the extractor's output, not about any adversary. -/
theorem findCollisionZ_sound (sponge : List ℤ → ℤ) :
    ∀ (siblings : List ℤ) (idx : Nat) (l1 l2 : ℤ) (x y : List ℤ),
      findCollisionZ sponge idx l1 l2 siblings = some (x, y) →
      x ≠ y ∧ sponge x = sponge y := by
  intro siblings
  induction siblings with
  | nil => intro idx l1 l2 x y h; simp [findCollisionZ] at h
  | cons s rest ih =>
      intro idx l1 l2 x y h
      rw [findCollisionZ] at h
      split_ifs at h with hc
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hc
      · exact ih (idx / 2) _ _ x y h

/-- **COMPLETENESS — two DISTINCT leaves at ONE root force a collision.** If `l1 ≠ l2` yet both leaves
recompute to the SAME root over the same index/sibling path, `findCollisionZ` returns `some`. The
extractor cannot fail to find the collision that binding-violation guarantees. Induction on `siblings`:
the empty path forces `l1 = l2` (contradiction), and on `s :: rest` the head preimages already differ
(`nodeInput_inj`), so either they collide now (`some`) or the next-level digests differ and recompute to
one root (IH). -/
theorem findCollisionZ_complete (sponge : List ℤ → ℤ) :
    ∀ (siblings : List ℤ) (idx : Nat) (l1 l2 : ℤ),
      l1 ≠ l2 →
      merkleRecomputeZ sponge idx l1 siblings = merkleRecomputeZ sponge idx l2 siblings →
      ∃ p, findCollisionZ sponge idx l1 l2 siblings = some p := by
  intro siblings
  induction siblings with
  | nil =>
      intro idx l1 l2 hne hroot
      simp only [merkleRecomputeZ] at hroot
      exact absurd hroot hne
  | cons s rest ih =>
      intro idx l1 l2 hne hroot
      rw [merkleRecomputeZ_cons, merkleRecomputeZ_cons] at hroot
      have hin : nodeInput idx l1 s ≠ nodeInput idx l2 s := fun heq => hne (nodeInput_inj idx l1 l2 s heq)
      rw [findCollisionZ]
      split_ifs with hc
      · exact ⟨_, rfl⟩
      · have hhne : sponge (nodeInput idx l1 s) ≠ sponge (nodeInput idx l2 s) := fun he => hc ⟨hin, he⟩
        exact ih (idx / 2) _ _ hhne hroot

/-- **`findCollisionZ_none_binds` — MERKLE BINDING, `Poseidon2SpongeCR` DERIVED.** If the extractor finds
NO collision along the path (`= none`) and the two leaves recompute to the SAME root, the leaves are
EQUAL. This is Merkle binding obtained from PATH-collision-freeness ALONE — NO `Poseidon2SpongeCR`
hypothesis. The named CR floor's ROLE in this leg is thereby replaced by the except-with-ε
collision-freeness the birthday bound (§2) supplies: `none` is exactly "no collision on this path". -/
theorem findCollisionZ_none_binds (sponge : List ℤ → ℤ) (siblings : List ℤ) (idx : Nat) (l1 l2 : ℤ)
    (hnone : findCollisionZ sponge idx l1 l2 siblings = none)
    (hroot : merkleRecomputeZ sponge idx l1 siblings = merkleRecomputeZ sponge idx l2 siblings) :
    l1 = l2 := by
  by_contra hne
  obtain ⟨p, hp⟩ := findCollisionZ_complete sponge siblings idx l1 l2 hne hroot
  rw [hp] at hnone
  exact absurd hnone (Option.some_ne_none p)

/-- **`equivocation_extracts_collisionZ` — the deployed `OodCommitmentBinding` equivocation, extracted as
data.** A prover that opens two DISTINCT values (`vOpened ≠ vCommitted`) to ONE committed root (the
`hCommitted`/`hOpened` premises of `commitmentOpening_binds_of_poseidon2CR`) hands the extractor a
concrete `sponge` collision. This is `opening_equivocation_breaks_cr` turned from "a break ⟹ `¬
Poseidon2SpongeCR`" into "a break ⟹ HERE IS THE COLLISION". -/
theorem equivocation_extracts_collisionZ (sponge : List ℤ → ℤ)
    {root : ℤ} {idx : Nat} {siblings : List ℤ} {vCommitted vOpened : ℤ}
    (hne : vOpened ≠ vCommitted)
    (hCommitted : merkleRecomputeZ sponge idx vCommitted siblings = root)
    (hOpened    : merkleRecomputeZ sponge idx vOpened    siblings = root) :
    ∃ x y : List ℤ, findCollisionZ sponge idx vOpened vCommitted siblings = some (x, y)
      ∧ x ≠ y ∧ sponge x = sponge y := by
  have hroot : merkleRecomputeZ sponge idx vOpened siblings
      = merkleRecomputeZ sponge idx vCommitted siblings := by rw [hOpened, hCommitted]
  obtain ⟨p, hp⟩ := findCollisionZ_complete sponge siblings idx vOpened vCommitted hne hroot
  obtain ⟨x, y⟩ := p
  exact ⟨x, y, hp, findCollisionZ_sound sponge siblings idx vOpened vCommitted x y hp⟩

/-! ## §2a — The polymorphic node-oracle recompute (no finiteness; the deployed instance is over ℤ). -/

section MerklePoly

variable {α : Type}

/-- The ordered node preimage as an ORACLE POINT `(l, r) : α × α` (even index ⇒ leaf on the left). -/
def pnode (idx : Nat) (acc s : α) : α × α :=
  if idx % 2 = 0 then (acc, s) else (s, acc)

/-- `pnode` is injective in the leaf slot. -/
theorem pnode_inj (idx : Nat) (a b s : α) (h : pnode idx a s = pnode idx b s) : a = b := by
  unfold pnode at h
  split_ifs at h with hp
  · exact ((Prod.mk.injEq ..).mp h).1
  · exact ((Prod.mk.injEq ..).mp h).2

/-- Recompute against the two-argument oracle `H : α × α → α`: the deployed `merkleRecomputeZ` with the
node hash `sponge [a,b]` replaced by the oracle value `H (a, b)`. Structural recursion on `siblings`. -/
def merkleRecO (H : α × α → α) : Nat → α → List α → α
  | _,   acc, []        => acc
  | idx, acc, s :: rest => merkleRecO H (idx / 2) (H (pnode idx acc s)) rest

theorem merkleRecO_cons (H : α × α → α) (idx : Nat) (acc s : α) (rest : List α) :
    merkleRecO H idx acc (s :: rest) = merkleRecO H (idx / 2) (H (pnode idx acc s)) rest := rfl

end MerklePoly

/-! ## §2b — The Merkle ε: `birthday_cond` bounds `Pr[the query log contains a collision]`.

The birthday bound needs a FINITE oracle. The deployed node hash is `sponge [a, b]` over the width-pinned
sponge state; we model it as the two-argument oracle `H : α × α → α` with `α` finite (the §4.2/§4.5
named instantiation carrier, `sponge_pair_oracle_bridge` below). The collision-finder `collFinder` is a
`QueryBounded` `OracleComp` that READS the recompute path — a straight-line query-log extractor — and
its `collWin` event fires on any equivocation. `birthday_cond` then bounds the collision probability. -/

section RomMerkle

variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]

/-- **The collision-finder as a query-log extractor.** Query the path preimages `pnode` level by level;
at the first level whose two distinct preimages receive equal answers, output that colliding pair;
otherwise recurse with the two answers as the next-level leaves. On the empty path (or when no collision
is found) it outputs the non-collision `((l1,l2),(l1,l2))`. Two queries per level ⇒ `QueryBounded (2·L)`. -/
def collFinder : Nat → α → α → List α → OracleComp (α × α) α ((α × α) × (α × α))
  | _,   l1, l2, []        => .pure ((l1, l2), (l1, l2))
  | idx, l1, l2, s :: rest =>
      .query (pnode idx l1 s) (fun h1 =>
        .query (pnode idx l2 s) (fun h2 =>
          if pnode idx l1 s ≠ pnode idx l2 s ∧ h1 = h2 then
            .pure (pnode idx l1 s, pnode idx l2 s)
          else collFinder (idx / 2) h1 h2 rest))

/-- `collFinder` makes at most `2·|siblings|` queries along every path. -/
theorem collFinder_bounded (idx : Nat) (l1 l2 : α) (siblings : List α) :
    QueryBounded (2 * siblings.length) (collFinder idx l1 l2 siblings) := by
  induction siblings generalizing idx l1 l2 with
  | nil => exact QueryBounded.pure 0 _
  | cons s rest ih =>
      have hstep : ∀ h1 h2 : α, QueryBounded (2 * rest.length)
          (if pnode idx l1 s ≠ pnode idx l2 s ∧ h1 = h2 then
              (OracleComp.pure (pnode idx l1 s, pnode idx l2 s) :
                OracleComp (α × α) α ((α × α) × (α × α)))
            else collFinder (idx / 2) h1 h2 rest) := by
        intro h1 h2
        split_ifs with hc
        · exact QueryBounded.pure _ _
        · exact ih (idx / 2) h1 h2
      have hlen : 2 * (s :: rest).length = (2 * rest.length + 1) + 1 := by
        simp only [List.length_cons]; ring
      rw [collFinder, hlen]
      exact QueryBounded.query _ _ _ (fun h1 =>
        QueryBounded.query _ _ _ (fun h2 => hstep h1 h2))

/-- **`collFinder` WINS `collWin` on any equivocation.** If `l1 ≠ l2` yet both leaves recompute to one
root under the oracle `H`, the finder's output is a genuine `H`-collision, so `collWin (collFinder …) H
= true`. Induction on the path, mirroring `findCollisionZ_complete` but over the oracle. -/
theorem collFinder_equivocation_collWin (H : α × α → α) :
    ∀ (siblings : List α) (idx : Nat) (l1 l2 : α),
      l1 ≠ l2 →
      merkleRecO H idx l1 siblings = merkleRecO H idx l2 siblings →
      collWin (collFinder idx l1 l2 siblings) H = true := by
  intro siblings
  induction siblings with
  | nil =>
      intro idx l1 l2 hne hroot
      simp only [merkleRecO] at hroot
      exact absurd hroot hne
  | cons s rest ih =>
      intro idx l1 l2 hne hroot
      rw [merkleRecO_cons, merkleRecO_cons] at hroot
      have hin : pnode idx l1 s ≠ pnode idx l2 s := fun heq => hne (pnode_inj idx l1 l2 s heq)
      -- Reduce `collWin` at the two head queries: answers are `H (pnode … l1 s)` and `H (pnode … l2 s)`.
      rw [collFinder]
      simp only [collWin_query]
      by_cases hcol : H (pnode idx l1 s) = H (pnode idx l2 s)
      · -- Collision at this level: the finder emits `(pnode l1, pnode l2)`.
        rw [if_pos ⟨hin, hcol⟩, collWin_pure]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hin, hcol⟩
      · -- No collision here: recurse with the two answers, still distinct, still to one root.
        rw [if_neg (fun h => hcol h.2)]
        exact ih (idx / 2) _ _ hcol hroot

/-- **⚑ THE MERKLE ε — `birthday_cond` bounds the probability the query log contains a collision.**
For the log-reading extractor `collFinder` over a path of length `L`, against an oracle already
conditioned collision-free on `S`, the probability its output is a genuine collision is at most
`(2L·|S| + (2L)² + 1)/|α|` — the birthday bound at query budget `Q = 2L`. This is `birthday_cond`
applied to `collFinder_bounded`; NOTHING under it is assumed. -/
theorem merkle_path_collision_prob_le (idx : Nat) (l1 l2 : α) (siblings : List α)
    (S : Finset (α × α)) (σ : α × α → α)
    (hσ : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → σ a ≠ σ b) :
    condProb (cyl S σ) (collWin (collFinder idx l1 l2 siblings))
      ≤ (((2 * siblings.length : ℕ) : ℝ) * (S.card : ℝ)
          + ((2 * siblings.length : ℕ) : ℝ) * ((2 * siblings.length : ℕ) : ℝ) + 1)
          / (Fintype.card α : ℝ) :=
  birthday_cond (collFinder_bounded idx l1 l2 siblings) S σ hσ

/-- **⚑ THE MERKLE-EQUIVOCATION ε.** For FIXED distinct leaves `l1 ≠ l2` and a fixed path, the
probability the RANDOM node oracle makes them recompute to one common root is at most the same birthday
bound — because any such equivocation is majorised by the finder's `collWin` event
(`collFinder_equivocation_collWin`), which `birthday_cond` bounds. So the two Merkle-recompute conjuncts
of `FriLdtExtractV3` hold except-with-ε in the ROM. -/
theorem merkle_equivocation_prob_le (idx : Nat) (l1 l2 : α) (siblings : List α)
    (hne : l1 ≠ l2) (S : Finset (α × α)) (σ : α × α → α)
    (hσ : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → σ a ≠ σ b) :
    condProb (cyl S σ)
        (fun H => decide (merkleRecO H idx l1 siblings = merkleRecO H idx l2 siblings))
      ≤ (((2 * siblings.length : ℕ) : ℝ) * (S.card : ℝ)
          + ((2 * siblings.length : ℕ) : ℝ) * ((2 * siblings.length : ℕ) : ℝ) + 1)
          / (Fintype.card α : ℝ) := by
  refine le_trans (condProb_le_of_imp ?_) (merkle_path_collision_prob_le idx l1 l2 siblings S σ hσ)
  intro H _ hwin
  exact collFinder_equivocation_collWin H siblings idx l1 l2 hne (of_decide_eq_true hwin)

end RomMerkle

/-- **`sponge_pair_oracle_bridge` — the deployed list sponge as the two-argument oracle (the §4.2/§4.5
named carrier).** The deployed node hash `sponge [a, b]` IS the two-argument oracle `H (a, b)` at
`H := fun p => sponge [p.1, p.2]`, and under this identification the deployed `merkleRecomputeZ` over ℤ
IS `merkleRecO`. The remaining carrier is the FINITE instantiation — pinning `α` (and the sponge width)
to the deployed BabyBear state — which is the permanent industry-standard random-oracle model, never
discharged. -/
theorem sponge_pair_oracle_bridge (sponge : List ℤ → ℤ) (idx : Nat) (acc : ℤ) (siblings : List ℤ) :
    merkleRecO (α := ℤ) (fun p => sponge [p.1, p.2]) idx acc siblings
      = merkleRecomputeZ sponge idx acc siblings := by
  induction siblings generalizing idx acc with
  | nil => rfl
  | cons s rest ih =>
      rw [merkleRecO_cons, merkleRecomputeZ_cons, ih]
      congr 1
      unfold pnode nodeInput
      split_ifs <;> rfl

/-! ## §3 — ⚑ DISCHARGE Stage 2's freshness carrier: the QueryLog freshness interface (§4.5).

Stage 2's `fs_epsilon_bound` supplies `hfs : ∀ i, fsPt i ∉ S` and `hpow : ∀ j, powPt j ∉ S` as a NAMED
carrier — `RomOracle` had no interface tying `S` to the adversary's real behaviour. Here `S` becomes the
adversary's ACTUAL query set, read off the `evalLog`/`queried` substrate (`RomQueryLog`). The carrier
is thereby re-phrased over the real log: `fsPt i ∉ S` ⟺ "the challenge squeeze point was NOT queried by
the adversary", with `S.card ≤ Q` (`permCallCount` on the verifier side). -/

open Dregg2.Circuit.FriVerifierFS (fs_epsilon_bound)
open Dregg2.Circuit.FriVerifierO (verifyAlgoO permCallCount verifyAlgoO_queryBounded)

/-- **THE ADVERSARY'S QUERY SET.** The finite set of points `M` actually queries under `H` — read off
the query trace (`OracleComp.queried`, equivalently the domain projection of `OracleComp.log`). This is
the `S` Stage 2's `cyl S σ` conditions on: what the adversary has already learned. -/
def queriedFinset {D R A : Type} [DecidableEq D] (M : OracleComp D R A) (H : D → R) : Finset D :=
  (M.queried H).toFinset

/-- FRESHNESS: `d` is fresh for `M` under `H` iff the adversary never queried it. -/
def Fresh {D R A : Type} [DecidableEq D] (M : OracleComp D R A) (H : D → R) (d : D) : Prop :=
  d ∉ queriedFinset M H

/-- Membership in the query set is membership in the query trace. -/
theorem mem_queriedFinset_iff {D R A : Type} [DecidableEq D] (M : OracleComp D R A) (H : D → R)
    (d : D) : d ∈ queriedFinset M H ↔ d ∈ M.queried H := by
  simp [queriedFinset, List.mem_toFinset]

/-- The query set is the domain projection of the `evalLog` trace — the interface tie-in the design
(§4.5) asks for: freshness is stated over `verifyAlgoO`'s (any adversary's) real logged queries. -/
theorem queriedFinset_eq_log_image {D R A : Type} [DecidableEq D] (M : OracleComp D R A) (H : D → R) :
    queriedFinset M H = ((M.evalLog H).2.map Prod.fst).toFinset := by
  rw [queriedFinset, M.evalLog_snd_map_fst_eq_queried]

/-- **⚑ THE FRESHNESS SET IS BOUNDED BY THE QUERY BUDGET.** A `Q`-query adversary's query set has at most
`Q` elements — so the conditioning set Stage 2 quantifies over is genuinely bounded, and (on the verifier
side) bounded by `permCallCount`. This is `QueryBounded.queried_length_le` through `List.toFinset_card_le`. -/
theorem queriedFinset_card_le {D R A : Type} [DecidableEq D] {M : OracleComp D R A} {Q : ℕ}
    (h : QueryBounded Q M) (H : D → R) : (queriedFinset M H).card ≤ Q :=
  le_trans (List.toFinset_card_le _) (h.queried_length_le H)

/-- **THE COUNT SIDE — the derived-challenge query set is `permCallCount`-bounded.** The verifier
`verifyAlgoO` queries at most `permCallCount` points, so the set of transcript/squeeze points it derives
(the challenges Stage 2 must be fresh FOR) has cardinality `≤ permCallCount`. This is the "counted against
`permCallCount`" half of §4.5. -/
theorem verifier_queriedFinset_card_le_permCallCount {F : Type} [Inhabited F] [DecidableEq F]
    (RATE : Nat) (toNat : F → Nat) (params : Dregg2.Circuit.FriVerifier.FriParams)
    (vk : Dregg2.Circuit.FriVerifier.RecursionVk F) (checks : Dregg2.Circuit.FriVerifier.FriChecks F)
    (initState : List F) (logN : Nat) (proof : Dregg2.Circuit.FriVerifier.BatchProofData F)
    (pub : Dregg2.Circuit.FriVerifier.WrapPublics F) (H : List F → List F) :
    (queriedFinset (verifyAlgoO RATE toNat params vk checks initState logN proof pub) H).card
      ≤ permCallCount params proof pub :=
  queriedFinset_card_le (verifyAlgoO_queryBounded RATE toNat params vk checks initState logN proof pub) H

/-- **⚑⚑ `fs_epsilon_bound_of_log` — Stage 2's FS ε-bound RE-BASED onto the real query log.**

Stage 2's `fs_epsilon_bound` took `hfs : ∀ i, fsPt i ∉ S` for an ABSTRACT `S`. Here `S := queriedFinset A H`
(the adversary `A`'s ACTUAL query set) and `σ := H` (the log pins `H` on what was queried). The supplied
freshness hypothesis is now `fsPt i ∉ queriedFinset A H` — a CONCRETE fact about the real log: "the
`i`-th derived challenge's squeeze point was not queried by the adversary". With `queriedFinset_card_le`,
`|S| ≤ Q` (≤ `permCallCount`). The FS-bad probability is the same `(Q+1)·deg/|F| + Q/2^pow`.

⚑ RESIDUAL, NAMED (not faked): proving `fsPt i ∉ queriedFinset A H` for the SPECIFIC derived challenges
is the transcript-ordering fact (the squeeze point is post-commitment sponge state the adversary cannot
have queried before committing). This interface reduces Stage 2's carrier to EXACTLY that non-membership
— no longer an abstract `S`, but the adversary's real log — and no further. -/
theorem fs_epsilon_bound_of_log
    {F : Type} [Fintype F] [DecidableEq F] [CommRing F] [IsDomain F]
    {D : Type} [Fintype D] [DecidableEq D] {AnsT : Type}
    (pow : ℕ) (A : OracleComp D (F × Fin (2 ^ pow)) AnsT) (H : D → F × Fin (2 ^ pow))
    (Q degBound : ℕ)
    (fsPt : Fin (Q + 1) → D) (hfs : ∀ i, fsPt i ∉ queriedFinset A H)
    (Efs : Fin (Q + 1) → Finset F) (hEfs : ∀ i, (Efs i).card ≤ degBound)
    (powPt : Fin Q → D) (hpow : ∀ j, powPt j ∉ queriedFinset A H) :
    condProb (cyl (queriedFinset A H) H)
        (fun G =>
          decide (∃ i : Fin (Q + 1), (G (fsPt i)).1 ∈ Efs i)
            || decide (∃ j : Fin Q, (G (powPt j)).2 = (0 : Fin (2 ^ pow))))
      ≤ ((Q + 1 : ℕ) * degBound : ℝ) / (Fintype.card F : ℝ) + (Q : ℝ) / ((2 : ℝ) ^ pow) :=
  fs_epsilon_bound pow (queriedFinset A H) H Q degBound fsPt hfs Efs hEfs powPt hpow

/-- **`freshness_card_bound` — the freshness carrier is now a BOUNDED, log-grounded obligation.** For a
`Q`-query adversary `A`, the conditioning set of the re-based `fs_epsilon_bound_of_log` has at most `Q`
elements; so the residual "the derived challenges are fresh" is a non-membership in a `≤ Q`-element set
read off `A`'s real trace — the shape Stage 4 discharges via the transcript-ordering argument. -/
theorem freshness_card_bound {D R A : Type} [DecidableEq D] {M : OracleComp D R A} {Q : ℕ}
    (h : QueryBounded Q M) (H : D → R) : (queriedFinset M H).card ≤ Q :=
  queriedFinset_card_le h H

/-! ## §4 — Teeth: the extraction and the ε are non-vacuous. -/

/-- **(TOOTH — the extractor FIRES on a concrete equivocation.)** On the constant-zero sponge (NOT
collision-resistant), the two distinct leaves `1 ≠ 2` recompute to root `0` over the one-level path `[5]`,
and `findCollisionZ` returns a genuine collision as data — so the completeness/soundness path is not
vacuous. Mirrors `OodCommitmentBinding.constant_sponge_equivocates`. -/
theorem findCollisionZ_fires_on_constant_sponge :
    ∃ x y : List ℤ,
      findCollisionZ (fun _ => 0) 0 1 2 [5] = some (x, y) ∧ x ≠ y ∧ (fun _ : List ℤ => (0 : ℤ)) x = 0 := by
  refine ⟨[1, 5], [2, 5], ?_, ?_, rfl⟩
  · decide
  · decide

/-- **(TOOTH — the Merkle ε is `< 1` at concrete params.)** At a path of length `1` (`Q = 2`), empty
conditioning `|S| = 0`, and `|α| = 7`, the birthday bound is `(0 + 4 + 1)/7 = 5/7 < 1` — a real
probability, not a vacuous `≤ 1`. -/
theorem merkle_epsilon_lt_one_example :
    (((2 * 1 : ℕ) : ℝ) * (0 : ℝ) + ((2 * 1 : ℕ) : ℝ) * ((2 * 1 : ℕ) : ℝ) + 1) / 7 < 1 := by norm_num

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  merkleRecomputeZ_cons,
  nodeInput_inj,
  findCollisionZ_sound,
  findCollisionZ_complete,
  findCollisionZ_none_binds,
  equivocation_extracts_collisionZ,
  pnode_inj,
  merkleRecO_cons,
  collFinder_bounded,
  collFinder_equivocation_collWin,
  merkle_path_collision_prob_le,
  merkle_equivocation_prob_le,
  sponge_pair_oracle_bridge,
  mem_queriedFinset_iff,
  queriedFinset_eq_log_image,
  queriedFinset_card_le,
  verifier_queriedFinset_card_le_permCallCount,
  fs_epsilon_bound_of_log,
  freshness_card_bound,
  findCollisionZ_fires_on_constant_sponge,
  merkle_epsilon_lt_one_example
]

end Dregg2.Circuit.FriVerifierMerkle
