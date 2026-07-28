/-
# Dregg2.Circuit.Emit.MinaStateQuery — verifiable Mina STATE-QUERY gadgets (K6)
(the last piece of the in-Lean Kimchi/Mina verifier: given a VERIFIED Mina ledger/state root,
prove a specific query — account balance/nonce, or a zkApp app-state field — via a Poseidon
Merkle path into the root; task K6 of `docs/MINA-KIMCHI-VERIFIER-PLAN.md`).

## What this file IS (and the honest boundary)

Mina's account database (and o1js application state) is a fixed-depth binary Merkle tree hashed
with **Poseidon over Pasta Fp** — NOT Keccak/SHA. So a state-query is a POSEIDON Merkle path from
an account/field leaf up to the ledger root. This REUSES K3 (`PastaPoseidon`, the Poseidon sponge)
as the node hash, and MIRRORS the ETH FIN/EXEC Merkle-fold PATTERN
(`LightClientEthFinFold`/`LightClientEthExecFold`): leaf → fold up the branch → root, with the
`reconstruct`-is-`foldReconstruct` and `htr*_commits_*` leaf-commitment shapes, at Poseidon
instead of SHA granularity.

Built here, over `PastaPoseidon.Ref.hash` (the o1js-`Poseidon.hash`-exact, KAT'd, `perm_forces`-
forced sponge):

  * `merkleFold` — the Poseidon Merkle-path fold, a `Nat` FOLD (the `absFold` shape of the ETH
    folds, at `poseidonPair = Poseidon(left,right)` over Fp); `ledgerReconstruct` = the ledger root
    a branch CLAIMS. `merkleFold_binding_of_noColl` — the fold is BINDING at a PER-INSTANCE
    non-equivocation side condition (mirrors `reconstruct_binding`): same-length branches to the
    same root carry the same leaf, provided the two paths do not collide the node hash at any
    level. ⚑ NOT "given Poseidon-2 CR" — see §3, the CR floor that used to sit here was PROVABLY
    FALSE and is deleted.
  * `leafHash` / `accountFields` — the account leaf as a Poseidon hash of the account fields in
    Mina's canonical order; `leafHash_commits_balance`/`_nonce`/`_zkappRoot` — the leaf COMMITS the
    queried field at the per-instance denial `¬ LeafColl` (mirrors `htrExec_commits_stateRoot`). A
    second layer commits a zkApp app-state field through `zkappRoot` (`query_binds_zkappField`).
  * `merkleFold_congr` — the path-fold CONGRUENCE (renamed 2026-07-27 from `merkleFold_forces`,
    which claimed a forcing it does not perform): substituting a pointwise-equal hash under the
    fold. It takes NO gate and NO `Assignment`; this file emits ZERO constraints. It is the shape
    that WOULD transport a per-node forcing to the whole path — and that per-node obligation
    (`PastaPoseidon` §7 residual #3) is NOT discharged here or anywhere. Residual #3.
  * the query DECISION: `verifyAccountQuery_from_fold` (a satisfying Merkle-path witness discharges
    the query boolean — no trusted bit), and `query_binds_balance`/`_nonce`/`_zkappField` (the
    non-equivocation payoff: under a verified root NO other account/field-value opens the same slot
    — the queried value is UNIQUELY bound). Both-polarity KAT'd against real Poseidon-Merkle
    vectors below.

## How this composes with K5 (verify-root → query-under-root)

The Kimchi verifier `KimchiVerify.kimchiVerifyDecision` (K5) attests the STATE — that a ledger root
is the state root of a Kimchi-VALID Mina block (subject to the IPA/FRI floor K5 names). This gadget
(K6) proves a QUERY UNDER a root. The INTENDED composition is
  (K5) verify-root  ∘  (K6) query-under-root.

⚑ IT IS NOT BUILT, AND AS OF 2026-07-27 THIS SECTION NO LONGER CLAIMS IT IS. There was a theorem
`mina_verify_then_query` here that "stated exactly that seam"; its seam-carrying conjunct was
`LedgerRootAttested root → … ∧ LedgerRootAttested root`, i.e. the caller's own hypothesis returned
— `P → P` over a universally quantified free predicate — and its other conjunct was vacuous through
the refuted floors. It is deleted (§7). A K5 caller invokes `query_binds_balance` directly with
`root` instantiated to the attested root; nothing in Lean connects the two files, and that gap is
residual #6 rather than a theorem. K6 does NOT re-verify the root; K5 does not touch the leaf.

## SOURCED vs RECONSTRUCTED (the Mina ledger-structure facts)

SOURCED (from the `~/dev/mina` o1-labs checkout + the pinned `mina-pasta-hash-probe`):

  * **Account field order** — `src/lib/mina_base/account.ml:222-232` (`Poly.t`):
    `public_key, token_id, token_symbol, balance, nonce, receipt_chain_hash, delegate, voting_for,
    timing, permissions, zkapp`. `accountFields` follows this order for the queryable prefix
    (`timing`/`permissions` folded away; `zkapp` → the committed `zkappRoot`).
  * **Account leaf hash** — `account.ml:377-380,506`: `Random_oracle.hash ~init:Hash_prefix.account
    (pack_input (to_input t))`, with `Hash_prefix.account = create "MinaAccount"`
    (`src/lib/hash_prefixes/hash_prefixes.ml:30`). So the leaf IS a Poseidon hash of the packed
    account fields under the "MinaAccount" domain prefix.
  * **o1js application `MerkleTree` node hash** — plain `Poseidon.hash([left, right])`, NO prefix,
    CONFIRMED by the pinned probe test `mina-pasta-hash-probe/src/main.rs:211`
    (`merkle_compress_matches_o1js_merkletree`, gold `0x0f82…b777`). This is EXACTLY `poseidonPair`
    here — so `merkleFold poseidonPair` is o1js `MerkleTree`/`MerkleWitness`/`MerkleMap` node
    hashing, byte-for-byte (the zkApp-state Merkle-query surface).
  * **Protocol account-ledger node hash** — `src/lib/mina_base/ledger_hash.ml:8,36-38`:
    `merge ~height h1 h2 = Random_oracle.hash ~init:(Hash_prefix.merkle_tree height) [h1; h2]`, with
    `Hash_prefix.merkle_tree i = create (Printf.sprintf "MinaMklTree%03d" i)`
    (`hash_prefixes.ml:51`) — a PER-HEIGHT domain prefix. This is the ONE fidelity gap vs the plain
    node hash (residual #1).

RECONSTRUCTED / MODELED here: `accountFields`/`leafHash` capture the account leaf's COMMITMENT
STRUCTURE (each field a committed Poseidon input) but NOT the exact `Account.crypto_hash` bit-
packing (`to_input`/`pack_input` packs balance/nonce/token into shared field elements) nor the
"MinaAccount" prefix; the commitment lemmas are packing-AGNOSTIC (they read positions out of the
field list and assume nothing about the encoding), so the exact serialization is a named
residual, not a hidden assumption. The `zkappRoot = zkappStateHash appState` model is a simplification of the real
`Zkapp_account.digest` (which also folds verification-key/permissions).

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. The `#guard` KATs reduce in the kernel (`Nat`/`Bool`, the o1js-exact Poseidon
reference). Imports `PastaPoseidon` (K3, transitively `PastaField` K1). ROOTED at
`Dregg2.lean:1540`, so the `#guard` KATs and `#assert_axioms` pins below run in the default build
(they did not when this file landed — see `docs/AUDIT-MINA-KIMCHI.md` F12).
-/
import Dregg2.Circuit.Emit.PastaPoseidon
import Dregg2.Circuit.Emit.PastaField

namespace Dregg2.Circuit.Emit.MinaStateQuery

open Dregg2.Circuit.Emit.PastaPoseidon
open Dregg2.Circuit.Emit.PastaField (pN)

set_option autoImplicit false

/-! ## §1 — The Poseidon pair-hash + the abstract Merkle-path fold.

`poseidonPair l r = Poseidon.hash [l, r]` is the o1js `MerkleTree` node hash (PINNED in-kernel at
§9 against the probe's depth-2 gold root — and false as shipped before the 2026-07-27 K3 sponge
fix, since length 2 was exactly the broken branch) and the Mina protocol-ledger `merge` at height 0 (the per-height prefix is residual #1). `merkleFold`
is the `absFold` of the ETH folds, at Nat/Fp with this pair-hash — walk the branch bottom-up,
index-bit selecting left/right at each level. -/

/-- **The Poseidon Merkle NODE hash** — `Poseidon(left, right)` over Pasta Fp, the K3 sponge on the
2-element input. Byte-for-byte the o1js `MerkleTree` node hash (probe `main.rs:211`). -/
def poseidonPair (l r : Nat) : Nat := Ref.hash [l, r]

/-- The node hash IS `PastaPoseidon.Ref.hash` of the 2-limb input — the o1js-`Poseidon.hash`-exact,
`perm_forces`-forced K3 primitive. (Definitional; the in-circuit forcing of ONE node is the
`absorbBlock_forces ∘ perm_forces ∘ squeeze` composition, K3 §7 residual #3.) -/
theorem poseidonPair_eq_hash (l r : Nat) : poseidonPair l r = Ref.hash [l, r] := rfl

/-- **The Poseidon Merkle-path FOLD** (the `absFold`/`reconstruct` shape at `poseidonPair`): walk
the sibling branch bottom-up, hashing `(sib, running)` or `(running, sib)` by the index bit, the
index shifting right each level. `merkleFold poseidonPair leaf branch idx` is the ledger root the
branch CLAIMS for `leaf` at path `idx`. Parameterized by the pair-hash `hp` (as `absFold` is) so
the forcing/binding lemmas are hash-generic and a per-height hash drops in (residual #1). -/
def merkleFold (hp : Nat → Nat → Nat) : Nat → List Nat → Nat → Nat
  | leaf, [], _ => leaf
  | leaf, sib :: rest, idx =>
      merkleFold hp (if idx % 2 = 1 then hp sib leaf else hp leaf sib) rest (idx / 2)

/-- The ledger root a Merkle-path witness reconstructs for `leaf` — `merkleFold` at the Poseidon
node hash (analogue of the ETH `reconstruct` / `foldReconstruct`). -/
def ledgerReconstruct (leaf : Nat) (branch : List Nat) (idx : Nat) : Nat :=
  merkleFold poseidonPair leaf branch idx

/-- Empty branch reconstructs the leaf. -/
theorem merkleFold_nil (hp : Nat → Nat → Nat) (leaf idx : Nat) :
    merkleFold hp leaf [] idx = leaf := rfl

/-- A one-level even step is the plain left-child hash (index bit 0). -/
theorem merkleFold_single_even (l s : Nat) : merkleFold poseidonPair l [s] 0 = poseidonPair l s :=
  rfl

/-- A one-level odd step swaps to the right (index bit 1). -/
theorem merkleFold_single_odd (l s : Nat) : merkleFold poseidonPair l [s] 1 = poseidonPair s l :=
  rfl

/-! ## §2 — The path-fold CONGRUENCE (function substitution up the branch).

⚑ NAMED FOR WHAT IT IS, 2026-07-27. This was `merkleFold_forces` and sat in the same `_forces`
family as `PastaPoseidon.perm_forces` and `PastaScalarMul.pallasLadder_forces` — which take an
`Assignment` and consume `acceptB … = true`, i.e. they read ACCEPTED GATES and conclude a value
relation. This one takes no gate, no `Assignment`, and no circuit: it is `f = g → F f = F g`, a
`congr` that holds for any two pointwise-equal functions over any carrier. Renamed
`merkleFold_congr`, and the claim that it "discharges the TREE" is downgraded to what it does —
substitute one hash for another under the fold.

The gap that leaves is REAL and is residual #3: this file emits ZERO constraints
(`grep -c 'VmConstraint2\|Assignment\|acceptB\|EmittedExpr'` = 0), so there is no per-node forcing
here to compose with. `merkleFold` is a `Nat` fold, not a generator. -/

/-- **The path-fold congruence.** If a hash `f` agrees with `hp` at every pair, folding `f` up the
branch equals folding `hp`. Pure function substitution — NO gate, NO `Assignment`, NO forcing. It
is the shape that WOULD let a per-node forcing lemma (`hnode`, K3 §7 residual #3, NOT proved here
and NOT proved anywhere for this file) transport to the whole path; that per-node obligation is the
entire content, and it is open. -/
theorem merkleFold_congr (f hp : Nat → Nat → Nat) (hnode : ∀ l r, f l r = hp l r) :
    ∀ (branch : List Nat) (leaf idx : Nat),
      merkleFold f leaf branch idx = merkleFold hp leaf branch idx := by
  intro branch
  induction branch with
  | nil => intro leaf idx; rfl
  | cons sib rest ih =>
    intro leaf idx
    simp only [merkleFold]
    by_cases hb : idx % 2 = 1
    · rw [if_pos hb, if_pos hb, hnode sib leaf]; exact ih _ _
    · rw [if_neg hb, if_neg hb, hnode leaf sib]; exact ih _ _

/-! ## §3 — The fold is BINDING (at a PER-INSTANCE non-equivocation side condition).

⚑ THE FLOOR THAT USED TO BE HERE WAS PROVABLY FALSE, AND EVERY PAYOFF BELOW IT WAS VACUOUS.
Until 2026-07-27 this section read

    def PoseidonPairCR : Prop := ∀ a b c d, poseidonPair a b = poseidonPair c d → a = c ∧ b = d

and called it "the named crypto floor … mirroring `EthLeaf.hashPairCR`". It is not that, in two
ways, and the second is fatal.

  * `EthLeaf.hashPairCR` (`Bridge/LightClientEth.lean:98-125`) is a `Prop` FIELD of an abstract
    structure over an OPAQUE `hashPair`, with `modelLeaf_hashPairCR` exhibiting a model that
    SATISFIES it and `collapseEthLeaf_not_hashPairCR` one that REFUTES it. Satisfiable, refutable,
    not provable — a floor. This file instead pinned the hash to the CONCRETE `Ref.hash` and
    asserted INJECTIVITY over all of `Nat`.
  * And so it is DISPROVABLE, in one line: `Ref.absorbAt` enters every input through
    `(state + x) % pN`, so `poseidonPair (l + pN) r = poseidonPair l r` while `l ≠ l + pN`
    (`poseidonPair_shift_collides` below, PROVED, no `decide` and no permutation evaluated).
    `PoseidonPairCR → False`. Its own doc-comment wrote "Poseidon is CR, not injective" and then
    defined injectivity on the next line.

Every theorem taking it as a hypothesis was therefore `False → anything`. That was the ENTIRE
claimed non-equivocation payoff of K6.

THE REPAIR follows the in-tree cutover doctrine for this class (`CircuitSoundness.NoLogSeamColl`,
the 2026-07-25 turn-log bundle cutover): the refuted ∀-injectivity is DELETED — not weakened, not
re-spelled — and each consumer takes a PER-INSTANCE non-equivocation side condition at exactly the
pairs the old proof fed the floor at, and no others. A theorem has argument positions; a global
injectivity claim does not. The result is strictly STRONGER than the pre-cutover statement (§3.4
derives the old conclusion from the old hypothesis in one step, so no capability is lost), it is
SATISFIABLE with an exhibited model (§3.3), it is REFUTABLE so it is not an empty ask (§3.5), and
it is REACHABLE at the deployed hash (§3.5) — which is what makes it a side condition a verifier
must actually discharge rather than a decoration. -/

/-- **A genuine EQUIVOCATION of the node hash** — two DISTINCT input pairs with the SAME digest.
Carries its own distinctness, so `¬ PairColl` is never satisfied vacuously by an equal pair. -/
def PairColl (hp : Nat → Nat → Nat) (a b c d : Nat) : Prop :=
  ¬ (a = c ∧ b = d) ∧ hp a b = hp c d

/-- The ordered list of node-hash INPUT pairs one fold visits, bottom-up — precisely the arguments
`merkleFold` presents to `hp`, level by level. -/
def foldPairs (hp : Nat → Nat → Nat) : Nat → List Nat → Nat → List (Nat × Nat)
  | _, [], _ => []
  | leaf, sib :: rest, idx =>
      (if idx % 2 = 1 then (sib, leaf) else (leaf, sib))
        :: foldPairs hp (if idx % 2 = 1 then hp sib leaf else hp leaf sib) rest (idx / 2)

/-- **`NoFoldColl`** — the PER-INSTANCE side condition that replaced the refuted `PoseidonPairCR`.
At EVERY level of the two folds, the node inputs the two paths present are not an equivocation.
`List.Forall₂` walks the two `foldPairs` lists in lockstep, so the condition is stated at exactly
the levels the induction consumes and carries the equal-length requirement itself. -/
def NoFoldColl (hp : Nat → Nat → Nat) (l₁ : Nat) (b₁ : List Nat) (l₂ : Nat) (b₂ : List Nat)
    (idx : Nat) : Prop :=
  List.Forall₂ (fun x y => ¬ PairColl hp x.1 x.2 y.1 y.2)
    (foldPairs hp l₁ b₁ idx) (foldPairs hp l₂ b₂ idx)

/-- **Merkle reconstruction is BINDING at the per-instance side condition**: two same-length
branches at the same index folding to the SAME root carry the SAME leaf, PROVIDED the two paths do
not equivocate the node hash at any level. A forger cannot open one ledger root to two different
account leaves at a slot without exhibiting a Poseidon collision at a specific level — which is
what the side condition denies, at that level, and nowhere else. -/
theorem merkleFold_binding_of_noColl (hp : Nat → Nat → Nat) :
    ∀ (b₁ b₂ : List Nat) (idx : Nat) (l₁ l₂ : Nat),
      NoFoldColl hp l₁ b₁ l₂ b₂ idx →
      merkleFold hp l₁ b₁ idx = merkleFold hp l₂ b₂ idx → l₁ = l₂ := by
  intro b₁
  induction b₁ with
  | nil =>
    intro b₂ idx l₁ l₂ hno h
    cases b₂ with
    | nil => simpa [merkleFold] using h
    | cons _ _ => simp [NoFoldColl, foldPairs] at hno
  | cons n₁ rest₁ ih =>
    intro b₂ idx l₁ l₂ hno h
    cases b₂ with
    | nil => simp [NoFoldColl, foldPairs] at hno
    | cons n₂ rest₂ =>
      simp only [merkleFold] at h
      rw [NoFoldColl, foldPairs, foldPairs] at hno
      cases hno with
      | cons hhead htail =>
        have hstep := ih rest₂ (idx / 2) _ _ htail h
        by_cases hb : idx % 2 = 1
        · rw [if_pos hb, if_pos hb] at hstep
          rw [if_pos hb, if_pos hb] at hhead
          exact (not_not.mp (fun hne => hhead ⟨hne, hstep⟩)).2
        · rw [if_neg hb, if_neg hb] at hstep
          rw [if_neg hb, if_neg hb] at hhead
          exact (not_not.mp (fun hne => hhead ⟨hne, hstep⟩)).1

/-! ### §3.1 — THE REFUTATION: the deleted floor was FALSE, and here is the collision as data.

Proved by ARITHMETIC ON THE ABSORB STATE — no permutation is evaluated, no `decide` runs 55 rounds.
That is the point: the collision is structural, not a lucky birthday. -/

/-- Absorbing `x + pN` IS absorbing `x`: the sponge enters every input through `(state + x) % pN`
(`PastaPoseidon.Ref.absorbAt`), so the input is only ever seen modulo the field. -/
theorem absorbAt_add_pN (st : List Nat) (j x : Nat) :
    Ref.absorbAt st j (x + pN) = Ref.absorbAt st j x := by
  simp [Ref.absorbAt, ← Nat.add_assoc, Nat.add_mod_right]

/-- One absorb step at lane 0 (definitional: the loop starts at `Absorbed 0` and `0 ≠ rate`). -/
theorem absorbFrom_cons_zero (st : List Nat) (x : Nat) (xs : List Nat) :
    Ref.absorbFrom st 0 (x :: xs) = Ref.absorbFrom (Ref.absorbAt st 0 x) 1 xs := rfl

/-- Shifting the FIRST absorbed input by `pN` leaves the hash unchanged — at ANY input length. -/
theorem hash_cons_add_pN (x : Nat) (xs : List Nat) :
    Ref.hash ((x + pN) :: xs) = Ref.hash (x :: xs) := by
  simp only [Ref.hash, Ref.absorbAll, absorbFrom_cons_zero, absorbAt_add_pN]

/-- ⚑ **THE DELETED `PoseidonPairCR` WAS FALSE.** It asserted
`poseidonPair a b = poseidonPair c d → a = c ∧ b = d`. Here is a refuting family, for EVERY `l r`:
the node hash cannot distinguish `l` from `l + pN`. -/
theorem poseidonPair_shift_collides (l r : Nat) :
    poseidonPair (l + pN) r = poseidonPair l r ∧ l + pN ≠ l := by
  refine ⟨hash_cons_add_pN l [r], ?_⟩
  have hp : pN ≠ 0 := by decide
  omega

/-! (The matching refutations of the deleted `AccountLeafCR` and `ZkappStateCR` are
`leafHash_shift_collides` (§4) and `zkappStateCR_refuted` (§5) — they are stated where their hash
is defined. All three are the SAME defect: `absorbAt` reduces every input mod `pN`.) -/

/-! ### §3.2 — NO STRENGTH LOST, and it is the same lemma that shows the condition is
non-degenerate. A hash with no collisions AT ALL gives the per-instance condition between
ARBITRARY folds — so (a) whatever the deleted floor would have bought, the side condition buys,
by one application; and (b) the condition is satisfiable between folds that genuinely DIFFER, not
only in the identical-fold case that makes the conclusion free. -/

theorem noFoldColl_of_no_collision (hp : Nat → Nat → Nat)
    (hno : ∀ a b c d : Nat, hp a b = hp c d → a = c ∧ b = d) :
    ∀ (b₁ b₂ : List Nat) (l₁ l₂ idx : Nat), b₁.length = b₂.length →
      NoFoldColl hp l₁ b₁ l₂ b₂ idx := by
  intro b₁
  induction b₁ with
  | nil =>
    intro b₂ l₁ l₂ idx hlen
    cases b₂ with
    | nil => exact List.Forall₂.nil
    | cons _ _ => simp at hlen
  | cons s₁ r₁ ih =>
    intro b₂ l₁ l₂ idx hlen
    cases b₂ with
    | nil => simp at hlen
    | cons s₂ r₂ =>
      rw [NoFoldColl, foldPairs, foldPairs]
      refine List.Forall₂.cons ?_ (ih r₂ _ _ (idx / 2) (by simpa using hlen))
      rintro ⟨hne, heq⟩
      exact hne (hno _ _ _ _ heq)

/-- ⚑ **THE RECOVERY, as an `example` and deliberately unnamed.** The pre-cutover conclusion
follows from the pre-cutover hypothesis in ONE step, so the cutover is strictly STRENGTHENING.
It is an `example` because any NAMED declaration of this type would be a fresh carrier of the very
injectivity this section refutes — the `TurnDecodeChainLogBundleCutoverCheck` §4 discipline. -/
example (cr : ∀ a b c d : Nat, poseidonPair a b = poseidonPair c d → a = c ∧ b = d)
    (b₁ b₂ : List Nat) (idx l₁ l₂ : Nat) (hlen : b₁.length = b₂.length)
    (h : merkleFold poseidonPair l₁ b₁ idx = merkleFold poseidonPair l₂ b₂ idx) : l₁ = l₂ :=
  merkleFold_binding_of_noColl poseidonPair b₁ b₂ idx l₁ l₂
    (noFoldColl_of_no_collision poseidonPair cr b₁ b₂ l₁ l₂ idx hlen) h

/-! ### §3.3 — SATISFIABILITY: an EXHIBITED model, at the DEPLOYED hash, with no hypothesis. -/

/-- **THE HONEST PROVER'S MODEL.** One leaf, one branch, one index: the two folds present
IDENTICAL node inputs at every level, so no level is an equivocation. Holds for EVERY `hp` —
including the deployed `poseidonPair`, whose collisions §3.1 exhibits — with NO hypothesis at all.
The prover who is not equivocating discharges the side condition totally and for free. -/
theorem noFoldColl_self (hp : Nat → Nat → Nat) (l : Nat) (b : List Nat) (idx : Nat) :
    NoFoldColl hp l b l b idx := by
  rw [NoFoldColl]
  induction b generalizing l idx with
  | nil => exact List.Forall₂.nil
  | cons s r ih =>
    rw [foldPairs]
    refine List.Forall₂.cons ?_ (ih _ _)
    rintro ⟨hne, -⟩
    exact hne ⟨rfl, rfl⟩

/-! ### §3.4 — THE CONDITION IS LOAD-BEARING (drop it and the theorem is FALSE), and it is a REAL
ask at the deployed hash (its negation is reachable there). Both legs, not one. -/

/-- **Drop the side condition and the theorem is FALSE.** At a collapsing node hash two distinct
leaves fold to one root — so `merkleFold_binding_of_noColl` is not true for free. -/
theorem merkleFold_binding_unconditional_false :
    ¬ (∀ (hp : Nat → Nat → Nat) (b₁ b₂ : List Nat) (idx l₁ l₂ : Nat),
        b₁.length = b₂.length →
        merkleFold hp l₁ b₁ idx = merkleFold hp l₂ b₂ idx → l₁ = l₂) := by
  intro h
  exact absurd (h (fun _ _ => 0) [0] [0] 0 1 2 rfl rfl) (by decide)

/-- ⚑ **AND THE ASK IS REAL AT THE DEPLOYED HASH.** `PairColl poseidonPair` is INHABITED, so
`NoFoldColl poseidonPair` is not true-for-free: a verifier that wants the binding must genuinely
rule the equivocation out at the levels it uses. This is what an honest floor looks like against a
CONCRETE hash — not injectivity, which is false, but a per-instance denial whose subject matter
demonstrably exists. -/
theorem pairColl_poseidonPair_reachable (r : Nat) : PairColl poseidonPair pN r 0 r := by
  refine ⟨?_, ?_⟩
  · have hp : pN ≠ 0 := by decide
    rintro ⟨h, -⟩; exact hp h
  · simpa only [Nat.zero_add] using (poseidonPair_shift_collides 0 r).1

/-! ## §4 — The account leaf COMMITS the queried field.

Mina account, canonical field order (`account.ml:222`, queryable prefix). `leafHash` is the
Poseidon hash of the fields (the leaf-commitment structure; the exact `Account.crypto_hash`
prefix+packing is residual #2). `LeafColl` is the PER-INSTANCE equivocation predicate that
replaced the refuted `AccountLeafCR` floor (§3). The commitments are
positional projections of the field list under CR (mirrors `htrExec_commits_stateRoot`). -/

/-- A Mina account (the queryable prefix of `account.ml:222`'s `Poly.t`, in that order; `timing`/
`permissions` folded away, the optional `zkapp` represented by its committed digest `zkappRoot`). -/
structure Account where
  publicKey : Nat
  tokenId : Nat
  tokenSymbol : Nat
  balance : Nat
  nonce : Nat
  receiptChainHash : Nat
  delegate : Nat
  votingFor : Nat
  /-- `Zkapp_account.digest` — commits the zkApp app-state (see §5); `0` for a non-zkApp account. -/
  zkappRoot : Nat

/-- The account fields as Poseidon leaf inputs, in Mina's canonical order (`account.ml:222`). -/
def accountFields (a : Account) : List Nat :=
  [a.publicKey, a.tokenId, a.tokenSymbol, a.balance, a.nonce, a.receiptChainHash,
    a.delegate, a.votingFor, a.zkappRoot]

/-- **The account leaf hash** — Poseidon over the account fields (the leaf a Merkle path folds
from). Models `Account.crypto_hash` (`account.ml:377`); the exact prefix+packing is residual #2. -/
def leafHash (a : Account) : Nat := Ref.hash (accountFields a)

/-- **`LeafColl a₁ a₂`** — a genuine EQUIVOCATION of the account leaf: two accounts with DIFFERENT
field lists and the SAME leaf hash. The PER-INSTANCE replacement for the deleted `AccountLeafCR`
(which asserted `leafHash a₁ = leafHash a₂ → accountFields a₁ = accountFields a₂` for ALL accounts,
and is refuted by `leafHash_shift_collides`). Carries its own distinctness, so `¬ LeafColl` is
never satisfied vacuously by an equal pair. -/
def LeafColl (a₁ a₂ : Account) : Prop :=
  accountFields a₁ ≠ accountFields a₂ ∧ leafHash a₁ = leafHash a₂

/-- ⚑ **THE DELETED `AccountLeafCR` WAS FALSE**: bump `publicKey` (leaf input 0) by `pN`. The two
accounts have DIFFERENT field lists and the SAME leaf hash — so `AccountLeafCR → False`, and every
theorem that took it was `False → anything`. -/
theorem leafHash_shift_collides (a : Account) :
    leafHash { a with publicKey := a.publicKey + pN } = leafHash a
      ∧ accountFields { a with publicKey := a.publicKey + pN } ≠ accountFields a := by
  constructor
  · simpa only [leafHash, accountFields] using hash_cons_add_pN a.publicKey _
  · intro h
    have h0 := congrArg (fun l => List.getD l 0 0) h
    simp only [accountFields, List.getD_cons_zero] at h0
    have hp : pN ≠ 0 := by decide
    omega

/-- **SATISFIABILITY, exhibited**: the honest prover's model — one account does not equivocate
against itself. No hypothesis, at the deployed `leafHash`. -/
theorem noLeafColl_self (a : Account) : ¬ LeafColl a a := by
  rintro ⟨hne, -⟩; exact hne rfl

/-- **NO STRENGTH LOST** — and the non-degenerate direction: a leaf hash with no collisions gives
the per-instance denial at every pair, so whatever the deleted floor bought, `¬ LeafColl` buys. -/
theorem noLeafColl_of_forall
    (h : ∀ a₁ a₂ : Account, leafHash a₁ = leafHash a₂ → accountFields a₁ = accountFields a₂)
    (a₁ a₂ : Account) : ¬ LeafColl a₁ a₂ := by
  rintro ⟨hne, heq⟩; exact hne (h a₁ a₂ heq)

/-- Field lists agree ⟹ balance (index 3) agrees. -/
theorem accountFields_commits_balance (a₁ a₂ : Account)
    (h : accountFields a₁ = accountFields a₂) : a₁.balance = a₂.balance := by
  have := congrArg (fun l => l.getD 3 0) h; simpa [accountFields] using this

/-- Field lists agree ⟹ nonce (index 4) agrees. -/
theorem accountFields_commits_nonce (a₁ a₂ : Account)
    (h : accountFields a₁ = accountFields a₂) : a₁.nonce = a₂.nonce := by
  have := congrArg (fun l => l.getD 4 0) h; simpa [accountFields] using this

/-- Field lists agree ⟹ zkappRoot (index 8) agrees. -/
theorem accountFields_commits_zkappRoot (a₁ a₂ : Account)
    (h : accountFields a₁ = accountFields a₂) : a₁.zkappRoot = a₂.zkappRoot := by
  have := congrArg (fun l => l.getD 8 0) h; simpa [accountFields] using this

/-- The per-instance denial, unpacked: equal leaves that are not an equivocation pin equal fields. -/
theorem accountFields_of_noLeafColl (a₁ a₂ : Account) (hno : ¬ LeafColl a₁ a₂)
    (h : leafHash a₁ = leafHash a₂) : accountFields a₁ = accountFields a₂ :=
  not_not.mp (fun hne => hno ⟨hne, h⟩)

/-- **The leaf COMMITS the balance**, at the per-instance denial (mirrors
`htrExec_commits_stateRoot`). -/
theorem leafHash_commits_balance (a₁ a₂ : Account) (hno : ¬ LeafColl a₁ a₂)
    (h : leafHash a₁ = leafHash a₂) : a₁.balance = a₂.balance :=
  accountFields_commits_balance a₁ a₂ (accountFields_of_noLeafColl a₁ a₂ hno h)

/-- **The leaf COMMITS the nonce**, at the per-instance denial. -/
theorem leafHash_commits_nonce (a₁ a₂ : Account) (hno : ¬ LeafColl a₁ a₂)
    (h : leafHash a₁ = leafHash a₂) : a₁.nonce = a₂.nonce :=
  accountFields_commits_nonce a₁ a₂ (accountFields_of_noLeafColl a₁ a₂ hno h)

/-- **The leaf COMMITS the zkApp digest `zkappRoot`**, at the per-instance denial. -/
theorem leafHash_commits_zkappRoot (a₁ a₂ : Account) (hno : ¬ LeafColl a₁ a₂)
    (h : leafHash a₁ = leafHash a₂) : a₁.zkappRoot = a₂.zkappRoot :=
  accountFields_commits_zkappRoot a₁ a₂ (accountFields_of_noLeafColl a₁ a₂ hno h)

/-! ## §5 — The zkApp app-state layer: `zkappRoot` commits an app-state field.

A zkApp's 8-field `app_state` is committed into `zkappRoot` by a Poseidon hash (simplifying
`Zkapp_account.digest`). A second per-instance denial (`¬ StateColl`, replacing the refuted
`ZkappStateCR`) commits an individual app-state field. Composing with
the leaf commitment gives a two-level Merkle-into-account-into-zkApp-state query. -/

/-- The zkApp app-state digest — Poseidon over the 8 app-state fields (models the app-state leg of
`Zkapp_account.digest`). -/
def zkappStateHash (appState : List Nat) : Nat := Ref.hash appState

/-- **`StateColl s₁ s₂`** — a genuine EQUIVOCATION of the app-state digest: two DISTINCT app-states
with the SAME digest. The PER-INSTANCE replacement for the deleted `ZkappStateCR`, which asserted
injectivity on all length-8 lists and is refuted INSIDE that restriction by
`zkappStateCR_refuted`. -/
def StateColl (s₁ s₂ : List Nat) : Prop := s₁ ≠ s₂ ∧ zkappStateHash s₁ = zkappStateHash s₂

/-- ⚑ **THE DELETED `ZkappStateCR` WAS FALSE**, and refuted INSIDE its own length-8 restriction:
two DISTINCT 8-field app-states with equal digests. -/
theorem zkappStateCR_refuted :
    ∃ s₁ s₂ : List Nat, s₁.length = 8 ∧ s₂.length = 8 ∧ s₁ ≠ s₂ ∧
      zkappStateHash s₁ = zkappStateHash s₂ := by
  refine ⟨pN :: [20, 30, 40, 50, 60, 70, 80], 0 :: [20, 30, 40, 50, 60, 70, 80], rfl, rfl, ?_, ?_⟩
  · intro h
    have h0 := congrArg (fun l => List.getD l 0 0) h
    simp only [List.getD_cons_zero] at h0
    exact absurd h0 (by decide)
  · simpa only [zkappStateHash, Nat.zero_add] using hash_cons_add_pN 0 [20, 30, 40, 50, 60, 70, 80]

/-- **SATISFIABILITY, exhibited**: the honest prover's model, at the deployed digest. -/
theorem noStateColl_self (s : List Nat) : ¬ StateColl s s := by
  rintro ⟨hne, -⟩; exact hne rfl

/-- **NO STRENGTH LOST**: the deleted floor implies the per-instance denial at every pair. -/
theorem noStateColl_of_forall
    (h : ∀ s₁ s₂ : List Nat, s₁.length = 8 → s₂.length = 8 →
      zkappStateHash s₁ = zkappStateHash s₂ → s₁ = s₂)
    (s₁ s₂ : List Nat) (h₁ : s₁.length = 8) (h₂ : s₂.length = 8) : ¬ StateColl s₁ s₂ := by
  rintro ⟨hne, heq⟩; exact hne (h s₁ s₂ h₁ h₂ heq)

/-! ## §6 — THE QUERY DECISION (positive discharge + non-equivocation payoff). -/

/-- The account-query verdict: the Merkle-path witness folds `leaf` to the trusted `root`. A
satisfying witness is EXHIBITED (no trusted bit) — the boolean is DERIVED from the fold. -/
def verifyAccountQuery (leaf : Nat) (branch : List Nat) (idx root : Nat) : Bool :=
  decide (merkleFold poseidonPair leaf branch idx = root)

/-- **The query boolean is DISCHARGED by the exhibited fold** — a prover must EXHIBIT a branch whose
Poseidon fold hits the verified root; there is no witnessed accept-bit to set (analogue of
`verifyExecutionPayload_from_fold`). -/
theorem verifyAccountQuery_from_fold (leaf : Nat) (branch : List Nat) (idx root : Nat)
    (hfold : merkleFold poseidonPair leaf branch idx = root) :
    verifyAccountQuery leaf branch idx root = true := by
  simp [verifyAccountQuery, hfold]

/-- **NON-EQUIVOCATION — the queried BALANCE is UNIQUELY bound under the root.** Two accounts whose
same-length Merkle paths at the same slot both fold to the SAME ledger root carry the SAME balance:
no forger opens one root to two different balances at a slot. Composition:
`merkleFold_binding_of_noColl` (leaves equal) ∘ `leafHash_commits_balance` (field committed), each
at its PER-INSTANCE non-equivocation condition — ⚑ NOT at the injectivity floors this theorem used
to take, which were false and made it vacuous (§3). This is the on-chain payoff — the state-query
is BINDING, conditional on the two named non-equivocations and on nothing that is provably false.
(Analogue of `exec_fold_binds_finStateRoot`.) -/
theorem query_binds_balance
    (a₁ a₂ : Account) (b₁ b₂ : List Nat) (idx root : Nat)
    (hnode : NoFoldColl poseidonPair (leafHash a₁) b₁ (leafHash a₂) b₂ idx)
    (hleaf : ¬ LeafColl a₁ a₂)
    (hf₁ : merkleFold poseidonPair (leafHash a₁) b₁ idx = root)
    (hf₂ : merkleFold poseidonPair (leafHash a₂) b₂ idx = root) :
    a₁.balance = a₂.balance :=
  leafHash_commits_balance a₁ a₂ hleaf
    (merkleFold_binding_of_noColl poseidonPair b₁ b₂ idx _ _ hnode (hf₁.trans hf₂.symm))

/-- **NON-EQUIVOCATION — the queried NONCE is UNIQUELY bound under the root.** -/
theorem query_binds_nonce
    (a₁ a₂ : Account) (b₁ b₂ : List Nat) (idx root : Nat)
    (hnode : NoFoldColl poseidonPair (leafHash a₁) b₁ (leafHash a₂) b₂ idx)
    (hleaf : ¬ LeafColl a₁ a₂)
    (hf₁ : merkleFold poseidonPair (leafHash a₁) b₁ idx = root)
    (hf₂ : merkleFold poseidonPair (leafHash a₂) b₂ idx = root) :
    a₁.nonce = a₂.nonce :=
  leafHash_commits_nonce a₁ a₂ hleaf
    (merkleFold_binding_of_noColl poseidonPair b₁ b₂ idx _ _ hnode (hf₁.trans hf₂.symm))

/-- **NON-EQUIVOCATION — a queried zkApp APP-STATE FIELD is UNIQUELY bound under the root.** Two
accounts whose paths fold to the same root, whose `zkappRoot`s commit 8-field app-states `s₁`/`s₂`,
carry the SAME value at every app-state index `i`. Three-floor composition: node CR (leaves) ∘ leaf
CR (`zkappRoot`) ∘ zkApp-state CR (the field). This is the "zkApp state field" query. -/
theorem query_binds_zkappField
    (a₁ a₂ : Account) (s₁ s₂ : List Nat) (i : Nat)
    (hz₁ : a₁.zkappRoot = zkappStateHash s₁) (hz₂ : a₂.zkappRoot = zkappStateHash s₂)
    (b₁ b₂ : List Nat) (idx root : Nat)
    (hnode : NoFoldColl poseidonPair (leafHash a₁) b₁ (leafHash a₂) b₂ idx)
    (hleafNo : ¬ LeafColl a₁ a₂) (hstateNo : ¬ StateColl s₁ s₂)
    (hf₁ : merkleFold poseidonPair (leafHash a₁) b₁ idx = root)
    (hf₂ : merkleFold poseidonPair (leafHash a₂) b₂ idx = root) :
    s₁.getD i 0 = s₂.getD i 0 := by
  have hleaf : leafHash a₁ = leafHash a₂ :=
    merkleFold_binding_of_noColl poseidonPair b₁ b₂ idx _ _ hnode (hf₁.trans hf₂.symm)
  have hzr : a₁.zkappRoot = a₂.zkappRoot := leafHash_commits_zkappRoot a₁ a₂ hleafNo hleaf
  have hst : zkappStateHash s₁ = zkappStateHash s₂ := by rw [← hz₁, ← hz₂, hzr]
  rw [not_not.mp (fun hne => hstateNo ⟨hne, hst⟩)]

/-! ## §7 — Composition with K5: verify-root (K5) → query-under-root (K6).

⚑ **`mina_verify_then_query` IS DELETED (2026-07-27), AND THE CAPABILITY LOST IS ZERO.** It read

    theorem mina_verify_then_query (nodeCR : PoseidonPairCR) (leafCR : AccountLeafCR)
        (LedgerRootAttested : Nat → Prop) (root : Nat) (hverified : LedgerRootAttested root) … :
        LedgerRootAttested root ∧ ∀ a' b', … → a'.balance = a.balance :=
      ⟨hverified, …⟩

and commit `38d64b233` presented it as "the K5 seam: (K5) attest-root ∘ (K6) query-under-root".
Neither conjunct carried the seam:

  * `LedgerRootAttested` is a UNIVERSALLY QUANTIFIED FREE PREDICATE and the first conjunct is
    returned as literally `hverified` — the caller's own hypothesis handed back. That half is
    `P → P`, for every `P`. A free predicate cannot compose with K5; it can only be instantiated
    at whatever the caller likes, including `fun _ => True`.
  * The second half was `query_binds_balance` applied, and therefore VACUOUS through the two
    refuted floors (§3).

So the theorem's entire content, once the tautology is removed, is `query_binds_balance` — which is
in §6, is now proved on the per-instance conditions, and is the statement a K5 caller should
invoke directly with `root` instantiated to the attested one. Re-adding an attestation parameter
would reintroduce an unused hypothesis, which is the same vacuity wearing a different name.

What K6 does NOT have, and this deletion makes visible rather than hiding behind a conjunction: a
CONNECTION to K5. `KimchiVerify`'s decision and this file's fold share no object in Lean — nothing
here derives `root` from a verified proof. That is the seam, it is OPEN, and it is residual #6. -/

/-! ## §8 — axiom hygiene. -/

#assert_axioms poseidonPair_eq_hash
#assert_axioms merkleFold_nil
#assert_axioms merkleFold_single_even
#assert_axioms merkleFold_single_odd
#assert_axioms merkleFold_congr
#assert_axioms merkleFold_binding_of_noColl
#assert_axioms accountFields_commits_balance
#assert_axioms accountFields_commits_nonce
#assert_axioms accountFields_commits_zkappRoot
#assert_axioms accountFields_of_noLeafColl
#assert_axioms leafHash_commits_balance
#assert_axioms leafHash_commits_nonce
#assert_axioms leafHash_commits_zkappRoot
#assert_axioms verifyAccountQuery_from_fold
#assert_axioms query_binds_balance
#assert_axioms query_binds_nonce
#assert_axioms query_binds_zkappField

-- The refutations of the three deleted floors, and the three legs that make the replacements
-- honest (satisfiable / strength-preserving / load-bearing + reachable).
#assert_axioms absorbAt_add_pN
#assert_axioms hash_cons_add_pN
#assert_axioms poseidonPair_shift_collides
#assert_axioms leafHash_shift_collides
#assert_axioms zkappStateCR_refuted
#assert_axioms noFoldColl_of_no_collision
#assert_axioms noFoldColl_self
#assert_axioms merkleFold_binding_unconditional_false
#assert_axioms pairColl_poseidonPair_reachable
#assert_axioms noLeafColl_self
#assert_axioms noLeafColl_of_forall
#assert_axioms noStateColl_self
#assert_axioms noStateColl_of_forall

#print axioms query_binds_balance
#print axioms query_binds_zkappField
#print axioms poseidonPair_shift_collides

/-! ## §9 — KATs: real Poseidon-Merkle vectors, both polarity (kernel-reducible over the o1js-exact
`Ref.hash`); a tampered sibling / balance / nonce / app-state field FLIPS the value (the query is
non-vacuous).

⚑ PROVENANCE, CORRECTED 2026-07-27. This paragraph used to say the root/leaf values were "computed
INDEPENDENTLY (a Python recomputation … that reproduces the o1js gold `Poseidon.hash` vectors K3 §5
pins)". That recomputation reproduced only the seven ODD-length vectors K3 pinned, because it
shared K3's even-length sponge defect — and `poseidonPair` (length 2) and `zkappStateHash`
(length 8) are BOTH the defective branch. So the KAT was circular: it confirmed the Lean against a
reimplementation of the same misreading, and two of the three numbers below were wrong.

The values here are now emitted by the PINNED `mina-poseidon` crate at rev `36a8b510` — the
upstream `ArithmeticSponge` itself, not a re-implementation of it — and independently reproduced by
a corrected Python reference. Both agree. `leafHash katAccount` is UNCHANGED (9 fields, an odd
length, which is why it was right all along); the Merkle root and the app-state digest MOVED. -/

/-- The KAT account: balance 5000, nonce 3 (fields `[111,1,0,5000,3,222,111,0,0]`). -/
def katAccount : Account := ⟨111, 1, 0, 5000, 3, 222, 111, 0, 0⟩
/-- The KAT zkApp app-state (8 fields). -/
def katAppState : List Nat := [10, 20, 30, 40, 50, 60, 70, 80]

-- The Merkle FOLD, depth 2 (leaf 7, siblings [11, 13], path idx 2): a real Poseidon-Merkle root.
-- ⚑ RE-DERIVED 2026-07-27. The value pinned here until then was
-- `21854892281928035201729884177122216581371284660515611400752318599290278209395`, which was the
-- output of the DOUBLE-PERMUTING sponge (K3 F1): `poseidonPair` IS the length-2 case, the exact
-- branch that was wrong. The "INDEPENDENT Python recomputation" this KAT was advertised as resting
-- on reproduced only the seven ODD-length K3 vectors, so it shared the bug and the pin was
-- circular. Below is the value the pinned `mina-poseidon` crate (rev `36a8b510`) emits.
#guard merkleFold poseidonPair 7 [11, 13] 2 ==
  17876594067382267673618811276889830204275361552710098244484066674450876785088
-- discrimination: a tampered sibling (13 → 99) FLIPS the reconstructed root.
#guard merkleFold poseidonPair 7 [11, 99] 2 !=
  17876594067382267673618811276889830204275361552710098244484066674450876785088
-- and it FLIPS to a value the crate agrees on, not merely to "something else".
#guard merkleFold poseidonPair 7 [11, 99] 2 ==
  28379189393635840065668947439190647246265260539673234272051124807677883901552
-- ⚑ A pin that FIRES if the double-permute ever returns: the old (wrong) root must NOT come back.
#guard merkleFold poseidonPair 7 [11, 13] 2 !=
  21854892281928035201729884177122216581371284660515611400752318599290278209395

-- ⚑ §10.1's o1js claim, now a KERNEL PIN instead of prose. `poseidonPair` IS the o1js `MerkleTree`
-- node hash, so a depth-2 root over leaves `[1,2,3,4]` must equal the probe's gold
-- (`main.rs:211`, `merkle_compress_matches_o1js_merkletree`). Before the K3 fix this was FALSE as
-- shipped — the claim named exactly the length the sponge got wrong.
#guard poseidonPair (poseidonPair 1 2) (poseidonPair 3 4) ==
  7015600548940256149412569585750804788713845761673517466748455515265959704439

-- The account LEAF hash (the fold's leaf): a real Poseidon hash of the 9 account fields.
#guard leafHash katAccount ==
  12121323423854282334593715199270902641335241266875461742331953283056607684178
-- discrimination: a different BALANCE FLIPS the leaf (the balance is committed).
#guard leafHash { katAccount with balance := 6000 } !=
  12121323423854282334593715199270902641335241266875461742331953283056607684178
-- discrimination: a different NONCE FLIPS the leaf (the nonce is committed).
#guard leafHash { katAccount with nonce := 4 } !=
  12121323423854282334593715199270902641335241266875461742331953283056607684178

-- The zkApp app-state digest: a real Poseidon hash of the 8 app-state fields.
-- ⚑ RE-DERIVED 2026-07-27, same cause: 8 fields is an EVEN length, so this was the broken branch
-- too. The value pinned until then was
-- `2877203160029291904480306281751044370917607895926420909241134854411259156922`.
#guard zkappStateHash katAppState ==
  7793532852580544308559766028812976281226577801406822679809933151814115881900
-- discrimination: a tampered app-state field (index 2, 30 → 31) FLIPS the digest.
#guard zkappStateHash (katAppState.set 2 31) !=
  7793532852580544308559766028812976281226577801406822679809933151814115881900
#guard zkappStateHash (katAppState.set 2 31) ==
  17573959357664042105050155716180654225398503296593826919656528956583585149380
-- ⚑ A pin that FIRES if the double-permute returns.
#guard zkappStateHash katAppState !=
  2877203160029291904480306281751044370917607895926420909241134854411259156922

-- Structural: the fold at the honest witness discharges the query boolean.
#guard verifyAccountQuery 7 [11, 13] 2
  17876594067382267673618811276889830204275361552710098244484066674450876785088 == true
-- and REJECTS the pre-fix root, which is now a wrong root like any other.
#guard verifyAccountQuery 7 [11, 13] 2
  21854892281928035201729884177122216581371284660515611400752318599290278209395 == false
-- Structural: a WRONG root fails the query (non-vacuous accept).
#guard verifyAccountQuery 7 [11, 13] 2 12345 == false
#guard (accountFields katAccount).length == 9

/-! ## §10 — The PRECISE named residuals (none `sorry`-ed).

  1. **The protocol account-ledger uses a PER-HEIGHT node prefix** `Hash_prefix.merkle_tree height`
     = `"MinaMklTree%03d"` (`ledger_hash.ml:8`, `hash_prefixes.ml:51`), NOT the plain
     `Poseidon(l,r)` baked here. `merkleFold`/`merkleFold_binding_of_noColl`/`merkleFold_congr` are
     hash-GENERIC (parameter `hp`), so a per-height `hp height l r` (its IV a Poseidon salt of the
     prefix string) drops straight in — dumping those IV field constants is the same mechanical
     step K3 did for the round constants. The plain node hash IS byte-exact for o1js application
     `MerkleTree`/`MerkleWitness`/`MerkleMap` — ⚑ and as of 2026-07-27 that is PINNED IN-KERNEL
     (§9, the depth-2 root over `[1,2,3,4]` against the probe's gold) rather than asserted as
     "probe-confirmed" prose. It was FALSE as shipped until the K3 even-length fix: those o1js
     structures hash `[left, right]`, which is exactly the length the sponge got wrong.
  2. **The exact `Account.crypto_hash` serialization is MODELED, not byte-verified** — the
     "MinaAccount" prefix (`hash_prefixes.ml:30`) and the `to_input`/`pack_input` bit-packing
     (balance/nonce/token co-packed into shared field elements) are not reproduced; `accountFields`
     captures the commitment STRUCTURE only. The commitment lemmas are packing-agnostic (they read
     positions out of the field list and never assume the encoding is injective), so this is a
     fidelity residual, not a soundness hole. Likewise `zkappRoot = zkappStateHash appState`
     simplifies the real `Zkapp_account.digest`.
  3. **⚑ THERE IS NO PER-NODE FORCING, AND NO AIR.** This file emits ZERO constraints — no
     `VmConstraint2`, no `Assignment`, no `acceptB`. `merkleFold_congr` (§2) is fold CONGRUENCE, not
     forcing; it would transport a per-node Poseidon forcing to the whole path IF one existed, and
     none does — `PastaPoseidon` §7 residual #3 (`absorbBlock_forces ∘ perm_forces ∘ squeeze`) is
     named there and discharged nowhere. Until it is, nothing here is in-circuit: this is a `Nat`
     model of the ledger's commitment structure, KAT-anchored to the real hash. The top-level query
     theorems take the reconstruction (`hfold`) as an explicit hypothesis, exactly as the ETH
     FIN/EXEC folds take theirs — what is DERIVED vs ASSUMED is visible.
  4. **⚑ THE CR FLOORS ARE GONE, BECAUSE ALL THREE WERE FALSE** (§3). `PoseidonPairCR`,
     `AccountLeafCR` and `ZkappStateCR` asserted INJECTIVITY of a concrete Poseidon over all of
     `Nat`; `absorbAt` reduces every input mod `pN`, so each is refuted by a one-line shift
     (`poseidonPair_shift_collides`, `leafHash_shift_collides`, `zkappStateCR_refuted` — the last
     inside its own length-8 restriction). Every payoff that took them was `False → anything`.
     They are replaced by PER-INSTANCE non-equivocation side conditions (`NoFoldColl`, `¬ LeafColl`,
     `¬ StateColl`) at exactly the pairs the old proofs fed the floors at. Each carries all three
     legs, not one: SATISFIABLE with an exhibited model at the deployed hash (`noFoldColl_self`,
     `noLeafColl_self`, `noStateColl_self` — the honest prover, no hypothesis), STRENGTH-PRESERVING
     (`noFoldColl_of_no_collision`, `noLeafColl_of_forall`, `noStateColl_of_forall` recover the old
     conclusions from the old hypotheses in one step), and LOAD-BEARING — drop the condition and
     the theorem is refuted (`merkleFold_binding_unconditional_false`), while its negation is
     REACHABLE at the deployed hash (`pairColl_poseidonPair_reachable`), so it is a real ask rather
     than a decoration. What is NOT here: any bound on how hard finding such a collision is. That
     is a genuine floor and it is not stated in this file; `Crypto.RomQueryFloor.birthday_bound`
     ((Q²+1)/‖R‖, PROVED, no assumption) is the in-tree shape for it, and connecting the deployed
     Poseidon to a random oracle is a MODELLING step — see `DomainSeparatedCREffRegrounded` §5,
     which says explicitly that taking it silently is laundering. Not taken here.
  5. **The shared K1/K3 field-width residual** — the `ℤ ↔ p_felt` gap (K1 §6) and the `z < p`
     canonical compare stand unchanged under this gadget (it composes over K3's forced sponge).
  6. **⚑ THE K5 SEAM IS OPEN** (§7). `mina_verify_then_query` claimed it and carried none of it:
     its first conjunct was `P → P` over a free predicate, its second was the vacuous
     `query_binds_balance`. It is DELETED. Nothing in this file derives a ledger root from a
     verified Kimchi proof; `KimchiVerify`'s decision and this fold share no object in Lean.

This is the Mina verifier's state-query layer as a COMMITMENT MODEL: the Poseidon Merkle-path fold
+ the account-leaf/zkApp-field commitment + the query decision, KAT-anchored to the real hash and
binding at explicit per-instance non-equivocation conditions. NOT claimed: a per-height
protocol-ledger prefix, byte-exact account serialization, an in-AIR per-node Poseidon composition,
a collision-hardness bound, or a composition with K5 (all named above).
-/

end Dregg2.Circuit.Emit.MinaStateQuery
