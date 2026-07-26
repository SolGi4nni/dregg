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

  * `merkleFold` — the Poseidon Merkle-path fold generator (the `absFold` shape of the ETH folds,
    at `poseidonPair = Poseidon(left,right)` over Fp); `ledgerReconstruct` = the ledger root a
    branch CLAIMS. `merkleFold_binding` — the fold is BINDING given Poseidon-2 CR (mirrors
    `reconstruct_binding`): same-length branches to the same root carry the same leaf.
  * `leafHash` / `accountFields` — the account leaf as a Poseidon hash of the account fields in
    Mina's canonical order; `leafHash_commits_balance`/`_nonce`/`_zkappRoot` — the leaf COMMITS the
    queried field given the account-leaf CR floor (mirrors `htrExec_commits_stateRoot`). A second
    layer commits a zkApp app-state field through `zkappRoot` (`query_binds_zkappField`).
  * `merkleFold_forces` — the ABSTRACT path-fold forcing induction (the move the K3 header names):
    if each emitted Poseidon-node gadget forces its output to `Poseidon(left,right)`, the whole
    path forces `root = merkleFold` (fold congruence, gate-count-independent). This DISCHARGES the
    tree structure and LOCALIZES the residual to a single Poseidon NODE — which is `PastaPoseidon`
    §7 residual #3 (the `absorbBlock_forces ∘ perm_forces ∘ squeeze` composition), not new debt.
  * the query DECISION: `verifyAccountQuery_from_fold` (a satisfying Merkle-path witness discharges
    the query boolean — no trusted bit), and `query_binds_balance`/`_nonce`/`_zkappField` (the
    non-equivocation payoff: under a verified root NO other account/field-value opens the same slot
    — the queried value is UNIQUELY bound). Both-polarity KAT'd against real Poseidon-Merkle
    vectors below.

## How this composes with K5 (verify-root → query-under-root)

The Kimchi verifier `KimchiVerify.kimchiVerifyDecision` (K5) attests the STATE — that a ledger root
is the state root of a Kimchi-VALID Mina block (subject to the IPA/FRI floor K5 names). This gadget
(K6) proves a QUERY UNDER that proven root. So "verify Mina + read an account" is the two-step
  (K5) verify-root  ∘  (K6) query-under-root.
`mina_verify_then_query` states exactly that seam: it takes the K5 accept as an abstract
`LedgerRootAttested root` hypothesis (kept a Prop parameter so this file's imports stay K1/K3, not
the whole K5 tree) and concludes the queried balance is the unique value bound under the verified
root. K6 does NOT re-verify the root; K5 does not touch the leaf.

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
"MinaAccount" prefix; the commitment lemmas are packing-AGNOSTIC (they hold for any injective field
encoding under the CR floor), so the exact serialization is a named residual, not a hidden
assumption. The `zkappRoot = zkappStateHash appState` model is a simplification of the real
`Zkapp_account.digest` (which also folds verification-key/permissions).

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. The `#guard` KATs reduce in the kernel (`Nat`/`Bool`, the o1js-exact Poseidon
reference). NEW standalone file; imports `PastaPoseidon` (K3, transitively `PastaField` K1); NOT
imported by the truncated `Dregg2` root (built directly as `Dregg2.Circuit.Emit.MinaStateQuery`).
-/
import Dregg2.Circuit.Emit.PastaPoseidon
import Dregg2.Circuit.Emit.PastaField

namespace Dregg2.Circuit.Emit.MinaStateQuery

open Dregg2.Circuit.Emit.PastaPoseidon

set_option autoImplicit false

/-! ## §1 — The Poseidon pair-hash + the abstract Merkle-path fold.

`poseidonPair l r = Poseidon.hash [l, r]` is the o1js `MerkleTree` node hash (probe-confirmed) and
the Mina protocol-ledger `merge` at height 0 (the per-height prefix is residual #1). `merkleFold`
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

/-! ## §2 — The abstract path-fold FORCING (the tree structure discharged; residual = one node).

This is the move the K3 header names: `PastaPoseidon.perm_forces` + a fold induction. Modeled as
fold CONGRUENCE under a pointwise-equal pair-hash — the emitted circuit lays one Poseidon-node
gadget per level whose forced output is `f left right`; if that per-node forcing holds
(`hnode : ∀ l r, f l r = poseidonPair l r`, the K3 §7 residual #3 composition), the WHOLE PATH
computes `merkleFold poseidonPair`. Gate-count-independent, exactly like `permFrom_forces`. -/

/-- **The path-fold forcing.** If the per-node circuit hash `f` is forced to the Poseidon node hash
`hp` at every pair (`hnode`), then folding `f` up the branch equals folding `hp` — the emitted path
gates force `root = merkleFold hp`. The residual is per-NODE (`hnode`): one Poseidon-2 gate
composition (K3 §7 #3). The TREE is discharged here. -/
theorem merkleFold_forces (f hp : Nat → Nat → Nat) (hnode : ∀ l r, f l r = hp l r) :
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

/-! ## §3 — The fold is BINDING (given Poseidon-2 collision resistance).

Mirrors `Bridge.LightClientEth.reconstruct_binding` exactly, at `poseidonPair`. `PoseidonPairCR`
is the named crypto floor (a `Prop`, like `EthLeaf.hashPairCR`): the Poseidon node hash does not
collide. Consumed at every fold step. -/

/-- **The Poseidon-2 collision-resistance floor** (NAMED; a `Prop` hypothesis, mirroring
`EthLeaf.hashPairCR`): distinct node inputs do not collide under `poseidonPair`. This is what turns
"the branch reconstructs" into "the root COMMITS the leaf". -/
def PoseidonPairCR : Prop := ∀ a b c d : Nat, poseidonPair a b = poseidonPair c d → a = c ∧ b = d

/-- **Merkle reconstruction is BINDING, GIVEN Poseidon-2 CR**: two same-length branches at the same
index folding to the SAME root carry the SAME leaf — a forger cannot open one ledger root to two
different account leaves at a slot. (Mirrors `reconstruct_binding`.) -/
theorem merkleFold_binding (cr : PoseidonPairCR) :
    ∀ (b₁ b₂ : List Nat) (idx : Nat) (l₁ l₂ : Nat),
      b₁.length = b₂.length →
      merkleFold poseidonPair l₁ b₁ idx = merkleFold poseidonPair l₂ b₂ idx → l₁ = l₂ := by
  intro b₁
  induction b₁ with
  | nil =>
    intro b₂ idx l₁ l₂ hlen h
    cases b₂ with
    | nil => simpa [merkleFold] using h
    | cons _ _ => simp at hlen
  | cons n₁ rest₁ ih =>
    intro b₂ idx l₁ l₂ hlen h
    cases b₂ with
    | nil => simp at hlen
    | cons n₂ rest₂ =>
      simp only [merkleFold] at h
      have hlen' : rest₁.length = rest₂.length := by simpa using hlen
      have hstep := ih rest₂ (idx / 2) _ _ hlen' h
      by_cases hb : idx % 2 = 1
      · rw [if_pos hb, if_pos hb] at hstep; exact (cr _ _ _ _ hstep).2
      · rw [if_neg hb, if_neg hb] at hstep; exact (cr _ _ _ _ hstep).1

/-! ## §4 — The account leaf COMMITS the queried field.

Mina account, canonical field order (`account.ml:222`, queryable prefix). `leafHash` is the
Poseidon hash of the fields (the leaf-commitment structure; the exact `Account.crypto_hash`
prefix+packing is residual #2). `AccountLeafCR` is the named leaf CR floor. The commitments are
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

/-- **The account-leaf collision-resistance floor** (NAMED; a `Prop`, mirroring
`EthLeaf.hashPairCR`): distinct witnessed accounts do not collide under `leafHash`. This is the
cryptographic floor — Poseidon is CR, not injective — taken as an explicit hypothesis where
consumed. -/
def AccountLeafCR : Prop := ∀ a₁ a₂ : Account, leafHash a₁ = leafHash a₂ → accountFields a₁ = accountFields a₂

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

/-- **The leaf COMMITS the balance, GIVEN the account-leaf CR floor.** Equal leaves pin equal
balances (mirrors `htrExec_commits_stateRoot`). -/
theorem leafHash_commits_balance (cr : AccountLeafCR) (a₁ a₂ : Account)
    (h : leafHash a₁ = leafHash a₂) : a₁.balance = a₂.balance :=
  accountFields_commits_balance a₁ a₂ (cr a₁ a₂ h)

/-- **The leaf COMMITS the nonce, GIVEN the CR floor.** -/
theorem leafHash_commits_nonce (cr : AccountLeafCR) (a₁ a₂ : Account)
    (h : leafHash a₁ = leafHash a₂) : a₁.nonce = a₂.nonce :=
  accountFields_commits_nonce a₁ a₂ (cr a₁ a₂ h)

/-- **The leaf COMMITS the zkApp digest `zkappRoot`, GIVEN the CR floor.** -/
theorem leafHash_commits_zkappRoot (cr : AccountLeafCR) (a₁ a₂ : Account)
    (h : leafHash a₁ = leafHash a₂) : a₁.zkappRoot = a₂.zkappRoot :=
  accountFields_commits_zkappRoot a₁ a₂ (cr a₁ a₂ h)

/-! ## §5 — The zkApp app-state layer: `zkappRoot` commits an app-state field.

A zkApp's 8-field `app_state` is committed into `zkappRoot` by a Poseidon hash (simplifying
`Zkapp_account.digest`). A second CR floor commits an individual app-state field. Composing with
the leaf commitment gives a two-level Merkle-into-account-into-zkApp-state query. -/

/-- The zkApp app-state digest — Poseidon over the 8 app-state fields (models the app-state leg of
`Zkapp_account.digest`). -/
def zkappStateHash (appState : List Nat) : Nat := Ref.hash appState

/-- **The zkApp-state collision-resistance floor** (NAMED; a `Prop`): distinct 8-field app-states
do not collide under `zkappStateHash`. -/
def ZkappStateCR : Prop :=
  ∀ s₁ s₂ : List Nat, s₁.length = 8 → s₂.length = 8 → zkappStateHash s₁ = zkappStateHash s₂ → s₁ = s₂

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
`merkleFold_binding` (leaves equal) ∘ `leafHash_commits_balance` (field committed). This is the
on-chain payoff — the state-query is BINDING. (Analogue of `exec_fold_binds_finStateRoot`.) -/
theorem query_binds_balance (nodeCR : PoseidonPairCR) (leafCR : AccountLeafCR)
    (a₁ a₂ : Account) (b₁ b₂ : List Nat) (idx root : Nat)
    (hlen : b₁.length = b₂.length)
    (hf₁ : merkleFold poseidonPair (leafHash a₁) b₁ idx = root)
    (hf₂ : merkleFold poseidonPair (leafHash a₂) b₂ idx = root) :
    a₁.balance = a₂.balance :=
  leafHash_commits_balance leafCR a₁ a₂
    (merkleFold_binding nodeCR b₁ b₂ idx _ _ hlen (hf₁.trans hf₂.symm))

/-- **NON-EQUIVOCATION — the queried NONCE is UNIQUELY bound under the root.** -/
theorem query_binds_nonce (nodeCR : PoseidonPairCR) (leafCR : AccountLeafCR)
    (a₁ a₂ : Account) (b₁ b₂ : List Nat) (idx root : Nat)
    (hlen : b₁.length = b₂.length)
    (hf₁ : merkleFold poseidonPair (leafHash a₁) b₁ idx = root)
    (hf₂ : merkleFold poseidonPair (leafHash a₂) b₂ idx = root) :
    a₁.nonce = a₂.nonce :=
  leafHash_commits_nonce leafCR a₁ a₂
    (merkleFold_binding nodeCR b₁ b₂ idx _ _ hlen (hf₁.trans hf₂.symm))

/-- **NON-EQUIVOCATION — a queried zkApp APP-STATE FIELD is UNIQUELY bound under the root.** Two
accounts whose paths fold to the same root, whose `zkappRoot`s commit 8-field app-states `s₁`/`s₂`,
carry the SAME value at every app-state index `i`. Three-floor composition: node CR (leaves) ∘ leaf
CR (`zkappRoot`) ∘ zkApp-state CR (the field). This is the "zkApp state field" query. -/
theorem query_binds_zkappField (nodeCR : PoseidonPairCR) (leafCR : AccountLeafCR)
    (zkCR : ZkappStateCR) (a₁ a₂ : Account) (s₁ s₂ : List Nat) (i : Nat)
    (hl₁ : s₁.length = 8) (hl₂ : s₂.length = 8)
    (hz₁ : a₁.zkappRoot = zkappStateHash s₁) (hz₂ : a₂.zkappRoot = zkappStateHash s₂)
    (b₁ b₂ : List Nat) (idx root : Nat)
    (hlen : b₁.length = b₂.length)
    (hf₁ : merkleFold poseidonPair (leafHash a₁) b₁ idx = root)
    (hf₂ : merkleFold poseidonPair (leafHash a₂) b₂ idx = root) :
    s₁.getD i 0 = s₂.getD i 0 := by
  have hleaf : leafHash a₁ = leafHash a₂ :=
    merkleFold_binding nodeCR b₁ b₂ idx _ _ hlen (hf₁.trans hf₂.symm)
  have hzr : a₁.zkappRoot = a₂.zkappRoot := leafHash_commits_zkappRoot leafCR a₁ a₂ hleaf
  have hst : zkappStateHash s₁ = zkappStateHash s₂ := by rw [← hz₁, ← hz₂, hzr]
  rw [zkCR s₁ s₂ hl₁ hl₂ hst]

/-! ## §7 — Composition with K5: verify-root (K5) → query-under-root (K6). -/

/-- **The K5 → K6 seam.** GIVEN the K5 verdict as an abstract `LedgerRootAttested root` (what
`KimchiVerify.kimchiVerifyDecision` supplies — the root is a Kimchi-VALID Mina block's ledger root,
subject to the IPA/FRI floor K5 names; kept a `Prop` parameter so this file imports K1/K3, not the
K5 tree) and a satisfying Merkle path for account `a` to that root, the queried balance is the
UNIQUE value bound in the verified ledger: no other account opens the same slot to a different
balance. So "verify Mina + read account `a`" = (K5) attest root ∘ (K6) query-under-root. -/
theorem mina_verify_then_query (nodeCR : PoseidonPairCR) (leafCR : AccountLeafCR)
    (LedgerRootAttested : Nat → Prop) (root : Nat) (hverified : LedgerRootAttested root)
    (a : Account) (branch : List Nat) (idx : Nat)
    (hfold : merkleFold poseidonPair (leafHash a) branch idx = root) :
    LedgerRootAttested root
    ∧ ∀ (a' : Account) (b' : List Nat), b'.length = branch.length →
        merkleFold poseidonPair (leafHash a') b' idx = root → a'.balance = a.balance :=
  ⟨hverified, fun a' b' hlen hf' =>
    query_binds_balance nodeCR leafCR a' a b' branch idx root hlen hf' hfold⟩

/-! ## §8 — axiom hygiene. -/

#assert_axioms poseidonPair_eq_hash
#assert_axioms merkleFold_nil
#assert_axioms merkleFold_single_even
#assert_axioms merkleFold_single_odd
#assert_axioms merkleFold_forces
#assert_axioms merkleFold_binding
#assert_axioms accountFields_commits_balance
#assert_axioms accountFields_commits_nonce
#assert_axioms accountFields_commits_zkappRoot
#assert_axioms leafHash_commits_balance
#assert_axioms leafHash_commits_nonce
#assert_axioms leafHash_commits_zkappRoot
#assert_axioms verifyAccountQuery_from_fold
#assert_axioms query_binds_balance
#assert_axioms query_binds_nonce
#assert_axioms query_binds_zkappField
#assert_axioms mina_verify_then_query

#print axioms query_binds_balance
#print axioms query_binds_zkappField
#print axioms mina_verify_then_query

/-! ## §9 — KATs: real Poseidon-Merkle vectors, both polarity (kernel-reducible over the o1js-exact
`Ref.hash`). Root/leaf values computed INDEPENDENTLY (a Python recomputation over the same dumped
Kimchi constants that reproduces the o1js gold `Poseidon.hash` vectors K3 §5 pins); a tampered
sibling / balance / nonce / app-state field FLIPS the value (the query is non-vacuous). -/

/-- The KAT account: balance 5000, nonce 3 (fields `[111,1,0,5000,3,222,111,0,0]`). -/
def katAccount : Account := ⟨111, 1, 0, 5000, 3, 222, 111, 0, 0⟩
/-- The KAT zkApp app-state (8 fields). -/
def katAppState : List Nat := [10, 20, 30, 40, 50, 60, 70, 80]

-- The Merkle FOLD, depth 2 (leaf 7, siblings [11, 13], path idx 2): a real Poseidon-Merkle root.
#guard merkleFold poseidonPair 7 [11, 13] 2 ==
  21854892281928035201729884177122216581371284660515611400752318599290278209395
-- discrimination: a tampered sibling (13 → 99) FLIPS the reconstructed root.
#guard merkleFold poseidonPair 7 [11, 99] 2 !=
  21854892281928035201729884177122216581371284660515611400752318599290278209395

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
#guard zkappStateHash katAppState ==
  2877203160029291904480306281751044370917607895926420909241134854411259156922
-- discrimination: a tampered app-state field (index 2, 30 → 31) FLIPS the digest.
#guard zkappStateHash (katAppState.set 2 31) !=
  2877203160029291904480306281751044370917607895926420909241134854411259156922

-- Structural: the fold at the honest witness discharges the query boolean.
#guard verifyAccountQuery 7 [11, 13] 2
  21854892281928035201729884177122216581371284660515611400752318599290278209395 == true
-- Structural: a WRONG root fails the query (non-vacuous accept).
#guard verifyAccountQuery 7 [11, 13] 2 12345 == false
#guard (accountFields katAccount).length == 9

/-! ## §10 — The PRECISE named residuals (none `sorry`-ed).

  1. **The protocol account-ledger uses a PER-HEIGHT node prefix** `Hash_prefix.merkle_tree height`
     = `"MinaMklTree%03d"` (`ledger_hash.ml:8`, `hash_prefixes.ml:51`), NOT the plain
     `Poseidon(l,r)` baked here. `merkleFold`/`merkleFold_binding`/`merkleFold_forces` are
     hash-GENERIC (parameter `hp`), so a per-height `hp height l r` (its IV a Poseidon salt of the
     prefix string) drops straight in — dumping those IV field constants is the same mechanical
     step K3 did for the round constants. The plain node hash IS byte-exact for o1js application
     `MerkleTree`/`MerkleWitness`/`MerkleMap` (probe-confirmed), which is the zkApp-state query.
  2. **The exact `Account.crypto_hash` serialization is MODELED, not byte-verified** — the
     "MinaAccount" prefix (`hash_prefixes.ml:30`) and the `to_input`/`pack_input` bit-packing
     (balance/nonce/token co-packed into shared field elements) are not reproduced; `accountFields`
     captures the commitment STRUCTURE only. The commitment lemmas are packing-agnostic (any
     injective encoding under the CR floor), so this is a fidelity residual, not a soundness hole.
     Likewise `zkappRoot = zkappStateHash appState` simplifies the real `Zkapp_account.digest`.
  3. **The per-node Poseidon forcing is K3 §7 residual #3.** `merkleFold_forces` discharges the
     TREE given per-node forcing `hnode : f = poseidonPair`; that one Poseidon-2 node forcing is the
     `absorbBlock_forces ∘ perm_forces ∘ squeeze` composition K3 named — localized here, not new
     debt. The top-level query theorems take the reconstruction (`hfold`) as an explicit hypothesis,
     exactly as the ETH FIN/EXEC folds take theirs — what is DERIVED vs ASSUMED is visible.
  4. **The CR floors** (`PoseidonPairCR`, `AccountLeafCR`, `ZkappStateCR`) are the named Poseidon
     collision-resistance assumptions (Props, like `EthLeaf.hashPairCR`) — the cryptographic floor,
     taken as explicit hypotheses where consumed, never claimed provable.
  5. **The shared K1/K3 field-width residual** — the `ℤ ↔ p_felt` gap (K1 §6) and the `z < p`
     canonical compare stand unchanged under this gadget (it composes over K3's forced sponge).

This FINISHES the Mina verifier's state-query layer: the Poseidon Merkle-path fold + the account-
leaf/zkApp-field commitment + the query decision, composing with K5 as verify-root → query-under-
root. NOT claimed: a per-height protocol-ledger prefix, byte-exact account serialization, or the
in-AIR per-node Poseidon composition (all named above).
-/

end Dregg2.Circuit.Emit.MinaStateQuery
