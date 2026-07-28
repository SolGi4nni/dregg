/-
# Dregg2.Circuit.Emit.LightClientTmHashFold — folding out the Cosmos/Tendermint SHA-256 HASH carriers
`VSET_OK` and `EPOCH_OK`: the validator-set-hash bindings become DERIVED by an in-circuit SHA-256
collection fold, not trusted witnessed boolean carriers.

## The carriers being folded out (the SHA-256 hash carriers — NOT the Ed25519 SIG carrier)

`LightClientTendermintAir` carries three witnessed carrier bits. Two are SHA-256 hash comparisons over
the encoded validator set (`LightClientTendermint.tmVerify`, the load-bearing conjuncts):

  * `EPOCH_OK` = `decide (L.hash (enc u.validators) = ts.nextValidatorsHash)` — the next-validators
    epoch/adjacency binding: the untrusted set is EXACTLY the set the trusted header committed to.
  * `VSET_OK`  = `decide (L.hash (enc u.validators) = u.header.validatorsHash)` — the header
    self-binding: the quorum is over the set the header names.

In the carrier slice `tmLcAir_no_forgery` takes the honest-witness relation for these two bits as a
hypothesis — it TRUSTS the prover set them to the true SHA-256 results. The verifier re-runs no hash.

This file replaces that trust with the SHA-256 fold itself, mirroring `LightClientEthFinFold` /
`LightClientEthExecFold` and REUSING the proven `Sha256MerkleFold.pairHash` (the FIPS-anchored two-block
SSZ SHA-256). The third carrier — `ED_OK`, the Ed25519 commit-signature result folded into
`SIGNED_POW` — stays a hypothesis (the Ed25519/EC arc, shared with BLS; NOT this file).

## The SHA shape: a flat COLLECTION hash, realized as a Merkle–Damgård chain over `pairHash`

Unlike the ETH carriers (which the bridge already states as branch reconstructions, `reconstruct L leaf
branch idx`), the Tendermint bridge states `validators_hash` as a FLAT hash of the encoded set,
`L.hash (enc validators)`. Real Tendermint's `validators_hash` IS a SHA-256 hash over the validator
collection (an RFC-6962 Merkle tree); this file REALIZES that flat abstraction as the Merkle–Damgård
CHAIN `chainCommit = foldl pairHash IV` over the per-validator leaf digests — a hash over the WHOLE
collection built ENTIRELY from the proven `pairHash` (House Law #1: no new SHA arithmetic authored; the
compression primitive is the `Sha256MerkleFold` two-block SSZ hash). `chainCommit` is the SHA-256
collection commit the AIR emits (as chained `sha256PairHash` blocks), so a satisfying witness must
EXHIBIT the validator leaves whose SHA-256 chain hits the bound `validatorsHash` / `nextValidatorsHash`
— the two hash carriers become DERIVED, not two trusted bits.

## The ties proved here (mirroring the ETH folds' four theorems, per carrier)

  * `tmShaLeaf_hash_eq_chainCommit` — the bridge leaf's abstract `hash` IS the generator's SHA-256
    collection chain (the `reconstruct_*_eq_foldReconstruct` analog: the object the carriers stood for,
    now the SHA arithmetic).
  * `chainCommit_binding_on` — GIVEN separation on the chain's OWN pairs (`Sha256MerkleFold.pairSepOn`
    + `ChainCovered`, the HONEST floor), equal-length equal chain roots pin the whole leaf list: the
    SHA-256 collection commit BINDS the validator set.
  * `tmHashBindings_from_fold` (`verify*_from_fold` analog) — the two carrier equalities are DISCHARGED
    by the exhibited SHA folds: NO `VSET_OK`/`EPOCH_OK` column is read.
  * `tm_hash_from_fold_gate_accepts` — the fold-derived hash bindings DISCHARGE `tmVerify`, with NO
    crypto carrier. Trust moves from "two opaque prover-set bits" to "the SHA-256 gadget's gates over
    an exhibited validator-leaf chain".
  * `tm_validatorSet_binding_on` — the NON-EQUIVOCATION content, on the HONEST floor.

## ⚑ 2026-07-27 — WHAT WAS DELETED AND WHY (the vacuity repair)

`tm_hash_from_fold_slots_into_no_forgery` is GONE, and `chainCommit_binding`'s `hpair` hypothesis
with it. Both rested on idealized injectivity of a COMPRESSING hash:

  * `tmShaLeaf.hashCR` was `∀ m₁ m₂, chainCommit m₁ = chainCommit m₂ → m₁ = m₂` — REFUTED here by
    TWO executable witnesses (`chainCommit_word64_collision`: message word 64 is never read;
    `chainCommit_high_bits_collision`: a word is read only mod `2^64`, so a validator's raw voting
    power aliases). `CryptoLeaf.noCollision` demands the carrier ENTAIL that, so the slot is `False`.
  * `chainCommit_binding` took the same shape one level down, on `pairHash`, also refuted.

Replacements: `chainCommit_binding_on` / `tm_validatorSet_binding_on`, on
`Sha256MerkleFold.pairSepOn` + `ChainCovered` — separation on the chain's OWN pairs, which is
SATISFIABLE (`pairSepOn_tmChainSep`, kernel-checked on the real SHA-256), REFUTABLE
(`Sha256MerkleFold.pairSepOn_truncSep_false`) and NOT PROVABLE. **CAPABILITY LOST, NAMED:**
`TmForeignValid`'s ∀-quantified non-equivocation conjunct, over the infinite space of alternative
validator sets, is not derivable at a compressing hash by any premise. The pairwise form is what
survives, and it is what a query-counted collision bound prices.

## What remains (the honest, PRICED residuals — proof-mode step, LOW resolution + LABELED)

  * RESIDUAL #1 (proof-composition wall): the folds `chainCommit (enc validators) = target` are, in the
    deployed circuit, the CONCLUSION of the chained `sha256PairHash` gates forcing their SHA outputs up
    ~30k gates/block × 2 blocks × #validators. The atomic gates are forced + both-polarity KAT'd
    (`Sha256Gadget`/`Sha256MerkleFold` §0/§2); the full composition is the next slice. Here the folds are
    explicit hypotheses, so DERIVED vs ASSUMED is visible.
  * RESIDUAL #2 (flat→tree modeling + full-collection): the bridge's `L.hash (enc validators)` is a flat
    abstraction; this file realizes it as a Merkle–Damgård chain over per-validator LEAF digests. The
    per-validator LEAF hashing (validator protobuf → 8-word leaf) is a separate SHA not re-derived here
    (the leaf digests are the chain's inputs); and the chain is a BOUNDED (fixed-#validator) fold — the
    arbitrary-N collection and the exact RFC-6962 tree shape are the named full-tree residual. The KAT
    fixes the demo's 3-validator set.
  * RESIDUAL #3 (deploy/emit wall): the chained two-block-SHA fold cannot be flat-merged into
    `tmLcVerifyDesc`'s byte-golden `emitVmJson2`; the deployed removal of the `VSET_OK`/`EPOCH_OK`
    columns routes through the IR-v2 `proofBind` recursion seam (identical to the ETH lane). This file
    lands the Lean tie; `tmLcVerifyDesc` and its golden are UNTOUCHED — NO VK regen.
  * RESIDUAL #4 (Ed25519/EC arc): `ED_OK` stays a hypothesis — the per-validator commit-signature
    soundness is the Ed25519 leaf, the EC arc, not folded here.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`/`admit`/`native_decide`. The
`#guard` KATs anchor the 3-validator SHA-256 chain against an independently-computed SHA-256 vector
(`hashlib`, matching `Sha256MerkleFold` §0's FIPS anchoring exactly — encoding verified against the
published `SHA256(64·0x00)` vector), both polarities (a real chain value + a tampered validator whose
chain DIFFERS). `tmShaLeaf` is the lawful SHA `CryptoLeaf` instance over the real `chainCommit`; its
`hashCR` slot is `False`, because `CryptoLeaf.noCollision` demands global injectivity of a
compressing hash (`chainCommitInjective_false`). The Ed25519 `sigSound` is the demo slot, the EC-arc
residual. Imports read-only (`Sha256MerkleFold`, `Bridge.LightClientTendermint`).
-/
import Dregg2.Circuit.Emit.Sha256MerkleFold
import Dregg2.Bridge.LightClientTendermint

namespace Dregg2.Circuit.Emit.LightClientTmHashFold

open Dregg2.Circuit.Emit.Sha256MerkleFold
open Dregg2.Bridge.VerifiedLightClient
open Dregg2.Bridge.LightClientTendermint

set_option autoImplicit false
set_option maxRecDepth 8192

/-! ## §0 — The SHA-256 COLLECTION COMMIT generator (the shared object; reused by the Solana fold).

`chainCommit` is a Merkle–Damgård chain over the proven two-block SSZ `Sha256MerkleFold.pairHash`: fold
the per-entry 8-word leaf digests through `pairHash` from the fixed IV. This is the SHA-256 hash over a
collection (validator set / stake table) — built ONLY from `pairHash`, no new SHA arithmetic. -/

/-- The chain IV — 32 zero bytes (8 zero words). -/
def chainIV : List Nat := List.replicate 8 0

/-- **The SHA-256 collection commit** — `foldl pairHash IV` over the per-entry leaf digests. Each step
`pairHash acc leaf` is the proven two-block SSZ SHA-256 of the 64-byte concatenation. Reduces in the
kernel; anchored to a real SHA-256 vector by the KATs below. -/
def chainCommit (leaves : List (List Nat)) : List Nat :=
  leaves.foldl (fun acc leaf => pairHash acc leaf) chainIV

/-- Appending one leaf is one more `pairHash` step (the chain's step law). -/
theorem chainCommit_concat (l : List (List Nat)) (x : List Nat) :
    chainCommit (l ++ [x]) = pairHash (chainCommit l) x := by
  simp [chainCommit, List.foldl_append]

/-- The chain from an arbitrary accumulator (`chainCommit = chainFrom chainIV`). -/
def chainFrom (acc : List Nat) (leaves : List (List Nat)) : List Nat :=
  leaves.foldl (fun a l => pairHash a l) acc

theorem chainCommit_eq_chainFrom (l : List (List Nat)) : chainCommit l = chainFrom chainIV l := rfl

/-- **`ChainCovered P acc leaves`** — `P` holds of every pair the collection chain feeds to
`pairHash` from `acc`. The chain's HASH TRANSCRIPT, as an obligation a consumer discharges by
exhibiting its leaves. -/
def ChainCovered (P : List Nat → List Nat → Prop) : List Nat → List (List Nat) → Prop
  | _, [] => True
  | acc, x :: rest => P acc x ∧ ChainCovered P (pairHash acc x) rest

/-- **THE COLLECTION COMMIT BINDS, at the HONEST floor** (`chainFrom` form).

⚑ 2026-07-27 — this used to take `hpair : ∀ a b c d, pairHash a b = pairHash c d → a = c ∧ b = d`,
described as "the honest per-pair SHA-256 CR". That `Prop` is FALSE — `pairHash` compresses, and
`Sha256MerkleFold.pairHashInjective_false` refutes it with an executable collision — so the theorem
had an empty premise. The proof only ever applied the floor at the chain's OWN pairs, so the honest
hypothesis is separation on exactly those (`Sha256MerkleFold.pairSepOn` + `ChainCovered`), which is
satisfiable, refutable and not provable. The conclusion is unchanged, and now strengthened to pin the
accumulator as well as the leaves. -/
theorem chainFrom_binding_on (P : List Nat → List Nat → Prop) (hsep : pairSepOn P) :
    ∀ (l₁ l₂ : List (List Nat)) (a₁ a₂ : List Nat), l₁.length = l₂.length →
      ChainCovered P a₁ l₁ → ChainCovered P a₂ l₂ →
      chainFrom a₁ l₁ = chainFrom a₂ l₂ → a₁ = a₂ ∧ l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ a₁ a₂ hlen _ _ h
    cases l₂ with
    | nil => exact ⟨h, rfl⟩
    | cons _ _ => simp at hlen
  | cons x₁ r₁ ih =>
    intro l₂ a₁ a₂ hlen hc₁ hc₂ h
    cases l₂ with
    | nil => simp at hlen
    | cons x₂ r₂ =>
      have hlen' : r₁.length = r₂.length := by simpa using hlen
      simp only [ChainCovered] at hc₁ hc₂
      simp only [chainFrom, List.foldl_cons] at h
      obtain ⟨hstep, hrest⟩ := ih r₂ (pairHash a₁ x₁) (pairHash a₂ x₂) hlen' hc₁.2 hc₂.2 h
      obtain ⟨ha, hx⟩ := hsep _ _ _ _ hc₁.1 hc₂.1 hstep
      exact ⟨ha, by rw [hx, hrest]⟩

/-- **THE VALIDATOR/STAKE COLLECTION COMMIT BINDS.** Equal-length collections whose SHA-256 chains
agree ARE the same collection — GIVEN separation on the two chains' own pairs. -/
theorem chainCommit_binding_on (P : List Nat → List Nat → Prop) (hsep : pairSepOn P)
    (l₁ l₂ : List (List Nat)) (hlen : l₁.length = l₂.length)
    (hc₁ : ChainCovered P chainIV l₁) (hc₂ : ChainCovered P chainIV l₂)
    (h : chainCommit l₁ = chainCommit l₂) : l₁ = l₂ :=
  (chainFrom_binding_on P hsep l₁ l₂ chainIV chainIV hlen hc₁ hc₂ h).2

/-! ## §1 — The SHA `CryptoLeaf` for Tendermint: `hash = chainCommit` (the SHA-256 collection fold).

A lawful `CryptoLeaf` whose `hash` IS the FIPS-anchored SHA-256 collection commit. The Ed25519 signature
fields are the demo slot (registered-key toy MAC — the EC-arc residual; the load-bearing quorum
genuineness rides `sigSound`, exactly as the bridge demo). The `hashCR` slot is `False`, because the interface's
unpacker demands global injectivity of a compressing hash
(the slot is `False` — see the leaf's docstring). -/

/-- Demo Ed25519-slot verifier (registered key + toy MAC): the EC-arc residual, NOT what is folded. -/
def tmDemoSigVerify (pk : Nat) (_m : List (List Nat)) (s : Nat) : Bool :=
  decide (pk < 100) && (s == pk)

/-- Demo `Signed` denotation: a registered key authorized the message. -/
def tmDemoSigned (pk : Nat) (_m : List (List Nat)) : Prop := pk < 100

/-- The demo signature-soundness leaf, PROVED (the Ed25519 `sigSound` slot). -/
theorem tmDemoSigSound (pk : Nat) (m : List (List Nat)) (s : Nat)
    (h : tmDemoSigVerify pk m s = true) : tmDemoSigned pk m := by
  simp only [tmDemoSigVerify, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- **The IDEALIZED collection-CR floor, NAMED so it can be REFUTED rather than assumed.** This is
the exact `Prop` `tmShaLeaf.hashCR` used to hold. -/
def chainCommitInjective : Prop :=
  ∀ m₁ m₂ : List (List Nat), chainCommit m₁ = chainCommit m₂ → m₁ = m₂

/-- Two one-element collections whose leaves differ only past message word 64 chain to the same root
(`chainCommit [x] = pairHash chainIV x`, and `pairHash` never reads word 64). -/
theorem chainCommit_word64_collision :
    chainCommit [List.replicate 56 0] = chainCommit [List.replicate 56 0 ++ [1]] :=
  pairHash_ignores_word_64

/-- ⚑ **THE SHARPER ONE — the validator-set commit does not see a field's high bits.** A leaf whose
third word is `50` and one whose third word is `50 + 2^64` chain to the SAME root, because `pairHash`
reads its message words only modulo `2^64`. Any protobuf-shaped encoder that drops an unbounded
`Nat` (a voting power, a height) into a word is non-injective AT THE DIGEST. -/
theorem chainCommit_high_bits_collision :
    chainCommit [[1, 2, 3, 4, 5, 6, 7, 8]] = chainCommit [[1, 2, 3, 4 + 2 ^ 64, 5, 6, 7, 8]] :=
  pairHash_ignores_bits_above_64

/-- **THE IDEALIZED COLLECTION-CR FLOOR IS FALSE**, by witness. -/
theorem chainCommitInjective_false : ¬ chainCommitInjective := by
  intro h
  exact absurd (h _ _ chainCommit_high_bits_collision) (by decide)

/-- **`tmShaLeaf`** — the lawful SHA `CryptoLeaf` whose hash IS `chainCommit` (the SHA-256 collection
fold over `pairHash`). The Ed25519 fields are the demo/EC-arc slot.

⚑ 2026-07-27 — `hashCR` used to be `∀ m₁ m₂, chainCommit m₁ = chainCommit m₂ → m₁ = m₂`, described
as "the GENUINE SHA-256 collection-CR floor". `CryptoLeaf.noCollision` demands the carrier ENTAIL
exactly that, and it is FALSE (`chainCommitInjective_false`, two executable witnesses). So every
theorem that took `hcr : tmShaLeaf.hashCR` proved nothing. The slot is now `False`, which is what
this interface can hold at a compressing hash; the binding content rides `chainCommit_binding_on`
on the HONEST floor `Sha256MerkleFold.pairSepOn`. -/
@[reducible] def tmShaLeaf : CryptoLeaf where
  PubKey := Nat
  Msg := List (List Nat)
  Sig := Nat
  Digest := List Nat
  sigVerify := tmDemoSigVerify
  hash := chainCommit
  Signed := tmDemoSigned
  sigSound := tmDemoSigSound
  hashCR := False
  noCollision := fun h => h.elim

instance : DecidableEq tmShaLeaf.Digest := inferInstanceAs (DecidableEq (List Nat))

/-! ### The floor's THREE legs (the audited guard tested only the middle one). -/

/-- A COLLAPSING collection commit (every collection digests to the zero root) — the badCompress. -/
def tmCollapseCommit (_ : List (List Nat)) : List Nat := chainIV

/-- **REFUTABLE at a collapsing hash (the guard that already existed).** Two DIFFERENT collections
share the root. This tests only that the SHAPE can be false — it says nothing about whether it is
SATISFIABLE at the real hash, which is the leg the audit found missing, and at which the answer
was NO (`chainCommitInjective_false`). -/
theorem tmCollapse_not_CR :
    ¬ (∀ m₁ m₂ : List (List Nat), tmCollapseCommit m₁ = tmCollapseCommit m₂ → m₁ = m₂) := by
  intro h
  exact absurd (h [] [[]] rfl) (by decide)

/-- **SATISFIABLE — the honest floor HOLDS on an exhibited chain transcript.** The two-leaf
validator chain's own pairs are separated (kernel-checked on the real SHA-256), so
`chainCommit_binding_on` is an implication with a NON-empty antecedent. -/
def tmChainSep (a b : List Nat) : Prop :=
  (a = chainIV ∧ b = [1, 2, 3, 4, 5, 6, 7, 8])
  ∨ (a = chainIV ∧ b = [1, 2, 3, 9, 5, 6, 7, 8])

set_option maxRecDepth 8192 in
theorem pairSepOn_tmChainSep : pairSepOn tmChainSep := by
  intro a b c d hab hcd e
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    first
      | exact ⟨rfl, rfl⟩
      | exact absurd e (by decide)

/-- **The satisfying floor FIRES** — obtained THROUGH `chainCommit_binding_on`: at a class the floor
genuinely holds on, two one-leaf collections differing in one word cannot share a chain root. Floor,
coverage and conclusion exercised together on the real SHA-256. -/
theorem tm_chain_binding_fires :
    chainCommit [[1, 2, 3, 4, 5, 6, 7, 8]] ≠ chainCommit [[1, 2, 3, 9, 5, 6, 7, 8]] := by
  intro h
  exact absurd (chainCommit_binding_on tmChainSep pairSepOn_tmChainSep
    [[1, 2, 3, 4, 5, 6, 7, 8]] [[1, 2, 3, 9, 5, 6, 7, 8]] rfl
    ⟨Or.inl ⟨rfl, rfl⟩, trivial⟩ ⟨Or.inr ⟨rfl, rfl⟩, trivial⟩ h) (by decide)

/-! ## §2 — The four fold theorems (mirroring the ETH folds), per the two hash carriers. -/

/-- **THE TIE (`reconstruct_*_eq_foldReconstruct` analog).** The bridge leaf's abstract `hash` IS the
generator's SHA-256 collection chain — the object `VSET_OK`/`EPOCH_OK` stood for, via the SHA
arithmetic, not a bit. -/
theorem tmShaLeaf_hash_eq_chainCommit (m : List (List Nat)) :
    tmShaLeaf.hash m = chainCommit m := rfl

/-- **THE CARRIER CONTENT, DERIVED from the SHA fold (`*_fold_derives_*` analog).** The fold gates force
the chain root `= chainCommit (enc validators)` (RESIDUAL #1, an explicit hypothesis here), and the
publish/bind forces that root `= target`; therefore the validator chain hashes to the bound root — the
`VSET_OK`/`EPOCH_OK` content, obtained from the exhibited validator leaves, not a trusted bit. -/
theorem vsetFold_derives_binding (leaves : List (List Nat)) (root target : List Nat)
    (hforce : root = chainCommit leaves) (hbind : root = target) :
    chainCommit leaves = target := by
  rw [← hforce, hbind]

/-- **THE TWO HASH CARRIERS DISCHARGED by the exhibited SHA folds (`verify*_from_fold` analog) — NO
`VSET_OK`/`EPOCH_OK` bit read.** Given SHA chains reconstructing the encoded validator set into the
trusted `nextValidatorsHash` (epoch binding) and the header's `validatorsHash` (self binding), the two
bridge hash equalities hold. A satisfying prover must EXHIBIT validator leaves whose SHA-256 chain hits
both roots; there is no witnessed carrier to set. -/
theorem tmHashBindings_from_fold
    (enc : List (TmValidator tmShaLeaf.PubKey) → tmShaLeaf.Msg)
    (ts : TmTrustedState tmShaLeaf) (u : TmUpdate tmShaLeaf)
    (hEpochFold : chainCommit (enc u.validators) = ts.nextValidatorsHash)
    (hVsetFold : chainCommit (enc u.validators) = u.header.validatorsHash) :
    tmShaLeaf.hash (enc u.validators) = ts.nextValidatorsHash
    ∧ tmShaLeaf.hash (enc u.validators) = u.header.validatorsHash :=
  ⟨hEpochFold, hVsetFold⟩

/-- **THE PAYOFF, CARRIER-FREE: the fold-derived hash bindings DISCHARGE THE WHOLE TENDERMINT GATE.**
Given the six arithmetic legs (chain-id match, adjacent height, the three time-window legs, and the
strict `>2/3` stake threshold), if the encoded validator set's SHA-256 chain reconstructs into BOTH
the trusted next-validators root and the header's validators-hash (`hEpochFold`/`hVsetFold` — DERIVED
from the exhibited validator leaves, not two witnessed bits), `tmVerify` accepts. No `VSET_OK` /
`EPOCH_OK` bit is read and NO hash floor is used.

⚑ 2026-07-27 — this replaces `tm_hash_from_fold_slots_into_no_forgery`, which concluded
`TmForeignValid` from `hcr : tmShaLeaf.hashCR` = idealized injectivity of `chainCommit`, REFUTED
(`chainCommitInjective_false`). **CAPABILITY LOST, NAMED:** `TmForeignValid`'s ∀-quantified
non-equivocation conjunct is not derivable at a compressing hash by any premise, because
`CryptoLeaf.noCollision` demands global injectivity. What replaces it is the PAIRWISE form
(`tm_validatorSet_binding_on`), which is also the form a collision bound prices. -/
theorem tm_hash_from_fold_gate_accepts
    (sb : TmHeader tmShaLeaf.Digest → tmShaLeaf.Msg)
    (enc : List (TmValidator tmShaLeaf.PubKey) → tmShaLeaf.Msg)
    (ts : TmTrustedState tmShaLeaf) (u : TmUpdate tmShaLeaf)
    (hChain : u.header.chainId = ts.chainId)
    (hHeight : u.header.height = ts.height + 1)
    (hMono : ts.headerTime < u.header.time)
    (hDrift : u.header.time ≤ ts.now + ts.clockDrift)
    (hTrust : ts.now < ts.headerTime + ts.trustingPeriod)
    (hThresh : 2 * totalPower u.validators
                < 3 * signedPower tmShaLeaf (sb u.header) u.validators u.commit)
    (hEpochFold : chainCommit (enc u.validators) = ts.nextValidatorsHash)
    (hVsetFold : chainCommit (enc u.validators) = u.header.validatorsHash) :
    tmVerify tmShaLeaf sb enc ts u = true :=
  (tmVerify_eq_true_iff tmShaLeaf sb enc ts u).mpr
    ⟨hChain, hHeight, hMono, hDrift, hTrust, hEpochFold, hVsetFold, hThresh⟩

/-- **THE VALIDATOR SET IS BOUND, at the HONEST floor.** Two equal-length validator-leaf collections
whose SHA-256 chains both hit the SAME trusted root ARE the same collection — GIVEN separation on
the two chains' own pairs. This is the crypto content `VSET_OK`/`EPOCH_OK` stood for: an attacker
cannot open one `validators_hash` to two different validator sets (hence cannot move the stake
denominator) without a `pairHash` collision on the pairs it exhibits. -/
theorem tm_validatorSet_binding_on (P : List Nat → List Nat → Prop) (hsep : pairSepOn P)
    (l₁ l₂ : List (List Nat)) (root : List Nat) (hlen : l₁.length = l₂.length)
    (hc₁ : ChainCovered P chainIV l₁) (hc₂ : ChainCovered P chainIV l₂)
    (h₁ : chainCommit l₁ = root) (h₂ : chainCommit l₂ = root) : l₁ = l₂ :=
  chainCommit_binding_on P hsep l₁ l₂ hlen hc₁ hc₂ (h₁.trans h₂.symm)

/-! ## §3 — KATs: the 3-validator SHA-256 chain, anchored to an independent SHA-256 vector.

Both-polarity, non-vacuous: a genuine 3-validator chain value computed independently (`hashlib`,
matching `Sha256MerkleFold` §0's FIPS anchoring — the `pairHash` encoding verified against the published
`SHA256(64·0x00)` vector), and a tampered validator (power `1 → 99`, a stake-inflation tamper) whose
chain DIFFERS (the validator-set binding is not vacuous). These reduce in the kernel (Nat SHA reference). -/

/-- Validator #1 (key 1, power 1) as an 8-word leaf digest. -/
def tmVal1 : List Nat := [0x76616c00, 1, 1, 0, 0, 0, 0, 0]
/-- Validator #2 (key 2, power 1). -/
def tmVal2 : List Nat := [0x76616c00, 2, 1, 0, 0, 0, 0, 0]
/-- Validator #3 (key 3, power 1). -/
def tmVal3 : List Nat := [0x76616c00, 3, 1, 0, 0, 0, 0, 0]
/-- The 3-validator leaf list (the demo `demoValidators` set, keys 1/2/3, power 1 each). -/
def tmValLeaves : List (List Nat) := [tmVal1, tmVal2, tmVal3]

-- Positive: the real 3-validator SHA-256 chain (validators_hash), independently computed (hashlib).
#guard chainCommit tmValLeaves ==
  [0xe4b5bf24, 0x4aeb78a6, 0xe6ae9134, 0x1f4c54f7, 0xed39016a, 0x76ff5782, 0x00e9ac8a, 0x1b50797b]
-- Negative (discrimination): validator 3's power 1 → 99 changes the collection root.
#guard chainCommit [tmVal1, tmVal2, [0x76616c00, 3, 99, 0, 0, 0, 0, 0]] !=
  [0xe4b5bf24, 0x4aeb78a6, 0xe6ae9134, 0x1f4c54f7, 0xed39016a, 0x76ff5782, 0x00e9ac8a, 0x1b50797b]
-- The chain's single-step law reduces (the IV-anchored first block).
#guard chainCommit [tmVal1] == pairHash chainIV tmVal1

/-! ## §4 — axiom hygiene. -/

#assert_axioms chainCommit_concat
#assert_axioms chainFrom_binding_on
#assert_axioms chainCommit_binding_on
#assert_axioms tmDemoSigSound
#assert_axioms tmCollapse_not_CR
#assert_axioms chainCommit_word64_collision
#assert_axioms chainCommit_high_bits_collision
#assert_axioms chainCommitInjective_false
#assert_axioms pairSepOn_tmChainSep
#assert_axioms tm_chain_binding_fires
#assert_axioms tmShaLeaf_hash_eq_chainCommit
#assert_axioms vsetFold_derives_binding
#assert_axioms tmHashBindings_from_fold
#assert_axioms tm_hash_from_fold_gate_accepts
#assert_axioms tm_validatorSet_binding_on

#print axioms tm_hash_from_fold_gate_accepts
#print axioms chainCommit_binding_on

end Dregg2.Circuit.Emit.LightClientTmHashFold
