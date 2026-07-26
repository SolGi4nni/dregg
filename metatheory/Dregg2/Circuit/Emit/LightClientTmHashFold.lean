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
  * `chainCommit_binding` — GIVEN the `pairHash` collision-resistance floor, equal-length equal chain
    roots pin the whole leaf list: the SHA-256 collection commit BINDS the validator set (the
    `htrExec_commits_stateRoot`-style commitment lemma, here reduced to the proven pair-hash floor —
    the honest content behind `noCollision`).
  * `tmHashBindings_from_fold` (`verify*_from_fold` analog) — the two carrier equalities are DISCHARGED
    by the exhibited SHA folds: NO `VSET_OK`/`EPOCH_OK` column is read.
  * `tm_hash_from_fold_slots_into_no_forgery` (`*_from_fold_slots_into_no_forgery` analog) — the
    fold-derived hash bindings slot into `tmNoForgery` IN PLACE of the two trusted bits: the Tendermint
    no-forgery guarantee holds with two fewer trusted carriers. Trust moves from "two opaque prover-set
    bits" to "the SHA-256 gadget's gates over an exhibited validator-leaf chain".

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
chain DIFFERS). `tmShaLeaf` is the lawful SHA `CryptoLeaf` demonstration instance whose `hashCR` is the
GENUINE SHA-256 collection-CR floor over `chainCommit` (taken as the explicit `hcr` hypothesis where
consumed, exactly as `shaWordLeaf.hashPairCR`; the Ed25519 `sigSound` is the demo slot, the EC-arc
residual). NEW file; imports read-only (`Sha256MerkleFold`, `Bridge.LightClientTendermint`).
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

/-- **THE COLLECTION COMMIT BINDS (the commitment lemma; reduced to the proven pair-hash floor).**
GIVEN the `pairHash` collision-resistance floor `hpair` (the honest per-pair SHA-256 CR, an explicit
hypothesis — for the real chain the named SHA-256 assumption), equal-length collections whose SHA-256
chains agree ARE the same collection: the commit pins the whole validator/stake leaf list. This is the
`htrExec_commits_stateRoot`-style commitment, here the WHOLE-collection binding, reduced by structural
induction to `hpair`. It is the genuine content behind the leaf's `noCollision` (which states the same
binding, unconditioned on length, as the named floor). -/
theorem chainCommit_binding
    (hpair : ∀ a b c d : List Nat, pairHash a b = pairHash c d → a = c ∧ b = d) :
    ∀ (l₁ l₂ : List (List Nat)), l₁.length = l₂.length →
      chainCommit l₁ = chainCommit l₂ → l₁ = l₂ := by
  intro l₁
  induction l₁ using List.reverseRecOn with
  | nil =>
    intro l₂ hlen _
    cases l₂ with
    | nil => rfl
    | cons a t => simp at hlen
  | append_singleton l₁' x₁ ih =>
    intro l₂ hlen h
    rcases List.eq_nil_or_concat l₂ with rfl | ⟨l₂', x₂, rfl⟩
    · simp at hlen
    · rw [List.concat_eq_append] at h hlen ⊢
      rw [chainCommit_concat, chainCommit_concat] at h
      obtain ⟨hc, hx⟩ := hpair _ _ _ _ h
      have hlen' : l₁'.length = l₂'.length := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen; omega
      rw [ih l₂' hlen' hc, hx]

/-! ## §1 — The SHA `CryptoLeaf` for Tendermint: `hash = chainCommit` (the SHA-256 collection fold).

A lawful `CryptoLeaf` whose `hash` IS the FIPS-anchored SHA-256 collection commit. The Ed25519 signature
fields are the demo slot (registered-key toy MAC — the EC-arc residual; the load-bearing quorum
genuineness rides `sigSound`, exactly as the bridge demo). The `hashCR` carrier is the GENUINE SHA-256
collection-CR floor over `chainCommit` — the named production assumption, taken as `hcr` where consumed
(never discharged positively, exactly as `shaWordLeaf.hashPairCR`). -/

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

/-- **`tmShaLeaf`** — the lawful SHA `CryptoLeaf` whose hash IS `chainCommit` (the SHA-256 collection
fold over `pairHash`). `hashCR` is the genuine collection-CR floor; `noCollision := id` unpacks it (the
named floor, `hcr` where consumed). The Ed25519 fields are the demo/EC-arc slot. -/
@[reducible] def tmShaLeaf : CryptoLeaf where
  PubKey := Nat
  Msg := List (List Nat)
  Sig := Nat
  Digest := List Nat
  sigVerify := tmDemoSigVerify
  hash := chainCommit
  Signed := tmDemoSigned
  sigSound := tmDemoSigSound
  hashCR := ∀ m₁ m₂ : List (List Nat), chainCommit m₁ = chainCommit m₂ → m₁ = m₂
  noCollision := fun h => h

instance : DecidableEq tmShaLeaf.Digest := inferInstanceAs (DecidableEq (List Nat))

/-! ### The CR-floor SHAPE discriminates (non-vacuity — not `True` in disguise). -/

/-- A COLLAPSING collection commit (every collection digests to the zero root) — the badCompress. -/
def tmCollapseCommit (_ : List (List Nat)) : List Nat := chainIV

/-- **The collapsing commit's CR carrier is FALSE (negative polarity).** Two DIFFERENT collections
share the root, so the carrier REFUTES a broken hash: `tmShaLeaf.hashCR`'s SHAPE is a real
discriminating hypothesis, not `True`. -/
theorem tmCollapse_not_CR :
    ¬ (∀ m₁ m₂ : List (List Nat), tmCollapseCommit m₁ = tmCollapseCommit m₂ → m₁ = m₂) := by
  intro h
  exact absurd (h [] [[]] rfl) (by decide)

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

/-- **THE PAYOFF: the fold-derived hash bindings slot into `tmNoForgery` in place of the two trusted
bits (`*_from_fold_slots_into_no_forgery` analog).** GIVEN the SHA-256 collection-CR carrier (`hcr` —
the named floor) and the six arithmetic legs (chain-id match, adjacent height, the three time-window
legs, and the strict `>2/3` stake threshold), if the encoded validator set's SHA-256 chain reconstructs
into BOTH the trusted next-validators root and the header's validators-hash (`hEpochFold`/`hVsetFold` —
DERIVED from the exhibited validator leaves, not two witnessed bits), the update is Tendermint-VALID
relative to the trusted state. The `VSET_OK`/`EPOCH_OK` carriers are folded out: their content is now
the conclusion of the SHA-256 collection fold. (`ED_OK`/Ed25519 rides `signedPower` — the EC-arc
hypothesis, unchanged here.) -/
theorem tm_hash_from_fold_slots_into_no_forgery
    (sb : TmHeader tmShaLeaf.Digest → tmShaLeaf.Msg)
    (enc : List (TmValidator tmShaLeaf.PubKey) → tmShaLeaf.Msg)
    (hcr : tmShaLeaf.hashCR)
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
    TmForeignValid tmShaLeaf sb enc u := by
  have hverify : tmVerify tmShaLeaf sb enc ts u = true :=
    (tmVerify_eq_true_iff tmShaLeaf sb enc ts u).mpr
      ⟨hChain, hHeight, hMono, hDrift, hTrust, hEpochFold, hVsetFold, hThresh⟩
  exact tmNoForgery tmShaLeaf sb enc hcr ts u hverify

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
#assert_axioms chainCommit_binding
#assert_axioms tmDemoSigSound
#assert_axioms tmCollapse_not_CR
#assert_axioms tmShaLeaf_hash_eq_chainCommit
#assert_axioms vsetFold_derives_binding
#assert_axioms tmHashBindings_from_fold
#assert_axioms tm_hash_from_fold_slots_into_no_forgery

#print axioms tm_hash_from_fold_slots_into_no_forgery
#print axioms chainCommit_binding

end Dregg2.Circuit.Emit.LightClientTmHashFold
