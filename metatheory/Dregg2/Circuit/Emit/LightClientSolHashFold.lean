/-
# Dregg2.Circuit.Emit.LightClientSolHashFold — folding out the Solana SHA-256 HASH carrier
`STAKE_TABLE_OK`: the stake-table-root binding becomes DERIVED by an in-circuit SHA-256 collection
fold, not a trusted witnessed boolean carrier.

## The carrier being folded out (the SHA-256 stake-table hash — NOT the Ed25519 SIG carrier)

`LightClientSolanaAir` carries `STAKE_TABLE_OK`, a witnessed carrier bit standing for
`LightClientSolana.stakeTableOk L ts u = L.dBeq (L.tableCommit (u.table.map entryRow)) ts.anchorRoot` —
the SHA-256 `EpochStakeTable::root` compare: the derived active stake table binds to the
governance-pinned weak-subjectivity (WS) anchor root (the HOLE-2 denominator pin). In the carrier slice
`solLcAir_no_forgery` takes the honest-witness relation for this bit as a hypothesis — it TRUSTS the
prover set it to the true SHA-256 result. The verifier re-runs no hash.

This file replaces that trust with the SHA-256 fold itself, mirroring `LightClientEthExecFold` and
REUSING the proven `Sha256MerkleFold.pairHash` (via the `LightClientTmHashFold.chainCommit` collection
commit). The other Solana carrier — `ED_OK`, the aggregate Ed25519 vote-signature result — stays a
hypothesis (the Ed25519/EC arc; NOT this file); `ROOTED_OK`/`AUTH_OK` are the in-AIR logic gates.

## The SHA shape: the stake-table root, a flat COLLECTION hash over the sorted rows

`EpochStakeTable::root` is a domain-separated SHA-256 over the sorted `(votePubkey, authorizedVoter,
stake)` rows — a hash over the WHOLE stake table. This file REALIZES `tableCommit` as the
Merkle–Damgård chain `chainCommit` (`LightClientTmHashFold`) over the per-row 8-word leaf digests
(`solRowLeaf`), built ENTIRELY from the proven `pairHash` (House Law #1: no new SHA arithmetic). So a
satisfying witness must EXHIBIT the stake rows whose SHA-256 chain hits the pinned WS anchor root — the
`STAKE_TABLE_OK` carrier becomes DERIVED, and the ACTIVE-STAKE DENOMINATOR is pinned in-circuit.

## The ties proved here (mirroring the ETH exec fold's four theorems)

  * `solTableCommit_eq_chainCommit` — the bridge leaf's `tableCommit` IS the generator's SHA-256 row
    chain (the `reconstruct_*_eq_foldReconstruct` analog).
  * `solTable_binding_on` — GIVEN separation on the chain's OWN pairs (the HONEST floor), equal-length equal chain roots pin the whole row
    list: the SHA-256 stake-table commit BINDS the denominator (the commitment lemma, reduced to the
    proven pair-hash floor — the content behind `noTableCollision`).
  * `stakeTableOk_from_fold` (`verify*_from_fold` analog) — the `stakeTableOk` Boolean is DISCHARGED by
    the exhibited SHA fold: NO `STAKE_TABLE_OK` column is read.
  * `sol_stake_from_fold_gate_accepts` (carrier-free) + `sol_stake_binding_on` (the HONEST floor) — the
    fold-derived table binding slots into `sol_no_forgery` IN PLACE of the trusted bit: the Solana
    rooted-finality no-forgery guarantee holds with one fewer trusted carrier (the denominator pinned by
    the SHA-256 gates over the exhibited stake rows, not an opaque bit).

## What remains (the honest, PRICED residuals)

  * RESIDUAL #1 (proof-composition wall): `chainCommit (rows) = anchorRoot` is, in the deployed circuit,
    the CONCLUSION of the chained `sha256PairHash` gates forcing their SHA outputs up ~30k gates/block ×
    2 blocks × #rows. The atomic gates are forced + both-polarity KAT'd; the composition is the next
    slice. Here the fold is an explicit hypothesis, so DERIVED vs ASSUMED is visible.
  * RESIDUAL #2 (flat→chain modeling + full-table): `tableCommit` is realized as a Merkle–Damgård chain
    over per-row LEAF digests; the per-row leaf hashing and the exact domain-separated sort order are the
    named residual, and the chain is a BOUNDED (fixed-#rows) fold — the arbitrary-N table is the full
    residual. The KAT fixes the demo's 2-entry table.
  * RESIDUAL #3 (deploy/emit wall): the chained SHA fold cannot be flat-merged into `solLcVerifyDesc`'s
    byte-golden `emitVmJson2`; the deployed removal of `STAKE_TABLE_OK` routes through the IR-v2
    `proofBind` recursion seam (identical to the ETH lane). `solLcVerifyDesc` and its golden are
    UNTOUCHED — NO VK regen.
  * RESIDUAL #4 (Ed25519/EC arc): `ED_OK` stays a hypothesis — the aggregate vote-signature soundness is
    the Ed25519 leaf, the EC arc, not folded here.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`/`admit`/`native_decide`. The
`#guard` KATs anchor the 2-entry SHA-256 chain against an independently-computed SHA-256 vector
(`hashlib`, matching `Sha256MerkleFold` §0's FIPS anchoring), both polarities (a real chain value + a
tampered stake entry whose chain DIFFERS). `solShaLeaf` is the lawful SHA `SolLeaf` instance over the
real row chain; its `stakeTableCR` slot is `False`, because `SolLeaf.noTableCollision` demands global
injectivity of a compressing hash and `solTableInjective_false` REFUTES it with an executable
STAKE-INFLATION collision. The Ed25519 `edSound` is the demo/EC-arc slot. Imports read-only
(`LightClientTmHashFold`, transitively `Sha256MerkleFold`; `Bridge.LightClientSolana`).

## ⚑ 2026-07-27 — WHAT WAS DELETED AND WHY (the vacuity repair)

`sol_stake_from_fold_slots_into_no_forgery` is GONE, and `solTable_binding`'s `hpair` hypothesis with
it: both rested on injectivity of a compressing hash. Replacements are
`sol_stake_from_fold_gate_accepts` (carrier-free: the gates discharge `solVerify`) and
`solTable_binding_on` / `sol_stake_binding_on` (the binding, on `Sha256MerkleFold.pairSepOn`).
**CAPABILITY LOST, NAMED:** `SolValidAt`'s ∀-quantified table-binding conjunct is not derivable at a
compressing hash by any premise. ⚠ AND A NEW HOLE WAS SURFACED: `solRowLeaf` dropped the raw `Nat`
stake into one message word and `pairHash` reads a word only mod `2^64`, so the anchor root did not
pin the stake denominator even in principle without an encoder range-check that did not exist.

## ⚑ 2026-07-28 — THAT RESIDUAL IS CLOSED: the encoder is fixed-width and RANGE-GATED

The named residual is now a constraint. Three changes, all Lean-authored AIR (`Dregg2.Circuit.Emit.
StakeWidthRange`, generated from `AirBuilder.rangeNonneg`; no Rust hand-writes any of it):

  * `solRowLeaf` is FIXED-WIDTH — the stake occupies two 32-bit words, the faithful model of the
    deployed `stake.to_le_bytes()` (`bridge/src/solana_consensus.rs:203`) and the only shape an AIR
    whose word is 32 boolean columns can carry. Every KAT digest is UNCHANGED.
  * `solRowWidthGates` is the emitted per-row width check (`131` constraints/row: `32 + 32 + 64`
    boolean pins + three recompositions), and `solRowWidthGates_forces` proves a satisfying
    assignment puts the row `SolRowInRange`. The forcing lemma it rides,
    `StakeWidthRange.rangeNonneg_forces`, is the bite `AirBuilder.rangeNonneg` had never been given
    by anything in this tree.
  * `solTable_binding_on` / `sol_stake_binding_on` now take `SolTableInRange` on both tables, and
    `sol_denominator_pinned_on` states the payoff directly: two in-range tables at the same anchor
    root have the SAME TOTAL STAKE. The anchor pins the denominator.

The collision exhibit is DELIBERATELY KEPT (`solTable_stake_collision`) as the tooth: it shows the
gate is load-bearing, `solTable_stake_collision_out_of_range` shows its witness is refused, and
`solTable_stake_collision_unwitnessable` shows there is no satisfying assignment carrying it.
-/
import Dregg2.Circuit.Emit.LightClientTmHashFold
import Dregg2.Circuit.Emit.StakeWidthRange
import Dregg2.Bridge.LightClientSolana

namespace Dregg2.Circuit.Emit.LightClientSolHashFold

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.StakeWidthRange
open Dregg2.Circuit.Emit.Sha256MerkleFold
open Dregg2.Circuit.Emit.LightClientTmHashFold
open Dregg2.Bridge.LightClientSolana

set_option autoImplicit false
set_option maxRecDepth 8192

/-! ## §1 — The per-row leaf encoding + the SHA `SolLeaf`: `tableCommit = chainCommit ∘ map leaf`. -/

/-! ### The declared field widths — the DEPLOYED shapes, not model conveniences.

`SOL_WORD_BITS` is what a SHA-256 message word IS in the emitted AIR: 32 boolean columns
(`Sha256Gadget` §1). `SOL_STAKE_BITS` is the deployed stake width — `EpochStakeTable`'s
`BTreeMap<[u8; 32], u64>` (`bridge/src/solana_consensus.rs:132`), hashed into the root as
`stake.to_le_bytes()` (`solana_consensus.rs:203`), i.e. FIXED 8 bytes = exactly two 32-bit words. -/

/-- The AIR word width: a SHA-256 message word is 32 boolean columns. -/
def SOL_WORD_BITS : Nat := 32
/-- The deployed stake width: `u64` lamports, hashed fixed-width as `stake.to_le_bytes()`. -/
def SOL_STAKE_BITS : Nat := 64

/-- A stake-table row `(votePubkey, authorizedVoter, stake)` as an 8-word leaf digest (the row's leaf
in the stake-table commit).

⚑ 2026-07-28 — THE STAKE IS FIXED-WIDTH, in TWO words. It used to be `[tag, vp, av, stk, 0,0,0,0]`,
dropping the raw unbounded `Nat` into ONE message word, which is (a) not representable in the emitted
AIR at all, where a word is 32 boolean columns, and (b) not what the deployed Rust hashes — `root()`
feeds `stake.to_le_bytes()`, a FIXED 8 bytes. The stake now occupies the low and high 32-bit words,
which is the faithful model of that encoding and the only shape the AIR can carry.

Being fixed-width, the encoder TRUNCATES above `2^64` and is therefore NOT injective — that is not a
regression, it is the defect made honest and local: `solTable_stake_collision` still exhibits it, and
`solRowLeaf_inj_on_range` proves the truncation is invisible once the width gate
(`solRowWidthGates`) is present. Every KAT digest below is UNCHANGED, because every demo stake is
`< 2^32` and the high word is `0` exactly where the old encoding already had `0`.

RESIDUAL (named, unchanged): `vp`/`av` are ONE-word demo pubkey ids; a real Solana vote account is 32
bytes = eight words, and the deployed `root()` preimage also carries the epoch and the row count. The
row shape is the demo's; the WIDTH DISCIPLINE proved here is not. -/
def solRowLeaf : Nat × Nat × Nat → List Nat
  | (vp, av, stk) => [0x766f7465, vp, av, stk % 2 ^ 32, stk / 2 ^ 32 % 2 ^ 32, 0, 0, 0]

/-! ### The width predicate the gate forces, and the gate that forces it. -/

/-- **A stake-table row is IN RANGE** when every field fits the width the encoder declares: the two
demo pubkey ids in one 32-bit word each, the stake in its `u64`. -/
def SolRowInRange (r : Nat × Nat × Nat) : Prop :=
  r.1 < 2 ^ SOL_WORD_BITS ∧ r.2.1 < 2 ^ SOL_WORD_BITS ∧ r.2.2 < 2 ^ SOL_STAKE_BITS

instance : DecidablePred SolRowInRange := fun r => by
  unfold SolRowInRange; infer_instance

/-- **A stake TABLE is in range** when every row is. -/
def SolTableInRange (t : List (Nat × Nat × Nat)) : Prop := ∀ r ∈ t, SolRowInRange r

instance : DecidablePred SolTableInRange := fun t => by
  unfold SolTableInRange; infer_instance

/-- **THE STAKE-TABLE ROW WIDTH GATES — LEAN-AUTHORED AIR.** Per row: one
`StakeWidthRange.widthGate` per field, i.e. `32 + 32 + 64 = 128` boolean pins and three
recomposition gates (`131` constraints/row). `bit0` is the row's first fresh bit column; the three
fields' bit windows are disjoint by construction.

This is the constraint the whole repair turns on, and it is generated here, in Lean, from
`AirBuilder.rangeNonneg` — no Rust hand-writes it. -/
def solRowWidthGates (vpCol avCol stkCol bit0 : Nat) : List VmConstraint2 :=
  widthGate vpCol bit0 SOL_WORD_BITS
  ++ widthGate avCol (bit0 + SOL_WORD_BITS) SOL_WORD_BITS
  ++ widthGate stkCol (bit0 + 2 * SOL_WORD_BITS) SOL_STAKE_BITS

/-- The emitted budget: `33 + 33 + 65 = 131` constraints per stake-table row. -/
theorem solRowWidthGates_length (vpCol avCol stkCol bit0 : Nat) :
    (solRowWidthGates vpCol avCol stkCol bit0).length = 131 := by
  simp [solRowWidthGates, widthGate, rangeNonneg, bitsFrom, SOL_WORD_BITS, SOL_STAKE_BITS]

/-- **THE ROW GATES FORCE THE ROW'S WIDTHS.** A satisfying assignment whose three value columns carry
the row's fields puts the row IN RANGE. This is the bridge from the emitted AIR to the model-side
predicate every theorem below quantifies over. -/
theorem solRowWidthGates_forces (a : Assignment) (r : Nat × Nat × Nat)
    (vpCol avCol stkCol bit0 : Nat)
    (hvp : a vpCol = (r.1 : ℤ)) (hav : a avCol = (r.2.1 : ℤ)) (hstk : a stkCol = (r.2.2 : ℤ))
    (hbVp : ∀ c ∈ bitsFrom bit0 SOL_WORD_BITS, (gBin c).eval a = 0)
    (hrVp : evalH (recompHead (Head.lin 1 vpCol) (bitsFrom bit0 SOL_WORD_BITS)) a = 0)
    (hbAv : ∀ c ∈ bitsFrom (bit0 + SOL_WORD_BITS) SOL_WORD_BITS, (gBin c).eval a = 0)
    (hrAv : evalH (recompHead (Head.lin 1 avCol)
              (bitsFrom (bit0 + SOL_WORD_BITS) SOL_WORD_BITS)) a = 0)
    (hbStk : ∀ c ∈ bitsFrom (bit0 + 2 * SOL_WORD_BITS) SOL_STAKE_BITS, (gBin c).eval a = 0)
    (hrStk : evalH (recompHead (Head.lin 1 stkCol)
              (bitsFrom (bit0 + 2 * SOL_WORD_BITS) SOL_STAKE_BITS)) a = 0) :
    SolRowInRange r :=
  ⟨widthGate_forces a r.1 vpCol bit0 SOL_WORD_BITS hvp hbVp hrVp,
   widthGate_forces a r.2.1 avCol (bit0 + SOL_WORD_BITS) SOL_WORD_BITS hav hbAv hrAv,
   widthGate_forces a r.2.2 stkCol (bit0 + 2 * SOL_WORD_BITS) SOL_STAKE_BITS hstk hbStk hrStk⟩

/-- **THE ENCODER IS INJECTIVE ON IN-RANGE ROWS.** Equal leaves force equal rows once the width gate
is present — the fixed-width truncation is invisible below `2^64`. Without the range hypothesis this
is FALSE (`solTable_stake_collision`), so the hypothesis is load-bearing, not decoration. -/
theorem solRowLeaf_inj_on_range (r₁ r₂ : Nat × Nat × Nat)
    (h₁ : SolRowInRange r₁) (h₂ : SolRowInRange r₂) (h : solRowLeaf r₁ = solRowLeaf r₂) :
    r₁ = r₂ := by
  obtain ⟨a₁, b₁, c₁⟩ := r₁
  obtain ⟨a₂, b₂, c₂⟩ := r₂
  simp only [SolRowInRange, SOL_WORD_BITS, SOL_STAKE_BITS] at h₁ h₂
  simp only [solRowLeaf, List.cons.injEq] at h
  obtain ⟨-, hva, hvb, hlo, hhi, -⟩ := h
  have hc : c₁ = c₂ := by
    have hd₁ : c₁ / 2 ^ 32 < 2 ^ 32 := by omega
    have hd₂ : c₂ / 2 ^ 32 < 2 ^ 32 := by omega
    rw [Nat.mod_eq_of_lt hd₁, Nat.mod_eq_of_lt hd₂] at hhi
    omega
  simp only [Prod.mk.injEq]
  exact ⟨hva, hvb, hc⟩

/-- The list lift: equal leaf lists over in-range tables force equal tables. -/
theorem solRows_eq_of_leaves_eq :
    ∀ (t₁ t₂ : List (Nat × Nat × Nat)), SolTableInRange t₁ → SolTableInRange t₂ →
      t₁.map solRowLeaf = t₂.map solRowLeaf → t₁ = t₂ := by
  intro t₁
  induction t₁ with
  | nil =>
    intro t₂ _ _ h
    cases t₂ with
    | nil => rfl
    | cons _ _ => simp at h
  | cons r rest ih =>
    intro t₂ h₁ h₂ h
    cases t₂ with
    | nil => simp at h
    | cons r' rest' =>
      simp only [List.map_cons, List.cons.injEq] at h
      have hr : r = r' :=
        solRowLeaf_inj_on_range r r' (h₁ r (by simp)) (h₂ r' (by simp)) h.1
      have htail : rest = rest' :=
        ih rest' (fun x hx => h₁ x (by simp [hx])) (fun x hx => h₂ x (by simp [hx])) h.2
      rw [hr, htail]

/-- Demo Ed25519-slot verifier (genuine key `7`, genuine sig `7`): the EC-arc residual, NOT folded. -/
def solEdVerify (pk : Nat) (_m : Nat × List Nat) (s : Nat) : Bool :=
  decide (pk = 7) && decide (s = 7)

/-- Demo `Signed` denotation: the genuine authorized voter is key `7`. -/
def solSigned (pk : Nat) (_m : Nat × List Nat) : Prop := pk = 7

/-- The demo Ed25519-soundness leaf, PROVED (the `edSound` slot). -/
theorem solEdSound (pk : Nat) (m : Nat × List Nat) (s : Nat)
    (h : solEdVerify pk m s = true) : solSigned pk m := by
  simp only [solEdVerify, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- **The IDEALIZED stake-table-CR floor, NAMED so it can be REFUTED rather than assumed.** This is
the exact `Prop` `solShaLeaf.stakeTableCR` used to hold. -/
def solTableInjective : Prop :=
  ∀ t₁ t₂ : List (Nat × Nat × Nat),
    chainCommit (t₁.map solRowLeaf) = chainCommit (t₂.map solRowLeaf) → t₁ = t₂

set_option maxRecDepth 8192 in
/-- ⚑ **THE STAKE DENOMINATOR IS NOT BOUND BY THE ANCHOR ALONE — an executable STAKE-INFLATION
collision, KEPT as the tooth.** A table with stake `50` and one with stake `50 + 2^64` produce the
SAME stake-table root. Two tables with WILDLY different `totalStake` share an anchor root, so the
anchor by itself pins no denominator at all.

The mechanism was, and after the 2026-07-28 encoder repair still is, a `2^64` truncation — only now
it is LOCAL to the encoder instead of buried in the hash: `solRowLeaf` keeps the stake's low and high
32-bit words and drops everything above, and independently `pairHash` reads a message word only
modulo `2^64` (`Sha256MerkleFold.pairHash_ignores_bits_above_64`), so an encoder without a width
gate is non-injective at the digest whichever of the two you look at.

⚑ THIS THEOREM IS THE REASON THE WIDTH GATE IS LOAD-BEARING, and it is deliberately NOT deleted:
`solTable_stake_collision_out_of_range` proves its second table is refused by
`solRowWidthGates`, and `solTable_binding_on` shows the binding conclusion IS recovered once the
gate is present. Delete the gate and this exhibit comes straight back. -/
theorem solTable_stake_collision :
    chainCommit (([(1, 7, 50)] : List (Nat × Nat × Nat)).map solRowLeaf)
      = chainCommit (([(1, 7, 50 + 2 ^ 64)] : List (Nat × Nat × Nat)).map solRowLeaf) := by
  decide

/-- **THE IDEALIZED STAKE-TABLE-CR FLOOR IS FALSE**, by witness. -/
theorem solTableInjective_false : ¬ solTableInjective := by
  intro h
  exact absurd (h _ _ solTable_stake_collision) (by decide)

/-! ### ⚑ 2026-07-28 — THE COLLISION IS NOW UNREACHABLE: the width gate refuses its witness.

The residual the 2026-07-27 repair NAMED ("the missing encoder range-check") is closed here. The
three statements are: the exhibit's second table is REFUSED by the gate; the whole `2^64`-alias
family collapses to a point in range; and the collision is therefore not merely unexhibited but
UNWITNESSABLE — no satisfying assignment for `solRowWidthGates` carries it. -/

/-- **THE INFLATED TABLE IS OUT OF RANGE** — the collision's second witness is refused by the width
predicate the gate forces, while the honest one is admitted. -/
theorem solTable_stake_collision_out_of_range :
    SolTableInRange [(1, 7, 50)] ∧ ¬ SolTableInRange [((1, 7, 50 + 2 ^ 64) : Nat × Nat × Nat)] := by
  constructor
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨by decide, by decide, by decide⟩
  · intro h
    have := (h (1, 7, 50 + 2 ^ 64) (by simp)).2.2
    simp only [SOL_STAKE_BITS] at this
    omega

/-- **THE `2^64`-ALIAS FAMILY COLLAPSES IN RANGE.** A row whose stake has been shifted by `k·2^64` —
the exact family the truncation generates — is in range only when `k = 0`. -/
theorem solRow_stake_alias_collapses (r : Nat × Nat × Nat) (k : Nat)
    (h : SolRowInRange (r.1, r.2.1, r.2.2 + k * 2 ^ SOL_STAKE_BITS)) : k = 0 :=
  alias_collapses_in_range SOL_STAKE_BITS r.2.2 k h.2.2

/-- **NO TABLE THE GATE ADMITS CARRIES AN INFLATED ROW.** The table-level form: an in-range stake
table cannot contain a `k·2^64`-shifted row for nonzero `k`. -/
theorem solTable_stake_alias_unreachable (t : List (Nat × Nat × Nat)) (r : Nat × Nat × Nat) (k : Nat)
    (ht : SolTableInRange t)
    (hmem : ((r.1, r.2.1, r.2.2 + k * 2 ^ SOL_STAKE_BITS) : Nat × Nat × Nat) ∈ t) : k = 0 :=
  solRow_stake_alias_collapses r k (ht _ hmem)

/-- ⚑ **THE COLLISION IS UNWITNESSABLE UNDER THE EMITTED GATE.** Not "no collision is known" — there
is NO satisfying assignment for `solRowWidthGates` whose stake column carries the exhibit's inflated
value. The forcing lemma is the whole content; this is it applied to the exact witness on the
record. -/
theorem solTable_stake_collision_unwitnessable (a : Assignment)
    (stkCol bit0 : Nat)
    (hstk : a stkCol = ((50 + 2 ^ 64 : Nat) : ℤ))
    (hbStk : ∀ c ∈ bitsFrom (bit0 + 2 * SOL_WORD_BITS) SOL_STAKE_BITS, (gBin c).eval a = 0)
    (hrStk : evalH (recompHead (Head.lin 1 stkCol)
              (bitsFrom (bit0 + 2 * SOL_WORD_BITS) SOL_STAKE_BITS)) a = 0) :
    False :=
  widthGate_refuses a (50 + 2 ^ 64) stkCol (bit0 + 2 * SOL_WORD_BITS) SOL_STAKE_BITS
    (by simp only [SOL_STAKE_BITS]; omega) hstk hbStk hrStk

/-- **`solShaLeaf`** — the lawful SHA `SolLeaf` whose `tableCommit` IS the SHA-256 collection chain
(`chainCommit` over the per-row `solRowLeaf` digests). The Ed25519 fields are the demo/EC-arc slot.

⚑ 2026-07-27 — `stakeTableCR` used to be the idealized injectivity of `chainCommit ∘ map solRowLeaf`,
described as "the genuine table-CR floor". `SolLeaf.noTableCollision` demands the carrier ENTAIL
exactly that, and it is FALSE (`solTableInjective_false` — and the witness is a stake-inflation
collision, not a pigeonhole appeal). So every theorem taking `hcr : solShaLeaf.stakeTableCR` proved
nothing. The slot is now `False`; the binding content rides `solTable_binding_on` on the HONEST
floor `Sha256MerkleFold.pairSepOn`. -/
@[reducible] def solShaLeaf : SolLeaf where
  PubKey := Nat
  Digest := List Nat
  Sig := Nat
  pkeq := inferInstance
  deqD := inferInstanceAs (DecidableEq (List Nat))
  edVerify := solEdVerify
  Signed := solSigned
  edSound := solEdSound
  tableCommit := fun rows => chainCommit (rows.map solRowLeaf)
  stakeTableCR := False
  noTableCollision := fun h => h.elim
  zeroSig := 0
  zeroDigest := chainIV

/-! ### The floor's THREE legs (the audited guard tested only the middle one). -/

/-- A COLLAPSING table commit (every table digests to the zero root). -/
def solCollapseCommit (_ : List (Nat × Nat × Nat)) : List Nat := chainIV

/-- **REFUTABLE at a collapsing hash (the guard that already existed).** Two DIFFERENT tables share
the root. This tests only that the SHAPE can be false; it says nothing about SATISFIABILITY at the
real hash, which is the leg that was missing and at which the answer is NO
(`solTableInjective_false`). -/
theorem solCollapse_not_CR :
    ¬ (∀ t₁ t₂ : List (Nat × Nat × Nat), solCollapseCommit t₁ = solCollapseCommit t₂ → t₁ = t₂) := by
  intro h
  exact absurd (h [(1, 7, 50)] [(2, 7, 50)] rfl) (by decide)

/-! ## §2 — The four fold theorems (mirroring the ETH exec fold), for the `STAKE_TABLE_OK` carrier. -/

/-- **THE TIE (`reconstruct_*_eq_foldReconstruct` analog).** The bridge leaf's `tableCommit` IS the
generator's SHA-256 row chain — the object `STAKE_TABLE_OK` stood for, via the SHA arithmetic. -/
theorem solTableCommit_eq_chainCommit (rows : List (Nat × Nat × Nat)) :
    solShaLeaf.tableCommit rows = chainCommit (rows.map solRowLeaf) := rfl

/-- **THE STAKE-TABLE COMMIT BINDS, at the HONEST floor AND THE EMITTED WIDTH GATE.** Equal-length
IN-RANGE tables whose SHA-256 row chains agree ARE the same table — so the WS-anchor-pinned root pins
the ACTIVE-STAKE DENOMINATOR — GIVEN separation on the two chains' OWN pairs
(`Sha256MerkleFold.pairSepOn` + `ChainCovered`) instead of the refuted global injectivity of
`pairHash`, and GIVEN that both tables satisfy `solRowWidthGates` (`SolTableInRange`).

⚑ 2026-07-28 — the two range hypotheses are NEW and LOAD-BEARING. Drop either and the conclusion is
FALSE by `solTable_stake_collision`: the encoder truncates at `2^64` and `pairHash` reads a message
word only mod `2^64`, so a stake-inflated table hits the same root. `solRowWidthGates_forces`
discharges them from the emitted gates, so this is not a new trust assumption — it is a constraint
the circuit now carries. -/
theorem solTable_binding_on (P : List Nat → List Nat → Prop) (hsep : pairSepOn P)
    (t₁ t₂ : List (Nat × Nat × Nat)) (hlen : t₁.length = t₂.length)
    (hr₁ : SolTableInRange t₁) (hr₂ : SolTableInRange t₂)
    (hc₁ : ChainCovered P chainIV (t₁.map solRowLeaf))
    (hc₂ : ChainCovered P chainIV (t₂.map solRowLeaf))
    (h : solShaLeaf.tableCommit t₁ = solShaLeaf.tableCommit t₂) : t₁ = t₂ := by
  have hleaf : t₁.map solRowLeaf = t₂.map solRowLeaf :=
    chainCommit_binding_on P hsep (t₁.map solRowLeaf) (t₂.map solRowLeaf)
      (by simp [hlen]) hc₁ hc₂ h
  -- `solRowLeaf` is injective ON IN-RANGE ROWS (and only there), so equal leaf lists force equal
  -- row lists.
  exact solRows_eq_of_leaves_eq t₁ t₂ hr₁ hr₂ hleaf

/-- **THE CARRIER CONTENT, DERIVED from the SHA fold (`*_fold_derives_*` analog).** The fold gates force
the chain root `= chainCommit (rows)` (RESIDUAL #1, an explicit hypothesis here), and the publish/bind
forces that root `= anchorRoot`; therefore the stake rows hash to the pinned anchor — the
`STAKE_TABLE_OK` content, from the exhibited rows, not a bit. -/
theorem stakeFold_derives_anchorBinding (rows : List (Nat × Nat × Nat)) (root anchor : List Nat)
    (hforce : root = chainCommit (rows.map solRowLeaf)) (hbind : root = anchor) :
    chainCommit (rows.map solRowLeaf) = anchor := by
  rw [← hforce, hbind]

/-- **THE `STAKE_TABLE_OK` CARRIER DISCHARGED by the exhibited SHA fold (`verify*_from_fold` analog) —
NO carrier bit read.** Given the SHA-256 chain reconstructing the stake rows into the pinned WS anchor
root, the bridge's `stakeTableOk` Boolean is `true`. A satisfying prover must EXHIBIT stake rows whose
SHA-256 chain hits the anchor; there is no witnessed carrier to set. -/
theorem stakeTableOk_from_fold (ts : SolTrustedState solShaLeaf) (u : SolUpdate solShaLeaf)
    (hfold : chainCommit ((u.table.map entryRow).map solRowLeaf) = ts.anchorRoot) :
    stakeTableOk solShaLeaf ts u = true := by
  unfold stakeTableOk
  exact solShaLeaf.dBeq_iff.mpr hfold

/-- **THE PAYOFF, CARRIER-FREE: the fold-derived table binding DISCHARGES THE WHOLE SOLANA GATE.**
Given the `total > 0` floor, the ≥2/3 rooted-stake threshold, and the Ed25519 / rooted /
authorized-voter results, if the stake rows' SHA-256 chain reconstructs into the pinned WS anchor
root (`hfold` — DERIVED from the exhibited rows, not a witnessed bit), `solVerify` accepts. No
`STAKE_TABLE_OK` bit is read and NO hash floor is used.

⚑ 2026-07-27 — this replaces `sol_stake_from_fold_slots_into_no_forgery`, which concluded
`SolValidAt` from `hcr : solShaLeaf.stakeTableCR`, REFUTED by an executable STAKE-INFLATION collision
(`solTableInjective_false`). **CAPABILITY LOST, NAMED:** `SolValidAt`'s ∀-quantified table-binding
conjunct is not derivable at a compressing hash by any premise. What replaces it is the PAIRWISE
form (`solTable_binding_on`). ⚠ AND THE WITNESS IS ITS OWN FINDING: `solRowLeaf` drops the raw `Nat`
stake into one message word, and `pairHash` reads a word only mod `2^64` — so even the pairwise form
is only as good as a range-check on the encoder. That range-check does not exist here; it is the
named residual this repair surfaces rather than hides. -/
theorem sol_stake_from_fold_gate_accepts
    (ts : SolTrustedState solShaLeaf) (u : SolUpdate solShaLeaf)
    (hpos : 0 < totalStake solShaLeaf u)
    (hthr : 2 * totalStake solShaLeaf u ≤ 3 * rootedStake solShaLeaf u)
    (hed : edOk solShaLeaf u = true)
    (hrooted : rootedOk solShaLeaf u = true)
    (hauth : authOk solShaLeaf u = true)
    (hfold : chainCommit ((u.table.map entryRow).map solRowLeaf) = ts.anchorRoot) :
    solVerify solShaLeaf ts u = true := by
  have hstk : stakeTableOk solShaLeaf ts u = true := stakeTableOk_from_fold ts u hfold
  unfold solVerify solVerifyDecision
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨hpos, hthr⟩, hed⟩, hstk⟩, hrooted⟩, hauth⟩

/-- **THE STAKE DENOMINATOR IS BOUND, at the HONEST floor AND THE WIDTH GATE.** Two equal-length
IN-RANGE stake tables whose SHA-256 row chains both hit the SAME pinned anchor root ARE the same
table — GIVEN separation on the two chains' own pairs. This is what `STAKE_TABLE_OK` stood for. -/
theorem sol_stake_binding_on (P : List Nat → List Nat → Prop) (hsep : pairSepOn P)
    (t₁ t₂ : List (Nat × Nat × Nat)) (anchor : List Nat) (hlen : t₁.length = t₂.length)
    (hr₁ : SolTableInRange t₁) (hr₂ : SolTableInRange t₂)
    (hc₁ : ChainCovered P chainIV (t₁.map solRowLeaf))
    (hc₂ : ChainCovered P chainIV (t₂.map solRowLeaf))
    (h₁ : chainCommit (t₁.map solRowLeaf) = anchor)
    (h₂ : chainCommit (t₂.map solRowLeaf) = anchor) : t₁ = t₂ :=
  solTable_binding_on P hsep t₁ t₂ hlen hr₁ hr₂ hc₁ hc₂ (h₁.trans h₂.symm)

/-- ⚑ **THE ANCHOR NOW PINS THE DENOMINATOR — the statement the finding said was false.** Two
in-range stake tables that both hit the pinned WS anchor root have the SAME TOTAL STAKE, so the
`≥ 2/3` threshold `solVerifyDecision` computes is computed against a denominator the anchor fixes.
Before the width gate this was refutable at the same anchor root (`solTable_stake_collision`: totals
`50` and `50 + 2^64`); it is now a theorem, on the honest hash floor. -/
theorem sol_denominator_pinned_on (P : List Nat → List Nat → Prop) (hsep : pairSepOn P)
    (t₁ t₂ : List (Nat × Nat × Nat)) (anchor : List Nat) (hlen : t₁.length = t₂.length)
    (hr₁ : SolTableInRange t₁) (hr₂ : SolTableInRange t₂)
    (hc₁ : ChainCovered P chainIV (t₁.map solRowLeaf))
    (hc₂ : ChainCovered P chainIV (t₂.map solRowLeaf))
    (h₁ : chainCommit (t₁.map solRowLeaf) = anchor)
    (h₂ : chainCommit (t₂.map solRowLeaf) = anchor) :
    (t₁.map (fun r => r.2.2)).sum = (t₂.map (fun r => r.2.2)).sum :=
  congrArg (fun t : List (Nat × Nat × Nat) => (t.map (fun r => r.2.2)).sum)
    (sol_stake_binding_on P hsep t₁ t₂ anchor hlen hr₁ hr₂ hc₁ hc₂ h₁ h₂)

/-! ## §3 — KATs: the 2-entry SHA-256 chain, anchored to an independent SHA-256 vector.

Both-polarity, non-vacuous: a genuine 2-entry chain value computed independently (`hashlib`, matching
`Sha256MerkleFold` §0's FIPS anchoring), and a tampered entry (stake `50 → 99`, a self-stake/denominator
inflation) whose chain DIFFERS (the denominator binding is not vacuous). These reduce in the kernel. -/

/-- Stake entry #1 (vote account 1, authorized voter 7, stake 50). -/
def solRow1 : Nat × Nat × Nat := (1, 7, 50)
/-- Stake entry #2 (vote account 2, authorized voter 7, stake 50). -/
def solRow2 : Nat × Nat × Nat := (2, 7, 50)
/-- The 2-entry stake table (the demo `modelTable` set — total stake 100). -/
def solRows : List (Nat × Nat × Nat) := [solRow1, solRow2]

-- Positive: the real 2-entry SHA-256 chain (stake_table_root), independently computed (hashlib).
#guard chainCommit (solRows.map solRowLeaf) ==
  [0x809d59f7, 0x921ec66f, 0x5ae9ef58, 0x0ced15f6, 0x62163500, 0xe7ce29e9, 0x7ddf1989, 0xa8335465]
-- Negative (discrimination): entry 2's stake 50 → 99 changes the table root.
#guard chainCommit ([solRow1, (2, 7, 99)].map solRowLeaf) !=
  [0x809d59f7, 0x921ec66f, 0x5ae9ef58, 0x0ced15f6, 0x62163500, 0xe7ce29e9, 0x7ddf1989, 0xa8335465]
-- The chain's single-step law reduces (the IV-anchored first block).
#guard chainCommit [solRowLeaf solRow1] == pairHash chainIV (solRowLeaf solRow1)

/-! ## §4 — axiom hygiene. -/

#assert_axioms solEdSound
#assert_axioms solCollapse_not_CR
#assert_axioms solTable_stake_collision
#assert_axioms solTableInjective_false
#assert_axioms solTableCommit_eq_chainCommit
#assert_axioms solTable_binding_on
#assert_axioms stakeFold_derives_anchorBinding
#assert_axioms stakeTableOk_from_fold
#assert_axioms sol_stake_from_fold_gate_accepts
#assert_axioms sol_stake_binding_on
#assert_axioms solRowWidthGates_length
#assert_axioms solRowWidthGates_forces
#assert_axioms solRowLeaf_inj_on_range
#assert_axioms solRows_eq_of_leaves_eq
#assert_axioms solTable_stake_collision_out_of_range
#assert_axioms solRow_stake_alias_collapses
#assert_axioms solTable_stake_alias_unreachable
#assert_axioms solTable_stake_collision_unwitnessable
#assert_axioms sol_denominator_pinned_on

#print axioms sol_stake_from_fold_gate_accepts
#print axioms solTable_binding_on

end Dregg2.Circuit.Emit.LightClientSolHashFold
