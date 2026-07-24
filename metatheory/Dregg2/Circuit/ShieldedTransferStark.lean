/-
# Dregg2.Circuit.ShieldedTransferStark — DEBT-A side-brick: scope + reduce the ONE
  deployed effect (`ShieldedTransfer`) DEBT-B classified as DEBT-A.

HONEST SCOPE (first paragraph). DEBT-B proved finite-map commuting squares for 32/33 deployed
effects; `Promise`/`Notify` are off-kernel; `ShieldedTransfer` was the ONE left as DEBT-A because
its acceptance carries a STARK-soundness obligation (`verify_stark_side`). This file SPLITS that
obligation exactly against the DEPLOYED code and proves the part that is provable NOW without any
crypto carrier: the **kernel part** of an accepted shielded transfer is EXACTLY a fold of the
already-covered `noteSpendNullifier` primitive — bal-neutral, commitment-neutral, growing the
nullifier set by precisely the domain-separated keys — and acceptance is EQUIVALENT to
"keys distinct ∧ all fresh" (both-truth, no vacuity). The **STARK residual** is then named as a
precise `Prop` over the deployed 3-slot public-input tuple `[nullifier, merkle_root, value_binding]`
and shown to reduce to the SAME FRI/AIR floor `StarkSound` packages (at the hiding uni-STARK config),
PLUS the explicitly-named side floors of §5 — NOT a new carrier. NAMING IS FAKING: the residual's
extractor is an explicit HYPOTHESIS, never a `def`-used-as-proof.

## ⚑ REPAIR 2026-07-24 — `StarkResidual` carries the C6↔C7a TIE (it did not before).

`Dregg2.Verify.ExistsImageVacuity` §5 proved the residual as previously stated VACUOUS: its
`value`/`randomness` witnesses occurred in no conjunct that mentioned `commitment`, so the obligation
was independent of the deployed public input `pi[2] = value_binding`
(`starkResidual_indep_of_valueBinding`), held for EVERY public-input triple at any root with one
member (`starkResidual_vacuous`), and its `extract` premise was inhabited with no crypto at all
(`starkResidual_floor_prices_nothing`). §4 below now states the obligation with the tie: ONE opening
`(value, asset, owner, randomness)` commits the member leaf, derives the nullifier, AND opens the
published value binding. The pre-repair shape is kept verbatim as `StarkResidualUntied` — the vacuity
teeth are about THAT object and remain true of it — and `starkResidual_untied_of_starkResidual`
proves the strengthening loses nothing. §5 gains the tie as a FOURTH named floor; its absence from
that list is precisely how the vacuity hid.

## The DEPLOYED split (read from `turn/src/executor/apply.rs :: apply_shielded_transfer`, ~1160).

An accepted shielded transfer runs three fail-closed gates. Splitting by WHAT TOUCHES THE KERNEL:

  (A) **KERNEL part — the ONLY committed mutation (GATE 3, `apply.rs`).** For each input the executor
      derives a 32-byte set key `shielded_nullifier_key(nf) = blake3_derive_key("dregg-shielded-
      nullifier v1", nf_le)` from the circuit's BabyBear field nullifier, pre-checks NONE are already
      in the production `note_nullifiers` set, then inserts each once (journaled). The recorded note
      *value* is the literal `0` (the STAGE-B placeholder the deployed comment flags): the shielded
      amount lives in a hidden Pedersen commitment and NEVER touches the transparent `bal` ledger.
      **So on the kernel, `ShieldedTransfer` = a sequence of nullifier-set inserts — nothing else.**
      This is a COVERED shape: it is iterated `noteSpendNullifier` (`RecordKernel.lean:966`), whose
      commuting square DEBT-B proved as `FinProgramSquares.noteSpendStmt_square:300`.

  (B) **STARK part — NOT a kernel mutation.** `verify_stark_side` (`circuit-prove/src/shielded/
      transfer.rs:146`) checks, per input, a hiding uni-STARK (`verify_dsl_zk`, `DslZkProof` over
      `HidingFriPcs`) against the shielded-spend AIR (`spend_circuit.rs`, constraints C1–C7b) with the
      DEPLOYED public-input tuple **`pi = [nullifier, merkle_root, value_binding]`** (`transfer.rs:89`,
      `spend_circuit.rs:146` `PUBLIC_INPUT_COUNT = 3`), and rejects any in-transfer duplicate nullifier
      (`DuplicateNullifier`). The value balance is a SEPARATE Pedersen leg
      (`verify_full_conservation_bytes` + one Bulletproof range proof per output, `apply.rs` GATE 2),
      Fiat-Shamir-bound to the STARK via `transfer_message`.

This module proves (A) in full and names (B) precisely with its floor reduction.
-/
import Dregg2.Exec.RecordKernel

namespace Dregg2.Circuit.ShieldedTransferStark

open Dregg2.Exec

/-! ## §1 — The KERNEL part: iterated `noteSpendNullifier` over the derived keys.

`shieldedTransferK k keys` is the deployed GATE-3 effect on kernel state: consume each key once,
fail-closed (`none`) on the first key already present. It is a verbatim fold of the SAME
`noteSpendNullifier` primitive DEBT-B's covered `noteSpendStmt` square models — the shielded transfer
adds NO new kernel verb. (`keys` are the post-`shielded_nullifier_key` 32-byte set keys, carried here
as the `Nat` set elements the deployed `note_nullifiers` set holds.) -/
def shieldedTransferK : RecordKernelState → List Nat → Option RecordKernelState
  | k, []         => some k
  | k, nf :: rest => (noteSpendNullifier k nf).bind (fun k' => shieldedTransferK k' rest)

/-- Peel one committed `noteSpendNullifier`: it fired ⇒ the key was fresh, and the ONLY change is the
nullifier cons (bal / commitments / cells / caps / revoked untouched). -/
theorem noteSpendNullifier_shape {k k' : RecordKernelState} {nf : Nat}
    (h : noteSpendNullifier k nf = some k') :
    nf ∉ k.nullifiers ∧ k' = { k with nullifiers := nf :: k.nullifiers } := by
  unfold noteSpendNullifier at h
  by_cases hin : nf ∈ k.nullifiers
  · rw [if_pos hin] at h; exact absurd h (by simp)
  · rw [if_neg hin] at h
    simp only [Option.some.injEq] at h
    exact ⟨hin, h.symm⟩

/-! ## §2 — THE DEBT-A KEYSTONE: the kernel part of an ACCEPTED shielded transfer, characterized.

An accepted `shieldedTransferK` is EXACTLY: grow the nullifier set by `keys.reverse`, touch NOTHING
else, and this is possible IFF the keys are pairwise-distinct and every one is fresh. The `↔`-strength
`shieldedTransferK_accepts` gives both-truth (accept ⟺ distinct+fresh, so the gate is neither vacuously
true nor vacuously false); the projections make the "bal-neutral nullifier-advance only" claim a
theorem over the deployed effect. This is the reduction to already-covered programs: every step IS the
covered `noteSpendNullifier` (`noteSpendStmt_square:300`), nothing more. -/
theorem shieldedTransferK_accepts :
    ∀ (keys : List Nat) (k k' : RecordKernelState),
      shieldedTransferK k keys = some k' →
        k'.nullifiers = keys.reverse ++ k.nullifiers
        ∧ k'.bal = k.bal ∧ k'.commitments = k.commitments
        ∧ k'.cell = k.cell ∧ k'.accounts = k.accounts
        ∧ k'.caps = k.caps ∧ k'.revoked = k.revoked
        ∧ keys.Nodup ∧ ∀ nf ∈ keys, nf ∉ k.nullifiers := by
  intro keys
  induction keys with
  | nil =>
      intro k k' h
      simp only [shieldedTransferK, Option.some.injEq] at h
      subst h
      refine ⟨by simp, rfl, rfl, rfl, rfl, rfl, rfl, List.nodup_nil, ?_⟩
      intro nf hnf; exact absurd hnf (by simp)
  | cons nf rest ih =>
      intro k k' h
      simp only [shieldedTransferK] at h
      cases hns : noteSpendNullifier k nf with
      | none => rw [hns] at h; exact absurd h (by simp)
      | some k1 =>
          rw [hns] at h
          simp only [Option.bind_some] at h
          obtain ⟨hfresh, hk1⟩ := noteSpendNullifier_shape hns
          subst hk1
          obtain ⟨hnull, hbal, hcom, hcell, hacc, hcap, hrev, hnod, hfree⟩ := ih _ _ h
          -- `nf ∉ rest`: every element of `rest` is fresh against `nf :: k.nullifiers`.
          have hnf_notin_rest : nf ∉ rest := by
            intro hmem
            exact (hfree nf hmem) (by simp)
          refine ⟨?_, hbal, hcom, hcell, hacc, hcap, hrev, ?_, ?_⟩
          · -- nullifier shape: rest.reverse ++ (nf :: k.null) = (nf::rest).reverse ++ k.null
            rw [hnull]; simp [List.reverse_cons]
          · exact List.nodup_cons.mpr ⟨hnf_notin_rest, hnod⟩
          · intro x hx
            rcases List.mem_cons.mp hx with hxnf | hxrest
            · subst hxnf; exact hfresh
            · have := hfree x hxrest
              simp only [List.mem_cons, not_or] at this
              exact this.2

/-- Corollary — **bal-NEUTRAL nullifier-advance**: the deployed shielded transfer moves ZERO
transparent balance and creates ZERO commitments; the sole committed change is the nullifier set. This
is the kernel-side truth that the value legs are hidden (Pedersen) and off-kernel. -/
theorem shieldedTransferK_balNeutral {k k' : RecordKernelState} {keys : List Nat}
    (h : shieldedTransferK k keys = some k') :
    k'.bal = k.bal ∧ k'.commitments = k.commitments := by
  obtain ⟨_, hbal, hcom, _⟩ := shieldedTransferK_accepts keys k k' h
  exact ⟨hbal, hcom⟩

/-- Both-truth NEGATIVE tooth: a stale key (already spent) is rejected — no double-spend across the
transfer boundary, exactly the deployed GATE-3 pre-check. -/
theorem shieldedTransferK_reject_stale {k : RecordKernelState} {nf : Nat} {rest : List Nat}
    (h : nf ∈ k.nullifiers) : shieldedTransferK k (nf :: rest) = none := by
  simp only [shieldedTransferK, note_no_double_spend k nf h, Option.bind_none]

/-! Both-truth #guard witnesses over the reference kernel `res0` (`RecordKernel.lean:1076`). -/

-- POSITIVE: two distinct fresh keys are consumed; the set grows by exactly both.
#guard ((shieldedTransferK res0 [7, 9]).map (fun k => k.nullifiers)) == some [9, 7]
-- NEGATIVE (stale): a key already in the set fails-closed.
#guard ((shieldedTransferK { res0 with nullifiers := [7] } [7]).isSome) == false
-- NEGATIVE (in-transfer dup): a repeated key within one transfer fails-closed (`DuplicateNullifier`
-- has a kernel echo here — the second insert double-spends).
#guard ((shieldedTransferK res0 [7, 7]).isSome) == false

/-! ## §3 — The blake3 key-derivation BRIDGE: STARK distinctness + injective key ⟹ kernel accepts.

`verify_stark_side` rejects an in-transfer duplicate *field* nullifier (`DuplicateNullifier`). The
kernel gate needs the derived 32-byte *set keys* distinct. The bridge is injectivity of
`shielded_nullifier_key` — a blake3 collision-resistance / injectivity assumption on distinct field
elements (the `blake3-CR` floor, NAMED, discharged by the hash layer, not here). Given it, the STARK's
field-nullifier distinctness transports to key distinctness, so the kernel part accepts on any fresh
root — the two halves compose. -/
theorem shielded_keys_distinct
    {key : Nat → Nat} (hinj : Function.Injective key)
    {nfs : List Nat} (hnd : nfs.Nodup) : (nfs.map key).Nodup :=
  hnd.map hinj

/-! ## §4 — The STARK residual, NAMED precisely (the DEBT-A tail that is NOT provable in Lean).

The deployed 3-slot public-input tuple the shielded-spend uni-STARK is checked against. -/
structure ShieldedSpendPI where
  /-- `pi[0]` — the revealed BabyBear field nullifier (the double-spend tag). -/
  nullifier    : Int
  /-- `pi[1]` — the shared commitment-tree root all inputs are proven members of. -/
  merkleRoot   : Int
  /-- `pi[2]` — `value_binding = hash_fact(value,[randomness,0,0])`, the hiding leaf-value commitment
  the downstream `verify_value_link` re-derives from the Pedersen leg (C7a/C7b). -/
  valueBinding : Int
  deriving Repr

/-- **`StarkResidualUntied` — the residual AS THIS MODULE STATED IT BEFORE 2026-07-24.** Kept, not
deleted, for two reasons: the vacuity teeth of `Dregg2.Verify.ExistsImageVacuity` §5 are theorems
ABOUT this object and remain true of it, and the strengthening below has to be measured against
something. What it actually says, conjunct by conjunct:

  * `commitment` is a `member` of the tree at `pi.merkleRoot`, and the published nullifier is `H` of
    that commitment and a free `key`;
  * `value` and `randomness` open the published `pi.valueBinding` — and occur in **no conjunct that
    mentions `commitment`**;
  * `0 ≤ value`, for the `value` the existential just picked to satisfy the previous conjunct.

So the spent leaf and the published value binding are related by nothing, and the range conjunct
ranges over a value nothing pins. Under the two-free-input surjectivity of the `H [·,·]` site this
predicate holds of EVERY public-input triple at any root with one member
(`ExistsImageVacuity.starkResidual_vacuous`), and inhabits `extract` with no crypto
(`ExistsImageVacuity.starkResidual_floor_prices_nothing`). **This is not the obligation; it is the
record of what the obligation used to say.** -/
def StarkResidualUntied (H : List Int → Int) (member : Int → Int → Prop) (pi : ShieldedSpendPI) :
    Prop :=
  ∃ (commitment key value randomness : Int),
    member commitment pi.merkleRoot
    ∧ pi.nullifier = H [commitment, key]
    ∧ pi.valueBinding = H [value, randomness]
    ∧ 0 ≤ value

/-- **`StarkResidual pi` — what `verify_stark_side` must guarantee for one input**, with the C6↔C7a
TIE carried explicitly (the AIR constraints C1–C7b of `spend_circuit.rs`, as a Prop over the deployed
tuple, parametric over the abstract hash `H` and a Merkle membership predicate `member`). ONE opening
`(value, asset, owner, randomness)` does all the work:

  * **C3/C6 — the SPENT LEAF is a member.** `H [value, asset, owner, randomness]` — the note
    commitment OF THAT OPENING — is a `member` of the tree at `pi.merkleRoot`. There is no free leaf:
    the leaf is a function of the opening.
  * **C4 — the nullifier is derived from THAT leaf**, not from a free felt:
    `pi.nullifier = H [H [value, asset, owner, randomness], key]`.
  * **C7a — THE TIE.** The published `pi.valueBinding` opens to the SAME `value` and `randomness`
    that commit the member leaf. This conjunct is the one that makes `pi[2]` a public input the
    obligation SEES at all (`starkResidual_sees_valueBinding`); without it the residual's truth value
    is independent of `pi[2]` (`ExistsImageVacuity.starkResidual_indep_of_valueBinding`).
  * `0 ≤ value` — and it is now the SPENT note's value that is range-checked, not a felt the
    existential invented to satisfy this conjunct alone.

⚠ **What these conjuncts do NOT establish** — the docstring this replaces read the third conjunct as
*"value-binding is the committed leaf value (C7a)"* and the fourth as *"value is range-valid"*, and
neither was what the untied `Prop` said. Even repaired, the residual does NOT say: that
`pi.merkleRoot` is the COMMITTED accumulator root (that pin is `Dregg2.Circuit.ShieldedMerkleRootPin`,
discharged in-AIR by `Emit.ShieldedSpendDescriptor.root_is_pinned`); that `value` is bounded ABOVE
(the `< 2^VALUE_BITS` gadget is `ShieldedSpendPortResidual` §C's named residual); or anything about
the Pedersen legs (§5 floor 2). The `0 ≤ value` conjunct is carried because the accepted transfer
relies on it, not because this STARK is the inflation gate. -/
def StarkResidual (H : List Int → Int) (member : Int → Int → Prop) (pi : ShieldedSpendPI) : Prop :=
  ∃ (value asset owner randomness key : Int),
    member (H [value, asset, owner, randomness]) pi.merkleRoot
    ∧ pi.nullifier = H [H [value, asset, owner, randomness], key]
    ∧ pi.valueBinding = H [value, randomness]
    ∧ 0 ≤ value

/-- **⚑ THE STRENGTHENING IS A REFINEMENT (`starkResidual_untied_of_starkResidual`).** Every tied
residual is the pre-repair residual — instantiate `commitment := H [value, asset, owner, randomness]`
— so EVERYTHING previously concluded from `StarkResidual` still follows. The repair adds obligations
on the prover; it removes none of the module's conclusions. -/
theorem starkResidual_untied_of_starkResidual {H : List Int → Int} {member : Int → Int → Prop}
    (pi : ShieldedSpendPI) (h : StarkResidual H member pi) : StarkResidualUntied H member pi := by
  obtain ⟨value, asset, owner, randomness, key, hmem, hnf, hvb, hv0⟩ := h
  exact ⟨H [value, asset, owner, randomness], key, value, randomness, hmem, hnf, hvb, hv0⟩

/-- The projection that names what the tie BUYS: the published value binding opens to the value of a
note whose commitment is in the tree at `pi.merkleRoot` — one statement relating `pi[1]` and `pi[2]`,
which is exactly what the untied form had none of. -/
theorem starkResidual_binds_valueBinding_to_a_member {H : List Int → Int}
    {member : Int → Int → Prop} (pi : ShieldedSpendPI) (h : StarkResidual H member pi) :
    ∃ value asset owner randomness : Int,
      member (H [value, asset, owner, randomness]) pi.merkleRoot
      ∧ pi.valueBinding = H [value, randomness]
      ∧ 0 ≤ value := by
  obtain ⟨value, asset, owner, randomness, _, hmem, _, hvb, hv0⟩ := h
  exact ⟨value, asset, owner, randomness, hmem, hvb, hv0⟩

/-- **The residual reduces to `StarkSound`'s floor — NOT a new carrier.** The shielded-spend proof is
a hiding uni-STARK (`verify_dsl_zk`), a DIFFERENT verifier instance from the batch `verifyBatch` that
`Dregg2.Circuit.CircuitSoundness.StarkSound` packages, but the SAME KIND of obligation: a verifying
FRI/AIR proof extracts a witness satisfying the AIR. We state that extraction as an explicit
HYPOTHESIS `extract` (the FRI/AIR floor at the hiding uni-STARK config) — NAMING IS FAKING, so it is a
premise, never a `def`. Given it, the residual holds by modus ponens: this IS the content — the STARK
part reduces to exactly this floor and nothing new.

⚑ **The premise is now the TIED obligation** — `extract` must return ONE opening that commits the
member leaf, derives the nullifier AND opens the published value binding. That is strictly more than
it had to return before (`forged_valueBinding_now_refused`), and it is why §5 carries the tie as a
separate fourth floor: floor 1 supplies "a witness satisfying the AIR", floor 4 is the claim that the
AIR's C6 and C7a sites read the SAME opening cells. -/
theorem starkResidual_of_floor
    {H : List Int → Int} {member : Int → Int → Prop} {pi : ShieldedSpendPI}
    (accepted : Prop) (hacc : accepted)
    (extract : accepted → StarkResidual H member pi) :
    StarkResidual H member pi :=
  extract hacc

/-! ### §4.1 — the NON-VACUITY TEETH: a forged `pi[2]` is refused where it previously passed.

`ExistsImageVacuity` §5 measured the old shape by exhibiting a site at which it held of everything.
The repair is measured the same way, at a site that is a genuine function: the 4-ary note-commitment
arm exposes the opening as `100·value + randomness`, the 2-ary arm (nullifier + value binding) is the
sum, and the tree at root `1` holds exactly the commitment `0`. Toy arithmetic, real separation — the
teeth show the tie is a CONSTRAINT (some triples are now refused), not a notational nicety. -/

/-- The teeth's hash site: 4-ary (the C6 note commitment) exposes `(value, randomness)`; 2-ary (the C4
nullifier site and the C7a value-binding site) is the sum. -/
def tieH : List Int → Int
  | [v, _, _, r] => 100 * v + r
  | [x, y]       => x + y
  | _            => 0

/-- The teeth's tree: root `1` holds exactly the commitment `0`. -/
def tieMember : Int → Int → Prop := fun c r => c = 0 ∧ r = 1

/-- **The repaired obligation is INHABITED** — it is a real constraint, not an empty one. The honest
triple `⟨5, 1, 0⟩` is accepted by the opening `value = asset = owner = randomness = 0`, whose note
commitment `0` is the tree's only member, with `key = 5`. -/
theorem starkResidual_holds_on_honest_pi : StarkResidual tieH tieMember ⟨5, 1, 0⟩ := by
  refine ⟨0, 0, 0, 0, 5, ⟨?_, rfl⟩, ?_, ?_, le_refl 0⟩ <;> simp [tieH]

/-- **⚑ THE NON-VACUITY TOOTH (`forged_valueBinding_now_refused`).** Forge the honest triple's
published value binding — swap `0` for `1`, leaving `pi[0]` and `pi[1]` untouched — and the repaired
`StarkResidual` REFUSES it, while `StarkResidualUntied` still ACCEPTS it: the free `value = 1,
randomness = 0` opens the forged binding at the 2-ary site with no relation whatever to the spent
leaf. The tie is what refuses it — the member conjunct forces `100·value + randomness = 0` and the
binding conjunct forces `value + randomness = 1`, and no integer pair does both. -/
theorem forged_valueBinding_now_refused :
    StarkResidualUntied tieH tieMember ⟨5, 1, 1⟩ ∧ ¬ StarkResidual tieH tieMember ⟨5, 1, 1⟩ := by
  constructor
  · refine ⟨0, 5, 1, 0, ⟨rfl, rfl⟩, ?_, ?_, by norm_num⟩ <;> simp [tieH]
  · rintro ⟨v, a, o, r, key, ⟨hc, -⟩, -, hvb, -⟩
    simp only [tieH] at hc hvb
    omega

/-- **⚑ THE INDEPENDENCE IS GONE (`starkResidual_sees_valueBinding`).** The exact shape of
`ExistsImageVacuity.starkResidual_indep_of_valueBinding` — "the residual has the same truth value at
any two triples agreeing on `nullifier` and `merkleRoot`" — REFUTED at the repaired predicate: two
such triples, one accepted and one refused, differing only in `pi[2]`. The deployed `value_binding`
public input is no longer unconstrained by the obligation the STARK is said to discharge. -/
theorem starkResidual_sees_valueBinding :
    ∃ (H : List Int → Int) (member : Int → Int → Prop) (pi : ShieldedSpendPI) (y : Int),
      StarkResidual H member pi ∧ ¬ StarkResidual H member { pi with valueBinding := y } := by
  refine ⟨tieH, tieMember, ⟨5, 1, 0⟩, 1, starkResidual_holds_on_honest_pi, ?_⟩
  exact forged_valueBinding_now_refused.2

/-!
## §5 — The residual's FULL floor list (honest close).

`verify_stark_side` acceptance of a whole shielded transfer reduces to, and ONLY to, these NAMED
floors (none a new crypto carrier):

  1. **`StarkSound`'s FRI/AIR floor**, at the hiding uni-STARK config — the shielded-spend AIR
     (C1–C7b) verify ⟹ ∃ satisfying witness (`starkResidual_of_floor`'s `extract`). Same floor family
     as `Dregg2.Circuit.CircuitSoundness.StarkSound`; a different verifier *instance*, not a new class.
  2. **A Pedersen-binding + Bulletproofs-range floor** (DLog-hardness) — value conservation
     `Σ C_in = Σ C_out` and each output in `[0,2^64)`, from `verify_full_conservation_bytes` (GATE 2).
     This is NOT `StarkSound` and NOT `Poseidon2SpongeCR`; it is the curve/range-argument soundness the
     `dregg-cell-crypto` layer discharges. It is what makes the kernel's placeholder-`0` value SAFE:
     the amounts are conserved off-kernel.
  3. **A `blake3-CR` injectivity floor** — `shielded_nullifier_key` maps distinct field nullifiers to
     distinct 32-byte set keys (`shielded_keys_distinct`), so the STARK's `DuplicateNullifier` gate and
     the kernel's double-spend gate agree.
  4. **⚑ THE C6↔C7a ONE-OPENING TIE floor** (ADDED 2026-07-24 — its absence from this list is exactly
     how the vacuity hid). The AIR's note-commitment site (C6) and its value-binding site (C7a) read
     the SAME `value`/`randomness` cells, so floor 1's extractor returns ONE opening rather than two
     independent ones. In `StarkResidual` this is the conjunct `pi.valueBinding = H [value,
     randomness]` at the SAME `value`/`randomness` that commit the member leaf.
     **It is not a consequence of floors 1–3 as they were stated**: `forged_valueBinding_now_refused`
     exhibits a site where the untied residual — all the content floors 1–3 delivered about `pi[2]` —
     accepts a forged `value_binding` and the tied one refuses it.
     STATUS, at the resolution each object actually has — three levels, do not conflate them:
       (i) **Inside the Lean-emitted value-link object it is a THEOREM**, not a floor:
           `ShieldedValueLinkDescriptor.value_link_bound`, via
           `ShieldedSpendPortDischarge.emitted_conserved_is_leaf_bound`, proves that on EVERY row
           `leaf_commit` and `value_binding` are hash images of the SAME in-AIR value cell `cVAL`.
       (ii) **Across the two emitted objects it is still open.** The membership/nullifier side is
           `shieldedSpendDesc` and the value side is `shieldedValueLinkDesc` — two descriptors, two
           traces. Nothing yet identifies the spend trace's `cLEAF` with the value-link trace's, so
           the object-level tie is (i) plus a cross-descriptor join that no theorem supplies. That
           join is the precise next lane.
       (iii) **For the deployed hand-written Rust AIR** (`spend_circuit.rs` C6/C7a — house-law-#1
           DEBT) it is a FAITHFULNESS claim about column identity in Rust `ConstraintExpr` data,
           discharged by nothing here and by no Rust test (a case test is not a ∀-inputs statement).
     Levels (ii) and (iii) are the honest content of floor 4, and (iii) is the reason the deployed
     effect should route the Lean-emitted descriptors rather than the Rust AIR.

  ⚠ **GENUINE OPEN RESIDUAL (a real finding, not a floor): the leaf↔leg VALUE LINK.** Distinct from
  floor 4: floor 4 is INSIDE the STARK (spent leaf ↔ published `value_binding`); this residual is
  BETWEEN the STARK's `value_binding` and the off-AIR Pedersen leg. The STARK proves
  a hiding leaf value (`pi.valueBinding`) and the Pedersen side conserves the legs, both bound to one
  transcript — but their cryptographic EQUALITY is only checkable with the secret opening
  (`verify_value_link`, named in `circuit-prove/src/shielded/mod.rs`). Deployed M2-a relies on the
  HONEST PROVER for it (`apply.rs` doc "NAMED RESIDUAL (honest) … (b)"). This is not discharged by any
  floor above; it is the standing gap this brick reports.

  ℹ **ShieldedValue.lean sorry-check at HEAD (requested):** `Dregg2/Exec/ShieldedValue.lean` is
  SORRY-FREE at HEAD — `created_value_conservation` and `refVC_conservation_witness` both carry
  `#assert_axioms` and build clean; the earlier sibling-WIP `sorryAx` flags are GONE. Its
  `unshield_value_binding` keystone (the amount = spent-note value, over the committed step) is real.
  NOTE the deployed `ShieldedTransfer` does NOT drive `unshieldK`'s transparent pool→dst move — that
  models `Unshield`; `ShieldedTransfer`'s kernel effect is nullifier-advance only, per §1.
-/

/-! ## §6 — axiom hygiene. -/

#assert_axioms noteSpendNullifier_shape
#assert_axioms shieldedTransferK_accepts
#assert_axioms shieldedTransferK_balNeutral
#assert_axioms shieldedTransferK_reject_stale
#assert_axioms shielded_keys_distinct
#assert_axioms starkResidual_untied_of_starkResidual
#assert_axioms starkResidual_binds_valueBinding_to_a_member
#assert_axioms starkResidual_of_floor
#assert_axioms starkResidual_holds_on_honest_pi
#assert_axioms forged_valueBinding_now_refused
#assert_axioms starkResidual_sees_valueBinding

end Dregg2.Circuit.ShieldedTransferStark
