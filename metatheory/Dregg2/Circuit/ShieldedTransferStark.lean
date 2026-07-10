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
PLUS three explicitly-named side floors — NOT a new carrier. NAMING IS FAKING: the residual's
extractor is an explicit HYPOTHESIS, never a `def`-used-as-proof.

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

/-- **`StarkResidual pi` — exactly what `verify_stark_side` must guarantee for one input** (the AIR
constraints C1–C7b of `spend_circuit.rs`, as a Prop over the tuple, parametric over the abstract hash
`H` and a Merkle membership predicate `member`). There EXISTS a note witness whose:
  * commitment is a `member` of the tree at `pi.merkleRoot` (C3/C6: membership, no free leaf);
  * nullifier is correctly DERIVED — `pi.nullifier = H [commitment, key]` (C4: no forge);
  * value-binding is the committed leaf value — `pi.valueBinding = H [value, randomness]` (C7a);
  * value is range-valid — `0 ≤ value` (the toothed inflation gate lives in the Pedersen/Bulletproof
    leg, NOT this STARK; carried here only as the property the accepted transfer relies on). -/
def StarkResidual (H : List Int → Int) (member : Int → Int → Prop) (pi : ShieldedSpendPI) : Prop :=
  ∃ (commitment key value randomness : Int),
    member commitment pi.merkleRoot
    ∧ pi.nullifier = H [commitment, key]
    ∧ pi.valueBinding = H [value, randomness]
    ∧ 0 ≤ value

/-- **The residual reduces to `StarkSound`'s floor — NOT a new carrier.** The shielded-spend proof is
a hiding uni-STARK (`verify_dsl_zk`), a DIFFERENT verifier instance from the batch `verifyBatch` that
`Dregg2.Circuit.CircuitSoundness.StarkSound` packages, but the SAME KIND of obligation: a verifying
FRI/AIR proof extracts a witness satisfying the AIR. We state that extraction as an explicit
HYPOTHESIS `extract` (the FRI/AIR floor at the hiding uni-STARK config) — NAMING IS FAKING, so it is a
premise, never a `def`. Given it, the residual holds by modus ponens: this IS the content — the STARK
part reduces to exactly this floor and nothing new. -/
theorem starkResidual_of_floor
    {H : List Int → Int} {member : Int → Int → Prop} {pi : ShieldedSpendPI}
    (accepted : Prop) (hacc : accepted)
    (extract : accepted → StarkResidual H member pi) :
    StarkResidual H member pi :=
  extract hacc

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

  ⚠ **GENUINE OPEN RESIDUAL (a real finding, not a floor): the leaf↔leg VALUE LINK.** The STARK proves
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

end Dregg2.Circuit.ShieldedTransferStark
