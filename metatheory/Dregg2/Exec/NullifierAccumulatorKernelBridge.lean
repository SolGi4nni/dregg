import Dregg2.Exec.RecordKernel
import Dregg2.Exec.NullifierAccumulator

/-!
# The nullifier-accumulator ↔ kernel bridge

`RecordKernelState` now carries the two Poseidon2 accumulator roots (`nullifierRoot` / `revokedRoot`,
landed in the VK-epoch apex and absorbed by `StateCommit.RestHashIffFrame`). This file plugs the
ALREADY-PROVEN double-spend / revocation gate (`Dregg2.Exec.NullifierAccumulator`, over the
standalone `NfAccState`) into those kernel fields WITHOUT re-proving any crypto: every theorem here
reduces to the banked `spend_inserts_root` / `present_no_witness` / `revoked_gate_fails` through the
`toNfAccState` projection. The sole crypto floor stays `SpineCommits8` / `Compress8CR` (a hypothesis
carried in the witness, never a Lean axiom).

The migration keeps the `List Nat` `nullifiers` in sync (no regression to `note_no_double_spend`);
the accumulator root is the O(1), client-witnessed spend frontier that the wire codec (stage E) will
feed. Fail-closed is EXTERNAL: a double-spend of a committed `nf` admits NO witness
(`noteSpendNullifierAcc_no_double_spend`), so a replaying caller simply cannot supply one — the
spend proof cannot be produced.
-/

namespace Dregg2.Exec

open Dregg2.Exec.NullifierAccumulator
open Dregg2.Circuit.DeployedHeapTree (Heap8Scheme)
open Dregg2.Circuit.SortedTreeNonMembershipHeap8 (keysOf8)

/-- Project the kernel's two accumulator roots into the standalone `NfAccState` the proven gate
operates over. Definitional on both roots. -/
def RecordKernelState.toNfAccState (k : RecordKernelState) : NfAccState :=
  { nullifierRoot := k.nullifierRoot, revokedRoot := k.revokedRoot }

@[simp] theorem toNfAccState_nullifierRoot (k : RecordKernelState) :
    k.toNfAccState.nullifierRoot = k.nullifierRoot := rfl

@[simp] theorem toNfAccState_revokedRoot (k : RecordKernelState) :
    k.toNfAccState.revokedRoot = k.revokedRoot := rfl

/-- **`noteSpendNullifierAcc` — the accumulator-backed spend over the kernel.** Given a valid
client-supplied `NfAccWitness` against the committed `nullifierRoot`, advance the root to the witness
after-root and keep the migration `List` in sync. O(1): verify the witness, swap the root. The
double-spend rejection is NOT a `List` scan — it is the ABSENCE of a witness for a present key
(`noteSpendNullifierAcc_no_double_spend`). -/
def noteSpendNullifierAcc {S8 : Heap8Scheme} (k : RecordKernelState) (nf : Nat)
    (w : NfAccWitness S8 k.nullifierRoot (nf : ℤ)) : RecordKernelState :=
  { k with nullifierRoot := w.newRoot, nullifiers := nf :: k.nullifiers }

@[simp] theorem noteSpendNullifierAcc_nullifierRoot {S8 : Heap8Scheme} (k : RecordKernelState)
    (nf : Nat) (w : NfAccWitness S8 k.nullifierRoot (nf : ℤ)) :
    (noteSpendNullifierAcc k nf w).nullifierRoot = w.newRoot := rfl

theorem noteSpendNullifierAcc_nullifiers {S8 : Heap8Scheme} (k : RecordKernelState)
    (nf : Nat) (w : NfAccWitness S8 k.nullifierRoot (nf : ℤ)) :
    (noteSpendNullifierAcc k nf w).nullifiers = nf :: k.nullifiers := rfl

/-- **THE INSERT IS FAITHFUL (kernel terms).** After a committed acc-spend, `nf` is PRESENT in the
new committed `nullifierRoot`. Reduces to `spend_inserts_root` under the `toNfAccState` projection. -/
theorem noteSpendNullifierAcc_present {S8 : Heap8Scheme} (k : RecordKernelState) (nf : Nat)
    (w : NfAccWitness S8 k.nullifierRoot (nf : ℤ)) :
    (nf : ℤ) ∈ keysOf8 S8 (noteSpendNullifierAcc k nf w).nullifierRoot := by
  simpa [noteSpendNullifierAcc, spendNullifierRoot] using
    spend_inserts_root k.toNfAccState (nf : ℤ) w

/-- **THE COMPOSED ANTI-REPLAY (kernel terms).** After an acc-spend of `nf`, NO witness exists for a
second spend of the SAME `nf`: double-spend is impossible. Reduces to `present_no_witness`. -/
theorem noteSpendNullifierAcc_no_rewitness {S8 : Heap8Scheme} (k : RecordKernelState) (nf : Nat)
    (w : NfAccWitness S8 k.nullifierRoot (nf : ℤ)) :
    IsEmpty (NfAccWitness S8 (noteSpendNullifierAcc k nf w).nullifierRoot (nf : ℤ)) :=
  present_no_witness (noteSpendNullifierAcc_present k nf w)

/-- **THE DOUBLE-SPEND GATE (kernel terms).** A nullifier already committed by `k.nullifierRoot`
(already spent) admits NO valid spend witness — fail-closed by witness scarcity, not a set scan. -/
theorem noteSpendNullifierAcc_no_double_spend {S8 : Heap8Scheme} (k : RecordKernelState) (nf : Nat)
    (hspent : (nf : ℤ) ∈ keysOf8 S8 k.nullifierRoot) :
    IsEmpty (NfAccWitness S8 k.nullifierRoot (nf : ℤ)) :=
  present_no_witness hspent

/-- **THE REVOCATION LEG (kernel terms).** A credential whose nullifier sits in the committed
`revokedRoot` admits NO non-membership witness ⇒ the revocation gate cannot pass. Reduces to
`revoked_gate_fails` under the projection. -/
theorem kernel_revoked_gate_fails {S8 : Heap8Scheme} (k : RecordKernelState) (credNul : ℤ)
    (hrev : credNul ∈ keysOf8 S8 k.revokedRoot) :
    ¬ revocationGateRootOK S8 k.toNfAccState credNul :=
  revoked_gate_fails S8 k.toNfAccState credNul (by simpa using hrev)

#assert_axioms noteSpendNullifierAcc_present
#assert_axioms noteSpendNullifierAcc_no_rewitness
#assert_axioms noteSpendNullifierAcc_no_double_spend
#assert_axioms kernel_revoked_gate_fails

/-! ## The COMMITMENT accumulator dual — GROW-ONLY (no double-spend gate).

The commitment set is the grow-only dual of the nullifier set: a note-create INSERTS a fresh
commitment, and — unlike a spend — there is NO rejection (a fresh commitment always admits a witness,
there is no double-spend polarity). The sole obligation is the `create_inserts_root` tooth: after a
committed create, the commitment is provably PRESENT in the advanced `commitmentsRoot`. It reduces to
the SAME banked `spend_inserts_root` (the `y = nf` disjunct of `update_sound8`) through a projection
that reads `commitmentsRoot` as the accumulator's active root. No `present_no_witness` obligation:
grow-only carries no fail-closed leg. -/

/-- Project the kernel's `commitmentsRoot` into the standalone `NfAccState`'s active root, so the
proven insert-is-faithful gate operates over it. Definitional. -/
def RecordKernelState.toCmAccState (k : RecordKernelState) : NfAccState :=
  { nullifierRoot := k.commitmentsRoot }

@[simp] theorem toCmAccState_nullifierRoot (k : RecordKernelState) :
    k.toCmAccState.nullifierRoot = k.commitmentsRoot := rfl

/-- **`noteCreateCommitmentAcc` — the accumulator-backed note-create over the kernel.** Given a valid
client-supplied `NfAccWitness` against the committed `commitmentsRoot`, advance the root to the
witness after-root and keep the migration `List` in sync. GROW-ONLY: a fresh commitment always has a
witness, there is no rejection — the dual of `noteSpendNullifierAcc` WITHOUT the double-spend gate. -/
def noteCreateCommitmentAcc {S8 : Heap8Scheme} (k : RecordKernelState) (cm : Nat)
    (w : NfAccWitness S8 k.commitmentsRoot (cm : ℤ)) : RecordKernelState :=
  { k with commitmentsRoot := w.newRoot, commitments := cm :: k.commitments }

@[simp] theorem noteCreateCommitmentAcc_commitmentsRoot {S8 : Heap8Scheme} (k : RecordKernelState)
    (cm : Nat) (w : NfAccWitness S8 k.commitmentsRoot (cm : ℤ)) :
    (noteCreateCommitmentAcc k cm w).commitmentsRoot = w.newRoot := rfl

theorem noteCreateCommitmentAcc_commitments {S8 : Heap8Scheme} (k : RecordKernelState)
    (cm : Nat) (w : NfAccWitness S8 k.commitmentsRoot (cm : ℤ)) :
    (noteCreateCommitmentAcc k cm w).commitments = cm :: k.commitments := rfl

/-- **THE INSERT IS FAITHFUL (kernel terms, GROW-ONLY tooth).** After a committed acc-create, `cm` is
PRESENT in the new committed `commitmentsRoot` — the `create_inserts_root` analog of the nullifier
`spend_inserts_root`, reducing to it through the `toCmAccState` projection. Non-vacuous: the witness
type is genuinely inhabitable (`witness_inhabited_of_bindings`), so this is a real membership over an
occupied domain, not a claim over an empty hypothesis. -/
theorem noteCreateCommitmentAcc_present {S8 : Heap8Scheme} (k : RecordKernelState) (cm : Nat)
    (w : NfAccWitness S8 k.commitmentsRoot (cm : ℤ)) :
    (cm : ℤ) ∈ keysOf8 S8 (noteCreateCommitmentAcc k cm w).commitmentsRoot := by
  simpa [noteCreateCommitmentAcc, spendNullifierRoot] using
    spend_inserts_root k.toCmAccState (cm : ℤ) w

#assert_axioms noteCreateCommitmentAcc_present
#assert_axioms noteCreateCommitmentAcc_commitments

/-! ## The REVOCATION accumulator dual — GROW-ONLY WRITER (closing hole #3 / #139).

The revoked-credential set is the grow-only dual of the nullifier set on the REVOCATION frontier: a
`cap_revoke` INSERTS a fresh `credNul` (the capability's provenance/derivation-node hash, domain-
separated `H("dregg-cred-revocation-v1" ‖ provenance_hash)` — `docs/REVOKED-ROOT-COMMITTED-LIMB.md`
§3b), advancing the committed `revokedRoot`, and — unlike a spend — there is NO rejection at the writer
(a re-revocation of an already-present `credNul` simply admits no witness; the root advances once per
distinct revocation). The reader side was ALREADY proven (`kernel_revoked_gate_fails`): a `credNul`
present in `revokedRoot` admits NO non-membership witness ⇒ the revocation gate refuses it. What was
MISSING — the entire hole — is the WRITER that makes an ACTION grow that committed root. This is it.

It reduces to the SAME banked `spend_inserts_root` (the `y = nf` disjunct of `update_sound8`) through
`toRevAccState`, which reads `revokedRoot` as the accumulator's active root — the exact analog of
`toCmAccState` for commitments. The kernel-op `RecordKernel.capRevoke` grows the `revoked : List Nat`
migration registry and swaps the root; this wrapper supplies the `NfAccWitness` that PROVES the swap
faithful (`credNul` genuinely present in the advanced root). Grow-only: no `present_no_witness`
obligation, no fail-closed leg at the writer. -/

/-- Project the kernel's `revokedRoot` into the standalone `NfAccState`'s active root, so the proven
insert-is-faithful gate operates over it. Definitional. The revocation-frontier analog of
`toCmAccState`. -/
def RecordKernelState.toRevAccState (k : RecordKernelState) : NfAccState :=
  { nullifierRoot := k.revokedRoot }

@[simp] theorem toRevAccState_nullifierRoot (k : RecordKernelState) :
    k.toRevAccState.nullifierRoot = k.revokedRoot := rfl

/-- **`revokeCredentialAcc` — the accumulator-backed credential-revocation WRITER over the kernel.**
Given a valid client-supplied `NfAccWitness` against the committed `revokedRoot`, insert `credNul`:
advance the root to the witness after-root (via `RecordKernel.capRevoke`) and keep the migration `List`
in sync. GROW-ONLY: a fresh `credNul` always has a witness; a re-revocation admits none (the root
already commits it) — the dual of `noteSpendNullifierAcc` WITHOUT the double-spend gate, on the
revocation frontier. THE WRITER hole #3 / #139 named and never built. -/
def revokeCredentialAcc {S8 : Heap8Scheme} (k : RecordKernelState) (credNul : Nat)
    (w : NfAccWitness S8 k.revokedRoot (credNul : ℤ)) : RecordKernelState :=
  capRevoke k credNul w.newRoot

@[simp] theorem revokeCredentialAcc_revokedRoot {S8 : Heap8Scheme} (k : RecordKernelState)
    (credNul : Nat) (w : NfAccWitness S8 k.revokedRoot (credNul : ℤ)) :
    (revokeCredentialAcc k credNul w).revokedRoot = w.newRoot := rfl

/-- **`revokeCredentialAcc_revoked` — the migration `List` stays in sync.** The writer grows the
`revoked` registry by exactly `credNul`, so the `List`-side reader (`gateOK`) and the root-side reader
(`kernel_revoked_gate_fails`) refuse the SAME credential. -/
theorem revokeCredentialAcc_revoked {S8 : Heap8Scheme} (k : RecordKernelState) (credNul : Nat)
    (w : NfAccWitness S8 k.revokedRoot (credNul : ℤ)) :
    (revokeCredentialAcc k credNul w).revoked = credNul :: k.revoked := rfl

/-- **THE INSERT IS FAITHFUL (kernel terms, GROW-ONLY tooth).** After a committed `revokeCredentialAcc`,
`credNul` is PRESENT in the new committed `revokedRoot` — the `revoke_inserts_root` analog of the
nullifier `spend_inserts_root`, reducing to it through the `toRevAccState` projection. Non-vacuous: the
witness type is genuinely inhabitable (`witness_inhabited_of_bindings`), so this is a real membership
over an occupied domain, not a claim over an empty hypothesis. -/
theorem revokeCredentialAcc_present {S8 : Heap8Scheme} (k : RecordKernelState) (credNul : Nat)
    (w : NfAccWitness S8 k.revokedRoot (credNul : ℤ)) :
    (credNul : ℤ) ∈ keysOf8 S8 (revokeCredentialAcc k credNul w).revokedRoot := by
  simpa [revokeCredentialAcc, capRevoke, spendNullifierRoot] using
    spend_inserts_root k.toRevAccState (credNul : ℤ) w

/-- **`capRevoke_then_gate_refuses` — THE ACCEPTANCE TEST, THE WHOLE POINT OF THE CAMPAIGN.** Every
prior revocation theorem took `credNul ∈ keysOf8 revokedRoot` (equivalently `credNul ∈ revoked`) as a
HYPOTHESIS, dischargeable only by hand-built fixtures — that is why the lock sat on an EMPTY registry.
Here an ACTION discharges it: after `revokeCredentialAcc k credNul w`, the antecedent of
`kernel_revoked_gate_fails` HOLDS (`revokeCredentialAcc_present`), hence the committed revocation gate
CANNOT pass for that credential — no matter how valid its signature. Revocation is now ATTESTABLE: a
light client verifies from commitment + proof alone that the credential was revoked and the turn honoured
it. -/
theorem capRevoke_then_gate_refuses {S8 : Heap8Scheme} (k : RecordKernelState) (credNul : Nat)
    (w : NfAccWitness S8 k.revokedRoot (credNul : ℤ)) :
    ¬ revocationGateRootOK S8 (revokeCredentialAcc k credNul w).toNfAccState (credNul : ℤ) :=
  kernel_revoked_gate_fails (revokeCredentialAcc k credNul w) (credNul : ℤ)
    (revokeCredentialAcc_present k credNul w)

#assert_axioms revokeCredentialAcc_present
#assert_axioms revokeCredentialAcc_revoked
#assert_axioms capRevoke_then_gate_refuses

end Dregg2.Exec
