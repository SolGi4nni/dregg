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

end Dregg2.Exec
