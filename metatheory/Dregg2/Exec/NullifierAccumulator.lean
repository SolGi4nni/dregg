/-
# Dregg2.Exec.NullifierAccumulator — the NULLIFIER / REVOCATION accumulator gate (executor-side weld)

The double-spend gate (`RecordKernel.noteSpendNullifier`) and the revocation gate
(`FullForestAuth.revocationGate`) carry a whole append-only `List Nat` in kernel state and check
membership by O(#history) scan — so the *entire* spent/revoked set crosses the FFI/wire boundary each
turn. This file is the accumulator gate that replaces that (`docs/SUPERSEDED/NULLIFIER-ACCUMULATOR-DESIGN.md`):
state carries only a fixed-width `Digest8` root, and the *transaction* supplies a client-side
non-membership + insert witness verified against that root. The wire carries the commitment, never
the set.

## Where this sits in the migration (READ THIS) — THE FLIP IS FIRED; THIS IS NO LONGER A BLOCKER
This is a WELD onto proven infra. It models the accumulator step over a standalone `NfAccState` (the
two roots). Those roots are NOW kernel fields: `RecordKernelState.nullifierRoot`
(`Exec/RecordKernel.lean:433`), `.revokedRoot` (`:442`) and the grow-only `.commitmentsRoot`
(`:452`), each defaulting to the empty-tree root. The flip was NOT a free additive step — the
full-state FRAME theorems (`Transfer.TransferSpec`, `StateCommit.RestHashIffFrame`, the
`RotatedKernelRefinement*` `fr*` frame structures, every effect's `↔`-spec) each PIN every kernel
field, so pinning the new roots forced the rest-hash `RH` to ABSORB them — the VK-epoch commitment
change itself. It was fired as ONE flag-day (ember-authorized, coordinated with the umem VK epoch,
design §6) and `RH` absorbs all three: `Circuit/StateCommit.lean:290-291`
(`∧ k'.nullifierRoot = k.nullifierRoot ∧ k'.revokedRoot = k.revokedRoot ∧ k'.commitmentsRoot =
k.commitmentsRoot`, inside `RestHashIffFrame`). The `NfAccState` model is KEPT — the proofs below
are stated over it and the kernel reaches them through the `toNfAccState` projection, without
re-proving any crypto (`Exec/NullifierAccumulatorKernelBridge.lean:7-8`, which records the same:
"`RecordKernelState` now carries the two Poseidon2 accumulator roots … landed in the VK-epoch apex
and absorbed by `StateCommit.RestHashIffFrame`"). Downstream files that cited this section as an
open ember-gate are stale by that citation alone.

## The reused, already-proven core (NOT re-proved here)
The sorted/indexed-Merkle-tree non-membership + fresh-key insert are fully proved over the DEPLOYED
`Heap8Scheme` node8 lane (the geometry the circuit's `nullifier_root` @ limb 26 actually rides):

  * `SortedTreeNonMembershipHeap8.nonMembership_sound8` — a valid gap open ⟹ key ABSENT.
  * `SortedTreeNonMembershipHeap8.update_sound8`        — the fresh-key insert grows the committed
                                                          set by EXACTLY the new key.
  * `SortedTreeNonMembershipHeap8.GapOpen8.excludesSpine` — the UNCONDITIONAL combinatorial keystone.

The three security obligations (`docs/SUPERSEDED/NULLIFIER-ACCUMULATOR-DESIGN.md` §4) re-derived over the root:

  (a) `no_double_spend_root`   ← contrapositive of `nonMembership_sound8` (present ⇒ no witness).
  (b) `spend_inserts_root`     ← the `y = nf` disjunct of `update_sound8`.
  (c) `present_no_witness`     ← non-forgeability: an adversary-supplied witness for a PRESENT key is
                                 impossible (combinatorial layer unconditional; the spine↔root
                                 binding `SpineCommits8` rests on the one deployed
                                 `Poseidon2SpongeCR`/`Compress8CR` floor — NO new trust).

## The crypto residue (named, honest)
The SOLE carrier is `SpineCommits8 S8 root spine` — "the sorted key spine is what `root` commits to",
the realizable `compute_canonical_heap_root_8` fold. It is a HYPOTHESIS carried by the witness, never
an axiom, and enters only at the spine↔root step (the deployed `Heap8Scheme` node8 CR). The
bracketing/insert combinatorics are unconditional.

## Non-vacuity (do not launder)
The accept relation is TWO-VALUED: `witness_inhabited_of_bindings` exhibits the TRUE pole (a fresh
key HAS a witness once the bindings realize) and `present_no_witness` is the FALSE pole (a present key
has NONE). The decidable spine-level demos witness the same at the combinatorial layer — a fresh
nullifier is bracketed-excluded (admissible), an already-spent one is present (no gap, gate refuses),
and the insert grows the set by EXACTLY the fresh key.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; `SpineCommits8` is a HYPOTHESIS carried
by the witness, never an axiom; the Poseidon-CR floor enters only through the `Heap8Scheme` carrier
already in play.
-/
import Dregg2.Circuit.SortedTreeNonMembershipHeap8

namespace Dregg2.Exec.NullifierAccumulator

open Dregg2.Circuit.DeployedCapTree (Digest8)
open Dregg2.Circuit.DeployedHeapTree (Heap8Scheme)
open Dregg2.Circuit.SortedTreeNonMembershipHeap8
open Dregg2.Circuit.SortedTreeNonMembership (sortedInsert)
open Dregg2.Crypto.NonMembership (Sorted Adjacent sorted_gap_excludes)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — the accumulator state (the two roots the VK-epoch flip lands in `RecordKernelState`). -/

/-- **`NfAccState`** — the O(1)-wire accumulator state: two `Digest8` roots, the double-spend
frontier (`nullifierRoot`, `nullifier_root` @ circuit limb 26) and the revocation frontier
(`revokedRoot`). This is EXACTLY the additive pair the VK epoch adds to `RecordKernelState`
(defaulting to the all-zero empty-tree root); the whole spent/revoked set NEVER crosses the wire, only
these commitments do. -/
structure NfAccState where
  /-- Poseidon2 sorted-tree root of the spent-note nullifier set (the double-spend frontier). -/
  nullifierRoot : Digest8 := fun _ => 0
  /-- Poseidon2 sorted-tree root of the revoked-credential-nullifier set (the revocation frontier). -/
  revokedRoot   : Digest8 := fun _ => 0

/-! ## §1 — the client-supplied witness (non-membership + insert, verified against the root). -/

/-- **`NfAccWitness S8 root nf`** — a client-side witness that spending nullifier `nf` is admissible
against the committed accumulator `root`, and the root it advances to. It carries:

  * `spine`      — the sorted key set the root commits to (the ghost the openings ride against);
  * `commitsOld` — the realizable `root ↔ spine` binding (the single named Poseidon2/`Compress8CR`
                   floor; a HYPOTHESIS, never an axiom);
  * `gap` + `gapValid` — the predecessor/successor bracketing NON-MEMBERSHIP open for `nf`
                   (`GapOpen8`, the deployed `insert_witness`'s non-membership leg);
  * `newRoot` + `commitsNew` — the AFTER root binds `sortedInsert nf spine` (the fresh-key splice,
                   the deployed insert's after-membership leg).

State holds ONLY `root`; the whole set never crosses the wire. Non-membership of `nf` over `root` is
DERIVED from the witness (`witness_fresh`), not assumed — so a valid witness genuinely proves `nf` was
absent. -/
structure NfAccWitness (S8 : Heap8Scheme) (root : Digest8) (nf : ℤ) where
  /-- The sorted key set the OLD root commits to. -/
  spine      : List ℤ
  /-- The root the accumulator advances to after inserting `nf`. -/
  newRoot    : Digest8
  /-- The realizable OLD `root ↔ spine` binding (the one Poseidon2/`Compress8CR` floor). -/
  commitsOld : SpineCommits8 S8 root spine
  /-- The non-membership covering-gap open for `nf` against `root`. -/
  gap        : GapOpen8 S8 root nf
  /-- The gap is VALID against the committed spine (predecessor/successor bracketing). -/
  gapValid   : gap.coversSpine spine
  /-- The NEW root binds the fresh-key-inserted spine. -/
  commitsNew : SpineCommits8 S8 newRoot (sortedInsert nf spine)

variable {S8 : Heap8Scheme} {root : Digest8} {nf : ℤ}

/-- **`witness_fresh`** — a valid `NfAccWitness` PROVES its key is absent from the committed set: the
non-membership leg is sound (`nonMembership_sound8`). The witness earns non-membership; it is not
assumed. -/
theorem witness_fresh (w : NfAccWitness S8 root nf) : nf ∉ keysOf8 S8 root :=
  nonMembership_sound8 S8 root nf w.spine w.commitsOld w.gap w.gapValid

/-! ## §2 — (c) NON-FORGEABILITY / (a) NO-DOUBLE-SPEND: a present key admits NO witness. -/

/-- **`present_no_witness` — THE SAFETY KEYSTONE (design §4(c)/(a)).** A key already committed by
`root` admits NO valid non-membership + insert witness: the accumulator gate is fail-closed for a
present key. This is the obligation the `List Nat` model got for free (the set was trusted state) and
the accumulator EARNS, because the witness is now adversary-supplied — a forged non-membership for a
present key would be a `GapOpen8` whose ordering contradicts `nf`'s presence (`excludesSpine`,
unconditional) OR a Poseidon2 collision opening a different spine than `root` commits (the single
`SpineCommits8`/`Compress8CR` floor). No new trust. -/
theorem present_no_witness (hpresent : nf ∈ keysOf8 S8 root) :
    IsEmpty (NfAccWitness S8 root nf) :=
  ⟨fun w => witness_fresh w hpresent⟩

/-! ## §3 — the executable spend step + (b) the insert is faithful. -/

/-- **`spendNullifierRoot` — the accumulator double-spend step (fail-closed by witness scarcity).**
Given a valid `NfAccWitness` against the committed `nullifierRoot`, advance the root to the witness's
after-root. The O(1) work: verify the proof (the witness), swap the root — no set crosses the wire.
The fail-closed rejection of a double-spend is NOT a scan: it is the ABSENCE of any valid witness for
a present key (`present_no_witness`) — the STARK cannot be produced. -/
def spendNullifierRoot (s : NfAccState) (nf : ℤ)
    (w : NfAccWitness S8 s.nullifierRoot nf) : NfAccState :=
  { s with nullifierRoot := w.newRoot }

/-- **`spend_inserts_root` — THE INSERT IS FAITHFUL (design §4(b)).** A committed spend advances
`nullifierRoot` so that `nf` is now PRESENT in the new committed set — the `y = nf` disjunct of
`update_sound8`. So a SUBSEQUENT spend of the same `nf` is refused by `present_no_witness` (the
composed anti-replay, `spend_then_no_rewitness`). -/
theorem spend_inserts_root (s : NfAccState) (nf : ℤ)
    (w : NfAccWitness S8 s.nullifierRoot nf) :
    nf ∈ keysOf8 S8 (spendNullifierRoot s nf w).nullifierRoot := by
  have hfresh : nf ∉ keysOf8 S8 s.nullifierRoot := witness_fresh w
  have hu := update_sound8 S8 s.nullifierRoot w.newRoot nf w.spine w.commitsOld hfresh w.commitsNew
  show nf ∈ keysOf8 S8 w.newRoot
  exact (hu nf).mpr (Or.inl rfl)

/-- **`spend_then_no_rewitness` — THE COMPOSED ANTI-REPLAY.** After a committed spend of `nf`, the
resulting `nullifierRoot` commits `nf`, so NO valid witness exists for a second spend of the same
`nf`: double-spend is impossible. -/
theorem spend_then_no_rewitness (s : NfAccState) (nf : ℤ)
    (w : NfAccWitness S8 s.nullifierRoot nf) :
    IsEmpty (NfAccWitness S8 (spendNullifierRoot s nf w).nullifierRoot nf) :=
  present_no_witness (spend_inserts_root s nf w)

/-- **`no_double_spend_root` — the double-spend gate in state terms.** A nullifier already committed
by `s.nullifierRoot` (already spent) admits NO valid spend witness. The `List Nat`
`note_no_double_spend` (`nf ∈ k.nullifiers → noteSpendNullifier k nf = none`) read over the root:
`nf` present ⇒ the witness-verifying step has no input ⇒ fail-closed. -/
theorem no_double_spend_root (s : NfAccState) (nf : Nat)
    (hspent : (nf : ℤ) ∈ keysOf8 S8 s.nullifierRoot) :
    IsEmpty (NfAccWitness S8 s.nullifierRoot (nf : ℤ)) :=
  present_no_witness hspent

/-! ## §4 — the REVOCATION dual (same accumulator, opposite gate polarity). -/

/-- **`revocationGateRootOK` — the revocation leg over the root.** The gate PASSES iff a valid
non-membership witness for `credNul` exists against the committed `revokedRoot` (the dual of the
`List.contains` read `!(s.kernel.revoked.contains na.credNul)`): pass ⟺ the credential's nullifier is
provably ABSENT from the revoked set. -/
abbrev revocationGateRootOK (S8 : Heap8Scheme) (s : NfAccState) (credNul : ℤ) : Prop :=
  Nonempty (NfAccWitness S8 s.revokedRoot credNul)

/-- **`revoked_gate_fails` — THE REVOCATION TEETH (design §6 dual of `gateOK_revoked_fails`).** A
credential whose nullifier sits in the COMMITTED revocation accumulator admits NO non-membership
witness ⇒ the gate's non-membership leg CANNOT pass ⇒ the credential is rejected. Non-vacuous by the
same `present_no_witness` argument: presence in `revokedRoot` is adversary-uncontrollable, so a
revoked credential cannot forge its way past no matter how valid its signature. -/
theorem revoked_gate_fails (S8 : Heap8Scheme) (s : NfAccState) (credNul : ℤ)
    (hrev : credNul ∈ keysOf8 S8 s.revokedRoot) :
    ¬ revocationGateRootOK S8 s credNul :=
  not_nonempty_iff.mpr (present_no_witness hrev)

/-! ## §NON-VACUITY — the accept relation is load-bearing (witness TRUE and FALSE). -/

/-- **TRUE pole** — the accept relation is INHABITABLE: given the realizable spine↔root bindings for
the empty tree and its single-key successor (exactly what the deployed `compute_canonical_heap_root_8`
provides), a fresh spend HAS a witness (the `empty` gap trivially covers the empty spine). So
`present_no_witness`/`IsEmpty` is genuinely two-valued — the safety theorem is NOT laundering a
categorically-empty type. -/
theorem witness_inhabited_of_bindings {emptyR oneR : Digest8} {nf : ℤ}
    (h0 : SpineCommits8 S8 emptyR [])
    (h1 : SpineCommits8 S8 oneR (sortedInsert nf [])) :
    Nonempty (NfAccWitness S8 emptyR nf) :=
  ⟨{ spine := [], newRoot := oneR, commitsOld := h0,
     gap := .empty, gapValid := rfl, commitsNew := h1 }⟩

-- The FALSE pole is `present_no_witness` (a present key has NO witness).

/-- A concrete sorted spent-set over `ℤ`: `[10, 20, 30]`. -/
private def demoSpine : List ℤ := [10, 20, 30]

private theorem demoSpine_sorted : Sorted demoSpine := by
  simp [demoSpine, Sorted, List.pairwise_cons]

private theorem demoSpine_adjacent : Adjacent demoSpine 20 30 := ⟨[10], [], rfl⟩

/-- **Combinatorial TRUE — a FRESH nullifier (25) is bracketed-excluded** ⇒ its spend is admissible
(a valid `inner` gap exists). -/
theorem demo_fresh_admissible : (25 : ℤ) ∉ demoSpine :=
  sorted_gap_excludes demoSpine 20 30 25 demoSpine_sorted demoSpine_adjacent
    (by norm_num) (by norm_num)

-- ANTI-GHOST: an ALREADY-SPENT nullifier (20) is PRESENT ⇒ no gap can exclude it ⇒ no witness ⇒
-- the double-spend gate refuses it. The set cannot double-count.
#guard decide ((20 : ℤ) ∈ demoSpine)
#guard decide ((25 : ℤ) ∈ demoSpine) == false
-- The INSERT grows the spent-set by EXACTLY the fresh nullifier, in sorted order:
#guard sortedInsert (25 : ℤ) demoSpine == [10, 20, 25, 30]
#guard sortedInsert (5 : ℤ) demoSpine == [5, 10, 20, 30]
-- ...and re-inserting an already-spent nullifier is a no-op (no double-count):
#guard sortedInsert (20 : ℤ) demoSpine == [10, 20, 30]

/-! ## §AXIOM HYGIENE. -/

#assert_axioms witness_fresh
#assert_axioms present_no_witness
#assert_axioms spend_inserts_root
#assert_axioms spend_then_no_rewitness
#assert_axioms no_double_spend_root
#assert_axioms revoked_gate_fails
#assert_axioms witness_inhabited_of_bindings

end Dregg2.Exec.NullifierAccumulator
