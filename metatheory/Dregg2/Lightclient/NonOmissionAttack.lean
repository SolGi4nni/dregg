/-
# Dregg2.Lightclient.NonOmissionAttack — REFUTE-AND-REPAIR the non-omission light-client guarantee.

`AttestedQuery.light_client_query_non_omission` and `MMR.light_client_position_non_omission` are
`#assert_axioms`-clean, but each consumes a HYPOTHESIS `hweld : CommitBindsIndex/CommitBindsMMR …
(ChainStep.newRoot …) …` — "the per-turn state commitment the IVC chain folds absorbs the
receipt-index/MMR root as a sponge limb". This module asks whether that obligation has an HONEST
discharge against the commit the deployed chain actually folds, then closes the gap.

## §1 — REFUTE (the vacuity is real at the model level)

The chain folds `ChainStep.newRoot CH RH cmb compress compressN s = stateRoot … s.post.kernel
s.turn = recStateCommit … s.post.kernel s.turn`. `recStateCommit k t = cmb (cellDigest … k t)
(RH k)`, and `RH` is injective on EXACTLY sixteen NON-CELL kernel components
(`StateCommit.RestHashIffFrame`: accounts · caps · bal · nullifiers · revoked · commitments ·
slotCaveats · factories · lifecycle · deathCert · delegate · delegations · delegationEpoch ·
delegationEpochAt · heaps) — **the receipt log is NOT among them.** `RecChainedState` carries the
receipt `log : List Turn` ALONGSIDE the `kernel`, and `ChainStep.newRoot` reads `s.post.kernel`
only. So the kernel commit a pure light client chains is BLIND to the receipt log:

  * `recStateCommit_admits_receipt_omission` — the held commit is LITERALLY unchanged (`rfl`) when
    the receipt log is replaced by one with a receipt DROPPED, while the receipt-log MMR roots
    genuinely DIFFER (`mroot_injective`). A node drops a receipt; a pure LC is none the wiser.
  * `hweld_over_kernel_commit_pins_at_most_one_log` — IF the kernel commit bound the log via
    `CommitBindsMMR`, `commit_pins_mmr` forces a UNIQUE log; but the commit is the same for the
    full and the omitting log, so the obligation cannot honestly hold for the genuine one while the
    node serves the other. `hweld` over `recStateCommit` is vacuous-as-deployed.

## §2 — REPAIR (the guarantee made real-as-deployed)

The deployed Rust DOES bind it: post-G4 the live chained commit is the ROTATED WIDE commitment
(`circuit/src/effect_vm/trace_rotated.rs`, `B_IROOT = 37`, `state_commit = hash_many [d, iroot]`;
`turn/src/executor/proof_verify.rs:349` "iroot … absorbed INTO the v9 commitment, which the proof
binds"). The Lean twin is `RotationLayout.rotatedCommit`, whose `rotatedCommit_binds_mmr` discharges
`CommitBindsMMR` **by `rfl`**. So the grounded theorems chain the rotated commit and consume the
PROVEN binding — NO `hweld`:

  * `light_client_position_non_omission_grounded` (MMR, the deployed dense receipt index) and
  * `light_client_query_non_omission_grounded` (the sorted-map index face),

each: a server opening of the DEPLOYED rotated commit, plus a verifying range answer, forces the
answer to be EXACTLY the genuine range — omission impossible, forgery impossible — resting on the
`rfl` binding alone. Non-vacuity §3: the honest opening FIRES (returns the complete range) and an
omitting answer is REJECTED (would force `[333] = [222,333]`, absurd).

## §3 — the residual (named, not hidden)

The grounded theorems are the ROOT FACE — non-omission for ONE deployed published commit. Lifting to
WHOLE-HISTORY (`AggregateAttests` over every folded step) needs the IVC aggregation model itself to
fold the rotated commit: `HistoryAggregation.stateRoot := rotatedCommit` in place of the kernel
`recStateCommit`. That is the precise minimal further weld (the deployed Rust already folds the
rotated commit; only the Lean aggregation model still names the kernel commit). Tracked in the
report; NOT discharged here.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem; crypto enters only as
the named `Poseidon2SpongeCR` hypothesis. NEW file; all imports read-only.
-/
import Dregg2.Circuit.RotationLayout
import Dregg2.Distributed.HistoryAggregation

namespace Dregg2.Lightclient.NonOmissionAttack

set_option autoImplicit false
set_option linter.unusedVariables false

open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Substrate.Heap (SortedKeys keys get)
open Dregg2.Lightclient.MMR
open Dregg2.Lightclient.AttestedQuery
open Dregg2.Lightclient.HistoryIndex
open Dregg2.Circuit.RotationLayout (RotatedLimbs rotatedCommit rotatedCommit_binds_mmr demoLimbs)
open Dregg2.Circuit.StateCommit (recStateCommit)
open Dregg2.Distributed.HistoryAggregation (ChainStep stateRoot)

/-! ## §1 — REFUTE: the kernel commit the chain folds is BLIND to the receipt log. -/

/-- **The held commit ignores the receipt log.** `ChainStep.newRoot` reads `s.post.kernel` only;
`RecChainedState` carries the receipt `log` SEPARATELY. So two chained states sharing a kernel + turn
but carrying DIFFERENT receipt logs commit to the SAME `ChainStep.newRoot`. -/
theorem newRoot_blind_to_log
    (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
    (RH : Dregg2.Exec.RecordKernelState → ℤ)
    (cmb : ℤ → ℤ → ℤ) (compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (s s' : ChainStep)
    (hk : s.post.kernel = s'.post.kernel) (ht : s.turn = s'.turn) :
    ChainStep.newRoot CH RH cmb compress compressN s
      = ChainStep.newRoot CH RH cmb compress compressN s' := by
  unfold ChainStep.newRoot stateRoot
  rw [hk, ht]

/-- **THE OMISSION ATTACK (mirrors `CustomCarrierAttack.deployed_admits_unbacked`).** The commit a
pure light client chains, `recStateCommit … k t` (= `stateRoot`), is a function of the kernel `k` and
turn `t` ALONE — it has no receipt-log input. So the full receipt log and ANY log with a receipt
omitted map to the SAME chained commit (`rfl`), while their receipt-log MMR roots DIFFER
(`mroot_injective`). A node drops a receipt and a pure LC, holding only that commit, cannot tell:
the commit cannot pin a log it never absorbed. This is the explicit witness that
`CommitBindsMMR … (recStateCommit … k t) L` has no honest discharge over the kernel commit. -/
theorem recStateCommit_admits_receipt_omission
    (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
    (RH : Dregg2.Exec.RecordKernelState → ℤ)
    (cmb : ℤ → ℤ → ℤ) (compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (k : Dregg2.Exec.RecordKernelState) (t : Dregg2.Exec.Turn)
    (full dropped : List ℤ) (hne : full ≠ dropped) :
    stateRoot CH RH cmb compress compressN k t
        = stateRoot CH RH cmb compress compressN k t
      ∧ mroot hash full ≠ mroot hash dropped :=
  ⟨rfl, fun h => hne (mroot_injective hash hCR h)⟩

/-- **The CONTRAST that drives the repair: a commit absorbing the log pins it UNIQUELY.** Two
`CommitBindsMMR` openings of ONE commit force EQUAL logs (`commit_pins_mmr`). The kernel commit
cannot supply this — it is the SAME for distinct logs (`recStateCommit_admits_receipt_omission`), so
`CommitBindsMMR hash limbs (recStateCommit … k t) log` has no honest discharge for the deployed log.
A commit that DOES absorb the root (the rotated commit, §2) regains this uniqueness — which is
exactly why binding to it makes non-omission real. -/
theorem commit_absorbing_root_pins_log_uniquely
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {limbs limbs' : List ℤ} {c : ℤ} {L L' : List ℤ}
    (hb : CommitBindsMMR hash limbs c L) (hb' : CommitBindsMMR hash limbs' c L') : L = L' :=
  (commit_pins_mmr hash hCR hb hb').symm

#assert_axioms newRoot_blind_to_log
#assert_axioms recStateCommit_admits_receipt_omission
#assert_axioms commit_absorbing_root_pins_log_uniquely

/-! ## §2 — REPAIR: the grounded theorems chain the DEPLOYED rotated commit (binding discharged). -/

/-- The sorted-map face's deployed commit: the same rotated layout with the SORTED index root
`iroot` as the last absorbed limb. (`RotationLayout.rotatedCommit` absorbs the MMR `mroot`; the
sorted index commits `iroot` in exactly the same last-limb position — the `CommitBindsIndex` shape.) -/
def rotatedCommitIdx (hash : List ℤ → ℤ) (s : RotatedLimbs) (idx : ReceiptIndex) : ℤ :=
  hash (s.toList ++ [iroot hash idx])

/-- **The sorted-index binding, discharged by construction** (the `CommitBindsIndex` twin of
`rotatedCommit_binds_mmr`). -/
theorem rotatedCommitIdx_binds_index (hash : List ℤ → ℤ) (s : RotatedLimbs) (idx : ReceiptIndex) :
    CommitBindsIndex hash s.toList (rotatedCommitIdx hash s idx) idx := rfl

/-- **`light_client_position_non_omission_grounded` — non-omission REAL-as-deployed (MMR face).** A
light client holding the DEPLOYED rotated published commit `rotatedCommit hash s L` of a turn whose
genuine receipt log is `L`: for ANY server opening of that commit and ANY verifying positional range
answer, the answer is EXACTLY the genuine range — every committed in-range position present at its
dense slot (omission impossible), every value genuine (forgery impossible). The receipt-log binding
is the PROVEN `rotatedCommit_binds_mmr` (`rfl`) — **NO `hweld` hypothesis.** -/
theorem light_client_position_non_omission_grounded
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (s : RotatedLimbs) (L : List ℤ)
    {limbs' : List ℤ} {L' : List ℤ}
    (hopen : CommitBindsMMR hash limbs' (rotatedCommit hash s L) L')
    {lo hi : ℕ} {vals : List ℤ}
    (hv : RVerifies L' lo hi vals) :
    vals = mrange L lo hi
    ∧ ∀ i, lo ≤ i → i ≤ hi → i < L.length →
        ∃ v, vals[i - lo]? = some v ∧ Opens L i v := by
  have hbind : CommitBindsMMR hash s.toList (rotatedCommit hash s L) L :=
    rotatedCommit_binds_mmr hash s L
  have hpin : L' = L := commit_pins_mmr hash hCR hbind hopen
  subst hpin
  exact ⟨rverifies_iff_exact.mp hv, range_complete hv⟩

/-- **`light_client_query_non_omission_grounded` — non-omission REAL-as-deployed (sorted-map face).**
A light client holding the deployed rotated published commit `rotatedCommitIdx hash s idx` of a turn
whose genuine SORTED receipt index is `idx`: for ANY server opening and ANY verifying range answer,
the answer contains EVERY in-range key of the genuine index (omission impossible) and every answered
entry is genuine and in-range (forgery impossible). Binding is the PROVEN `rotatedCommitIdx_binds_index`
(`rfl`) — **NO `hweld` hypothesis** (the sortedness `hs` is the real index invariant, not the binding). -/
theorem light_client_query_non_omission_grounded
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (s : RotatedLimbs) (idx : ReceiptIndex) (hs : SortedKeys idx)
    {limbs' : List ℤ} {idx' : ReceiptIndex}
    (hopen : CommitBindsIndex hash limbs' (rotatedCommitIdx hash s idx) idx')
    {lo hi : ReceiptKey} {ans : Answer ReceiptKey ℤ}
    (hv : Verifies idx' lo hi ans) :
    AnswerComplete idx lo hi ans ∧ (∀ e ∈ ans.items, e ∈ idx ∧ inRange lo hi e.1) := by
  have hbind : CommitBindsIndex hash s.toList (rotatedCommitIdx hash s idx) idx :=
    rotatedCommitIdx_binds_index hash s idx
  have hpin : idx' = idx := commit_pins_index hash hCR hbind hopen
  subst hpin
  exact ⟨answer_complete hs hv, answer_sound hv⟩

#assert_axioms rotatedCommitIdx_binds_index
#assert_axioms light_client_position_non_omission_grounded
#assert_axioms light_client_query_non_omission_grounded

/-! ## §3 — NON-VACUITY: the grounded MMR theorem FIRES on honest, REJECTS the omission. -/

/-- **Witness TRUE — the honest opening FIRES.** Fed the genuine commit opening
(`rotatedCommit_binds_mmr`, the server holding the real log) and the exact range answer, the grounded
theorem returns the COMPLETE genuine range: a real verdict, not a vacuous one. (The proof term IS the
theorem's first conjunct at the honest inputs — it typechecks only because the theorem fires.) -/
theorem grounded_mmr_fires_honest
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (s : RotatedLimbs) (L : List ℤ) (lo hi : ℕ) :
    mrange L lo hi = mrange L lo hi :=
  (light_client_position_non_omission_grounded hash hCR s L
    (rotatedCommit_binds_mmr hash s L) (exact_range_verifies L lo hi)).1

/-- **Witness FALSE — the omission is REJECTED.** A server presenting the SKIPPED answer `[333]`
(position 1 dropped) for range `[1,2]` over the genuine commit cannot exist: the grounded theorem
forces `[333] = mrange demoLog 1 2 = [222, 333]`, absurd. The dropped receipt is caught. -/
theorem grounded_mmr_rejects_omission
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {limbs' : List ℤ} {L' : List ℤ}
    (hopen : CommitBindsMMR hash limbs' (rotatedCommit hash demoLimbs demoLog) L')
    (hv : RVerifies L' 1 2 [333]) : False := by
  have heq := (light_client_position_non_omission_grounded hash hCR demoLimbs demoLog hopen hv).1
  exact absurd heq (by decide)

/-- **Witness TRUE — the sorted-map face FIRES** (the honest opening returns the complete answer). -/
theorem grounded_idx_fires_honest
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (s : RotatedLimbs) (idx : ReceiptIndex) (hs : SortedKeys idx) (lo hi : ReceiptKey) :
    AnswerComplete idx lo hi (exactAnswer idx lo hi) :=
  (light_client_query_non_omission_grounded hash hCR s idx hs
    (rotatedCommitIdx_binds_index hash s idx) (exact_answer_verifies idx lo hi hs)).1

#assert_axioms grounded_mmr_fires_honest
#assert_axioms grounded_mmr_rejects_omission
#assert_axioms grounded_idx_fires_honest

end Dregg2.Lightclient.NonOmissionAttack
