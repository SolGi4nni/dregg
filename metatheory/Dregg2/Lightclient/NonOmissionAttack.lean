/-
# Dregg2.Lightclient.NonOmissionAttack — REFUTE-AND-REPAIR the non-omission light-client guarantee.

`AttestedQuery.light_client_query_non_omission` and `MMR.light_client_position_non_omission` are
`#assert_axioms`-clean, but each consumes a HYPOTHESIS `hweld : CommitBindsIndex/CommitBindsMMR …
(ChainStep.newRoot …) …` — "the per-turn state commitment the IVC chain folds absorbs the
receipt-index/MMR root as a sponge limb". This module asks whether that obligation has an HONEST
discharge against the commit the deployed chain actually folds, then closes the gap.

## §1 — THE REPAIR, WELDED INTO THE AGGREGATION MODEL (the chain folds the rotated commit)

The aggregation model now folds `ChainStep.newRoot CH RH cmb compress compressN s =
HistoryAggregation.chainedCommit … s.post s.turn = compressN [recStateCommit … s.post.kernel s.turn,
logRoot … s.post.log]` — the deployed rotated commit `hash_many [d, iroot]`. The kernel-digest LIMB `d
= recStateCommit … k t` is still blind to the receipt log (`recStateCommit k t = cmb (cellDigest … k t)
(RH k)`, and `RH` is injective on the sixteen NON-CELL kernel components — accounts · caps · bal ·
nullifiers · revoked · commitments · slotCaveats · factories · lifecycle · deathCert · delegate ·
delegations · delegationEpoch · delegationEpochAt · heaps — **the receipt log is NOT among them**); that
is precisely WHY the rotated commit absorbs the log as its SECOND limb:

  * `recStateCommit_admits_receipt_omission` — the kernel-digest limb ALONE is LITERALLY unchanged
    (`rfl`) when a receipt is dropped, while the receipt-log MMR roots MOVE (unless the omitting
    server exhibits the named collision — `MMR.MRootColl`, the honest 2026-07-28 form). The
    residual a kernel-only chained commit would leave open.
  * `newRoot_binds_log` — the rotated `chainedCommit` CLOSES it: two steps sharing a turn whose
    `newRoot`s agree have EQUAL receipt logs (`HistoryAggregation.root_tooth_pins_log`, the outer
    sponge peel + `logRoot_injective`). A dropped/forged/reordered receipt MOVES the published commit;
    the light client catches it. So `hweld` over the per-turn commitment is now DISCHARGED by the model.

## §2 — the ROOT FACE grounded (the single deployed commit)

The deployed Rust binds it: post-G4 the live chained commit is the ROTATED WIDE commitment
(`circuit/src/effect_vm/trace_rotated.rs`, `B_IROOT = 37`, `state_commit = hash_many [d, iroot]`;
`turn/src/executor/proof_verify.rs:349` "iroot … absorbed INTO the v9 commitment, which the proof
binds"). The Lean twin is `RotationLayout.rotatedCommit`, whose `rotatedCommit_binds_mmr` discharges
`CommitBindsMMR` **by `rfl`**. So the grounded theorems chain the rotated commit and consume the
PROVEN binding — NO `hweld`:

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

## §3/§4 — the residual CLOSED (whole-history non-omission, no `hweld`)

§2's grounded theorems are the ROOT FACE — non-omission for ONE deployed published commit. The lift to
WHOLE-HISTORY (`AggregateAttests` over every folded step) needed the IVC aggregation model itself to
fold the rotated commit. That is now DONE: `HistoryAggregation.chainedCommit` (= `hash_many [d, iroot]`,
the deployed rotated commit) IS the per-turn commitment the chain folds (`ChainStep.oldRoot/newRoot`),
so its receipt-log limb binds the log at EVERY step (`root_tooth_pins_log`). §4 re-exposes the closed
headline `light_client_whole_history_non_omission` (= `RecursiveAggregation.non_omission_from_verification`):
`verify agg.root = true` ⟹ `LogChained` over the whole history — omission impossible everywhere, no
`hweld`. The aggregation model no longer lags the deployed Rust.

## Axiom hygiene, and what the MMR face costs after the 2026-07-28 port
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem.

The MMR-face theorems (`recStateCommit_admits_receipt_omission`,
`commit_absorbing_root_pins_log_uniquely`, `light_client_position_non_omission_grounded`, and BOTH of
§3's MMR witnesses) no longer carry `Poseidon2SpongeCR` at all: they take per-instance, decidable,
refutable residuals (`MMR.CommitColl` / `MMR.MRootColl`) at the pairs the total extractors NAME.
Worth ~2^15.5 queries at the deployed 1-felt root (`Lightclient/MMR.lean` header) — a real number,
where the floor was a false one.

⚠ THE SORTED-INDEX FACE STILL CARRIES IT. `light_client_query_non_omission_grounded` and its witness
`grounded_idx_fires_honest` route through `AttestedQuery.commit_pins_index` / `iroot`, a DIFFERENT
cone with its own extractors still unwritten, so both keep the refuted floor and both stay in
`FloorRatchetBaseline`. `grounded_idx_fires_honest` is therefore a satisfiability witness conditioned
on a hypothesis that is false where the system stands — i.e. it demonstrates nothing at deployment.
Named here rather than left to be rediscovered; it is the sorted cone's port to make.
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
open Dregg2.Circuit.StateCommit (recStateCommit compressNInjective)
open Dregg2.Distributed.HistoryAggregation (ChainStep stateRoot chainedCommit logRoot logRoot_injective
  root_tooth_pins_log LogChained LogGenesisPin SeamStruct)
open Dregg2.Circuit.RecursiveAggregation (Aggregate EngineSound non_omission_from_verification)

/-! ## §1 — THE REPAIR, WELDED INTO THE MODEL: the chain now folds the rotated commit (binds the log).

The kernel-only `recStateCommit` was BLIND to the receipt log; the canonical aggregation model now folds
`HistoryAggregation.chainedCommit` (= `hash_many [d, iroot]`, the deployed rotated commit), so
`ChainStep.newRoot` ABSORBS the receipt-log root as its second limb. The blindness is now a property of
the KERNEL-DIGEST LIMB ALONE (`stateRoot`, the FIRST limb) — which is exactly WHY the rotated commit
adds the second. -/

/-- **The rotated commit BINDS the receipt log (the repair).** `ChainStep.newRoot` is now the rotated
`chainedCommit`, which absorbs `logRoot … st.log`. Two steps sharing a turn whose `newRoot`s agree have
EQUAL receipt logs — directly `HistoryAggregation.root_tooth_pins_log`, here for two `newRoot`s. A node
that drops/forges/reorders a receipt MOVES the published commit; a pure light client, holding only that
commit, now CATCHES it. (Contrast the pre-repair `newRoot_blind_to_log`, which this supersedes.) -/
theorem newRoot_binds_log
    (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
    (RH : Dregg2.Exec.RecordKernelState → ℤ)
    (cmb : ℤ → ℤ → ℤ) (compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (hCompressN : compressNInjective compressN)
    (s s' : ChainStep) (ht : s.turn = s'.turn)
    (h : ChainStep.newRoot CH RH cmb compress compressN s
          = ChainStep.newRoot CH RH cmb compress compressN s') :
    s.post.log = s'.post.log := by
  unfold ChainStep.newRoot chainedCommit at h
  rw [ht] at h
  have hlimbs := hCompressN _ _ h
  simp only [List.cons.injEq, and_true] at hlimbs
  exact logRoot_injective compressN hCompressN hlimbs.2

/-- **The kernel-digest LIMB alone admits omission — WHY the rotated commit needs the log root.** The
FIRST limb `stateRoot … k t` (= `recStateCommit`, the kernel digest) is a function of the kernel and
turn ALONE: the full receipt log and ANY log with a receipt omitted map to the SAME kernel-digest limb
(`rfl`), while their receipt-log MMR roots MOVE. This is the residual that a kernel-ONLY chained
commit would have left open — and precisely what the rotated commit's SECOND limb (`logRoot`,
`newRoot_binds_log` above) closes.

⚑ PORTED 2026-07-28, AND ITS CONCLUSION WAS AS FALSE AS ITS PREMISE. This theorem used to take
`hCR : Poseidon2SpongeCR hash` and conclude, for ARBITRARY distinct logs,
`mroot hash full ≠ mroot hash dropped`. That conclusion IS injectivity of `mroot hash`, and
`MMR.mroot_not_injective_of_singleton_collision` refutes it at any sponge with a singleton collision —
`Storage.DeployedFloorRegrounded.mroot_conclusion_false_at_deployed` does so at the deployed
`poseidon2Hash` by `rfl`. So the old statement was refuted premise ⟹ refuted conclusion: it could
never have been cited honestly in either direction. The honest form names the escape rather than
assuming it away: the roots MOVE, unless the omitting server exhibits the collision the extractor
points at — and that exhibition itself refutes the floor (`MMR.mrootColl_refutes_poseidon2CR`). -/
theorem recStateCommit_admits_receipt_omission
    (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
    (RH : Dregg2.Exec.RecordKernelState → ℤ)
    (cmb : ℤ → ℤ → ℤ) (compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (hash : List ℤ → ℤ)
    (k : Dregg2.Exec.RecordKernelState) (t : Dregg2.Exec.Turn)
    (full dropped : List ℤ) (hne : full ≠ dropped) :
    stateRoot CH RH cmb compress compressN k t
        = stateRoot CH RH cmb compress compressN k t
      ∧ (mroot hash full ≠ mroot hash dropped ∨ MRootColl hash full dropped) := by
  refine ⟨rfl, ?_⟩
  by_cases hr : mroot hash full = mroot hash dropped
  · exact Or.inr ((mroot_binds_or_collides hash hr).resolve_left hne)
  · exact Or.inl hr

/-- **The CONTRAST that drives the repair: a commit absorbing the log pins it UNIQUELY.** Two
`CommitBindsMMR` openings of ONE commit force EQUAL logs (`commit_pins_mmr`). The kernel commit
cannot supply this — it is the SAME for distinct logs (`recStateCommit_admits_receipt_omission`), so
`CommitBindsMMR hash limbs (recStateCommit … k t) log` has no honest discharge for the deployed log.
A commit that DOES absorb the root (the rotated commit, §2) regains this uniqueness — which is
exactly why binding to it makes non-omission real. -/
theorem commit_absorbing_root_pins_log_uniquely
    (hash : List ℤ → ℤ)
    {limbs limbs' : List ℤ} {c : ℤ} {L L' : List ℤ}
    (hb : CommitBindsMMR hash limbs c L) (hb' : CommitBindsMMR hash limbs' c L')
    (hnc : ¬ CommitColl hash limbs limbs' L L') (hnr : ¬ MRootColl hash L' L) : L = L' :=
  (commit_pins_mmr hash hb hb' hnc hnr).symm

#assert_axioms newRoot_binds_log
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
    (hash : List ℤ → ℤ)
    (s : RotatedLimbs) (L : List ℤ)
    {limbs' : List ℤ} {L' : List ℤ}
    (hopen : CommitBindsMMR hash limbs' (rotatedCommit hash s L) L')
    (hnc : ¬ CommitColl hash s.toList limbs' L L') (hnr : ¬ MRootColl hash L' L)
    {lo hi : ℕ} {vals : List ℤ}
    (hv : RVerifies L' lo hi vals) :
    vals = mrange L lo hi
    ∧ ∀ i, lo ≤ i → i ≤ hi → i < L.length →
        ∃ v, vals[i - lo]? = some v ∧ Opens L i v := by
  have hbind : CommitBindsMMR hash s.toList (rotatedCommit hash s L) L :=
    rotatedCommit_binds_mmr hash s L
  have hpin : L' = L := commit_pins_mmr hash hbind hopen hnc hnr
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
    (hash : List ℤ → ℤ)
    (s : RotatedLimbs) (L : List ℤ) (lo hi : ℕ) :
    mrange L lo hi = mrange L lo hi :=
  (light_client_position_non_omission_grounded hash s L
    (rotatedCommit_binds_mmr hash s L)
    (commitColl_dischargeable hash s.toList L) (mrootColl_dischargeable hash L)
    (exact_range_verifies L lo hi)).1

/-- **Witness FALSE — the omission is REJECTED.** A server presenting the SKIPPED answer `[333]`
(position 1 dropped) for range `[1,2]` over the genuine commit cannot exist: the grounded theorem
forces `[333] = mrange demoLog 1 2 = [222, 333]`, absurd. The dropped receipt is caught. -/
theorem grounded_mmr_rejects_omission
    (hash : List ℤ → ℤ)
    {limbs' : List ℤ} {L' : List ℤ}
    (hopen : CommitBindsMMR hash limbs' (rotatedCommit hash demoLimbs demoLog) L')
    (hnc : ¬ CommitColl hash demoLimbs.toList limbs' demoLog L')
    (hnr : ¬ MRootColl hash L' demoLog)
    (hv : RVerifies L' 1 2 [333]) : False := by
  have heq :=
    (light_client_position_non_omission_grounded hash demoLimbs demoLog hopen hnc hnr hv).1
  exact absurd heq (by decide)

/-- **Witness FALSE, UNCONDITIONAL FORM — the omitting server has EXHIBITED a collision.** No
hypothesis at all on the sponge: a prover that opens the genuine deployed commit and gets the SKIPPED
answer `[333]` accepted has, by that very fact, produced one of the two NAMED collisions the
extractors point at. This is the honest shape of "the omission is caught": at the deployed 1-felt
sponge such a collision costs ~2^15.5 queries, and saying so is the whole content — the old version
of this witness assumed `Poseidon2SpongeCR` and therefore fired for nobody at deployment. -/
theorem grounded_mmr_omission_forces_collision
    (hash : List ℤ → ℤ) {limbs' : List ℤ} {L' : List ℤ}
    (hopen : CommitBindsMMR hash limbs' (rotatedCommit hash demoLimbs demoLog) L')
    (hv : RVerifies L' 1 2 [333]) :
    CommitColl hash demoLimbs.toList limbs' demoLog L' ∨ MRootColl hash L' demoLog := by
  by_contra hn
  push_neg at hn
  exact grounded_mmr_rejects_omission hash hopen hn.1 hn.2 hv

/-- **Witness TRUE — the sorted-map face FIRES** (the honest opening returns the complete answer). -/
theorem grounded_idx_fires_honest
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (s : RotatedLimbs) (idx : ReceiptIndex) (hs : SortedKeys idx) (lo hi : ReceiptKey) :
    AnswerComplete idx lo hi (exactAnswer idx lo hi) :=
  (light_client_query_non_omission_grounded hash hCR s idx hs
    (rotatedCommitIdx_binds_index hash s idx) (exact_answer_verifies idx lo hi hs)).1

#assert_axioms grounded_mmr_fires_honest
#assert_axioms grounded_mmr_rejects_omission
#assert_axioms grounded_mmr_omission_forces_collision
#assert_axioms grounded_idx_fires_honest

/-! ## §4 — WHOLE-HISTORY: the §3 residual CLOSED (the aggregation model folds the rotated commit).

§2 grounded the ROOT FACE — non-omission for ONE deployed published commit. The §3 residual was the
WHOLE-HISTORY lift: it needed the IVC aggregation model to fold the rotated commit, `stateRoot :=
rotatedCommit` in place of the kernel `recStateCommit`. That is now DONE: `HistoryAggregation.chainedCommit`
(= `hash_many [d, iroot]`) IS the per-turn commitment the chain folds (`ChainStep.oldRoot/newRoot`), so
its second limb binds the receipt log at EVERY folded step (`root_tooth_pins_log`). The whole-history
non-omission headline is therefore DERIVED from the one client check `verify agg.root = true`, with NO
`hweld`: `RecursiveAggregation.non_omission_from_verification` yields `LogChained` over the entire
attested history. We re-expose it here, in the grounded home, as the closed §3 residual. -/

/-- **`light_client_whole_history_non_omission` — the §3 residual CLOSED.** A light client that checks
ONLY `verify agg.root = true` learns the receipt log chains genuinely across the WHOLE history
(`LogChained g steps`): no node dropped / forged / reordered / truncated a receipt at ANY folded step.
The receipt-log binding is the rotated commit's second limb welded into the aggregation model
(`root_tooth_pins_log`), discharged under the one CR floor (`compressNInjective`) — there is NO `hweld`
hypothesis. This is `RecursiveAggregation.non_omission_from_verification`, the whole-history twin of §2's
single-commit grounded non-omission. -/
theorem light_client_whole_history_non_omission
    {Proof : Type} {verify : Proof → Bool}
    {CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ}
    {RH : Dregg2.Exec.RecordKernelState → ℤ}
    {cmb : ℤ → ℤ → ℤ} {compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    (hCompressN : compressNInjective compressN)
    {agg : Aggregate Proof} {g : Dregg2.Exec.RecChainedState} {steps : List ChainStep}
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
    (hroot : verify agg.root = true)
    (hgen : LogGenesisPin g steps) (hstruct : SeamStruct steps) :
    LogChained g steps :=
  non_omission_from_verification Proof verify CH RH cmb compress compressN
    hCompressN agg g steps es hroot hgen hstruct

#assert_axioms newRoot_binds_log
#assert_axioms light_client_whole_history_non_omission

end Dregg2.Lightclient.NonOmissionAttack
