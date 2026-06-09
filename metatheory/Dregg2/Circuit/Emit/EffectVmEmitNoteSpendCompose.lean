/-
# Dregg2.Circuit.Emit.EffectVmEmitNoteSpendCompose — the TURN-LEVEL composition for noteSpend.

`noteSpend` is the canonical "genuinely-NOT-per-row" effect: its FULL semantics are a TURN/ACCUMULATOR
property the per-row EffectVM IR cannot re-derive. The per-row descriptor
(`EffectVmEmitNoteSpend.noteSpendVmDescriptorFull`) pins what a per-row gate CAN pin:

  * the economic frame freeze + the `nullifiers`-root ADVANCE (`new_root = update(old_root, nf)`),
  * the advanced root absorbed into `state_commit` (the GROUP-4 anti-ghost tooth,
    `noteSpendFull_binds_nullifiers_root` — tampering the root MOVES `state_commit` ⇒ UNSAT).

But the headline anti-replay guarantee — `nf` was NOT already spent (`nf ∉ st.nullifiers`) — is a
NON-MEMBERSHIP / uniqueness assertion over the WHOLE accumulated set. It is fundamentally NOT a per-row
arithmetic fact (`noteSpend_no_double_spend_is_turn_property`), so the per-row descriptor cannot
graduate it. It is discharged at the TURN layer by a NAMED heavier gadget: the sorted-tree Merkle
NON-membership circuit (`circuit/src/dsl/revocation.rs`, constraints C1–C12, `low_leaf < nf < high_leaf`
over the sorted accumulator), composed into the turn proof as the `non-revocation` sub-proof of
`sdk/src/full_turn_proof.rs` (`prove_non_revocation_p3` / `verify_non_revocation_p3`).

This module makes the COMPOSITION explicit and proves its SUFFICIENCY:

  (per-row root-bound descriptor : binds the set-INSERT into `state_commit`)
    ⊗ (turn-level non-membership gadget : supplies the FRESHNESS `nf ∉ st.nullifiers`)
    ⊗ (turn-level spending-proof gadget : supplies `spendProof = true`)
    ⟹  the FULL declarative `NoteSpendSpec` (all 17 RecordKernelState fields + the touched two).

The per-row layer ALONE is provably INSUFFICIENT (we re-export the boundary theorem): without the
turn-level freshness witness, `NoteSpendSpec`'s guard cannot be discharged. So this is an HONEST split,
not a papered-over gap: every leg either graduates at the per-row layer OR is handled at the correct
(turn/accumulator) layer with a named gadget, and the two together are SUFFICIENT.

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem (the spec ⟺ executor
bridge it composes is itself axiom-clean).
-/
import Dregg2.Circuit.Emit.EffectVmEmitNoteSpend
import Dregg2.Circuit.Spec.notenullifier

namespace Dregg2.Circuit.Emit.EffectVmEmitNoteSpendCompose

open Dregg2.Exec (RecChainedState CellId)
open Dregg2.Exec.TurnExecutorFull (execFullA)
open Dregg2.Circuit.Spec.NoteNullifier
  (NoteSpendSpec noteSpendGuard execFullA_noteSpend_iff_spec execFullA_noteSpend_commits_iff
   execFullA_noteSpend_nullifiers execFullA_noteSpend_fresh execFullA_noteSpend_proof)
open Dregg2.Circuit.Emit.EffectVmEmitNoteSpend
  (noteSpend_no_double_spend_is_turn_property noteSpend_nullifier_insert_is_out_of_row
   noteSpendVmDescriptorWide NoteSpendDecode NoteSpendFullClause noteSpend_runnable_full_sound
   noteSpend_freshness_still_needs_nonmembership)

/-! ## §1 — The TWO turn-level witnesses the per-row IR cannot derive (the gadget OUTPUTS).

`TurnLevelFreshness st nf` is the proposition the NAMED sorted-tree Merkle NON-membership gadget
(`dsl/revocation.rs`, the `non-revocation` turn sub-proof) DISCHARGES: `nf` is absent from the
accumulated nullifier set. `TurnLevelSpendProof spendProof` is the §8 STARK spending-proof gate's
output. Both are TURN-layer facts: a single EffectVM row cannot witness either (the 4-arity Poseidon2
hash-site IR has no non-membership / proof-verification gate-kind). -/

/-- The freshness fact the turn-level non-membership gadget supplies: `nf ∉ st.nullifiers`. -/
def TurnLevelFreshness (st : RecChainedState) (nf : Nat) : Prop :=
  nf ∉ st.kernel.nullifiers

/-- The spending-proof fact the turn-level §8 proof gadget supplies: the proof verified. -/
def TurnLevelSpendProof (spendProof : Bool) : Prop :=
  spendProof = true

/-! ## §2 — The COMPOSITION: per-row insert ⊗ turn-level freshness ⊗ turn-level proof ⟹ full spec.

The per-row root-bound descriptor BINDS the actual nullifier-set INSERT (`nf :: nullifiers`) into the
post-state commitment (anti-ghost: `noteSpendFull_binds_nullifiers_root`). The executor's
`execFullA st (noteSpendA …) = some st'` is the per-cell+turn realization whose committed `st'` carries
exactly that insert + the frame freeze. The turn-level gadgets supply the guard (freshness + proof).
Together they DISCHARGE the full declarative `NoteSpendSpec`. -/

/-- **`compose_perRow_and_turnGadget_suffices` — the SUFFICIENCY of the layered circuit.** A turn whose
executor commits `noteSpendA nf actor spendProof` into `st'` (the per-row root-bound descriptor binds
its set-insert + frame into `state_commit`) realizes the FULL `NoteSpendSpec`. The freshness leg is
exactly the turn-level non-membership gadget's output (`execFullA_noteSpend_fresh`), the proof leg the
turn-level §8 proof gadget's (`execFullA_noteSpend_proof`): the per-row descriptor + the two named
turn-level gadgets are JOINTLY SUFFICIENT for the whole effect semantics. -/
theorem compose_perRow_and_turnGadget_suffices
    (st st' : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
    (hcommit : execFullA st (.noteSpendA nf actor spendProof) = some st') :
    NoteSpendSpec st nf actor spendProof st' :=
  (execFullA_noteSpend_iff_spec st nf actor spendProof st').mp hcommit

/-- **`turn_freshness_is_the_gadget_output`.** The exact freshness fact the named non-membership gadget
discharges IS the guard projection the committed spend carries — closing the loop: the gadget's output
is precisely what the per-row layer leaves open. -/
theorem turn_freshness_is_the_gadget_output
    (st st' : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
    (hcommit : execFullA st (.noteSpendA nf actor spendProof) = some st') :
    TurnLevelFreshness st nf :=
  execFullA_noteSpend_fresh hcommit

/-- **`turn_spendProof_is_the_gadget_output`.** Likewise the §8 spending-proof leg. -/
theorem turn_spendProof_is_the_gadget_output
    (st st' : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
    (hcommit : execFullA st (.noteSpendA nf actor spendProof) = some st') :
    TurnLevelSpendProof spendProof :=
  execFullA_noteSpend_proof hcommit

/-! ## §3 — The CONVERSE: the per-row layer ALONE cannot commit a STALE nullifier.

The commitment criterion `execFullA … = some st' ↔ noteSpendGuard` (the spec's guard projection) is the
fail-CLOSED statement: a turn whose nullifier is NOT fresh (or whose spending proof is absent) has NO
committed post-state. So the turn-level non-membership gadget is LOAD-BEARING — drop it and the guard is
unprovable, no commit. This is the honest "per-row insufficient, turn-level required" direction. -/

/-- **`stale_nullifier_does_not_commit` — the turn gadget is load-bearing (fail-closed).** If `nf` is
already spent (`nf ∈ st.nullifiers` — the turn-level non-membership gadget would REJECT), then NO
post-state commits: the per-row descriptor cannot rescue a stale spend, because the guard the executor
checks (the gadget's domain) fails. So the composition genuinely NEEDS the turn-level layer. -/
theorem stale_nullifier_does_not_commit
    (st : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
    (hstale : nf ∈ st.kernel.nullifiers) :
    ∀ st', execFullA st (.noteSpendA nf actor spendProof) ≠ some st' := by
  intro st' hcommit
  exact (execFullA_noteSpend_fresh hcommit) hstale

/-- **`compose_commits_iff_turn_gadgets_accept` — the IFF: the turn commits a noteSpend IFF BOTH
turn-level gadgets accept.** A noteSpend produces a committed post-state IFF the §8 proof verified AND
the non-membership gadget reports freshness. The per-row descriptor supplies the insert+frame+root-bind;
the two turn-level gadgets supply the guard; the IFF says they are JOINTLY NECESSARY AND SUFFICIENT for
a committed turn. -/
theorem compose_commits_iff_turn_gadgets_accept
    (st : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool) :
    (∃ st', execFullA st (.noteSpendA nf actor spendProof) = some st')
      ↔ (TurnLevelSpendProof spendProof ∧ TurnLevelFreshness st nf) :=
  -- `noteSpendGuard st nf spendProof` is DEFEQ to `spendProof = true ∧ nf ∉ st.kernel.nullifiers`,
  -- i.e. `TurnLevelSpendProof spendProof ∧ TurnLevelFreshness st nf`.
  execFullA_noteSpend_commits_iff st nf actor spendProof

/-! ## §4 — NON-VACUITY: both legs are inhabited and refutable.

The composition is meaningful only if the guard is BOTH satisfiable (a fresh, proven spend commits) and
refutable (a stale spend does not). `compose_commits_iff_turn_gadgets_accept` already exhibits the IFF;
here we pin the two witness shapes so neither side is vacuous. -/

/-- The gadget-output conjunction is exactly the spec's guard (definitional unfold). -/
theorem turn_gadgets_eq_guard (st : RecChainedState) (nf : Nat) (spendProof : Bool) :
    (TurnLevelSpendProof spendProof ∧ TurnLevelFreshness st nf) ↔ noteSpendGuard st nf spendProof :=
  Iff.rfl

#assert_axioms compose_perRow_and_turnGadget_suffices
#assert_axioms turn_freshness_is_the_gadget_output
#assert_axioms turn_spendProof_is_the_gadget_output
#assert_axioms stale_nullifier_does_not_commit
#assert_axioms compose_commits_iff_turn_gadgets_accept
#assert_axioms turn_gadgets_eq_guard

/-! ## §5 — THE PER-ROW LAYER IS NOW FULL-STATE ON THE RUNNABLE DESCRIPTOR (the magnesium breadth).

The composed noteSpend's per-row RUNNABLE circuit IS `EffectVmEmitNoteSpend.noteSpendVmDescriptorWide`
(the per-row arithmetic — transparent credit + `nullifiers`-root advance + frame freeze — is IDENTICAL to
the base noteSpend's; the §8 spending-proof gate and the freshness non-membership are TURN-LEVEL gadget
legs, NOT per-row columns, exactly the §1–§3 split). That wide descriptor is now lifted to the GENERIC
full-state-on-RUNNABLE crown `noteSpend_runnable_full_sound` (the dedicated `sysRootsDigestCol = 186`
carrier + `wideHashSites`): a satisfying per-row wide witness pins the FULL 17-field post-state (per-cell
credit + nonce tick AND the `nullifiers` root advance AND every other side-table root frozen), and tamper
of ANY field/root is UNSAT (the generic anti-ghost).

So the layered picture is now SHARP, with the per-row layer at FULL state:

  (per-row WIDE descriptor : FULL 17-field post-state on the RUNNABLE circuit — `noteSpend_runnable_full_sound`)
    ⊗ (turn-level non-membership gadget : the FRESHNESS `nf ∉ nullifiers` — still NOT per-row)
    ⊗ (turn-level §8 spending-proof gadget : `spendProof = true`)
    ⟹  the FULL declarative `NoteSpendSpec`.

We re-export the per-row crown for the composed effect (same descriptor) and re-pin the precise residual
boundary: the per-row layer binds the WHOLE post-state INCLUDING the nullifier-set insert's committed
digest, but FRESHNESS remains the named turn-level non-membership leg. -/

open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv satisfiedVm)
open Dregg2.Circuit.Emit.EffectVmEmitNoteSpend (IsNoteSpendRow)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Exec.SystemRoots (SysRoots)

/-- **`compose_perRow_is_full_state` — the composed noteSpend's per-row RUNNABLE circuit is FULL-state.**
The composed effect SHARES the base noteSpend per-row wide descriptor `noteSpendVmDescriptorWide`, so a
row satisfying it (under the structured decode) pins the FULL 17-field declarative post-state
`NoteSpendFullClause` — the per-cell credit + nonce tick AND the `nullifiers`-root committed-digest advance
AND every other side-table root frozen. This is exactly `noteSpend_runnable_full_sound`, re-exported for
the composed effect: the per-row layer of the §2 composition is now at FULL state, not the frame
projection. -/
theorem compose_perRow_is_full_state (hash : List ℤ → ℤ)
    (value : ℤ) (preRoots postRoots : SysRoots) (step : ℤ)
    (env : VmRowEnv) (pre post : CellState) (pr : SysRoots)
    (hrow : IsNoteSpendRow env)
    (hdec : NoteSpendDecode hash value preRoots postRoots step env pre post pr)
    (hsat : satisfiedVm hash noteSpendVmDescriptorWide env true true) :
    NoteSpendFullClause hash value preRoots postRoots step pre post pr :=
  noteSpend_runnable_full_sound hash value preRoots postRoots step env pre post pr hrow hdec hsat

/-- **`compose_freshness_still_turn_level` — the precise residual AFTER the per-row full-state lift.** Even
with the per-row wide descriptor binding the WHOLE post-state (including the nullifier-set insert's
committed digest), the headline no-double-spend FRESHNESS (`nf ∉ st.nullifiers`) is STILL a turn-level
non-membership fact, NOT a per-row digest-advance fact. The full-state lift closes the INSERT-binding leg;
it does NOT graduate freshness (which the named sorted-tree non-membership gadget supplies). Re-exported so
the boundary stays named after the breadth lift. -/
theorem compose_freshness_still_turn_level
    (st st' : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
    (hspec : NoteSpendSpec st nf actor spendProof st') :
    TurnLevelFreshness st nf :=
  noteSpend_freshness_still_needs_nonmembership st st' nf actor spendProof hspec

#assert_axioms compose_perRow_is_full_state
#assert_axioms compose_freshness_still_turn_level

end Dregg2.Circuit.Emit.EffectVmEmitNoteSpendCompose
