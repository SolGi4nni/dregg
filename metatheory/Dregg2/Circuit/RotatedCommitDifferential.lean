/-
# Dregg2.Circuit.RotatedCommitDifferential — the ROTATED wire-commit COMMITMENT DIFFERENTIAL
(the Lean model ⟺ the ACTUALLY-PUBLISHED Rust rotated commitment).

`Dregg2.Circuit.CommitDifferential` pins the deployed PER-CELL commitment (the Rust
`CellState::compute_commitment`: a `hash_4_to_1` tree over `[balLo, balHi, nonce, fields[0..8],
cap_root, record_digest]`, with the authority residue at the FIXED last index 12). But the LIGHT
CLIENT does not pin THAT tree — the rotated full-turn prover publishes the **rotated** commitment:
`OLD_COMMIT`/`NEW_COMMIT` are the row-0 / last-row `STATE_COMMIT` carriers of the rotated trace,
i.e. the cell-side `dregg_cell::commitment::compute_canonical_state_commitment_v9_felt`
(= the producer `dregg_turn::rotation_witness::wire_commit`) over the 32 rotated pre-iroot limbs

  `[cells_root, r0..r23, cap_root, nullifier_root, commitments_root, heap_root, lifecycle, epoch, committed_height]`

absorbed by the chained `wireCommitR` (4-wide head, 3-wide chip body, iroot ALONE last). The
authority residue that NO named rotated limb carries (permissions / VK / lifecycle-payload /
delegate / delegation / program / mode / token_id / visibility / commitments / proved_state /
side-table roots / fields[8..16]) rides register **r23**, which is list index **24** of the
pre-iroot limb list (limb 0 = cells_root, limbs 1..24 = r0..r23, so r23 sits at index 24), via the
SAME `dregg_cell::commitment::compute_authority_digest_felt` the per-cell `record_digest` uses.

This module makes "the PUBLISHED rotated commitment binds the FULL kernel — exactly as the per-cell
one does — at its OWN authority-residue position" a CHECKED Lean fact, the rotated twin of
`CommitDifferential`:

  * `rotatedLimbs …` — the ORDERED 32-limb pre-iroot list, in the Rust
    `compute_rotated_pre_limbs` absorption order, with `authorityDigest` NAMED at the FIXED index
    24 (= register r23), `capRoot` at index 25, `nullifierRoot` at 26, `commitmentsRoot` at 27 —
    exactly the positions the Rust producer fills
    (`rotation_witness.rs` `pre_limbs[24] = compute_authority_digest_felt`, `pre_limbs[25] =
    cap_root`) and the Lean `EffectVmEmitRotationV3.preLimbsAt`/`EffectVmEmitRotationR.preLimbs`
    layout pins.

  * `authority_digest_at_index_24` / `cap_root_at_index_25` — the named-correspondence pins
    (`rfl`): the published commitment's authority-residue limb is at index 24, the cap-root at 25.

  * `rotatedCommit` — the FAITHFUL Lean model of the published rotated commitment:
    `wireCommitR hash (rotatedLimbs …) iroot`, the SAME chained absorption the deployed
    `v9_wire_commit` / `rotation_witness::wire_commit` realize (and that
    `EffectVmEmitRotationR.wireCommitR` is the spec of).

  * `rotatedCommit_binds_authority_digest` (+ the per-limb binding family) — INJECTIVITY OVER THE
    FULL ROTATED LIMB LIST off the ONE realizable `Poseidon2SpongeCR hash` carrier (via the
    already-proven `EffectVmEmitRotationR.wireCommitR_binds`): the PUBLISHED rotated commitment
    binds the `authorityDigest` limb (and every other limb, and the iroot). So tampering the
    authority residue — a permission flip, a VK swap, a dropped side-table root — provably MOVES
    the PUBLISHED `OLD_COMMIT`/`NEW_COMMIT`. This is the rotated twin of
    `CommitDifferential.effectVmCommit_binds_record_digest`: the genuine "the published proof binds
    the deployed bytes" statement, on the commitment the light client actually pins.

  * `rotatedCommit_binds_cap_root` (corollary) — the published rotated commitment binds the
    openable c-list root at index 25 (the rotated twin of `effectVmCommit_binds_cap_root`).

  * the SHAPE CORRESPONDENCE (`rotated_and_perCell_both_bind_authority_residue`): the rotated
    authority-residue limb plays the SAME role at its OWN fixed index (24) that the per-cell
    `record_digest` plays at its fixed index (12) — both are the SINGLE authority-residue limb the
    commitment binds, both bound off one collision-resistance carrier, and in the deployed code both
    are LITERALLY `compute_authority_digest_felt(cell)`. Stated as one conjunction so the two
    differentials are visibly the SAME closure on two commitment shapes.

  * the VACUITY GUARD: concrete computable `#guard`s over the injective Horner toy sponge
    (`Dregg2.Substrate.Heap.refSponge`) — the authority-digest limb (24) is load-bearing (a cell
    whose ONLY change is its authority residue PUBLISHES a different rotated commitment), the
    cap-root limb (25) is load-bearing, the iroot is bound, and the honest recompute is stable.

Pure, computable, `#guard`-able (no `native_decide`). The carried `Poseidon2SpongeCR hash` is the
SAME ONE named CR floor `EffectVmEmitRotationR` already runs on, never an `axiom`, never a `+`-fold.
The Rust-side empirical twin is `circuit/tests/effect_vm_rotation_flip.rs`
(`rotated_published_commit_moves_on_permission_flip`): the REAL
`compute_canonical_state_commitment_v9_felt` over the SAME limb order, and a permission flip MOVES
the published rotated commitment (the P0-2 non-vacuity on the ACTUALLY-PUBLISHED commitment).
-/
import Dregg2.Circuit.Emit.EffectVmEmitRotationR
import Dregg2.Circuit.CommitDifferential

namespace Dregg2.Circuit.RotatedCommitDifferential

open Dregg2.Circuit.Emit.EffectVmEmitRotationR (wireCommitR wireCommitR_binds)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Substrate.Heap (refSponge)

set_option autoImplicit false

/-! ## §1 — the ORDERED rotated pre-iroot limb list, with the authority residue NAMED at index 24.

`rotatedLimbs` is the canonical 32-limb absorption order the PUBLISHED rotated commitment binds, in
the Rust `compute_rotated_pre_limbs` order: `cells_root · r0..r23 · cap_root · nullifier_root ·
heap_root · lifecycle · epoch · committed_height`. The authority residue `authorityDigest` rides
register r23 — list index 24 — exactly where the Rust producer writes
`pre_limbs[24] = compute_authority_digest_felt(cell)`. `capRoot` is at index 25. -/

/-- **`rotatedLimbs`** — the ORDERED 31-limb pre-iroot list the PUBLISHED rotated commitment
absorbs. `cellsRoot` at index 0; `r0..r22` the welded/app registers (`r0=balLo`, `r1=nonce`,
`r2=balHi`, `r3..r10 = fields[0..8]`, `r11..r22` app headroom); **`authorityDigest`** at index 24
(register r23 — the SINGLE authority-residue felt); `capRoot` at index 25; then `nullifierRoot`,
`heapRoot`, `lifecycle`, `epoch`, `committedHeight`. The Lean model of
`dregg_cell::commitment::compute_rotated_pre_limbs`. -/
def rotatedLimbs
    (cellsRoot r0 r1 r2 : ℤ) (fields : Fin 8 → ℤ)
    (r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 : ℤ)
    (authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
      committedHeight lifecycleDisc : ℤ) : List ℤ :=
  [ cellsRoot, r0, r1, r2, fields 0, fields 1, fields 2, fields 3, fields 4, fields 5, fields 6,
    fields 7, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22,
    authorityDigest, capRoot, nullifierRoot, commitmentsRoot, heapRoot, lifecycle, epoch,
    committedHeight, lifecycleDisc ]

/-- The rotated limb list has exactly 33 entries (cells_root + 24 registers + cap_root + nullifier
+ commitments + heap + 3 scalars + lifecycle_disc). The length the chained `wireCommitR` consumes
after the lifecycle-disc flag-day widening NUM_PRE_LIMBS 32→33. -/
theorem rotatedLimbs_length
    (cellsRoot r0 r1 r2 : ℤ) (fields : Fin 8 → ℤ)
    (r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 : ℤ)
    (authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
      committedHeight lifecycleDisc : ℤ) :
    (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
      authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
      committedHeight lifecycleDisc).length = 33 :=
  rfl

/-- **`authority_digest_at_index_24`** — the named-correspondence pin: the authority residue limb is
at list index 24 (register r23), exactly where the Rust `compute_rotated_pre_limbs` writes
`pre_limbs[24] = compute_authority_digest_felt(cell)`. -/
theorem authority_digest_at_index_24
    (cellsRoot r0 r1 r2 : ℤ) (fields : Fin 8 → ℤ)
    (r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 : ℤ)
    (authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
      committedHeight lifecycleDisc : ℤ) :
    (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
      authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
      committedHeight lifecycleDisc)[24]?
      = some authorityDigest := rfl

/-- **`cap_root_at_index_25`** — the cap-root limb is at index 25, right after the authority digest
(matching `pre_limbs[25] = compute_canonical_capability_root_felt(&cell.capabilities)`). -/
theorem cap_root_at_index_25
    (cellsRoot r0 r1 r2 : ℤ) (fields : Fin 8 → ℤ)
    (r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 : ℤ)
    (authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
      committedHeight lifecycleDisc : ℤ) :
    (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
      authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
      committedHeight lifecycleDisc)[25]?
      = some capRoot := rfl

/-- **`commitments_root_at_index_27`** — the note-commitments-set root limb is at index 27 (right
after `nullifierRoot` at 26), matching the flag-day `pre_limbs[27] = commitments_root` the producer
fills. The committed home of the `commitments : List Nat` shielded set the noteCreate grow-gate
forces (`RotatedKernelRefinementNotes.commitmentsRoot`). -/
theorem commitments_root_at_index_27
    (cellsRoot r0 r1 r2 : ℤ) (fields : Fin 8 → ℤ)
    (r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 : ℤ)
    (authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
      committedHeight lifecycleDisc : ℤ) :
    (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
      authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
      committedHeight lifecycleDisc)[27]?
      = some commitmentsRoot := rfl

/-! ## §2 — the FAITHFUL Lean model of the PUBLISHED rotated commitment.

`rotatedCommit hash limbs iroot = wireCommitR hash limbs iroot`. `wireCommitR`
(`EffectVmEmitRotationR`) is the proven spec of the deployed chained absorption — the 4-wide head,
the 3-wide chip body, the iroot ALONE last — which is byte-identically the Rust `v9_wire_commit`
/ `rotation_witness::wire_commit` the producer publishes as `OLD_COMMIT`/`NEW_COMMIT`. -/

/-- **`rotatedCommit hash limbs iroot`** — the published rotated commitment: the chained
`wireCommitR` over the pre-iroot limb list and the receipt-MMR `iroot` (absorbed last). The Lean
model of `compute_canonical_state_commitment_v9_felt` / the producer `wire_commit`. -/
def rotatedCommit (hash : List ℤ → ℤ) (limbs : List ℤ) (iroot : ℤ) : ℤ :=
  wireCommitR hash limbs iroot

/-! ## §3 — INJECTIVITY: the PUBLISHED rotated commitment binds the authority residue (and every limb).

Off the ONE realizable `Poseidon2SpongeCR hash` carrier (via the already-proven
`wireCommitR_binds`), equal published rotated commitments force equal pre-iroot limb lists — so
EVERY limb is bound, crucially `authorityDigest`. Tampering the authority residue MOVES the
published `OLD_COMMIT`/`NEW_COMMIT` (audit P0-2 closed on the ACTUALLY-PUBLISHED commitment). -/

/-- **`rotatedCommit_binds_limbs` — the full pre-iroot-limb binding.** Equal published rotated
commitments (over equal-length limb lists) force EQUAL limb lists AND equal iroots, off
`Poseidon2SpongeCR hash` alone. This IS `wireCommitR_binds`, re-exposed at the `rotatedCommit`
surface. -/
theorem rotatedCommit_binds_limbs (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {l l' : List ℤ} {iroot iroot' : ℤ} (hlen : l.length = l'.length)
    (h : rotatedCommit hash l iroot = rotatedCommit hash l' iroot') :
    l = l' ∧ iroot = iroot' :=
  wireCommitR_binds hash hCR hlen h

/-- **`rotatedCommit_binds_authority_digest` — THE audit-P0-2 anti-ghost tooth on the PUBLISHED
commitment.** Two rotated commitments over limb lists agreeing on every NAMED limb EXCEPT the
authority residue (and the SAME iroot) force EQUAL `authorityDigest`. So two cells differing ONLY in
their authority residue (permissions / VK / lifecycle / delegate / delegation / program / mode /
visibility / side-table roots / fields[8..16] — all of which live ONLY in `authorityDigest` =
register r23) PUBLISH a DIFFERENT `OLD_COMMIT`/`NEW_COMMIT`. The rotated twin of
`CommitDifferential.effectVmCommit_binds_record_digest`, on the commitment the light client pins. -/
theorem rotatedCommit_binds_authority_digest (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (cellsRoot r0 r1 r2 : ℤ) (fields : Fin 8 → ℤ)
    (r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 : ℤ)
    (authorityDigest authorityDigest' capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
      committedHeight lifecycleDisc iroot : ℤ)
    (h : rotatedCommit hash
          (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
            authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
            committedHeight lifecycleDisc) iroot
       = rotatedCommit hash
          (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
            authorityDigest' capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
            committedHeight lifecycleDisc) iroot) :
    authorityDigest = authorityDigest' := by
  have hlen :
      (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
        authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
        committedHeight lifecycleDisc).length
      = (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
        authorityDigest' capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
        committedHeight lifecycleDisc).length := by
    rw [rotatedLimbs_length, rotatedLimbs_length]
  obtain ⟨hlist, _⟩ := rotatedCommit_binds_limbs hash hCR hlen h
  -- the two limb lists are equal; read off the index-24 entry (the authority digest).
  have hidx := congrArg (fun L => L[24]?) hlist
  simp only [authority_digest_at_index_24, Option.some.injEq] at hidx
  exact hidx

/-- **`rotatedCommit_binds_cap_root` (corollary).** Equal published rotated commitments over limb
lists agreeing everywhere except the cap-root limb force EQUAL `capRoot` — the published-commitment
twin of cap-Phase-A's "the openable c-list root is bound" (`effectVmCommit_binds_cap_root`). -/
theorem rotatedCommit_binds_cap_root (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (cellsRoot r0 r1 r2 : ℤ) (fields : Fin 8 → ℤ)
    (r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 : ℤ)
    (authorityDigest capRoot capRoot' nullifierRoot commitmentsRoot heapRoot lifecycle epoch
      committedHeight lifecycleDisc iroot : ℤ)
    (h : rotatedCommit hash
          (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
            authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
            committedHeight lifecycleDisc) iroot
       = rotatedCommit hash
          (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
            authorityDigest capRoot' nullifierRoot commitmentsRoot heapRoot lifecycle epoch
            committedHeight lifecycleDisc) iroot) :
    capRoot = capRoot' := by
  have hlen :
      (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
        authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
        committedHeight lifecycleDisc).length
      = (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
        authorityDigest capRoot' nullifierRoot commitmentsRoot heapRoot lifecycle epoch
        committedHeight lifecycleDisc).length := by
    rw [rotatedLimbs_length, rotatedLimbs_length]
  obtain ⟨hlist, _⟩ := rotatedCommit_binds_limbs hash hCR hlen h
  have hidx := congrArg (fun L => L[25]?) hlist
  simp only [cap_root_at_index_25, Option.some.injEq] at hidx
  exact hidx

/-! ## §4 — THE SHAPE CORRESPONDENCE: the rotated and per-cell commitments bind the SAME authority residue.

The per-cell `CommitDifferential.effectVmCommit` binds its authority residue (`record_digest`) at
its FIXED index 12; the rotated `rotatedCommit` binds its authority residue (`authorityDigest` =
register r23) at its FIXED index 24. Both are the SINGLE authority-residue limb the commitment
folds, both bound off one collision-resistance carrier. In the deployed code the two residue felts
are LITERALLY the same value — both are `dregg_cell::commitment::compute_authority_digest_felt(cell)`
(the per-cell `record_digest` and the rotated `pre_limbs[24]`), so the per-cell and the published
rotated commitment bind the SAME bytes. The theorem below states the correspondence as one
conjunction. -/

/-- **`rotated_and_perCell_both_bind_authority_residue`** — the unified P0-2 closure: a change to the
SHARED authority residue felt `d ≠ d'` (the value the deployed code computes ONCE as
`compute_authority_digest_felt` and feeds to BOTH the per-cell `record_digest` and the rotated
`pre_limbs[24]`) MOVES the per-cell commitment AND the published rotated commitment. Both are
contrapositives of the respective binding theorems off their respective CR carriers; stated together
so "the published proof binds the full kernel exactly as the per-cell commitment does" is one
checked fact. -/
theorem rotated_and_perCell_both_bind_authority_residue
    -- per-cell side
    (h4 : ℤ → ℤ → ℤ → ℤ → ℤ)
    (hCR4 : Dregg2.Circuit.CommitDifferential.compress4Injective h4)
    (balLo balHi nonce : ℤ) (pcFields : Fin 8 → ℤ) (pcCapRoot : ℤ)
    -- rotated side
    (hash : List ℤ → ℤ) (hCRN : Poseidon2SpongeCR hash)
    (cellsRoot r0 r1 r2 : ℤ) (rFields : Fin 8 → ℤ)
    (r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 : ℤ)
    (capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch committedHeight lifecycleDisc iroot : ℤ)
    -- the SHARED authority residue felt and a tampered one
    (d d' : ℤ) (hd : d ≠ d') :
    -- per-cell commitment moves
    Dregg2.Circuit.CommitDifferential.effectVmCommit h4 balLo balHi nonce pcFields pcCapRoot d
      ≠ Dregg2.Circuit.CommitDifferential.effectVmCommit h4 balLo balHi nonce pcFields pcCapRoot d'
    -- AND the published rotated commitment moves
    ∧ rotatedCommit hash
        (rotatedLimbs cellsRoot r0 r1 r2 rFields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
          d capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch committedHeight lifecycleDisc) iroot
      ≠ rotatedCommit hash
        (rotatedLimbs cellsRoot r0 r1 r2 rFields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
          d' capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch committedHeight lifecycleDisc) iroot := by
  refine ⟨fun hpc => hd ?_, fun hrot => hd ?_⟩
  · exact Dregg2.Circuit.CommitDifferential.effectVmCommit_binds_record_digest h4 hCR4
      balLo balHi nonce pcFields pcCapRoot d d' hpc
  · exact rotatedCommit_binds_authority_digest hash hCRN cellsRoot r0 r1 r2 rFields
      r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 d d' capRoot nullifierRoot commitmentsRoot
      heapRoot lifecycle epoch committedHeight lifecycleDisc iroot hrot

/-- **`rotatedCommit_binds_commitments_root` (corollary).** Equal published rotated commitments over
limb lists agreeing everywhere except the `commitments_root` limb (index 27) force EQUAL
`commitmentsRoot` — the published-commitment twin of the noteCreate grow-gate's "the committed
shielded-set root is bound" (`RotatedKernelRefinementNotes.noteListRoot_binds`). So a forged note
commitments-set (a dropped/reordered/wrong commitment insert) MOVES the published commitment. -/
theorem rotatedCommit_binds_commitments_root (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (cellsRoot r0 r1 r2 : ℤ) (fields : Fin 8 → ℤ)
    (r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 : ℤ)
    (authorityDigest capRoot nullifierRoot commitmentsRoot commitmentsRoot' heapRoot lifecycle epoch
      committedHeight lifecycleDisc iroot : ℤ)
    (h : rotatedCommit hash
          (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
            authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
            committedHeight lifecycleDisc) iroot
       = rotatedCommit hash
          (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
            authorityDigest capRoot nullifierRoot commitmentsRoot' heapRoot lifecycle epoch
            committedHeight lifecycleDisc) iroot) :
    commitmentsRoot = commitmentsRoot' := by
  have hlen :
      (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
        authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
        committedHeight lifecycleDisc).length
      = (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
        authorityDigest capRoot nullifierRoot commitmentsRoot' heapRoot lifecycle epoch
        committedHeight lifecycleDisc).length := by
    rw [rotatedLimbs_length, rotatedLimbs_length]
  obtain ⟨hlist, _⟩ := rotatedCommit_binds_limbs hash hCR hlen h
  have hidx := congrArg (fun L => L[27]?) hlist
  simp only [commitments_root_at_index_27, Option.some.injEq] at hidx
  exact hidx

#assert_axioms rotatedLimbs_length
#assert_axioms authority_digest_at_index_24
#assert_axioms cap_root_at_index_25
#assert_axioms commitments_root_at_index_27
#assert_axioms rotatedCommit_binds_limbs
#assert_axioms rotatedCommit_binds_authority_digest
#assert_axioms rotatedCommit_binds_cap_root
#assert_axioms rotatedCommit_binds_commitments_root
#assert_axioms rotated_and_perCell_both_bind_authority_residue

/-! ## §5 — VACUITY GUARD: the authority-digest limb (index 24) is LOAD-BEARING on the published commit.

Concrete `#guard`s over the injective Horner toy sponge `refSponge` (the SAME toy
`EffectVmEmitRotationR`'s non-vacuity guards run on — `acc * 1000003 + x`, position-preserving, NOT
a lossy `+`-fold). A cell whose ONLY change is its authority residue (limb 24) PUBLISHES a different
rotated commitment; the cap-root limb (25) is likewise load-bearing; the iroot is bound; the honest
recompute is stable. This is the P0-2 non-vacuity on the ACTUALLY-PUBLISHED commitment, in Lean. -/

private def fieldsC : Fin 8 → ℤ := fun i => 10 + (i : ℤ)

/-- A concrete rotated limb list with a residue felt `d` at index 24 and cap-root `999` at 25; the
app registers `r11..r22` are distinct sentinels so the toy sponge keeps positions. -/
private def demoLimbs (d : ℤ) : List ℤ :=
  rotatedLimbs 1 2 3 4 fieldsC 50 51 52 53 54 55 56 57 58 59 60 61 d 999 70 700 71 72 73 74 75

-- The residue felt genuinely lands at index 24, cap-root at 25, commitments-root at 27, disc at 32.
#guard (demoLimbs 42)[24]? == some (42 : ℤ)
#guard (demoLimbs 42)[25]? == some (999 : ℤ)
#guard (demoLimbs 42)[27]? == some (700 : ℤ)
#guard (demoLimbs 42)[32]? == some (75 : ℤ)
#guard (demoLimbs 42).length == 33

-- LOAD-BEARING: a cell differing ONLY in its authority residue PUBLISHES a different rotated commit
-- (a `record_digest := 0`-style stub would make these EQUAL — the audit-P0-2 forgery, forbidden).
#guard decide (rotatedCommit refSponge (demoLimbs 42) 7
             = rotatedCommit refSponge (demoLimbs 43) 7) == false

-- ANTI-GHOST: two residues distinct ⇒ distinct published rotated commitments.
#guard decide (rotatedCommit refSponge (demoLimbs 11) 7
             = rotatedCommit refSponge (demoLimbs 22) 7) == false

-- HONEST RECOMPUTE: the same cell publishes the same rotated commitment (stable).
#guard decide (rotatedCommit refSponge (demoLimbs 42) 7
             = rotatedCommit refSponge (demoLimbs 42) 7)

-- The cap-root limb (25) is load-bearing too: moving ONLY cap_root moves the published commit.
#guard decide (rotatedCommit refSponge
                 (rotatedLimbs 1 2 3 4 fieldsC 50 51 52 53 54 55 56 57 58 59 60 61 42 999 70 700 71 72 73 74 75) 7
             = rotatedCommit refSponge
                 (rotatedLimbs 1 2 3 4 fieldsC 50 51 52 53 54 55 56 57 58 59 60 61 42 888 70 700 71 72 73 74 75) 7)
            == false

-- The commitments-root limb (27) is load-bearing: moving ONLY commitments_root moves the published
-- commit (the note shielded-set growth is bound — the flag-day's reason for the new limb).
#guard decide (rotatedCommit refSponge
                 (rotatedLimbs 1 2 3 4 fieldsC 50 51 52 53 54 55 56 57 58 59 60 61 42 999 70 700 71 72 73 74 75) 7
             = rotatedCommit refSponge
                 (rotatedLimbs 1 2 3 4 fieldsC 50 51 52 53 54 55 56 57 58 59 60 61 42 999 70 701 71 72 73 74 75) 7)
            == false

-- The lifecycle-disc limb (32) is load-bearing: moving ONLY the disc moves the published commit (a
-- frozen seal / resurrection would publish a DIFFERENT commitment — the disc flag-day's reason).
#guard decide (rotatedCommit refSponge
                 (rotatedLimbs 1 2 3 4 fieldsC 50 51 52 53 54 55 56 57 58 59 60 61 42 999 70 700 71 72 73 74 0) 7
             = rotatedCommit refSponge
                 (rotatedLimbs 1 2 3 4 fieldsC 50 51 52 53 54 55 56 57 58 59 60 61 42 999 70 700 71 72 73 74 1) 7)
            == false

-- The iroot is bound: moving ONLY the iroot moves the published commit (whole-log non-omission).
#guard decide (rotatedCommit refSponge (demoLimbs 42) 7
             = rotatedCommit refSponge (demoLimbs 42) 8) == false

end Dregg2.Circuit.RotatedCommitDifferential
