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

  * ⚑ THE BINDING FAMILY IS NO LONGER HERE (2026-08-01). `rotatedCommit_binds_authority_digest` (the
    audit-P0-2 anti-ghost tooth), `rotatedCommit_binds_limbs`, `rotatedCommit_binds_cap_root`,
    `rotatedCommit_binds_commitments_root` and the unified closure
    `rotated_and_perCell_both_bind_authority_residue` all bought their conclusions with
    `Poseidon2SpongeCR hash` — REFUTED at deployed BabyBear width by
    `Circuit.HashFloorHonesty.poseidon2SpongeCR_false_babyBear` — so at deployment they said nothing.
    All five are DELETED in favour of floor-free successors that state the same anti-ghost content
    with NO hypothesis on `hash` (a forgery moves the published commitment, OR the prover exhibits a
    genuine sponge collision at named arguments): the four `*_or_collides` teeth in
    `Circuit.RotatedCommitBindsOrCollides`, and
    `Circuit.RotatedPerCellBindsOrCollides.rotated_and_perCell_both_bind_authority_residue_or_collides`
    for the shape correspondence. See §3 below. Both successors import THIS module for the model.

  * the VACUITY GUARD: concrete computable `#guard`s over the injective Horner toy sponge
    (`Dregg2.Substrate.Heap.refSponge`) — the authority-digest limb (24) is load-bearing (a cell
    whose ONLY change is its authority residue PUBLISHES a different rotated commitment), the
    cap-root limb (25) is load-bearing, the iroot is bound, and the honest recompute is stable.

Pure, computable, `#guard`-able (no `native_decide`). This module now carries NO refuted floor in any
type — it is the faithful MODEL (limb layout, index pins, non-vacuity guards) and nothing else.
The Rust-side empirical twin is `circuit/tests/effect_vm_rotation_flip.rs`
(`rotated_published_commit_moves_on_permission_flip`): the REAL
`compute_canonical_state_commitment_v9_felt` over the SAME limb order, and a permission flip MOVES
the published rotated commitment (the P0-2 non-vacuity on the ACTUALLY-PUBLISHED commitment).
-/
import Dregg2.Circuit.Emit.EffectVmEmitRotationR
import Dregg2.Circuit.CommitDifferential

namespace Dregg2.Circuit.RotatedCommitDifferential

-- `wireCommitR_binds` and `Poseidon2Binding.Poseidon2SpongeCR` are DELIBERATELY NOT opened: the
-- five declarations that consumed that refuted floor are gone (§3), and this module now carries no
-- floor in any type. The floor-free successors open `wireCommitR_binds_or_collides` instead.
open Dregg2.Circuit.Emit.EffectVmEmitRotationR (wireCommitR)
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
      committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot : ℤ) : List ℤ :=
  [ cellsRoot, r0, r1, r2, fields 0, fields 1, fields 2, fields 3, fields 4, fields 5, fields 6,
    fields 7, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22,
    authorityDigest, capRoot, nullifierRoot, commitmentsRoot, heapRoot, lifecycle, epoch,
    committedHeight, lifecycleDisc, permsDigest, vkDigest, mode, fieldsRoot ]

/-- The rotated limb list has exactly 37 entries (cells_root + 24 registers + cap_root + nullifier
+ commitments + heap + 3 scalars + lifecycle_disc + perms_digest + vk_digest + mode + fields_root). The length the chained
`wireCommitR` consumes after the WAVE-3 mode/fields-root flag-day widening NUM_PRE_LIMBS 35→37. -/
theorem rotatedLimbs_length
    (cellsRoot r0 r1 r2 : ℤ) (fields : Fin 8 → ℤ)
    (r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 : ℤ)
    (authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
      committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot : ℤ) :
    (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
      authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
      committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot).length = 37 :=
  rfl

/-- **`authority_digest_at_index_24`** — the named-correspondence pin: the authority residue limb is
at list index 24 (register r23), exactly where the Rust `compute_rotated_pre_limbs` writes
`pre_limbs[24] = compute_authority_digest_felt(cell)`. -/
theorem authority_digest_at_index_24
    (cellsRoot r0 r1 r2 : ℤ) (fields : Fin 8 → ℤ)
    (r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 : ℤ)
    (authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
      committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot : ℤ) :
    (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
      authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
      committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot)[24]?
      = some authorityDigest := rfl

/-- **`cap_root_at_index_25`** — the cap-root limb is at index 25, right after the authority digest
(matching `pre_limbs[25] = compute_canonical_capability_root_felt(&cell.capabilities)`). -/
theorem cap_root_at_index_25
    (cellsRoot r0 r1 r2 : ℤ) (fields : Fin 8 → ℤ)
    (r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 : ℤ)
    (authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
      committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot : ℤ) :
    (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
      authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
      committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot)[25]?
      = some capRoot := rfl

/-- **`commitments_root_at_index_27`** — the note-commitments-set root limb is at index 27 (right
after `nullifierRoot` at 26), matching the flag-day `pre_limbs[27] = commitments_root` the producer
fills. The committed home of the `commitments : List Nat` shielded set the noteCreate grow-gate
forces (`RotatedKernelRefinementNotes.commitmentsRoot`). -/
theorem commitments_root_at_index_27
    (cellsRoot r0 r1 r2 : ℤ) (fields : Fin 8 → ℤ)
    (r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 : ℤ)
    (authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
      committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot : ℤ) :
    (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
      authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
      committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot)[27]?
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

/-! ## §3 — INJECTIVITY: MOVED, FLOOR-FREE, to `RotatedCommitBindsOrCollides`.

This section used to hold four binding theorems — `rotatedCommit_binds_limbs`,
`rotatedCommit_binds_authority_digest` (the audit-P0-2 anti-ghost tooth), `rotatedCommit_binds_cap_root`,
`rotatedCommit_binds_commitments_root` — plus the unified closure
`rotated_and_perCell_both_bind_authority_residue`. Every one of them bought its conclusion with
`hCR : Poseidon2SpongeCR hash`, which `Circuit.HashFloorHonesty.poseidon2SpongeCR_false_babyBear`
PROVES FALSE at deployed BabyBear width. They were therefore true-but-EMPTY at deployment: they
certified the AIR's arithmetic, not that a permission-flip / VK-swap / dropped-root MOVES the
published `OLD_COMMIT`/`NEW_COMMIT`.

⚑ ALL FIVE ARE DELETED (2026-08-01), not kept beside their successors. The floor-free replacements
prove the SAME anti-ghost content with NO hypothesis on `hash` — a forgery either moves the published
commitment, or the prover hands back a genuine sponge collision at the two limb lists the total
extractor returns:

  * `Circuit.RotatedCommitBindsOrCollides.rotatedCommit_binds_limbs_or_collides`
  * `Circuit.RotatedCommitBindsOrCollides.rotatedCommit_binds_authority_digest_or_collides`
  * `Circuit.RotatedCommitBindsOrCollides.rotatedCommit_binds_cap_root_or_collides`
  * `Circuit.RotatedCommitBindsOrCollides.rotatedCommit_binds_commitments_root_or_collides`
  * `Circuit.RotatedPerCellBindsOrCollides.rotated_and_perCell_both_bind_authority_residue_or_collides`

Those modules import THIS one (they reuse `rotatedCommit`, `rotatedLimbs` and the `[i]?`-index pins
below), which is why the successors live above rather than here. What remains in this file is the
faithful MODEL — the limb layout, the index pins, and the §5 non-vacuity guards — and it now carries
NO refuted floor in any type. -/

#assert_axioms rotatedLimbs_length
#assert_axioms authority_digest_at_index_24
#assert_axioms cap_root_at_index_25
#assert_axioms commitments_root_at_index_27

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
  rotatedLimbs 1 2 3 4 fieldsC 50 51 52 53 54 55 56 57 58 59 60 61 d 999 70 700 71 72 73 74 75 76 77 78 79

-- The residue felt genuinely lands at index 24, cap-root at 25, commitments-root at 27, disc at 32,
-- perms-digest at 33, vk-digest at 34, mode at 35, fields-root at 36.
#guard (demoLimbs 42)[24]? == some (42 : ℤ)
#guard (demoLimbs 42)[25]? == some (999 : ℤ)
#guard (demoLimbs 42)[27]? == some (700 : ℤ)
#guard (demoLimbs 42)[32]? == some (75 : ℤ)
#guard (demoLimbs 42)[33]? == some (76 : ℤ)
#guard (demoLimbs 42)[34]? == some (77 : ℤ)
#guard (demoLimbs 42)[35]? == some (78 : ℤ)
#guard (demoLimbs 42)[36]? == some (79 : ℤ)
#guard (demoLimbs 42).length == 37

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
                 (rotatedLimbs 1 2 3 4 fieldsC 50 51 52 53 54 55 56 57 58 59 60 61 42 999 70 700 71 72 73 74 75 76 77 78 79) 7
             = rotatedCommit refSponge
                 (rotatedLimbs 1 2 3 4 fieldsC 50 51 52 53 54 55 56 57 58 59 60 61 42 888 70 700 71 72 73 74 75 76 77 78 79) 7)
            == false

-- The commitments-root limb (27) is load-bearing: moving ONLY commitments_root moves the published
-- commit (the note shielded-set growth is bound — the flag-day's reason for the new limb).
#guard decide (rotatedCommit refSponge
                 (rotatedLimbs 1 2 3 4 fieldsC 50 51 52 53 54 55 56 57 58 59 60 61 42 999 70 700 71 72 73 74 75 76 77 78 79) 7
             = rotatedCommit refSponge
                 (rotatedLimbs 1 2 3 4 fieldsC 50 51 52 53 54 55 56 57 58 59 60 61 42 999 70 701 71 72 73 74 75 76 77 78 79) 7)
            == false

-- The lifecycle-disc limb (32) is load-bearing: moving ONLY the disc moves the published commit (a
-- frozen seal / resurrection would publish a DIFFERENT commitment — the disc flag-day's reason).
#guard decide (rotatedCommit refSponge
                 (rotatedLimbs 1 2 3 4 fieldsC 50 51 52 53 54 55 56 57 58 59 60 61 42 999 70 700 71 72 73 74 0 76 77 78 79) 7
             = rotatedCommit refSponge
                 (rotatedLimbs 1 2 3 4 fieldsC 50 51 52 53 54 55 56 57 58 59 60 61 42 999 70 700 71 72 73 74 1 76 77 78 79) 7)
            == false

-- The perms-digest limb (33) is load-bearing: moving ONLY the perms-digest moves the published commit
-- (a forged post-permissions would publish a DIFFERENT commitment — the WAVE-2 perms gate's reason).
#guard decide (rotatedCommit refSponge
                 (rotatedLimbs 1 2 3 4 fieldsC 50 51 52 53 54 55 56 57 58 59 60 61 42 999 70 700 71 72 73 74 75 76 77 78 79) 7
             = rotatedCommit refSponge
                 (rotatedLimbs 1 2 3 4 fieldsC 50 51 52 53 54 55 56 57 58 59 60 61 42 999 70 700 71 72 73 74 75 99 77 78 79) 7)
            == false

-- The vk-digest limb (34) is load-bearing: moving ONLY the vk-digest moves the published commit (a
-- forged post-VK would publish a DIFFERENT commitment — the WAVE-2 vk gate's upgrade-safety reason).
#guard decide (rotatedCommit refSponge
                 (rotatedLimbs 1 2 3 4 fieldsC 50 51 52 53 54 55 56 57 58 59 60 61 42 999 70 700 71 72 73 74 75 76 77 78 79) 7
             = rotatedCommit refSponge
                 (rotatedLimbs 1 2 3 4 fieldsC 50 51 52 53 54 55 56 57 58 59 60 61 42 999 70 700 71 72 73 74 75 76 99 78 79) 7)
            == false

-- The mode limb (35) is load-bearing: moving ONLY the mode byte moves the published commit (an
-- un-promoted sovereign would publish a DIFFERENT commitment — the WAVE-3 makeSovereign gate's reason).
#guard decide (rotatedCommit refSponge
                 (rotatedLimbs 1 2 3 4 fieldsC 50 51 52 53 54 55 56 57 58 59 60 61 42 999 70 700 71 72 73 74 75 76 77 0 79) 7
             = rotatedCommit refSponge
                 (rotatedLimbs 1 2 3 4 fieldsC 50 51 52 53 54 55 56 57 58 59 60 61 42 999 70 700 71 72 73 74 75 76 77 1 79) 7)
            == false

-- The fields-root limb (36) is load-bearing: moving ONLY the fields_root digest moves the published
-- commit (a forged post-`fields_root` / refusal audit would publish a DIFFERENT commitment — the
-- WAVE-3 setFieldDyn / refusal weld's reason).
#guard decide (rotatedCommit refSponge
                 (rotatedLimbs 1 2 3 4 fieldsC 50 51 52 53 54 55 56 57 58 59 60 61 42 999 70 700 71 72 73 74 75 76 77 78 79) 7
             = rotatedCommit refSponge
                 (rotatedLimbs 1 2 3 4 fieldsC 50 51 52 53 54 55 56 57 58 59 60 61 42 999 70 700 71 72 73 74 75 76 77 78 99) 7)
            == false

-- The iroot is bound: moving ONLY the iroot moves the published commit (whole-log non-omission).
#guard decide (rotatedCommit refSponge (demoLimbs 42) 7
             = rotatedCommit refSponge (demoLimbs 42) 8) == false

end Dregg2.Circuit.RotatedCommitDifferential
