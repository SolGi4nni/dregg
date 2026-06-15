//! # `rotation_witness` — the per-turn ROTATION producers (the deferred long pole).
//!
//! `docs/ROTATION-CUTOVER.md` §5 items 3-5 name three witness columns of the rotated
//! state block that no v1 column carries, and that no producer existed for: `cells_root`
//! (the turn-level boundary view over present cells), `iroot` (the MMR root over the
//! receipt log — whole-history non-omission, Lean `mroot_injective` /
//! `metatheory/Dregg2/Lightclient/MMR.lean`), and the `lifecycle` / `epoch` scalar limbs.
//!
//! The cutover doc is explicit that these were DELIBERATELY UNBUILT: a producer is only
//! validatable against the rotated trace builder that consumes it, and that builder is the
//! flip's act. THIS module is that producer, built TOGETHER with its consumer (the
//! circuit-side rotated trace builder + the cell≡circuit differential in
//! `circuit/tests/effect_vm_rotation_flip.rs`): the producer derives the limbs from the
//! REAL executed turn's `RecordKernelState` (`Ledger` after-state + the receipt-hash log),
//! the differential proves the limbs it derives EQUAL the limbs the circuit trace carries,
//! and the rotated transfer descriptor (`transferVmDescriptor2R24`) proves+verifies over a
//! trace welded to exactly these values.
//!
//! ## The rotated block (R = 24, CONFIRMED — `ROTATION-CUTOVER.md` §2b)
//!
//! The 31 pre-iroot limbs ride in the absorption order the Lean keystone
//! (`EffectVmEmitRotationV3.preLimbsAt`, `EffectVmEmitRotationR.wireCommitR`) pins:
//!
//! ```text
//!   cells_root · r0..r23 · cap_root · nullifier_root · heap_root
//!              · lifecycle · epoch · committed_height · iroot   (LAST)
//! ```
//!
//! The register file welds where the datum already lives in the v1 state block
//! (`EffectVmEmitRotationV3.weldsAt`): `r0 ↔ balance_lo` · `r1 ↔ nonce` · `r2 ↔ balance_hi`
//! · `r3..r10 ↔ fields[0..7]` · `cap_root ↔ cap_root`. The producer fills those welded
//! limbs with the SAME felt encodings the v1 trace uses (`split_u64`, `BabyBear::new`), so
//! the rotated trace's weld gates `colEq` are satisfied by construction; the remaining
//! limbs (`cells_root`, the map roots, `lifecycle`, `epoch`, `committed_height`, `iroot`,
//! and `r11..r23`) are witness-carried and commitment-bound — THIS module produces them.
//!
//! ## Honest boundary notes
//!
//! * The `iroot` MMR is a left-leaning Poseidon2 fold over the per-position receipt
//!   leaves — the Rust twin of the Lean MMR whose root `mroot_injective` makes
//!   tamper/truncate/extend/reorder all move (`MMR.lean:313`). No Rust MMR primitive
//!   existed before this module (`ROTATION-CUTOVER.md` §5 item 4).
//! * `cells_root` is the sorted-Poseidon2 boundary root over the present cells' existence
//!   leaves (`dregg_circuit::heap_root` — the SAME tree the heap domain commits to), the
//!   `boundary_root_derived` analogue at the turn level (`UNIVERSAL-MEMORY.md`).
//! * The per-cell scalar limbs (balance/nonce/fields/cap_root/lifecycle/epoch/height)
//!   read a SINGLE cell's `RecordKernelState` — the rotated per-effect descriptor is a
//!   per-cell shape (the v1 state block is one cell's before/after). The turn-level
//!   `cells_root` and `iroot` are the same for every effect row of the turn.

use dregg_cell::commitment::{
    compute_authority_digest_felt, compute_canonical_capability_root_felt,
};
use dregg_cell::{Cell, Ledger, lifecycle::CellLifecycle};
use dregg_circuit::effect_vm::{fold_bytes32_to_bb, split_u64};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::{compute_heap_root_entries, empty_heap_root};
use dregg_circuit::poseidon2::{hash_bytes, hash_many};

/// The CONFIRMED rotated register count (ember 2026-06-12, `ROTATION-CUTOVER.md` §2b).
pub const NUM_REGISTERS: usize = 24;

/// The number of pre-iroot absorption limbs (cells_root · r0..r23 · cap/nullifier/heap
/// roots · lifecycle · epoch · committed_height). Matches Lean `preLimbsAt_length = 31`
/// at R = 24.
pub const NUM_PRE_LIMBS: usize = 1 + NUM_REGISTERS + 3 + 3; // 1 + 24 + 3 + 3 = 31

/// The collection id under which a present-cell existence leaf is keyed in the cells tree.
const CELLS_COLLECTION: u32 = 0;

/// One turn's rotated state-block witness for a single cell's before/after RecordKernelState.
///
/// `pre_limbs` is the 31-limb absorption vector in the Lean-pinned order; `iroot` is the
/// MMR root absorbed LAST. `state_commit = wireCommitR(pre_limbs, iroot)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RotationWitness {
    /// The 31 pre-iroot limbs, in absorption order.
    pub pre_limbs: Vec<BabyBear>,
    /// The receipt-index MMR root (absorbed last).
    pub iroot: BabyBear,
    /// The chained state commitment `wireCommitR(pre_limbs, iroot)`.
    pub state_commit: BabyBear,
}

/// Felt-encode a cell's signed balance LOW limb — the `r0 ↔ balance_lo` weld value,
/// byte-identical to the v1 trace (`CellState::compute_commitment`'s `split_u64`).
#[inline]
pub fn balance_lo_felt(balance: i64) -> BabyBear {
    split_u64(balance as u64).0
}

/// Felt-encode a cell's signed balance HIGH limb — the `r2 ↔ balance_hi` weld value.
#[inline]
pub fn balance_hi_felt(balance: i64) -> BabyBear {
    split_u64(balance as u64).1
}

/// Felt-encode the nonce — the `r1 ↔ nonce` weld value.
#[inline]
pub fn nonce_felt(nonce: u64) -> BabyBear {
    BabyBear::new((nonce & 0x7FFF_FFFF) as u32)
}

/// The canonical scalar limb of a cell's lifecycle: the discriminant folded with its
/// payload bytes so two distinct lifecycle states (Live / Sealed / Destroyed / …) yield
/// distinct limbs — the in-circuit twin of `cell::commitment::hash_lifecycle_into`'s
/// anti-omission tooth (a malicious executor must not present a Destroyed cell as Live).
pub fn lifecycle_felt(lc: &CellLifecycle) -> BabyBear {
    // The variant discriminant (a distinct base value per state) folded with payload
    // bytes. `CellLifecycle::discriminant` is `pub(crate)` to `dregg-cell`; the producer
    // re-derives the same per-variant ordering locally (the absolute value is opaque — the
    // tooth is only that distinct lifecycle states yield distinct felts).
    let disc: u8 = match lc {
        CellLifecycle::Live => 0,
        CellLifecycle::Sealed { .. } => 1,
        CellLifecycle::Migrated { .. } => 2,
        CellLifecycle::Destroyed { .. } => 3,
        CellLifecycle::Archived { .. } => 4,
    };
    let mut bytes = Vec::with_capacity(40);
    bytes.push(disc);
    match lc {
        CellLifecycle::Live => {}
        CellLifecycle::Sealed {
            reason_hash,
            sealed_at,
        } => {
            bytes.extend_from_slice(reason_hash);
            bytes.extend_from_slice(&sealed_at.to_le_bytes());
        }
        CellLifecycle::Migrated {
            to,
            attestation,
            migrated_at,
        } => {
            bytes.extend_from_slice(to.as_bytes());
            bytes.extend_from_slice(attestation);
            bytes.extend_from_slice(&migrated_at.to_le_bytes());
        }
        CellLifecycle::Destroyed {
            death_certificate_hash,
            destroyed_at,
        } => {
            bytes.extend_from_slice(death_certificate_hash);
            bytes.extend_from_slice(&destroyed_at.to_le_bytes());
        }
        CellLifecycle::Archived {
            checkpoint_hash,
            archived_through,
        } => {
            bytes.extend_from_slice(checkpoint_hash);
            bytes.extend_from_slice(&archived_through.to_le_bytes());
        }
    }
    hash_bytes(&bytes)
}

/// Felt-encode the parent-side delegation epoch — the `epoch` scalar limb.
#[inline]
pub fn epoch_felt(epoch: u64) -> BabyBear {
    BabyBear::new((epoch & 0x7FFF_FFFF) as u32)
}

/// Felt-encode the committed height — the `committed_height` scalar limb (PI-v3, §2.6).
#[inline]
pub fn committed_height_felt(height: u64) -> BabyBear {
    BabyBear::new((height & 0x7FFF_FFFF) as u32)
}

/// Pack a 32-byte root (a BLAKE3 / table-map root carried in cell state) into a single
/// BabyBear limb. The same packing the heap domain uses to lift byte roots into the field
/// (`dregg_circuit::poseidon2::hash_bytes`).
#[inline]
pub fn root_felt(root: &[u8; 32]) -> BabyBear {
    hash_bytes(root)
}

/// **THE `cells_root` PRODUCER** — the turn-level boundary view over the present cells.
///
/// The sorted-Poseidon2 root over one existence leaf per present cell (`value = 1`,
/// keyed by a felt digest of the cell id under `CELLS_COLLECTION`). Input-order
/// independent (the underlying `CanonicalHeapTree` sorts by address — see
/// `heap_root::root_is_input_order_independent`), so the root is a function of the SET of
/// present cells, never the ledger's iteration order. The empty ledger yields the empty
/// sorted-tree sentinel root.
pub fn cells_root(ledger: &Ledger) -> BabyBear {
    let mut entries: Vec<((BabyBear, BabyBear), BabyBear)> = Vec::new();
    for (id, _) in ledger.iter() {
        let key = hash_bytes(id.as_bytes());
        entries.push((
            (BabyBear::new(CELLS_COLLECTION), key),
            BabyBear::ONE, // existence bit
        ));
    }
    if entries.is_empty() {
        return empty_heap_root();
    }
    compute_heap_root_entries(&entries)
}

/// **THE `iroot` PRODUCER** — the MMR root over the receipt log.
///
/// A left-leaning Poseidon2 fold over the per-position receipt leaves: each leaf is the
/// felt digest of `(position, receipt_hash)`, and the running root accumulates
/// `root := hash[root, leaf]` in chronological order. This is the Rust realization of the
/// Lean MMR whose `mroot_injective` (`MMR.lean:313`) makes the root bind the WHOLE log:
/// tampering any leaf, truncating, extending, or reordering all move the fold. The empty
/// log yields the zero root (a uniform no-op for a turn that appends nothing).
pub fn iroot(receipt_hashes: &[[u8; 32]]) -> BabyBear {
    let mut root = BabyBear::ZERO;
    for (position, rh) in receipt_hashes.iter().enumerate() {
        let leaf = hash_many(&[BabyBear::new(position as u32), hash_bytes(rh)]);
        root = hash_many(&[root, leaf]);
    }
    root
}

/// The chained rotated state commitment — the Rust twin of Lean `wireCommitR`
/// (`EffectVmEmitRotationR.lean`): the 4-wide head over the first four limbs, 3-wide chip
/// groups while ≥ 3 pre-iroot limbs remain, the iroot absorbed ALONE last. Byte-identical
/// to the chained absorption the rotated descriptor's hash sites realize
/// (`descriptor_ir2.rs::rotation_probe_trace_r`), so the producer's `state_commit` is the
/// value the rotated trace's `STATE_COMMIT` carrier MUST carry.
pub fn wire_commit(pre_limbs: &[BabyBear], iroot: BabyBear) -> BabyBear {
    assert_eq!(
        pre_limbs.len(),
        NUM_PRE_LIMBS,
        "wire_commit: {NUM_PRE_LIMBS} pre-iroot limbs at R={NUM_REGISTERS}"
    );
    let mut d = hash_many(&[pre_limbs[0], pre_limbs[1], pre_limbs[2], pre_limbs[3]]);
    let mut col = 4;
    while col < NUM_PRE_LIMBS {
        let remaining = NUM_PRE_LIMBS - col;
        if remaining >= 3 {
            d = hash_many(&[d, pre_limbs[col], pre_limbs[col + 1], pre_limbs[col + 2]]);
            col += 3;
        } else {
            d = hash_many(&[d, pre_limbs[col]]);
            col += 1;
        }
    }
    hash_many(&[d, iroot])
}

/// The full witness producer for one cell's before/after state in a real turn.
///
/// `cell` is the per-cell `RecordKernelState` (after-state for the AFTER block; supply the
/// before-cell for the BEFORE block), `ledger` is the after-ledger (for `cells_root`),
/// `nullifier_root` / `heap_root` are the cell's committed map roots, and
/// `receipt_hashes` is the turn's receipt log (for `iroot`). `r11..r23` are witness-free
/// in this turn (no app data) → zero; a real app's hot scalars would fill them.
pub fn produce(
    cell: &Cell,
    ledger: &Ledger,
    nullifier_root: &[u8; 32],
    receipt_hashes: &[[u8; 32]],
) -> RotationWitness {
    let mut pre_limbs = vec![BabyBear::ZERO; NUM_PRE_LIMBS];
    // limb 0: cells_root (turn-level).
    pre_limbs[0] = cells_root(ledger);
    // limbs 1..=24: r0..r23. Welded scalars first (r0,r1,r2,r3..r10), then app registers.
    pre_limbs[1] = balance_lo_felt(cell.state.balance()); // r0
    pre_limbs[2] = nonce_felt(cell.state.nonce()); // r1
    pre_limbs[3] = balance_hi_felt(cell.state.balance()); // r2
    for i in 0..8 {
        // r3..r10 ↔ fields[0..7]: the 32-byte record field packed into the field limb the
        // v1 circuit state block carries (`fold_bytes32_to_bb`, the same Horner packing).
        pre_limbs[4 + i] = fold_bytes32_to_bb(&cell.state.fields[i]);
    }
    // r11..r22 (limbs 12..=23): app-register headroom — zero for this kernel turn.
    // r23 (limb 24): THE AUTHORITY DIGEST — folds ALL authority-bearing cell state that no
    // other rotated limb carries (permissions/VK/delegate/delegation/program/mode/token_id +
    // visibility/commitments/proved/side-table roots + fields[8..16]). Byte-identical to the
    // cell-side `commitment::compute_rotated_pre_limbs` so the three-way agreement holds; the
    // commitment binds it (the Lean welds leave r23 free, the anti-ghost keystone binds it).
    pre_limbs[24] = compute_authority_digest_felt(cell);
    // limb 25: cap_root (welded) — the SAME openable sorted-Poseidon2 felt the circuit's
    // `cap_root` column carries (cell and circuit compute it through the SAME impl, the A2
    // differential guards it), so the `cap_root ↔ cap_root` weld holds by construction.
    pre_limbs[25] = compute_canonical_capability_root_felt(&cell.capabilities);
    // limbs 26,27: nullifier_root, heap_root.
    pre_limbs[26] = root_felt(nullifier_root);
    pre_limbs[27] = root_felt(&cell.state.heap_root);
    // limbs 28,29,30: lifecycle, epoch, committed_height.
    pre_limbs[28] = lifecycle_felt(&cell.lifecycle);
    pre_limbs[29] = epoch_felt(cell.state.delegation_epoch());
    pre_limbs[30] = committed_height_felt(cell.state.committed_height());

    let iroot_val = iroot(receipt_hashes);
    let state_commit = wire_commit(&pre_limbs, iroot_val);
    RotationWitness {
        pre_limbs,
        iroot: iroot_val,
        state_commit,
    }
}

/// **THE ROTATED-LEG MINTING RECIPE (Bucket-F / PATH-PRESERVE Phase 5a).** Build a
/// [`RotatedParticipantLeg`](dregg_circuit::joint_turn_aggregation::RotatedParticipantLeg) for a
/// single homogeneous-cohort turn from the real before/after actor `Cell`s: run [`produce`] over
/// each cell to derive its rotated block witness (`pre_limbs` + `iroot`), then hand those to the
/// pure-circuit
/// [`RotatedParticipantLeg::mint_from_block_witnesses`](dregg_circuit::joint_turn_aggregation::RotatedParticipantLeg::mint_from_block_witnesses),
/// which generates the 311-column rotated trace + 38-PI vector and proves it through the IR-v2
/// batch prover under the leaf-wrap config (so the minted `Ir2BatchProof` folds directly as a
/// `NativeBatchStark` recursion leaf). The proof self-verifies natively before return.
///
/// This lives in `dregg-turn` (NOT `dregg-circuit`) because it drives [`produce`] over
/// `dregg_cell::Cell`s, and `dregg-circuit` cannot depend on `dregg-cell` / `dregg-turn` (a
/// dependency cycle — both depend on `dregg-circuit`). It is the ONE recipe the recursion
/// consumers (lightclient / wasm / `circuit/tests/proof_economics.rs`) use to build a mandatory
/// rotated participant; it mirrors `circuit/tests/rotation_batchstark_leaf_smoke.rs`'s mint
/// sequence exactly.
///
/// `turn_id`, when `Some`, overrides the `TURN_HASH` slot of the carried PI prefix (the joint
/// aggregator's shared-turn-id projection) — pass it for joint-turn participants that must agree
/// on a shared id; pass `None` for whole-chain turns (the carried hash from the witness stands).
///
/// Fails closed if the turn's effect is not a single rotated R=24 cohort member (the generator
/// rejects a non-cohort / empty / heterogeneous slice).
#[cfg(feature = "recursion")]
#[allow(clippy::too_many_arguments)]
pub fn mint_rotated_participant_leg(
    initial_state: &dregg_circuit::effect_vm::CellState,
    effects: &[dregg_circuit::effect_vm::Effect],
    before_cell: &Cell,
    after_cell: &Cell,
    nullifier_root: &[u8; 32],
    receipt_log: &[[u8; 32]],
    turn_id: Option<BabyBear>,
) -> Result<dregg_circuit::joint_turn_aggregation::RotatedParticipantLeg, String> {
    use dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness;
    use dregg_circuit::joint_turn_aggregation::RotatedParticipantLeg;

    // The turn-context ledger snapshot: a single-cell ledger holding the after-cell (the
    // cells_root shape `produce` reads).
    let mut ledger = Ledger::new();
    ledger
        .insert_cell(after_cell.clone())
        .map_err(|e| format!("mint_rotated_participant_leg: ledger seed failed: {e:?}"))?;

    let before_w = produce(before_cell, &ledger, nullifier_root, receipt_log);
    let after_w = produce(after_cell, &ledger, nullifier_root, receipt_log);
    let bridge = |w: &RotationWitness| -> Result<RotatedBlockWitness, String> {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot)
            .map_err(|e| format!("mint_rotated_participant_leg: rotated block witness: {e}"))
    };

    RotatedParticipantLeg::mint_from_block_witnesses(
        initial_state,
        effects,
        &bridge(&before_w)?,
        &bridge(&after_w)?,
        turn_id,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::Cell;

    fn cell(seed: u8, balance: i64) -> Cell {
        let mut pk = [0u8; 32];
        pk[0] = seed;
        Cell::with_balance(pk, [0u8; 32], balance)
    }

    #[test]
    fn pre_limb_count_is_31_at_r24() {
        assert_eq!(NUM_PRE_LIMBS, 31);
    }

    /// THE iroot NON-OMISSION TOOTH (Lean `mroot_injective`): tamper / truncate / extend /
    /// reorder of the receipt log each MOVE the root.
    #[test]
    fn iroot_binds_the_whole_log() {
        let log = vec![[1u8; 32], [2u8; 32], [3u8; 32]];
        let base = iroot(&log);
        // tamper a leaf
        let mut tampered = log.clone();
        tampered[1] = [9u8; 32];
        assert_ne!(base, iroot(&tampered), "tampered leaf must move the root");
        // truncate
        assert_ne!(base, iroot(&log[..2]), "truncation must move the root");
        // extend
        let mut extended = log.clone();
        extended.push([4u8; 32]);
        assert_ne!(base, iroot(&extended), "extension must move the root");
        // reorder
        let reordered = vec![log[1], log[0], log[2]];
        assert_ne!(base, iroot(&reordered), "reorder must move the root");
        // the empty log is the zero root
        assert_eq!(iroot(&[]), BabyBear::ZERO);
    }

    /// `cells_root` is a function of the SET of present cells, not the insertion order.
    #[test]
    fn cells_root_is_set_valued() {
        let (a, b) = (cell(1, 10), cell(2, 20));
        let mut l1 = Ledger::new();
        l1.insert_cell(a.clone()).unwrap();
        l1.insert_cell(b.clone()).unwrap();
        let mut l2 = Ledger::new();
        l2.insert_cell(b).unwrap();
        l2.insert_cell(a).unwrap();
        assert_eq!(
            cells_root(&l1),
            cells_root(&l2),
            "cells_root must be insertion-order independent"
        );
        // a different cell set yields a different root
        let mut l3 = Ledger::new();
        l3.insert_cell(cell(1, 10)).unwrap();
        assert_ne!(cells_root(&l1), cells_root(&l3));
        // the empty ledger is the empty-tree sentinel root
        assert_eq!(cells_root(&Ledger::new()), empty_heap_root());
    }

    /// The chained `wire_commit` binds every pre-iroot limb and the iroot: moving any limb
    /// (here the heap_root limb at offset 27) or the iroot moves the commitment.
    #[test]
    fn wire_commit_binds_limbs_and_iroot() {
        let limbs: Vec<BabyBear> = (0..NUM_PRE_LIMBS)
            .map(|i| BabyBear::new(300 + i as u32))
            .collect();
        let c = wire_commit(&limbs, BabyBear::new(7));
        let mut moved = limbs.clone();
        moved[27] = BabyBear::new(999);
        assert_ne!(
            c,
            wire_commit(&moved, BabyBear::new(7)),
            "heap_root limb is bound"
        );
        assert_ne!(c, wire_commit(&limbs, BabyBear::new(8)), "iroot is bound");
    }

    /// Distinct lifecycle states yield distinct limbs (the anti-omission tooth).
    #[test]
    fn lifecycle_felt_separates_states() {
        let live = lifecycle_felt(&CellLifecycle::Live);
        let destroyed = lifecycle_felt(&CellLifecycle::Destroyed {
            death_certificate_hash: [5u8; 32],
            destroyed_at: 42,
        });
        assert_ne!(live, destroyed, "Live and Destroyed must commit distinctly");
    }
}
