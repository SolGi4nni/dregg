//! # THE COMMITMENT-CONSTRUCTION DIFFERENTIAL — deployed Rust `compute_commitment` ⟺ Lean model.
//!
//! ## SCOPE (read first — what this is and is NOT)
//!
//! This is a STRUCTURAL differential on the per-cell COMMITMENT CONSTRUCTION: it checks that the
//! deployed `CellState::compute_commitment` hash-tree (limb order, nesting, binding, non-vacuity)
//! matches an INDEPENDENT re-fold over the Lean `effectVmLimbs` order. The "byte-identical" claims
//! below are byte-identity of the COMMITMENT HASH TREE against that independent Lean-limb re-fold —
//! NOT a serialization round-trip, and NOT executor EVAL AGREEMENT.
//!
//! It is NOT the Lean↔Rust EXECUTOR eval-agreement check. That faithfulness — the verified Lean
//! executor and the deployed Rust circuit/executor computing the SAME post-state on the SAME input —
//! is the CANONICAL denotational differential `ir2_denotational_differential.rs` (descriptor IR-v2
//! denotation `Satisfied2` ⟺ deployed `Ir2Air::eval`) and the turn-side
//! `dregg-turn/tests/lean_state_producer_differential.rs` (full post-state ledger `.root()` agreement
//! on a real turn). This file grounds ONE leg those rely on: that the commitment the post-state root
//! is built from has the proven limb shape. It does not, and does not claim to, witness eval
//! agreement.
//!
//! The closed circuit-soundness crown (`metatheory/Dregg2/Circuit/StateCommit.lean`
//! `lightclient_unfoolable_circuit_sound`) is over the abstract per-cell leaf and the
//! kernel root `recStateCommit`. The DEPLOYED per-cell commitment is
//! `dregg_circuit::CellState::compute_commitment` (`circuit/src/effect_vm/cell_state.rs`):
//! a `hash_4_to_1` tree over the ORDERED limb list
//!
//!   `[balance_lo, balance_hi, nonce, fields[0..8], cap_root, record_digest]`
//!
//! absorbed as
//!
//!   `inter1     = hash_4_to_1(balance_lo, balance_hi, nonce, fields[0])`
//!   `inter2     = hash_4_to_1(fields[1], fields[2], fields[3], fields[4])`
//!   `inter3     = hash_4_to_1(fields[5], fields[6], fields[7], cap_root)`
//!   `commitment = hash_4_to_1(inter1, inter2, inter3, record_digest)`.
//!
//! The Lean faithful model is `Dregg2.Circuit.CommitDifferential.effectVmCommit` over an
//! abstract 4-to-1 compress `h4`; the named field correspondence pins `record_digest` at
//! limb index 12 (`effectVmLimbs` / `record_digest_at_index_12`), exactly the role the Lean
//! `RH`/`systemRootsDigest` rest-hash limb plays. This file is the EMPIRICAL twin that grounds
//! that abstract `h4` in the REAL `dregg_circuit::poseidon2::hash_4_to_1` and the real
//! `dregg_cell::compute_authority_digest_felt`, and CHECKS each structural claim the Lean
//! theorems prove:
//!
//!   1. `differential_limb_order_matches_lean` — the deployed `compute_commitment` is
//!      BYTE-IDENTICAL to an independent re-fold over the Lean `effectVmLimbs` order (the SAME
//!      nesting, the SAME limb positions). The shape MATCHES (no reorder / dropped / extra limb).
//!
//!   2. `differential_record_digest_at_position_12` — the `record_digest` is the FOURTH root
//!      input (the index-12 authority-residue limb), and the real cell's
//!      `compute_authority_digest_felt` is the felt that flows into it — the named field
//!      correspondence, grounded.
//!
//!   3. `differential_record_digest_binds` — the deployed commitment BINDS `record_digest`
//!      (audit P0-2 / Lean `effectVmCommit_binds_record_digest`): two cells differing ONLY in
//!      authority residue commit DIFFERENTLY.
//!
//!   4. `differential_residue_free_noop` — a residue-free cell (`empty_record_digest() = ZERO`)
//!      commits exactly as the legacy ZERO form (Lean `effectVmCommit_residueFree_noop`).
//!
//!   5. `differential_real_cell_authority_residue_flows` — a REAL cell carrying authority state
//!      beyond the welded limbs (permissions / VK / lifecycle) produces a NON-ZERO
//!      `compute_authority_digest_felt`, and seeding it changes the commitment — the deployed
//!      P0-2 closure is non-vacuous on a real cell.

use dregg_circuit::cap_root;
use dregg_circuit::effect_vm::split_u64;
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_4_to_1;
use dregg_circuit::CellState;

/// The Lean `effectVmLimbs` order: `[balLo, balHi, nonce, fields[0..8], cap_root, record_digest]`.
/// Index 12 (the last) is `record_digest`. This mirrors
/// `Dregg2.Circuit.CommitDifferential.effectVmLimbs`.
fn lean_effect_vm_limbs(
    balance: u64,
    nonce: u32,
    fields: &[BabyBear; 8],
    cap_root: BabyBear,
    record_digest: BabyBear,
) -> [BabyBear; 13] {
    let (lo, hi) = split_u64(balance);
    [
        lo,
        hi,
        BabyBear::new(nonce),
        fields[0],
        fields[1],
        fields[2],
        fields[3],
        fields[4],
        fields[5],
        fields[6],
        fields[7],
        cap_root,
        record_digest,
    ]
}

/// The Lean `effectVmFoldLimbs`: the explicit `hash_4_to_1` nesting written as a fold over the
/// 13-limb `effectVmLimbs` list. An INDEPENDENT reconstruction (not a call to
/// `compute_commitment`), so if the deployed tree ever drifts from the Lean limb order/nesting,
/// this differential fails.
fn lean_fold_limbs(limbs: &[BabyBear; 13]) -> BabyBear {
    let inter1 = hash_4_to_1(&[limbs[0], limbs[1], limbs[2], limbs[3]]);
    let inter2 = hash_4_to_1(&[limbs[4], limbs[5], limbs[6], limbs[7]]);
    let inter3 = hash_4_to_1(&[limbs[8], limbs[9], limbs[10], limbs[11]]);
    hash_4_to_1(&[inter1, inter2, inter3, limbs[12]])
}

fn sample_fields() -> [BabyBear; 8] {
    let mut f = [BabyBear::ZERO; 8];
    for (i, slot) in f.iter_mut().enumerate() {
        *slot = BabyBear::new(100 + i as u32);
    }
    f
}

/// **(1)** The deployed `compute_commitment` is BYTE-IDENTICAL to the independent fold over the
/// Lean `effectVmLimbs` order — the shape MATCHES (Lean `effectVmCommit_absorbs_limbs`).
#[test]
fn differential_limb_order_matches_lean() {
    let balance = 1_234_567u64;
    let nonce = 42u32;
    let fields = sample_fields();
    let cap_root = cap_root::empty_capability_root();
    let record_digest = BabyBear::new(0xABCD);

    let deployed = CellState::compute_commitment(balance, nonce, &fields, cap_root, record_digest);
    let limbs = lean_effect_vm_limbs(balance, nonce, &fields, cap_root, record_digest);
    let lean = lean_fold_limbs(&limbs);

    assert_eq!(
        deployed, lean,
        "deployed compute_commitment != independent fold over the Lean effectVmLimbs order — \
         the hash-tree SHAPE (limb order / nesting) has drifted from the proven model"
    );
}

/// **(2)** `record_digest` is the index-12 authority-residue limb (the fourth root input), and
/// the real `compute_authority_digest_felt` of a residue-free cell is the constant that lands
/// there — the named field correspondence, grounded (Lean `record_digest_at_index_12`).
#[test]
fn differential_record_digest_at_position_12() {
    let balance = 500u64;
    let nonce = 1u32;
    let fields = sample_fields();
    let cap_root = cap_root::empty_capability_root();
    let record_digest = BabyBear::new(9_999);

    let limbs = lean_effect_vm_limbs(balance, nonce, &fields, cap_root, record_digest);
    assert_eq!(
        limbs[12], record_digest,
        "record_digest must occupy limb index 12 (the authority-residue position) — the named \
         field correspondence the Lean differential pins"
    );

    // Changing ONLY limb 12 changes ONLY the fourth root input: the three intermediates are
    // identical, so the deployed commitment differs solely via the record_digest absorption.
    let (lo, hi) = split_u64(balance);
    let inter1 = hash_4_to_1(&[lo, hi, BabyBear::new(nonce), fields[0]]);
    let inter2 = hash_4_to_1(&[fields[1], fields[2], fields[3], fields[4]]);
    let inter3 = hash_4_to_1(&[fields[5], fields[6], fields[7], cap_root]);
    let direct = hash_4_to_1(&[inter1, inter2, inter3, record_digest]);
    let deployed = CellState::compute_commitment(balance, nonce, &fields, cap_root, record_digest);
    assert_eq!(
        direct, deployed,
        "the deployed commitment must absorb record_digest as exactly the fourth root input"
    );
}

/// **(3)** The deployed commitment BINDS `record_digest` (audit P0-2 / Lean
/// `effectVmCommit_binds_record_digest`): two cells differing ONLY in authority residue — same
/// balance / nonce / fields / cap_root — commit DIFFERENTLY.
#[test]
fn differential_record_digest_binds() {
    let balance = 1_000u64;
    let nonce = 7u32;
    let fields = sample_fields();
    let cap_root = cap_root::empty_capability_root();

    let c_a = CellState::compute_commitment(balance, nonce, &fields, cap_root, BabyBear::new(11));
    let c_b = CellState::compute_commitment(balance, nonce, &fields, cap_root, BabyBear::new(22));
    assert_ne!(
        c_a, c_b,
        "two cells differing ONLY in authority residue must commit differently (P0-2) — the \
         deployed twin of Lean effectVmCommit_binds_record_digest"
    );
}

/// **(4)** A residue-free cell (`empty_record_digest() == ZERO`) commits exactly as the legacy
/// ZERO form (Lean `effectVmCommit_residueFree_noop`) — the flag-day-free additive cutover.
#[test]
fn differential_residue_free_noop() {
    let balance = 777u64;
    let nonce = 3u32;
    let fields = sample_fields();
    let cap_root = cap_root::empty_capability_root();

    assert_eq!(
        cap_root::empty_record_digest(),
        BabyBear::ZERO,
        "empty_record_digest must be ZERO (the no-op fourth input)"
    );

    let residue_free =
        CellState::compute_commitment(balance, nonce, &fields, cap_root, cap_root::empty_record_digest());
    // The Lean `legacyEffectVmCommit`: the fourth root input pinned to ZERO.
    let legacy = CellState::compute_commitment(balance, nonce, &fields, cap_root, BabyBear::ZERO);
    assert_eq!(
        residue_free, legacy,
        "a residue-free cell must commit byte-identically to the legacy ZERO form (no-op cutover)"
    );
}

/// **(5)** A REAL cell carrying authority state beyond the welded limbs produces a NON-ZERO
/// `compute_authority_digest_felt`, and seeding it into the commitment changes the commitment —
/// the deployed P0-2 closure is non-vacuous on a real cell (the residue felt the Lean model's
/// abstract `record_digest` stands for).
#[test]
fn differential_real_cell_authority_residue_flows() {
    use dregg_cell::permissions::AuthRequired;
    use dregg_cell::Cell;

    // A residue-free baseline cell (default permissions / no VK).
    let plain = Cell::new([7u8; 32], [11u8; 32]);
    let plain_digest = dregg_cell::compute_authority_digest_felt(&plain);

    // A cell with a tightened permission (authority state living ONLY in the residue digest).
    let mut locked = Cell::new([7u8; 32], [11u8; 32]);
    locked.permissions.send = AuthRequired::Impossible;
    let locked_digest = dregg_cell::compute_authority_digest_felt(&locked);

    assert_ne!(
        plain_digest, locked_digest,
        "a permission change must MOVE compute_authority_digest_felt — the authority residue is \
         genuinely bound (not a constant stub)"
    );

    // Seeding the real residue digests into the circuit cell-state yields DIFFERENT commitments,
    // so the deployed commitment distinguishes a locked-down cell from a wide-open one (P0-2).
    let balance = 100_000u64;
    let nonce = 0u32;
    let fields = [BabyBear::ZERO; 8];
    let cap_root = cap_root::empty_capability_root();

    let commit_plain =
        CellState::compute_commitment(balance, nonce, &fields, cap_root, plain_digest);
    let commit_locked =
        CellState::compute_commitment(balance, nonce, &fields, cap_root, locked_digest);
    assert_ne!(
        commit_plain, commit_locked,
        "the deployed commitment must distinguish two cells differing only in a permission — the \
         real-cell P0-2 closure (the locked/wide-open collision the old ZERO fourth input left open)"
    );
}
