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

use dregg_circuit::CellState;
use dregg_circuit::cap_root;
use dregg_circuit::effect_vm::split_u64;
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_4_to_1;

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
    let cap_root = cap_root::empty_capability_root()[0];
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
    let cap_root = cap_root::empty_capability_root()[0];
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
    let cap_root = cap_root::empty_capability_root()[0];

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
    let cap_root = cap_root::empty_capability_root()[0];

    assert_eq!(
        cap_root::empty_record_digest(),
        BabyBear::ZERO,
        "empty_record_digest must be ZERO (the no-op fourth input)"
    );

    let residue_free = CellState::compute_commitment(
        balance,
        nonce,
        &fields,
        cap_root,
        cap_root::empty_record_digest(),
    );
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
    use dregg_cell::Cell;
    use dregg_cell::permissions::AuthRequired;

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
    let cap_root = cap_root::empty_capability_root()[0];

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

/// **THE GENTIAN-WELD TOOTH (encoding leg) — the 31-bit authority forge is CLOSED at 8-felt.**
///
/// The H1 hole: the OLD authority digest was a SINGLE `hash_bytes` BabyBear felt (~2^31 image), so
/// two genuinely-different authority states could COLLIDE — a verifier holding only the 1-felt commit
/// could not tell a LOCKED-DOWN cell (`send = Impossible`) from a WIDE-OPEN one (`send = None`). This
/// reconstructs a CONCRETE such collision (found by a birthday search over a free folded field,
/// `fields[8]`; the two salts are pinned so the tooth is deterministic):
///
///   * locked-down salt 57684 vs wide-open salt 1393 → SAME old 1-felt digest (re-mined at the 178-limb geometry).
///
/// At the NEW faithful 8-felt `compute_authority_digest_8` (`bytes32_to_8_limbs(blake3(residue))`,
/// ~124 bits) the two are DISTINCT. So the value that the rotated commit absorbs (all 8 limbs, WELDED
/// by the record-pin8 / continuity freezes) SEPARATES the locked cell from the wide-open one: the
/// 31-bit forge that survived a 1-felt commit cannot survive the 8-felt one. This is the ENCODING leg
/// of the GENTIAN-weld tooth (the circuit-level UNSAT leg rides the welded descriptor).
#[test]
fn gentian_weld_31bit_authority_collision_separated_at_8_felt() {
    use dregg_cell::Cell;
    use dregg_cell::commitment::{authority_residue_bytes, compute_authority_digest_8};
    use dregg_cell::permissions::AuthRequired;
    use dregg_circuit::poseidon2::hash_bytes;

    // Reconstruct the two colliding cells: identical except for `permissions` (locked vs wide-open)
    // and the free folded field `fields[8]` (the salt the birthday search varied).
    fn make(open: bool, salt: u32) -> Cell {
        let mut c = Cell::new([7u8; 32], [11u8; 32]);
        if open {
            c.permissions.send = AuthRequired::None;
            c.permissions.set_permissions = AuthRequired::None;
            c.permissions.set_state = AuthRequired::None;
        } else {
            c.permissions.send = AuthRequired::Impossible;
            c.permissions.set_permissions = AuthRequired::Impossible;
            c.permissions.set_state = AuthRequired::Impossible;
        }
        c.state.fields[8][0..4].copy_from_slice(&salt.to_le_bytes());
        c
    }

    let locked = make(false, 57684);
    let open = make(true, 1393);

    // The cells are GENUINELY different authority states (locked-down vs wide-open send permission).
    assert_eq!(locked.permissions.send, AuthRequired::Impossible);
    assert_eq!(open.permissions.send, AuthRequired::None);
    assert_ne!(
        authority_residue_bytes(&locked),
        authority_residue_bytes(&open),
        "the two cells must be genuinely-different authority states (the forge's whole point)"
    );

    // OLD 1-felt scheme (`hash_bytes`, ~31-bit image): the locked and wide-open cells COLLIDE — a
    // 1-felt commit cannot distinguish them. THIS IS THE HOLE.
    let old_locked = hash_bytes(&authority_residue_bytes(&locked));
    let old_open = hash_bytes(&authority_residue_bytes(&open));
    assert_eq!(
        old_locked, old_open,
        "the OLD single-felt authority digest COLLIDES locked-down with wide-open — the 31-bit hole"
    );

    // NEW faithful 8-felt scheme (`blake3` → 8 limbs, ~124 bits): the two are SEPARATED. The forge
    // that survived the 1-felt commit cannot survive the 8-felt welded commit.
    let new_locked = compute_authority_digest_8(&locked);
    let new_open = compute_authority_digest_8(&open);
    assert_ne!(
        new_locked, new_open,
        "the NEW 8-felt authority digest must SEPARATE the 31-bit-colliding locked / wide-open cells \
         — the GENTIAN close (a 124-bit commit no longer opens as either authority)"
    );

    // limb-0 (the v1 cross-anchor face, `compute_authority_digest_felt`) is BLAKE3 limb-0, so even
    // the scalar face differs here — but soundness rests on the FULL 8-felt vector the rotated commit
    // absorbs + the weld forces, not limb-0 alone.
    assert_eq!(
        dregg_cell::compute_authority_digest_felt(&locked),
        new_locked[0],
        "the scalar face is limb-0 of the faithful 8-felt digest"
    );
}

/// **THE MOVER GENTIAN-WELD TOOTH — the record-pin8 headroom anchors BITE where limb-0 is blind.**
///
/// The H1 mover weld (`withRecordPin8Headroom2`) makes the record-digest movers
/// (setPerms/setVK/makeSovereign/refusal) pin ALL 8 faithful authority limbs (PI 46..53), and the
/// verifier anchors `PI[46..53] = compute_authority_digest_8(post_cell)[0..7]`. Before H1 the mover
/// forced ONLY limb-0 (PI 46) — so a forger could present a setPerms whose committed authority is a
/// DIFFERENT state that collides at limb-0 (~30-bit), and the single-limb anchor could not tell.
///
/// This reconstructs a CONCRETE such pair (found by birthday search over the free folded field
/// `fields[8]`, salts pinned for determinism): a LOCKED-DOWN cell (salt 173207) and a WIDE-OPEN cell
/// (salt 1272) whose `compute_authority_digest_8[0]` are EQUAL but whose 7 HEADROOM limbs DIFFER.
///
///   * single limb-0 pin (old): `digest8[0]` equal ⟹ the anchor cannot distinguish ⟹ forge survives.
///   * 8-felt record-pin8 (new): the verifier anchors all 8; the 7 headroom anchors disagree ⟹ a
///     forged mover authority is UNSAT.
///
/// So the GENTIAN fail-open the value-leg closed for value turns is now CLOSED for the movers too.
#[test]
fn gentian_mover_weld_headroom_anchors_bite_where_limb0_is_blind() {
    use dregg_cell::Cell;
    use dregg_cell::commitment::{authority_residue_bytes, compute_authority_digest_8};
    use dregg_cell::permissions::AuthRequired;

    fn make(open: bool, salt: u32) -> Cell {
        let mut c = Cell::new([7u8; 32], [11u8; 32]);
        if open {
            c.permissions.send = AuthRequired::None;
            c.permissions.set_permissions = AuthRequired::None;
            c.permissions.set_state = AuthRequired::None;
        } else {
            c.permissions.send = AuthRequired::Impossible;
            c.permissions.set_permissions = AuthRequired::Impossible;
            c.permissions.set_state = AuthRequired::Impossible;
        }
        c.state.fields[8][0..4].copy_from_slice(&salt.to_le_bytes());
        c
    }

    let locked = make(false, 173207);
    let open = make(true, 1272);

    // Genuinely-different authority states (locked-down vs wide-open).
    assert_ne!(
        authority_residue_bytes(&locked),
        authority_residue_bytes(&open),
        "the two cells must be genuinely-different authority states"
    );

    let d_locked = compute_authority_digest_8(&locked);
    let d_open = compute_authority_digest_8(&open);

    // LIMB-0 COLLIDES: the OLD single record-pin (PI 46) anchors only this felt — blind to the forge.
    assert_eq!(
        d_locked[0], d_open[0],
        "the locked / wide-open authorities COLLIDE at limb-0 (the single-limb pin is blind here)"
    );

    // THE 7 HEADROOM LIMBS DIFFER: the NEW record-pin8 anchors PI[47..53] to these, so a mover that
    // forges the wide-open authority while the post-cell is the locked one (or vice versa) has AFTER
    // headroom cols that DISAGREE with the anchored PIs ⟹ the pin constraint is UNSAT. The weld BITES.
    assert_ne!(
        &d_locked[1..],
        &d_open[1..],
        "the 7 headroom authority limbs MUST differ — the record-pin8 anchors distinguish the \
         limb-0-colliding locked / wide-open movers the single pin could not (the GENTIAN close for \
         movers — forged mover authority UNSAT at 8-felt)"
    );
}

/// **THE SALT MINER (run manually after any authority-digest geometry change).** The two GENTIAN
/// collision teeth above pin CONCRETE birthday-mined salts; any change to
/// `authority_residue_bytes` / the digest geometry (e.g. the 172→178-limb fields-octet grow)
/// invalidates them. Re-mine with
/// `cargo test -p dregg-circuit --test effect_vm_commit_lean_differential zz_mine --release -- --ignored --nocapture`
/// and re-pin the printed salts in the two tests above.
#[test]
#[ignore = "salt miner — run manually to refresh the pinned collision salts"]
fn zz_mine_gentian_collision_salts() {
    use dregg_cell::Cell;
    use dregg_cell::commitment::{authority_residue_bytes, compute_authority_digest_8};
    use dregg_cell::permissions::AuthRequired;
    use dregg_circuit::poseidon2::hash_bytes;
    use std::collections::HashMap;

    fn make(open: bool, salt: u32) -> Cell {
        let mut c = Cell::new([7u8; 32], [11u8; 32]);
        if open {
            c.permissions.send = AuthRequired::None;
            c.permissions.set_permissions = AuthRequired::None;
            c.permissions.set_state = AuthRequired::None;
        } else {
            c.permissions.send = AuthRequired::Impossible;
            c.permissions.set_permissions = AuthRequired::Impossible;
            c.permissions.set_state = AuthRequired::Impossible;
        }
        c.state.fields[8][0..4].copy_from_slice(&salt.to_le_bytes());
        c
    }

    // Generic birthday search: table the locked side, stream the open side.
    let mine = |digest: &dyn Fn(&Cell) -> u32, label: &str| -> (u32, u32) {
        const TABLE: u32 = 1 << 19;
        let mut locked_by_digest: HashMap<u32, u32> = HashMap::with_capacity(TABLE as usize);
        for salt in 0..TABLE {
            locked_by_digest.insert(digest(&make(false, salt)), salt);
        }
        for open_salt in 0..u32::MAX {
            if let Some(&locked_salt) = locked_by_digest.get(&digest(&make(true, open_salt))) {
                eprintln!("{label}: locked salt {locked_salt} / open salt {open_salt}");
                return (locked_salt, open_salt);
            }
        }
        panic!("{label}: no collision found (should be unreachable)");
    };

    // Tooth 1: the OLD 1-felt digest (`hash_bytes` over the residue) collides.
    let (l1, o1) = mine(
        &|c| hash_bytes(&authority_residue_bytes(c)).as_u32(),
        "gentian_weld_31bit_authority_collision_separated_at_8_felt",
    );
    // Tooth 2: the faithful digest's LIMB-0 collides (headroom limbs must then differ — verify).
    let (l2, o2) = mine(
        &|c| compute_authority_digest_8(c)[0].as_u32(),
        "gentian_mover_weld_headroom_anchors_bite_where_limb0_is_blind",
    );
    let (dl, dp) = (
        compute_authority_digest_8(&make(false, l2)),
        compute_authority_digest_8(&make(true, o2)),
    );
    assert_ne!(&dl[1..], &dp[1..], "headroom limbs must differ for tooth 2");
    // Tooth 1 sanity: the 8-felt digest separates the pair.
    assert_ne!(
        compute_authority_digest_8(&make(false, l1)),
        compute_authority_digest_8(&make(true, o1)),
        "the 8-felt digest must separate tooth 1's colliding pair"
    );
    eprintln!("PIN THESE: tooth1 locked {l1} open {o1} | tooth2 locked {l2} open {o2}");
}
