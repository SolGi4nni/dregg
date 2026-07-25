//! Note spending circuit: ZK proof that the spender knows the spending key.
//!
//! # DEPRECATION NOTICE
//!
//! This AIR is **superseded for proof-to-action binding purposes** by the
//! schema-based generalized AIR in `effect_action_air.rs`:
//!   - `SCHEMA_NOTE_SPEND` (full-fidelity binding for `Effect::NoteSpend`)
//!   - `SCHEMA_NOTE_CREATE` (full-fidelity binding for `Effect::NoteCreate`)
//!
//! The legacy AIR below pins `nullifier`/`merkle_root`/`value`/`asset_type`
//! as **single BabyBear felts** (Poseidon2-compressed digests, ~31 bits
//! each). That suffices for spend-side semantics (knowledge of spending
//! key + Merkle membership) but provides only felt-sized binding to a
//! verifier asking "which 32-byte nullifier was spent?".
//!
//! The schema-based AIRs in `effect_action_air.rs` carry every 32-byte
//! field as 8 × 4-byte BabyBear limbs (~248-bit binding) and every u64
//! amount as 2 × 32-bit limbs (full 64-bit binding). New code SHOULD
//! prefer them for action binding. The spend-side semantics half of the
//! legacy AIR (key knowledge + Merkle membership) can continue to live
//! here, or migrate to a dedicated key/membership AIR; only the binding
//! role moves.
//!
//! # Original docs
//!
//! This AIR proves:
//! 1. Prover knows `spending_key` (8 BabyBear limbs = 248 bits) such that
//!    `nullifier = poseidon2(commitment || spending_key[0..8] || creation_nonce)`
//! 2. Prover knows `owner`, `value`, `asset_type`, `creation_nonce`, `randomness` such that
//!    `commitment = poseidon2(owner || value || asset_type || creation_nonce || randomness)`
//! 3. The commitment is a member of a Merkle tree with a given root (Poseidon2 Merkle path)
//!
//! # Trace layout
//!
//! The trace is organized as a sequence of rows with width = 19:
//!
//! ```text
//! Row type: COMMITMENT (rows 0)
//!   col 0: owner
//!   col 1: value
//!   col 2: asset_type
//!   col 3: creation_nonce
//!   col 4: (zero — reserved for Merkle position validity constraint)
//!   col 5: commitment (computed = poseidon2_hash(owner, value, asset_type, creation_nonce, randomness))
//!   col 6..13: spending_key[0..8] (8 BabyBear limbs = 248 bits of security)
//!   col 14: nullifier (computed = poseidon2_hash(commitment, spending_key[0..8], creation_nonce))
//!   col 15: randomness
//!   col 16: is_merkle (0 for this row)
//!   col 17..18: unused (zero)
//!
//! Row type: MERKLE_LEVEL (rows 1..depth)
//!   col 0: current hash at this level
//!   col 1: sibling[0]
//!   col 2: sibling[1]
//!   col 3: sibling[2]
//!   col 4: position (0..3)
//!   col 5: parent = poseidon2_hash_4_to_1(children arranged by position)
//!   col 6..18: unused (zero)
//! ```
//!
//! # Public inputs
//!
//! - `nullifier`: The revealed nullifier (verifier sees this)
//! - `merkle_root`: The Merkle tree root (verifier sees this)
//! - `value`: The note value (verifier sees this — prevents value inflation)
//! - `asset_type`: The note asset type (verifier sees this — prevents asset substitution)
//! - `destination_federation`: Target federation identity, as a BabyBear felt
//!   (prevents cross-federation replay of bridge proofs). For non-bridge spends,
//!   set this to `BabyBear::ZERO`; the AIR pins the trace column to whatever
//!   the prover put in pi[4] so the verifier can require a specific value.
//!
//! # Security properties
//!
//! - The spending key is 248 bits (8 × 31-bit BabyBear limbs), requiring ~2^248 brute-force attempts
//! - The spending key is private (only in the witness, never in public inputs)
//! - The note owner is private (only in the witness)
//! - Value and asset_type are public inputs, bound by boundary constraints to the
//!   trace columns that participate in commitment recomputation. A spender cannot
//!   claim a different value/asset_type than what is committed in the note.
//! - Soundness: a cheating prover must break Poseidon2 collision resistance
//!
//! # Companion AIR: `bridge_action_witness`
//!
//! Each 32-byte field in this AIR's PI vector (`nullifier`, `merkle_root`,
//! `destination_federation`) lives in a **single** BabyBear slot — the prover
//! compresses the 32 bytes via `bytes_to_babybear` (Poseidon2 of 8 limbs).
//! That compression is sufficient for the spending-key + Merkle proof's
//! binding, but for bridge mints the destination wants algebraic guarantees
//! at full 32-byte fidelity on (nullifier, recipient, destination_federation)
//! and at full 64-bit fidelity on amount. The sibling AIR
//! `crate::bridge_action_witness::BridgeActionAir` provides exactly that: 8 limbs
//! per 32-byte field and 2 limbs (low+high 32) for u64 amount. A complete
//! bridge presentation now carries BOTH proofs.

use crate::field::BabyBear;
use crate::poseidon2::{hash_4_to_1, hash_many};

/// Trace width for the note spending AIR.
///
/// Columns 0..20 are the legacy layout: 5 note preimage felts + commitment +
/// 8 key limbs + nullifier + randomness + is_merkle + nullifier_intermediate +
/// destination_federation + value_hi (the 30-bit-trunc fix high limb).
///
/// Columns 20..62 are the FULL-WIDTH commitment-binding extension (this lane).
/// They carry the 28-limb Poseidon2 preimage (owner 8 ‖ value 2 ‖ asset_type 2
/// ‖ creation_nonce 8 ‖ randomness 8) — the SAME limb layout as
/// `dregg_cell::Note::poseidon2_commitment` — plus 6 chained-hash intermediate
/// columns. The legacy single-felt commitment (col 5) previously bound only the
/// first 4 bytes of each 32-byte field (~31 bits) and the low 32 bits of each
/// u64; the limb columns + the `commitment_full` binding close that truncation
/// so two notes differing in ANY byte of ANY field produce distinct in-circuit
/// commitments. See [`limb_col`].
pub const NOTE_SPENDING_WIDTH: usize = 62;

/// Number of BabyBear limbs for the spending key (248 bits of security).
pub const SPENDING_KEY_LIMBS: usize = 8;

/// Minimum Merkle depth supported.
pub const MIN_MERKLE_DEPTH: usize = 2;

/// Column indices for the commitment row.
/// Note: column 4 is kept as zero for the commitment row to satisfy
/// the position validity constraint (which checks all rows uniformly).
pub mod col {
    pub const OWNER: usize = 0;
    pub const VALUE: usize = 1;
    pub const ASSET_TYPE: usize = 2;
    pub const CREATION_NONCE: usize = 3;
    // col 4 is zero in commitment row (reserved for Merkle position)
    pub const COMMITMENT: usize = 5;
    /// Spending key limbs occupy columns 6..14 (8 BabyBear elements = 248 bits).
    pub const SPENDING_KEY_START: usize = 6;
    pub const SPENDING_KEY_END: usize = 14; // exclusive
    pub const NULLIFIER: usize = 14;
    pub const RANDOMNESS: usize = 15;
    /// Row type: 0 = commitment row, 1 = Merkle/padding row.
    /// Used to gate constraints appropriately.
    pub const IS_MERKLE: usize = 16;
    // col 17 is `NULLIFIER_INTERMEDIATE` (DSL two-step nullifier hash).
    /// Destination-federation column (commitment row only).
    /// Bound to pi[4] by a boundary constraint so the proof is pinned to a
    /// single target federation. For non-bridge spends the prover sets this
    /// (and pi[4]) to BabyBear::ZERO.
    pub const DESTINATION_FEDERATION: usize = 18;
    /// High limb of the note value (bits 30..64 of the claimed u64 amount),
    /// commitment row only. Bound to `pi::VALUE_HI` by a boundary constraint.
    ///
    /// The 30-bit-trunc fix (CAVEAT-LAYER-COVERAGE.md §6.5): `col::VALUE`
    /// (pi[2]) holds the low-30-bit limb that participates in the note
    /// commitment; this column holds the upper 34 bits so the proof binds the
    /// FULL u64 amount, not just the low 30 bits. For a u64 amount `v`, the
    /// prover sets `VALUE = v & ((1<<30)-1)` and `VALUE_HI = v >> 30`. Two
    /// amounts differing above bit 30 produce distinct `VALUE_HI` and thus
    /// distinct proofs. For amounts that fit in 30 bits (and all pre-fix
    /// callers using the BabyBear-typed API), `VALUE_HI == 0`.
    pub const VALUE_HI: usize = 19;
}

/// Column indices for the FULL-WIDTH commitment-binding extension.
///
/// These columns live only on the commitment row (row 0); they are zero on
/// Merkle / padding rows (which only touch cols 0..6). They carry the 28-limb
/// Poseidon2 preimage matching `dregg_cell::Note::poseidon2_commitment`:
///
/// ```text
///   owner          : 8 limbs  (owner[0..32] as 8 LE 4-byte chunks mod p)
///   value          : 2 limbs  (low 32 bits, high 32 bits)
///   asset_type     : 2 limbs  (low 32 bits, high 32 bits)
///   creation_nonce : 8 limbs  (creation_nonce[0..32] as 8 LE chunks)
///   randomness     : 8 limbs  (randomness[0..32] as 8 LE chunks)
/// ```
///
/// ordered owner ‖ value ‖ asset_type ‖ creation_nonce ‖ randomness, plus 6
/// chained-hash intermediate columns used to bind `col::COMMITMENT` to a
/// Poseidon2 sponge over all 28 limbs (see [`commitment_chain`]). Two notes
/// that differ in ANY byte of ANY field produce a DISTINCT 28-limb vector and
/// therefore a distinct in-circuit commitment (up to Poseidon2 collision
/// resistance) — the full-256-bit-per-field binding the legacy 5-felt layout
/// lacked.
pub mod limb_col {
    /// Total number of preimage limbs (8 + 2 + 2 + 8 + 8). Matches the 28-limb
    /// preimage of `dregg_cell::Note::poseidon2_commitment`.
    pub const PREIMAGE_LIMBS: usize = 28;
    /// Number of chained-hash intermediate columns (one per absorb step beyond
    /// the first, for the 7-step hash_fact chain over 28 limbs).
    pub const CHAIN_INTERMEDIATES: usize = 6;

    /// First limb column. The 28 preimage limbs occupy `START .. START+28`.
    pub const START: usize = 20;

    pub const OWNER_START: usize = START; // 20..28
    pub const VALUE_LO: usize = OWNER_START + 8; // 28
    pub const VALUE_HI: usize = VALUE_LO + 1; // 29
    pub const ASSET_LO: usize = VALUE_HI + 1; // 30
    pub const ASSET_HI: usize = ASSET_LO + 1; // 31
    pub const NONCE_START: usize = ASSET_HI + 1; // 32..40
    pub const RANDOMNESS_START: usize = NONCE_START + 8; // 40..48

    /// First chained-hash intermediate column. 6 intermediates occupy
    /// `CHAIN_START .. CHAIN_START+6` (48..54).
    pub const CHAIN_START: usize = RANDOMNESS_START + 8; // 48
    /// The recomputed full-width commitment (Poseidon2 sponge over the 28
    /// limbs). Bound to `col::COMMITMENT` by an equality constraint so the
    /// legacy commitment column equals the full-width binding.
    pub const COMMITMENT_FULL: usize = CHAIN_START + CHAIN_INTERMEDIATES; // 54

    /// Iterator over the 28 preimage limb column indices in canonical order
    /// (owner ‖ value ‖ asset_type ‖ creation_nonce ‖ randomness).
    pub fn preimage_cols() -> [usize; PREIMAGE_LIMBS] {
        let mut cols = [0usize; PREIMAGE_LIMBS];
        let mut i = 0;
        let mut c = 0;
        while c < 8 {
            cols[i] = OWNER_START + c;
            i += 1;
            c += 1;
        }
        cols[i] = VALUE_LO;
        i += 1;
        cols[i] = VALUE_HI;
        i += 1;
        cols[i] = ASSET_LO;
        i += 1;
        cols[i] = ASSET_HI;
        i += 1;
        c = 0;
        while c < 8 {
            cols[i] = NONCE_START + c;
            i += 1;
            c += 1;
        }
        c = 0;
        while c < 8 {
            cols[i] = RANDOMNESS_START + c;
            i += 1;
            c += 1;
        }
        cols
    }
}

/// Column indices for Merkle level rows.
pub mod merkle_col {
    pub const CURRENT: usize = 0;
    pub const SIB0: usize = 1;
    pub const SIB1: usize = 2;
    pub const SIB2: usize = 3;
    pub const POSITION: usize = 4;
    pub const PARENT: usize = 5;
}

/// Public input indices.
///
/// PI layout (5 BabyBear felts):
///   pi[0] = NULLIFIER
///   pi[1] = MERKLE_ROOT
///   pi[2] = VALUE
///   pi[3] = ASSET_TYPE
///   pi[4] = DESTINATION_FEDERATION  (bridge-replay binding; ZERO for non-bridge spends)
///
/// The DESTINATION_FEDERATION slot pins col::DESTINATION_FEDERATION (col 18)
/// of the commitment row via a boundary constraint, so a proof generated with
/// federation A cannot be replayed against federation B (cross-federation
/// inflation prevention). For local (non-bridge) spends, the prover puts
/// `BabyBear::ZERO` in this slot and the executor passes ZERO as well — the
/// boundary constraint then trivially holds.
pub mod pi {
    /// The nullifier (what the verifier sees).
    pub const NULLIFIER: usize = 0;
    /// The Merkle root (what the verifier sees).
    pub const MERKLE_ROOT: usize = 1;
    /// The note value (what the verifier sees — prevents value inflation).
    pub const VALUE: usize = 2;
    /// The note asset type (what the verifier sees — prevents asset type substitution).
    pub const ASSET_TYPE: usize = 3;
    /// The destination federation identity (BabyBear felt; ZERO for non-bridge spends).
    ///
    /// Bound to `col::DESTINATION_FEDERATION` (col 18) of the commitment row by a
    /// boundary constraint. This prevents replay of a spending proof against a
    /// federation the prover did not commit to.
    pub const DESTINATION_FEDERATION: usize = 4;
    /// The high limb of the note value (bits 30..64 of the claimed u64 amount).
    ///
    /// 30-bit-trunc fix (CAVEAT-LAYER-COVERAGE.md §6.5): `pi[2]` (VALUE) holds
    /// the low 30 bits (the felt that participates in the commitment); this
    /// slot holds the upper 34 bits. Bound to `col::VALUE_HI` by a boundary
    /// constraint at row 0 so the proof binds the FULL u64 amount. For amounts
    /// ≤ 2^30 (and all BabyBear-typed callers), this is `BabyBear::ZERO`.
    pub const VALUE_HI: usize = 5;
}

/// Witness for a note spending proof.
#[derive(Clone, Debug)]
pub struct NoteSpendingWitness {
    /// The owner's public key (field element representation).
    pub owner: BabyBear,
    /// The note value (amount).
    pub value: BabyBear,
    /// The asset type.
    pub asset_type: BabyBear,
    /// Creation nonce.
    pub creation_nonce: BabyBear,
    /// Random blinding factor.
    pub randomness: BabyBear,
    /// The spending key (secret): 8 BabyBear limbs = 248 bits of security.
    ///
    /// Each limb holds up to 31 bits (BabyBear modulus ~ 2^31). An adversary must
    /// brute-force all 8 limbs (~2^248 attempts) to recover the key from a known
    /// nullifier and commitment. Previously this was a single BabyBear element
    /// (~2^31 attempts = ~2 seconds on modern hardware).
    pub spending_key: [BabyBear; SPENDING_KEY_LIMBS],
    /// Merkle path siblings (one [BabyBear; 3] per level).
    pub merkle_siblings: Vec<[BabyBear; 3]>,
    /// Merkle path positions (one u8 per level, 0..3).
    pub merkle_positions: Vec<u8>,
    /// Destination-federation identity for bridge proofs.
    ///
    /// Bound to public input `pi[4]` (`pi::DESTINATION_FEDERATION`) and to
    /// `col::DESTINATION_FEDERATION` of the commitment row via a boundary
    /// constraint. For non-bridge spends, set to `BabyBear::ZERO`. The
    /// verifier expects the same value here as the executor passes in the PI
    /// buffer; otherwise the proof is rejected.
    pub destination_federation: BabyBear,
    /// The FULL-WIDTH 28-limb Poseidon2 preimage of the note commitment.
    ///
    /// Layout matches `dregg_cell::Note::poseidon2_commitment` exactly:
    /// owner[8] ‖ value[lo,hi] ‖ asset_type[lo,hi] ‖ creation_nonce[8] ‖
    /// randomness[8]. These limbs are placed into the [`limb_col`] columns and
    /// the in-circuit commitment binds ALL 28 of them via a chained Poseidon2
    /// sponge ([`commitment_chain`]). This closes the legacy truncation where
    /// each 32-byte field contributed only its first 4 bytes (~31 bits) and
    /// each u64 only its low 32 bits.
    ///
    /// For witnesses constructed from BabyBear-typed fields (the legacy API),
    /// [`NoteSpendingWitness::from_real_proof`] derives a faithful 28-limb
    /// vector by limb-decomposing `owner`/`creation_nonce`/`randomness` (single
    /// felts → high limbs zero) and splitting `value`/`asset_type` into
    /// low/high. For full-width binding, construct the witness with
    /// [`NoteSpendingWitness::from_note_limbs`] so every byte of every field is
    /// bound.
    pub preimage_limbs: [BabyBear; limb_col::PREIMAGE_LIMBS],
}

/// Decompose a u64 into 2 BabyBear limbs `[low 32 bits, high 32 bits]` (mod p).
///
/// Binds the FULL 64 bits of a u64 note field. Matches
/// `dregg_cell::note::u64_to_limbs` (a 32/32 split). Used for the asset_type
/// field, where there is no separate PI high limb.
pub fn u64_to_limbs(v: u64) -> [BabyBear; 2] {
    [
        BabyBear::new_canonical(v as u32),
        BabyBear::new_canonical((v >> 32) as u32),
    ]
}

/// Decompose a u64 into the (low-30, upper-34) BabyBear limb pair used for the
/// note VALUE field.
///
/// Unlike [`u64_to_limbs`]'s 32/32 split, the value field uses a 30/34 boundary
/// so the low limb (`col::VALUE`, which is also pinned by `pi::VALUE`) is a
/// canonical sub-2^30 BabyBear that participates directly in the commitment
/// preimage, while the high limb (`col::VALUE_HI` / `limb_col::VALUE_HI`, pinned
/// by `pi::VALUE_HI`) carries the remaining 34 bits. Together they bind the FULL
/// u64 amount. This matches the executor's bridge-mint `u64_to_limbs` split
/// (CAVEAT-LAYER-COVERAGE.md §6.5), so prover and verifier agree.
pub fn value_to_limbs_30_34(v: u64) -> [BabyBear; 2] {
    [
        BabyBear::new_canonical((v & ((1u64 << 30) - 1)) as u32),
        BabyBear::new_canonical((v >> 30) as u32),
    ]
}

/// Assemble the canonical 28-limb commitment preimage from a real note's raw
/// fields, in the SAME order as `dregg_cell::Note::poseidon2_commitment`:
/// owner[8] ‖ value[lo,hi] ‖ asset_type[lo,hi] ‖ creation_nonce[8] ‖
/// randomness[8].
pub fn note_to_preimage_limbs(
    owner: &[u8; 32],
    value: u64,
    asset_type: u64,
    creation_nonce: &[u8; 32],
    randomness: &[u8; 32],
) -> [BabyBear; limb_col::PREIMAGE_LIMBS] {
    let mut out = [BabyBear::ZERO; limb_col::PREIMAGE_LIMBS];
    let owner_l = crate::effect_vm::bytes32_to_8_limbs(owner);
    // VALUE uses the 30/34 split so the low limb matches `col::VALUE`/`pi::VALUE`
    // and the high limb matches `col::VALUE_HI`/`pi::VALUE_HI`. asset_type uses a
    // plain 32/32 split (no separate PI high limb; high bits bind only through
    // the commitment).
    let value_l = value_to_limbs_30_34(value);
    let asset_l = u64_to_limbs(asset_type);
    let nonce_l = crate::effect_vm::bytes32_to_8_limbs(creation_nonce);
    let rand_l = crate::effect_vm::bytes32_to_8_limbs(randomness);
    out[0..8].copy_from_slice(&owner_l);
    out[8] = value_l[0];
    out[9] = value_l[1];
    out[10] = asset_l[0];
    out[11] = asset_l[1];
    out[12..20].copy_from_slice(&nonce_l);
    out[20..28].copy_from_slice(&rand_l);
    out
}

/// Recompute the FULL-WIDTH note commitment as a chained Poseidon2 sponge over
/// the 28 preimage limbs, returning `(commitment, intermediates)`.
///
/// The chain absorbs the 28 limbs in 7 `hash_fact` steps (predicate + 4 terms
/// per step): the first step consumes limbs 0..5, each subsequent step folds the
/// running hash with the next 4 limbs (last step zero-pads). The 6 intermediate
/// digests (after steps 1..7, excluding the final) are returned so the trace can
/// expose them in the [`limb_col`] chain columns for the in-circuit `Hash`
/// constraints to recompute and check.
///
/// This is a DIFFERENT sponge than `Note::poseidon2_commitment`'s single
/// `hash_many(28)` call (the DSL constraint primitive is `hash_fact`, not the
/// variable-length `hash_many`). It is, however, a full-256-bit-per-field
/// binding over the IDENTICAL 28-limb preimage: two notes differing in any byte
/// of any field yield a distinct limb vector and therefore a distinct commitment
/// (up to Poseidon2 collision resistance). The in-circuit commitment is
/// internally consistent (prover computes it, the AIR re-derives and checks it,
/// the nullifier and Merkle membership both chain off it), so an exact match to
/// `hash_many` is not required for soundness; full-width binding is. See the
/// residual note in this file's tests.
// crypto index loops kept verbatim
#[allow(clippy::needless_range_loop)]
pub fn commitment_chain(
    limbs: &[BabyBear; limb_col::PREIMAGE_LIMBS],
) -> (BabyBear, [BabyBear; limb_col::CHAIN_INTERMEDIATES]) {
    use crate::poseidon2::hash_fact;
    // Step 1: h = hash_fact(limbs[0], [limbs[1..5]])  (consumes 5)
    let mut running = hash_fact(limbs[0], &[limbs[1], limbs[2], limbs[3], limbs[4]]);
    let mut intermediates = [BabyBear::ZERO; limb_col::CHAIN_INTERMEDIATES];
    // Steps 2..8: each folds 4 more limbs. 28 - 5 = 23 remaining => 6 steps
    // of 4 (the 6th zero-pads its last term). After each step (except the
    // final) we record the running hash as an intermediate.
    let mut idx = 5usize;
    for step in 0..limb_col::CHAIN_INTERMEDIATES {
        intermediates[step] = running;
        let t0 = if idx < limbs.len() {
            limbs[idx]
        } else {
            BabyBear::ZERO
        };
        let t1 = if idx + 1 < limbs.len() {
            limbs[idx + 1]
        } else {
            BabyBear::ZERO
        };
        let t2 = if idx + 2 < limbs.len() {
            limbs[idx + 2]
        } else {
            BabyBear::ZERO
        };
        let t3 = if idx + 3 < limbs.len() {
            limbs[idx + 3]
        } else {
            BabyBear::ZERO
        };
        running = hash_fact(running, &[t0, t1, t2, t3]);
        idx += 4;
    }
    (running, intermediates)
}

impl NoteSpendingWitness {
    /// Compute the commitment: poseidon2_hash(owner, value, asset_type, creation_nonce, randomness).
    ///
    /// NOTE: this is the LEGACY 5-felt commitment, retained for the deprecated
    /// hand-written AIR and for callers that still reason in single felts. The
    /// production DSL path binds the FULL-WIDTH commitment via
    /// [`NoteSpendingWitness::commitment_full`] (28-limb chained sponge).
    pub fn commitment(&self) -> BabyBear {
        hash_many(&[
            self.owner,
            self.value,
            self.asset_type,
            self.creation_nonce,
            self.randomness,
        ])
    }

    /// Compute the FULL-WIDTH commitment binding all 28 preimage limbs (the
    /// chained Poseidon2 sponge of [`commitment_chain`]). Two notes differing in
    /// ANY byte of ANY field produce distinct values here.
    pub fn commitment_full(&self) -> BabyBear {
        commitment_chain(&self.preimage_limbs).0
    }

    /// Compute the nullifier: poseidon2_hash(commitment, spending_key[0..8], creation_nonce).
    ///
    /// The nullifier is derived from all 8 key limbs, making brute-force infeasible (~2^248).
    ///
    /// NOTE: this LEGACY accessor chains off the legacy 5-felt [`commitment`].
    /// The production DSL nullifier (`dsl_nullifier`) chains off the FULL-WIDTH
    /// commitment so the nullifier also binds the full 256-bit-per-field
    /// identity.
    pub fn nullifier(&self) -> BabyBear {
        let commitment = self.commitment();
        let mut inputs = Vec::with_capacity(1 + SPENDING_KEY_LIMBS + 1);
        inputs.push(commitment);
        inputs.extend_from_slice(&self.spending_key);
        inputs.push(self.creation_nonce);
        hash_many(&inputs) // 10 inputs: commitment + 8 key limbs + nonce
    }

    /// Compute the Merkle root by hashing up the path from the commitment.
    pub fn merkle_root(&self) -> BabyBear {
        let commitment = self.commitment();
        let mut current = commitment;

        for (i, siblings) in self.merkle_siblings.iter().enumerate() {
            let pos = self.merkle_positions[i];
            let mut children = [BabyBear::ZERO; 4];
            let mut sib_idx = 0;
            for j in 0..4u8 {
                if j == pos {
                    children[j as usize] = current;
                } else {
                    children[j as usize] = siblings[sib_idx];
                    sib_idx += 1;
                }
            }
            current = hash_4_to_1(&children);
        }
        current
    }

    /// Create a witness from a real Poseidon2 Merkle proof (from a Poseidon2MerkleTree).
    ///
    /// This is the bridge between the persistent note tree and the STARK prover:
    /// given a note's field-element preimage, a spending key, and a real Merkle proof
    /// from the Poseidon2 tree, construct a witness that can be used to generate
    /// a valid STARK proof.
    ///
    /// # Arguments
    ///
    /// * `owner` - The note owner (field element)
    /// * `value` - The note value (field element)
    /// * `asset_type` - The asset type (field element)
    /// * `creation_nonce` - The creation nonce (field element)
    /// * `randomness` - The randomness/blinding factor (field element)
    /// * `spending_key` - The spending key (8 BabyBear limbs = 248-bit secret)
    /// * `merkle_siblings` - Siblings from the Poseidon2MerkleProof
    /// * `merkle_positions` - Positions from the Poseidon2MerkleProof
    ///
    /// # Panics
    ///
    /// Panics if `merkle_siblings.len() != merkle_positions.len()`.
    // signature kept as-is
    #[allow(clippy::too_many_arguments)]
    pub fn from_real_proof(
        owner: BabyBear,
        value: BabyBear,
        asset_type: BabyBear,
        creation_nonce: BabyBear,
        randomness: BabyBear,
        spending_key: [BabyBear; SPENDING_KEY_LIMBS],
        merkle_siblings: Vec<[BabyBear; 3]>,
        merkle_positions: Vec<u8>,
    ) -> Self {
        assert_eq!(
            merkle_siblings.len(),
            merkle_positions.len(),
            "siblings and positions must have the same length"
        );
        // Derive a 28-limb preimage from the BabyBear-typed fields. The
        // single-felt owner/creation_nonce/randomness occupy their first limb
        // (high limbs zero); value/asset_type split into low/high. Callers with
        // raw 32-byte/u64 note fields should use `from_note_limbs` for true
        // full-256-bit binding.
        let preimage_limbs =
            Self::limbs_from_felts(owner, value, asset_type, creation_nonce, randomness);
        Self {
            owner,
            value,
            asset_type,
            creation_nonce,
            randomness,
            spending_key,
            merkle_siblings,
            merkle_positions,
            destination_federation: BabyBear::ZERO,
            preimage_limbs,
        }
    }

    /// Derive a 28-limb preimage from single BabyBear felts (legacy callers).
    ///
    /// owner/creation_nonce/randomness go into their lowest limb (the rest of
    /// the 8-limb slots are zero); value/asset_type split low/high. This is a
    /// faithful, injective embedding of the felt-typed witness into the
    /// full-width layout — it does NOT recover bytes a single felt never had,
    /// but it binds whatever the legacy witness carried.
    pub fn limbs_from_felts(
        owner: BabyBear,
        value: BabyBear,
        asset_type: BabyBear,
        creation_nonce: BabyBear,
        randomness: BabyBear,
    ) -> [BabyBear; limb_col::PREIMAGE_LIMBS] {
        let mut out = [BabyBear::ZERO; limb_col::PREIMAGE_LIMBS];
        out[0] = owner; // owner limb 0
        out[8] = value; // value lo
        out[10] = asset_type; // asset lo
        out[12] = creation_nonce; // nonce limb 0
        out[20] = randomness; // randomness limb 0
        out
    }

    /// Construct a full-width witness directly from a note's RAW fields so the
    /// in-circuit commitment binds all 256 bits per field, matching
    /// `dregg_cell::Note::poseidon2_commitment`'s 28-limb preimage.
    ///
    /// The single-felt `owner`/`value`/`asset_type`/`creation_nonce`/
    /// `randomness` columns (used by the legacy commitment + the value/asset PI
    /// boundary bindings) are set to the LOW limb of the corresponding field so
    /// the existing boundary constraints remain meaningful; the full identity is
    /// bound through `preimage_limbs`.
    #[allow(clippy::too_many_arguments)]
    pub fn from_note_limbs(
        owner: &[u8; 32],
        value: u64,
        asset_type: u64,
        creation_nonce: &[u8; 32],
        randomness: &[u8; 32],
        spending_key: [BabyBear; SPENDING_KEY_LIMBS],
        merkle_siblings: Vec<[BabyBear; 3]>,
        merkle_positions: Vec<u8>,
    ) -> Self {
        assert_eq!(
            merkle_siblings.len(),
            merkle_positions.len(),
            "siblings and positions must have the same length"
        );
        let preimage_limbs =
            note_to_preimage_limbs(owner, value, asset_type, creation_nonce, randomness);
        Self {
            owner: preimage_limbs[0],
            value: preimage_limbs[8],
            asset_type: preimage_limbs[10],
            creation_nonce: preimage_limbs[12],
            randomness: preimage_limbs[20],
            spending_key,
            merkle_siblings,
            merkle_positions,
            destination_federation: BabyBear::ZERO,
            preimage_limbs,
        }
    }

    /// Builder helper: set the destination federation for a bridge-spend proof.
    ///
    /// For local (non-bridge) spends, leave at `BabyBear::ZERO` (the default).
    /// Verifiers passing a non-zero `pi[4]` reject proofs whose trace column
    /// `col::DESTINATION_FEDERATION` does not match.
    pub fn with_destination_federation(mut self, dest: BabyBear) -> Self {
        self.destination_federation = dest;
        self
    }
}

/// The note spending AIR. Proves knowledge of spending key + note preimage + Merkle membership.
///
/// The Note Spending AIR's shape descriptor (VK v2; see
/// `circuit::air_descriptor`). Captures the externally visible shape
/// of [`NoteSpendingAir`] so callers can fingerprint it into VK v2's
/// layered hash.
///
/// `column_count` is the fixed-width commitment row (`NOTE_SPENDING_WIDTH`);
/// the Merkle-level rows that follow use a different 6-column layout
/// (see [`merkle_col`]) but are not separately surfaced through the
/// descriptor — the AIR's `width()` is the trace-row width, which is
/// the commitment-row width.
pub const AIR_DESCRIPTOR: crate::air_descriptor::AirDescriptor =
    crate::air_descriptor::AirDescriptor {
        air_id: "note_spending_witness_v1",
        column_count: NOTE_SPENDING_WIDTH,
        public_input_layout: &[
            crate::air_descriptor::PiSlot {
                name: "nullifier",
                offset: pi::NULLIFIER,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "merkle_root",
                offset: pi::MERKLE_ROOT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "value",
                offset: pi::VALUE,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "asset_type",
                offset: pi::ASSET_TYPE,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "destination_federation",
                offset: pi::DESTINATION_FEDERATION,
                length_in_felts: 1,
            },
        ],
        // Constraints: commitment-row Poseidon2 binding, spending-key
        // verification, Merkle-level recursion, nullifier derivation,
        // is_merkle flag boolean, position validity. Approximate count
        // is a stable property of the AIR shape — the exact value will
        // not vary across rebuilds.
        constraint_polynomial_count: 12,
        boundary_constraint_count: 5,
        max_degree: 4,
        source_hash: None,
    };

/// DEPRECATED: use `crate::dsl::note_spending::note_spending_dsl_circuit()`.
///
/// Despite the `Air` name this type carries NO constraint algebra — it is a
/// depth/config holder retained for the trace-generation helpers below. The
/// constraints live in `note_spending_circuit_descriptor()`; the executor's
/// verification path is `turn::executor::apply::verify_note_spend_descriptor2`.
#[deprecated(note = "Use crate::dsl::note_spending::note_spending_dsl_circuit() instead")]
pub struct NoteSpendingAir {
    /// Merkle tree depth (number of levels in the path).
    pub depth: usize,
}

impl NoteSpendingAir {
    pub fn new(depth: usize) -> Self {
        assert!(
            depth >= MIN_MERKLE_DEPTH,
            "Merkle depth must be at least {MIN_MERKLE_DEPTH}"
        );
        Self { depth }
    }

    /// Generate the execution trace from a witness.
    ///
    /// Returns (trace, public_inputs) where:
    /// - trace: rows of width NOTE_SPENDING_WIDTH
    /// - public_inputs: [nullifier, merkle_root]
    pub fn generate_trace(witness: &NoteSpendingWitness) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let depth = witness.merkle_siblings.len();
        assert_eq!(witness.merkle_positions.len(), depth);
        assert!(
            depth >= MIN_MERKLE_DEPTH,
            "Need at least depth {MIN_MERKLE_DEPTH}"
        );

        let commitment = witness.commitment();
        let nullifier = witness.nullifier();

        // Total rows: 1 (commitment/nullifier row) + depth (Merkle levels)
        let total_rows = 1 + depth;
        let padded_rows = total_rows.next_power_of_two();

        let mut trace = Vec::with_capacity(padded_rows);

        // Row 0: commitment and nullifier computation
        // Note: col 4 (position) is left as zero to satisfy the position validity constraint.
        let mut row0 = vec![BabyBear::ZERO; NOTE_SPENDING_WIDTH];
        row0[col::OWNER] = witness.owner;
        row0[col::VALUE] = witness.value;
        row0[col::ASSET_TYPE] = witness.asset_type;
        row0[col::CREATION_NONCE] = witness.creation_nonce;
        row0[col::COMMITMENT] = commitment;
        // Place all 8 spending key limbs in columns 6..14
        for (j, &limb) in witness.spending_key.iter().enumerate() {
            row0[col::SPENDING_KEY_START + j] = limb;
        }
        row0[col::NULLIFIER] = nullifier;
        row0[col::RANDOMNESS] = witness.randomness;
        row0[col::IS_MERKLE] = BabyBear::ZERO; // This is the commitment row
        row0[col::DESTINATION_FEDERATION] = witness.destination_federation;
        // FULL-WIDTH commitment-binding columns (28 limbs + chain). These are
        // present on the commitment row only; Merkle/padding rows leave them
        // zero. The legacy hand-written AIR fills them for layout consistency
        // even though its `eval_constraints` keeps using the legacy 5-felt
        // commitment (the DSL path is the one that algebraically binds them).
        let preimage = witness.preimage_limbs;
        for (slot, &col) in limb_col::preimage_cols().iter().enumerate() {
            row0[col] = preimage[slot];
        }
        let (full_commit, intermediates) = commitment_chain(&preimage);
        for (k, &inter) in intermediates.iter().enumerate() {
            row0[limb_col::CHAIN_START + k] = inter;
        }
        row0[limb_col::COMMITMENT_FULL] = full_commit;
        trace.push(row0);

        // Rows 1..depth+1: Merkle membership proof
        let mut current = commitment;
        for i in 0..depth {
            let pos = witness.merkle_positions[i];
            assert!(pos < 4, "Merkle position must be 0..3");

            let siblings = &witness.merkle_siblings[i];

            // Compute parent hash
            let mut children = [BabyBear::ZERO; 4];
            let mut sib_idx = 0;
            for j in 0..4u8 {
                if j == pos {
                    children[j as usize] = current;
                } else {
                    children[j as usize] = siblings[sib_idx];
                    sib_idx += 1;
                }
            }
            let parent = hash_4_to_1(&children);

            let mut row = vec![BabyBear::ZERO; NOTE_SPENDING_WIDTH];
            row[merkle_col::CURRENT] = current;
            row[merkle_col::SIB0] = siblings[0];
            row[merkle_col::SIB1] = siblings[1];
            row[merkle_col::SIB2] = siblings[2];
            row[merkle_col::POSITION] = BabyBear::new(pos as u32);
            row[merkle_col::PARENT] = parent;
            row[col::IS_MERKLE] = BabyBear::ONE; // Merkle row
            trace.push(row);

            current = parent;
        }

        let merkle_root = current;

        // Pad to power of 2
        let padding_parent =
            hash_4_to_1(&[merkle_root, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO]);
        for _ in total_rows..padded_rows {
            let mut row = vec![BabyBear::ZERO; NOTE_SPENDING_WIDTH];
            row[merkle_col::CURRENT] = merkle_root;
            row[merkle_col::PARENT] = padding_parent;
            row[col::IS_MERKLE] = BabyBear::ONE; // Padding treated as Merkle row
            trace.push(row);
        }

        let public_inputs = vec![
            nullifier,
            merkle_root,
            witness.value,
            witness.asset_type,
            witness.destination_federation,
        ];
        (trace, public_inputs)
    }
}

/// Create a test witness for note spending proofs.
///
/// Generates a deterministic witness with the given parameters and a Merkle path of the specified depth.
/// The spending key is provided as 8 BabyBear limbs (248 bits).
pub fn create_test_witness(
    owner: BabyBear,
    value: BabyBear,
    asset_type: BabyBear,
    spending_key: [BabyBear; SPENDING_KEY_LIMBS],
    depth: usize,
) -> NoteSpendingWitness {
    // Deterministic creation nonce and randomness
    let creation_nonce = hash_many(&[owner, value, BabyBear::new(0xCAFE)]);
    let randomness = hash_many(&[owner, value, BabyBear::new(0xBEEF)]);

    // Build a Merkle path with deterministic siblings
    let mut merkle_siblings = Vec::with_capacity(depth);
    let mut merkle_positions = Vec::with_capacity(depth);

    for i in 0..depth {
        let pos = (i % 4) as u8;
        let siblings = [
            hash_many(&[BabyBear::new((i * 3 + 1) as u32), owner]),
            hash_many(&[BabyBear::new((i * 3 + 2) as u32), owner]),
            hash_many(&[BabyBear::new((i * 3 + 3) as u32), owner]),
        ];
        merkle_siblings.push(siblings);
        merkle_positions.push(pos);
    }

    let preimage_limbs =
        NoteSpendingWitness::limbs_from_felts(owner, value, asset_type, creation_nonce, randomness);
    NoteSpendingWitness {
        owner,
        value,
        asset_type,
        creation_nonce,
        randomness,
        spending_key,
        merkle_siblings,
        merkle_positions,
        destination_federation: BabyBear::ZERO,
        preimage_limbs,
    }
}

/// Create a deterministic 8-limb test spending key from a single seed value.
///
/// Each limb is derived deterministically from the seed, giving a full 248-bit key
/// while keeping tests reproducible.
// crypto index loops kept verbatim
#[allow(clippy::needless_range_loop)]
pub fn test_spending_key(seed: u32) -> [BabyBear; SPENDING_KEY_LIMBS] {
    let mut limbs = [BabyBear::ZERO; SPENDING_KEY_LIMBS];
    for i in 0..SPENDING_KEY_LIMBS {
        limbs[i] = hash_many(&[BabyBear::new(seed), BabyBear::new(i as u32)]);
    }
    limbs
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn witness_commitment_deterministic() {
        let key = test_spending_key(0xDEAD);
        let w1 = create_test_witness(
            BabyBear::new(1000),
            BabyBear::new(500),
            BabyBear::new(1),
            key,
            4,
        );
        let w2 = create_test_witness(
            BabyBear::new(1000),
            BabyBear::new(500),
            BabyBear::new(1),
            key,
            4,
        );
        assert_eq!(w1.commitment(), w2.commitment());
        assert_eq!(w1.nullifier(), w2.nullifier());
        assert_eq!(w1.merkle_root(), w2.merkle_root());
    }

    #[test]
    fn witness_different_key_different_nullifier() {
        let key1 = test_spending_key(0xDEAD);
        let key2 = test_spending_key(0xBEEF);
        let w1 = create_test_witness(
            BabyBear::new(1000),
            BabyBear::new(500),
            BabyBear::new(1),
            key1,
            4,
        );
        let w2 = create_test_witness(
            BabyBear::new(1000),
            BabyBear::new(500),
            BabyBear::new(1),
            key2, // different key
            4,
        );
        // Same commitment (key doesn't affect commitment)
        assert_eq!(w1.commitment(), w2.commitment());
        // Different nullifier (key affects nullifier)
        assert_ne!(w1.nullifier(), w2.nullifier());
    }

    #[test]
    fn trace_generation_correct_dimensions() {
        let key = test_spending_key(0xFF);
        let witness = create_test_witness(
            BabyBear::new(42),
            BabyBear::new(100),
            BabyBear::new(1),
            key,
            4,
        );
        let (trace, public_inputs) = NoteSpendingAir::generate_trace(&witness);

        // 1 commitment row + 4 Merkle rows = 5, padded to 8
        assert_eq!(trace.len(), 8);
        assert!(trace.len().is_power_of_two());

        // Width is NOTE_SPENDING_WIDTH (19)
        for row in &trace {
            assert_eq!(row.len(), NOTE_SPENDING_WIDTH);
        }

        // Public inputs: [nullifier, merkle_root, value, asset_type, destination_federation]
        assert_eq!(public_inputs.len(), 5);
        assert_eq!(public_inputs[pi::NULLIFIER], witness.nullifier());
        assert_eq!(public_inputs[pi::MERKLE_ROOT], witness.merkle_root());
        assert_eq!(public_inputs[pi::VALUE], witness.value);
        assert_eq!(public_inputs[pi::ASSET_TYPE], witness.asset_type);
        assert_eq!(
            public_inputs[pi::DESTINATION_FEDERATION],
            witness.destination_federation
        );
    }

    #[test]
    fn trace_commitment_row_has_correct_hashes() {
        let key = test_spending_key(0xFF);
        let witness = create_test_witness(
            BabyBear::new(42),
            BabyBear::new(100),
            BabyBear::new(1),
            key,
            4,
        );
        let (trace, _) = NoteSpendingAir::generate_trace(&witness);

        // Row 0 is the commitment/nullifier row
        let row0 = &trace[0];
        assert_eq!(row0[col::OWNER], witness.owner);
        assert_eq!(row0[col::VALUE], witness.value);
        assert_eq!(row0[col::ASSET_TYPE], witness.asset_type);
        assert_eq!(row0[col::CREATION_NONCE], witness.creation_nonce);
        assert_eq!(row0[col::RANDOMNESS], witness.randomness);
        assert_eq!(row0[col::COMMITMENT], witness.commitment());
        // All 8 spending key limbs are in the trace
        for j in 0..SPENDING_KEY_LIMBS {
            assert_eq!(row0[col::SPENDING_KEY_START + j], witness.spending_key[j]);
        }
        assert_eq!(row0[col::NULLIFIER], witness.nullifier());
        // Position column is zero for commitment row (satisfies position validity)
        assert_eq!(row0[merkle_col::POSITION], BabyBear::ZERO);
    }

    #[test]
    fn trace_merkle_chain_continuity() {
        let key = test_spending_key(0xFF);
        let witness = create_test_witness(
            BabyBear::new(42),
            BabyBear::new(100),
            BabyBear::new(1),
            key,
            4,
        );
        let (trace, _) = NoteSpendingAir::generate_trace(&witness);

        // Row 0 commitment should feed into row 1 current
        assert_eq!(trace[0][col::COMMITMENT], trace[1][merkle_col::CURRENT]);

        // Each Merkle level: parent[i] = current[i+1]
        for i in 1..4 {
            assert_eq!(
                trace[i][merkle_col::PARENT],
                trace[i + 1][merkle_col::CURRENT],
                "Merkle chain broken at level {i}"
            );
        }
    }

    #[test]
    fn spending_key_not_brute_forceable() {
        // With 8 limbs, brute-forcing requires ~2^248 attempts.
        // This test verifies the key space is > 2^31 (the old vulnerability).
        let key = test_spending_key(0xDEAD_BEEF);
        let witness = create_test_witness(
            BabyBear::new(1000),
            BabyBear::new(500),
            BabyBear::new(1),
            key,
            4,
        );

        // The spending key is 8 limbs, each ~31 bits, totalling ~248 bits.
        assert_eq!(witness.spending_key.len(), SPENDING_KEY_LIMBS);
        assert_eq!(SPENDING_KEY_LIMBS, 8);

        // Verify that all limbs are non-trivial (not all zero — the test key is derived)
        let non_zero_limbs = witness
            .spending_key
            .iter()
            .filter(|&&l| l != BabyBear::ZERO)
            .count();
        assert!(
            non_zero_limbs >= 6,
            "Test key should have most limbs non-zero, got {non_zero_limbs}"
        );
    }

    #[test]
    fn spending_key_limbs_roundtrip() {
        // Verify the conversion from 256-bit external key to 8 BabyBear limbs.
        let external_key: [u8; 32] = [
            0xDE, 0xAD, 0xBE, 0xEF, 0xCA, 0xFE, 0xBA, 0xBE, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06,
            0x07, 0x08, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xAA, 0xBB, 0xCC,
            0xDD, 0xEE, 0xFF, 0x00,
        ];
        let limbs = crate::effect_vm::bytes32_to_8_limbs(&external_key);
        assert_eq!(limbs.len(), 8);

        // Each limb should be a valid BabyBear element (< p)
        for limb in &limbs {
            assert!(limb.0 < (1u32 << 31) - 1); // BabyBear p = 2^31 - 1
        }

        // Deterministic
        let limbs2 = crate::effect_vm::bytes32_to_8_limbs(&external_key);
        assert_eq!(limbs, limbs2);
    }

    #[test]
    fn flipping_single_key_limb_changes_nullifier() {
        // Verify that changing ANY single limb of the 8-limb key changes the nullifier.
        let base_key = test_spending_key(0x12345678);
        let witness = create_test_witness(
            BabyBear::new(42),
            BabyBear::new(100),
            BabyBear::new(1),
            base_key,
            4,
        );
        let base_nullifier = witness.nullifier();

        for i in 0..SPENDING_KEY_LIMBS {
            let mut modified_key = base_key;
            modified_key[i] = BabyBear::new(modified_key[i].0.wrapping_add(1) % ((1u32 << 31) - 1));
            let mut modified_witness = witness.clone();
            modified_witness.spending_key = modified_key;
            assert_ne!(
                modified_witness.nullifier(),
                base_nullifier,
                "Flipping limb {i} must change the nullifier"
            );
        }
    }
}
