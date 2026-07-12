//! The MPT HOLDING-COMMITMENT leaf — P0 of the verified-light-client fold pilot
//! (`docs/deos/VERIFIED-LIGHTCLIENT-FOLD-PILOT.md` §2 P0): the EVM-MPT/keccak
//! state-inclusion verification's first recursion-foldable increment, riding the
//! DEPLOYED `CarrierWitness::Custom` arm with ZERO new circuit code and NO VK
//! movement.
//!
//! ## What this leaf proves IN-AIR (the DECO shape, exactly)
//!
//! A Poseidon2-only [`CellProgram`] that recomputes, in-AIR, the HOLDING IDENTITY
//! over its PI-pinned fields — the EIP-1186 ERC-20 holding tuple the rung-2
//! executor verifies (`eth-lightclient/src/evm.rs::verify_erc20_holding`):
//!
//!   * First-row PI pins: `state_root[0..8]`, `token`, `holder`, `slot`,
//!     `balance`, `holding_hash` — 13 descriptor PIs, folded through the
//!     multi-chunk PI sponge (the ≤4-PI blocker is CLOSED at HEAD;
//!     `custom_leaf_adapter::incircuit_custom_pi_commitment` chains 4-PI chunks).
//!   * The Nomad floor: `balance ≠ 0` (an unconditional inverse gate
//!     `balance·bal_inv − 1 == 0`) and `balance < 2^30` (30 boolean bit columns +
//!     recomposition — the DECO `AMOUNT_RANGE_BITS` precedent).
//!   * The holding identity, recomputed through FOUR `Hash4to1`/`Hash2to1` chip
//!     sites ([`mpt_holding_hash_felt`]):
//!     `holding_hash = H2(H2(H4(root[0..4]), H4(root[4..8])), H4(token, holder, slot, balance))`.
//!
//! A prover cannot expose a `holding_hash` that disagrees with the pinned fields:
//! the First-row pins + the chip-recomputed Poseidon2 chain make a mismatch UNSAT
//! AT THE LEAF. The leaf's 13-PI tuple is committed by the in-circuit multi-chunk
//! PI sponge (`prove_custom_leaf_with_commitment`) and `connect`ed to the leg's
//! published `custom_proof_commitment` (IR2 PI 46..53, the 8-felt flag-day exposure) inside the recursion tree
//! a PURE LIGHT CLIENT folds (`ivc_turn_chain::prove_chain_core_rotated`, the
//! `CarrierWitness::Custom` arm).
//!
//! ## What stays OFF-AIR (the named P0 carriers — NEVER present this as full rung 3)
//!
//! The MPT two-tier walk and every keccak256 digest link stay OFF-AIR,
//! executor-verified named carriers (the deployed DECO posture): the executor runs
//! the REAL `verify_erc20_holding` (`eth-lightclient/src/evm.rs:167`), crypto
//! included, before the turn is accepted, and this leaf's PI commitment binds the
//! same tuple into the turn hash. The `state_root`'s FINALITY (the Eth
//! sync-committee BLS check) stays rung-2 (`verify_erc20_holding_finalized`).
//! P1 folds the walk rules (`verifyRules`); P2 (the TID_KECCAK chip) closes the
//! keccak links in-AIR — the pilot doc's §2 ladder.

use std::collections::HashMap;

use dregg_circuit::dsl::circuit::{
    BoundaryDef, BoundaryRow, CellProgram, CircuitDescriptor, ColumnDef, ColumnKind,
    ConstraintExpr, PolyTerm,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::poseidon2::{hash_2_to_1, hash_4_to_1};

use crate::joint_turn_aggregation::CustomWitnessBundle;

// ---- Base trace columns. ----
/// Base of the 8 PI-pinned `state_root` limb columns (cols 0..8).
pub const COL_ROOT_BASE: usize = 0;
/// The ERC-20 token contract felt, PI-pinned.
pub const COL_TOKEN: usize = 8;
/// The holder address felt, PI-pinned.
pub const COL_HOLDER: usize = 9;
/// The storage slot felt (the EIP-1186 mapping slot), PI-pinned.
pub const COL_SLOT: usize = 10;
/// The held balance felt, PI-pinned (the zero floor + range apply to it).
pub const COL_BALANCE: usize = 11;
/// The balance inverse witness (`balance·bal_inv == 1` — the nonzero floor).
pub const COL_BAL_INV: usize = 12;
/// `rd1 = hash_4_to_1(root[0..4])` (chip-recomputed).
pub const COL_RD1: usize = 13;
/// `rd2 = hash_4_to_1(root[4..8])` (chip-recomputed).
pub const COL_RD2: usize = 14;
/// `root_digest = hash_2_to_1(rd1, rd2)` (chip-recomputed).
pub const COL_ROOT_DIGEST: usize = 15;
/// `acct = hash_4_to_1(token, holder, slot, balance)` (chip-recomputed).
pub const COL_ACCT: usize = 16;
/// The holding identity `holding_hash = hash_2_to_1(root_digest, acct)`, PI-pinned.
pub const COL_HOLDING_HASH: usize = 17;
/// Base of the [`BALANCE_RANGE_BITS`] boolean bit columns decomposing `balance`.
pub const RANGE_BASE: usize = 18;

/// The balance range bit-width: `balance ∈ [0, 2^30)` (with `balance ≠ 0` enforced
/// separately by the inverse gate) — the single-felt umem/DECO amount-limb precedent.
pub const BALANCE_RANGE_BITS: usize = 30;

/// The base trace width (fields + inverse + 5 digests + the range bits).
pub const MPT_HOLDING_BASE_WIDTH: usize = RANGE_BASE + BALANCE_RANGE_BITS;

/// The descriptor PI tuple width: `[root0..root7, token, holder, slot, balance,
/// holding_hash]` — 13 felts, the plan's 12–16-felt natural tuple, NO pre-hash digest.
pub const MPT_HOLDING_PI_LEN: usize = 13;

/// The PI lane of the holding identity (the last lane).
pub const MPT_HOLDING_HASH_PI: usize = 12;

/// The trace row count the pilot proves over (a small power of two; every row is a
/// firing row, the First-row pins bind row 0 — the DECO/custom-demo shape).
pub const MPT_HOLDING_ROWS: usize = 4;

/// The `vk_hash` KAT for [`mpt_holding_program`] (BLAKE3 of the postcard-serialized
/// descriptor, `CellProgram::compute_vk_hash`). Pinned so descriptor drift is a hash
/// mismatch, never a silent divergence (the pilot doc's §3 discipline). Re-derive
/// with `mpt_holding_program().vk_hash` if the descriptor is DELIBERATELY revised.
pub const MPT_HOLDING_VK_HASH_HEX: &str =
    "1169e0137298b5b5f9f0028b06d79f5e881cbcc572f52697f7567f657fc7c161";

/// The HOST-side holding identity — the same Poseidon2 chain the leaf's four chip
/// sites recompute in-AIR:
/// `H2(H2(H4(root[0..4]), H4(root[4..8])), H4(token, holder, slot, balance))`.
pub fn mpt_holding_hash_felt(
    state_root: &[BabyBear; 8],
    token: BabyBear,
    holder: BabyBear,
    slot: BabyBear,
    balance: BabyBear,
) -> BabyBear {
    let rd1 = hash_4_to_1(&[state_root[0], state_root[1], state_root[2], state_root[3]]);
    let rd2 = hash_4_to_1(&[state_root[4], state_root[5], state_root[6], state_root[7]]);
    let root_digest = hash_2_to_1(rd1, rd2);
    let acct = hash_4_to_1(&[token, holder, slot, balance]);
    hash_2_to_1(root_digest, acct)
}

/// Build the MPT holding-commitment `CellProgram` (P0). Registered in the host
/// [`dregg_circuit::dsl::circuit::ProgramRegistry`] under its `vk_hash`
/// ([`MPT_HOLDING_VK_HASH_HEX`]); an unknown program fails closed
/// (`custom_proof_bind::ProofBindError::UnknownProgram`).
pub fn mpt_holding_program() -> CellProgram {
    let p_minus_1 = BabyBear::new(BABYBEAR_P - 1);

    let mut columns: Vec<ColumnDef> = Vec::with_capacity(MPT_HOLDING_BASE_WIDTH);
    for i in 0..8 {
        columns.push(ColumnDef {
            name: format!("root{i}"),
            index: COL_ROOT_BASE + i,
            kind: ColumnKind::Value,
        });
    }
    for (name, index) in [
        ("token", COL_TOKEN),
        ("holder", COL_HOLDER),
        ("slot", COL_SLOT),
        ("balance", COL_BALANCE),
        ("bal_inv", COL_BAL_INV),
        ("rd1", COL_RD1),
        ("rd2", COL_RD2),
        ("root_digest", COL_ROOT_DIGEST),
        ("acct", COL_ACCT),
        ("holding_hash", COL_HOLDING_HASH),
    ] {
        columns.push(ColumnDef {
            name: name.to_string(),
            index,
            kind: ColumnKind::Value,
        });
    }
    for i in 0..BALANCE_RANGE_BITS {
        columns.push(ColumnDef {
            name: format!("bit{i}"),
            index: RANGE_BASE + i,
            kind: ColumnKind::Binary,
        });
    }

    let mut constraints: Vec<ConstraintExpr> = Vec::new();

    // The holding-identity chip chain (4×Hash4to1/Hash2to1 → TID_P2 sites when lowered).
    constraints.push(ConstraintExpr::Hash4to1 {
        output_col: COL_RD1,
        input_cols: [
            COL_ROOT_BASE,
            COL_ROOT_BASE + 1,
            COL_ROOT_BASE + 2,
            COL_ROOT_BASE + 3,
        ],
    });
    constraints.push(ConstraintExpr::Hash4to1 {
        output_col: COL_RD2,
        input_cols: [
            COL_ROOT_BASE + 4,
            COL_ROOT_BASE + 5,
            COL_ROOT_BASE + 6,
            COL_ROOT_BASE + 7,
        ],
    });
    constraints.push(ConstraintExpr::Hash2to1 {
        output_col: COL_ROOT_DIGEST,
        input_col_a: COL_RD1,
        input_col_b: COL_RD2,
    });
    constraints.push(ConstraintExpr::Hash4to1 {
        output_col: COL_ACCT,
        input_cols: [COL_TOKEN, COL_HOLDER, COL_SLOT, COL_BALANCE],
    });
    constraints.push(ConstraintExpr::Hash2to1 {
        output_col: COL_HOLDING_HASH,
        input_col_a: COL_ROOT_DIGEST,
        input_col_b: COL_ACCT,
    });

    // The nonzero floor: `balance·bal_inv − 1 == 0` (unconditional — every row).
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![COL_BALANCE, COL_BAL_INV],
            },
            PolyTerm {
                coeff: p_minus_1,
                col_indices: vec![],
            },
        ],
    });

    // The balance range: 30 boolean bits + the recomposition `Σ bitᵢ·2^i − balance == 0`.
    let mut recompose: Vec<PolyTerm> = Vec::with_capacity(BALANCE_RANGE_BITS + 1);
    for i in 0..BALANCE_RANGE_BITS {
        constraints.push(ConstraintExpr::Binary {
            col: RANGE_BASE + i,
        });
        recompose.push(PolyTerm {
            coeff: BabyBear::new(1u32 << i),
            col_indices: vec![RANGE_BASE + i],
        });
    }
    recompose.push(PolyTerm {
        coeff: p_minus_1,
        col_indices: vec![COL_BALANCE],
    });
    constraints.push(ConstraintExpr::Polynomial { terms: recompose });

    // First-row PI pins: each pinned field ↔ its descriptor PI (the boundary form —
    // graduates to the row-tagged IR-v2 `PiBinding{First}` in `cellprogram_to_descriptor2`).
    let mut boundaries: Vec<BoundaryDef> = Vec::with_capacity(MPT_HOLDING_PI_LEN);
    for i in 0..8 {
        boundaries.push(BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: COL_ROOT_BASE + i,
            pi_index: i,
        });
    }
    for (col, pi) in [
        (COL_TOKEN, 8),
        (COL_HOLDER, 9),
        (COL_SLOT, 10),
        (COL_BALANCE, 11),
        (COL_HOLDING_HASH, MPT_HOLDING_HASH_PI),
    ] {
        boundaries.push(BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col,
            pi_index: pi,
        });
    }

    let descriptor = CircuitDescriptor {
        name: "dregg-mpt-holding-v1".to_string(),
        trace_width: MPT_HOLDING_BASE_WIDTH,
        max_degree: 2,
        columns,
        constraints,
        boundaries,
        public_input_count: MPT_HOLDING_PI_LEN,
        lookup_tables: vec![],
    };
    CellProgram::new(descriptor, 1)
}

/// The felt-domain witness the P0 leaf proves over — the EIP-1186 holding tuple the
/// rung-2 executor verified (every field the SAME felt the producer publishes).
#[derive(Clone, Copy, Debug)]
pub struct MptHoldingWitness {
    /// The 8-limb Eth `state_root` the inclusion was verified under (trusted-state PI;
    /// its FINALITY stays rung-2 — `verify_erc20_holding_finalized`).
    pub state_root: [BabyBear; 8],
    /// The ERC-20 token contract felt.
    pub token: BabyBear,
    /// The holder address felt.
    pub holder: BabyBear,
    /// The storage slot felt.
    pub slot: BabyBear,
    /// The held balance (`1 ≤ balance < 2^30`).
    pub balance: BabyBear,
}

impl MptHoldingWitness {
    /// The in-AIR-recomputed holding identity over this witness's fields.
    pub fn holding_hash(&self) -> BabyBear {
        mpt_holding_hash_felt(
            &self.state_root,
            self.token,
            self.holder,
            self.slot,
            self.balance,
        )
    }

    /// The HONEST 13-slot descriptor PI tuple:
    /// `[root0..root7, token, holder, slot, balance, holding_hash]`.
    pub fn public_inputs(&self) -> Vec<BabyBear> {
        let mut pis: Vec<BabyBear> = self.state_root.to_vec();
        pis.push(self.token);
        pis.push(self.holder);
        pis.push(self.slot);
        pis.push(self.balance);
        pis.push(self.holding_hash());
        debug_assert_eq!(pis.len(), MPT_HOLDING_PI_LEN);
        pis
    }

    /// The named trace-column witness ([`CellProgram::generate_trace`] input):
    /// [`MPT_HOLDING_ROWS`] identical rows, digests host-recomputed, `bal_inv` the
    /// genuine inverse (ZERO for a zero balance — the floor gate then has no
    /// satisfying row, the fail-closed pole), bits the balance decomposition.
    pub fn witness_values(&self) -> (HashMap<String, Vec<BabyBear>>, usize) {
        let rows = MPT_HOLDING_ROWS;
        let rd1 = hash_4_to_1(&[
            self.state_root[0],
            self.state_root[1],
            self.state_root[2],
            self.state_root[3],
        ]);
        let rd2 = hash_4_to_1(&[
            self.state_root[4],
            self.state_root[5],
            self.state_root[6],
            self.state_root[7],
        ]);
        let root_digest = hash_2_to_1(rd1, rd2);
        let acct = hash_4_to_1(&[self.token, self.holder, self.slot, self.balance]);
        let holding_hash = hash_2_to_1(root_digest, acct);
        debug_assert_eq!(holding_hash, self.holding_hash());

        let mut w: HashMap<String, Vec<BabyBear>> = HashMap::new();
        let mut put = |name: &str, v: BabyBear| {
            w.insert(name.to_string(), vec![v; rows]);
        };
        for (i, &limb) in self.state_root.iter().enumerate() {
            put(&format!("root{i}"), limb);
        }
        put("token", self.token);
        put("holder", self.holder);
        put("slot", self.slot);
        put("balance", self.balance);
        put("bal_inv", self.balance.inverse().unwrap_or(BabyBear::ZERO));
        put("rd1", rd1);
        put("rd2", rd2);
        put("root_digest", root_digest);
        put("acct", acct);
        put("holding_hash", holding_hash);
        let bal = self.balance.as_u32();
        for i in 0..BALANCE_RANGE_BITS {
            put(&format!("bit{i}"), BabyBear::new((bal >> i) & 1));
        }
        (w, rows)
    }

    /// The prover-side [`CustomWitnessBundle`] for the deployed
    /// `CarrierWitness::Custom` arm (`RotatedParticipantLeg::with_custom_witness` /
    /// `mint_custom_wide_from_block_witnesses`) — the Some-witness rung: re-provable,
    /// foldable, NEVER serialized.
    pub fn bundle(&self) -> CustomWitnessBundle {
        let (witness_values, num_rows) = self.witness_values();
        CustomWitnessBundle {
            program: mpt_holding_program(),
            witness_values,
            num_rows,
            public_inputs: self.public_inputs(),
        }
    }
}

// The fast structural tests (vk KAT, registry round-trip, adapter lowering, identity
// composition, trace generation) live in `circuit-prove/tests/mpt_holding_fold_pilot.rs`
// alongside the fold teeth, so the whole pilot surface runs from ONE test target.
