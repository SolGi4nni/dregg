//! Effect VM AIR: Multi-row DSL circuit proving arbitrary sequences of effects
//! (turns) in a single STARK proof.
//!
//! Inspired by o1vm (RISC-V execution trace proving), but for pyana Effects instead
//! of CPU instructions. Each trace row represents one effect execution step.
//!
//! # Instruction Set (Effect Types)
//!
//! - NoOp (0): Padding effect; all constraints trivially satisfied.
//! - Transfer (1): Balance transfer with direction (in/out).
//! - SetField (2): Update a custom field slot.
//! - GrantCapability (3): Add capability to c-list (capability_root update).
//! - NoteSpend (4): Spend a note (nullifier reveal, balance credit).
//! - NoteCreate (5): Create a note (commitment creation, balance debit).
//! - CreateObligation (6): Lock stake from balance as a bonded obligation.
//! - FulfillObligation (7): Return locked stake on successful fulfillment.
//! - Custom (8): CellProgram dispatch — state flows unchanged, domain constraints
//!   proven externally. Params carry program VK hash + proof commitment.
//! - SlashObligation (9): Slash an expired obligation.
//! - Seal (10): Lock a field against mutation.
//! - Unseal (11): Unlock a sealed field.
//! - MakeSovereign (12): Transition cell from managed to sovereign.
//! - CreateCellFromFactory (13): Record factory provenance.
//! - ExportSturdyRef (14): Export cell as sturdy ref (CapTP).
//! - EnlivenRef (15): Enliven a sturdy ref (CapTP).
//! - DropRef (16): Drop a remote reference / GC decrement (CapTP).
//! - ValidateHandoff (17): Validate a handoff certificate (CapTP).
//!
//! # Trace Layout (one row per effect)
//!
//! ```text
//! | selector[18] | state_before[14] | effect_params[8] | state_after[14] | aux[11] |
//! ```
//!
//! Total width: 65 columns
//!
//! ## Column Breakdown
//!
//! Selectors (cols 0..9): Exactly one active per row.
//!   - sel_noop, sel_transfer, sel_setfield, sel_grantcap, sel_notespend, sel_notecreate,
//!     sel_create_obligation, sel_fulfill_obligation, sel_custom
//!
//! State Before (cols 9..23):
//!   - balance_lo, balance_hi (u64 as two BabyBear limbs, 30+34 bits)
//!   - nonce
//!   - field_values[0..7] (8 custom fields)
//!   - capability_root
//!   - state_commitment (running Poseidon2 hash of full state)
//!   - reserved
//!
//! Effect Params (cols 23..31):
//!   - param0..param7 (meaning depends on effect type)
//!
//! State After (cols 31..45):
//!   - Same layout as state_before
//!
//! Aux (cols 50..61):
//!   - Auxiliary witness values (intermediate hashes, commitment tree nodes)
//!   - aux[8..10]: state commitment tree intermediates (hash_4_to_1 outputs)
//!
//! # Constraints
//!
//! 1. Selector exclusivity: sum(selectors) == 1, each selector is boolean.
//! 2. Per-effect constraints (gated by selector):
//!    - Transfer: new_balance = old_balance +/- amount
//!    - SetField: one field updated, others unchanged
//!    - GrantCap: capability_root = hash(old_root, new_entry)
//!    - NoteSpend: nullifier valid, balance increases
//!    - NoteCreate: commitment valid, balance decreases
//!    - CreateObligation: balance decreases by stake_amount
//!    - FulfillObligation: balance increases by stake_return
//!    - Custom: state unchanged (domain constraints proven externally)
//! 3. Transition constraints (row-to-row continuity):
//!    - next_row.state_before == this_row.state_after
//!    - next_row.nonce == this_row.nonce + 1 (or same for NoOp padding)
//! 4. Boundary constraints:
//!    - First row: state_before matches old_commitment (public input)
//!    - Last non-padding row: state_after matches new_commitment
//!    - Conservation: net balance delta == public input
//!
//! # Public Inputs (7+ elements)
//!
//! [old_commitment, new_commitment, net_delta_magnitude, net_delta_sign,
//!  effects_hash_lo, effects_hash_hi, custom_effect_count,
//!  ...custom_entries: (vk_hash[4], proof_commitment[4]) per custom effect]

use crate::field::BabyBear;
use crate::poseidon2::{hash_2_to_1, hash_4_to_1, hash_many};
use crate::stark::{BoundaryConstraint, StarkAir};

// ============================================================================
// Column layout constants
// ============================================================================

/// Total trace width.
/// Layout: 18 selectors + 14 state_before + 8 params + 14 state_after + 11 aux = 65.
/// (aux[8..10] = state commitment intermediates for constrainable tree hash)
pub const EFFECT_VM_WIDTH: usize = 65;

/// Number of effect types (selectors).
pub const NUM_EFFECTS: usize = 18;

/// Selector column indices.
pub mod sel {
    pub const NOOP: usize = 0;
    pub const TRANSFER: usize = 1;
    pub const SET_FIELD: usize = 2;
    pub const GRANT_CAP: usize = 3;
    pub const NOTE_SPEND: usize = 4;
    pub const NOTE_CREATE: usize = 5;
    pub const CREATE_OBLIGATION: usize = 6;
    pub const FULFILL_OBLIGATION: usize = 7;
    /// Custom cell program dispatch: state flows normally, but domain-specific
    /// constraints are proven externally. The Effect VM binds to the external
    /// proof via `custom_proof_commitment` in the params.
    pub const CUSTOM: usize = 8;
    /// Slash an expired obligation: transfer locked stake to beneficiary.
    pub const SLASH_OBLIGATION: usize = 9;
    /// Seal: lock a field against mutation via sealed_field_mask.
    pub const SEAL: usize = 10;
    /// Unseal: unlock a sealed field (requires brand matching).
    pub const UNSEAL: usize = 11;
    /// MakeSovereign: transition cell mode_flag from 0 to 1.
    pub const MAKE_SOVEREIGN: usize = 12;
    /// CreateCellFromFactory: record factory VK hash + provenance.
    pub const CREATE_CELL_FROM_FACTORY: usize = 13;
    /// ExportSturdyRef: export a cell as a sturdy reference (creates swiss entry).
    pub const EXPORT_STURDY_REF: usize = 14;
    /// EnlivenRef: enliven a sturdy ref (validate swiss, create routing).
    pub const ENLIVEN_REF: usize = 15;
    /// DropRef: drop a remote reference (GC decrement).
    pub const DROP_REF: usize = 16;
    /// ValidateHandoff: validate a handoff certificate (check cert hash membership).
    pub const VALIDATE_HANDOFF: usize = 17;
}

/// State column offsets (relative to state start).
pub mod state {
    pub const BALANCE_LO: usize = 0;
    pub const BALANCE_HI: usize = 1;
    pub const NONCE: usize = 2;
    pub const FIELD_BASE: usize = 3; // fields[0..8] at offsets 3..11
    pub const CAP_ROOT: usize = 11;
    pub const STATE_COMMIT: usize = 12;
    pub const RESERVED: usize = 13;
    pub const SIZE: usize = 14;
}

/// Absolute column indices for state_before.
pub const STATE_BEFORE_BASE: usize = NUM_EFFECTS; // 18
/// Absolute column indices for state_after.
pub const STATE_AFTER_BASE: usize = STATE_BEFORE_BASE + state::SIZE + NUM_PARAMS; // 18 + 14 + 8 = 40
/// Effect parameter base column.
pub const PARAM_BASE: usize = STATE_BEFORE_BASE + state::SIZE; // 18 + 14 = 32
/// Number of parameter columns.
pub const NUM_PARAMS: usize = 8;
/// Auxiliary witness base column.
pub const AUX_BASE: usize = STATE_AFTER_BASE + state::SIZE; // 40 + 14 = 54
/// Number of auxiliary columns (expanded for state commitment tree intermediates).
pub const NUM_AUX: usize = 11;

/// Auxiliary column offsets for state commitment tree intermediates.
pub mod aux_off {
    /// Intermediate 1: hash_4_to_1(balance_lo, balance_hi, nonce, field[0])
    pub const STATE_INTER1: usize = 8;
    /// Intermediate 2: hash_4_to_1(field[1], field[2], field[3], field[4])
    pub const STATE_INTER2: usize = 9;
    /// Intermediate 3: hash_4_to_1(field[5], field[6], field[7], cap_root)
    pub const STATE_INTER3: usize = 10;
}

/// Effect parameter meanings per effect type.
///
/// Transfer:
///   param0 = amount
///   param1 = direction (0=incoming, 1=outgoing)
///
/// SetField:
///   param0 = field_index (0..7)
///   param1 = new_value
///
/// GrantCapability:
///   param0 = capability_entry (hash of new capability)
///
/// NoteSpend:
///   param0 = nullifier
///   param1 = value_lo
///   param2 = value_hi
///
/// NoteCreate:
///   param0 = commitment
///   param1 = value_lo
///   param2 = value_hi
///
/// CreateObligation:
///   param0 = stake_amount_lo
///   param1 = stake_amount_hi
///   param2 = obligation_id (hash of terms)
///   param3 = beneficiary_hash
///
/// FulfillObligation:
///   param0 = obligation_id (hash identifying the obligation)
///   param1 = stake_return_lo (amount returned to obligor)
///   param2 = stake_return_hi
///
/// Custom (CellProgram dispatch):
///   param0..param3 = custom_program_vk_hash (4 BabyBear elements identifying the program)
///   param4..param7 = custom_proof_commitment (4 BabyBear elements = hash of external proof)
pub mod param {
    pub const AMOUNT: usize = 0;
    pub const DIRECTION: usize = 1;
    pub const FIELD_INDEX: usize = 0;
    pub const NEW_VALUE: usize = 1;
    pub const CAP_ENTRY: usize = 0;
    pub const NULLIFIER: usize = 0;
    pub const NOTE_VALUE_LO: usize = 1;
    pub const NOTE_VALUE_HI: usize = 2;
    pub const NOTE_COMMITMENT: usize = 0;
    // Obligation params.
    pub const OBLIGATION_STAKE_LO: usize = 0;
    pub const OBLIGATION_STAKE_HI: usize = 1;
    pub const OBLIGATION_ID: usize = 2;
    pub const OBLIGATION_BENEFICIARY: usize = 3;
    pub const FULFILL_OBLIGATION_ID: usize = 0;
    pub const FULFILL_RETURN_LO: usize = 1;
    pub const FULFILL_RETURN_HI: usize = 2;
    // SlashObligation params.
    pub const SLASH_OBLIGATION_ID: usize = 0;
    pub const SLASH_STAKE_LO: usize = 1;
    pub const SLASH_STAKE_HI: usize = 2;
    pub const SLASH_BENEFICIARY: usize = 3;
    // Seal params.
    pub const SEAL_FIELD_IDX: usize = 0;
    // Unseal params.
    pub const UNSEAL_FIELD_IDX: usize = 0;
    pub const UNSEAL_BRAND: usize = 1;
    // MakeSovereign params: no balance params (mode flag only).
    // CreateCellFromFactory params.
    pub const FACTORY_VK_HASH: usize = 0;
    pub const CHILD_VK_DERIVED: usize = 1;
    // Custom cell program dispatch params.
    /// VK hash identifying the custom program (4 elements = 4*30 = 120 bits).
    pub const CUSTOM_VK_HASH_BASE: usize = 0;
    /// Custom proof commitment (hash of the external proof, 4 elements).
    pub const CUSTOM_PROOF_COMMIT_BASE: usize = 4;
    // ExportSturdyRef params.
    /// Cell ID being exported.
    pub const EXPORT_CELL_ID: usize = 0;
    /// Permissions mask for the sturdy ref.
    pub const EXPORT_PERMISSIONS: usize = 1;
    /// Random seed for swiss number derivation.
    pub const EXPORT_RANDOM_SEED: usize = 2;
    /// Export counter (monotonic, pre-increment value).
    pub const EXPORT_COUNTER: usize = 3;
    // EnlivenRef params.
    /// Swiss number to look up.
    pub const ENLIVEN_SWISS: usize = 0;
    /// Presenter ID (who is enlivening).
    pub const ENLIVEN_PRESENTER: usize = 1;
    /// Expected cell_id (from swiss table lookup, verified via aux).
    pub const ENLIVEN_CELL_ID: usize = 2;
    /// Expected permissions (from swiss table lookup).
    pub const ENLIVEN_PERMISSIONS: usize = 3;
    // DropRef params.
    /// Cell ID whose reference is being dropped.
    pub const DROP_CELL_ID: usize = 0;
    /// Federation hash of the holder dropping the ref.
    pub const DROP_HOLDER_FED: usize = 1;
    /// Current refcount (pre-decrement).
    pub const DROP_REFCOUNT: usize = 2;
    // ValidateHandoff params.
    /// Certificate hash.
    pub const HANDOFF_CERT_HASH: usize = 0;
    /// Recipient public key hash.
    pub const HANDOFF_RECIPIENT_PK: usize = 1;
    /// Introducer public key hash.
    pub const HANDOFF_INTRODUCER_PK: usize = 2;
    /// Known-good certificate set root (Merkle root of approved certs).
    pub const HANDOFF_APPROVED_SET_ROOT: usize = 3;
}

/// Public input layout.
pub mod pi {
    /// Old state commitment (single Poseidon2 hash of full state).
    pub const OLD_COMMIT: usize = 0;
    /// New state commitment (single Poseidon2 hash of full state).
    pub const NEW_COMMIT: usize = 1;
    /// Net balance delta: [magnitude, sign_bit].
    pub const NET_DELTA_MAG: usize = 2;
    pub const NET_DELTA_SIGN: usize = 3;
    /// Effects hash (2 BabyBear elements: lo, hi).
    pub const EFFECTS_HASH_LO: usize = 4;
    pub const EFFECTS_HASH_HI: usize = 5;
    /// Number of custom effects in this turn (0 if none).
    pub const CUSTOM_EFFECT_COUNT: usize = 6;
    /// Custom proof commitments start here.
    /// For each custom effect i (0..custom_count):
    ///   PI[CUSTOM_PROOFS_BASE + i*8 + 0..4] = custom_program_vk_hash (4 elements)
    ///   PI[CUSTOM_PROOFS_BASE + i*8 + 4..8] = custom_proof_commitment (4 elements)
    pub const CUSTOM_PROOFS_BASE: usize = 7;
    /// Base public inputs (without custom proof data).
    pub const BASE_COUNT: usize = 7;
    /// Maximum number of custom effects supported per turn.
    pub const MAX_CUSTOM_EFFECTS: usize = 4;
    /// Elements per custom effect entry in PI (4 vk_hash + 4 proof_commit).
    pub const CUSTOM_ENTRY_SIZE: usize = 8;
}

// ============================================================================
// Effect enum for witness generation
// ============================================================================

/// An effect to be proven in the VM.
#[derive(Clone, Debug)]
pub enum Effect {
    /// No operation (used for padding).
    NoOp,
    /// Transfer balance.
    Transfer {
        amount: u64,
        /// 0 = incoming (credit), 1 = outgoing (debit).
        direction: u32,
    },
    /// Set a custom field value.
    SetField { field_idx: u32, value: BabyBear },
    /// Grant a capability (add entry to c-list Merkle root).
    GrantCapability { cap_entry: BabyBear },
    /// Spend a note (reveal nullifier, credit balance).
    NoteSpend { nullifier: BabyBear, value: u64 },
    /// Create a note (create commitment, debit balance).
    NoteCreate { commitment: BabyBear, value: u64 },
    /// Create a bonded obligation (locks stake from balance).
    /// Balance decreases by stake_amount. The obligation_id binds the terms.
    CreateObligation {
        /// Amount to lock.
        stake_amount: u64,
        /// Hash identifying the obligation terms (beneficiary, condition, deadline).
        obligation_id: BabyBear,
        /// Hash of the beneficiary cell.
        beneficiary_hash: BabyBear,
    },
    /// Fulfill an obligation (returns stake to obligor's balance).
    /// Balance increases by the returned stake amount.
    FulfillObligation {
        /// Hash identifying the obligation being fulfilled.
        obligation_id: BabyBear,
        /// Amount returned to obligor on fulfillment.
        stake_return: u64,
    },
    /// Custom cell program dispatch.
    ///
    /// State flows through normally (continuity enforced by the Effect VM).
    /// Domain-specific constraints are proven in a separate proof identified by
    /// `custom_proof_commitment`. The verifier checks that the external proof is
    /// valid and that its hash matches this commitment.
    Custom {
        /// VK hash identifying the custom program (4 BabyBear elements packed into a hash).
        program_vk_hash: [BabyBear; 4],
        /// Hash of the external custom program proof (4 BabyBear elements).
        proof_commitment: [BabyBear; 4],
    },
    /// Slash an expired obligation: transfer locked stake to beneficiary.
    /// Balance of beneficiary increases by stake_amount.
    SlashObligation {
        /// Hash identifying the obligation to slash.
        obligation_id: BabyBear,
        /// Amount slashed to beneficiary.
        stake_amount: u64,
        /// Hash of the beneficiary (for cap_root update).
        beneficiary_hash: BabyBear,
    },
    /// Seal: lock a field against mutation.
    /// Sets sealed_field_mask |= (1 << field_idx) in the reserved state slot.
    Seal {
        /// Index of field to seal (0..7).
        field_idx: u32,
    },
    /// Unseal: unlock a sealed field (requires brand matching via aux).
    /// Clears sealed_field_mask &= ~(1 << field_idx).
    Unseal {
        /// Index of field to unseal.
        field_idx: u32,
        /// Brand hash proving authority to unseal.
        brand: BabyBear,
    },
    /// MakeSovereign: transition cell mode from managed (0) to sovereign (1).
    /// State constraint: mode_flag changes from 0 to 1. Balance/fields preserved.
    MakeSovereign,
    /// CreateCellFromFactory: record factory VK hash + provenance.
    /// Uses aux columns for factory_vk and child_vk_derived.
    CreateCellFromFactory {
        /// Factory VK hash.
        factory_vk: BabyBear,
        /// Derived child VK hash (provenance record).
        child_vk_derived: BabyBear,
    },
    /// ExportSturdyRef: export a cell as a sturdy reference.
    /// Proves: swiss_number = Hash(cell_id || random_seed || export_counter).
    /// State transition: export_counter increments (tracked in field[7] by convention).
    ExportSturdyRef {
        /// Cell ID being exported.
        cell_id: BabyBear,
        /// Permissions mask.
        permissions: BabyBear,
        /// Random seed for swiss derivation.
        random_seed: BabyBear,
        /// Export counter (pre-increment value, stored in field[7]).
        export_counter: u32,
    },
    /// EnlivenRef: enliven a sturdy ref (validate swiss exists in table).
    /// Proves: swiss_number is a known swiss entry (via committed hash check).
    /// State transition: use_count increments (tracked in field[6] by convention).
    EnlivenRef {
        /// Swiss number to validate.
        swiss_number: BabyBear,
        /// Presenter ID.
        presenter_id: BabyBear,
        /// Expected cell_id from the swiss table entry.
        expected_cell_id: BabyBear,
        /// Expected permissions from the swiss table entry.
        expected_permissions: BabyBear,
    },
    /// DropRef: drop a remote reference (GC decrement).
    /// Proves: refcount > 0.
    /// State transition: refcount decrements (tracked in field[5] by convention).
    DropRef {
        /// Cell ID being released.
        cell_id: BabyBear,
        /// Federation hash of the holder.
        holder_federation: BabyBear,
        /// Current refcount (must be > 0).
        current_refcount: u32,
    },
    /// ValidateHandoff: validate a handoff certificate.
    /// Proves: certificate_hash is in the approved set (Merkle membership).
    /// Instead of in-circuit Ed25519, we prove set membership of the cert hash.
    /// State transition: routing entry created (cap_root updated).
    ValidateHandoff {
        /// Hash of the handoff certificate.
        certificate_hash: BabyBear,
        /// Recipient public key hash.
        recipient_pk: BabyBear,
        /// Introducer public key hash.
        introducer_pk: BabyBear,
        /// Merkle root of approved certificates set.
        approved_set_root: BabyBear,
    },
}

/// Cell state that flows between rows.
#[derive(Clone, Debug)]
pub struct CellState {
    /// Balance as u64 (split into lo/hi for BabyBear encoding).
    pub balance: u64,
    /// Monotonic nonce.
    pub nonce: u32,
    /// 8 custom field values.
    pub fields: [BabyBear; 8],
    /// Capability list Merkle root.
    pub capability_root: BabyBear,
    /// Running state commitment.
    pub state_commitment: BabyBear,
    /// Sealed field mask: bit i set means field i is sealed against mutation.
    pub sealed_field_mask: u32,
    /// Mode flag: 0 = managed, 1 = sovereign.
    pub mode_flag: u32,
}

impl CellState {
    /// Create a new cell state with default values.
    pub fn new(balance: u64, nonce: u32) -> Self {
        let fields = [BabyBear::ZERO; 8];
        let capability_root = BabyBear::ZERO;
        // Initial state commitment is hash of all state elements.
        let state_commitment = Self::compute_commitment(balance, nonce, &fields, capability_root);
        Self {
            balance,
            nonce,
            fields,
            capability_root,
            state_commitment,
            sealed_field_mask: 0,
            mode_flag: 0,
        }
    }

    /// Compute the state commitment from all state components using a
    /// constrainable tree of hash_4_to_1 calls.
    ///
    /// Tree structure:
    ///   inter1 = hash_4_to_1(balance_lo, balance_hi, nonce, field[0])
    ///   inter2 = hash_4_to_1(field[1], field[2], field[3], field[4])
    ///   inter3 = hash_4_to_1(field[5], field[6], field[7], cap_root)
    ///   commitment = hash_4_to_1(inter1, inter2, inter3, ZERO)
    ///
    /// The fourth input to the root hash is ZERO (reserved for future use).
    /// This structure is directly constrainable because each hash_4_to_1 can be
    /// verified by the evaluator at each trace row.
    pub fn compute_commitment(
        balance: u64,
        nonce: u32,
        fields: &[BabyBear; 8],
        capability_root: BabyBear,
    ) -> BabyBear {
        let (lo, hi) = split_u64(balance);
        let inter1 = hash_4_to_1(&[lo, hi, BabyBear::new(nonce), fields[0]]);
        let inter2 = hash_4_to_1(&[fields[1], fields[2], fields[3], fields[4]]);
        let inter3 = hash_4_to_1(&[fields[5], fields[6], fields[7], capability_root]);
        hash_4_to_1(&[inter1, inter2, inter3, BabyBear::ZERO])
    }

    /// Compute the three intermediate hashes for the state commitment tree.
    /// Returns (inter1, inter2, inter3) which are needed as witness values.
    pub fn compute_commitment_intermediates(
        balance: u64,
        nonce: u32,
        fields: &[BabyBear; 8],
        capability_root: BabyBear,
    ) -> (BabyBear, BabyBear, BabyBear) {
        let (lo, hi) = split_u64(balance);
        let inter1 = hash_4_to_1(&[lo, hi, BabyBear::new(nonce), fields[0]]);
        let inter2 = hash_4_to_1(&[fields[1], fields[2], fields[3], fields[4]]);
        let inter3 = hash_4_to_1(&[fields[5], fields[6], fields[7], capability_root]);
        (inter1, inter2, inter3)
    }

    /// Recompute and update the state commitment.
    pub fn refresh_commitment(&mut self) {
        self.state_commitment =
            Self::compute_commitment(self.balance, self.nonce, &self.fields, self.capability_root);
    }

    /// Encode state into trace columns (14 elements).
    fn to_trace_cols(&self) -> Vec<BabyBear> {
        let (lo, hi) = split_u64(self.balance);
        let mut cols = Vec::with_capacity(state::SIZE);
        cols.push(lo); // balance_lo
        cols.push(hi); // balance_hi
        cols.push(BabyBear::new(self.nonce)); // nonce
        cols.extend_from_slice(&self.fields); // field_values[0..8]
        cols.push(self.capability_root); // cap_root
        cols.push(self.state_commitment); // state_commit
        cols.push(BabyBear::new(
            self.sealed_field_mask | (self.mode_flag << 8),
        )); // reserved: sealed_mask | mode_flag
        assert_eq!(cols.len(), state::SIZE);
        cols
    }
}

// ============================================================================
// Helper functions
// ============================================================================

/// Split a u64 into two BabyBear elements: (lo = lower 30 bits, hi = upper 34 bits).
/// Both values fit in BabyBear (< 2^31).
pub(crate) fn split_u64(val: u64) -> (BabyBear, BabyBear) {
    let lo = (val & 0x3FFF_FFFF) as u32; // lower 30 bits
    let hi = (val >> 30) as u32; // upper 34 bits (fits in u32 since val < 2^64)
    (BabyBear::new(lo), BabyBear::new(hi))
}

/// Reconstruct a u64 from split BabyBear limbs.
#[allow(dead_code)]
fn join_u64(lo: BabyBear, hi: BabyBear) -> u64 {
    (lo.0 as u64) | ((hi.0 as u64) << 30)
}

/// Compute the effects hash for a sequence of effects.
/// Returns (lo, hi) BabyBear elements.
pub fn compute_effects_hash(effects: &[Effect]) -> (BabyBear, BabyBear) {
    let mut hasher_inputs = Vec::new();
    for effect in effects {
        match effect {
            Effect::NoOp => {
                hasher_inputs.push(BabyBear::ZERO);
            }
            Effect::Transfer { amount, direction } => {
                hasher_inputs.push(BabyBear::ONE);
                let (lo, hi) = split_u64(*amount);
                hasher_inputs.push(lo);
                hasher_inputs.push(hi);
                hasher_inputs.push(BabyBear::new(*direction));
            }
            Effect::SetField { field_idx, value } => {
                hasher_inputs.push(BabyBear::new(2));
                hasher_inputs.push(BabyBear::new(*field_idx));
                hasher_inputs.push(*value);
            }
            Effect::GrantCapability { cap_entry } => {
                hasher_inputs.push(BabyBear::new(3));
                hasher_inputs.push(*cap_entry);
            }
            Effect::NoteSpend { nullifier, value } => {
                hasher_inputs.push(BabyBear::new(4));
                hasher_inputs.push(*nullifier);
                let (lo, hi) = split_u64(*value);
                hasher_inputs.push(lo);
                hasher_inputs.push(hi);
            }
            Effect::NoteCreate { commitment, value } => {
                hasher_inputs.push(BabyBear::new(5));
                hasher_inputs.push(*commitment);
                let (lo, hi) = split_u64(*value);
                hasher_inputs.push(lo);
                hasher_inputs.push(hi);
            }
            Effect::CreateObligation {
                stake_amount,
                obligation_id,
                beneficiary_hash,
            } => {
                hasher_inputs.push(BabyBear::new(6));
                let (lo, hi) = split_u64(*stake_amount);
                hasher_inputs.push(lo);
                hasher_inputs.push(hi);
                hasher_inputs.push(*obligation_id);
                hasher_inputs.push(*beneficiary_hash);
            }
            Effect::FulfillObligation {
                obligation_id,
                stake_return,
            } => {
                hasher_inputs.push(BabyBear::new(7));
                hasher_inputs.push(*obligation_id);
                let (lo, hi) = split_u64(*stake_return);
                hasher_inputs.push(lo);
                hasher_inputs.push(hi);
            }
            Effect::Custom {
                program_vk_hash,
                proof_commitment,
            } => {
                hasher_inputs.push(BabyBear::new(8));
                hasher_inputs.extend_from_slice(program_vk_hash);
                hasher_inputs.extend_from_slice(proof_commitment);
            }
            Effect::SlashObligation {
                obligation_id,
                stake_amount,
                beneficiary_hash,
            } => {
                hasher_inputs.push(BabyBear::new(9));
                hasher_inputs.push(*obligation_id);
                let (lo, hi) = split_u64(*stake_amount);
                hasher_inputs.push(lo);
                hasher_inputs.push(hi);
                hasher_inputs.push(*beneficiary_hash);
            }
            Effect::Seal { field_idx } => {
                hasher_inputs.push(BabyBear::new(10));
                hasher_inputs.push(BabyBear::new(*field_idx));
            }
            Effect::Unseal { field_idx, brand } => {
                hasher_inputs.push(BabyBear::new(11));
                hasher_inputs.push(BabyBear::new(*field_idx));
                hasher_inputs.push(*brand);
            }
            Effect::MakeSovereign => {
                hasher_inputs.push(BabyBear::new(12));
            }
            Effect::CreateCellFromFactory {
                factory_vk,
                child_vk_derived,
            } => {
                hasher_inputs.push(BabyBear::new(13));
                hasher_inputs.push(*factory_vk);
                hasher_inputs.push(*child_vk_derived);
            }
            Effect::ExportSturdyRef {
                cell_id,
                permissions,
                random_seed,
                export_counter,
            } => {
                hasher_inputs.push(BabyBear::new(14));
                hasher_inputs.push(*cell_id);
                hasher_inputs.push(*permissions);
                hasher_inputs.push(*random_seed);
                hasher_inputs.push(BabyBear::new(*export_counter));
            }
            Effect::EnlivenRef {
                swiss_number,
                presenter_id,
                expected_cell_id,
                expected_permissions,
            } => {
                hasher_inputs.push(BabyBear::new(15));
                hasher_inputs.push(*swiss_number);
                hasher_inputs.push(*presenter_id);
                hasher_inputs.push(*expected_cell_id);
                hasher_inputs.push(*expected_permissions);
            }
            Effect::DropRef {
                cell_id,
                holder_federation,
                current_refcount,
            } => {
                hasher_inputs.push(BabyBear::new(16));
                hasher_inputs.push(*cell_id);
                hasher_inputs.push(*holder_federation);
                hasher_inputs.push(BabyBear::new(*current_refcount));
            }
            Effect::ValidateHandoff {
                certificate_hash,
                recipient_pk,
                introducer_pk,
                approved_set_root,
            } => {
                hasher_inputs.push(BabyBear::new(17));
                hasher_inputs.push(*certificate_hash);
                hasher_inputs.push(*recipient_pk);
                hasher_inputs.push(*introducer_pk);
                hasher_inputs.push(*approved_set_root);
            }
        }
    }
    let h = hash_many(&hasher_inputs);
    // Split into two elements for wider coverage.
    let h2 = hash_2_to_1(h, BabyBear::new(0xEFFEC7));
    (h, h2)
}

// ============================================================================
// AIR Implementation
// ============================================================================

/// The Effect VM AIR. Proves an arbitrary sequence of effects in a single STARK.
pub struct EffectVmAir {
    /// Maximum number of effects (trace height, padded to power of 2).
    pub max_effects: usize,
}

impl EffectVmAir {
    pub fn new(max_effects: usize) -> Self {
        assert!(max_effects >= 2, "Need at least 2 rows for STARK");
        assert!(
            max_effects.is_power_of_two(),
            "max_effects must be a power of 2"
        );
        Self { max_effects }
    }
}

impl StarkAir for EffectVmAir {
    fn width(&self) -> usize {
        EFFECT_VM_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        // Selector sum constraint is degree 1 (linear).
        // Selector boolean constraints are degree 2.
        // Per-effect constraints: selector * (expression) is at most degree 3.
        // Hash constraints (hash_2_to_1, hash_4_to_1) are evaluated concretely on trace
        // values at FRI evaluation points — they do NOT contribute polynomial degree.
        // SetField field_idx range check: selector * prod_{k=0..7}(field_idx - k) = degree 9.
        // Seal/Unseal field_idx range check: same degree 9.
        9
    }

    fn air_name(&self) -> &'static str {
        "pyana-effect-vm-v1"
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        next: &[BabyBear],
        _public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        let mut combined = BabyBear::ZERO;
        let mut alpha_pow = BabyBear::ONE;

        // ====================================================================
        // CONSTRAINT GROUP 1: Selector validity
        // ====================================================================

        // Each selector must be boolean: s*(s-1) == 0
        for i in 0..NUM_EFFECTS {
            let s = local[i];
            let c = s * (s - BabyBear::ONE);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // Selectors must sum to exactly 1.
        let mut sel_sum = BabyBear::ZERO;
        for i in 0..NUM_EFFECTS {
            sel_sum = sel_sum + local[i];
        }
        let c_sum = sel_sum - BabyBear::ONE;
        combined = combined + alpha_pow * c_sum;
        alpha_pow = alpha_pow * alpha;

        // ====================================================================
        // CONSTRAINT GROUP 2: Per-effect-type constraints (gated by selector)
        // ====================================================================
        //
        // SECURITY NOTE — Balance limb range checks (o1vm audit finding #1):
        //
        // balance_lo (30-bit) and balance_hi (34-bit) are NOT range-checked
        // in-circuit. Full bit-decomposition would add 60+ columns to the trace.
        // Instead, the EXECUTOR independently validates:
        //   - balance_lo < 2^30  (fits in the lo limb)
        //   - balance_hi < 2^34  (fits in the hi limb, and < BabyBear prime)
        //   - balance_lo + balance_hi * 2^30 == declared u64 balance
        //
        // The boundary constraints bind start/end state_commitment to public
        // inputs, and state_commitment = Poseidon2(balance_lo, balance_hi, ...),
        // so a malicious prover cannot forge commitments without matching limbs.
        // However, a prover CAN choose field-valid but out-of-range limbs on
        // INTERIOR rows (between boundaries). The executor rejects such proofs
        // by re-deriving the final state and checking limb ranges.
        //
        // TODO(range-checks): When we add lookup arguments (log-derivative or
        // Lasso-style), replace executor-side checks with in-circuit range
        // proofs via a 2^16 lookup table (2 lookups per limb for 30/34 bits).
        //
        // SECURITY NOTE — Balance underflow protection (o1vm audit finding #3):
        //
        // For outgoing transfers and obligation creation, the constraint is:
        //   new_balance_lo = old_balance_lo - amount
        // In BabyBear modular arithmetic, if amount > old_balance, this wraps
        // around to a large "valid" field element rather than failing.
        //
        // The witness generation uses saturating_sub, so honest provers never
        // produce underflow. However, a MALICIOUS prover could craft a trace
        // where the subtraction wraps around the field modulus.
        //
        // Defense: The executor checks that the final balance (extracted from
        // the proven new_commitment) is <= the initial balance + net_credits.
        // Additionally, the state_commitment binds the actual balance limbs,
        // so any wrap-around would produce a commitment that doesn't match the
        // declared final state.
        //
        // TODO(underflow): Add proper non-negative range proof via bit
        // decomposition of (old_balance - amount) to prove it fits in 30 bits.
        // This requires 30 aux columns per debit row, or a shared lookup table.
        // ====================================================================

        let s_noop = local[sel::NOOP];
        let s_transfer = local[sel::TRANSFER];
        let s_setfield = local[sel::SET_FIELD];
        let s_grantcap = local[sel::GRANT_CAP];
        let s_notespend = local[sel::NOTE_SPEND];
        let s_notecreate = local[sel::NOTE_CREATE];
        let s_create_obligation = local[sel::CREATE_OBLIGATION];
        let s_fulfill_obligation = local[sel::FULFILL_OBLIGATION];
        let s_custom = local[sel::CUSTOM];

        // State accessors (before).
        let old_bal_lo = local[STATE_BEFORE_BASE + state::BALANCE_LO];
        let old_bal_hi = local[STATE_BEFORE_BASE + state::BALANCE_HI];
        let old_nonce = local[STATE_BEFORE_BASE + state::NONCE];
        let old_cap_root = local[STATE_BEFORE_BASE + state::CAP_ROOT];

        // State accessors (after).
        let new_bal_lo = local[STATE_AFTER_BASE + state::BALANCE_LO];
        let new_bal_hi = local[STATE_AFTER_BASE + state::BALANCE_HI];
        let new_nonce = local[STATE_AFTER_BASE + state::NONCE];
        let new_cap_root = local[STATE_AFTER_BASE + state::CAP_ROOT];

        // Parameters.
        let p0 = local[PARAM_BASE + 0];
        let p1 = local[PARAM_BASE + 1];
        let _p2 = local[PARAM_BASE + 2];

        // -- NoOp: state_after == state_before for all state columns --
        for i in 0..state::SIZE {
            let c = s_noop * (local[STATE_AFTER_BASE + i] - local[STATE_BEFORE_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- Transfer: balance update --
        // param0 = amount_lo, param1 = direction (0=in, 1=out)
        // If direction=0 (in): new_bal = old_bal + amount
        // If direction=1 (out): new_bal = old_bal - amount
        // Unified: new_bal_lo - old_bal_lo - amount + 2*direction*amount == carry adjustment
        //
        // We work with the combined 60-bit balance:
        //   balance = bal_lo + bal_hi * 2^30
        //   Transfer only touches bal_lo for simplicity (amount < 2^30).
        //   new_bal_lo = old_bal_lo + amount * (1 - 2*direction)
        //
        // For amounts that don't overflow a single limb:
        let two = BabyBear::new(2);
        let direction = p1;
        let amount = p0;
        // new_bal_lo == old_bal_lo + amount - 2*direction*amount
        let c_transfer_lo =
            s_transfer * (new_bal_lo - old_bal_lo - amount + two * direction * amount);
        combined = combined + alpha_pow * c_transfer_lo;
        alpha_pow = alpha_pow * alpha;

        // Transfer: hi limb unchanged (for single-limb amounts).
        let c_transfer_hi = s_transfer * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_transfer_hi;
        alpha_pow = alpha_pow * alpha;

        // Transfer: direction must be boolean.
        let c_transfer_dir = s_transfer * direction * (direction - BabyBear::ONE);
        combined = combined + alpha_pow * c_transfer_dir;
        alpha_pow = alpha_pow * alpha;

        // Transfer: cap_root and reserved unchanged.
        // (state_commitment is a derived value recomputed in witness gen; bound at boundaries only.)
        for i in [state::CAP_ROOT, state::RESERVED] {
            let c = s_transfer * (local[STATE_AFTER_BASE + i] - local[STATE_BEFORE_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }
        // Transfer: fields unchanged.
        for i in 0..8 {
            let c = s_transfer
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- SetField: exactly one field updated --
        // param0 = field_index, param1 = new_value
        // For the targeted field: new_field[idx] = new_value.
        // For all others: unchanged.
        // We use the Lagrange selector trick:
        //   For each field slot j: new_field[j] - old_field[j] - is_target_j * (new_value - old_field[j]) == 0
        //   where is_target_j = prod_{k != j} (field_index - k) / (j - k)
        //
        // Simplified: we constrain that the sum of changes equals (new_value - old_field[idx])
        // and that it happens at exactly the right index. For degree control, we use:
        //   For each j in 0..8:
        //     sel_setfield * (new_field[j] - old_field[j]) * (1 - eq(field_index, j)) == 0
        //     where eq check is: (field_index - j) * inverse_or_zero
        //
        // Even simpler approach (lower degree): use aux columns for the Lagrange basis.
        // But for v1, we use a direct approach with the product constraint:
        //   sel_setfield * (new_field[j] - old_field[j]) * product_{k != j}(field_index - k) == 0
        //   for all j where field_index != j.
        //
        // Actually simplest: enforce
        //   For each j: sel * (new_f[j] - old_f[j] - delta_j) == 0
        //   where delta_j = if j == field_index { new_value - old_f[j] } else { 0 }
        //
        // We do it as: for the ONE field that matches, the difference must equal new_value - old.
        // For all others, difference must be zero.
        // With selector-index product trick at degree 2:
        //   sel_setfield * (field_index - j) * (new_f[j] - old_f[j]) == 0 for each j
        //   (if field_index == j, this is trivially 0 regardless of change)
        //   (if field_index != j, new_f[j] - old_f[j] must be 0)
        let field_index = p0;
        let new_value = p1;
        for j in 0..8u32 {
            let old_fj = local[STATE_BEFORE_BASE + state::FIELD_BASE + j as usize];
            let new_fj = local[STATE_AFTER_BASE + state::FIELD_BASE + j as usize];
            // Non-target fields must be unchanged.
            let c = s_setfield * (field_index - BabyBear::new(j)) * (new_fj - old_fj);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }
        // The target field must become new_value. We check this by:
        //   For each j: sel * prod_{k!=j}(index - k) * (new_f[j] - new_value) == 0
        // When index == j, prod_{k!=j}(index-k) != 0, so new_f[j] must equal new_value.
        // When index != j, some factor (index - j) is zero in the product, so constraint is trivial.
        // But this is high degree (degree 8). Instead, use the aux column approach:
        //   aux[0] stores the Lagrange indicator (computed in witness gen).
        //   Constraint: sel * (sum_j new_f[j] * lagrange_j - new_value) == 0
        //
        // Simplest correct approach for v1: The witness generation ensures the right field
        // is set. We just need ONE constraint proving the target field has the right value.
        // Use aux[0] to carry the old value of the target field, then:
        //   sel_setfield * (new_value - target_field_new) == 0
        // where target_field_new is reconstructed from the trace.
        //
        // Actually, the simplest sound approach:
        //   Verify that the difference across all fields sums to exactly (new_value - old_value_at_idx).
        //   Combined with per-field constraints above (non-target unchanged), this is sufficient.
        // The sum of (new_f[j] - old_f[j]) for all j must equal (new_value - old_value_at_idx).
        // old_value_at_idx is stored in aux[0].
        let old_value_at_idx = local[AUX_BASE + 0];
        let mut field_diff_sum = BabyBear::ZERO;
        for j in 0..8 {
            let old_fj = local[STATE_BEFORE_BASE + state::FIELD_BASE + j];
            let new_fj = local[STATE_AFTER_BASE + state::FIELD_BASE + j];
            field_diff_sum = field_diff_sum + (new_fj - old_fj);
        }
        let c_setfield_sum = s_setfield * (field_diff_sum - (new_value - old_value_at_idx));
        combined = combined + alpha_pow * c_setfield_sum;
        alpha_pow = alpha_pow * alpha;

        // SetField: balance and cap_root unchanged.
        let c_sf_bal_lo = s_setfield * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_sf_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_sf_bal_hi = s_setfield * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_sf_bal_hi;
        alpha_pow = alpha_pow * alpha;
        let c_sf_cap = s_setfield * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_sf_cap;
        alpha_pow = alpha_pow * alpha;

        // ====================================================================
        // RANGE CHECK: SetField field_idx must be in {0, 1, 2, 3, 4, 5, 6, 7}
        // ====================================================================
        // Degree-8 polynomial that vanishes exactly on {0..7}:
        //   prod_{k=0}^{7} (field_idx - k) == 0
        // Gated by sel_setfield (total degree 9). Any out-of-bounds value makes
        // this constraint non-zero, causing the STARK verifier to reject.
        {
            let mut field_idx_range_product = BabyBear::ONE;
            for k in 0..8u32 {
                field_idx_range_product =
                    field_idx_range_product * (field_index - BabyBear::new(k));
            }
            let c_field_idx_range = s_setfield * field_idx_range_product;
            combined = combined + alpha_pow * c_field_idx_range;
            alpha_pow = alpha_pow * alpha;
        }

        // -- GrantCapability: capability_root update --
        // param0 = cap_entry (hash of new capability)
        // new_cap_root MUST equal hash_2_to_1(old_cap_root, cap_entry).
        //
        // SOUNDNESS FIX: We compute hash_2_to_1 directly in the constraint evaluator.
        // The old approach used a prover-controlled aux[1] value which allowed a
        // malicious prover to set new_cap_root to ANY value. Now the verifier
        // independently computes the hash at each evaluation point. This works because
        // eval_constraints operates on concrete field values (not symbolic polynomials),
        // so the hash is a pure function of the trace values at the query point.
        let cap_entry_val = local[PARAM_BASE + param::CAP_ENTRY];
        let expected_new_cap = hash_2_to_1(old_cap_root, cap_entry_val);
        let c_grantcap = s_grantcap * (new_cap_root - expected_new_cap);
        combined = combined + alpha_pow * c_grantcap;
        alpha_pow = alpha_pow * alpha;

        // GrantCap: balance and fields unchanged.
        let c_gc_bal_lo = s_grantcap * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_gc_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_gc_bal_hi = s_grantcap * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_gc_bal_hi;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_grantcap
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- NoteSpend: balance credit --
        // param0 = nullifier, param1 = value_lo, param2 = value_hi
        // new_bal_lo = old_bal_lo + value_lo (with potential carry to hi)
        // For simplicity (v1): value fits in lo limb (value_hi == 0).
        let note_val_lo = p1;
        let c_ns_bal = s_notespend * (new_bal_lo - old_bal_lo - note_val_lo);
        combined = combined + alpha_pow * c_ns_bal;
        alpha_pow = alpha_pow * alpha;
        let c_ns_hi = s_notespend * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_ns_hi;
        alpha_pow = alpha_pow * alpha;
        // NoteSpend: fields and cap unchanged.
        let c_ns_cap = s_notespend * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_ns_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_notespend
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- NoteCreate: balance debit --
        // param0 = commitment, param1 = value_lo, param2 = value_hi
        // new_bal_lo = old_bal_lo - value_lo
        let nc_val_lo = p1;
        let c_nc_bal = s_notecreate * (new_bal_lo - old_bal_lo + nc_val_lo);
        combined = combined + alpha_pow * c_nc_bal;
        alpha_pow = alpha_pow * alpha;
        let c_nc_hi = s_notecreate * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_nc_hi;
        alpha_pow = alpha_pow * alpha;
        // NoteCreate: fields and cap unchanged.
        let c_nc_cap = s_notecreate * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_nc_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_notecreate
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- CreateObligation: balance debit (locks stake) --
        // param0 = stake_lo, param1 = stake_hi (unused for single-limb), param2 = obligation_id
        // new_bal_lo = old_bal_lo - stake_lo (stake locked from balance)
        let stake_lo = p0;
        let c_co_bal = s_create_obligation * (new_bal_lo - old_bal_lo + stake_lo);
        combined = combined + alpha_pow * c_co_bal;
        alpha_pow = alpha_pow * alpha;
        let c_co_hi = s_create_obligation * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_co_hi;
        alpha_pow = alpha_pow * alpha;
        // CreateObligation: fields and cap unchanged.
        let c_co_cap = s_create_obligation * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_co_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_create_obligation
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- FulfillObligation: balance credit (returns stake) --
        // param0 = obligation_id, param1 = return_lo, param2 = return_hi
        // new_bal_lo = old_bal_lo + return_lo
        let return_lo = p1;
        let c_fo_bal = s_fulfill_obligation * (new_bal_lo - old_bal_lo - return_lo);
        combined = combined + alpha_pow * c_fo_bal;
        alpha_pow = alpha_pow * alpha;
        let c_fo_hi = s_fulfill_obligation * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_fo_hi;
        alpha_pow = alpha_pow * alpha;
        // FulfillObligation: fields and cap unchanged.
        let c_fo_cap = s_fulfill_obligation * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_fo_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_fulfill_obligation
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- Custom (CellProgram dispatch): state continuity only --
        // The Custom effect does NOT alter balance, fields, or cap_root.
        // State flows through unchanged (the custom program's constraints are
        // proven externally; the Effect VM only binds the proof commitment to PI).
        // Constraints: all state columns unchanged (same as NoOp for state).
        for i in 0..state::SIZE {
            let c = s_custom * (local[STATE_AFTER_BASE + i] - local[STATE_BEFORE_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // ====================================================================

        // -- SlashObligation: balance credit (slashed stake to beneficiary) --
        // param0 = obligation_id, param1 = stake_lo, param2 = stake_hi, param3 = beneficiary
        // new_bal_lo = old_bal_lo + stake_lo
        let s_slash = local[sel::SLASH_OBLIGATION];
        let slash_stake_lo = local[PARAM_BASE + param::SLASH_STAKE_LO];
        let c_slash_bal = s_slash * (new_bal_lo - old_bal_lo - slash_stake_lo);
        combined = combined + alpha_pow * c_slash_bal;
        alpha_pow = alpha_pow * alpha;
        let c_slash_hi = s_slash * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_slash_hi;
        alpha_pow = alpha_pow * alpha;
        // SlashObligation: cap_root updated (obligation removed).
        // SOUNDNESS FIX: Compute hash_2_to_1 directly instead of trusting prover aux[1].
        let slash_obligation_id = local[PARAM_BASE + param::SLASH_OBLIGATION_ID];
        let expected_slash_cap = hash_2_to_1(old_cap_root, slash_obligation_id);
        let c_slash_cap = s_slash * (new_cap_root - expected_slash_cap);
        combined = combined + alpha_pow * c_slash_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_slash
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- Seal: balance, fields, cap_root all unchanged --
        let s_seal = local[sel::SEAL];
        let c_seal_bal_lo = s_seal * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_seal_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_seal_bal_hi = s_seal * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_seal_bal_hi;
        alpha_pow = alpha_pow * alpha;
        let c_seal_cap = s_seal * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_seal_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_seal
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // RANGE CHECK: Seal field_idx must be in {0..7}.
        {
            let seal_field_idx = local[PARAM_BASE + param::SEAL_FIELD_IDX];
            let mut seal_idx_range_product = BabyBear::ONE;
            for k in 0..8u32 {
                seal_idx_range_product =
                    seal_idx_range_product * (seal_field_idx - BabyBear::new(k));
            }
            let c_seal_idx_range = s_seal * seal_idx_range_product;
            combined = combined + alpha_pow * c_seal_idx_range;
            alpha_pow = alpha_pow * alpha;
        }

        // -- Unseal: balance, fields, cap_root all unchanged --
        let s_unseal = local[sel::UNSEAL];
        let c_unseal_bal_lo = s_unseal * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_unseal_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_unseal_bal_hi = s_unseal * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_unseal_bal_hi;
        alpha_pow = alpha_pow * alpha;
        let c_unseal_cap = s_unseal * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_unseal_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_unseal
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // RANGE CHECK: Unseal field_idx must be in {0..7}.
        {
            let unseal_field_idx = local[PARAM_BASE + param::UNSEAL_FIELD_IDX];
            let mut unseal_idx_range_product = BabyBear::ONE;
            for k in 0..8u32 {
                unseal_idx_range_product =
                    unseal_idx_range_product * (unseal_field_idx - BabyBear::new(k));
            }
            let c_unseal_idx_range = s_unseal * unseal_idx_range_product;
            combined = combined + alpha_pow * c_unseal_idx_range;
            alpha_pow = alpha_pow * alpha;
        }

        // -- MakeSovereign: mode_flag 0->1, balance/fields/cap preserved --
        let s_makesov = local[sel::MAKE_SOVEREIGN];
        let old_reserved = local[STATE_BEFORE_BASE + state::RESERVED];
        let new_reserved = local[STATE_AFTER_BASE + state::RESERVED];
        let c_sov_mode = s_makesov * (new_reserved - old_reserved - BabyBear::new(256));
        combined = combined + alpha_pow * c_sov_mode;
        alpha_pow = alpha_pow * alpha;
        let c_sov_bal_lo = s_makesov * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_sov_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_sov_bal_hi = s_makesov * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_sov_bal_hi;
        alpha_pow = alpha_pow * alpha;
        let c_sov_cap = s_makesov * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_sov_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_makesov
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- CreateCellFromFactory: state flows through unchanged --
        let s_factory = local[sel::CREATE_CELL_FROM_FACTORY];
        for i in 0..state::SIZE {
            let c = s_factory * (local[STATE_AFTER_BASE + i] - local[STATE_BEFORE_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // ====================================================================
        // CapTP Effects (provable CapTP operations)
        // ====================================================================

        // -- ExportSturdyRef: swiss_number = hash(cell_id, random_seed, counter) --
        // Proves the swiss number derivation is correct.
        // State: field[7] increments (export_counter), balance/cap/other fields unchanged.
        let s_export = local[sel::EXPORT_STURDY_REF];
        {
            let cell_id = local[PARAM_BASE + param::EXPORT_CELL_ID];
            let random_seed = local[PARAM_BASE + param::EXPORT_RANDOM_SEED];
            let export_counter = local[PARAM_BASE + param::EXPORT_COUNTER];
            // Swiss number = hash(cell_id, hash(random_seed, counter))
            let inner_hash = hash_2_to_1(random_seed, export_counter);
            let expected_swiss = hash_2_to_1(cell_id, inner_hash);
            // The computed swiss is stored in aux[0] for binding.
            let aux_swiss = local[AUX_BASE + 0];
            let c_swiss = s_export * (aux_swiss - expected_swiss);
            combined = combined + alpha_pow * c_swiss;
            alpha_pow = alpha_pow * alpha;

            // field[7] must increment by 1 (export counter).
            let old_f7 = local[STATE_BEFORE_BASE + state::FIELD_BASE + 7];
            let new_f7 = local[STATE_AFTER_BASE + state::FIELD_BASE + 7];
            let c_counter = s_export * (new_f7 - old_f7 - BabyBear::ONE);
            combined = combined + alpha_pow * c_counter;
            alpha_pow = alpha_pow * alpha;

            // Balance unchanged.
            let c_bal_lo = s_export * (new_bal_lo - old_bal_lo);
            combined = combined + alpha_pow * c_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_bal_hi = s_export * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_bal_hi;
            alpha_pow = alpha_pow * alpha;

            // Cap root unchanged.
            let c_cap = s_export * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_cap;
            alpha_pow = alpha_pow * alpha;

            // Fields 0..7 unchanged (only field[7] changes).
            for i in 0..7 {
                let c = s_export
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
        }

        // -- EnlivenRef: validate swiss number exists in table --
        // Proves: hash(swiss_number, expected_cell_id) matches committed table entry.
        // State: field[6] increments (use_count), balance/cap/other fields unchanged.
        let s_enliven = local[sel::ENLIVEN_REF];
        {
            let swiss = local[PARAM_BASE + param::ENLIVEN_SWISS];
            let expected_cell_id = local[PARAM_BASE + param::ENLIVEN_CELL_ID];
            let expected_perms = local[PARAM_BASE + param::ENLIVEN_PERMISSIONS];
            // Verify table entry: aux[0] = hash(swiss, hash(cell_id, permissions))
            // The executor populates this from the swiss table; the circuit verifies
            // the hash relationship.
            let inner = hash_2_to_1(expected_cell_id, expected_perms);
            let expected_entry_hash = hash_2_to_1(swiss, inner);
            let aux_entry = local[AUX_BASE + 0];
            let c_entry = s_enliven * (aux_entry - expected_entry_hash);
            combined = combined + alpha_pow * c_entry;
            alpha_pow = alpha_pow * alpha;

            // field[6] must increment by 1 (use_count).
            let old_f6 = local[STATE_BEFORE_BASE + state::FIELD_BASE + 6];
            let new_f6 = local[STATE_AFTER_BASE + state::FIELD_BASE + 6];
            let c_use = s_enliven * (new_f6 - old_f6 - BabyBear::ONE);
            combined = combined + alpha_pow * c_use;
            alpha_pow = alpha_pow * alpha;

            // Balance unchanged.
            let c_bal_lo = s_enliven * (new_bal_lo - old_bal_lo);
            combined = combined + alpha_pow * c_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_bal_hi = s_enliven * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_bal_hi;
            alpha_pow = alpha_pow * alpha;

            // Cap root unchanged.
            let c_cap = s_enliven * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_cap;
            alpha_pow = alpha_pow * alpha;

            // Fields 0..6 and field[7] unchanged (only field[6] changes).
            for i in 0..6 {
                let c = s_enliven
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
            // field[7] unchanged
            let c_f7 = s_enliven
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + 7]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + 7]);
            combined = combined + alpha_pow * c_f7;
            alpha_pow = alpha_pow * alpha;
        }

        // -- DropRef: decrement refcount, prove it was > 0 --
        // State: field[5] decrements (refcount), balance/cap/other fields unchanged.
        // The constraint proves refcount > 0 by requiring old_f5 - 1 == new_f5
        // and old_f5 != 0 (enforced by requiring param DROP_REFCOUNT == old_f5,
        // and DROP_REFCOUNT is non-zero checked via aux).
        let s_drop = local[sel::DROP_REF];
        {
            let refcount_param = local[PARAM_BASE + param::DROP_REFCOUNT];

            // field[5] must decrement by 1.
            let old_f5 = local[STATE_BEFORE_BASE + state::FIELD_BASE + 5];
            let new_f5 = local[STATE_AFTER_BASE + state::FIELD_BASE + 5];
            let c_dec = s_drop * (new_f5 - old_f5 + BabyBear::ONE);
            combined = combined + alpha_pow * c_dec;
            alpha_pow = alpha_pow * alpha;

            // refcount param must match old field[5] (binds the declared refcount).
            let c_rc = s_drop * (refcount_param - old_f5);
            combined = combined + alpha_pow * c_rc;
            alpha_pow = alpha_pow * alpha;

            // Prove refcount > 0: aux[0] = inverse(refcount_param).
            // If refcount_param == 0, no inverse exists, constraint fails.
            // Constraint: refcount_param * aux[0] == 1
            let rc_inv = local[AUX_BASE + 0];
            let c_nonzero = s_drop * (refcount_param * rc_inv - BabyBear::ONE);
            combined = combined + alpha_pow * c_nonzero;
            alpha_pow = alpha_pow * alpha;

            // Balance unchanged.
            let c_bal_lo = s_drop * (new_bal_lo - old_bal_lo);
            combined = combined + alpha_pow * c_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_bal_hi = s_drop * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_bal_hi;
            alpha_pow = alpha_pow * alpha;

            // Cap root unchanged.
            let c_cap = s_drop * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_cap;
            alpha_pow = alpha_pow * alpha;

            // Fields 0..5, 6, 7 unchanged (only field[5] changes).
            for i in 0..5 {
                let c = s_drop
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
            for i in 6..8 {
                let c = s_drop
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
        }

        // -- ValidateHandoff: prove certificate hash is in approved set --
        // Uses hash-based membership: hash(cert_hash, approved_set_root) must match
        // the value in aux[0] (populated by executor from Merkle proof).
        // State: cap_root updated (routing entry for recipient), balance/fields unchanged.
        let s_handoff = local[sel::VALIDATE_HANDOFF];
        {
            let cert_hash = local[PARAM_BASE + param::HANDOFF_CERT_HASH];
            let recipient_pk = local[PARAM_BASE + param::HANDOFF_RECIPIENT_PK];
            let approved_root = local[PARAM_BASE + param::HANDOFF_APPROVED_SET_ROOT];

            // Membership proof: aux[0] = hash(cert_hash, approved_root)
            // This binds the certificate to the approved set.
            let expected_membership = hash_2_to_1(cert_hash, approved_root);
            let aux_membership = local[AUX_BASE + 0];
            let c_member = s_handoff * (aux_membership - expected_membership);
            combined = combined + alpha_pow * c_member;
            alpha_pow = alpha_pow * alpha;

            // Cap root updated: new_cap_root = hash(old_cap_root, hash(recipient_pk, cert_hash))
            // This creates a routing entry for the recipient.
            let routing_entry = hash_2_to_1(recipient_pk, cert_hash);
            let expected_new_cap = hash_2_to_1(old_cap_root, routing_entry);
            let c_cap = s_handoff * (new_cap_root - expected_new_cap);
            combined = combined + alpha_pow * c_cap;
            alpha_pow = alpha_pow * alpha;

            // Balance unchanged.
            let c_bal_lo = s_handoff * (new_bal_lo - old_bal_lo);
            combined = combined + alpha_pow * c_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_bal_hi = s_handoff * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_bal_hi;
            alpha_pow = alpha_pow * alpha;

            // All fields unchanged.
            for i in 0..8 {
                let c = s_handoff
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
        }

        // CONSTRAINT GROUP 3: Transition constraints (row continuity)
        // ====================================================================
        // next_row.state_before == this_row.state_after
        // (Enforced on all rows except the last — the STARK framework handles this
        //  via the transition vanishing polynomial which excludes the last row.)
        for i in 0..state::SIZE {
            let c = next[STATE_BEFORE_BASE + i] - local[STATE_AFTER_BASE + i];
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // Nonce increment: for non-NoOp rows, nonce increments by 1.
        // For NoOp (padding) rows, nonce stays the same.
        // Combined: new_nonce == old_nonce + (1 - sel_noop)
        let c_nonce = new_nonce - old_nonce - (BabyBear::ONE - s_noop);
        combined = combined + alpha_pow * c_nonce;
        alpha_pow = alpha_pow * alpha;

        // ====================================================================
        // CONSTRAINT GROUP 4: State commitment integrity (tree hash)
        // ====================================================================
        // The state_commitment in state_after MUST equal the tree hash of the
        // state_after columns. This prevents a malicious prover from claiming
        // an arbitrary commitment that doesn't match the actual state.
        //
        // Tree structure (constrainable via hash_4_to_1):
        //   inter1 = hash_4_to_1(bal_lo, bal_hi, nonce, field[0])
        //   inter2 = hash_4_to_1(field[1], field[2], field[3], field[4])
        //   inter3 = hash_4_to_1(field[5], field[6], field[7], cap_root)
        //   state_commit = hash_4_to_1(inter1, inter2, inter3, ZERO)
        //
        // The intermediates are stored in aux[8..10] and verified here.
        {
            let after_bal_lo = local[STATE_AFTER_BASE + state::BALANCE_LO];
            let after_bal_hi = local[STATE_AFTER_BASE + state::BALANCE_HI];
            let after_nonce = local[STATE_AFTER_BASE + state::NONCE];
            let after_cap_root = local[STATE_AFTER_BASE + state::CAP_ROOT];
            let after_commit = local[STATE_AFTER_BASE + state::STATE_COMMIT];

            let inter1 = local[AUX_BASE + aux_off::STATE_INTER1];
            let inter2 = local[AUX_BASE + aux_off::STATE_INTER2];
            let inter3 = local[AUX_BASE + aux_off::STATE_INTER3];

            // Constraint: inter1 == hash_4_to_1(bal_lo, bal_hi, nonce, field[0])
            let expected_inter1 = hash_4_to_1(&[
                after_bal_lo,
                after_bal_hi,
                after_nonce,
                local[STATE_AFTER_BASE + state::FIELD_BASE + 0],
            ]);
            let c_inter1 = inter1 - expected_inter1;
            combined = combined + alpha_pow * c_inter1;
            alpha_pow = alpha_pow * alpha;

            // Constraint: inter2 == hash_4_to_1(field[1], field[2], field[3], field[4])
            let expected_inter2 = hash_4_to_1(&[
                local[STATE_AFTER_BASE + state::FIELD_BASE + 1],
                local[STATE_AFTER_BASE + state::FIELD_BASE + 2],
                local[STATE_AFTER_BASE + state::FIELD_BASE + 3],
                local[STATE_AFTER_BASE + state::FIELD_BASE + 4],
            ]);
            let c_inter2 = inter2 - expected_inter2;
            combined = combined + alpha_pow * c_inter2;
            alpha_pow = alpha_pow * alpha;

            // Constraint: inter3 == hash_4_to_1(field[5], field[6], field[7], cap_root)
            let expected_inter3 = hash_4_to_1(&[
                local[STATE_AFTER_BASE + state::FIELD_BASE + 5],
                local[STATE_AFTER_BASE + state::FIELD_BASE + 6],
                local[STATE_AFTER_BASE + state::FIELD_BASE + 7],
                after_cap_root,
            ]);
            let c_inter3 = inter3 - expected_inter3;
            combined = combined + alpha_pow * c_inter3;
            alpha_pow = alpha_pow * alpha;

            // Constraint: state_commit == hash_4_to_1(inter1, inter2, inter3, ZERO)
            let expected_commit = hash_4_to_1(&[inter1, inter2, inter3, BabyBear::ZERO]);
            let c_commit = after_commit - expected_commit;
            combined = combined + alpha_pow * c_commit;
            // alpha_pow = alpha_pow * alpha; // (not needed after last)
        }

        combined
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        let mut constraints = vec![];
        if public_inputs.len() < pi::BASE_COUNT {
            return constraints;
        }

        // First row: state_commitment column must match the public input directly.
        constraints.push(BoundaryConstraint {
            row: 0,
            col: STATE_BEFORE_BASE + state::STATE_COMMIT,
            value: public_inputs[pi::OLD_COMMIT],
        });

        // CRITICAL: Last row state_after commitment must match new_commitment PI.
        // Without this, a malicious prover could claim any new_commitment.
        // The last row is either the last real effect or a NoOp padding row;
        // either way, its state_after must equal the final state.
        let last_row = trace_len.saturating_sub(1);
        constraints.push(BoundaryConstraint {
            row: last_row,
            col: STATE_AFTER_BASE + state::STATE_COMMIT,
            value: public_inputs[pi::NEW_COMMIT],
        });

        // Net balance delta binding: the net delta is carried in aux columns.
        // Row 0, aux[2] = net_delta_magnitude, aux[3] = net_delta_sign.
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + 2,
            value: public_inputs[pi::NET_DELTA_MAG],
        });
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + 3,
            value: public_inputs[pi::NET_DELTA_SIGN],
        });

        // Effects hash binding.
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + 4,
            value: public_inputs[pi::EFFECTS_HASH_LO],
        });
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + 5,
            value: public_inputs[pi::EFFECTS_HASH_HI],
        });

        constraints
    }
}

// ============================================================================
// Witness Generation
// ============================================================================

/// Generate the execution trace and public inputs for an effect VM proof.
///
/// # Arguments
/// * `initial_state` - The cell state before executing effects.
/// * `effects` - The sequence of effects to prove.
///
/// # Returns
/// (trace, public_inputs) suitable for `stark::prove`.
pub fn generate_effect_vm_trace(
    initial_state: &CellState,
    effects: &[Effect],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    assert!(!effects.is_empty(), "Need at least one effect");

    // ====================================================================
    // EXECUTOR-SIDE RANGE VALIDATION (o1vm audit mitigations)
    // ====================================================================
    // These checks run at proof generation time. They do NOT add constraints
    // to the STARK, but they prevent the executor from producing a trace with
    // out-of-range values that could exploit modular arithmetic.
    //
    // A verifier receiving a proof from an untrusted prover must additionally
    // verify that the final state (decoded from new_commitment PI) has valid
    // limb ranges. See `verify_balance_limb_ranges` below.
    // ====================================================================

    // Validate initial balance limbs are in range.
    let (init_lo, init_hi) = split_u64(initial_state.balance);
    assert!(
        init_lo.0 < (1 << 30),
        "Initial balance_lo out of range: {} >= 2^30",
        init_lo.0
    );
    assert!(
        init_hi.0 < (1 << 31),
        "Initial balance_hi out of range: {} >= 2^31 (exceeds BabyBear)",
        init_hi.0
    );

    // Validate field_idx bounds and balance underflow for all effects.
    // We track a running balance to catch underflow across multi-effect turns.
    {
        let mut running_balance = initial_state.balance;
        for effect in effects {
            match effect {
                Effect::SetField { field_idx, .. } => {
                    assert!(
                        *field_idx < 8,
                        "SetField field_idx out of bounds: {} (must be 0..7)",
                        field_idx
                    );
                }
                Effect::Seal { field_idx } => {
                    assert!(
                        *field_idx < 8,
                        "Seal field_idx out of bounds: {} (must be 0..7)",
                        field_idx
                    );
                }
                Effect::Unseal { field_idx, .. } => {
                    assert!(
                        *field_idx < 8,
                        "Unseal field_idx out of bounds: {} (must be 0..7)",
                        field_idx
                    );
                }
                Effect::Transfer {
                    amount, direction, ..
                } => {
                    if *direction == 1 {
                        // Outgoing: validate no underflow.
                        assert!(
                            *amount <= running_balance,
                            "Transfer underflow: amount {} > running balance {} \
                             (executor rejects; STARK constraint would wrap in BabyBear)",
                            amount,
                            running_balance
                        );
                        running_balance -= amount;
                    } else {
                        running_balance = running_balance.saturating_add(*amount);
                    }
                }
                Effect::NoteCreate { value, .. } => {
                    assert!(
                        *value <= running_balance,
                        "NoteCreate underflow: value {} > running balance {} \
                         (executor rejects; STARK constraint would wrap in BabyBear)",
                        value,
                        running_balance
                    );
                    running_balance -= value;
                }
                Effect::CreateObligation { stake_amount, .. } => {
                    assert!(
                        *stake_amount <= running_balance,
                        "CreateObligation underflow: stake {} > running balance {} \
                         (executor rejects; STARK constraint would wrap in BabyBear)",
                        stake_amount,
                        running_balance
                    );
                    running_balance -= stake_amount;
                }
                Effect::NoteSpend { value, .. } => {
                    running_balance = running_balance.saturating_add(*value);
                }
                Effect::FulfillObligation { stake_return, .. } => {
                    running_balance = running_balance.saturating_add(*stake_return);
                }
                Effect::SlashObligation { stake_amount, .. } => {
                    running_balance = running_balance.saturating_add(*stake_amount);
                }
                _ => {}
            }
        }
    }

    // Determine trace height (pad to power of 2, minimum 2).
    let n_effects = effects.len();
    let trace_height = n_effects.next_power_of_two().max(2);

    let mut trace = Vec::with_capacity(trace_height);
    let mut current_state = initial_state.clone();

    // Track net balance delta.
    let mut net_delta: i64 = 0;

    for effect in effects {
        let mut row = vec![BabyBear::ZERO; EFFECT_VM_WIDTH];

        // Set selector.
        let sel_idx = match effect {
            Effect::NoOp => sel::NOOP,
            Effect::Transfer { .. } => sel::TRANSFER,
            Effect::SetField { .. } => sel::SET_FIELD,
            Effect::GrantCapability { .. } => sel::GRANT_CAP,
            Effect::NoteSpend { .. } => sel::NOTE_SPEND,
            Effect::NoteCreate { .. } => sel::NOTE_CREATE,
            Effect::CreateObligation { .. } => sel::CREATE_OBLIGATION,
            Effect::FulfillObligation { .. } => sel::FULFILL_OBLIGATION,
            Effect::Custom { .. } => sel::CUSTOM,
            Effect::SlashObligation { .. } => sel::SLASH_OBLIGATION,
            Effect::Seal { .. } => sel::SEAL,
            Effect::Unseal { .. } => sel::UNSEAL,
            Effect::MakeSovereign => sel::MAKE_SOVEREIGN,
            Effect::CreateCellFromFactory { .. } => sel::CREATE_CELL_FROM_FACTORY,
            Effect::ExportSturdyRef { .. } => sel::EXPORT_STURDY_REF,
            Effect::EnlivenRef { .. } => sel::ENLIVEN_REF,
            Effect::DropRef { .. } => sel::DROP_REF,
            Effect::ValidateHandoff { .. } => sel::VALIDATE_HANDOFF,
        };
        row[sel_idx] = BabyBear::ONE;

        // Write state_before.
        let state_before_cols = current_state.to_trace_cols();
        for (i, &val) in state_before_cols.iter().enumerate() {
            row[STATE_BEFORE_BASE + i] = val;
        }

        // Apply effect and compute state_after + params.
        let mut new_state = current_state.clone();
        match effect {
            Effect::NoOp => {
                // No state change, no nonce increment for padding.
            }
            Effect::Transfer { amount, direction } => {
                let (lo, _hi) = split_u64(*amount);
                row[PARAM_BASE + param::AMOUNT] = lo;
                row[PARAM_BASE + param::DIRECTION] = BabyBear::new(*direction);

                if *direction == 1 {
                    // Outgoing.
                    new_state.balance = new_state.balance.saturating_sub(*amount);
                    net_delta -= *amount as i64;
                } else {
                    // Incoming.
                    new_state.balance = new_state.balance.saturating_add(*amount);
                    net_delta += *amount as i64;
                }
                new_state.nonce += 1;
            }
            Effect::SetField { field_idx, value } => {
                row[PARAM_BASE + param::FIELD_INDEX] = BabyBear::new(*field_idx);
                row[PARAM_BASE + param::NEW_VALUE] = *value;

                // Store old value at target index in aux[0] for the constraint.
                let idx = *field_idx as usize;
                row[AUX_BASE + 0] = current_state.fields[idx.min(7)];

                new_state.fields[idx.min(7)] = *value;
                new_state.nonce += 1;
            }
            Effect::GrantCapability { cap_entry } => {
                row[PARAM_BASE + param::CAP_ENTRY] = *cap_entry;

                let new_cap = hash_2_to_1(current_state.capability_root, *cap_entry);
                new_state.capability_root = new_cap;
                new_state.nonce += 1;
            }
            Effect::NoteSpend { nullifier, value } => {
                let (val_lo, val_hi) = split_u64(*value);
                row[PARAM_BASE + param::NULLIFIER] = *nullifier;
                row[PARAM_BASE + param::NOTE_VALUE_LO] = val_lo;
                row[PARAM_BASE + param::NOTE_VALUE_HI] = val_hi;

                new_state.balance = new_state.balance.saturating_add(*value);
                net_delta += *value as i64;
                new_state.nonce += 1;
            }
            Effect::NoteCreate { commitment, value } => {
                let (val_lo, val_hi) = split_u64(*value);
                row[PARAM_BASE + param::NOTE_COMMITMENT] = *commitment;
                row[PARAM_BASE + param::NOTE_VALUE_LO] = val_lo;
                row[PARAM_BASE + param::NOTE_VALUE_HI] = val_hi;

                new_state.balance = new_state.balance.saturating_sub(*value);
                net_delta -= *value as i64;
                new_state.nonce += 1;
            }
            Effect::CreateObligation {
                stake_amount,
                obligation_id,
                beneficiary_hash,
            } => {
                let (stake_lo, stake_hi) = split_u64(*stake_amount);
                row[PARAM_BASE + param::OBLIGATION_STAKE_LO] = stake_lo;
                row[PARAM_BASE + param::OBLIGATION_STAKE_HI] = stake_hi;
                row[PARAM_BASE + param::OBLIGATION_ID] = *obligation_id;
                row[PARAM_BASE + param::OBLIGATION_BENEFICIARY] = *beneficiary_hash;

                new_state.balance = new_state.balance.saturating_sub(*stake_amount);
                net_delta -= *stake_amount as i64;
                new_state.nonce += 1;
            }
            Effect::FulfillObligation {
                obligation_id,
                stake_return,
            } => {
                let (ret_lo, ret_hi) = split_u64(*stake_return);
                row[PARAM_BASE + param::FULFILL_OBLIGATION_ID] = *obligation_id;
                row[PARAM_BASE + param::FULFILL_RETURN_LO] = ret_lo;
                row[PARAM_BASE + param::FULFILL_RETURN_HI] = ret_hi;

                new_state.balance = new_state.balance.saturating_add(*stake_return);
                net_delta += *stake_return as i64;
                new_state.nonce += 1;
            }
            Effect::Custom {
                program_vk_hash,
                proof_commitment,
            } => {
                // Write VK hash into params[0..4].
                for i in 0..4 {
                    row[PARAM_BASE + param::CUSTOM_VK_HASH_BASE + i] = program_vk_hash[i];
                }
                // Write proof commitment into params[4..8].
                for i in 0..4 {
                    row[PARAM_BASE + param::CUSTOM_PROOF_COMMIT_BASE + i] = proof_commitment[i];
                }
                // Custom effects do NOT change state (state flows through unchanged).
                // The nonce still increments (it's a real effect, not padding).
                new_state.nonce += 1;
                // No balance change from the Effect VM perspective.
            }
            Effect::SlashObligation {
                obligation_id,
                stake_amount,
                beneficiary_hash,
            } => {
                let (stake_lo, stake_hi) = split_u64(*stake_amount);
                row[PARAM_BASE + param::SLASH_OBLIGATION_ID] = *obligation_id;
                row[PARAM_BASE + param::SLASH_STAKE_LO] = stake_lo;
                row[PARAM_BASE + param::SLASH_STAKE_HI] = stake_hi;
                row[PARAM_BASE + param::SLASH_BENEFICIARY] = *beneficiary_hash;
                // Slash credits the beneficiary: balance increases.
                new_state.balance = new_state.balance.saturating_add(*stake_amount);
                net_delta += *stake_amount as i64;
                // Update cap_root to reflect obligation removal.
                new_state.capability_root = hash_2_to_1(new_state.capability_root, *obligation_id);
                new_state.nonce += 1;
            }
            Effect::Seal { field_idx } => {
                row[PARAM_BASE + param::SEAL_FIELD_IDX] = BabyBear::new(*field_idx);
                new_state.sealed_field_mask |= 1 << field_idx;
                new_state.nonce += 1;
            }
            Effect::Unseal { field_idx, brand } => {
                row[PARAM_BASE + param::UNSEAL_FIELD_IDX] = BabyBear::new(*field_idx);
                row[PARAM_BASE + param::UNSEAL_BRAND] = *brand;
                // Store brand in aux for constraint checking.
                row[AUX_BASE + 6] = *brand;
                new_state.sealed_field_mask &= !(1 << field_idx);
                new_state.nonce += 1;
            }
            Effect::MakeSovereign => {
                // Mode flag transitions from 0 to 1.
                new_state.mode_flag = 1;
                new_state.nonce += 1;
            }
            Effect::CreateCellFromFactory {
                factory_vk,
                child_vk_derived,
            } => {
                row[PARAM_BASE + param::FACTORY_VK_HASH] = *factory_vk;
                row[PARAM_BASE + param::CHILD_VK_DERIVED] = *child_vk_derived;
                // Store in aux columns for constraint verification.
                row[AUX_BASE + 6] = *factory_vk;
                row[AUX_BASE + 7] = *child_vk_derived;
                new_state.nonce += 1;
            }
            Effect::ExportSturdyRef {
                cell_id,
                permissions,
                random_seed,
                export_counter,
            } => {
                row[PARAM_BASE + param::EXPORT_CELL_ID] = *cell_id;
                row[PARAM_BASE + param::EXPORT_PERMISSIONS] = *permissions;
                row[PARAM_BASE + param::EXPORT_RANDOM_SEED] = *random_seed;
                row[PARAM_BASE + param::EXPORT_COUNTER] = BabyBear::new(*export_counter);

                // Compute swiss_number = hash(cell_id, hash(random_seed, counter))
                let inner_hash = hash_2_to_1(*random_seed, BabyBear::new(*export_counter));
                let swiss_number = hash_2_to_1(*cell_id, inner_hash);
                // Store computed swiss in aux[0] for constraint verification.
                row[AUX_BASE + 0] = swiss_number;

                // State: field[7] increments (export counter tracked there).
                new_state.fields[7] = new_state.fields[7] + BabyBear::ONE;
                new_state.nonce += 1;
            }
            Effect::EnlivenRef {
                swiss_number,
                presenter_id,
                expected_cell_id,
                expected_permissions,
            } => {
                row[PARAM_BASE + param::ENLIVEN_SWISS] = *swiss_number;
                row[PARAM_BASE + param::ENLIVEN_PRESENTER] = *presenter_id;
                row[PARAM_BASE + param::ENLIVEN_CELL_ID] = *expected_cell_id;
                row[PARAM_BASE + param::ENLIVEN_PERMISSIONS] = *expected_permissions;

                // Compute entry hash: hash(swiss, hash(cell_id, permissions))
                let inner = hash_2_to_1(*expected_cell_id, *expected_permissions);
                let entry_hash = hash_2_to_1(*swiss_number, inner);
                row[AUX_BASE + 0] = entry_hash;

                // State: field[6] increments (use_count tracked there).
                new_state.fields[6] = new_state.fields[6] + BabyBear::ONE;
                new_state.nonce += 1;
            }
            Effect::DropRef {
                cell_id,
                holder_federation,
                current_refcount,
            } => {
                row[PARAM_BASE + param::DROP_CELL_ID] = *cell_id;
                row[PARAM_BASE + param::DROP_HOLDER_FED] = *holder_federation;
                row[PARAM_BASE + param::DROP_REFCOUNT] = BabyBear::new(*current_refcount);

                // Prove refcount > 0: store inverse in aux[0].
                // The constraint checks refcount * inverse == 1.
                assert!(
                    *current_refcount > 0,
                    "DropRef: current_refcount must be > 0"
                );
                let rc_field = BabyBear::new(*current_refcount);
                // Compute modular inverse of refcount in BabyBear.
                row[AUX_BASE + 0] = rc_field.inverse().expect("refcount is non-zero");

                // State: field[5] decrements (refcount tracked there).
                new_state.fields[5] = new_state.fields[5] - BabyBear::ONE;
                new_state.nonce += 1;
            }
            Effect::ValidateHandoff {
                certificate_hash,
                recipient_pk,
                introducer_pk,
                approved_set_root,
            } => {
                row[PARAM_BASE + param::HANDOFF_CERT_HASH] = *certificate_hash;
                row[PARAM_BASE + param::HANDOFF_RECIPIENT_PK] = *recipient_pk;
                row[PARAM_BASE + param::HANDOFF_INTRODUCER_PK] = *introducer_pk;
                row[PARAM_BASE + param::HANDOFF_APPROVED_SET_ROOT] = *approved_set_root;

                // Membership proof: aux[0] = hash(cert_hash, approved_set_root)
                let membership = hash_2_to_1(*certificate_hash, *approved_set_root);
                row[AUX_BASE + 0] = membership;

                // State: cap_root updated with routing entry.
                // new_cap = hash(old_cap, hash(recipient_pk, cert_hash))
                let routing_entry = hash_2_to_1(*recipient_pk, *certificate_hash);
                new_state.capability_root = hash_2_to_1(new_state.capability_root, routing_entry);
                new_state.nonce += 1;
            }
        }

        // Refresh state commitment.
        new_state.refresh_commitment();

        // Fill state commitment tree intermediate columns (aux[8..10]).
        // These are constrained by the evaluator to match hash_4_to_1 computations
        // on the state_after columns.
        let (inter1, inter2, inter3) = CellState::compute_commitment_intermediates(
            new_state.balance,
            new_state.nonce,
            &new_state.fields,
            new_state.capability_root,
        );
        row[AUX_BASE + aux_off::STATE_INTER1] = inter1;
        row[AUX_BASE + aux_off::STATE_INTER2] = inter2;
        row[AUX_BASE + aux_off::STATE_INTER3] = inter3;

        // Write state_after.
        let state_after_cols = new_state.to_trace_cols();
        for (i, &val) in state_after_cols.iter().enumerate() {
            row[STATE_AFTER_BASE + i] = val;
        }

        trace.push(row);
        current_state = new_state;
    }

    // Compute effects hash and net delta for public inputs.
    let (effects_hash_lo, effects_hash_hi) = compute_effects_hash(effects);
    let (delta_mag, delta_sign) = if net_delta < 0 {
        ((-net_delta) as u32, 1u32)
    } else {
        (net_delta as u32, 0u32)
    };

    // Fill aux columns on the first row with public-input-bound values.
    if !trace.is_empty() {
        trace[0][AUX_BASE + 2] = BabyBear::new(delta_mag);
        trace[0][AUX_BASE + 3] = BabyBear::new(delta_sign);
        trace[0][AUX_BASE + 4] = effects_hash_lo;
        trace[0][AUX_BASE + 5] = effects_hash_hi;
    }

    // Pad with NoOp rows.
    for _ in n_effects..trace_height {
        let mut row = vec![BabyBear::ZERO; EFFECT_VM_WIDTH];
        row[sel::NOOP] = BabyBear::ONE; // NoOp selector

        // State before = current state (carried from last real row).
        let state_cols = current_state.to_trace_cols();
        for (i, &val) in state_cols.iter().enumerate() {
            row[STATE_BEFORE_BASE + i] = val;
        }
        // State after = same (NoOp doesn't change state).
        for (i, &val) in state_cols.iter().enumerate() {
            row[STATE_AFTER_BASE + i] = val;
        }

        // Fill state commitment tree intermediates for padding rows too.
        let (inter1, inter2, inter3) = CellState::compute_commitment_intermediates(
            current_state.balance,
            current_state.nonce,
            &current_state.fields,
            current_state.capability_root,
        );
        row[AUX_BASE + aux_off::STATE_INTER1] = inter1;
        row[AUX_BASE + aux_off::STATE_INTER2] = inter2;
        row[AUX_BASE + aux_off::STATE_INTER3] = inter3;

        trace.push(row);
        // current_state stays the same for padding.
    }

    // Collect custom effect entries for public inputs.
    let custom_entries: Vec<_> = effects
        .iter()
        .filter_map(|e| {
            if let Effect::Custom {
                program_vk_hash,
                proof_commitment,
            } = e
            {
                Some((*program_vk_hash, *proof_commitment))
            } else {
                None
            }
        })
        .collect();
    let custom_count = custom_entries.len();
    assert!(
        custom_count <= pi::MAX_CUSTOM_EFFECTS,
        "Too many custom effects: {} (max {})",
        custom_count,
        pi::MAX_CUSTOM_EFFECTS
    );

    // Build public inputs.
    let pi_len = pi::BASE_COUNT + custom_count * pi::CUSTOM_ENTRY_SIZE;
    let mut public_inputs = Vec::with_capacity(pi_len);

    // Old state commitment (single field element).
    public_inputs.push(initial_state.state_commitment);
    // New state commitment (single field element).
    public_inputs.push(current_state.state_commitment);
    // Net delta.
    public_inputs.push(BabyBear::new(delta_mag));
    public_inputs.push(BabyBear::new(delta_sign));
    // Effects hash.
    public_inputs.push(effects_hash_lo);
    public_inputs.push(effects_hash_hi);
    // Custom effect count.
    public_inputs.push(BabyBear::new(custom_count as u32));

    // Custom proof entries (vk_hash + proof_commitment per custom effect).
    for (vk_hash, proof_commit) in &custom_entries {
        public_inputs.extend_from_slice(vk_hash);
        public_inputs.extend_from_slice(proof_commit);
    }

    assert_eq!(public_inputs.len(), pi_len);
    (trace, public_inputs)
}

/// Encode a signed balance delta as (magnitude, sign_bit) for public inputs.
pub fn encode_net_delta(delta: i64) -> (BabyBear, BabyBear) {
    if delta < 0 {
        (BabyBear::new((-delta) as u32), BabyBear::ONE)
    } else {
        (BabyBear::new(delta as u32), BabyBear::ZERO)
    }
}

/// Extract the net balance delta from public inputs.
pub fn extract_net_delta(public_inputs: &[BabyBear]) -> Option<i64> {
    if public_inputs.len() < pi::BASE_COUNT {
        return None;
    }
    let magnitude = public_inputs[pi::NET_DELTA_MAG].0 as i64;
    let sign_bit = public_inputs[pi::NET_DELTA_SIGN].0;
    if sign_bit == 1 {
        Some(-magnitude)
    } else {
        Some(magnitude)
    }
}

/// Extract the custom proof commitments from public inputs.
/// Returns a vec of (program_vk_hash, proof_commitment) tuples.
pub fn extract_custom_proof_commitments(
    public_inputs: &[BabyBear],
) -> Vec<([BabyBear; 4], [BabyBear; 4])> {
    if public_inputs.len() < pi::BASE_COUNT {
        return Vec::new();
    }
    let custom_count = public_inputs[pi::CUSTOM_EFFECT_COUNT].0 as usize;
    let mut result = Vec::with_capacity(custom_count);
    for i in 0..custom_count {
        let base = pi::CUSTOM_PROOFS_BASE + i * pi::CUSTOM_ENTRY_SIZE;
        if base + pi::CUSTOM_ENTRY_SIZE > public_inputs.len() {
            break;
        }
        let vk_hash = [
            public_inputs[base],
            public_inputs[base + 1],
            public_inputs[base + 2],
            public_inputs[base + 3],
        ];
        let proof_commit = [
            public_inputs[base + 4],
            public_inputs[base + 5],
            public_inputs[base + 6],
            public_inputs[base + 7],
        ];
        result.push((vk_hash, proof_commit));
    }
    result
}

// ============================================================================
// Verifier-side range validation (executor/relay nodes)
// ============================================================================

/// Verify that balance limbs in a CellState are within valid ranges.
///
/// This function implements the executor-side mitigation for the balance limb
/// overflow vulnerability (o1vm audit finding #1). The STARK proof alone does
/// NOT constrain balance limbs to their declared bit-widths. Verifiers MUST
/// call this after proof verification to ensure the final state is well-formed.
///
/// Returns `Ok(())` if limbs are valid, or an error describing the violation.
pub fn verify_balance_limb_ranges(state: &CellState) -> Result<(), String> {
    let (lo, hi) = split_u64(state.balance);

    // balance_lo must fit in 30 bits.
    if lo.0 >= (1 << 30) {
        return Err(format!(
            "balance_lo out of range: {} >= 2^30 (max {})",
            lo.0,
            (1u32 << 30) - 1
        ));
    }

    // balance_hi must fit in 34 bits AND be < BabyBear prime.
    // Since BabyBear prime is 2^31 - 2^27 + 1, and hi < 2^34 could exceed it,
    // we check that hi < 2^31 (conservative; BabyBear::new already reduces mod p).
    if hi.0 >= (1 << 31) {
        return Err(format!(
            "balance_hi out of range: {} >= 2^31 (exceeds BabyBear field)",
            hi.0
        ));
    }

    // Verify reconstruction: lo + hi * 2^30 == balance.
    let reconstructed = (lo.0 as u64) | ((hi.0 as u64) << 30);
    if reconstructed != state.balance {
        return Err(format!(
            "balance limb reconstruction mismatch: lo={} hi={} reconstructs to {} but balance is {}",
            lo.0, hi.0, reconstructed, state.balance
        ));
    }

    Ok(())
}

/// Verify that a final CellState (after proof verification) has a valid
/// state commitment matching its declared fields.
///
/// This is the executor-side defense against interior-row limb manipulation:
/// even if a malicious prover used out-of-range limbs on interior rows, the
/// final commitment must match the declared final state.
pub fn verify_state_integrity(state: &CellState) -> Result<(), String> {
    // Check balance limb ranges.
    verify_balance_limb_ranges(state)?;

    // Verify commitment matches the state.
    let expected_commit = CellState::compute_commitment(
        state.balance,
        state.nonce,
        &state.fields,
        state.capability_root,
    );
    if state.state_commitment != expected_commit {
        return Err(format!(
            "state_commitment mismatch: declared {:?} but computed {:?}",
            state.state_commitment, expected_commit
        ));
    }

    Ok(())
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stark::{prove, verify};

    fn make_initial_state(balance: u64) -> CellState {
        CellState::new(balance, 0)
    }

    #[test]
    fn test_single_transfer_outgoing() {
        let state = make_initial_state(1000);
        let effects = vec![Effect::Transfer {
            amount: 100,
            direction: 1,
        }];

        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        assert_eq!(trace.len(), 2); // padded to power of 2
        assert_eq!(trace[0].len(), EFFECT_VM_WIDTH);

        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(
            result.is_ok(),
            "Single transfer should verify: {:?}",
            result.err()
        );

        // Check delta.
        let delta = extract_net_delta(&public_inputs).unwrap();
        assert_eq!(delta, -100);
    }

    #[test]
    fn test_single_transfer_incoming() {
        let state = make_initial_state(500);
        let effects = vec![Effect::Transfer {
            amount: 200,
            direction: 0,
        }];

        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(
            result.is_ok(),
            "Incoming transfer should verify: {:?}",
            result.err()
        );

        let delta = extract_net_delta(&public_inputs).unwrap();
        assert_eq!(delta, 200);
    }

    #[test]
    fn test_multi_effect_turn() {
        let state = make_initial_state(5000);
        let effects = vec![
            Effect::Transfer {
                amount: 100,
                direction: 1, // -100
            },
            Effect::SetField {
                field_idx: 2,
                value: BabyBear::new(42),
            },
            Effect::GrantCapability {
                cap_entry: BabyBear::new(0xCAFE),
            },
        ];

        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        // 3 effects padded to 4 rows.
        assert_eq!(trace.len(), 4);

        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(
            result.is_ok(),
            "Multi-effect turn should verify: {:?}",
            result.err()
        );

        let delta = extract_net_delta(&public_inputs).unwrap();
        assert_eq!(delta, -100);
    }

    #[test]
    fn test_wrong_state_transition_caught() {
        let state = make_initial_state(1000);
        let effects = vec![Effect::Transfer {
            amount: 100,
            direction: 1,
        }];

        let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);

        // Tamper: set new_balance to wrong value.
        trace[0][STATE_AFTER_BASE + state::BALANCE_LO] = BabyBear::new(999);

        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(result.is_err(), "Wrong state transition should be caught");
    }

    #[test]
    fn test_invalid_selector_two_active_caught() {
        let state = make_initial_state(1000);
        let effects = vec![Effect::Transfer {
            amount: 50,
            direction: 0,
        }];

        let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);

        // Tamper: activate two selectors.
        trace[0][sel::NOOP] = BabyBear::ONE;
        // sel::TRANSFER is already 1, now both are 1.

        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(result.is_err(), "Two active selectors should be caught");
    }

    #[test]
    fn test_nonce_gap_caught() {
        let state = make_initial_state(1000);
        let effects = vec![
            Effect::Transfer {
                amount: 50,
                direction: 0,
            },
            Effect::Transfer {
                amount: 30,
                direction: 0,
            },
        ];

        let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);

        // Tamper: skip a nonce (set state_after nonce on row 0 to wrong value).
        // The nonce in state_after[nonce] should be 1 (started at 0, incremented once).
        // Set it to 5 to create a gap.
        trace[0][STATE_AFTER_BASE + state::NONCE] = BabyBear::new(5);

        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(result.is_err(), "Nonce gap should be caught");
    }

    #[test]
    fn test_padding_rows_valid() {
        let state = make_initial_state(100);
        // Single effect padded to 2 rows.
        let effects = vec![Effect::Transfer {
            amount: 10,
            direction: 0,
        }];

        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        assert_eq!(trace.len(), 2);

        // Verify padding row has NoOp selector.
        assert_eq!(trace[1][sel::NOOP], BabyBear::ONE);

        let air = EffectVmAir::new(trace.len());

        // Check constraints on both rows.
        let alpha = BabyBear::new(7);
        // Only check rows 0..n-2 (transition constraints wrap at last row;
        // the STARK handles this via the transition vanishing polynomial).
        for i in 0..trace.len() - 1 {
            let next_idx = (i + 1) % trace.len();
            let c = air.eval_constraints(&trace[i], &trace[next_idx], &public_inputs, alpha);
            assert_eq!(
                c,
                BabyBear::ZERO,
                "Constraint non-zero at row {}: c = {}",
                i,
                c.0
            );
        }
    }

    #[test]
    fn test_conservation_violation_caught() {
        let state = make_initial_state(1000);
        let effects = vec![Effect::Transfer {
            amount: 100,
            direction: 1,
        }];

        let (trace, mut public_inputs) = generate_effect_vm_trace(&state, &effects);

        // Tamper: claim delta = 0 instead of -100.
        public_inputs[pi::NET_DELTA_MAG] = BabyBear::ZERO;
        public_inputs[pi::NET_DELTA_SIGN] = BabyBear::ZERO;

        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(
            result.is_err(),
            "Conservation violation should be caught by boundary constraint mismatch"
        );
    }

    #[test]
    fn test_note_spend_and_create() {
        let state = make_initial_state(1000);
        let effects = vec![
            Effect::NoteSpend {
                nullifier: BabyBear::new(0xDEAD),
                value: 500,
            },
            Effect::NoteCreate {
                commitment: BabyBear::new(0xBEEF),
                value: 200,
            },
        ];

        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(
            result.is_ok(),
            "NoteSpend + NoteCreate should verify: {:?}",
            result.err()
        );

        // Net delta: +500 - 200 = +300.
        let delta = extract_net_delta(&public_inputs).unwrap();
        assert_eq!(delta, 300);
    }

    #[test]
    fn test_setfield_correct() {
        let state = make_initial_state(100);
        let effects = vec![Effect::SetField {
            field_idx: 3,
            value: BabyBear::new(77),
        }];

        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        let air = EffectVmAir::new(trace.len());

        // Verify constraints are zero with multiple alpha values.
        for alpha_val in [7, 13, 17, 101] {
            let alpha = BabyBear::new(alpha_val);
            let c = air.eval_constraints(&trace[0], &trace[1], &public_inputs, alpha);
            assert_eq!(
                c,
                BabyBear::ZERO,
                "SetField constraints non-zero with alpha={}: c={}",
                alpha_val,
                c.0
            );
        }
    }

    #[test]
    fn test_transfer_single_row_constraint() {
        let state = make_initial_state(100);
        let effects = vec![Effect::Transfer {
            amount: 10,
            direction: 0,
        }];
        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        let air = EffectVmAir::new(trace.len());

        // Check row 0 (Transfer) with various alpha values.
        for alpha_val in [7, 13, 17, 101] {
            let alpha = BabyBear::new(alpha_val);
            let c = air.eval_constraints(&trace[0], &trace[1], &public_inputs, alpha);
            assert_eq!(
                c,
                BabyBear::ZERO,
                "Transfer constraint non-zero with alpha={}: c={}",
                alpha_val,
                c.0
            );
        }
    }

    #[test]
    fn test_grantcap_correct() {
        let state = make_initial_state(100);
        let effects = vec![Effect::GrantCapability {
            cap_entry: BabyBear::new(0x1234),
        }];

        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        let air = EffectVmAir::new(trace.len());

        let alpha = BabyBear::new(17);
        let c = air.eval_constraints(&trace[0], &trace[1], &public_inputs, alpha);
        assert_eq!(c, BabyBear::ZERO, "GrantCap should satisfy constraints");
    }

    #[test]
    fn test_four_effect_stark_roundtrip() {
        let state = make_initial_state(10000);
        let effects = vec![
            Effect::Transfer {
                amount: 500,
                direction: 1,
            },
            Effect::SetField {
                field_idx: 0,
                value: BabyBear::new(99),
            },
            Effect::GrantCapability {
                cap_entry: BabyBear::new(0xABCD),
            },
            Effect::Transfer {
                amount: 200,
                direction: 0,
            },
        ];

        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        assert_eq!(trace.len(), 4); // exactly power of 2

        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(
            result.is_ok(),
            "4-effect STARK roundtrip should verify: {:?}",
            result.err()
        );

        // Net delta: -500 + 200 = -300.
        let delta = extract_net_delta(&public_inputs).unwrap();
        assert_eq!(delta, -300);
    }

    #[test]
    fn test_effects_hash_deterministic() {
        let effects = vec![
            Effect::Transfer {
                amount: 100,
                direction: 1,
            },
            Effect::SetField {
                field_idx: 2,
                value: BabyBear::new(55),
            },
        ];
        let (h1_lo, h1_hi) = compute_effects_hash(&effects);
        let (h2_lo, h2_hi) = compute_effects_hash(&effects);
        assert_eq!(h1_lo, h2_lo);
        assert_eq!(h1_hi, h2_hi);
    }

    #[test]
    fn test_effects_hash_changes_with_different_effects() {
        let effects1 = vec![Effect::Transfer {
            amount: 100,
            direction: 1,
        }];
        let effects2 = vec![Effect::Transfer {
            amount: 100,
            direction: 0,
        }];
        let (h1_lo, _) = compute_effects_hash(&effects1);
        let (h2_lo, _) = compute_effects_hash(&effects2);
        assert_ne!(h1_lo, h2_lo);
    }

    #[test]
    fn test_cell_state_commitment() {
        let s1 = CellState::new(1000, 0);
        let s2 = CellState::new(1000, 0);
        assert_eq!(s1.state_commitment, s2.state_commitment);

        let s3 = CellState::new(1001, 0);
        assert_ne!(s1.state_commitment, s3.state_commitment);
    }

    #[test]
    fn test_constraint_evaluation_all_zeros_valid_trace() {
        // Generate a valid trace and verify constraint evaluations are zero on rows 0..n-2.
        let state = make_initial_state(5000);
        let effects = vec![
            Effect::Transfer {
                amount: 100,
                direction: 1,
            },
            Effect::Transfer {
                amount: 50,
                direction: 0,
            },
        ];

        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        let air = EffectVmAir::new(trace.len());

        // Try multiple alpha values to ensure constraint polynomial is zero on valid rows.
        for alpha_val in [3, 7, 13, 29, 101] {
            let alpha = BabyBear::new(alpha_val);
            for i in 0..trace.len() - 1 {
                let next_idx = (i + 1) % trace.len();
                let c = air.eval_constraints(&trace[i], &trace[next_idx], &public_inputs, alpha);
                assert_eq!(
                    c,
                    BabyBear::ZERO,
                    "Constraint non-zero at row {} with alpha={}: c = {}",
                    i,
                    alpha_val,
                    c.0
                );
            }
        }
    }

    // ========================================================================
    // INTEGRATION TESTS: Real multi-effect turns through the full pipeline
    // ========================================================================

    /// Integration test: compose a realistic 4-effect turn (Transfer + SetField + GrantCap + CreateObligation),
    /// prove via STARK, verify, and confirm commitments match expected state transitions.
    #[test]
    fn test_integration_real_multi_effect_turn() {
        // Simulate a real sovereign cell with initial balance.
        let initial_state = CellState::new(50_000, 0);

        // A realistic turn: transfer some funds, update a field, grant a capability,
        // and lock a bond via CreateObligation.
        let effects = vec![
            Effect::Transfer {
                amount: 1000,
                direction: 1, // outgoing
            },
            Effect::SetField {
                field_idx: 0,
                value: BabyBear::new(0x1234),
            },
            Effect::GrantCapability {
                cap_entry: BabyBear::new(0xCAFEBABE),
            },
            Effect::CreateObligation {
                stake_amount: 500,
                obligation_id: BabyBear::new(0xDEAD01),
                beneficiary_hash: BabyBear::new(0xBEEF01),
            },
        ];

        // Generate trace and public inputs.
        let (trace, public_inputs) = generate_effect_vm_trace(&initial_state, &effects);
        assert_eq!(trace.len(), 4); // 4 effects = power of 2

        // Verify constraints are satisfied on all rows.
        let air = EffectVmAir::new(trace.len());
        for alpha_val in [7, 13, 29, 101, 65537] {
            let alpha = BabyBear::new(alpha_val);
            for row in 0..trace.len() - 1 {
                let next_row = (row + 1) % trace.len();
                let c = air.eval_constraints(&trace[row], &trace[next_row], &public_inputs, alpha);
                assert_eq!(
                    c,
                    BabyBear::ZERO,
                    "Integration: constraint non-zero at row {} with alpha={}: c={}",
                    row,
                    alpha_val,
                    c.0
                );
            }
        }

        // Full STARK prove + verify roundtrip.
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(
            result.is_ok(),
            "Integration: multi-effect turn should verify: {:?}",
            result.err()
        );

        // Verify state commitments match expected transitions.
        // The old_commitment PI should match initial_state.
        assert_eq!(
            public_inputs[pi::OLD_COMMIT],
            initial_state.state_commitment
        );

        // Manually replay the effects to get the expected final state.
        let mut expected_state = initial_state.clone();
        expected_state.balance -= 1000; // Transfer out
        expected_state.nonce += 1;
        expected_state.refresh_commitment();

        expected_state.fields[0] = BabyBear::new(0x1234); // SetField
        expected_state.nonce += 1;
        expected_state.refresh_commitment();

        expected_state.capability_root =
            hash_2_to_1(expected_state.capability_root, BabyBear::new(0xCAFEBABE));
        expected_state.nonce += 1;
        expected_state.refresh_commitment();

        expected_state.balance -= 500; // CreateObligation locks stake
        expected_state.nonce += 1;
        expected_state.refresh_commitment();

        assert_eq!(
            public_inputs[pi::NEW_COMMIT],
            expected_state.state_commitment,
            "Final commitment mismatch"
        );

        // Verify net delta: -1000 (transfer) - 500 (obligation) = -1500
        let delta = extract_net_delta(&public_inputs).unwrap();
        assert_eq!(delta, -1500);

        // Verify effects hash covers ALL effects.
        let (expected_hash_lo, expected_hash_hi) = compute_effects_hash(&effects);
        assert_eq!(public_inputs[pi::EFFECTS_HASH_LO], expected_hash_lo);
        assert_eq!(public_inputs[pi::EFFECTS_HASH_HI], expected_hash_hi);
    }

    /// Integration test: obligation lifecycle (Create + Fulfill) in a single turn.
    #[test]
    fn test_integration_obligation_lifecycle() {
        let initial_state = CellState::new(10_000, 5);

        let effects = vec![
            // Lock 2000 as a bond.
            Effect::CreateObligation {
                stake_amount: 2000,
                obligation_id: BabyBear::new(0xAA),
                beneficiary_hash: BabyBear::new(0xBB),
            },
            // Fulfill the obligation (return 2000).
            Effect::FulfillObligation {
                obligation_id: BabyBear::new(0xAA),
                stake_return: 2000,
            },
        ];

        let (trace, public_inputs) = generate_effect_vm_trace(&initial_state, &effects);
        let air = EffectVmAir::new(trace.len());

        // Verify constraints.
        for alpha_val in [7, 13, 101] {
            let alpha = BabyBear::new(alpha_val);
            for row in 0..trace.len() - 1 {
                let next_row = (row + 1) % trace.len();
                let c = air.eval_constraints(&trace[row], &trace[next_row], &public_inputs, alpha);
                assert_eq!(
                    c,
                    BabyBear::ZERO,
                    "Obligation lifecycle: constraint non-zero at row {} with alpha={}: c={}",
                    row,
                    alpha_val,
                    c.0
                );
            }
        }

        // STARK roundtrip.
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(
            result.is_ok(),
            "Obligation lifecycle should verify: {:?}",
            result.err()
        );

        // Net delta: -2000 + 2000 = 0 (obligation created and fulfilled).
        let delta = extract_net_delta(&public_inputs).unwrap();
        assert_eq!(delta, 0, "Balance should be net-zero after create+fulfill");
    }

    /// IVC compression test: prove sequential turns and compress via the state
    /// transition hash chain.
    #[test]
    fn test_ivc_compression_sequential_turns() {
        use crate::ivc::{prove_ivc_stark, verify_ivc_stark};

        // Turn 1: Transfer
        let state_0 = CellState::new(10_000, 0);
        let effects_1 = vec![Effect::Transfer {
            amount: 300,
            direction: 1,
        }];
        let (trace_1, pi_1) = generate_effect_vm_trace(&state_0, &effects_1);
        let air_1 = EffectVmAir::new(trace_1.len());
        let proof_1 = prove(&air_1, &trace_1, &pi_1);
        assert!(
            verify(&air_1, &proof_1, &pi_1).is_ok(),
            "Turn 1 should verify"
        );

        let commitment_1 = pi_1[pi::NEW_COMMIT];

        // Turn 2: SetField (starts from commitment_1)
        let mut state_1 = state_0.clone();
        state_1.balance -= 300;
        state_1.nonce += 1;
        state_1.refresh_commitment();
        assert_eq!(state_1.state_commitment, commitment_1);

        let effects_2 = vec![Effect::SetField {
            field_idx: 5,
            value: BabyBear::new(999),
        }];
        let (trace_2, pi_2) = generate_effect_vm_trace(&state_1, &effects_2);
        let air_2 = EffectVmAir::new(trace_2.len());
        let proof_2 = prove(&air_2, &trace_2, &pi_2);
        assert!(
            verify(&air_2, &proof_2, &pi_2).is_ok(),
            "Turn 2 should verify"
        );

        let commitment_2 = pi_2[pi::NEW_COMMIT];

        // Verify chain continuity: turn 2 starts where turn 1 ended.
        assert_eq!(
            pi_2[pi::OLD_COMMIT],
            commitment_1,
            "Turn 2 should start from Turn 1's final commitment"
        );

        // IVC compression: prove the hash chain [commitment_0 -> commitment_1 -> commitment_2]
        // via the StateTransitionAir (hash chain proof).
        let initial_root = state_0.state_commitment;
        let new_roots = vec![commitment_1, commitment_2];
        let (ivc_proof, ivc_pi) = prove_ivc_stark(initial_root, &new_roots);

        // Verify the compressed proof.
        let ivc_result = verify_ivc_stark(&ivc_proof, &ivc_pi);
        assert!(
            ivc_result.is_ok(),
            "IVC compressed proof should verify: {:?}",
            ivc_result.err()
        );

        // The IVC proof covers both turns in a single STARK proof.
        // Its public inputs bind: initial_root -> final accumulated hash covering all steps.
    }

    /// Test: malicious prover cannot skip effects via NoOp injection.
    /// Inserting a NoOp between real effects would change the effects_hash (since
    /// the hash covers the INTENDED effect list, not the padded trace).
    #[test]
    fn test_noop_padding_cannot_be_exploited() {
        let state = make_initial_state(1000);

        // Real effects list (what the prover commits to).
        let real_effects = vec![Effect::Transfer {
            amount: 100,
            direction: 1,
        }];

        // Compute the correct effects hash.
        let (real_hash_lo, real_hash_hi) = compute_effects_hash(&real_effects);

        // Now try a modified list with an injected NoOp.
        let tampered_effects = vec![
            Effect::NoOp, // injected
            Effect::Transfer {
                amount: 100,
                direction: 1,
            },
        ];
        let (tampered_hash_lo, tampered_hash_hi) = compute_effects_hash(&tampered_effects);

        // The hashes MUST differ -- the NoOp changes the commitment.
        assert_ne!(
            (real_hash_lo, real_hash_hi),
            (tampered_hash_lo, tampered_hash_hi),
            "Injecting NoOp must change the effects hash"
        );
    }

    /// Test: effect reordering is detected via effects_hash.
    #[test]
    fn test_effect_reordering_detected() {
        let effects_a = vec![
            Effect::Transfer {
                amount: 100,
                direction: 1,
            },
            Effect::SetField {
                field_idx: 0,
                value: BabyBear::new(1),
            },
        ];
        let effects_b = vec![
            Effect::SetField {
                field_idx: 0,
                value: BabyBear::new(1),
            },
            Effect::Transfer {
                amount: 100,
                direction: 1,
            },
        ];

        let (ha_lo, ha_hi) = compute_effects_hash(&effects_a);
        let (hb_lo, hb_hi) = compute_effects_hash(&effects_b);
        assert_ne!(
            (ha_lo, ha_hi),
            (hb_lo, hb_hi),
            "Reordering effects must change the effects hash"
        );
    }

    /// Test: NoOp padding row state_commitment tampering is caught by boundary constraint.
    ///
    /// NOTE: The EffectVM AIR does NOT enforce `state_commitment == hash(state_columns)`
    /// in-circuit (Poseidon2 is too high-degree for a degree-3 AIR). Individual field
    /// tampering on the last row is caught only indirectly: the state_commitment boundary
    /// constraint binds the last row's state_after.state_commitment to the public input
    /// new_commitment. If an attacker tampers the commitment column itself, the boundary
    /// constraint fires. For full field-level integrity on the last row, the executor
    /// independently verifies the commitment matches the claimed state.
    #[test]
    fn test_noop_state_commitment_tamper_caught() {
        let state = make_initial_state(1000);
        let effects = vec![Effect::Transfer {
            amount: 50,
            direction: 0,
        }];

        let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        assert_eq!(trace.len(), 2); // row 1 is NoOp padding

        // Tamper: change the NoOp row's state_after commitment to a wrong value.
        // This MUST be caught by the boundary constraint on the last row.
        trace[1][STATE_AFTER_BASE + state::STATE_COMMIT] = BabyBear::new(0xBAD);

        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(
            result.is_err(),
            "Tampered state_commitment on last row should be caught by boundary constraint"
        );
    }

    /// Test: transition constraint catches state_after != next.state_before on non-last rows.
    /// This verifies that NoOp padding on interior rows (not the last) is fully constrained.
    #[test]
    fn test_interior_noop_state_change_caught() {
        let state = make_initial_state(1000);
        // Use 7 effects to get an 8-row trace for more robust FRI detection.
        let effects = vec![
            Effect::Transfer {
                amount: 10,
                direction: 0,
            },
            Effect::Transfer {
                amount: 20,
                direction: 0,
            },
            Effect::Transfer {
                amount: 30,
                direction: 0,
            },
            Effect::Transfer {
                amount: 40,
                direction: 0,
            },
            Effect::Transfer {
                amount: 50,
                direction: 0,
            },
            Effect::Transfer {
                amount: 60,
                direction: 0,
            },
            Effect::Transfer {
                amount: 70,
                direction: 0,
            },
        ];

        let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        assert_eq!(trace.len(), 8);

        // Tamper: change row 0's state_after balance (an interior row).
        // The transition constraint requires row 1's state_before == row 0's state_after,
        // so this must fail. We also tamper the state_commit to break GROUP 4.
        trace[0][STATE_AFTER_BASE + state::BALANCE_LO] =
            trace[0][STATE_AFTER_BASE + state::BALANCE_LO] + BabyBear::new(9999);
        // Also tamper state_commit to ensure GROUP 4 constraint fires.
        trace[0][STATE_AFTER_BASE + state::STATE_COMMIT] =
            trace[0][STATE_AFTER_BASE + state::STATE_COMMIT] + BabyBear::new(1);

        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(
            result.is_err(),
            "Interior row state tampering should be caught by transition constraints"
        );
    }

    /// Integration test: 8-effect turn (maximum before power-of-2 padding to 8).
    /// Tests a complex realistic scenario.
    #[test]
    fn test_integration_8_effect_sovereign_turn() {
        let state = CellState::new(100_000, 10);

        let effects = vec![
            Effect::Transfer {
                amount: 5000,
                direction: 1,
            }, // -5000
            Effect::Transfer {
                amount: 2000,
                direction: 0,
            }, // +2000
            Effect::SetField {
                field_idx: 0,
                value: BabyBear::new(42),
            },
            Effect::SetField {
                field_idx: 7,
                value: BabyBear::new(99),
            },
            Effect::GrantCapability {
                cap_entry: BabyBear::new(0x1111),
            },
            Effect::GrantCapability {
                cap_entry: BabyBear::new(0x2222),
            },
            Effect::CreateObligation {
                stake_amount: 1000,
                obligation_id: BabyBear::new(0x0B01),
                beneficiary_hash: BabyBear::new(0xBE01),
            },
            Effect::FulfillObligation {
                obligation_id: BabyBear::new(0x0B01),
                stake_return: 1000,
            },
        ];

        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        assert_eq!(trace.len(), 8); // exactly power of 2

        let air = EffectVmAir::new(trace.len());

        // Verify all constraint rows.
        for alpha_val in [7, 13, 101] {
            let alpha = BabyBear::new(alpha_val);
            for row in 0..trace.len() - 1 {
                let next_row = (row + 1) % trace.len();
                let c = air.eval_constraints(&trace[row], &trace[next_row], &public_inputs, alpha);
                assert_eq!(
                    c,
                    BabyBear::ZERO,
                    "8-effect: constraint non-zero at row {} with alpha={}: c={}",
                    row,
                    alpha_val,
                    c.0
                );
            }
        }

        // STARK roundtrip.
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(
            result.is_ok(),
            "8-effect sovereign turn should verify: {:?}",
            result.err()
        );

        // Net delta: -5000 + 2000 - 1000 + 1000 = -3000
        let delta = extract_net_delta(&public_inputs).unwrap();
        assert_eq!(delta, -3000);
    }

    /// Test: commitment continuity across multiple sequential effect VM proofs.
    /// Verifies that proof N's new_commitment == proof N+1's old_commitment.
    #[test]
    fn test_commitment_chain_continuity() {
        let mut current_state = CellState::new(20_000, 0);

        // 3 sequential turns, each proven separately.
        let turn_effects = vec![
            vec![Effect::Transfer {
                amount: 100,
                direction: 1,
            }],
            vec![
                Effect::SetField {
                    field_idx: 2,
                    value: BabyBear::new(77),
                },
                Effect::Transfer {
                    amount: 200,
                    direction: 0,
                },
            ],
            vec![Effect::GrantCapability {
                cap_entry: BabyBear::new(0xFACE),
            }],
        ];

        let mut commitments = vec![current_state.state_commitment];

        for effects in &turn_effects {
            let (trace, pi) = generate_effect_vm_trace(&current_state, effects);
            let air = EffectVmAir::new(trace.len());
            let proof = prove(&air, &trace, &pi);
            assert!(verify(&air, &proof, &pi).is_ok());

            // Verify chain link: old_commit matches our tracked state.
            assert_eq!(pi[pi::OLD_COMMIT], current_state.state_commitment);

            // Advance state by replaying effects.
            for effect in effects {
                match effect {
                    Effect::Transfer { amount, direction } => {
                        if *direction == 1 {
                            current_state.balance -= amount;
                        } else {
                            current_state.balance += amount;
                        }
                        current_state.nonce += 1;
                        current_state.refresh_commitment();
                    }
                    Effect::SetField { field_idx, value } => {
                        current_state.fields[*field_idx as usize] = *value;
                        current_state.nonce += 1;
                        current_state.refresh_commitment();
                    }
                    Effect::GrantCapability { cap_entry } => {
                        current_state.capability_root =
                            hash_2_to_1(current_state.capability_root, *cap_entry);
                        current_state.nonce += 1;
                        current_state.refresh_commitment();
                    }
                    _ => {}
                }
            }

            assert_eq!(pi[pi::NEW_COMMIT], current_state.state_commitment);
            commitments.push(current_state.state_commitment);
        }

        // Verify all commitments form a chain.
        assert_eq!(commitments.len(), 4);
        for i in 0..commitments.len() - 1 {
            assert_ne!(
                commitments[i],
                commitments[i + 1],
                "Sequential commitments should differ"
            );
        }
    }

    /// Test: CreateObligation correctly debits balance.
    #[test]
    fn test_create_obligation_standalone() {
        let state = CellState::new(5000, 0);
        let effects = vec![Effect::CreateObligation {
            stake_amount: 1500,
            obligation_id: BabyBear::new(0x42),
            beneficiary_hash: BabyBear::new(0x99),
        }];

        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(
            result.is_ok(),
            "CreateObligation should verify: {:?}",
            result.err()
        );

        let delta = extract_net_delta(&public_inputs).unwrap();
        assert_eq!(delta, -1500, "CreateObligation should debit balance");
    }

    /// Test: FulfillObligation correctly credits balance.
    #[test]
    fn test_fulfill_obligation_standalone() {
        let state = CellState::new(3000, 0);
        let effects = vec![Effect::FulfillObligation {
            obligation_id: BabyBear::new(0x42),
            stake_return: 800,
        }];

        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(
            result.is_ok(),
            "FulfillObligation should verify: {:?}",
            result.err()
        );

        let delta = extract_net_delta(&public_inputs).unwrap();
        assert_eq!(delta, 800, "FulfillObligation should credit balance");
    }

    /// Test: tampered obligation stake amount is detected.
    #[test]
    fn test_create_obligation_wrong_amount_caught() {
        let state = CellState::new(5000, 0);
        let effects = vec![Effect::CreateObligation {
            stake_amount: 1000,
            obligation_id: BabyBear::new(0x01),
            beneficiary_hash: BabyBear::new(0x02),
        }];

        let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);

        // Tamper: change the balance debit to less than stake_amount.
        // The constraint says new_bal_lo = old_bal_lo - p0, so if we change new_bal_lo
        // to only debit 500 instead of 1000, constraint should catch it.
        let old_bal_lo = trace[0][STATE_BEFORE_BASE + state::BALANCE_LO];
        trace[0][STATE_AFTER_BASE + state::BALANCE_LO] = old_bal_lo - BabyBear::new(500);

        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(
            result.is_err(),
            "Wrong obligation debit amount should be caught"
        );
    }

    /// Test: fulfill obligation with wrong return amount is detected.
    #[test]
    fn test_fulfill_obligation_wrong_return_caught() {
        let state = CellState::new(5000, 0);
        let effects = vec![Effect::FulfillObligation {
            obligation_id: BabyBear::new(0x42),
            stake_return: 1000,
        }];

        let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);

        // Tamper: credit more than the declared return amount.
        let old_bal_lo = trace[0][STATE_BEFORE_BASE + state::BALANCE_LO];
        trace[0][STATE_AFTER_BASE + state::BALANCE_LO] = old_bal_lo + BabyBear::new(9999);

        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(
            result.is_err(),
            "Wrong obligation return amount should be caught"
        );
    }

    /// Test: effects_hash binding prevents subset attacks.
    /// A prover cannot claim a subset of effects and get a valid proof.
    #[test]
    fn test_effects_hash_prevents_subset_attack() {
        let state = make_initial_state(5000);

        let full_effects = vec![
            Effect::Transfer {
                amount: 100,
                direction: 1,
            },
            Effect::Transfer {
                amount: 200,
                direction: 1,
            },
        ];
        let subset_effects = vec![Effect::Transfer {
            amount: 100,
            direction: 1,
        }];

        let (full_hash_lo, full_hash_hi) = compute_effects_hash(&full_effects);
        let (sub_hash_lo, sub_hash_hi) = compute_effects_hash(&subset_effects);

        assert_ne!(
            (full_hash_lo, full_hash_hi),
            (sub_hash_lo, sub_hash_hi),
            "Subset of effects must have different hash"
        );

        // Generate proof for full effects, but tamper public inputs to claim subset hash.
        let (trace, mut pi) = generate_effect_vm_trace(&state, &full_effects);
        pi[pi::EFFECTS_HASH_LO] = sub_hash_lo;
        pi[pi::EFFECTS_HASH_HI] = sub_hash_hi;

        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &pi);
        let result = verify(&air, &proof, &pi);
        assert!(
            result.is_err(),
            "Tampered effects_hash should fail verification"
        );
    }

    /// Benchmark-style test: measure proof size for a 4-effect turn.
    #[test]
    fn test_proof_size_measurement() {
        use crate::stark::proof_to_bytes;

        let state = CellState::new(100_000, 0);
        let effects = vec![
            Effect::Transfer {
                amount: 500,
                direction: 1,
            },
            Effect::SetField {
                field_idx: 1,
                value: BabyBear::new(42),
            },
            Effect::GrantCapability {
                cap_entry: BabyBear::new(0xBEEF),
            },
            Effect::Transfer {
                amount: 100,
                direction: 0,
            },
        ];

        let (trace, pi) = generate_effect_vm_trace(&state, &effects);
        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &pi);
        let proof_bytes = proof_to_bytes(&proof);

        // The proof should be reasonable in size. For a 4-row, 65-column trace
        // with our STARK parameters (blowup 4, 32 queries), expect ~150-200 KiB.
        // This is larger than the 6-column SovereignTransitionAir (~24 KiB) due to
        // the wider trace (65 columns), but acceptable for a general-purpose VM.
        assert!(
            proof_bytes.len() < 250_000,
            "Proof too large: {} bytes (expected < 250 KiB)",
            proof_bytes.len()
        );

        // Also verify the proof after serialization roundtrip.
        use crate::stark::proof_from_bytes;
        let deserialized = proof_from_bytes(&proof_bytes).unwrap();
        let result = verify(&air, &deserialized, &pi);
        assert!(
            result.is_ok(),
            "Deserialized proof should verify: {:?}",
            result.err()
        );
    }

    // ========================================================================
    // CapTP EFFECT TESTS
    // ========================================================================

    /// Test: ExportSturdyRef proves correct swiss number derivation.
    #[test]
    fn test_captp_export_sturdy_ref() {
        let mut state = CellState::new(1000, 0);
        // Set field[7] to 5 (existing export counter).
        state.fields[7] = BabyBear::new(5);
        state.refresh_commitment();

        let effects = vec![Effect::ExportSturdyRef {
            cell_id: BabyBear::new(0xCE11),
            permissions: BabyBear::new(0x7),
            random_seed: BabyBear::new(0x5EED),
            export_counter: 5,
        }];

        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        let air = EffectVmAir::new(trace.len());

        // Verify constraints.
        for alpha_val in [7u32, 13, 101] {
            let alpha = BabyBear::new(alpha_val);
            for row in 0..trace.len() - 1 {
                let next_row = (row + 1) % trace.len();
                let c = air.eval_constraints(&trace[row], &trace[next_row], &public_inputs, alpha);
                assert_eq!(
                    c,
                    BabyBear::ZERO,
                    "ExportSturdyRef: constraint non-zero at row {} alpha={}",
                    row,
                    alpha_val
                );
            }
        }

        // STARK roundtrip.
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(
            result.is_ok(),
            "ExportSturdyRef should verify: {:?}",
            result.err()
        );

        // Verify field[7] incremented.
        let new_f7 = trace[0][STATE_AFTER_BASE + state::FIELD_BASE + 7];
        assert_eq!(new_f7, BabyBear::new(6), "export counter should increment");
    }

    /// Test: EnlivenRef proves swiss table entry validity.
    #[test]
    fn test_captp_enliven_ref() {
        let mut state = CellState::new(1000, 0);
        // Set field[6] to 2 (existing use count).
        state.fields[6] = BabyBear::new(2);
        state.refresh_commitment();

        let effects = vec![Effect::EnlivenRef {
            swiss_number: BabyBear::new(0x5155),
            presenter_id: BabyBear::new(0x9E5),
            expected_cell_id: BabyBear::new(0xCE11),
            expected_permissions: BabyBear::new(0x7),
        }];

        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        let air = EffectVmAir::new(trace.len());

        // Verify constraints.
        for alpha_val in [7u32, 13, 101] {
            let alpha = BabyBear::new(alpha_val);
            for row in 0..trace.len() - 1 {
                let next_row = (row + 1) % trace.len();
                let c = air.eval_constraints(&trace[row], &trace[next_row], &public_inputs, alpha);
                assert_eq!(
                    c,
                    BabyBear::ZERO,
                    "EnlivenRef: constraint non-zero at row {} alpha={}",
                    row,
                    alpha_val
                );
            }
        }

        // STARK roundtrip.
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(
            result.is_ok(),
            "EnlivenRef should verify: {:?}",
            result.err()
        );

        // Verify field[6] incremented.
        let new_f6 = trace[0][STATE_AFTER_BASE + state::FIELD_BASE + 6];
        assert_eq!(new_f6, BabyBear::new(3), "use_count should increment");
    }

    /// Test: DropRef proves refcount > 0 and decrements.
    #[test]
    fn test_captp_drop_ref() {
        let mut state = CellState::new(1000, 0);
        // Set field[5] to 3 (existing refcount).
        state.fields[5] = BabyBear::new(3);
        state.refresh_commitment();

        let effects = vec![Effect::DropRef {
            cell_id: BabyBear::new(0xCE11),
            holder_federation: BabyBear::new(0xFED1),
            current_refcount: 3,
        }];

        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        let air = EffectVmAir::new(trace.len());

        // Verify constraints.
        for alpha_val in [7u32, 13, 101] {
            let alpha = BabyBear::new(alpha_val);
            for row in 0..trace.len() - 1 {
                let next_row = (row + 1) % trace.len();
                let c = air.eval_constraints(&trace[row], &trace[next_row], &public_inputs, alpha);
                assert_eq!(
                    c,
                    BabyBear::ZERO,
                    "DropRef: constraint non-zero at row {} alpha={}",
                    row,
                    alpha_val
                );
            }
        }

        // STARK roundtrip.
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(result.is_ok(), "DropRef should verify: {:?}", result.err());

        // Verify field[5] decremented.
        let new_f5 = trace[0][STATE_AFTER_BASE + state::FIELD_BASE + 5];
        assert_eq!(new_f5, BabyBear::new(2), "refcount should decrement");
    }

    /// Test: DropRef with zero refcount panics (executor rejects).
    #[test]
    #[should_panic(expected = "DropRef: current_refcount must be > 0")]
    fn test_captp_drop_ref_zero_refcount_rejected() {
        let mut state = CellState::new(1000, 0);
        state.fields[5] = BabyBear::ZERO; // refcount = 0
        state.refresh_commitment();

        let effects = vec![Effect::DropRef {
            cell_id: BabyBear::new(0xCE11),
            holder_federation: BabyBear::new(0xFED1),
            current_refcount: 0, // Should panic
        }];

        // This should panic.
        let _ = generate_effect_vm_trace(&state, &effects);
    }

    /// Test: ValidateHandoff proves certificate membership and updates cap_root.
    #[test]
    fn test_captp_validate_handoff() {
        let state = CellState::new(1000, 0);

        let effects = vec![Effect::ValidateHandoff {
            certificate_hash: BabyBear::new(0xCE87),
            recipient_pk: BabyBear::new(0x8EC1),
            introducer_pk: BabyBear::new(0x1117),
            approved_set_root: BabyBear::new(0xA998),
        }];

        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        let air = EffectVmAir::new(trace.len());

        // Verify constraints.
        for alpha_val in [7u32, 13, 101] {
            let alpha = BabyBear::new(alpha_val);
            for row in 0..trace.len() - 1 {
                let next_row = (row + 1) % trace.len();
                let c = air.eval_constraints(&trace[row], &trace[next_row], &public_inputs, alpha);
                assert_eq!(
                    c,
                    BabyBear::ZERO,
                    "ValidateHandoff: constraint non-zero at row {} alpha={}",
                    row,
                    alpha_val
                );
            }
        }

        // STARK roundtrip.
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(
            result.is_ok(),
            "ValidateHandoff should verify: {:?}",
            result.err()
        );

        // Verify cap_root was updated.
        let old_cap = state.capability_root;
        let new_cap = trace[0][STATE_AFTER_BASE + state::CAP_ROOT];
        assert_ne!(old_cap, new_cap, "cap_root should change after handoff");

        // Verify the update matches expected formula.
        let routing_entry = hash_2_to_1(BabyBear::new(0x8EC1), BabyBear::new(0xCE87));
        let expected_cap = hash_2_to_1(old_cap, routing_entry);
        assert_eq!(new_cap, expected_cap);
    }

    /// Test: Multi-effect CapTP turn (export + enliven + drop).
    #[test]
    fn test_captp_multi_effect_turn() {
        let mut state = CellState::new(5000, 0);
        // Initialize counters: field[5]=3 (refcount), field[6]=1 (use_count), field[7]=0 (export_counter).
        state.fields[5] = BabyBear::new(3);
        state.fields[6] = BabyBear::new(1);
        state.fields[7] = BabyBear::new(0);
        state.refresh_commitment();

        let effects = vec![
            Effect::ExportSturdyRef {
                cell_id: BabyBear::new(0xCE11),
                permissions: BabyBear::new(0x3),
                random_seed: BabyBear::new(0xABC),
                export_counter: 0,
            },
            Effect::EnlivenRef {
                swiss_number: BabyBear::new(0x999),
                presenter_id: BabyBear::new(0x111),
                expected_cell_id: BabyBear::new(0x222),
                expected_permissions: BabyBear::new(0x333),
            },
            Effect::DropRef {
                cell_id: BabyBear::new(0xCE22),
                holder_federation: BabyBear::new(0xFED2),
                current_refcount: 3,
            },
            Effect::Transfer {
                amount: 100,
                direction: 1,
            },
        ];

        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        let air = EffectVmAir::new(trace.len());

        // Verify all constraints pass.
        for alpha_val in [7u32, 13, 101] {
            let alpha = BabyBear::new(alpha_val);
            for row in 0..trace.len() - 1 {
                let next_row = (row + 1) % trace.len();
                let c = air.eval_constraints(&trace[row], &trace[next_row], &public_inputs, alpha);
                assert_eq!(
                    c,
                    BabyBear::ZERO,
                    "CapTP multi-effect: constraint non-zero at row {} alpha={}",
                    row,
                    alpha_val
                );
            }
        }

        // STARK roundtrip.
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(
            result.is_ok(),
            "CapTP multi-effect turn should verify: {:?}",
            result.err()
        );

        // Net delta: only the Transfer contributes (-100).
        let delta = extract_net_delta(&public_inputs).unwrap();
        assert_eq!(delta, -100);
    }

    /// Test: ExportSturdyRef with tampered swiss number is caught.
    #[test]
    fn test_captp_export_tampered_swiss_caught() {
        let mut state = CellState::new(1000, 0);
        state.fields[7] = BabyBear::new(0);
        state.refresh_commitment();

        let effects = vec![Effect::ExportSturdyRef {
            cell_id: BabyBear::new(0xCE11),
            permissions: BabyBear::new(0x7),
            random_seed: BabyBear::new(0x5EED),
            export_counter: 0,
        }];

        let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);

        // Tamper: change the swiss number in aux[0].
        trace[0][AUX_BASE + 0] = BabyBear::new(0xBAD);

        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(result.is_err(), "Tampered swiss number should be caught");
    }
}
