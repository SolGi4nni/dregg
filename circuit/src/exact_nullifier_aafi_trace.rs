//! Honest main-trace marshalling for the additive exact-nullifier AAFI columns.
//!
//! This module is intentionally narrower than a live FNSP-v3 prover.  It materializes the
//! 16-row exact-AAFI band from a hostile-input-validated [`ExactAafiWitness`], including every
//! incremental state16 permutation output and its lookup tuple.  It does not invent the hidden
//! note-opening columns in the inherited FNSP-v2 band, emit/register the staged Lean descriptor,
//! or claim that the complete descriptor is satisfiable.
//!
//! Column constants mirror the guarded geometry in
//! `Dregg2.Circuit.Emit.ExactNullifierAafiDescriptorPlan`.  The tests below pin those guards and
//! recompute every covered state16 output with the same permutation used by the IR2 chip table.

use crate::descriptor_ir2::chip_permute_state16;
use crate::exact_nullifier_aafi::{
    Digest8, EXACT_LINKED_LEAF_DOMAIN, ExactAafiError, ExactAafiWitness, ExactPath4, ROOT_LANES,
    TREE_DEPTH, TaggedKeyWire, exact_empty_leaf_digest, exact_node_preimage, exact_state_preimage,
    validate_exact_aafi_witness,
};
use crate::field::BabyBear;
use crate::poseidon2::{WIDTH as STATE_LANES, hash_many_8};
use std::error::Error;
use std::fmt;

/// Inherited FNSP-v2 columns consumed by the exact additive band.
pub const VALUE_BASE: usize = 50;
pub const NULLIFIER_RAW_BASE: usize = 714;
pub const SUCCESSOR_NULLIFIER_ROOT_BASE: usize = 1014;
pub const LEVEL_COL: usize = 1022;
pub const V3_BASE: usize = 1023;

pub const LOW_ADDR_TAG: usize = V3_BASE;
pub const LOW_ADDR_BASE: usize = LOW_ADDR_TAG + 1;
pub const LOW_VALUE_BASE: usize = LOW_ADDR_BASE + 16;
pub const LOW_NEXT_TAG: usize = LOW_VALUE_BASE + 4;
pub const LOW_NEXT_BASE: usize = LOW_NEXT_TAG + 1;

pub const ROOT_CUR_BASE: usize = LOW_NEXT_BASE + 16;
pub const PRED_SIB_BASE: usize = ROOT_CUR_BASE + 4 * ROOT_LANES;
pub const PRED_POS_B0: usize = PRED_SIB_BASE + 3 * ROOT_LANES;
pub const PRED_POS_B1: usize = PRED_POS_B0 + 1;
pub const APP_SIB_BASE: usize = PRED_POS_B1 + 1;
pub const APP_POS_B0: usize = APP_SIB_BASE + 3 * ROOT_LANES;
pub const APP_POS_B1: usize = APP_POS_B0 + 1;

pub const LEX_LOW_KEY_AUX_BASE: usize = APP_POS_B1 + 1;
pub const LEX_KEY_NEXT_AUX_BASE: usize = LEX_LOW_KEY_AUX_BASE + 17;

pub const LEAF_SHARED_STATE_BASE: usize = LEX_KEY_NEXT_AUX_BASE + 17;
pub const LEAF_SHARED_STATE_STEPS: usize = 5;
pub const OLD_LEAF_STATE_BASE: usize =
    LEAF_SHARED_STATE_BASE + STATE_LANES * LEAF_SHARED_STATE_STEPS;
pub const LEAF_TAIL_STATE_STEPS: usize = 6;
pub const LOW_NEW_LEAF_STATE_BASE: usize =
    OLD_LEAF_STATE_BASE + STATE_LANES * LEAF_TAIL_STATE_STEPS;
pub const APPENDED_LEAF_STATE_BASE: usize =
    LOW_NEW_LEAF_STATE_BASE + STATE_LANES * LEAF_TAIL_STATE_STEPS;
pub const APPENDED_LEAF_STATE_STEPS: usize = 11;

pub const EXACT_NODE_STATE_STEPS: usize = 10;
pub const NODE_CHAINS_BASE: usize =
    APPENDED_LEAF_STATE_BASE + STATE_LANES * APPENDED_LEAF_STATE_STEPS;

pub const PRE_COUNT_BASE: usize = NODE_CHAINS_BASE + 4 * STATE_LANES * EXACT_NODE_STATE_STEPS;
pub const POST_COUNT_BASE: usize = PRE_COUNT_BASE + 4;
pub const CURSOR_Q_LO: usize = POST_COUNT_BASE + 4;
pub const CURSOR_Q_HI: usize = CURSOR_Q_LO + 1;
pub const RADIX_CARRY_B0: usize = CURSOR_Q_HI + 1;
pub const RADIX_CARRY_B1: usize = RADIX_CARRY_B0 + 1;
pub const COUNT_CARRY_BASE: usize = RADIX_CARRY_B1 + 1;

pub const STATE_COMMIT_STEPS: usize = 5;
pub const PRE_STATE_COMMIT_BASE: usize = COUNT_CARRY_BASE + 3;
pub const POST_STATE_COMMIT_BASE: usize = PRE_STATE_COMMIT_BASE + STATE_LANES * STATE_COMMIT_STEPS;
pub const V3_TRACE_WIDTH: usize = POST_STATE_COMMIT_BASE + STATE_LANES * STATE_COMMIT_STEPS;
pub const EXACT_AAFI_TRACE_ROWS: usize = TREE_DEPTH;
pub const EXACT_AAFI_STATE16_SITES_PER_ROW: usize = 78;
pub const EXACT_AAFI_STATE16_EVENTS: usize =
    EXACT_AAFI_TRACE_ROWS * EXACT_AAFI_STATE16_SITES_PER_ROW;

pub const fn root_cur_base(chain: usize) -> usize {
    ROOT_CUR_BASE + chain * ROOT_LANES
}

pub const fn node_state_base(chain: usize) -> usize {
    NODE_CHAINS_BASE + chain * STATE_LANES * EXACT_NODE_STATE_STEPS
}

pub const fn digest_cols(state_base: usize, absorb_chunks: usize) -> [usize; ROOT_LANES] {
    let lo = state_base + STATE_LANES * (absorb_chunks - 1);
    let hi = state_base + STATE_LANES * absorb_chunks;
    [lo, lo + 1, lo + 2, lo + 3, hi, hi + 1, hi + 2, hi + 3]
}

pub const OLD_LEAF_DIGEST_COLS: [usize; ROOT_LANES] = digest_cols(OLD_LEAF_STATE_BASE, 5);
pub const LOW_NEW_LEAF_DIGEST_COLS: [usize; ROOT_LANES] = digest_cols(LOW_NEW_LEAF_STATE_BASE, 5);
pub const APPENDED_LEAF_DIGEST_COLS: [usize; ROOT_LANES] =
    digest_cols(APPENDED_LEAF_STATE_BASE, 10);
pub const PRE_STATE_COMMIT_DIGEST_COLS: [usize; ROOT_LANES] = digest_cols(PRE_STATE_COMMIT_BASE, 4);
pub const POST_STATE_COMMIT_DIGEST_COLS: [usize; ROOT_LANES] =
    digest_cols(POST_STATE_COMMIT_BASE, 4);

pub const fn node_digest_cols(chain: usize) -> [usize; ROOT_LANES] {
    digest_cols(node_state_base(chain), 9)
}

/// One exact `[16, input_state16, output_state16]` lookup claimed by a main row.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExactAafiState16Event {
    pub main_row: usize,
    pub output_base: usize,
    pub input: [BabyBear; STATE_LANES],
    pub output: [BabyBear; STATE_LANES],
}

impl ExactAafiState16Event {
    /// The 33-felt lookup tuple consumed by `poseidon2_state16_chip`.
    pub fn lookup_tuple(self) -> [BabyBear; 1 + 2 * STATE_LANES] {
        let mut tuple = [BabyBear::ZERO; 1 + 2 * STATE_LANES];
        tuple[0] = BabyBear::new(STATE_LANES as u32);
        tuple[1..1 + STATE_LANES].copy_from_slice(&self.input);
        tuple[1 + STATE_LANES..].copy_from_slice(&self.output);
        tuple
    }

    pub fn is_genuine(self) -> bool {
        chip_permute_state16(self.input) == self.output
    }
}

/// The covered exact-AAFI main-trace band and its genuine state16 lookup keys.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactAafiTraceWitness {
    rows: Vec<Vec<BabyBear>>,
    state16_events: Vec<ExactAafiState16Event>,
}

impl ExactAafiTraceWitness {
    pub fn rows(&self) -> &[Vec<BabyBear>] {
        &self.rows
    }

    pub fn state16_events(&self) -> &[ExactAafiState16Event] {
        &self.state16_events
    }

    pub fn state16_lookup_tuples(&self) -> Vec<[BabyBear; 1 + 2 * STATE_LANES]> {
        self.state16_events
            .iter()
            .copied()
            .map(ExactAafiState16Event::lookup_tuple)
            .collect()
    }

    pub fn all_state16_events_are_genuine(&self) -> bool {
        self.state16_events
            .iter()
            .copied()
            .all(ExactAafiState16Event::is_genuine)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExactAafiTraceError {
    Semantic(ExactAafiError),
    InvalidLexWitness(&'static str),
    InternalInvariant(&'static str),
}

impl fmt::Display for ExactAafiTraceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Semantic(error) => write!(f, "invalid exact-AAFI witness: {error}"),
            Self::InvalidLexWitness(which) => {
                write!(f, "strict lexicographic witness is invalid for {which}")
            }
            Self::InternalInvariant(which) => {
                write!(f, "exact-AAFI trace marshaller invariant failed: {which}")
            }
        }
    }
}

impl Error for ExactAafiTraceError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Semantic(error) => Some(error),
            Self::InvalidLexWitness(_) | Self::InternalInvariant(_) => None,
        }
    }
}

impl From<ExactAafiError> for ExactAafiTraceError {
    fn from(value: ExactAafiError) -> Self {
        Self::Semantic(value)
    }
}

fn felt_u16(value: u16) -> BabyBear {
    BabyBear::new(u32::from(value))
}

fn limbs_to_felts<const N: usize>(limbs: [u16; N]) -> [BabyBear; N] {
    limbs.map(felt_u16)
}

fn write_block(row: &mut [BabyBear], base: usize, values: &[BabyBear]) {
    row[base..base + values.len()].copy_from_slice(values);
}

#[cfg(test)]
fn read_digest(row: &[BabyBear], cols: [usize; ROOT_LANES]) -> Digest8 {
    cols.map(|col| row[col])
}

fn leaf_preimage(addr: TaggedKeyWire, value: [u16; 4], next: TaggedKeyWire) -> Vec<BabyBear> {
    let mut out = Vec::with_capacity(39);
    out.push(BabyBear::new(EXACT_LINKED_LEAF_DOMAIN));
    out.push(BabyBear::new(u32::from(addr.tag)));
    out.extend(addr.raw_u16_le.map(felt_u16));
    out.extend(value.map(felt_u16));
    out.push(BabyBear::new(u32::from(next.tag)));
    out.extend(next.raw_u16_le.map(felt_u16));
    debug_assert_eq!(out.len(), 39);
    out
}

fn record_permutation(
    main_row: usize,
    output_base: usize,
    input: [BabyBear; STATE_LANES],
    row: &mut [BabyBear],
    events: &mut Vec<ExactAafiState16Event>,
) -> [BabyBear; STATE_LANES] {
    let output = chip_permute_state16(input);
    write_block(row, output_base, &output);
    events.push(ExactAafiState16Event {
        main_row,
        output_base,
        input,
        output,
    });
    output
}

fn initial_sponge_state(input_len: usize) -> [BabyBear; STATE_LANES] {
    let mut state = [BabyBear::ZERO; STATE_LANES];
    state[4] = BabyBear::new(input_len as u32);
    state
}

fn absorb_chunks(
    main_row: usize,
    output_base: usize,
    mut state: [BabyBear; STATE_LANES],
    inputs: &[BabyBear],
    row: &mut [BabyBear],
    events: &mut Vec<ExactAafiState16Event>,
) -> (Vec<[BabyBear; STATE_LANES]>, [BabyBear; STATE_LANES]) {
    let mut outputs = Vec::with_capacity(inputs.len().div_ceil(4));
    for (stage, chunk) in inputs.chunks(4).enumerate() {
        for (lane, value) in chunk.iter().copied().enumerate() {
            state[lane] += value;
        }
        state = record_permutation(
            main_row,
            output_base + stage * STATE_LANES,
            state,
            row,
            events,
        );
        outputs.push(state);
    }
    (outputs, state)
}

fn full_sponge_plan(
    main_row: usize,
    output_base: usize,
    preimage: &[BabyBear],
    row: &mut [BabyBear],
    events: &mut Vec<ExactAafiState16Event>,
) -> (Vec<[BabyBear; STATE_LANES]>, Digest8) {
    let (mut outputs, state) = absorb_chunks(
        main_row,
        output_base,
        initial_sponge_state(preimage.len()),
        preimage,
        row,
        events,
    );
    let squeeze_base = output_base + outputs.len() * STATE_LANES;
    let squeezed = record_permutation(main_row, squeeze_base, state, row, events);
    let low = *outputs
        .last()
        .expect("domain-separated preimages are nonempty");
    outputs.push(squeezed);
    let digest = [
        low[0],
        low[1],
        low[2],
        low[3],
        squeezed[0],
        squeezed[1],
        squeezed[2],
        squeezed[3],
    ];
    (outputs, digest)
}

fn shared_leaf_plans(
    main_row: usize,
    old_preimage: &[BabyBear],
    low_new_preimage: &[BabyBear],
    row: &mut [BabyBear],
    events: &mut Vec<ExactAafiState16Event>,
) -> Result<(Digest8, Digest8), ExactAafiTraceError> {
    if old_preimage.len() != 39
        || low_new_preimage.len() != 39
        || old_preimage[..20] != low_new_preimage[..20]
    {
        return Err(ExactAafiTraceError::InternalInvariant(
            "old/new predecessor leaf prefix",
        ));
    }

    let (_shared, shared_state) = absorb_chunks(
        main_row,
        LEAF_SHARED_STATE_BASE,
        initial_sponge_state(39),
        &old_preimage[..20],
        row,
        events,
    );

    let (mut old_outputs, old_state) = absorb_chunks(
        main_row,
        OLD_LEAF_STATE_BASE,
        shared_state,
        &old_preimage[20..],
        row,
        events,
    );
    let old_squeeze = record_permutation(
        main_row,
        OLD_LEAF_STATE_BASE + old_outputs.len() * STATE_LANES,
        old_state,
        row,
        events,
    );
    let old_low = *old_outputs
        .last()
        .ok_or(ExactAafiTraceError::InternalInvariant("old leaf tail"))?;
    old_outputs.push(old_squeeze);
    let old_digest = [
        old_low[0],
        old_low[1],
        old_low[2],
        old_low[3],
        old_squeeze[0],
        old_squeeze[1],
        old_squeeze[2],
        old_squeeze[3],
    ];

    let (mut new_outputs, new_state) = absorb_chunks(
        main_row,
        LOW_NEW_LEAF_STATE_BASE,
        shared_state,
        &low_new_preimage[20..],
        row,
        events,
    );
    let new_squeeze = record_permutation(
        main_row,
        LOW_NEW_LEAF_STATE_BASE + new_outputs.len() * STATE_LANES,
        new_state,
        row,
        events,
    );
    let new_low = *new_outputs
        .last()
        .ok_or(ExactAafiTraceError::InternalInvariant("new leaf tail"))?;
    new_outputs.push(new_squeeze);
    let new_digest = [
        new_low[0],
        new_low[1],
        new_low[2],
        new_low[3],
        new_squeeze[0],
        new_squeeze[1],
        new_squeeze[2],
        new_squeeze[3],
    ];

    Ok((old_digest, new_digest))
}

fn strict_lex_aux(
    left: [u16; 16],
    right: [u16; 16],
    which: &'static str,
) -> Result<[u16; 17], ExactAafiTraceError> {
    let first = left
        .iter()
        .zip(right.iter())
        .position(|(a, b)| a != b)
        .ok_or(ExactAafiTraceError::InvalidLexWitness(which))?;
    if left[first] >= right[first] {
        return Err(ExactAafiTraceError::InvalidLexWitness(which));
    }
    let mut aux = [0u16; 17];
    aux[first] = 1;
    aux[16] = right[first] - left[first] - 1;
    Ok(aux)
}

fn endpoint_unit_raw() -> [u16; 16] {
    let mut out = [0u16; 16];
    out[0] = 1;
    out
}

fn low_lex_aux(
    predecessor: TaggedKeyWire,
    inserted: TaggedKeyWire,
) -> Result<[u16; 17], ExactAafiTraceError> {
    let (left, right) = if predecessor.tag == 1 {
        (predecessor.raw_u16_le, inserted.raw_u16_le)
    } else {
        ([0u16; 16], endpoint_unit_raw())
    };
    strict_lex_aux(left, right, "predecessor < inserted")
}

fn next_lex_aux(
    inserted: TaggedKeyWire,
    successor: TaggedKeyWire,
) -> Result<[u16; 17], ExactAafiTraceError> {
    let (left, right) = if successor.tag == 1 {
        (inserted.raw_u16_le, successor.raw_u16_le)
    } else {
        ([0u16; 16], endpoint_unit_raw())
    };
    strict_lex_aux(left, right, "inserted < successor")
}

fn count_carries(pre: u64) -> [BabyBear; 3] {
    let limbs = [
        pre as u16,
        (pre >> 16) as u16,
        (pre >> 32) as u16,
        (pre >> 48) as u16,
    ];
    let mut carries = [BabyBear::ZERO; 3];
    let mut carry = 1u32;
    for i in 0..3 {
        let sum = u32::from(limbs[i]) + carry;
        carry = sum >> 16;
        carries[i] = BabyBear::new(carry);
    }
    carries
}

fn cursor_words(cursor: u64, row: usize) -> (u16, u16) {
    let quotient = cursor >> (2 * row);
    (quotient as u16, (quotient >> 16) as u16)
}

fn radix_carry(cursor: u64, row: usize) -> u8 {
    if row + 1 == TREE_DEPTH {
        0
    } else {
        let quotient = cursor >> (2 * row);
        ((quotient >> 16) & 3) as u8
    }
}

fn write_path_row(
    row: &mut [BabyBear],
    path: &ExactPath4,
    level: usize,
    sibling_base: usize,
    b0: usize,
    b1: usize,
) {
    for sibling in 0..3 {
        write_block(
            row,
            sibling_base + sibling * ROOT_LANES,
            &path.siblings[level][sibling],
        );
    }
    let position = path.positions[level];
    row[b0] = BabyBear::new(u32::from(position & 1));
    row[b1] = BabyBear::new(u32::from((position >> 1) & 1));
}

fn ordered_children(
    current: Digest8,
    path: &ExactPath4,
    level: usize,
) -> Result<[Digest8; 4], ExactAafiTraceError> {
    let position = usize::from(path.positions[level]);
    if position >= 4 {
        return Err(ExactAafiTraceError::InternalInvariant("path digit"));
    }
    let mut children = [[BabyBear::ZERO; ROOT_LANES]; 4];
    let mut sibling = 0;
    for (slot, child) in children.iter_mut().enumerate() {
        if slot == position {
            *child = current;
        } else {
            *child = path.siblings[level][sibling];
            sibling += 1;
        }
    }
    Ok(children)
}

/// Marshal the exact additive 16-row band after fully validating the hostile witness.
///
/// This constructor covers the exact-AAFI columns and their 1,248 incremental state16 events.
/// The inherited hidden-note FNSP-v2 witness remains a separate producer, so this return value is
/// not by itself a proof witness for the complete 2,442-column descriptor.
pub fn marshal_exact_aafi_trace(
    witness: &ExactAafiWitness,
) -> Result<ExactAafiTraceWitness, ExactAafiTraceError> {
    let validated = validate_exact_aafi_witness(witness)?;
    let inserted = witness.inserted_key;
    let predecessor = witness.predecessor;
    let successor = predecessor.next_addr;

    let old_preimage = leaf_preimage(
        predecessor.addr,
        predecessor.value_u16_le,
        predecessor.next_addr,
    );
    let low_new_preimage = leaf_preimage(
        predecessor.addr,
        predecessor.value_u16_le,
        witness.inserted_key,
    );
    let appended_preimage = leaf_preimage(
        witness.inserted_key,
        witness.inserted_value_u16_le,
        predecessor.next_addr,
    );
    let leaf_digests = [
        hash_many_8(&old_preimage),
        hash_many_8(&low_new_preimage),
        exact_empty_leaf_digest(),
        hash_many_8(&appended_preimage),
    ];

    let low_aux = limbs_to_felts(low_lex_aux(predecessor.addr, inserted)?);
    let next_aux = limbs_to_felts(next_lex_aux(inserted, successor)?);
    let pre_count = limbs_to_felts(crate::exact_nullifier_aafi::u64_to_u16_le(
        witness.prior_count,
    ));
    let post_count = limbs_to_felts(crate::exact_nullifier_aafi::u64_to_u16_le(
        witness.successor_count,
    ));
    let count_carry = count_carries(witness.prior_count);

    let mut rows = vec![vec![BabyBear::ZERO; V3_TRACE_WIDTH]; EXACT_AAFI_TRACE_ROWS];
    let mut events = Vec::with_capacity(EXACT_AAFI_STATE16_EVENTS);
    let mut current = leaf_digests;
    let mut final_parents = [[BabyBear::ZERO; ROOT_LANES]; 4];
    let mut final_pre_commit = [BabyBear::ZERO; ROOT_LANES];
    let mut final_post_commit = [BabyBear::ZERO; ROOT_LANES];

    for level in 0..EXACT_AAFI_TRACE_ROWS {
        let row = &mut rows[level];
        let event_start = events.len();

        // Inherited values consumed by the additive band.
        write_block(
            row,
            VALUE_BASE,
            &limbs_to_felts(witness.inserted_value_u16_le),
        );
        write_block(
            row,
            NULLIFIER_RAW_BASE,
            &limbs_to_felts(inserted.raw_u16_le),
        );
        write_block(row, SUCCESSOR_NULLIFIER_ROOT_BASE, &witness.successor_root);

        // Exact predecessor/tag/count/arithmetic carriers.
        row[LOW_ADDR_TAG] = BabyBear::new(u32::from(predecessor.addr.tag));
        write_block(
            row,
            LOW_ADDR_BASE,
            &limbs_to_felts(predecessor.addr.raw_u16_le),
        );
        write_block(
            row,
            LOW_VALUE_BASE,
            &limbs_to_felts(predecessor.value_u16_le),
        );
        row[LOW_NEXT_TAG] = BabyBear::new(u32::from(successor.tag));
        write_block(row, LOW_NEXT_BASE, &limbs_to_felts(successor.raw_u16_le));
        write_block(row, LEX_LOW_KEY_AUX_BASE, &low_aux);
        write_block(row, LEX_KEY_NEXT_AUX_BASE, &next_aux);
        write_block(row, PRE_COUNT_BASE, &pre_count);
        write_block(row, POST_COUNT_BASE, &post_count);
        if level == 0 {
            write_block(row, COUNT_CARRY_BASE, &count_carry);
        }
        row[LEVEL_COL] = BabyBear::new(level as u32);

        let (q_lo, q_hi) = cursor_words(witness.cursor, level);
        row[CURSOR_Q_LO] = felt_u16(q_lo);
        row[CURSOR_Q_HI] = felt_u16(q_hi);
        let radix = radix_carry(witness.cursor, level);
        row[RADIX_CARRY_B0] = BabyBear::new(u32::from(radix & 1));
        row[RADIX_CARRY_B1] = BabyBear::new(u32::from((radix >> 1) & 1));

        write_path_row(
            row,
            &witness.predecessor_path,
            level,
            PRED_SIB_BASE,
            PRED_POS_B0,
            PRED_POS_B1,
        );
        write_path_row(
            row,
            &witness.append_path,
            level,
            APP_SIB_BASE,
            APP_POS_B0,
            APP_POS_B1,
        );

        let (old_digest, low_new_digest) =
            shared_leaf_plans(level, &old_preimage, &low_new_preimage, row, &mut events)?;
        let (_appended_states, appended_digest) = full_sponge_plan(
            level,
            APPENDED_LEAF_STATE_BASE,
            &appended_preimage,
            row,
            &mut events,
        );
        if [
            old_digest,
            low_new_digest,
            exact_empty_leaf_digest(),
            appended_digest,
        ] != leaf_digests
        {
            return Err(ExactAafiTraceError::InternalInvariant(
                "leaf state16 schedule",
            ));
        }

        for chain in 0..4 {
            write_block(row, root_cur_base(chain), &current[chain]);
        }

        let mut parents = [[BabyBear::ZERO; ROOT_LANES]; 4];
        for chain in 0..4 {
            let path = if chain < 2 {
                &witness.predecessor_path
            } else {
                &witness.append_path
            };
            let children = ordered_children(current[chain], path, level)?;
            let preimage = exact_node_preimage(children);
            let (_states, parent) =
                full_sponge_plan(level, node_state_base(chain), &preimage, row, &mut events);
            parents[chain] = parent;
        }

        let pre_state_preimage = exact_state_preimage(parents[0], witness.prior_count);
        let (_pre_states, pre_commit) = full_sponge_plan(
            level,
            PRE_STATE_COMMIT_BASE,
            &pre_state_preimage,
            row,
            &mut events,
        );
        let post_state_preimage = exact_state_preimage(parents[3], witness.successor_count);
        let (_post_states, post_commit) = full_sponge_plan(
            level,
            POST_STATE_COMMIT_BASE,
            &post_state_preimage,
            row,
            &mut events,
        );

        if events.len() - event_start != EXACT_AAFI_STATE16_SITES_PER_ROW {
            return Err(ExactAafiTraceError::InternalInvariant(
                "incremental state16 site count",
            ));
        }
        current = parents;
        final_parents = parents;
        final_pre_commit = pre_commit;
        final_post_commit = post_commit;
    }

    if final_parents[0] != witness.prior_root
        || final_parents[1] != witness.middle_root
        || final_parents[2] != witness.middle_root
        || final_parents[3] != witness.successor_root
        || final_pre_commit != witness.prior_state_commit
        || final_post_commit != witness.successor_state_commit
        || validated.prior_root() != witness.prior_root
        || validated.successor_root() != witness.successor_root
    {
        return Err(ExactAafiTraceError::InternalInvariant(
            "final root/state-commit closure",
        ));
    }
    if events.len() != EXACT_AAFI_STATE16_EVENTS {
        return Err(ExactAafiTraceError::InternalInvariant(
            "total incremental state16 event count",
        ));
    }

    Ok(ExactAafiTraceWitness {
        rows,
        state16_events: events,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::exact_nullifier_aafi::ExactNullifierAafi;

    fn raw_with_first_u16(value: u16) -> [u8; 32] {
        let mut raw = [0u8; 32];
        raw[..2].copy_from_slice(&value.to_le_bytes());
        raw
    }

    #[test]
    fn lean_guarded_geometry_is_pinned() {
        assert_eq!(LOW_ADDR_TAG, 1023);
        assert_eq!(LOW_ADDR_BASE, 1024);
        assert_eq!(LOW_VALUE_BASE, 1040);
        assert_eq!(LOW_NEXT_TAG, 1044);
        assert_eq!(LOW_NEXT_BASE, 1045);
        assert_eq!(ROOT_CUR_BASE, 1061);
        assert_eq!(PRED_SIB_BASE, 1093);
        assert_eq!(APP_SIB_BASE, 1119);
        assert_eq!(LEX_LOW_KEY_AUX_BASE, 1145);
        assert_eq!(LEAF_SHARED_STATE_BASE, 1179);
        assert_eq!(OLD_LEAF_STATE_BASE, 1259);
        assert_eq!(LOW_NEW_LEAF_STATE_BASE, 1355);
        assert_eq!(APPENDED_LEAF_STATE_BASE, 1451);
        assert_eq!(NODE_CHAINS_BASE, 1627);
        assert_eq!(PRE_COUNT_BASE, 2267);
        assert_eq!(POST_COUNT_BASE, 2271);
        assert_eq!(CURSOR_Q_LO, 2275);
        assert_eq!(COUNT_CARRY_BASE, 2279);
        assert_eq!(PRE_STATE_COMMIT_BASE, 2282);
        assert_eq!(POST_STATE_COMMIT_BASE, 2362);
        assert_eq!(V3_TRACE_WIDTH, 2442);
        assert_eq!(POST_STATE_COMMIT_BASE + 5 * STATE_LANES, V3_TRACE_WIDTH);
        assert_eq!(
            OLD_LEAF_DIGEST_COLS,
            [1323, 1324, 1325, 1326, 1339, 1340, 1341, 1342]
        );
        assert_eq!(
            node_digest_cols(0),
            [1755, 1756, 1757, 1758, 1771, 1772, 1773, 1774]
        );
        assert_eq!(
            PRE_STATE_COMMIT_DIGEST_COLS,
            [2330, 2331, 2332, 2333, 2346, 2347, 2348, 2349]
        );
    }

    #[test]
    fn genesis_to_full_domain_trace_has_genuine_state16_rows() {
        let state = ExactNullifierAafi::new();
        let witness = state.prepare_insert([0xff; 32], u64::MAX).unwrap();
        let trace = marshal_exact_aafi_trace(&witness).unwrap();
        assert_eq!(trace.rows().len(), TREE_DEPTH);
        assert!(trace.rows().iter().all(|row| row.len() == V3_TRACE_WIDTH));
        assert_eq!(trace.state16_events().len(), EXACT_AAFI_STATE16_EVENTS);
        assert!(trace.all_state16_events_are_genuine());
        assert!(
            trace
                .state16_lookup_tuples()
                .iter()
                .all(|tuple| tuple[0] == BabyBear::new(16))
        );

        // Lean `exactLeafDigestReal exactGenesisLeaf` KAT.
        let genesis_digest = [
            553_521_783,
            739_395_667,
            1_064_497_434,
            1_669_175_865,
            23_127_124,
            831_993_428,
            200_020_645,
            56_289_367,
        ]
        .map(BabyBear::new);
        assert_eq!(
            read_digest(&trace.rows()[0], OLD_LEAF_DIGEST_COLS),
            genesis_digest
        );
        assert_eq!(
            read_digest(&trace.rows()[TREE_DEPTH - 1], node_digest_cols(0)),
            witness.prior_root
        );
        assert_eq!(
            read_digest(&trace.rows()[TREE_DEPTH - 1], node_digest_cols(3)),
            witness.successor_root
        );
        assert_eq!(
            read_digest(&trace.rows()[TREE_DEPTH - 1], PRE_STATE_COMMIT_DIGEST_COLS),
            witness.prior_state_commit
        );
        assert_eq!(
            read_digest(&trace.rows()[TREE_DEPTH - 1], POST_STATE_COMMIT_DIGEST_COLS),
            witness.successor_state_commit
        );
    }

    #[test]
    fn covered_events_match_the_lean_emitted_staged_descriptor() {
        use crate::descriptor_ir2::{
            TID_P2_STATE16, VmConstraint2, eval_lean_expr, parse_vm_descriptor2,
        };

        // This is the staged, unregistered, no-VK rotated descriptor emitted by Lean.  Its first
        // 50 state16 sites are the inherited hidden-note schedule; the next 78 are exactly the
        // additive AAFI plan materialized by this module.  Parsing and evaluating those emitted
        // expressions prevents the Rust constants/schedule from silently becoming a second ABI.
        const STAGED: &str = include_str!(
            "../staged-descriptors/fnsp-v3/faithful-note-spend-exact-aafi-fns3-rotated-wide-state.json"
        );
        let descriptor = parse_vm_descriptor2(STAGED).expect("Lean-emitted v3 descriptor parses");
        assert_eq!(descriptor.trace_width, 3760);
        assert_eq!(descriptor.public_input_count, 76);
        assert_eq!(descriptor.constraints.len(), 1258);
        let state16: Vec<_> = descriptor
            .constraints
            .iter()
            .filter_map(|constraint| match constraint {
                VmConstraint2::Lookup(lookup) if lookup.table == TID_P2_STATE16 => Some(lookup),
                _ => None,
            })
            .collect();
        assert_eq!(state16.len(), 128);
        let exact = &state16[50..];
        assert_eq!(exact.len(), EXACT_AAFI_STATE16_SITES_PER_ROW);

        let state = ExactNullifierAafi::new();
        let witness = state
            .prepare_insert(raw_with_first_u16(256), 0x1234)
            .unwrap();
        let trace = marshal_exact_aafi_trace(&witness).unwrap();
        for (level, row) in trace.rows().iter().enumerate() {
            let events = &trace.state16_events()[level * EXACT_AAFI_STATE16_SITES_PER_ROW
                ..(level + 1) * EXACT_AAFI_STATE16_SITES_PER_ROW];
            for (site, (lookup, event)) in exact.iter().zip(events).enumerate() {
                let emitted: Vec<_> = lookup
                    .tuple
                    .iter()
                    .map(|expression| eval_lean_expr(expression, row))
                    .collect();
                assert_eq!(
                    emitted.as_slice(),
                    event.lookup_tuple().as_slice(),
                    "emitted state16 tuple mismatch at row {level}, exact site {site}"
                );
            }
        }
    }

    #[test]
    fn nontrivial_real_real_bracket_and_two_paths_are_marshaled() {
        let mut state = ExactNullifierAafi::new();
        state.insert(raw_with_first_u16(20), 20).unwrap();
        state.insert(raw_with_first_u16(5), 5).unwrap();
        let witness = state.prepare_insert(raw_with_first_u16(10), 10).unwrap();
        let trace = marshal_exact_aafi_trace(&witness).unwrap();
        let first = &trace.rows()[0];

        assert_eq!(first[LOW_ADDR_TAG], BabyBear::ONE);
        assert_eq!(first[LOW_NEXT_TAG], BabyBear::ONE);
        assert_eq!(first[LEX_LOW_KEY_AUX_BASE], BabyBear::ONE);
        assert_eq!(first[LEX_LOW_KEY_AUX_BASE + 16], BabyBear::new(4));
        assert_eq!(first[LEX_KEY_NEXT_AUX_BASE], BabyBear::ONE);
        assert_eq!(first[LEX_KEY_NEXT_AUX_BASE + 16], BabyBear::new(9));

        // Predecessor lives in physical slot two; append cursor/count is physical slot three.
        assert_eq!(first[PRED_POS_B0], BabyBear::ZERO);
        assert_eq!(first[PRED_POS_B1], BabyBear::ONE);
        assert_eq!(first[APP_POS_B0], BabyBear::ONE);
        assert_eq!(first[APP_POS_B1], BabyBear::ONE);
        assert_eq!(first[CURSOR_Q_LO], BabyBear::new(3));
        assert_eq!(trace.rows()[1][CURSOR_Q_LO], BabyBear::ZERO);

        for level in 0..TREE_DEPTH - 1 {
            for chain in 0..4 {
                assert_eq!(
                    read_digest(&trace.rows()[level], node_digest_cols(chain)),
                    read_digest(
                        &trace.rows()[level + 1],
                        core::array::from_fn(|lane| root_cur_base(chain) + lane)
                    )
                );
            }
        }
        assert_eq!(
            read_digest(&trace.rows()[TREE_DEPTH - 1], node_digest_cols(1)),
            witness.middle_root
        );
        assert_eq!(
            read_digest(&trace.rows()[TREE_DEPTH - 1], node_digest_cols(2)),
            witness.middle_root
        );
    }

    #[test]
    fn integer_cursor_and_count_carries_match_lean_equations() {
        let cursor = 0x89ab_cdefu64;
        for row in 0..TREE_DEPTH - 1 {
            let (lo, hi) = cursor_words(cursor, row);
            let (next_lo, next_hi) = cursor_words(cursor, row + 1);
            let digit = ((cursor >> (2 * row)) & 3) as i64;
            let carry = i64::from(radix_carry(cursor, row));
            assert_eq!(
                i64::from(lo) - 4 * i64::from(next_lo) + 65_536 * carry - digit,
                0
            );
            assert_eq!(i64::from(hi) - carry - 4 * i64::from(next_hi), 0);
        }
        assert_eq!(
            count_carries(0x0000_0000_0000_ffff),
            [BabyBear::ONE, BabyBear::ZERO, BabyBear::ZERO]
        );
        assert_eq!(
            count_carries(0x0000_0000_ffff_ffff),
            [BabyBear::ONE, BabyBear::ONE, BabyBear::ZERO]
        );
    }

    #[test]
    fn malformed_hostile_witness_refuses_before_marshalling() {
        let state = ExactNullifierAafi::new();
        let mut witness = state.prepare_insert(raw_with_first_u16(1), 1).unwrap();
        witness.cursor += 1;
        assert!(matches!(
            marshal_exact_aafi_trace(&witness),
            Err(ExactAafiTraceError::Semantic(
                ExactAafiError::CursorDoesNotEqualPriorCount
            ))
        ));
    }
}
