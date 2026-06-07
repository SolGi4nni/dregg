//! Constraint-COMPLETE Plonky3 `Air` for the Effect VM — the migration of the
//! live commit-path EffectVM proof OFF the bespoke `crate::stark` (whose FRI
//! has no terminal low-degree test and never low-degree-tests the trace
//! columns) and ONTO the AUDITED `p3-batch-stark` verifier.
//!
//! ## Why this exists (the TCB-shrinking point)
//!
//! `crate::effect_vm::EffectVmAir` implements dregg's local `StarkAir`, proved
//! and verified through `stark::prove` / `stark::verify`. The node commit path
//! (`node::turn_proving::prove_and_verify_finalized_turn` →
//! `dregg_sdk::prove_turn_self_sovereign` → `prove_full_turn`) routes EVERY
//! finalized-turn proof through that unaudited verifier. This module replaces
//! that path with the real Plonky3 verifier (`p3_batch_stark::prove_batch` /
//! `verify_batch`) over the production `DreggStarkConfig` (`create_config`),
//! the same config the migrated DSL / lean-descriptor / lean-lookup AIRs use.
//!
//! ## Faithfulness to `EffectVmAir::eval_constraints` (no dropped constraints)
//!
//! [`EffectVmP3Air::eval`] is a term-for-term symbolic mirror of the bespoke
//! `EffectVmAir::eval_constraints` body (circuit/src/effect_vm/air.rs). Every
//! `combined += alpha_pow * c; alpha_pow *= alpha` fold step in the concrete
//! evaluator becomes a `builder.when_transition().assert_zero(c)` here — the
//! bespoke prover divides the WHOLE constraint polynomial by the transition
//! vanishing polynomial `Z_T` (stark.rs:1106-1164), so every constraint is
//! enforced on rows `0..n-2` exactly as `when_transition()` does. The boundary
//! pins (`EffectVmAir::boundary_constraints`) become `when_first_row()` /
//! `when_last_row()` `assert_zero`.
//!
//! ### The hash sites — REAL in-circuit Poseidon2 (the soundness upgrade)
//!
//! The bespoke evaluator computes `hash_2_to_1` / `hash_4_to_1` CONCRETELY on
//! the opened trace cells at each FRI query point. As the DSL-migration module
//! documents, a concrete hash does NOT constrain the low-degree extension — it
//! is exactly the unsound trick. Here every hash site is arithmetized through
//! the genuine [`poseidon2_permute_expr`] gadget (the same round-by-round
//! arithmetization `P3MerklePoseidon2Air` uses), each consuming one Poseidon2
//! aux block laid out after the 186 base columns in a FIXED order. The witness
//! generator [`extend_trace_with_hashes`] fills those blocks via
//! [`poseidon2_permute_aux_witness`] in the SAME order, so a forged digest is
//! UNSAT against the audited verifier.
//!
//! The hash-site order is the single source of truth [`hash_sites`], consumed
//! identically by `eval` (symbolic) and the witness generator (concrete), so
//! the two can never drift.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_batch_stark::{BatchProof, ProverData, StarkInstance, prove_batch, verify_batch};
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;

use crate::effect_vm::{
    AUX_BASE, BAL_LIMB_BITS, EFFECT_VM_WIDTH, NUM_EFFECTS, PARAM_BASE, STATE_AFTER_BASE,
    STATE_BEFORE_BASE, aux_off, param, pi, sel, state,
};
use crate::field::{BABYBEAR_P, BabyBear};
use crate::plonky3_prover::{
    DreggStarkConfig, POSEIDON2_PERM_AUX_COLS, POSEIDON2_WIDTH, create_config,
    poseidon2_permute_aux_witness, poseidon2_permute_expr, to_p3,
};

/// The Effect-VM p3 proof: a `p3-batch-stark` batch proof over the production
/// audited `DreggStarkConfig`.
pub type EffectVmP3Proof = BatchProof<DreggStarkConfig>;

// ============================================================================
// Hash-site enumeration (the single source of truth shared by eval + witness)
// ============================================================================

/// One Poseidon2 hash evaluated on a row. `arity` selects the capacity tag
/// (2 → `hash_2_to_1`, 4 → `hash_4_to_1`) and how many of `inputs` are absorbed
/// into the rate region (positions 0..arity). Inputs not absorbed are ignored.
struct HashSite {
    inputs: [usize_or_expr::Slot; 4],
    arity: u8,
}

/// A hash input is either a trace COLUMN (read on the row) or the DIGEST of an
/// earlier hash site on the SAME row (for nested hashes like
/// `hash(old_cap, hash(a, b))`). This keeps `eval` and witness-gen in lockstep
/// for nested compositions.
mod usize_or_expr {
    #[derive(Clone, Copy)]
    pub enum Slot {
        /// Trace column index on the current row.
        Col(usize),
        /// Digest of hash-site `#k` (0-based, must be < this site's index).
        Digest(usize),
        /// The constant field zero (used for `hash_2_to_1(ZERO, ZERO)` etc.).
        Zero,
    }
}
use usize_or_expr::Slot;

/// Build the ordered list of hash sites for a row. The order here is the
/// CONTRACT between [`EffectVmP3Air::eval`] and [`extend_trace_with_hashes`]:
/// both walk this list in the same order, mapping site `i` to aux block `i`.
///
/// Sites mirror, in source order, every `hash_2_to_1` / `hash_4_to_1` call in
/// `EffectVmAir::eval_constraints`. Nested calls become two sites (inner first,
/// then outer referencing the inner's digest).
fn hash_sites() -> Vec<HashSite> {
    use Slot::*;
    let fb = |i: usize| Col(STATE_AFTER_BASE + state::FIELD_BASE + i);
    let mut v: Vec<HashSite> = Vec::new();

    // ---- Group 4: state-commitment integrity (4 hash_4_to_1, UNCONDITIONAL) ----
    // inter1 = H4(after.bal_lo, after.bal_hi, after.nonce, after.field[0])
    v.push(HashSite {
        inputs: [
            Col(STATE_AFTER_BASE + state::BALANCE_LO),
            Col(STATE_AFTER_BASE + state::BALANCE_HI),
            Col(STATE_AFTER_BASE + state::NONCE),
            fb(0),
        ],
        arity: 4,
    });
    // inter2 = H4(field[1..5])
    v.push(HashSite { inputs: [fb(1), fb(2), fb(3), fb(4)], arity: 4 });
    // inter3 = H4(field[5], field[6], field[7], after.cap_root)
    v.push(HashSite {
        inputs: [fb(5), fb(6), fb(7), Col(STATE_AFTER_BASE + state::CAP_ROOT)],
        arity: 4,
    });
    // state_commit = H4(inter1, inter2, inter3, 0)
    v.push(HashSite { inputs: [Digest(0), Digest(1), Digest(2), Zero], arity: 4 });

    // ---- GrantCapability: H2(old_cap_root, cap_entry) ----  (site 4)
    v.push(HashSite {
        inputs: [
            Col(STATE_BEFORE_BASE + state::CAP_ROOT),
            Col(PARAM_BASE + param::CAP_ENTRY),
            Zero,
            Zero,
        ],
        arity: 2,
    });
    // ---- RevokeCapability: H2(old_cap_root, slot_hash) ----  (site 5)
    v.push(HashSite {
        inputs: [
            Col(STATE_BEFORE_BASE + state::CAP_ROOT),
            Col(PARAM_BASE + param::CAP_ENTRY),
            Zero,
            Zero,
        ],
        arity: 2,
    });
    // ---- CreateObligation: leaf = H2(obligation_id, beneficiary) (site 6),
    //      expected = H2(old_cap_root, leaf) (site 7) ----
    v.push(HashSite {
        inputs: [
            Col(PARAM_BASE + param::OBLIGATION_ID),
            Col(PARAM_BASE + param::OBLIGATION_BENEFICIARY),
            Zero,
            Zero,
        ],
        arity: 2,
    });
    v.push(HashSite {
        inputs: [Col(STATE_BEFORE_BASE + state::CAP_ROOT), Digest(6), Zero, Zero],
        arity: 2,
    });
    // ---- SlashObligation: H2(old_cap_root, slash_obligation_id) ---- (site 8)
    v.push(HashSite {
        inputs: [
            Col(STATE_BEFORE_BASE + state::CAP_ROOT),
            Col(PARAM_BASE + param::SLASH_OBLIGATION_ID),
            Zero,
            Zero,
        ],
        arity: 2,
    });
    // ---- ExportSturdyRef: inner = H2(random_seed, counter) (site 9),
    //      swiss = H2(cell_id, inner) (site 10) ----
    v.push(HashSite {
        inputs: [
            Col(PARAM_BASE + param::EXPORT_RANDOM_SEED),
            Col(PARAM_BASE + param::EXPORT_COUNTER),
            Zero,
            Zero,
        ],
        arity: 2,
    });
    v.push(HashSite {
        inputs: [Col(PARAM_BASE + param::EXPORT_CELL_ID), Digest(9), Zero, Zero],
        arity: 2,
    });
    // ---- EnlivenRef: inner = H2(cell_id, perms) (site 11),
    //      leaf = H2(swiss, inner) (site 12),
    //      chosen = H2(leaf, sibling) (site 13) ----
    v.push(HashSite {
        inputs: [
            Col(PARAM_BASE + param::ENLIVEN_CELL_ID),
            Col(PARAM_BASE + param::ENLIVEN_PERMISSIONS),
            Zero,
            Zero,
        ],
        arity: 2,
    });
    v.push(HashSite {
        inputs: [Col(PARAM_BASE + param::ENLIVEN_SWISS), Digest(11), Zero, Zero],
        arity: 2,
    });
    v.push(HashSite {
        inputs: [Col(AUX_BASE + 1), Col(AUX_BASE + 6), Zero, Zero],
        arity: 2,
    });
    // ---- DropRef: leaf = H2(cell_id, holder_fed) (site 14),
    //      chosen = H2(leaf, sibling) (site 15) ----
    v.push(HashSite {
        inputs: [
            Col(PARAM_BASE + param::DROP_CELL_ID),
            Col(PARAM_BASE + param::DROP_HOLDER_FED),
            Zero,
            Zero,
        ],
        arity: 2,
    });
    v.push(HashSite {
        inputs: [Col(AUX_BASE + 1), Col(AUX_BASE + 6), Zero, Zero],
        arity: 2,
    });
    // ---- ValidateHandoff: pks = H2(recipient_pk, introducer_pk) (site 16),
    //      leaf = H2(cert_hash, pks) (site 17),
    //      chosen = H2(leaf, sibling) (site 18),
    //      routing = H2(recipient_pk, cert_hash) (site 19),
    //      expected_new_cap = H2(old_cap_root, routing) (site 20) ----
    v.push(HashSite {
        inputs: [
            Col(PARAM_BASE + param::HANDOFF_RECIPIENT_PK),
            Col(PARAM_BASE + param::HANDOFF_INTRODUCER_PK),
            Zero,
            Zero,
        ],
        arity: 2,
    });
    v.push(HashSite {
        inputs: [Col(PARAM_BASE + param::HANDOFF_CERT_HASH), Digest(16), Zero, Zero],
        arity: 2,
    });
    v.push(HashSite {
        inputs: [Col(AUX_BASE + 0), Col(AUX_BASE + 1), Zero, Zero],
        arity: 2,
    });
    v.push(HashSite {
        inputs: [
            Col(PARAM_BASE + param::HANDOFF_RECIPIENT_PK),
            Col(PARAM_BASE + param::HANDOFF_CERT_HASH),
            Zero,
            Zero,
        ],
        arity: 2,
    });
    v.push(HashSite {
        inputs: [Col(STATE_BEFORE_BASE + state::CAP_ROOT), Digest(19), Zero, Zero],
        arity: 2,
    });
    // ---- AllocateQueue: empty_queue = H2(0, 0) ---- (site 21)
    v.push(HashSite { inputs: [Zero, Zero, Zero, Zero], arity: 2 });
    // ---- EnqueueMessage: new_root = H2(old_root=before.field[4], msg_hash) (22),
    //      inner = H2(sender, msg_hash) (23),
    //      expected_validation = H2(program_vk, inner) (24) ----
    v.push(HashSite {
        inputs: [
            Col(STATE_BEFORE_BASE + state::FIELD_BASE + 4),
            Col(PARAM_BASE + param::ENQUEUE_MSG_HASH),
            Zero,
            Zero,
        ],
        arity: 2,
    });
    v.push(HashSite {
        inputs: [
            Col(PARAM_BASE + param::ENQUEUE_SENDER),
            Col(PARAM_BASE + param::ENQUEUE_MSG_HASH),
            Zero,
            Zero,
        ],
        arity: 2,
    });
    v.push(HashSite {
        inputs: [Col(PARAM_BASE + param::ENQUEUE_PROGRAM_VK), Digest(23), Zero, Zero],
        arity: 2,
    });
    // ---- DequeueMessage: new_root = H2(old_root, expected_msg_hash) ---- (25)
    v.push(HashSite {
        inputs: [
            Col(STATE_BEFORE_BASE + state::FIELD_BASE + 4),
            Col(PARAM_BASE + param::DEQUEUE_EXPECTED_HASH),
            Zero,
            Zero,
        ],
        arity: 2,
    });
    // ---- AtomicQueueTx: inner = H2(combined_old, combined_new) (26),
    //      binding = H2(tx_hash, inner) (27) ----
    v.push(HashSite {
        inputs: [
            Col(PARAM_BASE + param::ATOMIC_TX_COMBINED_OLD_ROOT),
            Col(PARAM_BASE + param::ATOMIC_TX_COMBINED_NEW_ROOT),
            Zero,
            Zero,
        ],
        arity: 2,
    });
    v.push(HashSite {
        inputs: [Col(PARAM_BASE + param::ATOMIC_TX_HASH), Digest(26), Zero, Zero],
        arity: 2,
    });
    // ---- PipelineStep: expected_source_new = H2(source_old, msg_hash) ---- (28)
    v.push(HashSite {
        inputs: [
            Col(PARAM_BASE + param::PIPELINE_SOURCE_OLD_ROOT),
            Col(PARAM_BASE + param::PIPELINE_MESSAGE_HASH),
            Zero,
            Zero,
        ],
        arity: 2,
    });
    // ---- AttenuateCapability: leaf = H2(slot_hash, narrower) (29),
    //      expected = H2(old_cap_root, leaf) (30) ----
    v.push(HashSite {
        inputs: [
            Col(PARAM_BASE + param::ATTN_CAP_SLOT_HASH),
            Col(PARAM_BASE + param::ATTN_NARROWER_COMMITMENT),
            Zero,
            Zero,
        ],
        arity: 2,
    });
    v.push(HashSite {
        inputs: [Col(STATE_BEFORE_BASE + state::CAP_ROOT), Digest(29), Zero, Zero],
        arity: 2,
    });

    v
}

// Symbolic hash-site digest indices (named for readability in `eval`).
mod hs {
    pub const STATE_COMMIT: usize = 3;
    pub const GRANT_CAP: usize = 4;
    pub const REVOKE_CAP: usize = 5;
    pub const CO_EXPECTED_CAP: usize = 7;
    pub const SLASH_CAP: usize = 8;
    pub const EXPORT_SWISS: usize = 10;
    pub const ENLIVEN_LEAF: usize = 12;
    pub const ENLIVEN_CHOSEN: usize = 13;
    pub const DROP_LEAF: usize = 14;
    pub const DROP_CHOSEN: usize = 15;
    pub const HANDOFF_LEAF: usize = 17;
    pub const HANDOFF_CHOSEN: usize = 18;
    pub const HANDOFF_NEW_CAP: usize = 20;
    pub const ALLOC_EMPTY: usize = 21;
    pub const ENQUEUE_NEW_ROOT: usize = 22;
    pub const ENQUEUE_VALIDATION: usize = 24;
    pub const DEQUEUE_NEW_ROOT: usize = 25;
    pub const ATOMIC_BINDING: usize = 27;
    pub const PIPELINE_SOURCE_NEW: usize = 28;
    pub const ATTN_EXPECTED_CAP: usize = 30;
}

/// Number of hash sites (= number of Poseidon2 aux blocks per row).
fn num_hash_sites() -> usize {
    hash_sites().len()
}

/// FULL p3 trace width = base EffectVM width + one Poseidon2 aux block per site.
pub fn effect_vm_p3_width() -> usize {
    EFFECT_VM_WIDTH + num_hash_sites() * POSEIDON2_PERM_AUX_COLS
}

// ============================================================================
// The AIR
// ============================================================================

/// Constraint-complete p3 `Air` for the Effect VM. See module docs.
#[derive(Clone, Debug)]
pub struct EffectVmP3Air;

impl<F: PrimeCharacteristicRing + Sync> BaseAir<F> for EffectVmP3Air {
    fn width(&self) -> usize {
        effect_vm_p3_width()
    }
    fn num_public_values(&self) -> usize {
        pi::BASE_COUNT
    }
    fn main_next_row_columns(&self) -> Vec<usize> {
        // Transition continuity reads next.state_before for every state column.
        (STATE_BEFORE_BASE..STATE_BEFORE_BASE + state::SIZE).collect()
    }
}

/// Build the 16-wide Poseidon2 input state (as `AB::Expr`) for hash site `site`,
/// resolving `Slot::Col` from `local`, `Slot::Digest` from already-computed
/// `digests`, and `Slot::Zero` from the constant. Capacity tag at position 4 =
/// arity, matching `hash_2_to_1` (tag 2) / `hash_4_to_1` (tag 4).
fn site_input_state<AB: AirBuilder>(
    site: &HashSite,
    local: &[AB::Var],
    digests: &[AB::Expr],
) -> [AB::Expr; POSEIDON2_WIDTH] {
    let mut st: [AB::Expr; POSEIDON2_WIDTH] = core::array::from_fn(|_| AB::Expr::ZERO);
    let n = site.arity as usize;
    for i in 0..n {
        st[i] = match site.inputs[i] {
            Slot::Col(c) => local[c].into(),
            Slot::Digest(k) => digests[k].clone(),
            Slot::Zero => AB::Expr::ZERO,
        };
    }
    st[4] = AB::Expr::from_u64(site.arity as u64);
    st
}

/// Concrete sibling of [`site_input_state`] for witness generation.
fn site_input_state_concrete(
    site: &HashSite,
    row: &[BabyBear],
    digests: &[BabyBear],
) -> [BabyBear; POSEIDON2_WIDTH] {
    let mut st = [BabyBear::ZERO; POSEIDON2_WIDTH];
    let n = site.arity as usize;
    for i in 0..n {
        st[i] = match site.inputs[i] {
            Slot::Col(c) => row[c],
            Slot::Digest(k) => digests[k],
            Slot::Zero => BabyBear::ZERO,
        };
    }
    st[4] = BabyBear::new(site.arity as u32);
    st
}

impl<AB: AirBuilder> Air<AB> for EffectVmP3Air
where
    AB::F: PrimeField32,
{
    fn eval(&self, builder: &mut AB) {
        let (local, next): (Vec<AB::Var>, Vec<AB::Var>) = {
            let main = builder.main();
            (main.current_slice().to_vec(), main.next_slice().to_vec())
        };
        let pv: Vec<AB::Expr> = builder.public_values().iter().map(|&v| v.into()).collect();

        // -- Emit the real Poseidon2 permutation for every hash site, binding
        //    each digest. `digests[i]` is the output of site i, available to
        //    later sites (nested hashing) and to the constraints below. --
        let sites = hash_sites();
        let mut digests: Vec<AB::Expr> = Vec::with_capacity(sites.len());
        for (i, site) in sites.iter().enumerate() {
            let base = EFFECT_VM_WIDTH + i * POSEIDON2_PERM_AUX_COLS;
            let aux: Vec<AB::Var> = local[base..base + POSEIDON2_PERM_AUX_COLS].to_vec();
            let input = site_input_state::<AB>(site, &local, &digests);
            let d = poseidon2_permute_expr::<AB>(builder, input, &aux);
            digests.push(d);
        }

        // All Effect VM constraints hold on the transition domain (rows 0..n-2):
        // the bespoke prover divides the whole constraint polynomial by Z_T.
        let mut tb = builder.when_transition();
        let one = AB::Expr::ONE;
        let two = AB::Expr::TWO;

        // Convenience column readers.
        let lc = |i: usize| -> AB::Expr { local[i].into() };
        let nc = |i: usize| -> AB::Expr { next[i].into() };
        let sb = |i: usize| -> AB::Expr { local[STATE_BEFORE_BASE + i].into() };
        let sa = |i: usize| -> AB::Expr { local[STATE_AFTER_BASE + i].into() };
        let prm = |i: usize| -> AB::Expr { local[PARAM_BASE + i].into() };
        let aux = |i: usize| -> AB::Expr { local[AUX_BASE + i].into() };
        let fld_b = |i: usize| -> AB::Expr { sb(state::FIELD_BASE + i) };
        let fld_a = |i: usize| -> AB::Expr { sa(state::FIELD_BASE + i) };

        // ===== GROUP 1: selector validity =====
        for i in 0..NUM_EFFECTS {
            let s = lc(i);
            tb.assert_zero(s.clone() * (s - one.clone()));
        }
        let mut sel_sum = AB::Expr::ZERO;
        for i in 0..NUM_EFFECTS {
            sel_sum = sel_sum + lc(i);
        }
        tb.assert_zero(sel_sum - one.clone());

        // ===== GROUP 2a: balance-limb range / underflow (UNCONDITIONAL) =====
        {
            let mut recomposed_lo = AB::Expr::ZERO;
            for i in 0..BAL_LIMB_BITS {
                let bit = aux(aux_off::NEW_BAL_LO_BIT_BASE + i);
                tb.assert_zero(bit.clone() * (bit.clone() - one.clone()));
                recomposed_lo = recomposed_lo + bit * AB::Expr::from_u64(1u64 << i);
            }
            tb.assert_zero(recomposed_lo - sa(state::BALANCE_LO));

            let mut recomposed_hi = AB::Expr::ZERO;
            for i in 0..BAL_LIMB_BITS {
                let bit = aux(aux_off::NEW_BAL_HI_BIT_BASE + i);
                tb.assert_zero(bit.clone() * (bit.clone() - one.clone()));
                recomposed_hi = recomposed_hi + bit * AB::Expr::from_u64(1u64 << i);
            }
            tb.assert_zero(recomposed_hi - sa(state::BALANCE_HI));
        }

        // Selector / state accessors.
        let s_noop = lc(sel::NOOP);
        let s_transfer = lc(sel::TRANSFER);
        let s_setfield = lc(sel::SET_FIELD);
        let s_grantcap = lc(sel::GRANT_CAP);
        let s_notespend = lc(sel::NOTE_SPEND);
        let s_notecreate = lc(sel::NOTE_CREATE);
        let s_create_obligation = lc(sel::CREATE_OBLIGATION);
        let s_fulfill_obligation = lc(sel::FULFILL_OBLIGATION);
        let s_custom = lc(sel::CUSTOM);

        let old_bal_lo = sb(state::BALANCE_LO);
        let old_bal_hi = sb(state::BALANCE_HI);
        let old_nonce = sb(state::NONCE);
        let old_cap_root = sb(state::CAP_ROOT);
        let new_bal_lo = sa(state::BALANCE_LO);
        let new_bal_hi = sa(state::BALANCE_HI);
        let new_nonce = sa(state::NONCE);
        let new_cap_root = sa(state::CAP_ROOT);

        let p0 = prm(0);
        let p1 = prm(1);

        // -- NoOp: state passthrough --
        for i in 0..state::SIZE {
            tb.assert_zero(s_noop.clone() * (sa(i) - sb(i)));
        }

        // -- Transfer --
        let direction = p1.clone();
        let amount = p0.clone();
        tb.assert_zero(
            s_transfer.clone()
                * (new_bal_lo.clone() - old_bal_lo.clone() - amount.clone()
                    + two.clone() * direction.clone() * amount.clone()),
        );
        tb.assert_zero(s_transfer.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
        tb.assert_zero(
            s_transfer.clone() * direction.clone() * (direction.clone() - one.clone()),
        );
        for i in [state::CAP_ROOT, state::RESERVED] {
            tb.assert_zero(s_transfer.clone() * (sa(i) - sb(i)));
        }
        for i in 0..8 {
            tb.assert_zero(s_transfer.clone() * (fld_a(i) - fld_b(i)));
        }

        // -- SetField --
        let field_index = p0.clone();
        let new_value = p1.clone();
        for j in 0..8u32 {
            tb.assert_zero(
                s_setfield.clone()
                    * (field_index.clone() - AB::Expr::from_u64(j as u64))
                    * (fld_a(j as usize) - fld_b(j as usize)),
            );
        }
        let old_value_at_idx = aux(0);
        let mut field_diff_sum = AB::Expr::ZERO;
        for j in 0..8 {
            field_diff_sum = field_diff_sum + (fld_a(j) - fld_b(j));
        }
        tb.assert_zero(
            s_setfield.clone() * (field_diff_sum - (new_value.clone() - old_value_at_idx)),
        );
        tb.assert_zero(s_setfield.clone() * (new_bal_lo.clone() - old_bal_lo.clone()));
        tb.assert_zero(s_setfield.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
        tb.assert_zero(s_setfield.clone() * (new_cap_root.clone() - old_cap_root.clone()));
        tb.assert_zero(
            s_setfield.clone() * (sa(state::RESERVED) - sb(state::RESERVED)),
        );
        // reserved bit-decomposition (UNCONDITIONAL booleanity + decomposition).
        let bbits: [AB::Expr; 8] = core::array::from_fn(|i| aux(aux_off::RESERVED_BIT_0 + i));
        let mode_bit = aux(aux_off::RESERVED_MODE);
        for bit in bbits.iter().cloned().chain(core::iter::once(mode_bit.clone())) {
            tb.assert_zero(bit.clone() * (bit - one.clone()));
        }
        let mut reconstructed = AB::Expr::ZERO;
        for (i, b) in bbits.iter().enumerate() {
            reconstructed = reconstructed + b.clone() * AB::Expr::from_u64(1u64 << i);
        }
        reconstructed = reconstructed + mode_bit.clone() * AB::Expr::from_u64(256);
        tb.assert_zero(reconstructed - sb(state::RESERVED));
        // Lagrange-basis bit selection at an index expression.
        let lagrange_bit = |x: &AB::Expr| -> AB::Expr {
            let mut acc = AB::Expr::ZERO;
            for k in 0..8usize {
                let mut num = one.clone();
                let mut den = BabyBear::ONE;
                for j in 0..8usize {
                    if j == k {
                        continue;
                    }
                    num = num * (x.clone() - AB::Expr::from_u64(j as u64));
                    let diff = if k > j {
                        BabyBear::new((k - j) as u32)
                    } else {
                        BabyBear::ZERO - BabyBear::new((j - k) as u32)
                    };
                    den = den * diff;
                }
                let den_inv = den.inverse().expect("Lagrange denom nonzero on {0..7}");
                acc = acc + num * lift::<AB>(den_inv) * bbits[k].clone();
            }
            acc
        };
        let bit_at_idx = lagrange_bit(&field_index);
        tb.assert_zero(s_setfield.clone() * bit_at_idx);
        let s_seal = lc(sel::SEAL);
        let s_unseal = lc(sel::UNSEAL);
        let seal_bit_at_idx = lagrange_bit(&prm(param::SEAL_FIELD_IDX));
        tb.assert_zero(s_seal.clone() * seal_bit_at_idx);
        let unseal_bit_at_idx = lagrange_bit(&prm(param::UNSEAL_FIELD_IDX));
        tb.assert_zero(s_unseal.clone() * (unseal_bit_at_idx - one.clone()));
        // SetField field_idx range {0..7}.
        {
            let mut prod = one.clone();
            for k in 0..8u32 {
                prod = prod * (field_index.clone() - AB::Expr::from_u64(k as u64));
            }
            tb.assert_zero(s_setfield.clone() * prod);
        }

        // -- GrantCapability (hash site 4) --
        tb.assert_zero(
            s_grantcap.clone() * (new_cap_root.clone() - digests[hs::GRANT_CAP].clone()),
        );
        tb.assert_zero(s_grantcap.clone() * (new_bal_lo.clone() - old_bal_lo.clone()));
        tb.assert_zero(s_grantcap.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
        for i in 0..8 {
            tb.assert_zero(s_grantcap.clone() * (fld_a(i) - fld_b(i)));
        }

        // -- EmitEvent --
        let s_emitevent = lc(sel::EMIT_EVENT);
        tb.assert_zero(s_emitevent.clone() * (new_bal_lo.clone() - old_bal_lo.clone()));
        tb.assert_zero(s_emitevent.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
        tb.assert_zero(s_emitevent.clone() * (new_cap_root.clone() - old_cap_root.clone()));
        for i in 0..8 {
            tb.assert_zero(s_emitevent.clone() * (fld_a(i) - fld_b(i)));
        }
        for i in 0..4 {
            tb.assert_zero(
                s_emitevent.clone() * (prm(i) - pv[pi::EMIT_EVENT_TOPIC_HASH_BASE + i].clone()),
            );
        }
        for i in 0..4 {
            tb.assert_zero(
                s_emitevent.clone()
                    * (prm(4 + i) - pv[pi::EMIT_EVENT_PAYLOAD_HASH_BASE + i].clone()),
            );
        }

        // -- Passthrough effects that only touch balance/cap/fields (no hash,
        //    no reserved equality — mirrors the bespoke variants that pass
        //    balance+cap+8 fields through). Inline via a local macro so it
        //    borrows `tb` directly (the filtered builder is not nameable as an
        //    associated type). --
        macro_rules! passthrough_bal_cap_fields {
            ($s:expr) => {{
                let s: AB::Expr = $s;
                tb.assert_zero(s.clone() * (new_bal_lo.clone() - old_bal_lo.clone()));
                tb.assert_zero(s.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
                tb.assert_zero(s.clone() * (new_cap_root.clone() - old_cap_root.clone()));
                for i in 0..8 {
                    tb.assert_zero(s.clone() * (fld_a(i) - fld_b(i)));
                }
            }};
        }

        // SetPermissions / SetVerificationKey.
        passthrough_bal_cap_fields!(lc(sel::SET_PERMISSIONS));
        passthrough_bal_cap_fields!(lc(sel::SET_VERIFICATION_KEY));

        // Stage 3 passthrough batch.
        for s_sel_idx in [
            sel::CREATE_SEAL_PAIR,
            sel::REFRESH_DELEGATION,
            sel::INCREMENT_NONCE,
            sel::REVOKE_DELEGATION,
            sel::CREATE_CELL,
            sel::SPAWN_WITH_DELEGATION,
            sel::BRIDGE_CANCEL,
            sel::EXERCISE_VIA_CAPABILITY,
            sel::INTRODUCE,
            sel::PIPELINED_SEND,
            sel::CREATE_COMMITTED_ESCROW,
            sel::BRIDGE_FINALIZE,
            sel::RELEASE_ESCROW,
            sel::REFUND_ESCROW,
            sel::RELEASE_COMMITTED_ESCROW,
            sel::REFUND_COMMITTED_ESCROW,
        ] {
            passthrough_bal_cap_fields!(lc(s_sel_idx));
        }

        // -- RevokeCapability (hash site 5) --
        let s_revokecap = lc(sel::REVOKE_CAPABILITY);
        tb.assert_zero(
            s_revokecap.clone() * (new_cap_root.clone() - digests[hs::REVOKE_CAP].clone()),
        );
        tb.assert_zero(s_revokecap.clone() * (new_bal_lo.clone() - old_bal_lo.clone()));
        tb.assert_zero(s_revokecap.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
        for i in 0..8 {
            tb.assert_zero(s_revokecap.clone() * (fld_a(i) - fld_b(i)));
        }

        // -- NoteSpend --
        let note_val_lo = p1.clone();
        tb.assert_zero(
            s_notespend.clone() * (new_bal_lo.clone() - old_bal_lo.clone() - note_val_lo),
        );
        tb.assert_zero(s_notespend.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
        tb.assert_zero(s_notespend.clone() * (new_cap_root.clone() - old_cap_root.clone()));
        for i in 0..8 {
            tb.assert_zero(s_notespend.clone() * (fld_a(i) - fld_b(i)));
        }
        tb.assert_zero(
            s_notespend.clone()
                * (prm(param::NULLIFIER) - pv[pi::NOTESPEND_NULLIFIER].clone()),
        );
        // D5b NoteCreate commitment cross-binding.
        tb.assert_zero(
            s_notecreate.clone()
                * (prm(param::NOTE_COMMITMENT) - pv[pi::NOTECREATE_COMMITMENT].clone()),
        );
        // D5c Burn target cross-binding.
        let s_burn = lc(sel::BURN);
        tb.assert_zero(
            s_burn.clone() * (prm(param::BURN_TARGET) - pv[pi::BURN_TARGET_PI].clone()),
        );

        // -- NoteCreate --
        let nc_val_lo = p1.clone();
        tb.assert_zero(
            s_notecreate.clone() * (new_bal_lo.clone() - old_bal_lo.clone() + nc_val_lo),
        );
        tb.assert_zero(s_notecreate.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
        tb.assert_zero(s_notecreate.clone() * (new_cap_root.clone() - old_cap_root.clone()));
        for i in 0..8 {
            tb.assert_zero(s_notecreate.clone() * (fld_a(i) - fld_b(i)));
        }

        // -- BridgeMint --
        let s_bridgemint = lc(sel::BRIDGE_MINT);
        let bm_val_lo = prm(1);
        tb.assert_zero(
            s_bridgemint.clone() * (new_bal_lo.clone() - old_bal_lo.clone() - bm_val_lo),
        );
        tb.assert_zero(s_bridgemint.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
        tb.assert_zero(s_bridgemint.clone() * (new_cap_root.clone() - old_cap_root.clone()));
        for i in 0..8 {
            tb.assert_zero(s_bridgemint.clone() * (fld_a(i) - fld_b(i)));
        }

        // -- CreateEscrow / BridgeLock --
        for s_sel_idx in [sel::CREATE_ESCROW, sel::BRIDGE_LOCK] {
            let s_v = lc(s_sel_idx);
            let amount_lo = prm(1);
            tb.assert_zero(
                s_v.clone() * (new_bal_lo.clone() - old_bal_lo.clone() + amount_lo),
            );
            tb.assert_zero(s_v.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
            tb.assert_zero(s_v.clone() * (new_cap_root.clone() - old_cap_root.clone()));
            for i in 0..8 {
                tb.assert_zero(s_v.clone() * (fld_a(i) - fld_b(i)));
            }
        }

        // -- CreateObligation (hash sites 6,7) --
        let stake_lo = p0.clone();
        tb.assert_zero(
            s_create_obligation.clone() * (new_bal_lo.clone() - old_bal_lo.clone() + stake_lo),
        );
        tb.assert_zero(
            s_create_obligation.clone() * (new_bal_hi.clone() - old_bal_hi.clone()),
        );
        tb.assert_zero(
            s_create_obligation.clone()
                * (new_cap_root.clone() - digests[hs::CO_EXPECTED_CAP].clone()),
        );
        for i in 0..8 {
            tb.assert_zero(s_create_obligation.clone() * (fld_a(i) - fld_b(i)));
        }

        // -- FulfillObligation --
        let return_lo = p1.clone();
        tb.assert_zero(
            s_fulfill_obligation.clone() * (new_bal_lo.clone() - old_bal_lo.clone() - return_lo),
        );
        tb.assert_zero(
            s_fulfill_obligation.clone() * (new_bal_hi.clone() - old_bal_hi.clone()),
        );
        tb.assert_zero(
            s_fulfill_obligation.clone() * (new_cap_root.clone() - old_cap_root.clone()),
        );
        for i in 0..8 {
            tb.assert_zero(s_fulfill_obligation.clone() * (fld_a(i) - fld_b(i)));
        }

        // -- Custom: state passthrough (no reserved equality; nonce ticks global) --
        tb.assert_zero(s_custom.clone() * (new_bal_lo.clone() - old_bal_lo.clone()));
        tb.assert_zero(s_custom.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
        tb.assert_zero(s_custom.clone() * (new_cap_root.clone() - old_cap_root.clone()));
        for i in 0..8 {
            tb.assert_zero(s_custom.clone() * (fld_a(i) - fld_b(i)));
        }
        tb.assert_zero(
            s_custom.clone() * (sa(state::RESERVED) - sb(state::RESERVED)),
        );

        // -- SlashObligation (hash site 8) --
        let s_slash = lc(sel::SLASH_OBLIGATION);
        let slash_stake_lo = prm(param::SLASH_STAKE_LO);
        tb.assert_zero(
            s_slash.clone() * (new_bal_lo.clone() - old_bal_lo.clone() - slash_stake_lo),
        );
        tb.assert_zero(s_slash.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
        tb.assert_zero(
            s_slash.clone() * (new_cap_root.clone() - digests[hs::SLASH_CAP].clone()),
        );
        for i in 0..8 {
            tb.assert_zero(s_slash.clone() * (fld_a(i) - fld_b(i)));
        }

        // -- Seal / Unseal pow2 lagrange helper --
        let lagrange_pow2 = |x: &AB::Expr| -> AB::Expr {
            let mut result = AB::Expr::ZERO;
            for k in 0..8u32 {
                let mut num = one.clone();
                let mut den = BabyBear::ONE;
                for j in 0..8u32 {
                    if j == k {
                        continue;
                    }
                    num = num * (x.clone() - AB::Expr::from_u64(j as u64));
                    let diff = if k > j {
                        BabyBear::new(k - j)
                    } else {
                        BabyBear::ZERO - BabyBear::new(j - k)
                    };
                    den = den * diff;
                }
                let den_inv = den.inverse().expect("Lagrange denom nonzero on {0..7}");
                result = result + num * lift::<AB>(den_inv) * AB::Expr::from_u64(1u64 << k);
            }
            result
        };

        // -- Seal --
        let old_reserved_seal = sb(state::RESERVED);
        let new_reserved_seal = sa(state::RESERVED);
        let seal_pow2 = aux(aux_off::SEAL_POW2_IDX);
        tb.assert_zero(s_seal.clone() * (new_bal_lo.clone() - old_bal_lo.clone()));
        tb.assert_zero(s_seal.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
        tb.assert_zero(s_seal.clone() * (new_cap_root.clone() - old_cap_root.clone()));
        for i in 0..8 {
            tb.assert_zero(s_seal.clone() * (fld_a(i) - fld_b(i)));
        }
        tb.assert_zero(
            s_seal.clone() * (new_reserved_seal - old_reserved_seal - seal_pow2.clone()),
        );
        tb.assert_zero(
            s_seal.clone() * (seal_pow2 - lagrange_pow2(&prm(param::SEAL_FIELD_IDX))),
        );
        {
            let seal_field_idx = prm(param::SEAL_FIELD_IDX);
            let mut prod = one.clone();
            for k in 0..8u32 {
                prod = prod * (seal_field_idx.clone() - AB::Expr::from_u64(k as u64));
            }
            tb.assert_zero(s_seal.clone() * prod);
        }

        // -- Unseal --
        let old_reserved_unseal = sb(state::RESERVED);
        let new_reserved_unseal = sa(state::RESERVED);
        let unseal_pow2 = aux(aux_off::SEAL_POW2_IDX);
        tb.assert_zero(s_unseal.clone() * (new_bal_lo.clone() - old_bal_lo.clone()));
        tb.assert_zero(s_unseal.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
        tb.assert_zero(s_unseal.clone() * (new_cap_root.clone() - old_cap_root.clone()));
        for i in 0..8 {
            tb.assert_zero(s_unseal.clone() * (fld_a(i) - fld_b(i)));
        }
        tb.assert_zero(
            s_unseal.clone() * (old_reserved_unseal - new_reserved_unseal - unseal_pow2.clone()),
        );
        tb.assert_zero(
            s_unseal.clone() * (unseal_pow2 - lagrange_pow2(&prm(param::UNSEAL_FIELD_IDX))),
        );
        {
            let unseal_field_idx = prm(param::UNSEAL_FIELD_IDX);
            let mut prod = one.clone();
            for k in 0..8u32 {
                prod = prod * (unseal_field_idx.clone() - AB::Expr::from_u64(k as u64));
            }
            tb.assert_zero(s_unseal.clone() * prod);
        }

        // -- MakeSovereign --
        let s_makesov = lc(sel::MAKE_SOVEREIGN);
        let old_reserved = sb(state::RESERVED);
        let new_reserved = sa(state::RESERVED);
        tb.assert_zero(
            s_makesov.clone() * (new_reserved - old_reserved - AB::Expr::from_u64(256)),
        );
        tb.assert_zero(s_makesov.clone() * mode_bit.clone());
        tb.assert_zero(s_makesov.clone() * (new_bal_lo.clone() - old_bal_lo.clone()));
        tb.assert_zero(s_makesov.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
        tb.assert_zero(s_makesov.clone() * (new_cap_root.clone() - old_cap_root.clone()));
        for i in 0..8 {
            tb.assert_zero(s_makesov.clone() * (fld_a(i) - fld_b(i)));
        }

        // -- CreateCellFromFactory --
        let s_factory = lc(sel::CREATE_CELL_FROM_FACTORY);
        tb.assert_zero(s_factory.clone() * (new_bal_lo.clone() - old_bal_lo.clone()));
        tb.assert_zero(s_factory.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
        tb.assert_zero(s_factory.clone() * (new_cap_root.clone() - old_cap_root.clone()));
        for i in 0..8 {
            tb.assert_zero(s_factory.clone() * (fld_a(i) - fld_b(i)));
        }
        tb.assert_zero(
            s_factory.clone() * (sa(state::RESERVED) - sb(state::RESERVED)),
        );

        // -- ExportSturdyRef (hash sites 9,10) --
        let s_export = lc(sel::EXPORT_STURDY_REF);
        {
            let aux_swiss = aux(0);
            tb.assert_zero(
                s_export.clone() * (aux_swiss - digests[hs::EXPORT_SWISS].clone()),
            );
            tb.assert_zero(
                s_export.clone()
                    * (fld_a(7) - fld_b(7) - one.clone()),
            );
            tb.assert_zero(s_export.clone() * (new_bal_lo.clone() - old_bal_lo.clone()));
            tb.assert_zero(s_export.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
            tb.assert_zero(s_export.clone() * (new_cap_root.clone() - old_cap_root.clone()));
            for i in 0..7 {
                tb.assert_zero(s_export.clone() * (fld_a(i) - fld_b(i)));
            }
        }

        // -- EnlivenRef (hash sites 11,12,13) --
        let s_enliven = lc(sel::ENLIVEN_REF);
        {
            let aux_root = aux(0);
            let aux_leaf = aux(1);
            tb.assert_zero(
                s_enliven.clone() * (aux_leaf - digests[hs::ENLIVEN_LEAF].clone()),
            );
            let aux_chosen = aux(7);
            tb.assert_zero(
                s_enliven.clone() * (aux_chosen.clone() - digests[hs::ENLIVEN_CHOSEN].clone()),
            );
            tb.assert_zero(s_enliven.clone() * (aux_root.clone() - fld_a(4)));
            tb.assert_zero(s_enliven.clone() * (aux_chosen - aux_root));
            tb.assert_zero(s_enliven.clone() * (aux(6) - fld_b(4)));
            tb.assert_zero(
                s_enliven.clone() * (fld_a(6) - fld_b(6) - one.clone()),
            );
            tb.assert_zero(s_enliven.clone() * (new_bal_lo.clone() - old_bal_lo.clone()));
            tb.assert_zero(s_enliven.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
            tb.assert_zero(s_enliven.clone() * (new_cap_root.clone() - old_cap_root.clone()));
            for i in [0usize, 1, 2, 3, 5, 7] {
                tb.assert_zero(s_enliven.clone() * (fld_a(i) - fld_b(i)));
            }
        }

        // -- DropRef (hash sites 14,15) --
        let s_drop = lc(sel::DROP_REF);
        {
            let refcount_param = prm(param::DROP_REFCOUNT);
            tb.assert_zero(
                s_drop.clone() * (fld_a(5) - fld_b(5) + one.clone()),
            );
            tb.assert_zero(s_drop.clone() * (refcount_param.clone() - fld_b(5)));
            let rc_inv = aux(0);
            tb.assert_zero(
                s_drop.clone() * (refcount_param * rc_inv - one.clone()),
            );
            let aux_leaf = aux(1);
            tb.assert_zero(s_drop.clone() * (aux_leaf - digests[hs::DROP_LEAF].clone()));
            let aux_chosen = aux(7);
            tb.assert_zero(
                s_drop.clone() * (aux_chosen.clone() - digests[hs::DROP_CHOSEN].clone()),
            );
            tb.assert_zero(s_drop.clone() * (aux_chosen - fld_a(3)));
            tb.assert_zero(s_drop.clone() * (aux(6) - fld_b(3)));
            tb.assert_zero(s_drop.clone() * (new_bal_lo.clone() - old_bal_lo.clone()));
            tb.assert_zero(s_drop.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
            tb.assert_zero(s_drop.clone() * (new_cap_root.clone() - old_cap_root.clone()));
            for i in [0usize, 1, 2, 4, 6, 7] {
                tb.assert_zero(s_drop.clone() * (fld_a(i) - fld_b(i)));
            }
        }

        // -- ValidateHandoff (hash sites 16..20) --
        let s_handoff = lc(sel::VALIDATE_HANDOFF);
        {
            let approved_root = prm(param::HANDOFF_APPROVED_SET_ROOT);
            let aux_leaf = aux(0);
            tb.assert_zero(s_handoff.clone() * (aux_leaf - digests[hs::HANDOFF_LEAF].clone()));
            let aux_chosen = aux(6);
            tb.assert_zero(
                s_handoff.clone() * (aux_chosen.clone() - digests[hs::HANDOFF_CHOSEN].clone()),
            );
            tb.assert_zero(s_handoff.clone() * (aux_chosen - approved_root.clone()));
            tb.assert_zero(
                s_handoff.clone() * (approved_root - pv[pi::APPROVED_HANDOFFS_BASE].clone()),
            );
            tb.assert_zero(
                s_handoff.clone() * (new_cap_root.clone() - digests[hs::HANDOFF_NEW_CAP].clone()),
            );
            tb.assert_zero(s_handoff.clone() * (new_bal_lo.clone() - old_bal_lo.clone()));
            tb.assert_zero(s_handoff.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
            for i in 0..8 {
                tb.assert_zero(s_handoff.clone() * (fld_a(i) - fld_b(i)));
            }
        }

        // -- AllocateQueue (hash site 21) --
        let s_alloc_queue = lc(sel::ALLOCATE_QUEUE);
        {
            let capacity = prm(param::QUEUE_CAPACITY);
            let cost_per_slot = prm(param::QUEUE_COST_PER_SLOT);
            let alloc_cost = capacity * cost_per_slot;
            tb.assert_zero(
                s_alloc_queue.clone() * (new_bal_lo.clone() - old_bal_lo.clone() + alloc_cost),
            );
            tb.assert_zero(s_alloc_queue.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
            tb.assert_zero(
                s_alloc_queue.clone() * (fld_a(4) - digests[hs::ALLOC_EMPTY].clone()),
            );
            tb.assert_zero(s_alloc_queue.clone() * (new_cap_root.clone() - old_cap_root.clone()));
            for i in 0..4 {
                tb.assert_zero(s_alloc_queue.clone() * (fld_a(i) - fld_b(i)));
            }
            for i in 5..8 {
                tb.assert_zero(s_alloc_queue.clone() * (fld_a(i) - fld_b(i)));
            }
        }

        // -- EnqueueMessage (hash sites 22,23,24) --
        let s_enqueue = lc(sel::ENQUEUE_MESSAGE);
        {
            let deposit = prm(param::ENQUEUE_DEPOSIT);
            tb.assert_zero(
                s_enqueue.clone() * (fld_a(4) - digests[hs::ENQUEUE_NEW_ROOT].clone()),
            );
            tb.assert_zero(
                s_enqueue.clone() * (new_bal_lo.clone() - old_bal_lo.clone() + deposit),
            );
            tb.assert_zero(s_enqueue.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
            tb.assert_zero(s_enqueue.clone() * (new_cap_root.clone() - old_cap_root.clone()));
            for i in 0..4 {
                tb.assert_zero(s_enqueue.clone() * (fld_a(i) - fld_b(i)));
            }
            for i in 5..8 {
                tb.assert_zero(s_enqueue.clone() * (fld_a(i) - fld_b(i)));
            }
            let program_vk = prm(param::ENQUEUE_PROGRAM_VK);
            let validation_hash = aux(6);
            let program_vk_inv = aux(7);
            tb.assert_zero(
                s_enqueue.clone()
                    * program_vk.clone()
                    * (validation_hash.clone() - digests[hs::ENQUEUE_VALIDATION].clone()),
            );
            tb.assert_zero(
                s_enqueue.clone()
                    * (one.clone() - program_vk * program_vk_inv)
                    * validation_hash,
            );
        }

        // -- DequeueMessage (hash site 25) --
        let s_dequeue = lc(sel::DEQUEUE_MESSAGE);
        {
            let expected_msg_hash = prm(param::DEQUEUE_EXPECTED_HASH);
            let deposit_refund = prm(param::DEQUEUE_DEPOSIT_REFUND);
            tb.assert_zero(
                s_dequeue.clone() * (fld_a(4) - digests[hs::DEQUEUE_NEW_ROOT].clone()),
            );
            let msg_inv = aux(1);
            tb.assert_zero(
                s_dequeue.clone() * (expected_msg_hash * msg_inv - one.clone()),
            );
            tb.assert_zero(
                s_dequeue.clone() * (new_bal_lo.clone() - old_bal_lo.clone() - deposit_refund),
            );
            tb.assert_zero(s_dequeue.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
            tb.assert_zero(s_dequeue.clone() * (new_cap_root.clone() - old_cap_root.clone()));
            for i in 0..4 {
                tb.assert_zero(s_dequeue.clone() * (fld_a(i) - fld_b(i)));
            }
            for i in 5..8 {
                tb.assert_zero(s_dequeue.clone() * (fld_a(i) - fld_b(i)));
            }
        }

        // -- ResizeQueue (no hash) --
        let s_resize = lc(sel::RESIZE_QUEUE);
        {
            let new_capacity = prm(param::RESIZE_NEW_CAPACITY);
            let old_capacity = prm(param::RESIZE_OLD_CAPACITY);
            let cost_per_slot = prm(param::RESIZE_COST_PER_SLOT);
            let delta_sign = aux(aux_off::RESIZE_DELTA_SIGN);
            let delta_mag = aux(aux_off::RESIZE_DELTA_MAG);
            tb.assert_zero(
                s_resize.clone() * delta_sign.clone() * (delta_sign.clone() - one.clone()),
            );
            tb.assert_zero(
                s_resize.clone()
                    * ((new_capacity.clone() - old_capacity)
                        - delta_mag.clone() * (one.clone() - two.clone() * delta_sign.clone())),
            );
            let resize_cost = delta_mag * cost_per_slot * (one.clone() - delta_sign);
            tb.assert_zero(
                s_resize.clone() * (new_bal_lo.clone() - old_bal_lo.clone() + resize_cost),
            );
            tb.assert_zero(s_resize.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
            tb.assert_zero(s_resize.clone() * (fld_a(5) - new_capacity));
            tb.assert_zero(s_resize.clone() * (new_cap_root.clone() - old_cap_root.clone()));
            tb.assert_zero(s_resize.clone() * (fld_a(4) - fld_b(4)));
            for i in 0..4 {
                tb.assert_zero(s_resize.clone() * (fld_a(i) - fld_b(i)));
            }
            for i in 6..8 {
                tb.assert_zero(s_resize.clone() * (fld_a(i) - fld_b(i)));
            }
        }

        // -- AtomicQueueTx (hash sites 26,27) --
        let s_atomic_tx = lc(sel::ATOMIC_QUEUE_TX);
        {
            let combined_old = prm(param::ATOMIC_TX_COMBINED_OLD_ROOT);
            let combined_new = prm(param::ATOMIC_TX_COMBINED_NEW_ROOT);
            let net_deposit = prm(param::ATOMIC_TX_NET_DEPOSIT);
            tb.assert_zero(s_atomic_tx.clone() * (fld_b(4) - combined_old));
            tb.assert_zero(s_atomic_tx.clone() * (fld_a(4) - combined_new));
            let aux_binding = aux(0);
            tb.assert_zero(
                s_atomic_tx.clone() * (aux_binding - digests[hs::ATOMIC_BINDING].clone()),
            );
            tb.assert_zero(
                s_atomic_tx.clone() * (new_bal_lo.clone() - old_bal_lo.clone() + net_deposit),
            );
            tb.assert_zero(s_atomic_tx.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
            tb.assert_zero(s_atomic_tx.clone() * (new_cap_root.clone() - old_cap_root.clone()));
            for i in 0..4 {
                tb.assert_zero(s_atomic_tx.clone() * (fld_a(i) - fld_b(i)));
            }
            for i in 5..8 {
                tb.assert_zero(s_atomic_tx.clone() * (fld_a(i) - fld_b(i)));
            }
        }

        // -- PipelineStep (hash site 28) --
        let s_pipeline = lc(sel::PIPELINE_STEP);
        {
            let pipeline_id_val = prm(param::PIPELINE_ID);
            let source_old = prm(param::PIPELINE_SOURCE_OLD_ROOT);
            let source_new = prm(param::PIPELINE_SOURCE_NEW_ROOT);
            let sink_new = prm(param::PIPELINE_SINK_NEW_ROOT);
            let pipeline_id_inv = aux(6);
            tb.assert_zero(
                s_pipeline.clone() * (pipeline_id_val * pipeline_id_inv - one.clone()),
            );
            tb.assert_zero(
                s_pipeline.clone()
                    * (source_new.clone() - digests[hs::PIPELINE_SOURCE_NEW].clone()),
            );
            let aux_expected = aux(0);
            tb.assert_zero(
                s_pipeline.clone() * (aux_expected - digests[hs::PIPELINE_SOURCE_NEW].clone()),
            );
            tb.assert_zero(s_pipeline.clone() * (fld_b(4) - source_old));
            tb.assert_zero(s_pipeline.clone() * (fld_a(4) - source_new));
            let aux_sink = aux(1);
            tb.assert_zero(s_pipeline.clone() * (aux_sink - sink_new));
            tb.assert_zero(s_pipeline.clone() * (new_bal_lo.clone() - old_bal_lo.clone()));
            tb.assert_zero(s_pipeline.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
            tb.assert_zero(s_pipeline.clone() * (new_cap_root.clone() - old_cap_root.clone()));
            for i in 0..4 {
                tb.assert_zero(s_pipeline.clone() * (fld_a(i) - fld_b(i)));
            }
            for i in 5..8 {
                tb.assert_zero(s_pipeline.clone() * (fld_a(i) - fld_b(i)));
            }
        }

        // -- Burn --
        {
            let burn_amount = prm(param::BURN_AMOUNT_LO);
            let burn_flag = prm(param::BURN_WAS_BURN_FLAG);
            tb.assert_zero(
                s_burn.clone() * (new_bal_lo.clone() - old_bal_lo.clone() + burn_amount),
            );
            tb.assert_zero(s_burn.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
            tb.assert_zero(s_burn.clone() * (burn_flag - one.clone()));
            tb.assert_zero(s_burn.clone() * (new_cap_root.clone() - old_cap_root.clone()));
            for i in 0..8 {
                tb.assert_zero(s_burn.clone() * (fld_a(i) - fld_b(i)));
            }
            tb.assert_zero(
                s_burn.clone() * (sa(state::RESERVED) - sb(state::RESERVED)),
            );
        }

        // -- CellDestroy --
        let s_cell_destroy = lc(sel::CELL_DESTROY);
        {
            tb.assert_zero(s_cell_destroy.clone() * (new_bal_lo.clone() - old_bal_lo.clone()));
            tb.assert_zero(s_cell_destroy.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
            tb.assert_zero(s_cell_destroy.clone() * (new_cap_root.clone() - old_cap_root.clone()));
            for i in 0..8 {
                tb.assert_zero(s_cell_destroy.clone() * (fld_a(i) - fld_b(i)));
            }
            tb.assert_zero(
                s_cell_destroy.clone() * (sa(state::RESERVED) - sb(state::RESERVED)),
            );
        }

        // -- AttenuateCapability (hash sites 29,30) --
        let s_attn_cap = lc(sel::ATTENUATE_CAPABILITY);
        {
            tb.assert_zero(
                s_attn_cap.clone() * (new_cap_root.clone() - digests[hs::ATTN_EXPECTED_CAP].clone()),
            );
            tb.assert_zero(s_attn_cap.clone() * (new_bal_lo.clone() - old_bal_lo.clone()));
            tb.assert_zero(s_attn_cap.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
            for i in 0..8 {
                tb.assert_zero(s_attn_cap.clone() * (fld_a(i) - fld_b(i)));
            }
            tb.assert_zero(
                s_attn_cap.clone() * (sa(state::RESERVED) - sb(state::RESERVED)),
            );
        }

        // -- CellSeal --
        let s_cell_seal = lc(sel::CELL_SEAL);
        {
            tb.assert_zero(s_cell_seal.clone() * (new_bal_lo.clone() - old_bal_lo.clone()));
            tb.assert_zero(s_cell_seal.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
            tb.assert_zero(s_cell_seal.clone() * (new_cap_root.clone() - old_cap_root.clone()));
            for i in 0..8 {
                tb.assert_zero(s_cell_seal.clone() * (fld_a(i) - fld_b(i)));
            }
            tb.assert_zero(
                s_cell_seal.clone() * (sa(state::RESERVED) - sb(state::RESERVED)),
            );
        }

        // -- CellUnseal --
        let s_cell_unseal = lc(sel::CELL_UNSEAL);
        {
            tb.assert_zero(
                s_cell_unseal.clone() * (prm(param::CELL_UNSEAL_TARGET) - aux(0)),
            );
            tb.assert_zero(s_cell_unseal.clone() * (new_bal_lo.clone() - old_bal_lo.clone()));
            tb.assert_zero(s_cell_unseal.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
            tb.assert_zero(s_cell_unseal.clone() * (new_cap_root.clone() - old_cap_root.clone()));
            for i in 0..8 {
                tb.assert_zero(s_cell_unseal.clone() * (fld_a(i) - fld_b(i)));
            }
            tb.assert_zero(
                s_cell_unseal.clone() * (sa(state::RESERVED) - sb(state::RESERVED)),
            );
        }

        // -- ReceiptArchive --
        let s_receipt_archive = lc(sel::RECEIPT_ARCHIVE);
        {
            tb.assert_zero(s_receipt_archive.clone() * (new_bal_lo.clone() - old_bal_lo.clone()));
            tb.assert_zero(s_receipt_archive.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
            tb.assert_zero(
                s_receipt_archive.clone() * (new_cap_root.clone() - old_cap_root.clone()),
            );
            for i in 0..8 {
                tb.assert_zero(s_receipt_archive.clone() * (fld_a(i) - fld_b(i)));
            }
            tb.assert_zero(
                s_receipt_archive.clone() * (sa(state::RESERVED) - sb(state::RESERVED)),
            );
        }

        // -- Refusal --
        let s_refusal = lc(sel::REFUSAL);
        {
            tb.assert_zero(s_refusal.clone() * (new_bal_lo.clone() - old_bal_lo.clone()));
            tb.assert_zero(s_refusal.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
            tb.assert_zero(s_refusal.clone() * (new_cap_root.clone() - old_cap_root.clone()));
            for i in 0..8 {
                tb.assert_zero(s_refusal.clone() * (fld_a(i) - fld_b(i)));
            }
            tb.assert_zero(
                s_refusal.clone() * (sa(state::RESERVED) - sb(state::RESERVED)),
            );
        }

        // ===== GROUP 3: transition continuity (next.before == this.after) =====
        for i in 0..state::SIZE {
            tb.assert_zero(nc(STATE_BEFORE_BASE + i) - sa(i));
        }

        // ===== Nonce increment: new_nonce == old_nonce + (1 - s_noop) =====
        tb.assert_zero(new_nonce - old_nonce - (one.clone() - s_noop.clone()));

        // ===== GROUP 4: state-commit integrity (hash sites 0..3) =====
        tb.assert_zero(sa(state::STATE_COMMIT) - digests[hs::STATE_COMMIT].clone());
        // The intermediate aux columns must equal their hashes (binds inter1..3).
        tb.assert_zero(aux(aux_off::STATE_INTER1) - digests[0].clone());
        tb.assert_zero(aux(aux_off::STATE_INTER2) - digests[1].clone());
        tb.assert_zero(aux(aux_off::STATE_INTER3) - digests[2].clone());

        // ===== GROUP 5: net_delta sign boolean =====
        {
            let delta_sign = aux(3);
            tb.assert_zero(delta_sign.clone() * (delta_sign - one.clone()));
        }

        // ===== GROUP 6: PI net_delta algebraic binding =====
        {
            let init_lo = pv[pi::INIT_BAL_LO].clone();
            let init_hi = pv[pi::INIT_BAL_HI].clone();
            let final_lo = pv[pi::FINAL_BAL_LO].clone();
            let final_hi = pv[pi::FINAL_BAL_HI].clone();
            let mag = pv[pi::NET_DELTA_MAG].clone();
            let sign = pv[pi::NET_DELTA_SIGN].clone();
            let two_pow_30 = AB::Expr::from_u64(1u64 << 30);
            let actual_delta = (final_lo - init_lo) + (final_hi - init_hi) * two_pow_30;
            let signed_delta = mag * (one.clone() - two.clone() * sign);
            tb.assert_zero(actual_delta - signed_delta);
        }

        // ===== GROUP 7: custom-effect count exclusive running sum =====
        {
            let this_acc = aux(aux_off::CUSTOM_COUNT_ACC);
            let next_acc = nc(AUX_BASE + aux_off::CUSTOM_COUNT_ACC);
            let this_s_custom = lc(sel::CUSTOM);
            tb.assert_zero(next_acc - this_acc - this_s_custom);
        }

        // ====================================================================
        // BOUNDARY constraints (mirror EffectVmAir::boundary_constraints).
        // ====================================================================
        let mut fb_ = builder.when_first_row();
        fb_.assert_zero(lc(STATE_BEFORE_BASE + state::STATE_COMMIT) - pv[pi::OLD_COMMIT].clone());
        fb_.assert_zero(lc(AUX_BASE + 2) - pv[pi::NET_DELTA_MAG].clone());
        fb_.assert_zero(lc(AUX_BASE + 3) - pv[pi::NET_DELTA_SIGN].clone());
        fb_.assert_zero(lc(STATE_BEFORE_BASE + state::BALANCE_LO) - pv[pi::INIT_BAL_LO].clone());
        fb_.assert_zero(lc(STATE_BEFORE_BASE + state::BALANCE_HI) - pv[pi::INIT_BAL_HI].clone());
        fb_.assert_zero(lc(AUX_BASE + 4) - pv[pi::EFFECTS_HASH_BASE].clone());
        fb_.assert_zero(lc(AUX_BASE + 5) - pv[pi::EFFECTS_HASH_BASE + 1].clone());
        fb_.assert_zero(lc(AUX_BASE + aux_off::CUSTOM_COUNT_ACC));

        let mut lb = builder.when_last_row();
        lb.assert_zero(lc(STATE_AFTER_BASE + state::STATE_COMMIT) - pv[pi::NEW_COMMIT].clone());
        lb.assert_zero(lc(STATE_AFTER_BASE + state::BALANCE_LO) - pv[pi::FINAL_BAL_LO].clone());
        lb.assert_zero(lc(STATE_AFTER_BASE + state::BALANCE_HI) - pv[pi::FINAL_BAL_HI].clone());
    }
}

/// Lift a `BabyBear` into an `AB::Expr`. BabyBear < p < 2^31, so `from_u64` is
/// exact and canonical.
fn lift<AB: AirBuilder>(v: BabyBear) -> AB::Expr {
    let _ = BABYBEAR_P; // keep the import meaningful / documents the modulus bound
    AB::Expr::from_u64(v.0 as u64)
}

// ============================================================================
// Witness extension (concrete Poseidon2 aux blocks, in hash-site order)
// ============================================================================

/// Extend each base-width (`EFFECT_VM_WIDTH`) trace row with one Poseidon2 aux
/// block per hash site, in [`hash_sites`] order — the same order `eval`
/// consumes them. Nested sites read earlier sites' digests, matching the
/// symbolic `digests` chain exactly.
pub fn extend_trace_with_hashes(trace: &[Vec<BabyBear>]) -> Vec<Vec<BabyBear>> {
    let sites = hash_sites();
    trace
        .iter()
        .map(|row| {
            let mut full = row.clone();
            let mut digests: Vec<BabyBear> = Vec::with_capacity(sites.len());
            for site in &sites {
                let input = site_input_state_concrete(site, row, &digests);
                let auxw = poseidon2_permute_aux_witness(input);
                // The digest the gadget binds is the LAST round's state[0]:
                // poseidon2_permute_aux_witness returns rounds 0..=TOTAL_ROUNDS,
                // each WIDTH wide; the final block's [0] is the permutation output.
                let digest = auxw[auxw.len() - POSEIDON2_WIDTH];
                digests.push(digest);
                full.extend(auxw);
            }
            full
        })
        .collect()
}

fn to_matrix(trace: &[Vec<BabyBear>]) -> RowMajorMatrix<P3BabyBear> {
    let width = trace[0].len();
    let values: Vec<P3BabyBear> = trace
        .iter()
        .flat_map(|row| row.iter().map(|&v| to_p3(v)))
        .collect();
    RowMajorMatrix::new(values, width)
}

/// Errors from the Effect-VM p3 path.
#[derive(Debug, Clone)]
pub enum EffectVmP3Error {
    /// The audited Plonky3 verifier rejected the proof.
    VerificationFailed(String),
}

impl core::fmt::Display for EffectVmP3Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            EffectVmP3Error::VerificationFailed(r) => write!(f, "p3 verification failed: {r}"),
        }
    }
}
impl std::error::Error for EffectVmP3Error {}

/// Prove an Effect-VM trace through the AUDITED Plonky3 prover (`p3-batch-stark`).
///
/// `base_trace` is the bespoke EffectVM trace (width `EFFECT_VM_WIDTH`,
/// power-of-two height ≥ 64); it is extended with Poseidon2 aux blocks here.
/// The proof self-verifies before return, so a returned proof is one the
/// audited verifier accepts.
pub fn prove_effect_vm_p3(
    base_trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
) -> Result<EffectVmP3Proof, EffectVmP3Error> {
    let air = EffectVmP3Air;
    let config = create_config();
    let full_trace = extend_trace_with_hashes(base_trace);
    let matrix = to_matrix(&full_trace);
    let pis: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();

    let instances = vec![StarkInstance {
        air: &air,
        trace: &matrix,
        public_values: pis.clone(),
    }];
    let prover_data = ProverData::from_instances(&config, &instances);
    let common = &prover_data.common;
    let proof = prove_batch(&config, &instances, &prover_data);

    let airs = vec![air];
    let pvs = vec![pis];
    verify_batch(&config, &airs, &proof, &pvs, common)
        .map_err(|e| EffectVmP3Error::VerificationFailed(format!("{e:?}")))?;
    Ok(proof)
}

/// Verify an Effect-VM p3 proof through the AUDITED Plonky3 verifier. The
/// verifier reconstructs `CommonData` from the AIR + the proof's degree bits;
/// it needs no witness.
pub fn verify_effect_vm_p3(
    proof: &EffectVmP3Proof,
    public_inputs: &[BabyBear],
) -> Result<(), EffectVmP3Error> {
    let air = EffectVmP3Air;
    let config = create_config();
    let pis: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();
    let airs = vec![air];
    let pvs = vec![pis];
    let common = ProverData::from_airs_and_degrees(&config, &airs, &proof.degree_bits).common;
    verify_batch(&config, &airs, proof, &pvs, &common)
        .map_err(|e| EffectVmP3Error::VerificationFailed(format!("{e:?}")))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::effect_vm::{CellState, Effect as VmEffect, generate_effect_vm_trace, pi};

    /// Honest self-sovereign Transfer turn proves + verifies through the
    /// AUDITED p3 verifier.
    #[test]
    fn transfer_turn_proves_and_verifies_through_audited_p3() {
        let initial = CellState::new(1000, 0);
        let effects = vec![VmEffect::Transfer { amount: 100, direction: 1 }];
        let (trace, pis) = generate_effect_vm_trace(&initial, &effects);
        let proof = prove_effect_vm_p3(&trace, &pis)
            .expect("honest Effect VM turn must prove+verify through audited p3");
        verify_effect_vm_p3(&proof, &pis).expect("audited p3 verify accepts honest proof");
    }

    /// THE ANTI-GHOST TOOTH on the audited verifier: a forged post-state
    /// commitment (NEW_COMMIT public input flipped) MUST be rejected.
    #[test]
    fn forged_post_state_commit_rejected_by_audited_p3() {
        let initial = CellState::new(1000, 0);
        let effects = vec![VmEffect::Transfer { amount: 100, direction: 1 }];
        let (trace, pis) = generate_effect_vm_trace(&initial, &effects);
        let proof = prove_effect_vm_p3(&trace, &pis).expect("honest proof");

        // Forge the published post-state commitment.
        let mut forged = pis.clone();
        forged[pi::NEW_COMMIT] = forged[pi::NEW_COMMIT] + BabyBear::new(1);
        let res = verify_effect_vm_p3(&proof, &forged);
        assert!(
            res.is_err(),
            "forged NEW_COMMIT MUST be rejected by the audited p3 verifier"
        );
    }

    /// A forged FINAL_BAL public input (not matching the trace's last-row
    /// balance) MUST be rejected by the last-row boundary.
    #[test]
    fn forged_final_balance_rejected_by_audited_p3() {
        let initial = CellState::new(1000, 0);
        let effects = vec![VmEffect::Transfer { amount: 100, direction: 1 }];
        let (trace, pis) = generate_effect_vm_trace(&initial, &effects);
        let proof = prove_effect_vm_p3(&trace, &pis).expect("honest proof");

        let mut forged = pis.clone();
        forged[pi::FINAL_BAL_LO] = forged[pi::FINAL_BAL_LO] + BabyBear::new(7);
        let res = verify_effect_vm_p3(&proof, &forged);
        assert!(res.is_err(), "forged FINAL_BAL_LO MUST be rejected");
    }
}
