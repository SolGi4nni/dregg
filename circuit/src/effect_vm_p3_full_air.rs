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
//! EXCEPTION (anti-ghost, intentional): the GROUP-4 post-state-commitment
//! integrity binding (`STATE_COMMIT == genuine Poseidon2 digest of the
//! after-state`) is emitted on the WHOLE domain via the unfiltered `builder`,
//! NOT `when_transition`, so it covers the LAST row (n-1) too. The last row's
//! STATE_COMMIT is the published commitment; if this binding were skipped there
//! (as a careless `when_transition` mirror would), it would be pinned ONLY to
//! the attacker-chosen `NEW_COMMIT` public input — an arbitrary post-state
//! commitment could be forged and the audited verifier would accept. The hash
//! sites' `poseidon2_permute_expr` round constraints are likewise unfiltered
//! (emitted in the digest loop via `builder`), so the full digest dependency
//! chain is last-row-sound. See `forged_last_row_state_commit_trace_cell_*`.
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

use crate::cap_root::CAP_TREE_DEPTH;
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
    // ---- AttenuateCapability ----
    // Phase B: the cap_root advance is NO LONGER a pinned 2-of-2 digest fold.
    // It is a GENUINE sorted-tree membership-open (held leaf authenticated
    // against old_cap_root) + leaf-update (granted leaf folded up the SAME path
    // to new_cap_root), emitted in a DEDICATED block of Poseidon2 sites laid out
    // after the generic sites (see [`attn`] + [`emit_attenuate_hashes`]). The
    // generic site list therefore ends at PipelineStep (site 28); Attenuate adds
    // no generic sites.

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
}

/// Number of hash sites (= number of Poseidon2 aux blocks per row).
fn num_hash_sites() -> usize {
    hash_sites().len()
}

// ============================================================================
// Cap non-amplification — Phase B (AttenuateCapability, the reference) +
// Phase B2 (GrantCapability granter-side delegation rows, which REUSE this
// entire block: the same scalar witness columns, the same dedicated Poseidon2
// chain, and the same order gates, fired on sel 3 × direction. Grant differs
// only in the cap_root move — passthrough, the granter's tree is unchanged —
// and in binding params[0] to the granted leaf digest instead of forcing the
// in-place leaf-update.)
// ============================================================================
//
// A verifying AttenuateCapability proof IMPLIES `granted ⊑ held` (no
// amplification on EITHER lattice + monotone expiry), with `held` AUTHENTICATED
// against `old_cap_root` (the seeded openable sorted-Poseidon2 capability tree,
// `cap_root.rs`). Five teeth, all gated by `sel::ATTENUATE_CAPABILITY`:
//
//   1. MEMBERSHIP-OPEN: the held leaf
//        H_many[slot_hash, target, held_auth_tag, held_mask_lo, held_mask_hi,
//               held_expiry, breadstuff]
//      is opened (depth-`CAP_TREE_DEPTH` `hash_fact` path) against
//      `state_before.cap_root`. A sorted tree has exactly one leaf per slot, so
//      this authenticates the held rights — they are the real committed ones,
//      not adversary-chosen. (Forgery 3.)
//   2. LEAF-UPDATE + ROOT RECOMPUTE: the granted (narrowed) leaf — same
//      slot_hash/target/breadstuff, narrowed rights — is folded up the SAME
//      sibling path to `state_after.cap_root`. This REPLACES the pinned-digest
//      advance: the circuit forces the canonical sorted-tree root move.
//   3. SUBMASK (EffectMask facet order): `granted_mask & held_mask == granted_mask`
//      on the 16+16 bit-decomposed mask limbs. (Forgery 1.)
//   4. AUTHREQUIRED LATTICE (the partial order, NOT a numeric ≤): an
//      admissible-(granted_tag, held_tag) selector table over the 6 tier bytes
//      encoding EXACTLY `AuthRequired::is_narrower_or_equal` — it rejects
//      strict-superset AND INCOMPARABLE pairs ({Signature} vs {Proof}). A
//      vk-equality sub-gate fires when both tags are `Custom`. (Forgeries 2, 4.)
//   5. EXPIRY-MONOTONE: `granted_expiry ⊑ held_expiry` over the encoded-expiry
//      lattice (`None`=⊤ broadest; finite shrink-only). (Matches
//      `attenuate_in_place`.)
//
// All other selectors keep FREEZING cap_root (their own constraints, unchanged).
pub mod attn {
    use super::POSEIDON2_PERM_AUX_COLS;
    use super::{EFFECT_VM_WIDTH, num_hash_sites};
    use crate::cap_root::CAP_TREE_DEPTH;

    /// Number of bits decomposing each 16-bit mask limb (lo / hi).
    pub const MASK_LIMB_BITS: usize = 16;
    /// Range-check bit-width for the expiry-monotone GTE gadget. BabyBear
    /// `(p-1)/2 < 2^30`, so a 30-bit reconstruction of `(p-1)/2 - diff` proves
    /// `diff ≤ (p-1)/2`, i.e. the canonical ordering, exactly as the revocation
    /// tree's `ORDERING_BITS` does.
    pub const EXPIRY_DIFF_BITS: usize = 30;
    /// Number of dedicated Poseidon2 hash sites for the Attenuate membership +
    /// leaf-update + expiry-binding:
    ///   2 (held leaf, `hash_many`-7 = 2 perms) + 2 (granted leaf)
    ///   + `CAP_TREE_DEPTH` (held path) + `CAP_TREE_DEPTH` (new path)
    ///   + 2 (held / granted raw-height `encode_expiry` folds, `hash_many`-2 =
    ///        1 perm each — bind the RAW heights to the leaf's encoded-expiry felt
    ///        so the monotone GTE runs on RAW heights, not the non-monotone fold).
    pub const NUM_ATTN_HASH_SITES: usize = 6 + 2 * CAP_TREE_DEPTH;

    // ---- Scalar witness column offsets, relative to ATTN_SCALAR_BASE ----
    /// Shared leaf sort key (held == granted: the slot is fixed across an
    /// attenuation).
    pub const SLOT_HASH: usize = 0;
    /// Shared target cell-id felt (held == granted).
    pub const TARGET: usize = 1;
    /// Shared breadstuff felt (held == granted).
    pub const BREADSTUFF: usize = 2;
    /// Held auth tier tag (None=0…Custom=5; Custom absorbs vk → a felt).
    pub const HELD_AUTH_TAG: usize = 3;
    /// Held mask low-16.
    pub const HELD_MASK_LO: usize = 4;
    /// Held mask high-16.
    pub const HELD_MASK_HI: usize = 5;
    /// Held encoded expiry (`None`-sentinel or finite-height fold).
    pub const HELD_EXPIRY: usize = 6;
    /// Granted (narrowed) auth tier tag.
    pub const GRANTED_AUTH_TAG: usize = 7;
    /// Granted mask low-16.
    pub const GRANTED_MASK_LO: usize = 8;
    /// Granted mask high-16.
    pub const GRANTED_MASK_HI: usize = 9;
    /// Granted encoded expiry.
    pub const GRANTED_EXPIRY: usize = 10;
    /// 32 held-mask bits (16 lo then 16 hi) for the submask gate.
    pub const HELD_MASK_BITS_BASE: usize = 11;
    /// 32 granted-mask bits (16 lo then 16 hi): recompose the granted limbs AND
    /// (with the held bits) enforce the bitwise-subset submask gate.
    pub const GRANTED_MASK_BITS_BASE: usize = HELD_MASK_BITS_BASE + 2 * MASK_LIMB_BITS; // 43
    /// `CAP_TREE_DEPTH` path direction bits (0 = current is left child).
    pub const DIR_BITS_BASE: usize = GRANTED_MASK_BITS_BASE + 2 * MASK_LIMB_BITS; // 75
    /// `CAP_TREE_DEPTH` sibling digests along the path.
    pub const SIBLINGS_BASE: usize = DIR_BITS_BASE + CAP_TREE_DEPTH; // 91
    // ---- AuthRequired lattice witness ----
    /// The granted auth TIER byte (0=None…5=Custom) — the small ordinal, as
    /// distinct from [`GRANTED_AUTH_TAG`] (the leaf felt, which for `Custom`
    /// absorbs the vk_hash). Bound to the tag for built-in tiers; for `Custom`
    /// the tag is the vk-absorbed felt and only the tier is the ordinal 5.
    pub const GRANTED_TIER: usize = SIBLINGS_BASE + CAP_TREE_DEPTH; // 107
    /// The held auth TIER byte.
    pub const HELD_TIER: usize = GRANTED_TIER + 1; // 108
    /// One admissibility selector per ordered (granted_tier, held_tier) pair the
    /// tier partial order ACCEPTS (see [`admissible_tier_pairs`], which INCLUDES
    /// the mixed `(4,5)`/`(5,0)` Custom rows and EXCLUDES `(5,5)` — the vk path).
    /// The witness sets the one selector matching the row's tiers (built-in or
    /// mixed), or NONE for the `(5,5)` vk path; the AIR forces "exactly one
    /// table selector OR the vk path", each selector to a listed admissible
    /// pair, and the selected tiers to match.
    pub const LATTICE_SEL_BASE: usize = HELD_TIER + 1; // 109
    /// Number of admissible (granted,held) tier pairs (see [`admissible_tier_pairs`]).
    pub const NUM_LATTICE_PAIRS: usize = 16;
    /// Boolean: this row takes the Custom-vs-Custom vk path (`(5,5)`), admitted
    /// only by vk-equality. Mutually exclusive with the table-selector path.
    pub const VK_PATH: usize = LATTICE_SEL_BASE + NUM_LATTICE_PAIRS; // 125
    /// Inverse witness used to pin the tier↔tag consistency for built-in tiers
    /// (drives `(tag - tier)` to zero only when the tier is built-in).
    pub const CUSTOM_VK_EQ_INV: usize = VK_PATH + 1; // 126
    // ---- Expiry-monotone GTE witness ----
    /// `held_is_none` indicator: held_expiry == NONE_SENTINEL (⊤, any granted ok).
    pub const HELD_EXPIRY_IS_NONE: usize = CUSTOM_VK_EQ_INV + 1; // 127
    /// `granted_is_none` indicator: granted_expiry == NONE_SENTINEL.
    pub const GRANTED_EXPIRY_IS_NONE: usize = HELD_EXPIRY_IS_NONE + 1; // 128
    /// `diff = HALF_P_MINUS_1 - (held_expiry - granted_expiry)` carrier for the
    /// finite/finite shrink-only range check.
    pub const EXPIRY_DIFF: usize = GRANTED_EXPIRY_IS_NONE + 1; // 129
    /// 30 range bits reconstructing `held_height - granted_height ≤ (p-1)/2` on
    /// the RAW heights (NOT the non-monotone encoded-expiry fold).
    pub const EXPIRY_DIFF_BITS_BASE: usize = EXPIRY_DIFF + 1; // 130
    /// Held RAW expiry HEIGHT (the integer, < 2^30) used by the monotone GTE.
    /// Bound to [`HELD_EXPIRY`] (the encoded felt) by re-folding
    /// `encode_expiry(raw)` in-circuit when the held expiry is finite.
    pub const HELD_EXPIRY_RAW: usize = EXPIRY_DIFF_BITS_BASE + EXPIRY_DIFF_BITS; // 160
    /// Granted RAW expiry HEIGHT.
    pub const GRANTED_EXPIRY_RAW: usize = HELD_EXPIRY_RAW + 1; // 161
    // ---- Phase B2 (GrantCapability delegation) generalization ----
    /// The GRANTED leaf's own sort key. For an Attenuate row this MUST equal
    /// [`SLOT_HASH`] (the slot is fixed across an attenuation — explicit
    /// equality gate); for a witnessed Grant delegation row it is the
    /// RECIPIENT's new slot_hash (a different c-list), left free here and
    /// bound publicly via the granted-leaf digest pinned to `params[0]`.
    pub const GRANTED_SLOT_HASH: usize = GRANTED_EXPIRY_RAW + 1; // 162
    /// The GRANTED leaf's own breadstuff felt. Attenuate rows force equality
    /// with [`BREADSTUFF`]; Grant delegation rows may carry the delegated
    /// cap's own breadstuff.
    pub const GRANTED_BREADSTUFF: usize = GRANTED_SLOT_HASH + 1; // 163
    /// Total scalar witness columns in the shared cap non-amp block.
    pub const ATTN_SCALAR_COLS: usize = GRANTED_BREADSTUFF + 1; // 164

    /// Hash-site index of the held raw-height `encode_expiry` fold.
    pub const HS_HELD_EXPIRY_FOLD: usize = 4 + 2 * CAP_TREE_DEPTH;
    /// Hash-site index of the granted raw-height `encode_expiry` fold.
    pub const HS_GRANTED_EXPIRY_FOLD: usize = 4 + 2 * CAP_TREE_DEPTH + 1;

    /// Absolute column where the Attenuate scalar witness block begins (after
    /// the generic hash-site blocks).
    pub fn attn_scalar_base() -> usize {
        EFFECT_VM_WIDTH + num_hash_sites() * POSEIDON2_PERM_AUX_COLS
    }
    /// Absolute column where the Attenuate dedicated Poseidon2 hash blocks begin.
    pub fn attn_hash_base() -> usize {
        attn_scalar_base() + ATTN_SCALAR_COLS
    }
    /// Absolute base of Attenuate hash site `i`'s 352-col aux block.
    pub fn attn_hash_block(i: usize) -> usize {
        attn_hash_base() + i * POSEIDON2_PERM_AUX_COLS
    }
    /// Hash-site index of the held-leaf digest (the second of its two perms,
    /// whose output[0] is the leaf digest).
    pub const HS_HELD_LEAF_1: usize = 1;
    /// Hash-site index of the granted-leaf digest (second perm).
    pub const HS_GRANTED_LEAF_1: usize = 3;
    /// Hash-site index of the held path's TOP node (== old_cap_root).
    pub const HS_HELD_PATH_TOP: usize = 4 + CAP_TREE_DEPTH - 1;
    /// Hash-site index of the new path's TOP node (== new_cap_root).
    pub const HS_NEW_PATH_TOP: usize = 4 + 2 * CAP_TREE_DEPTH - 1;

    /// The admissible ordered (granted_tier, held_tier) pairs over the BUILT-IN
    /// `AuthRequired` tiers (None=0, Signature=1, Proof=2, Either=3,
    /// Impossible=4), encoding EXACTLY `AuthRequired::is_narrower_or_equal`
    /// (`cell/src/permissions.rs`). This is the partial order, NOT a numeric ≤:
    ///
    ///   * `Impossible (4)` ⊑ EVERYTHING (it is the bottom).
    ///   * EVERYTHING ⊑ `None (0)` (it is the top).
    ///   * `Signature (1)` ⊑ `Either (3)`, `Proof (2)` ⊑ `Either (3)`.
    ///   * reflexivity `t ⊑ t`.
    ///   * `{Signature}` and `{Proof}` are INCOMPARABLE — the (1,2) and (2,1)
    ///     pairs are ABSENT, so a GTE/≤ that would admit one of them is rejected.
    ///
    /// The Custom-vs-Custom case `(5,5)` is DELIBERATELY ABSENT: it is admitted
    /// only by the vk-equality sub-gate (both Custom AND vk-equal). The
    /// (Impossible⊑Custom) `(4,5)` and (Custom⊑None) `(5,0)` rows ARE listed —
    /// those are decided by the tier order alone. A row whose (granted,held)
    /// tier pair is none of these and is not the `(5,5)` vk path has NO
    /// satisfying admissibility selector ⇒ UNSAT.
    pub const fn admissible_tier_pairs() -> [(u32, u32); NUM_LATTICE_PAIRS] {
        [
            // reflexivity for the 5 built-in tiers (granted tier == held tier)
            (0, 0),
            (1, 1),
            (2, 2),
            (3, 3),
            (4, 4),
            // Impossible (4) is narrower-or-equal to EVERY held tier (bottom).
            (4, 0),
            (4, 1),
            (4, 2),
            (4, 3),
            (4, 5), // Impossible ⊑ Custom
            // EVERY granted tier is narrower-or-equal to None (0) (None = top).
            (1, 0),
            (2, 0),
            (3, 0),
            (5, 0), // Custom ⊑ None
            // Signature / Proof are strictly narrower than Either.
            (1, 3),
            (2, 3),
        ]
    }
}

/// FULL p3 trace width = base EffectVM width + generic hash blocks + the
/// dedicated Attenuate scalar-witness block + the Attenuate hash blocks.
pub fn effect_vm_p3_width() -> usize {
    EFFECT_VM_WIDTH
        + num_hash_sites() * POSEIDON2_PERM_AUX_COLS
        + attn::ATTN_SCALAR_COLS
        + attn::NUM_ATTN_HASH_SITES * POSEIDON2_PERM_AUX_COLS
}

// ============================================================================
// Attenuate dedicated Poseidon2 chain — symbolic (eval) + concrete (witness).
// Both walk the SAME 36-permutation ordering (see [`attn`]). The held/granted
// leaf digests are `hash_many` of the 7 CapLeaf fields (a 2-permutation rate-4
// sponge); the path nodes are `hash_fact(l,[r])`. The emitted DIGESTS are the
// held-leaf digest, the granted-leaf digest, the held-path top (= old_cap_root),
// and the new-path top (= new_cap_root), which the eval gates pin.
// ============================================================================

/// `hash_fact`'s leaf-domain capacity markers (`poseidon2::hash_fact`): the
/// sorted-tree node hash sets `state[5] = 0xFACF`, `state[6] = 1`.
const FACT_MARKER: u64 = 0xFACF;

/// The output state (all `POSEIDON2_WIDTH` felts) of the permutation whose aux
/// block begins at `block_base`: the LAST round's state, the final
/// `POSEIDON2_WIDTH` columns of the 352-col block.
fn perm_out_state_expr<AB: AirBuilder>(local: &[AB::Var], block_base: usize) -> [AB::Expr; POSEIDON2_WIDTH] {
    let off = block_base + POSEIDON2_PERM_AUX_COLS - POSEIDON2_WIDTH;
    core::array::from_fn(|j| local[off + j].into())
}

/// Concrete sibling of [`perm_out_state_expr`].
fn perm_out_state_concrete(row: &[BabyBear], block_base: usize) -> [BabyBear; POSEIDON2_WIDTH] {
    let off = block_base + POSEIDON2_PERM_AUX_COLS - POSEIDON2_WIDTH;
    core::array::from_fn(|j| row[off + j])
}

/// Symbolically emit the Attenuate membership + leaf-update Poseidon2 chain and
/// return `(held_leaf_digest, granted_leaf_digest, old_root, new_root)` as
/// `AB::Expr`. The round-by-round permutation constraints are emitted on EVERY
/// row (like the generic sites); the gates that USE these digests are
/// selector-gated in `eval`, so non-Attenuate rows carry a (vacuously
/// satisfiable, witness-filled) chain that constrains nothing downstream.
fn emit_attenuate_hashes<AB: AirBuilder>(
    builder: &mut AB,
    local: &[AB::Var],
) -> AttnDigests<AB::Expr>
where
    AB::F: PrimeField32,
{
    use attn::*;
    let s = attn_scalar_base();
    let sc = |off: usize| -> AB::Expr { local[s + off].into() };
    let hb = |i: usize| attn_hash_block(i);
    let block_aux = |i: usize| -> Vec<AB::Var> {
        local[hb(i)..hb(i) + POSEIDON2_PERM_AUX_COLS].to_vec()
    };
    let zero = AB::Expr::ZERO;
    let seven = AB::Expr::from_u64(7);
    let fact = AB::Expr::from_u64(FACT_MARKER);
    let one = AB::Expr::ONE;

    // ---- Held leaf digest = hash_many[slot,target,held_tag,held_mlo,held_mhi,held_exp,bread] ----
    // Perm 0: absorb chunk0 into a fresh state (state[4] = len = 7).
    let h0_in: [AB::Expr; POSEIDON2_WIDTH] = {
        let mut st: [AB::Expr; POSEIDON2_WIDTH] = core::array::from_fn(|_| zero.clone());
        st[0] = sc(SLOT_HASH);
        st[1] = sc(TARGET);
        st[2] = sc(HELD_AUTH_TAG);
        st[3] = sc(HELD_MASK_LO);
        st[4] = seven.clone();
        st
    };
    let _ = poseidon2_permute_expr::<AB>(builder, h0_in, &block_aux(0));
    // Perm 1: absorb chunk1 (3 elems added to positions 0..3 of perm0's output).
    let h0_out = perm_out_state_expr::<AB>(local, hb(0));
    let h1_in: [AB::Expr; POSEIDON2_WIDTH] = core::array::from_fn(|j| match j {
        0 => h0_out[0].clone() + sc(HELD_MASK_HI),
        1 => h0_out[1].clone() + sc(HELD_EXPIRY),
        2 => h0_out[2].clone() + sc(BREADSTUFF),
        _ => h0_out[j].clone(),
    });
    let held_leaf = poseidon2_permute_expr::<AB>(builder, h1_in, &block_aux(1));

    // ---- Granted leaf digest (same shape, narrowed rights). Phase B2: the
    //      granted leaf hashes its OWN slot_hash / breadstuff columns (a Grant
    //      delegation installs at the RECIPIENT's new slot, possibly with its
    //      own breadstuff); Attenuate rows force GRANTED_SLOT_HASH == SLOT_HASH
    //      and GRANTED_BREADSTUFF == BREADSTUFF via explicit gates in `eval`.
    //      TARGET stays SHARED — the delegated cap points at the same target
    //      the held cap does (the runtime looks the held cap up BY target). ----
    let g0_in: [AB::Expr; POSEIDON2_WIDTH] = {
        let mut st: [AB::Expr; POSEIDON2_WIDTH] = core::array::from_fn(|_| zero.clone());
        st[0] = sc(GRANTED_SLOT_HASH);
        st[1] = sc(TARGET);
        st[2] = sc(GRANTED_AUTH_TAG);
        st[3] = sc(GRANTED_MASK_LO);
        st[4] = seven.clone();
        st
    };
    let _ = poseidon2_permute_expr::<AB>(builder, g0_in, &block_aux(2));
    let g0_out = perm_out_state_expr::<AB>(local, hb(2));
    let g1_in: [AB::Expr; POSEIDON2_WIDTH] = core::array::from_fn(|j| match j {
        0 => g0_out[0].clone() + sc(GRANTED_MASK_HI),
        1 => g0_out[1].clone() + sc(GRANTED_EXPIRY),
        2 => g0_out[2].clone() + sc(GRANTED_BREADSTUFF),
        _ => g0_out[j].clone(),
    });
    let granted_leaf = poseidon2_permute_expr::<AB>(builder, g1_in, &block_aux(3));

    // ---- Held path (depth nodes) from held leaf up to old_cap_root ----
    // node_in = hash_fact(left, [right]); dir=0 ⇒ current is LEFT child.
    // left  = dir==0 ? cur : sib;  right = dir==0 ? sib : cur.
    let mut held_cur = held_leaf.clone();
    let mut new_cur = granted_leaf.clone();
    for level in 0..CAP_TREE_DEPTH {
        let dir = sc(DIR_BITS_BASE + level);
        let sib = sc(SIBLINGS_BASE + level);
        // left = cur + dir*(sib - cur); right = sib + dir*(cur - sib).
        let held_left = held_cur.clone() + dir.clone() * (sib.clone() - held_cur.clone());
        let held_right = sib.clone() + dir.clone() * (held_cur.clone() - sib.clone());
        let held_node_in: [AB::Expr; POSEIDON2_WIDTH] = core::array::from_fn(|j| match j {
            0 => held_left.clone(),
            1 => held_right.clone(),
            5 => fact.clone(),
            6 => one.clone(),
            _ => zero.clone(),
        });
        held_cur = poseidon2_permute_expr::<AB>(builder, held_node_in, &block_aux(4 + level));

        let new_left = new_cur.clone() + dir.clone() * (sib.clone() - new_cur.clone());
        let new_right = sib.clone() + dir.clone() * (new_cur.clone() - sib.clone());
        let new_node_in: [AB::Expr; POSEIDON2_WIDTH] = core::array::from_fn(|j| match j {
            0 => new_left.clone(),
            1 => new_right.clone(),
            5 => fact.clone(),
            6 => one.clone(),
            _ => zero.clone(),
        });
        new_cur = poseidon2_permute_expr::<AB>(builder, new_node_in, &block_aux(4 + CAP_TREE_DEPTH + level));
    }

    // ---- Raw-height encode_expiry folds: hash_many([raw, 0]) (state[4]=len=2).
    //      These bind the RAW height columns to the leaf's encoded-expiry felt
    //      (gated finite in GATE 5), so the monotone GTE runs on raw heights. ----
    let two = AB::Expr::from_u64(2);
    let held_exp_in: [AB::Expr; POSEIDON2_WIDTH] = core::array::from_fn(|j| match j {
        0 => sc(HELD_EXPIRY_RAW),
        4 => two.clone(),
        _ => zero.clone(),
    });
    let held_exp_fold =
        poseidon2_permute_expr::<AB>(builder, held_exp_in, &block_aux(HS_HELD_EXPIRY_FOLD));
    let granted_exp_in: [AB::Expr; POSEIDON2_WIDTH] = core::array::from_fn(|j| match j {
        0 => sc(GRANTED_EXPIRY_RAW),
        4 => two.clone(),
        _ => zero.clone(),
    });
    let granted_exp_fold =
        poseidon2_permute_expr::<AB>(builder, granted_exp_in, &block_aux(HS_GRANTED_EXPIRY_FOLD));

    AttnDigests {
        held_leaf,
        granted_leaf,
        old_root: held_cur,
        new_root: new_cur,
        held_exp_fold,
        granted_exp_fold,
    }
}

/// The named digests emitted by [`emit_attenuate_hashes`].
struct AttnDigests<E> {
    held_leaf: E,
    granted_leaf: E,
    old_root: E,
    new_root: E,
    held_exp_fold: E,
    granted_exp_fold: E,
}

/// Concrete witness for the Attenuate hash chain: returns the `Vec<BabyBear>` of
/// all `NUM_ATTN_HASH_SITES * POSEIDON2_PERM_AUX_COLS` aux columns, in the SAME
/// order [`emit_attenuate_hashes`] consumes them. Driven by the already-filled
/// scalar witness columns in `row` (slots, leaf fields, siblings, dir bits).
fn attenuate_hash_witness(row: &[BabyBear]) -> Vec<BabyBear> {
    use attn::*;
    let s = attn_scalar_base();
    let sc = |off: usize| row[s + off];
    let mut out: Vec<BabyBear> = Vec::with_capacity(NUM_ATTN_HASH_SITES * POSEIDON2_PERM_AUX_COLS);

    // Held leaf: hash_many over 7 fields (2 perms).
    let mut h0 = [BabyBear::ZERO; POSEIDON2_WIDTH];
    h0[0] = sc(SLOT_HASH);
    h0[1] = sc(TARGET);
    h0[2] = sc(HELD_AUTH_TAG);
    h0[3] = sc(HELD_MASK_LO);
    h0[4] = BabyBear::new(7);
    let h0_aux = poseidon2_permute_aux_witness(h0);
    let h0_out = last_state(&h0_aux);
    out.extend(h0_aux);
    let mut h1 = h0_out;
    h1[0] += sc(HELD_MASK_HI);
    h1[1] += sc(HELD_EXPIRY);
    h1[2] += sc(BREADSTUFF);
    let h1_aux = poseidon2_permute_aux_witness(h1);
    let held_leaf = last_state(&h1_aux)[0];
    out.extend(h1_aux);

    // Granted leaf (its OWN slot_hash / breadstuff columns — Phase B2).
    let mut g0 = [BabyBear::ZERO; POSEIDON2_WIDTH];
    g0[0] = sc(GRANTED_SLOT_HASH);
    g0[1] = sc(TARGET);
    g0[2] = sc(GRANTED_AUTH_TAG);
    g0[3] = sc(GRANTED_MASK_LO);
    g0[4] = BabyBear::new(7);
    let g0_aux = poseidon2_permute_aux_witness(g0);
    let g0_out = last_state(&g0_aux);
    out.extend(g0_aux);
    let mut g1 = g0_out;
    g1[0] += sc(GRANTED_MASK_HI);
    g1[1] += sc(GRANTED_EXPIRY);
    g1[2] += sc(GRANTED_BREADSTUFF);
    let g1_aux = poseidon2_permute_aux_witness(g1);
    let granted_leaf = last_state(&g1_aux)[0];
    out.extend(g1_aux);

    // Held path + new path (shared siblings / directions).
    let mut held_cur = held_leaf;
    let mut new_cur = granted_leaf;
    let mut held_blocks: Vec<BabyBear> = Vec::new();
    let mut new_blocks: Vec<BabyBear> = Vec::new();
    for level in 0..CAP_TREE_DEPTH {
        let dir = sc(DIR_BITS_BASE + level).as_u32();
        let sib = sc(SIBLINGS_BASE + level);
        let (hl, hr) = if dir == 0 { (held_cur, sib) } else { (sib, held_cur) };
        let mut hin = [BabyBear::ZERO; POSEIDON2_WIDTH];
        hin[0] = hl;
        hin[1] = hr;
        hin[5] = BabyBear::new(FACT_MARKER as u32);
        hin[6] = BabyBear::ONE;
        let haux = poseidon2_permute_aux_witness(hin);
        held_cur = last_state(&haux)[0];
        held_blocks.extend(haux);

        let (nl, nr) = if dir == 0 { (new_cur, sib) } else { (sib, new_cur) };
        let mut nin = [BabyBear::ZERO; POSEIDON2_WIDTH];
        nin[0] = nl;
        nin[1] = nr;
        nin[5] = BabyBear::new(FACT_MARKER as u32);
        nin[6] = BabyBear::ONE;
        let naux = poseidon2_permute_aux_witness(nin);
        new_cur = last_state(&naux)[0];
        new_blocks.extend(naux);
    }
    out.extend(held_blocks);
    out.extend(new_blocks);

    // Raw-height encode_expiry folds: hash_many([raw, 0]) (state[4] = len = 2).
    let mut he = [BabyBear::ZERO; POSEIDON2_WIDTH];
    he[0] = sc(HELD_EXPIRY_RAW);
    he[4] = BabyBear::new(2);
    out.extend(poseidon2_permute_aux_witness(he));
    let mut ge = [BabyBear::ZERO; POSEIDON2_WIDTH];
    ge[0] = sc(GRANTED_EXPIRY_RAW);
    ge[4] = BabyBear::new(2);
    out.extend(poseidon2_permute_aux_witness(ge));

    debug_assert_eq!(out.len(), NUM_ATTN_HASH_SITES * POSEIDON2_PERM_AUX_COLS);
    out
}

/// The final permutation state (last `POSEIDON2_WIDTH` felts of a 352-col aux
/// block produced by [`poseidon2_permute_aux_witness`]).
fn last_state(aux: &[BabyBear]) -> [BabyBear; POSEIDON2_WIDTH] {
    let off = aux.len() - POSEIDON2_WIDTH;
    core::array::from_fn(|j| aux[off + j])
}

// ============================================================================
// Attenuate Phase-B scalar-witness builder + proving / accept entry points.
// ============================================================================

/// Build the Phase-B scalar-witness block for ONE Attenuate row from its
/// [`AttenuateWitness`]. Fills the slot/target/breadstuff felts, the held +
/// granted rights felts, the 16+16 mask bit-decompositions, the path siblings
/// + direction bits, the AuthRequired tier ordinals + admissibility selector
/// (or vk-path flag), and the expiry-monotone GTE witness. The returned block
/// has length [`attn::ATTN_SCALAR_COLS`].
///
/// This is a PURE function of the witness; the AIR's gates re-derive every
/// relation from these columns, so a block that does not encode a genuine
/// narrowing yields an UNSAT trace.
pub fn attenuate_scalar_block(w: &crate::effect_vm::AttenuateWitness) -> Vec<BabyBear> {
    use attn::*;
    let mut b = vec![BabyBear::ZERO; ATTN_SCALAR_COLS];
    let held = &w.held;
    let granted = &w.granted;

    b[SLOT_HASH] = held.slot_hash;
    b[TARGET] = held.target;
    b[BREADSTUFF] = held.breadstuff;
    // Phase B2: the granted leaf hashes its OWN slot / breadstuff. For an
    // Attenuate witness these equal held's (the AIR's same-slot gates check);
    // for a Grant delegation they are the recipient-side leaf's own fields.
    b[GRANTED_SLOT_HASH] = granted.slot_hash;
    b[GRANTED_BREADSTUFF] = granted.breadstuff;
    b[HELD_AUTH_TAG] = held.auth_tag;
    b[HELD_MASK_LO] = held.mask_lo;
    b[HELD_MASK_HI] = held.mask_hi;
    b[HELD_EXPIRY] = held.expiry;
    b[GRANTED_AUTH_TAG] = granted.auth_tag;
    b[GRANTED_MASK_LO] = granted.mask_lo;
    b[GRANTED_MASK_HI] = granted.mask_hi;
    b[GRANTED_EXPIRY] = granted.expiry;

    // Mask bit-decompositions (16 lo then 16 hi, for held and granted).
    let bits = |v: u32, base: usize, b: &mut [BabyBear]| {
        for i in 0..MASK_LIMB_BITS {
            b[base + i] = BabyBear::new((v >> i) & 1);
        }
    };
    bits(held.mask_lo.as_u32(), HELD_MASK_BITS_BASE, &mut b);
    bits(held.mask_hi.as_u32(), HELD_MASK_BITS_BASE + MASK_LIMB_BITS, &mut b);
    bits(granted.mask_lo.as_u32(), GRANTED_MASK_BITS_BASE, &mut b);
    bits(granted.mask_hi.as_u32(), GRANTED_MASK_BITS_BASE + MASK_LIMB_BITS, &mut b);

    // Path siblings + directions.
    for (i, &sib) in w.siblings.iter().enumerate() {
        b[SIBLINGS_BASE + i] = sib;
    }
    for (i, &dir) in w.directions.iter().enumerate() {
        b[DIR_BITS_BASE + i] = BabyBear::new(dir as u32);
    }

    // AuthRequired tier ordinals + admissibility selector / vk path.
    b[GRANTED_TIER] = BabyBear::new(w.granted_tier as u32);
    b[HELD_TIER] = BabyBear::new(w.held_tier as u32);
    if w.granted_tier == 5 && w.held_tier == 5 {
        // Custom-vs-Custom: vk path (admitted only if the vk-absorbed tags match).
        b[VK_PATH] = BabyBear::ONE;
    } else {
        let pairs = admissible_tier_pairs();
        if let Some(k) = pairs
            .iter()
            .position(|&(pg, ph)| pg == w.granted_tier as u32 && ph == w.held_tier as u32)
        {
            b[LATTICE_SEL_BASE + k] = BabyBear::ONE;
        }
        // If no admissible pair matches (an amplifying / incomparable tier pair),
        // NO selector is set ⇒ the AIR's "exactly one path active" gate is UNSAT.
    }

    // Expiry-monotone GTE witness — on the RAW heights (bound to the encoded
    // leaf felts via the in-circuit encode_expiry fold).
    let none_sent = crate::cap_root::SENTINEL_MAX;
    let h_none = w.held_expiry_height.is_none();
    let g_none = w.granted_expiry_height.is_none();
    // Sanity: the raw-None state matches the encoded-felt sentinel.
    debug_assert_eq!(h_none, held.expiry == none_sent);
    debug_assert_eq!(g_none, granted.expiry == none_sent);
    b[HELD_EXPIRY_IS_NONE] = BabyBear::new(h_none as u32);
    b[GRANTED_EXPIRY_IS_NONE] = BabyBear::new(g_none as u32);
    let held_raw = w.held_expiry_height.unwrap_or(0);
    let granted_raw = w.granted_expiry_height.unwrap_or(0);
    // Raw heights as single felts (heights < 2^30 fit one limb; the in-circuit
    // fold uses hash_many([raw, 0]) = encode_expiry for h_hi == 0).
    b[HELD_EXPIRY_RAW] = BabyBear::new(held_raw as u32);
    b[GRANTED_EXPIRY_RAW] = BabyBear::new(granted_raw as u32);
    if !h_none && !g_none {
        // 30-bit reconstruction of (p-1)/2 - (held_raw - granted_raw). For an
        // honest shrink (granted ≤ held) this is in [0, 2^30); a widening wraps
        // past (p-1)/2 ⇒ no 30-bit witness ⇒ the AIR rejects.
        let half = crate::dsl::revocation::HALF_P_MINUS_1;
        let field_diff =
            (BabyBear::new(held_raw as u32) - BabyBear::new(granted_raw as u32)).as_u32();
        let check = half.wrapping_sub(field_diff);
        for i in 0..EXPIRY_DIFF_BITS {
            b[EXPIRY_DIFF_BITS_BASE + i] = BabyBear::new((check >> i) & 1);
        }
        b[EXPIRY_DIFF] = BabyBear::new(check);
    }
    b
}

/// Build the per-row cap-non-amp scalar blocks for an effect sequence: the
/// all-zero block for every unwitnessed row, and [`attenuate_scalar_block`]
/// for each `AttenuateCapability { phase_b: Some(_), .. }` or (Phase B2)
/// `GrantCapability { phase_b: Some(_), .. }` row. The result is
/// row-aligned to [`generate_effect_vm_trace`]'s output (one row per effect,
/// then NoOp padding to the power-of-two height), so it is consumed by
/// [`extend_trace_with_attenuation`].
pub fn attenuate_scalar_blocks_for(
    effects: &[crate::effect_vm::Effect],
    trace_height: usize,
) -> Vec<Vec<BabyBear>> {
    use crate::effect_vm::Effect;
    let mut blocks: Vec<Vec<BabyBear>> = Vec::with_capacity(trace_height);
    for eff in effects {
        match eff {
            Effect::AttenuateCapability { phase_b: Some(w), .. } => {
                blocks.push(attenuate_scalar_block(w));
            }
            // Phase B2: a witnessed GrantCapability delegation row carries the
            // SAME scalar block (held membership + order-gate witness); the
            // grant-specific gates in `eval` fire on sel 3 × direction.
            Effect::GrantCapability { phase_b: Some(w), .. } => {
                blocks.push(attenuate_scalar_block(w));
            }
            _ => blocks.push(vec![BabyBear::ZERO; attn::ATTN_SCALAR_COLS]),
        }
    }
    while blocks.len() < trace_height {
        blocks.push(vec![BabyBear::ZERO; attn::ATTN_SCALAR_COLS]);
    }
    blocks
}

/// Prove an Attenuate / witnessed-Grant (or any) effect turn through the
/// AUDITED p3 prover with
/// the Phase-B scalar witness threaded in. `base_trace` is the 186-col trace
/// from [`generate_effect_vm_trace`]; `effects` is the SAME sequence (used to
/// recover the per-row Phase-B witness). The proof self-verifies before return.
pub fn prove_effect_vm_p3_attenuation(
    base_trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    effects: &[crate::effect_vm::Effect],
) -> Result<EffectVmP3Proof, EffectVmP3Error> {
    let air = EffectVmP3Air;
    let config = create_config();
    let scalar_blocks = attenuate_scalar_blocks_for(effects, base_trace.len());
    let full_trace = extend_trace_with_attenuation(base_trace, &scalar_blocks);
    let matrix = to_matrix(&full_trace);
    let pis: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();
    let instances = vec![StarkInstance { air: &air, trace: &matrix, public_values: pis.clone() }];
    let prover_data = ProverData::from_instances(&config, &instances);
    let common = &prover_data.common;
    let proof = prove_batch(&config, &instances, &prover_data);
    let airs = vec![air];
    let pvs = vec![pis];
    verify_batch(&config, &airs, &proof, &pvs, common)
        .map_err(|e| EffectVmP3Error::VerificationFailed(format!("{e:?}")))?;
    Ok(proof)
}

/// FRI-free accept/reject decision (the exact predicate the audited verifier
/// enforces) for an Attenuate / witnessed-Grant turn carrying the Phase-B
/// scalar witness. Mirrors
/// [`p3_air_accepts`] but threads the witness through
/// [`extend_trace_with_attenuation`].
pub fn p3_air_accepts_attenuation(
    base_trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    effects: &[crate::effect_vm::Effect],
) -> bool {
    let air = EffectVmP3Air;
    let scalar_blocks = attenuate_scalar_blocks_for(effects, base_trace.len());
    let full_trace = extend_trace_with_attenuation(base_trace, &scalar_blocks);
    let matrix = to_matrix(&full_trace);
    let pis: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();
    p3_air::check_all_constraints(&air, &matrix, &pis, Some(1)).is_ok()
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

        // -- AttenuateCapability dedicated Poseidon2 chain (membership + leaf-update
        //    + expiry-folds). Emitted on every row (round constraints
        //    unconditional, like the generic sites); the digests feed the
        //    selector-gated gates below. --
        let attn_d = emit_attenuate_hashes(builder, &local);

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

        // -- GrantCapability (ONE selector, TWO row roles — params[1] direction,
        //    mirroring Transfer). direction 0 = recipient install (legacy hash
        //    site 4 fold); direction 1 = the Phase-B2 GRANTER-side delegation
        //    row, whose cap_root PASSES THROUGH (the granter's tree is not
        //    moved by delegating) and whose non-amp gates live with the shared
        //    Attenuate gate block below (where the scalar witness is in scope). --
        let grant_dir = prm(param::GRANT_DIRECTION);
        // direction is boolean on grant rows.
        tb.assert_zero(
            s_grantcap.clone() * grant_dir.clone() * (grant_dir.clone() - one.clone()),
        );
        // direction 0: the legacy recipient-install cap_root advance.
        tb.assert_zero(
            s_grantcap.clone()
                * (one.clone() - grant_dir.clone())
                * (new_cap_root.clone() - digests[hs::GRANT_CAP].clone()),
        );
        // direction 1: granter-side passthrough — delegating must NOT move the
        // granter's own cap_root.
        tb.assert_zero(
            s_grantcap.clone()
                * grant_dir.clone()
                * (new_cap_root.clone() - old_cap_root.clone()),
        );
        tb.assert_zero(s_grantcap.clone() * (new_bal_lo.clone() - old_bal_lo.clone()));
        tb.assert_zero(s_grantcap.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
        for i in 0..8 {
            tb.assert_zero(s_grantcap.clone() * (fld_a(i) - fld_b(i)));
        }
        // delegation rows: reserved passthrough (mirrors the Attenuate frame).
        tb.assert_zero(
            s_grantcap.clone()
                * grant_dir.clone()
                * (sa(state::RESERVED) - sb(state::RESERVED)),
        );

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

        // -- NoteCreate: BALANCE-NEUTRAL --
        // The note value is hidden in the commitment and is NEVER moved on the
        // transparent ledger (the shielding convention the executor uses:
        // `apply_note_create` records the commitment and does not touch balance).
        // So `bal_lo` is FROZEN: new_bal_lo = old_bal_lo. Matches the verified Lean
        // descriptor (`EffectVmEmitNoteCreate`, balance-neutral) + universe-A's
        // `noteCreateA_bal_neutral`. (`p1` = value_lo stays bound into the commitment
        // cross-binding; a prior version debited it, which diverged — closed.)
        tb.assert_zero(
            s_notecreate.clone() * (new_bal_lo.clone() - old_bal_lo.clone()),
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

        // -- Shared cap NON-AMPLIFICATION block: PHASE B (AttenuateCapability,
        //    sel 48) + PHASE B2 (GrantCapability granter-side delegation rows,
        //    sel 3 × direction). A verifying row IMPLIES granted ⊑ held on BOTH
        //    lattices + monotone expiry, with held AUTHENTICATED against the
        //    row's own old_cap_root (Attenuate: the actor's tree; Grant: the
        //    GRANTER's tree — the delegated-from rights). See [`attn`]. --
        let s_attn_cap = lc(sel::ATTENUATE_CAPABILITY);
        // The witnessed-grant delegation selector: sel 3 × the boolean
        // direction param (boolean-gated above). Selector exclusivity makes
        // `s_attn_cap + s_grant_del` ∈ {0, 1} on every row.
        let s_grant_del = s_grantcap.clone() * grant_dir.clone();
        {
            use attn::*;
            let sbase = attn_scalar_base();
            let w = |off: usize| -> AB::Expr { local[sbase + off].into() };
            // `s` gates the SHARED non-amp gates (membership-open + submask +
            // AuthRequired lattice + expiry-monotone); the per-effect framing
            // and cap_root-move gates are pinned to their own selectors.
            let s = s_attn_cap.clone() + s_grant_del.clone();

            // -- Attenuate state frame: balance / fields / reserved unchanged.
            //    (Grant's frame lives with its selector block above.) --
            tb.assert_zero(s_attn_cap.clone() * (new_bal_lo.clone() - old_bal_lo.clone()));
            tb.assert_zero(s_attn_cap.clone() * (new_bal_hi.clone() - old_bal_hi.clone()));
            for i in 0..8 {
                tb.assert_zero(s_attn_cap.clone() * (fld_a(i) - fld_b(i)));
            }
            tb.assert_zero(s_attn_cap.clone() * (sa(state::RESERVED) - sb(state::RESERVED)));

            // ===== GATE 1 (SHARED): MEMBERSHIP-OPEN — held leaf authenticated vs
            // old_cap_root. The held-path top (folded from the held leaf digest up
            // the witnessed sibling path) MUST equal state_before.cap_root. The
            // sorted tree has exactly one leaf per slot, so this pins the held
            // rights to the real committed leaf (Forgery 3: a fabricated held leaf
            // has no path to the real root ⇒ this fails). On a Grant delegation
            // row, state_before.cap_root is the GRANTER's tree, so the held
            // (delegated-from) rights are granter-authenticated.
            tb.assert_zero(s.clone() * (attn_d.old_root.clone() - old_cap_root.clone()));
            // Bind the param-anchored slot hash to the witnessed slot, so the
            // public params identify the same slot the membership opens (no
            // swapping the proven slot for another). Attenuate uses params[0];
            // Grant delegation rows use params[2] (params[0] carries the granted
            // leaf digest there).
            tb.assert_zero(
                s_attn_cap.clone() * (prm(param::ATTN_CAP_SLOT_HASH) - w(SLOT_HASH)),
            );
            tb.assert_zero(
                s_grant_del.clone() * (prm(param::GRANT_HELD_SLOT_HASH) - w(SLOT_HASH)),
            );

            // ===== GATE 2a (Attenuate): LEAF-UPDATE — new_cap_root forced by the
            // canonical move. The granted (narrowed) leaf folded up the SAME
            // sibling path MUST equal state_after.cap_root. This REPLACES the
            // pinned-digest advance: the circuit forces the sorted-tree root move,
            // not the executor.
            tb.assert_zero(
                s_attn_cap.clone() * (attn_d.new_root.clone() - new_cap_root.clone()),
            );
            // The narrower-commitment param (params[1]) is bound to the granted
            // leaf digest, so the public attestation commits to exactly the leaf
            // whose narrowed rights the gates check.
            tb.assert_zero(
                s_attn_cap.clone()
                    * (prm(param::ATTN_NARROWER_COMMITMENT) - attn_d.granted_leaf.clone()),
            );
            // Attenuate same-slot / same-breadstuff law (previously structural —
            // the granted leaf hashed the shared columns; now that the granted
            // leaf has its own slot/breadstuff columns for Grant, Attenuate pins
            // them equal explicitly): an attenuation narrows IN PLACE.
            tb.assert_zero(
                s_attn_cap.clone() * (w(GRANTED_SLOT_HASH) - w(SLOT_HASH)),
            );
            tb.assert_zero(
                s_attn_cap.clone() * (w(GRANTED_BREADSTUFF) - w(BREADSTUFF)),
            );

            // ===== GATE 2b (Grant delegation): GRANTED-LEAF BINDING — the public
            // cap_entry param (params[0], all 8 limbs in effects_hash) is pinned
            // to the granted CapLeaf's 7-field Poseidon2 digest recomputed
            // in-circuit from the witnessed rights fields. The installed entry's
            // ACTUAL rights (slot/target/auth/mask/expiry/breadstuff) — not an
            // opaque digest — are what the recipient-side root advance consumes
            // (the recipient install row's cap_entry is the same wire value).
            // The granter row's cap_root passthrough is enforced with its frame
            // above.
            tb.assert_zero(
                s_grant_del.clone() * (prm(param::CAP_ENTRY) - attn_d.granted_leaf.clone()),
            );

            // ===== GATE 3: SUBMASK (EffectMask facet order) — granted ⊆ held bitwise.
            // Decompose held + granted mask limbs into 16+16 bits each; recompose
            // (binds the witnessed limbs to the leaf fields); then enforce
            // granted_bit ⇒ held_bit (granted_bit * (1 - held_bit) == 0) for all 32
            // bits. (Forgery 1: a granted bit absent from held ⇒ this fails.)
            {
                let mut held_lo = AB::Expr::ZERO;
                let mut held_hi = AB::Expr::ZERO;
                let mut grant_lo = AB::Expr::ZERO;
                let mut grant_hi = AB::Expr::ZERO;
                for i in 0..MASK_LIMB_BITS {
                    let hb = w(HELD_MASK_BITS_BASE + i);
                    let hbh = w(HELD_MASK_BITS_BASE + MASK_LIMB_BITS + i);
                    let gb = w(GRANTED_MASK_BITS_BASE + i);
                    let gbh = w(GRANTED_MASK_BITS_BASE + MASK_LIMB_BITS + i);
                    // booleanity (gated).
                    tb.assert_zero(s.clone() * hb.clone() * (hb.clone() - one.clone()));
                    tb.assert_zero(s.clone() * hbh.clone() * (hbh.clone() - one.clone()));
                    tb.assert_zero(s.clone() * gb.clone() * (gb.clone() - one.clone()));
                    tb.assert_zero(s.clone() * gbh.clone() * (gbh.clone() - one.clone()));
                    let w_i = AB::Expr::from_u64(1u64 << i);
                    held_lo = held_lo + hb.clone() * w_i.clone();
                    held_hi = held_hi + hbh.clone() * w_i.clone();
                    grant_lo = grant_lo + gb.clone() * w_i.clone();
                    grant_hi = grant_hi + gbh.clone() * w_i.clone();
                    // subset: granted bit set ⇒ held bit set, on BOTH limbs.
                    tb.assert_zero(s.clone() * gb.clone() * (one.clone() - hb.clone()));
                    tb.assert_zero(s.clone() * gbh.clone() * (one.clone() - hbh.clone()));
                }
                // recomposition binds the bit columns to the witnessed mask limbs…
                tb.assert_zero(s.clone() * (held_lo - w(HELD_MASK_LO)));
                tb.assert_zero(s.clone() * (held_hi - w(HELD_MASK_HI)));
                tb.assert_zero(s.clone() * (grant_lo - w(GRANTED_MASK_LO)));
                tb.assert_zero(s.clone() * (grant_hi - w(GRANTED_MASK_HI)));
            }

            // ===== GATE 4: AUTHREQUIRED LATTICE — the PARTIAL order, not a ≤.
            // Tier bytes 0..5 = None,Signature,Proof,Either,Impossible,Custom.
            // An admissibility selector table over (granted_tier, held_tier)
            // encodes EXACTLY `is_narrower_or_equal` (incl. mixed Custom rows
            // (4,5)/(5,0), EXCLUDING (5,5) which is the vk path). The witness sets
            // ONE table selector OR the vk-path flag; the AIR forces:
            //   (a) each selector + vk_path boolean,
            //   (b) exactly one of {table selectors, vk_path} active,
            //   (c) the active selector's pair to match (granted_tier, held_tier),
            //   (d) tier↔tag consistency for built-in tiers (tag == tier for 0..4),
            //   (e) vk path ⇒ both tiers Custom (5) AND granted_tag == held_tag.
            // {Signature}(1) vs {Proof}(2) are INCOMPARABLE: (1,2)/(2,1) are NOT in
            // the table and are not the vk path ⇒ UNSAT (Forgery 2). Two distinct
            // Customs fail (e) (Forgery 4).
            {
                let gt = w(GRANTED_TIER);
                let ht = w(HELD_TIER);
                let vk = w(VK_PATH);
                tb.assert_zero(s.clone() * vk.clone() * (vk.clone() - one.clone()));

                let pairs = admissible_tier_pairs();
                let mut sel_sum = vk.clone();
                // For each table selector: boolean, and when active force the pair.
                for (k, (pg, ph)) in pairs.iter().enumerate() {
                    let selk = w(LATTICE_SEL_BASE + k);
                    tb.assert_zero(s.clone() * selk.clone() * (selk.clone() - one.clone()));
                    // active ⇒ granted_tier == pg AND held_tier == ph.
                    tb.assert_zero(
                        s.clone() * selk.clone() * (gt.clone() - AB::Expr::from_u64(*pg as u64)),
                    );
                    tb.assert_zero(
                        s.clone() * selk.clone() * (ht.clone() - AB::Expr::from_u64(*ph as u64)),
                    );
                    sel_sum = sel_sum + selk;
                }
                // (b) exactly one path active.
                tb.assert_zero(s.clone() * (sel_sum - one.clone()));

                // (d) tier↔tag consistency for BUILT-IN tiers. For tiers 0..4 the
                // leaf auth_tag IS the tier byte; for tier 5 (Custom) the tag is the
                // vk-absorbed felt (left free here, pinned by (e)). We force:
                //   (tag - tier) * (5 - tier == 0 ? 0 : 1) ... encoded as: when the
                // row is NOT on the vk path, granted/held tiers are < 5 (the table
                // pairs only list tier 5 in the mixed Custom rows, where the tag is
                // checked equal to tier 5's vk felt only via (e)). To keep this a
                // low-degree gate we bind tag==tier whenever the tier selector that
                // is active lists a BUILT-IN tier (≤4). Concretely: for each table
                // selector whose pair tier is ≤4, force tag==tier.
                for (k, (pg, ph)) in pairs.iter().enumerate() {
                    let selk = w(LATTICE_SEL_BASE + k);
                    if *pg <= 4 {
                        tb.assert_zero(
                            s.clone()
                                * selk.clone()
                                * (w(GRANTED_AUTH_TAG) - AB::Expr::from_u64(*pg as u64)),
                        );
                    }
                    if *ph <= 4 {
                        tb.assert_zero(
                            s.clone()
                                * selk.clone()
                                * (w(HELD_AUTH_TAG) - AB::Expr::from_u64(*ph as u64)),
                        );
                    }
                }
                // (e) vk path ⇒ both tiers Custom(5) AND granted_tag == held_tag.
                tb.assert_zero(s.clone() * vk.clone() * (gt.clone() - AB::Expr::from_u64(5)));
                tb.assert_zero(s.clone() * vk.clone() * (ht.clone() - AB::Expr::from_u64(5)));
                tb.assert_zero(
                    s.clone() * vk.clone() * (w(GRANTED_AUTH_TAG) - w(HELD_AUTH_TAG)),
                );

                // (f) tier↔tag AIRTIGHT binding (belt-and-suspenders): for EITHER
                // side, the claimed tier is either Custom(5) OR the (built-in) tag
                // equals the tier — `(tier - 5) * (auth_tag - tier) == 0`. This
                // forbids claiming a built-in tier whose authenticated tag differs
                // (a prover cannot relabel an Either(3) leaf as Signature(1)) and
                // forbids a built-in tag masquerading under a mismatched ordinal.
                // Combined with (c)/(d)/(e) the lattice decides on the GENUINE
                // authenticated tags, closing any free-tier loophole.
                let five = AB::Expr::from_u64(5);
                tb.assert_zero(
                    s.clone() * (gt.clone() - five.clone()) * (w(GRANTED_AUTH_TAG) - gt.clone()),
                );
                tb.assert_zero(
                    s.clone() * (ht.clone() - five.clone()) * (w(HELD_AUTH_TAG) - ht.clone()),
                );
            }

            // ===== GATE 5: EXPIRY-MONOTONE — granted_expiry ⊑ held_expiry.
            // The encoded-expiry leaf felt (encode_expiry) is NONE_SENTINEL for
            // "no bound" (⊤) or a Poseidon2 FOLD of the height for a finite bound
            // — and the fold is NOT order-preserving, so a felt-≤ would be wrong.
            // We instead range-check the RAW heights, binding each raw height to
            // its authenticated leaf felt via the in-circuit encode_expiry fold:
            //   * h_none / g_none booleans, each ⇒ the leaf expiry == NONE_SENTINEL;
            //   * NOT-None ⇒ leaf expiry == encode_expiry(raw_height) (the fold
            //     site), pinning raw_height to the genuine committed height
            //     (Poseidon2 injective);
            //   * granted None ⇒ held None (can't widen a finite bound to ∞);
            //   * both finite ⇒ granted_raw ≤ held_raw via a 30-bit reconstruction
            //     of (p-1)/2 - (held_raw - granted_raw) (heights < 2^30 < (p-1)/2,
            //     so the field difference equals the integer difference iff
            //     granted ≤ held; a widening wraps past (p-1)/2 ⇒ no 30-bit
            //     witness ⇒ UNSAT — the revocation tree's ORDERING_BITS soundness).
            {
                let none_sent = lift::<AB>(crate::cap_root::SENTINEL_MAX);
                let g_none = w(GRANTED_EXPIRY_IS_NONE);
                let h_none = w(HELD_EXPIRY_IS_NONE);
                tb.assert_zero(s.clone() * g_none.clone() * (g_none.clone() - one.clone()));
                tb.assert_zero(s.clone() * h_none.clone() * (h_none.clone() - one.clone()));
                // None ⇒ leaf expiry == NONE_SENTINEL.
                tb.assert_zero(s.clone() * g_none.clone() * (w(GRANTED_EXPIRY) - none_sent.clone()));
                tb.assert_zero(s.clone() * h_none.clone() * (w(HELD_EXPIRY) - none_sent.clone()));
                // NOT-None ⇒ leaf expiry == encode_expiry(raw) = the fold digest.
                // (1 - none) * (leaf_expiry - fold) == 0.
                tb.assert_zero(
                    s.clone()
                        * (one.clone() - h_none.clone())
                        * (w(HELD_EXPIRY) - attn_d.held_exp_fold.clone()),
                );
                tb.assert_zero(
                    s.clone()
                        * (one.clone() - g_none.clone())
                        * (w(GRANTED_EXPIRY) - attn_d.granted_exp_fold.clone()),
                );
                // granted None ⇒ held None (else widening a finite bound to ∞).
                tb.assert_zero(s.clone() * g_none.clone() * (one.clone() - h_none.clone()));

                // Both finite ⇒ granted_raw ≤ held_raw (30-bit reconstruction).
                let both_finite = (one.clone() - g_none.clone()) * (one.clone() - h_none.clone());
                let half_p = AB::Expr::from_u64(crate::dsl::revocation::HALF_P_MINUS_1 as u64);
                let mut recomposed = AB::Expr::ZERO;
                for i in 0..EXPIRY_DIFF_BITS {
                    let b = w(EXPIRY_DIFF_BITS_BASE + i);
                    tb.assert_zero(s.clone() * b.clone() * (b.clone() - one.clone()));
                    recomposed = recomposed + b * AB::Expr::from_u64(1u64 << i);
                }
                // recomposed + (held_raw - granted_raw) - (p-1)/2 == 0 (both finite).
                tb.assert_zero(
                    s.clone()
                        * both_finite
                        * (recomposed + w(HELD_EXPIRY_RAW) - w(GRANTED_EXPIRY_RAW) - half_p),
                );
            }

            let _ = (attn_d.held_leaf.clone(), w(CUSTOM_VK_EQ_INV));
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

        // ===== GROUP 4: state-commit integrity (hash sites 0..3) =====
        //
        // ANTI-GHOST, ALL-ROWS (incl. the LAST row). This binding is the entire
        // reason this AIR exists: the published post-state commitment MUST equal
        // the genuine Poseidon2 digest of the genuine final state. It is emitted
        // on the WHOLE domain via the unfiltered `builder` (NOT `when_transition`)
        // so the last row (row n-1) is covered. Were it under `when_transition`,
        // the last row's STATE_COMMIT column would be pinned ONLY by the boundary
        // `STATE_COMMIT == NEW_COMMIT` (line below) to the attacker-chosen public
        // input, fully decoupled from the executed effects' hash — an arbitrary
        // post-state commitment could be forged. The full digest dependency chain
        // (state_commit = H4(inter1,inter2,inter3,0); inter1..3 = H4 of the
        // after-state cells) is already enforced on ALL rows because the
        // `poseidon2_permute_expr` round constraints for sites 0..3 are emitted
        // via `builder` (see the digest loop above), not `tb`. So pinning
        // `sa(STATE_COMMIT) == digests[STATE_COMMIT]` here on every row forces the
        // last-row STATE_COMMIT to the genuine digest; combined with the last-row
        // boundary `STATE_COMMIT == NEW_COMMIT`, NEW_COMMIT is forced genuine.
        //
        // Honest-prover soundness on every row: `extend_trace_with_hashes` /
        // `generate_effect_vm_trace` fill `state_after[STATE_COMMIT]` (and the
        // STATE_INTER aux cells) with the refreshed commitment on EVERY row,
        // including NoOp padding rows, so this holds for the honest witness.
        builder.assert_zero(sa(state::STATE_COMMIT) - digests[hs::STATE_COMMIT].clone());
        // The intermediate aux columns must equal their hashes (binds inter1..3),
        // also on every row.
        builder.assert_zero(aux(aux_off::STATE_INTER1) - digests[0].clone());
        builder.assert_zero(aux(aux_off::STATE_INTER2) - digests[1].clone());
        builder.assert_zero(aux(aux_off::STATE_INTER3) - digests[2].clone());

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
        // ---- DRIFT FIX (circuit-correspondence differential): the following
        // first-row boundary pins are in `EffectVmAir::boundary_constraints` but
        // were DROPPED from the original hand-port. Without them the audited p3
        // verifier accepts turns the constraint reference REJECTS — a forged
        // actor nonce (#49 AIR nonce-bump invisibility), a swapped sovereign
        // witness identity, or a proof minted under the wrong federation / owner
        // cell. Each is restored here term-for-term from the reference. The
        // `effect_vm_p3_descriptor_differential` test pins this set going forward.
        //
        // Row-0 actor-nonce binding (γ.0a turn-identity): state_before.nonce ==
        // PI[ACTOR_NONCE].
        fb_.assert_zero(lc(STATE_BEFORE_BASE + state::NONCE) - pv[pi::ACTOR_NONCE].clone());
        // Sovereign-witness identity: row-0 witness-key-commit + sequence aux
        // columns pinned to their PI slots (sentinel-zero on the hosted path).
        fb_.assert_zero(
            lc(AUX_BASE + aux_off::WITNESS_KEY_COMMIT_0)
                - pv[pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE].clone(),
        );
        fb_.assert_zero(
            lc(AUX_BASE + aux_off::WITNESS_KEY_COMMIT_1)
                - pv[pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE + 1].clone(),
        );
        fb_.assert_zero(
            lc(AUX_BASE + aux_off::WITNESS_KEY_COMMIT_2)
                - pv[pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE + 2].clone(),
        );
        fb_.assert_zero(
            lc(AUX_BASE + aux_off::WITNESS_KEY_COMMIT_3)
                - pv[pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE + 3].clone(),
        );
        fb_.assert_zero(
            lc(AUX_BASE + aux_off::WITNESS_SEQUENCE) - pv[pi::SOVEREIGN_WITNESS_SEQUENCE].clone(),
        );
        // Federation / owner-cell binding: a proof minted under one federation
        // (resp. owner cell) cannot claim a PI federation/owner disagreeing with
        // the row-0 aux columns its trace committed.
        for i in 0..pi::FEDERATION_ID_LEN {
            fb_.assert_zero(
                lc(AUX_BASE + aux_off::FEDERATION_ID_0 + i)
                    - pv[pi::FEDERATION_ID_BASE + i].clone(),
            );
        }
        for i in 0..pi::OWNER_CELL_ID_LEN {
            fb_.assert_zero(
                lc(AUX_BASE + aux_off::OWNER_CELL_ID_0 + i)
                    - pv[pi::OWNER_CELL_ID_BASE + i].clone(),
            );
        }

        let mut lb = builder.when_last_row();
        lb.assert_zero(lc(STATE_AFTER_BASE + state::STATE_COMMIT) - pv[pi::NEW_COMMIT].clone());
        lb.assert_zero(lc(STATE_AFTER_BASE + state::BALANCE_LO) - pv[pi::FINAL_BAL_LO].clone());
        lb.assert_zero(lc(STATE_AFTER_BASE + state::BALANCE_HI) - pv[pi::FINAL_BAL_HI].clone());
        // ---- DRIFT FIX (continued): the custom-effect count sum-check closes on
        // the LAST row (`aux[CUSTOM_COUNT_ACC] == PI[CUSTOM_EFFECT_COUNT]`). The
        // hand-port ported only the row-0 anchor (`== 0`) above, leaving the
        // count unbound — a prover could claim any CUSTOM_EFFECT_COUNT.
        lb.assert_zero(
            lc(AUX_BASE + aux_off::CUSTOM_COUNT_ACC) - pv[pi::CUSTOM_EFFECT_COUNT].clone(),
        );
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

/// Extend each base-width (`EFFECT_VM_WIDTH`) trace row to the full p3 width,
/// with the Attenuate scalar-witness block filled with ZEROS (no Phase-B
/// witness). Non-Attenuate rows are unaffected (their gates don't fire); a bare
/// Attenuate row with a zeroed witness will (correctly) FAIL the Phase-B gates.
/// An honest witnessed Attenuate turn goes through
/// [`extend_trace_with_attenuation`] instead.
pub fn extend_trace_with_hashes(trace: &[Vec<BabyBear>]) -> Vec<Vec<BabyBear>> {
    extend_trace_inner(trace, None)
}

/// Extend a base trace where row `r` carries the Phase-B Attenuate scalar
/// witness `scalar_blocks[r]` (length [`attn::ATTN_SCALAR_COLS`]; the all-zero
/// block for non-Attenuate rows). Produces the full p3-width trace whose
/// Attenuate gates can be SATISFIED on the witnessed Attenuate rows.
pub fn extend_trace_with_attenuation(
    trace: &[Vec<BabyBear>],
    scalar_blocks: &[Vec<BabyBear>],
) -> Vec<Vec<BabyBear>> {
    assert_eq!(trace.len(), scalar_blocks.len(), "one scalar block per row");
    extend_trace_inner(trace, Some(scalar_blocks))
}

fn extend_trace_inner(
    trace: &[Vec<BabyBear>],
    scalar_blocks: Option<&[Vec<BabyBear>]>,
) -> Vec<Vec<BabyBear>> {
    let sites = hash_sites();
    let generic_end = EFFECT_VM_WIDTH + sites.len() * POSEIDON2_PERM_AUX_COLS;
    let scalar_end = attn::attn_hash_base(); // generic_end + ATTN_SCALAR_COLS
    let full_width = effect_vm_p3_width();
    trace
        .iter()
        .enumerate()
        .map(|(r, row)| {
            // (1) base 186 columns.
            let mut full = row[..EFFECT_VM_WIDTH].to_vec();
            // (2) generic hash-site blocks, computed from the base portion.
            let mut digests: Vec<BabyBear> = Vec::with_capacity(sites.len());
            for site in &sites {
                let input = site_input_state_concrete(site, row, &digests);
                let auxw = poseidon2_permute_aux_witness(input);
                let digest = auxw[auxw.len() - POSEIDON2_WIDTH];
                digests.push(digest);
                full.extend(auxw);
            }
            debug_assert_eq!(full.len(), generic_end);
            // (3) Attenuate scalar block: from the supplied witness, else zeros.
            match scalar_blocks {
                Some(blocks) => {
                    debug_assert_eq!(blocks[r].len(), attn::ATTN_SCALAR_COLS);
                    full.extend_from_slice(&blocks[r]);
                }
                None => full.extend(std::iter::repeat(BabyBear::ZERO).take(attn::ATTN_SCALAR_COLS)),
            }
            debug_assert_eq!(full.len(), scalar_end);
            // (4) Attenuate Poseidon2 hash blocks, computed from the scalar block.
            let attn_aux = attenuate_hash_witness(&full);
            full.extend(attn_aux);
            debug_assert_eq!(full.len(), full_width);
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

// ============================================================================
// CIRCUIT-CORRESPONDENCE DIFFERENTIAL — the running p3 AIR vs the constraint
// reference it claims to mirror.
//
// `EffectVmP3Air::eval` is documented as a *term-for-term symbolic mirror* of
// the bespoke `EffectVmAir::eval_constraints`. The audited p3 verifier is sound
// about THIS AIR's constraints; if those constraints drifted from the reference
// the soundness would be about the wrong circuit. These helpers expose a
// CONCRETE, FRI-free decision for the running p3 AIR (via Plonky3's own
// `check_all_constraints`, the canonical debug constraint checker that both
// uni-stark and batch-stark use) so a differential test can assert the running
// AIR and the reference decide accept/reject IDENTICALLY over a shared witness
// corpus — honest AND tampered. A trace one accepts and the other rejects is a
// drift and FAILS the test.
//
// The decision returned here is the SAME predicate the audited verifier
// enforces — `check_all_constraints` evaluates exactly `EffectVmP3Air::eval`
// over the trace (with the genuine wrap-around `next` window and the
// first/last/transition selectors), so "all constraints satisfied" here ⟺ the
// prover can build a verifying proof there. It is purely deterministic (no
// random FRI queries), so the differential has a sharp, reproducible tooth.
// ============================================================================

/// Concrete accept/reject decision of the RUNNING p3 AIR (`EffectVmP3Air`) on a
/// base Effect-VM trace + public inputs, via Plonky3's `check_all_constraints`.
///
/// `base_trace` is the bespoke trace (`EFFECT_VM_WIDTH` columns); it is extended
/// with the Poseidon2 aux blocks exactly as the prover does
/// ([`extend_trace_with_hashes`]) before constraint checking, so the hash-site
/// gadget constraints are exercised on real witness data.
///
/// Returns `true` iff EVERY constraint of `EffectVmP3Air::eval` vanishes on
/// every row (the exact predicate the audited p3 verifier accepts).
pub fn p3_air_accepts(base_trace: &[Vec<BabyBear>], public_inputs: &[BabyBear]) -> bool {
    let air = EffectVmP3Air;
    let full_trace = extend_trace_with_hashes(base_trace);
    let matrix = to_matrix(&full_trace);
    let pis: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();
    let report = p3_air::check_all_constraints(&air, &matrix, &pis, Some(1));
    report.is_ok()
}

/// Concrete accept/reject decision of the REFERENCE constraint system — the
/// bespoke `EffectVmAir::eval_constraints` body the p3 AIR mirrors term-for-term
/// — on the SAME base trace + public inputs, using the SAME row-window semantics
/// `check_all_constraints` uses for the p3 AIR (the `next` row wraps around at
/// the last row).
///
/// The bespoke evaluator alpha-folds every constraint into one field element;
/// it accepts a row iff that fold is zero. To make the fold a faithful AND of
/// the individual gates (a fold could spuriously cancel for one unlucky alpha),
/// we require it to vanish for EVERY alpha in `alphas` — a non-trivial gate
/// makes the fold a non-zero polynomial in alpha with at most (#gates) roots,
/// so several independent alphas pin "all gates satisfied" with overwhelming
/// confidence and zero false-accepts in practice.
///
/// The reference decision = ALL transition gates vanish on every (wrap-around)
/// row AND ALL boundary pins (`EffectVmAir::boundary_constraints`) hold. This is
/// the same constraint set the p3 AIR's `eval` enforces (its `when_transition`
/// gates + its `when_first_row` / `when_last_row` boundary asserts), so a
/// disagreement between this and [`p3_air_accepts`] is a genuine drift.
///
/// Returns `true` iff the reference accepts.
pub fn bespoke_air_accepts(
    base_trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    alphas: &[BabyBear],
) -> bool {
    use crate::effect_vm::EffectVmAir;
    use crate::stark::StarkAir;
    let air = EffectVmAir::new(base_trace.len());
    let n = base_trace.len();

    // (1) Transition gates: `eval_constraints` folded to zero on every
    //     TRANSITION row (0..n-1), for every probe alpha (so the fold faithfully
    //     ANDs the individual gates). The bespoke prover divides the whole
    //     constraint polynomial by Z_T, so `eval_constraints` is enforced on
    //     rows 0..n-2 exactly — the SAME domain the p3 AIR's `when_transition()`
    //     covers. (The last row n-1 carries no `eval_constraints` obligation in
    //     either circuit; its post-state commitment is pinned by the boundary
    //     below, and additionally by the p3 AIR's unconditional GROUP-4
    //     last-row anti-ghost binding — a strengthening checked separately.)
    for row in 0..n.saturating_sub(1) {
        let next = &base_trace[row + 1];
        let local = &base_trace[row];
        for &alpha in alphas {
            let c = air.eval_constraints(local, next, public_inputs, alpha);
            if c != BabyBear::ZERO {
                return false;
            }
        }
    }

    // (2) Boundary pins: each `(row, col, value)` must hold exactly.
    for bc in air.boundary_constraints(public_inputs, n) {
        if base_trace[bc.row][bc.col] != bc.value {
            return false;
        }
    }
    true
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

    /// Control: a NON-last-row STATE_COMMIT trace-cell forgery (row 0's
    /// after-state commit cell decoupled from its genuine digest) MUST be
    /// rejected. This was already covered by the transition-domain GROUP-4
    /// binding; the fix keeps it covered (the all-rows binding subsumes it).
    #[test]
    fn forged_non_last_row_state_commit_trace_cell_rejected_by_audited_p3() {
        let initial = CellState::new(1000, 0);
        // Two effects so row 0 is a real, non-last row.
        let effects = vec![
            VmEffect::Transfer { amount: 100, direction: 1 },
            VmEffect::Transfer { amount: 50, direction: 0 },
        ];
        let (trace, pis) = generate_effect_vm_trace(&initial, &effects);
        assert!(trace.len() >= 2, "need a non-last row to forge");

        let mut forged_trace = trace.clone();
        let honest_commit = forged_trace[0][STATE_AFTER_BASE + state::STATE_COMMIT];
        forged_trace[0][STATE_AFTER_BASE + state::STATE_COMMIT] =
            honest_commit + BabyBear::new(1);

        let outcome = std::panic::catch_unwind(|| {
            prove_effect_vm_p3(&forged_trace, &pis)
                .and_then(|p| verify_effect_vm_p3(&p, &pis))
        });
        let accepted = matches!(outcome, Ok(Ok(())));
        assert!(
            !accepted,
            "FORGED non-last-row STATE_COMMIT trace cell MUST be rejected"
        );
    }

    /// THE LAST-ROW ANTI-GHOST TOOTH (the GROUP-4 hole this fix closes): an
    /// adversary forges BOTH the last row's `STATE_AFTER.STATE_COMMIT` trace
    /// cell AND the matching `pis[NEW_COMMIT]` to an arbitrary value
    /// (honest + 1), trying to publish a post-state commitment decoupled from
    /// the genuine Poseidon2 hash of the executed effects. Before the fix, the
    /// last-row STATE_COMMIT integrity binding was under `when_transition()`
    /// and so was NOT enforced on row n-1 — the only last-row constraint pinned
    /// STATE_COMMIT to the attacker-chosen NEW_COMMIT, and this forgery
    /// VERIFIED. With the fix (GROUP-4 binding emitted on ALL rows via the
    /// unfiltered builder), `digests[STATE_COMMIT]` is recomputed from the
    /// genuine after-state cells (STATE_COMMIT is NOT a hash input), so the
    /// forged STATE_COMMIT cell cannot equal the genuine digest and
    /// proving-or-verifying MUST FAIL.
    #[test]
    fn forged_last_row_state_commit_trace_cell_rejected_by_audited_p3() {
        let initial = CellState::new(1000, 0);
        let effects = vec![VmEffect::Transfer { amount: 100, direction: 1 }];
        let (trace, pis) = generate_effect_vm_trace(&initial, &effects);

        // Sanity: the honest version proves+verifies.
        let honest = prove_effect_vm_p3(&trace, &pis).expect("honest proof");
        verify_effect_vm_p3(&honest, &pis).expect("honest verify");

        // Forge BOTH the last-row trace STATE_COMMIT cell AND the NEW_COMMIT PI
        // to (honest + 1), keeping them mutually consistent so the last-row
        // boundary `STATE_COMMIT == NEW_COMMIT` is satisfied. The ONLY thing
        // that can now reject this is the all-rows GROUP-4 genuine-digest bind.
        let last = trace.len() - 1;
        let mut forged_trace = trace.clone();
        let honest_commit = forged_trace[last][STATE_AFTER_BASE + state::STATE_COMMIT];
        forged_trace[last][STATE_AFTER_BASE + state::STATE_COMMIT] =
            honest_commit + BabyBear::new(1);

        let mut forged_pis = pis.clone();
        forged_pis[pi::NEW_COMMIT] = forged_pis[pi::NEW_COMMIT] + BabyBear::new(1);

        // The prover self-verifies before returning; with the fix it must be
        // unable to satisfy the constraints (panic inside prove) OR the verify
        // step rejects. Either way the forgery must NOT yield an accepted proof.
        let outcome = std::panic::catch_unwind(|| {
            prove_effect_vm_p3(&forged_trace, &forged_pis)
                .and_then(|p| verify_effect_vm_p3(&p, &forged_pis))
        });
        let accepted = matches!(outcome, Ok(Ok(())));
        assert!(
            !accepted,
            "FORGED last-row STATE_COMMIT (trace cell + NEW_COMMIT PI) MUST be \
             rejected by the audited p3 verifier — the GROUP-4 anti-ghost hole \
             is NOT closed"
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
