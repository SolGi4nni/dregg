//! **THE CUSTOM-PROOF STATE-BINDING ABI** — the canonical public-input prefix that
//! makes a custom sub-proof provably ABOUT a specific cell-state transition.
//!
//! ## The gap this closes
//!
//! `Effect::Custom` binds two things into the EffectVM's public inputs
//! (`pi::CUSTOM_PROOFS_BASE + i*16`): the sub-program's `vk_hash` (8 felts) and a
//! `custom_proof_commitment` (8 felts) = [`custom_proof_pi_commitment_8`] over the
//! sub-proof's public inputs. The deployed fold
//! (`dregg_circuit_prove::joint_turn_recursive::prove_custom_binding_node_segmented`)
//! `connect`s that CLAIMED commitment, lane by lane, to the commitment the custom leaf
//! computes IN-CIRCUIT from the sub-proof's REAL public inputs — so a claimed commitment
//! no verifying sub-proof backs is UNSAT.
//!
//! That chain binds **which public inputs the sub-proof used**. It does NOT bind what
//! those public inputs SAY. The commitment is an opaque hash: nothing required the
//! sub-proof's PIs to mention the cell's pre-state or post-state at all. So a custom AIR
//! could prove a beautiful transition `R1 -> R2` while the turn commits `S1 -> S2`, with
//! `R1 != S1` and `R2 != S2`, and every existing gate passed. The custom proof verified;
//! it was simply not ABOUT the state the turn committed.
//!
//! ## The ABI
//!
//! A state-binding custom proof's public inputs are, by construction:
//!
//! ```text
//!   pis[0..8]   = the cell's PRE-state  commitment (the leg's tail PI [n-16..n-8))
//!   pis[8..16]  = the cell's POST-state commitment (the leg's tail PI [n-8..n))
//!   pis[16..]   = application-specific (the game's board roots, move seals, …)
//! ```
//!
//! **WHICH 8-felt commitment (read this — two different values in this system are both
//! called "the commitment"):** the prefix is the deployed **v9 CHIP commit** —
//! `dregg_cell::commitment::bytes32_to_felt8` of the stored/claimed 32-byte commitment,
//! i.e. `compute_canonical_state_commitment_v9_felt8` = `wire_commit_8_chip` over the
//! cell's 178 rotated pre-limbs + iroot (the byte-twin of the circuit's `fill_wide_block`).
//! That is the value the executor holds, the value the WIDE leg publishes in its LAST 16
//! descriptor PIs, and the value the in-circuit fold connects against.
//!
//! It is **NOT** `CellState::compute_commitment_8`, and **NOT** the EffectVM
//! `PI[OLD_COMMIT_BASE..+8]` / `PI[NEW_COMMIT_BASE..+8]` prefix slots. That legacy
//! bundle-path commitment is a 5-node `hash_4_to_1` tree over
//! `balance/nonce/fields[8]/cap_root/record_digest` — a different function over a strict
//! SUBSET of the limbs, with no cells_root, no map roots, no iroot. The two values are not
//! two encodings of one commitment and can never be equal; nothing pins them to each other.
//! (This doc previously named those two — the prose had drifted from the wire. The
//! executor's comparands, below, are and were the v9 chip commit.)
//!
//! ## Why the prefix rides for free
//!
//! [`custom_proof_pi_commitment_8`] hashes the WHOLE public-input vector. So the moment
//! the state roots are IN the PIs, they are already covered by the commitment the
//! `Effect::Custom` row carries and the fold binds in-circuit. No new EffectVM PI slot, no
//! new trace column, no descriptor change, no VK rotation — the binding surface already
//! exists; this module fixes what MUST occupy its preimage.
//!
//! ## The two teeth (and their exact reach)
//!
//! 1. **Off-AIR, executor (LANDED here):**
//!    `dregg_turn::executor::proof_verify::TurnExecutor::enforce_custom_proof_state_binding`
//!    recomputes [`custom_proof_pi_commitment_8`] over the wire sub-proof's PIs and
//!    requires (a) it equals the in-circuit-committed `custom_proof_commitment`, and
//!    (b) the PI prefix equals the turn's OLD/NEW state commitments. This is what an
//!    EXECUTOR (and any re-executing validator) enforces.
//!
//! 2. **In-circuit, fold (LANDED — and the DEPLOYED DEFAULT):** the dual-expose leg leaf
//!    carries the descriptor-bound REAL roots in its exposed segment
//!    (`ivc_turn_chain::SEG_FIRST_OLD` lanes `0..8`, `SEG_LAST_NEW` lanes `8..16`). The
//!    custom leaf's `expose_claim` is widened from `[commitment(8)]` to
//!    `[commitment(8) ‖ pis[0..16]]`
//!    (`dregg_circuit_prove::custom_leaf_adapter::prove_custom_leaf_with_state_commitment`),
//!    and `dregg_circuit_prove::joint_turn_recursive::prove_custom_binding_node_state_segmented`
//!    `connect`s those 16 lanes to the leg's segment lanes. The deployed chain prover
//!    (`ivc_turn_chain::prove_chain_core_rotated`'s Custom arm) mints THAT pair — so a
//!    custom sub-proof whose declared roots are not the leg's real rotated roots has no
//!    satisfying partner: UNSAT, no root, and the light client never receives a verifying
//!    artifact.
//!
//! A PURE LIGHT CLIENT (folding only the recursion tree, never re-running the executor) now
//! witnesses BOTH "a sub-proof backs this commitment" AND "its PIs are this cell's roots".
//!
//! The two teeth are deliberately kept, and they are not redundant: tooth 1 refuses the
//! turn at admission (cheap, before any STARK), tooth 2 makes the refusal a property of the
//! ARTIFACT rather than of the verifier's diligence. Tooth 2 is not a conditional gate —
//! the state node REQUIRES the 24-lane claim, so a prover cannot dodge it by minting the
//! narrow leaf.
//!
//! **The ABI is now load-bearing on the prover side.** A sub-program publishing fewer than
//! `CUSTOM_PI_STATE_PREFIX_LEN` PIs is refused by the deployed prover, exactly as it was
//! already refused by the deployed executor. A custom carrier must publish the prefix.

use crate::field::BabyBear;

/// Offset of the PRE-state commitment in a state-binding custom proof's public inputs.
pub const CUSTOM_PI_OLD_COMMIT_BASE: usize = 0;
/// Width of the PRE-state commitment (the 8-felt Poseidon2 form the EffectVM binds).
pub const CUSTOM_PI_OLD_COMMIT_LEN: usize = 8;
/// Offset of the POST-state commitment in a state-binding custom proof's public inputs.
pub const CUSTOM_PI_NEW_COMMIT_BASE: usize = CUSTOM_PI_OLD_COMMIT_BASE + CUSTOM_PI_OLD_COMMIT_LEN;
/// Width of the POST-state commitment.
pub const CUSTOM_PI_NEW_COMMIT_LEN: usize = 8;
/// Total felts the state-binding prefix occupies. Application public inputs start here.
pub const CUSTOM_PI_STATE_PREFIX_LEN: usize = CUSTOM_PI_NEW_COMMIT_BASE + CUSTOM_PI_NEW_COMMIT_LEN;

/// Domain separator for the custom sub-proof's public-input commitment.
///
/// **Byte-identical to `dregg_circuit_prove::custom_proof_bind::CUSTOM_PROOF_PI_DOMAIN`**
/// and to [`crate::effect_vm::trace_rotated::DFA_ROUTE_COMMIT_DOMAIN`]. Duplicated here
/// because `dregg-circuit` cannot depend on `dregg-circuit-prove` (the verify floor must
/// not pull the prover); the cross-pin test
/// `circuit-prove/tests/custom_state_binding_cross_pin.rs` fails loudly on any drift.
pub const CUSTOM_PROOF_PI_DOMAIN: &str = "dregg-custom-proof-bind-pi-v1";

/// The canonical 8-felt commitment to a custom sub-proof's public inputs — the value the
/// `Effect::Custom` row carries and the fold binds in-circuit.
///
/// **Byte-identical to `dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment`**
/// (same domain, same `WideHash::from_poseidon2` full 8-felt squeeze). This copy exists so
/// the VERIFY floor (`dregg-turn`'s executor, which must not depend on the prover) can
/// recompute the commitment from a wire sub-proof's PIs and reject a mismatch.
pub fn custom_proof_pi_commitment_8(public_inputs: &[BabyBear]) -> [BabyBear; 8] {
    crate::binding::WideHash::from_poseidon2(CUSTOM_PROOF_PI_DOMAIN, public_inputs).to_felts()
}

/// Build the canonical state-binding public-input prefix for a custom sub-proof that
/// attests the transition `old_commit8 -> new_commit8`.
///
/// A custom program's own public inputs are appended after this prefix:
/// `[state_binding_prefix(old, new), ..app_pis].concat()`.
pub fn custom_pi_state_prefix(
    old_commit8: &[BabyBear; 8],
    new_commit8: &[BabyBear; 8],
) -> [BabyBear; CUSTOM_PI_STATE_PREFIX_LEN] {
    let mut out = [BabyBear::ZERO; CUSTOM_PI_STATE_PREFIX_LEN];
    out[CUSTOM_PI_OLD_COMMIT_BASE..CUSTOM_PI_OLD_COMMIT_BASE + CUSTOM_PI_OLD_COMMIT_LEN]
        .copy_from_slice(old_commit8);
    out[CUSTOM_PI_NEW_COMMIT_BASE..CUSTOM_PI_NEW_COMMIT_BASE + CUSTOM_PI_NEW_COMMIT_LEN]
        .copy_from_slice(new_commit8);
    out
}

/// Read the (pre, post) state commitments a state-binding custom proof's public inputs
/// claim. Returns `None` when the vector is too short to carry the prefix — a proof that
/// cannot even express the binding, which the executor refuses fail-closed rather than
/// zero-padding into a false match.
pub fn extract_custom_pi_state_roots(
    public_inputs: &[BabyBear],
) -> Option<([BabyBear; 8], [BabyBear; 8])> {
    if public_inputs.len() < CUSTOM_PI_STATE_PREFIX_LEN {
        return None;
    }
    let old = core::array::from_fn(|j| public_inputs[CUSTOM_PI_OLD_COMMIT_BASE + j]);
    let new = core::array::from_fn(|j| public_inputs[CUSTOM_PI_NEW_COMMIT_BASE + j]);
    Some((old, new))
}

// ============================================================================
// THE APP-ROOT WELD ABI — the keystone: force an app's PUBLISHED root R to EQUAL
// the cell's REAL committed field value, visible to a pure light client.
// ============================================================================
//
// The state prefix above ties a custom sub-proof's `[old8 ‖ new8]` PIs to the cell's real
// rotated roots — so a pure light client witnesses that the transition is about THIS cell's
// pre/post commitments. But an application (automatafl's board_new_root8, tug's winner,
// param-compose/entity-compose's outcome_commitment) ALSO publishes an application ROOT `R` in
// its app PIs (past the state prefix). `R` is BOUND (covered by the sub-proof's PI commitment,
// which the fold connects, so a prover cannot swap it post-hoc) but it is NOT TIED to what the
// cell actually STORES: nothing forces `R == the committed field the app wrote it into`. The
// `new8` commitment commits the WHOLE post-state (every cell field), but it is an opaque hash —
// the CellProgram constraint vocabulary cannot open it to re-expose one field, and a prover who
// picks BOTH the field value it writes AND the `R` it publishes makes them agree trivially.
//
// The sound GENERAL form is an IN-CIRCUIT TIE at the fold node: the wide effect-VM leg exposes
// the cell's committed value for a DECLARED field key `K` (a value carried faithfully in the
// rotated pre-limbs the `new8` commitment absorbs), and the fold `connect`s it, lane by lane, to
// the sub-proof's published `R` at a DECLARED PI offset `j`. Then `new8` (welded to the leg's
// real root) commits the field, the leg exposes that same committed field, and the connect forces
// `R == field[K]` — a property of the ARTIFACT a pure light client verifies, not of an executor's
// diligence.
//
// This module carries the APP-DECLARED half of that ABI: where `R` sits in the sub-proof PIs
// (`j`, width `L`) and which cell field key `K` it must equal. The leg-side exposure of `field[K]`
// and the fold connect live in `dregg-circuit-prove` (the prover), the way the state weld's leg
// exposure and connect do — this floor crate must not pull the prover.

/// An application-root weld declaration: the sub-proof's published root `R` occupies
/// `pis[app_root_pi_offset .. app_root_pi_offset + app_root_len]` and MUST equal the cell's
/// committed value at wide-leg field key `field_key`.
///
/// `app_root_pi_offset` is an APP PI index (past the state prefix, so `>= CUSTOM_PI_STATE_PREFIX_LEN`
/// — an app root overlapping the state commitments is refused). `app_root_len` is the root's width
/// in felts (`1` for a scalar register like tug's `winner`, `8` for an octet root like automatafl's
/// `board_new_root8` or the compose `outcome_commitment`). `field_key` is opaque to this floor
/// crate — the prover maps it to the leg's field-exposure PI slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AppRootBinding {
    /// `j`: the app PI index where the published root `R` begins.
    pub app_root_pi_offset: usize,
    /// `L`: the width of `R` in felts.
    pub app_root_len: usize,
    /// `K`: the cell field key `R` must equal (the leg exposes its committed value).
    pub field_key: usize,
}

impl AppRootBinding {
    /// Fail-closed validity: the root must sit strictly past the state prefix (never aliasing
    /// `[old8 ‖ new8]`) and have nonzero width. A binding that violates this cannot express the
    /// weld and is refused rather than silently welding the wrong lanes.
    pub fn is_well_formed(&self) -> bool {
        self.app_root_len > 0 && self.app_root_pi_offset >= CUSTOM_PI_STATE_PREFIX_LEN
    }

    /// The last PI index (exclusive) the root occupies — the minimum `public_input_count` a
    /// sub-program carrying this binding must publish.
    pub fn app_root_pi_end(&self) -> usize {
        self.app_root_pi_offset + self.app_root_len
    }
}

/// Read the published app root `R` a sub-proof's public inputs carry for `binding`. Returns `None`
/// when the binding is ill-formed or the vector is too short to carry `R` — never zero-padding a
/// short vector into a false root (the in-circuit mirror refuses the same shape fail-closed).
pub fn extract_custom_pi_app_root(
    public_inputs: &[BabyBear],
    binding: &AppRootBinding,
) -> Option<Vec<BabyBear>> {
    if !binding.is_well_formed() || public_inputs.len() < binding.app_root_pi_end() {
        return None;
    }
    Some(public_inputs[binding.app_root_pi_offset..binding.app_root_pi_end()].to_vec())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prefix_roundtrips_through_the_extractor() {
        let old: [BabyBear; 8] = core::array::from_fn(|j| BabyBear::new(100 + j as u32));
        let new: [BabyBear; 8] = core::array::from_fn(|j| BabyBear::new(200 + j as u32));
        let mut pis = custom_pi_state_prefix(&old, &new).to_vec();
        pis.extend_from_slice(&[BabyBear::new(7), BabyBear::new(9)]);

        let (got_old, got_new) = extract_custom_pi_state_roots(&pis).expect("prefix present");
        assert_eq!(got_old, old, "pre-state root must roundtrip");
        assert_eq!(got_new, new, "post-state root must roundtrip");
    }

    /// A vector too short to carry the prefix yields `None` — never a zero-padded
    /// "match" against a genuine all-zero root.
    #[test]
    fn short_public_inputs_do_not_zero_pad_into_a_binding() {
        let short = vec![BabyBear::ZERO; CUSTOM_PI_STATE_PREFIX_LEN - 1];
        assert!(
            extract_custom_pi_state_roots(&short).is_none(),
            "a PI vector too short to express the binding must not be readable as one"
        );
    }

    /// The commitment covers the WHOLE PI vector — so mutating the state prefix (the
    /// forgery the weld exists to catch) moves the commitment the fold binds. This is
    /// why the prefix rides the existing binding surface for free.
    #[test]
    fn commitment_moves_when_the_state_prefix_is_forged() {
        let old: [BabyBear; 8] = core::array::from_fn(|j| BabyBear::new(100 + j as u32));
        let new: [BabyBear; 8] = core::array::from_fn(|j| BabyBear::new(200 + j as u32));
        let honest = custom_pi_state_prefix(&old, &new).to_vec();

        let mut forged = honest.clone();
        forged[CUSTOM_PI_NEW_COMMIT_BASE] = BabyBear::new(999);

        assert_ne!(
            custom_proof_pi_commitment_8(&honest),
            custom_proof_pi_commitment_8(&forged),
            "a forged post-state root must move the PI commitment the fold connects"
        );
    }

    /// **THE BUDGET MEASUREMENT.** The weld's whole cost, measured against the deployed
    /// caps — not asserted. It rides the EXISTING binding surface: the state roots go
    /// into the custom sub-program's OWN public inputs, which the
    /// `custom_proof_commitment` already hashes in full. So:
    ///
    ///   * EffectVM trace columns:  +0  (`MAX_TRACE_WIDTH` = 1024 untouched)
    ///   * EffectVM constraints:    +0  (`MAX_CONSTRAINT_DEGREE` = 8 untouched)
    ///   * EffectVM PI slots:       +0  (no new `pi::` constant; `ACTIVE_BASE_COUNT` and
    ///                                   `CUSTOM_ENTRY_SIZE` are unchanged)
    ///   * custom sub-program PIs: +16  (the state prefix) out of `MAX_PUBLIC_INPUTS` = 64
    ///
    /// The only budget the weld spends is the sub-program's PI allowance, and it leaves
    /// 48 for the application. (For scale: automatafl's AIR publishes 2 PIs today.)
    #[test]
    fn the_weld_costs_no_effectvm_budget_and_leaves_48_app_public_inputs() {
        use crate::dsl::circuit::{MAX_CONSTRAINT_DEGREE, MAX_PUBLIC_INPUTS, MAX_TRACE_WIDTH};
        use crate::effect_vm::pi;

        // The EffectVM side is untouched — the weld adds no PI slot, so the custom entry
        // stride and the active base count are exactly what they were.
        assert_eq!(
            pi::CUSTOM_ENTRY_SIZE,
            16,
            "custom entry stride unchanged by the weld"
        );
        assert_eq!(
            pi::CUSTOM_PROOFS_BASE,
            pi::ACTIVE_BASE_COUNT,
            "the weld introduced no PI slot before the custom entries"
        );

        // The prefix fits the deployed program-validation caps with room to spare.
        assert!(
            CUSTOM_PI_STATE_PREFIX_LEN < MAX_PUBLIC_INPUTS,
            "the state-binding prefix ({CUSTOM_PI_STATE_PREFIX_LEN}) must fit the deployed \
             {MAX_PUBLIC_INPUTS}-PI cap"
        );
        assert_eq!(
            MAX_PUBLIC_INPUTS - CUSTOM_PI_STATE_PREFIX_LEN,
            48,
            "the weld must leave 48 public inputs for the application"
        );

        // Pinned so a future widening of the caps cannot silently reprice the weld.
        assert_eq!(MAX_TRACE_WIDTH, 1024);
        assert_eq!(MAX_CONSTRAINT_DEGREE, 8);
        assert_eq!(MAX_PUBLIC_INPUTS, 64);
    }

    /// The app-root binding's well-formedness gate: a root aliasing the state prefix, or of zero
    /// width, is refused (it cannot express the weld).
    #[test]
    fn app_root_binding_well_formedness() {
        let ok = AppRootBinding {
            app_root_pi_offset: CUSTOM_PI_STATE_PREFIX_LEN,
            app_root_len: 8,
            field_key: 0,
        };
        assert!(ok.is_well_formed());
        assert_eq!(ok.app_root_pi_end(), CUSTOM_PI_STATE_PREFIX_LEN + 8);

        // Aliases the state prefix.
        let aliased = AppRootBinding {
            app_root_pi_offset: 8,
            app_root_len: 8,
            field_key: 0,
        };
        assert!(!aliased.is_well_formed());
        // Zero width.
        let empty = AppRootBinding {
            app_root_pi_offset: CUSTOM_PI_STATE_PREFIX_LEN,
            app_root_len: 0,
            field_key: 0,
        };
        assert!(!empty.is_well_formed());
    }

    /// The extractor reads exactly the declared root lanes, and refuses (returns `None`) a vector
    /// too short to carry it — never zero-padding a short vector into a false root.
    #[test]
    fn app_root_extractor_reads_the_declared_lanes_or_refuses() {
        let old: [BabyBear; 8] = core::array::from_fn(|j| BabyBear::new(100 + j as u32));
        let new: [BabyBear; 8] = core::array::from_fn(|j| BabyBear::new(200 + j as u32));
        let r: [BabyBear; 8] = core::array::from_fn(|j| BabyBear::new(300 + j as u32));
        let mut pis = custom_pi_state_prefix(&old, &new).to_vec();
        pis.extend_from_slice(&r);

        let b = AppRootBinding {
            app_root_pi_offset: CUSTOM_PI_STATE_PREFIX_LEN,
            app_root_len: 8,
            field_key: 0,
        };
        assert_eq!(
            extract_custom_pi_app_root(&pis, &b).expect("root present"),
            r.to_vec()
        );

        // One short of R's end ⇒ None (never zero-padded).
        let short = &pis[..pis.len() - 1];
        assert!(extract_custom_pi_app_root(short, &b).is_none());
        // Ill-formed binding ⇒ None regardless of length.
        let bad = AppRootBinding {
            app_root_pi_offset: 0,
            app_root_len: 8,
            field_key: 0,
        };
        assert!(extract_custom_pi_app_root(&pis, &bad).is_none());
    }

    /// The published root rides the SAME commitment surface: mutating any lane of R (past the state
    /// prefix) moves the PI commitment the fold binds — so the app-root weld needs no new hash, only
    /// the fold connect.
    #[test]
    fn app_root_lanes_move_the_commitment() {
        let old: [BabyBear; 8] = core::array::from_fn(|j| BabyBear::new(100 + j as u32));
        let new: [BabyBear; 8] = core::array::from_fn(|j| BabyBear::new(200 + j as u32));
        let r: [BabyBear; 8] = core::array::from_fn(|j| BabyBear::new(300 + j as u32));
        let mut honest = custom_pi_state_prefix(&old, &new).to_vec();
        honest.extend_from_slice(&r);
        let base = custom_proof_pi_commitment_8(&honest);
        for k in 0..8 {
            let mut forged = honest.clone();
            forged[CUSTOM_PI_STATE_PREFIX_LEN + k] += BabyBear::ONE;
            assert_ne!(
                custom_proof_pi_commitment_8(&forged),
                base,
                "published-root lane {k} must be load-bearing in the PI commitment"
            );
        }
    }

    /// Every lane of both roots is load-bearing in the commitment: a node binding only
    /// some lanes would accept a forgery in the rest.
    #[test]
    fn every_state_prefix_lane_moves_the_commitment() {
        let old: [BabyBear; 8] = core::array::from_fn(|j| BabyBear::new(100 + j as u32));
        let new: [BabyBear; 8] = core::array::from_fn(|j| BabyBear::new(200 + j as u32));
        let honest = custom_pi_state_prefix(&old, &new).to_vec();
        let base = custom_proof_pi_commitment_8(&honest);

        for k in 0..CUSTOM_PI_STATE_PREFIX_LEN {
            let mut forged = honest.clone();
            forged[k] = forged[k] + BabyBear::ONE;
            assert_ne!(
                custom_proof_pi_commitment_8(&forged),
                base,
                "state-prefix lane {k} must be load-bearing in the PI commitment"
            );
        }
    }
}
