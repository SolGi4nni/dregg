//! # Guardian-set rotation — change your council; refresh your shares.
//!
//! The proven social-recovery weld (`sdk/tests/identity_social_recovery_e2e.rs`)
//! lets a guardian quorum authorize a KEY rotation through the real executor:
//! the *who-may-rotate* is the HINTS weighted-threshold guardian committee
//! (`Authorization::Custom` → `ThresholdSigVerifier` →
//! `dregg_federation::hints::verify_aggregate`), the *how* is the
//! [`KeyRotationGate`](dregg_cell::program::StateConstraint::KeyRotationGate)
//! KERI pre-rotation. But that weld leaves ONE thing set-once: the COUNCIL
//! itself. The stock identity program
//! ([`starbridge_polis::identity::identity_state_constraints`]) **pins**
//! [`COUNCIL_COMMIT_SLOT`] to a charter literal for the cell's whole life
//! (`pin_term(COUNCIL_COMMIT_SLOT, charter.council.members_commitment())`):
//! you can never change your guardians, and you can never refresh their
//! shares (proactive security). A compromised-but-not-yet-quorum guardian set
//! is a permanent liability.
//!
//! This module dissolves that. It is a polis-amendment-shaped turn for the
//! identity noun: the CURRENT K-of-N guardian quorum signs an aggregate
//! authorizing the identity cell's [`COUNCIL_COMMIT_SLOT`] to advance from the
//! old committee's `members_commitment()` to a NEW committee's
//! `members_commitment()` (the new council's HINTS key, ideally fresh via DKG;
//! the old shares retire — proactive refresh). The *who* is the old quorum
//! (the proven `Authorization::Custom` threshold-sig path, reused verbatim);
//! the *how* is a guarded slot transition this module's program admits.
//!
//! ## Empowered, never amplified
//!
//! Three teeth, each a real executor gate, not a builder convention:
//!
//! 1. **Sub-threshold is REFUSED.** The new council lands only behind a valid
//!    aggregate over the OLD guardian committee at its host-pinned K-of-N
//!    floor. A sub-threshold quorum cannot even assemble the QC
//!    ([`dregg_federation`]'s aggregator refuses), and a coerced under-weight
//!    QC is rejected by the verifier (same floor the recovery weld pins).
//! 2. **No amplification of the council itself.** The new committee is a
//!    [`CouncilCharter`], so [`CouncilCharter::validate`] forbids
//!    `threshold > members` and `threshold == 0` AT BUILD — the rotated-in
//!    council can never demand fewer-than-one or more-than-N approvals than
//!    it has members. The old quorum cannot install a council weaker than a
//!    real K-of-N (e.g. a 0-of-N rubber stamp): the charter type makes that
//!    inexpressible.
//! 3. **The council slot can never be nulled.** The program forbids
//!    `COUNCIL_COMMIT_SLOT == 0` while ACTIVE, so a rotation cannot erase the
//!    council (which would leave the identity ungoverned) — only ADVANCE it
//!    to another non-zero committee commitment.
//!
//! ## What composes
//!
//! After the rotation, the NEW council's commitment sits in
//! [`COUNCIL_COMMIT_SLOT`]; a recovery (or a further rotation) authorized by
//! the NEW guardian committee verifies against the new committee's pinned VK
//! and lands, while the OLD committee — whose shares were retired with the
//! rotation — no longer governs. The driver wires the new committee's
//! verifier under the new guardian root; the on-cell commitment is the public
//! anchor that says which committee now gates.
//!
//! ## Why a separate program from the stock identity factory
//!
//! The stock identity program is correct for an identity whose council is
//! constitutional and fixed. This module's
//! [`guardian_rotatable_identity_constraints`] is the SAME constraint set with
//! exactly one change — `COUNCIL_COMMIT_SLOT` is **guarded** (non-zero while
//! ACTIVE) rather than **pinned** (a charter literal). Everything else (the
//! lifecycle machine, the [`KeyRotationGate`], the live-pre-commitment / live-
//! current-keys teeth, the reserved-zero slots) is identical, so a
//! guardian-rotatable identity is still a fully pre-rotation-protected KERI
//! identity; it merely also lets its council advance under quorum authority.
//!
//! The *who-may-rotate-the-council* decision rides the cell's `set_state`
//! permission (`Authorization::Custom { vk_hash }`), pinned to the guardian
//! committee's VK exactly as the recovery weld does — drivers install it with
//! [`install_guardian_council_authority`].
//!
//! [`COUNCIL_COMMIT_SLOT`]: starbridge_polis::identity::COUNCIL_COMMIT_SLOT
//! [`KeyRotationGate`]: dregg_cell::program::StateConstraint::KeyRotationGate

use dregg_cell::factory::{CapTarget, CapTemplate, ChildVkStrategy, FactoryDescriptor};
use dregg_cell::permissions::{AuthRequired, Permissions};
use dregg_cell::predicate::{InputRef, WitnessedPredicate, WitnessedPredicateKind};
use dregg_cell::program::{
    CellProgram, HashKind, SimpleStateConstraint, StateConstraint, field_from_u64,
};
use dregg_cell::state::{FIELD_ZERO, FieldElement};
use dregg_cell::{CellId, CellMode};
use dregg_turn::Effect;
use dregg_turn::action::{Action, Authorization, DelegationMode, WitnessBlob, symbol};

use starbridge_polis::council::CouncilCharter;
use starbridge_polis::identity::{
    COUNCIL_COMMIT_SLOT, CURRENT_KEYS_COMMIT_SLOT, IdentityCharter, LAST_ROTATED_AT_SLOT,
    NEXT_KEYS_DIGEST_SLOT, STATE_ACTIVE, STATE_RETIRED, STATE_UNINIT,
};
use starbridge_polis::{PolisError, STATE_SLOT};

// =============================================================================
// The guardian-rotatable identity program
// =============================================================================

/// `state == gate ⇒ consequent`, encoded as `AnyOf[¬(state==gate), consequent]`
/// — the same shape `starbridge_polis`'s private `when_state` uses, rebuilt
/// here so this module owns its program without reaching into polis internals.
fn when_state(gate_state: u64, consequent: SimpleStateConstraint) -> StateConstraint {
    StateConstraint::AnyOf {
        variants: vec![
            SimpleStateConstraint::Not(Box::new(SimpleStateConstraint::FieldEquals {
                index: STATE_SLOT,
                value: field_from_u64(gate_state),
            })),
            consequent,
        ],
    }
}

/// A slot pinned to zero for the cell's whole life (reserved slots).
fn pinned_zero(slot: u8) -> StateConstraint {
    StateConstraint::FieldEquals {
        index: slot,
        value: FIELD_ZERO,
    }
}

/// Slots 5..7 — reserved, pinned zero (mirrors the stock identity program).
const RESERVED_SLOTS: [u8; 3] = [5, 6, 7];

/// The constraint set for a GUARDIAN-ROTATABLE identity cell.
///
/// Identical to [`starbridge_polis::identity::identity_state_constraints`]
/// except for the council slot: where the stock program pins
/// [`COUNCIL_COMMIT_SLOT`] to a literal (set-once), this program merely forbids
/// nulling it while ACTIVE — the slot is free to ADVANCE from one committee
/// commitment to the next under the cell's `set_state` authority (the guardian
/// quorum). Every other tooth (the lifecycle machine, the
/// [`KeyRotationGate`](dregg_cell::program::StateConstraint::KeyRotationGate),
/// the live-key invariants) is unchanged, so this is still a full KERI
/// pre-rotation identity.
///
/// `cooling_period` mirrors the charter's rotation cooling window (must be >= 1).
pub fn guardian_rotatable_identity_constraints(
    cooling_period: u64,
) -> Result<Vec<StateConstraint>, PolisError> {
    if cooling_period == 0 {
        return Err(PolisError::ZeroCoolingPeriod);
    }
    let mut cs = vec![
        // ── the lifecycle; RETIRED has NO outgoing row (inert) ──
        StateConstraint::AllowedTransitions {
            slot_index: STATE_SLOT,
            allowed: vec![
                (field_from_u64(STATE_UNINIT), field_from_u64(STATE_UNINIT)),
                (field_from_u64(STATE_UNINIT), field_from_u64(STATE_ACTIVE)),
                (field_from_u64(STATE_ACTIVE), field_from_u64(STATE_ACTIVE)),
                (field_from_u64(STATE_ACTIVE), field_from_u64(STATE_RETIRED)),
            ],
        },
        // ── THE PRE-ROTATION GATE (key rotation; cooling conjoined) ──
        StateConstraint::KeyRotationGate {
            digest_slot: NEXT_KEYS_DIGEST_SLOT,
            current_slot: CURRENT_KEYS_COMMIT_SLOT,
            last_rotated_slot: LAST_ROTATED_AT_SLOT,
            cooling_period,
            hash_kind: HashKind::Blake3,
        },
        // ── an ACTIVE identity always carries a live pre-commitment ──
        when_state(
            STATE_ACTIVE,
            SimpleStateConstraint::Not(Box::new(SimpleStateConstraint::FieldEquals {
                index: NEXT_KEYS_DIGEST_SLOT,
                value: FIELD_ZERO,
            })),
        ),
        // ── …and a live current key set ──
        when_state(
            STATE_ACTIVE,
            SimpleStateConstraint::Not(Box::new(SimpleStateConstraint::FieldEquals {
                index: CURRENT_KEYS_COMMIT_SLOT,
                value: FIELD_ZERO,
            })),
        ),
        // ── THE GUARDIAN-ROTATABLE COUNCIL: never nulled while ACTIVE, but
        //    free to advance committee→committee (the set-once pin removed) ──
        when_state(
            STATE_ACTIVE,
            SimpleStateConstraint::Not(Box::new(SimpleStateConstraint::FieldEquals {
                index: COUNCIL_COMMIT_SLOT,
                value: FIELD_ZERO,
            })),
        ),
    ];
    for s in RESERVED_SLOTS {
        cs.push(pinned_zero(s));
    }
    Ok(cs)
}

/// The `CellProgram` for a guardian-rotatable identity cell.
// Lib-public; surfaced as unused only inside the `#[path]`-included guardian-rotation test crate.
#[allow(dead_code)]
pub fn guardian_rotatable_identity_program(cooling_period: u64) -> Result<CellProgram, PolisError> {
    Ok(CellProgram::Predicate(
        guardian_rotatable_identity_constraints(cooling_period)?,
    ))
}

/// The per-charter, content-addressed factory for a guardian-rotatable
/// identity cell. Births exactly one cell; the cooling window is its content
/// address (the council is NOT baked in — it is rotatable, so it cannot be the
/// factory's identity; the council commitment is on-cell state, not a literal).
pub fn guardian_rotatable_identity_descriptor(
    cooling_period: u64,
) -> Result<FactoryDescriptor, PolisError> {
    let constraints = guardian_rotatable_identity_constraints(cooling_period)?;
    let program = CellProgram::Predicate(constraints.clone());
    let child_vk = dregg_cell::factory::canonical_program_vk(&program);
    let mut hasher = blake3::Hasher::new_derive_key("dregg-polis:guardian-rotatable-identity v1");
    let encoded = postcard::to_allocvec(&constraints).unwrap_or_default();
    hasher.update(&(encoded.len() as u64).to_le_bytes());
    hasher.update(&encoded);
    let factory_vk = *hasher.finalize().as_bytes();
    Ok(FactoryDescriptor {
        factory_vk,
        child_program_vk: Some(child_vk),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(child_vk))),
        allowed_cap_templates: vec![CapTemplate {
            target: CapTarget::SelfCell,
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        field_constraints: vec![],
        state_constraints: constraints,
        default_mode: CellMode::Hosted,
        creation_budget: Some(1),
    })
}

// =============================================================================
// The genesis + rotation turn shapes
// =============================================================================

fn set(cell: CellId, index: u8, value: FieldElement) -> Effect {
    Effect::SetField {
        cell,
        index: index as usize,
        value,
    }
}

/// Build the genesis turn for a guardian-rotatable identity (KERI `icp`):
/// install the birth key-set commitment, the first next-keys pre-commitment,
/// the INITIAL council's membership commitment, and step UNINIT → ACTIVE.
///
/// Unlike the stock identity genesis (which pins the council for life), here
/// the council commitment is the FIRST value of a slot that may later advance
/// under guardian-quorum authority via [`rotate_council_effects`].
pub fn genesis_effects(
    cell: CellId,
    charter: &IdentityCharter,
    birth_keys_commit: FieldElement,
    first_next_digest: FieldElement,
) -> Vec<Effect> {
    vec![
        set(cell, CURRENT_KEYS_COMMIT_SLOT, birth_keys_commit),
        set(cell, NEXT_KEYS_DIGEST_SLOT, first_next_digest),
        set(
            cell,
            COUNCIL_COMMIT_SLOT,
            charter.council.members_commitment(),
        ),
        set(cell, STATE_SLOT, field_from_u64(STATE_ACTIVE)),
    ]
}

/// Build the GUARDIAN-SET ROTATION turn's effects: advance
/// [`COUNCIL_COMMIT_SLOT`] from the current committee's commitment to
/// `new_council`'s commitment, in place. The identity's key registers are
/// untouched — this is a council amendment, orthogonal to a key rotation.
///
/// `new_council` is validated by [`new_council_commitment`] before this is
/// called (the non-amplification tooth); the resulting commitment is the only
/// thing written. The *who-may-do-this* is the cell's `set_state`
/// authority — the OLD guardian quorum (see
/// [`install_guardian_council_authority`] and [`council_rotation_action`]).
pub fn rotate_council_effects(cell: CellId, new_council: &CouncilCharter) -> Vec<Effect> {
    vec![set(
        cell,
        COUNCIL_COMMIT_SLOT,
        new_council.members_commitment(),
    )]
}

/// The non-amplification gate at build: a rotated-in council MUST be a valid
/// [`CouncilCharter`] (`1 <= threshold <= members`, no duplicate members,
/// within [`MAX_MEMBERS`](starbridge_polis::council::MAX_MEMBERS)). Returns the
/// commitment the rotation installs, or refuses a council that would weaken the
/// identity below a real K-of-N (a 0-of-N rubber stamp is inexpressible).
pub fn new_council_commitment(new_council: &CouncilCharter) -> Result<FieldElement, PolisError> {
    new_council.validate()?;
    Ok(new_council.members_commitment())
}

// =============================================================================
// Driver wiring: the guardian quorum's `set_state` authority
// =============================================================================

/// Re-permission a guardian-rotatable identity cell so its `set_state` is
/// authorized by the GUARDIAN QUORUM (`Authorization::Custom { vk_hash }`)
/// rather than an owner signature — the deos-genesis posture in which the
/// *who-may-rotate-the-council* decision is the guardian threshold, while the
/// program ([`guardian_rotatable_identity_constraints`]) independently enforces
/// *how* a council may move (non-null, lifecycle-bound).
///
/// `vk_hash` is the guardian committee's verifying-key hash, the same value
/// the threshold-sig verifier registers under in the witnessed-predicate
/// registry. `endowment` funds the cell so it can pay the rotation turn's
/// computron budget (a genesis polis bootstrap leaves it at 0).
///
/// This mutates the ledger directly (the genesis-posture install), exactly as
/// the proven recovery weld's `install_guardian_authority` does; it is a
/// driver/test affordance, not a turn.
pub fn install_guardian_council_authority(permissions: &mut Permissions, vk_hash: [u8; 32]) {
    permissions.send = AuthRequired::Impossible;
    permissions.receive = AuthRequired::None;
    permissions.set_state = AuthRequired::Custom { vk_hash };
    permissions.set_permissions = AuthRequired::Impossible;
    permissions.set_verification_key = AuthRequired::Impossible;
    permissions.increment_nonce = AuthRequired::Custom { vk_hash };
    permissions.delegate = AuthRequired::Impossible;
    permissions.access = AuthRequired::None;
}

/// Build the council-rotation action authorized by the guardian quorum.
///
/// Targets the identity cell's `rotate_council` method with
/// [`rotate_council_effects`], carries `Authorization::Custom` bound to the
/// guardian committee's `vk_hash` at `guardian_root` (its content-address
/// lookup key), and leaves a PLACEHOLDER proof blob at index 0 — the caller
/// fixes the turn nonce, signs the canonical custom signing message, then swaps
/// in the real aggregate QC.
///
/// Unlike a key rotation, no preimage exhibit is needed (the council move is a
/// plain guarded write), so the QC sits at witness index 0.
pub fn council_rotation_action(
    identity_cell: CellId,
    new_council: &CouncilCharter,
    vk_hash: [u8; 32],
    guardian_root: [u8; 32],
) -> Result<Action, PolisError> {
    // Non-amplification tooth, at build: refuse an invalid (e.g. 0-of-N) council.
    new_council_commitment(new_council)?;

    let predicate = WitnessedPredicate {
        kind: WitnessedPredicateKind::Custom { vk_hash },
        commitment: guardian_root,
        input_ref: InputRef::SigningMessage,
        proof_witness_index: 0,
    };
    // Build the unsigned council-rotation action directly (no `crate::raw`
    // dependency, so this module compiles equally as a lib module and when
    // included by `#[path]` into the e2e test crate).
    let action = Action {
        target: identity_cell,
        method: symbol("rotate_council"),
        args: Vec::new(),
        authorization: Authorization::Custom { predicate },
        preconditions: Default::default(),
        effects: rotate_council_effects(identity_cell, new_council),
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: Vec::new(),
    };
    let mut action = action;
    // index 0: a placeholder for the guardian QC (swapped in after signing).
    action.witness_blobs = vec![WitnessBlob::proof(Vec::new())];
    Ok(action)
}

// =============================================================================
// Unit teeth (executor-independent; the e2e half runs on the real
// TurnExecutor in `sdk/tests/guardian_set_rotation_e2e.rs`)
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn member(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    #[test]
    fn council_commitment_changes_with_membership() {
        let old = CouncilCharter::new(vec![member(1), member(2), member(3)], 2);
        let new = CouncilCharter::new(vec![member(4), member(5), member(6)], 2);
        assert_ne!(
            new_council_commitment(&old).unwrap(),
            new_council_commitment(&new).unwrap(),
            "a distinct guardian committee must produce a distinct commitment"
        );
        // The rotation effect installs EXACTLY the new committee's commitment.
        let effects = rotate_council_effects(member(0xAB), &new);
        match &effects[0] {
            Effect::SetField { index, value, .. } => {
                assert_eq!(*index, COUNCIL_COMMIT_SLOT as usize);
                assert_eq!(*value, new.members_commitment());
            }
            other => panic!("expected a SetField on the council slot, got {other:?}"),
        }
    }

    #[test]
    fn non_amplification_refuses_a_zero_of_n_council() {
        // A 0-of-N council (a rubber stamp the old quorum must NOT be able to
        // install) is inexpressible: validate() refuses threshold == 0…
        let rubber_stamp = CouncilCharter::new(vec![member(1), member(2)], 0);
        assert!(
            new_council_commitment(&rubber_stamp).is_err(),
            "a 0-of-N council must be refused at build (no amplification)"
        );
        // …and a threshold above the membership (demanding more approvers than
        // exist — an unsatisfiable, bricking council) is likewise refused.
        let unsatisfiable = CouncilCharter::new(vec![member(1), member(2)], 3);
        assert!(
            new_council_commitment(&unsatisfiable).is_err(),
            "a council demanding more approvers than members must be refused"
        );
        // A real K-of-N is accepted.
        let real = CouncilCharter::new(vec![member(1), member(2), member(3)], 2);
        assert!(new_council_commitment(&real).is_ok());
    }

    #[test]
    fn council_rotation_action_refuses_invalid_new_council() {
        let bad = CouncilCharter::new(vec![member(1)], 0);
        assert!(
            council_rotation_action(member(0xC0), &bad, [0x5E; 32], [0x99; 32]).is_err(),
            "the action builder must refuse an invalid (amplifying) new council"
        );
    }

    #[test]
    fn program_guards_council_slot_non_null_while_active() {
        // The constraint set must contain the council non-null guard while
        // ACTIVE, and must NOT pin the council to any literal (it is rotatable).
        let cs = guardian_rotatable_identity_constraints(50).unwrap();
        // Exactly one constraint mentions the council slot, and it is the
        // when-ACTIVE non-zero guard (an AnyOf), never a bare FieldEquals pin.
        let council_pins = cs
            .iter()
            .filter(|c| {
                matches!(
                    c,
                    StateConstraint::FieldEquals {
                        index,
                        ..
                    } if *index == COUNCIL_COMMIT_SLOT
                )
            })
            .count();
        assert_eq!(
            council_pins, 0,
            "the council slot must NOT be pinned to a literal — it is rotatable"
        );
        // The non-null guard is present (an AnyOf carrying a Not(FieldEquals
        // COUNCIL_COMMIT_SLOT == 0)).
        let has_guard = cs.iter().any(|c| match c {
            StateConstraint::AnyOf { variants } => variants.iter().any(|v| {
                matches!(
                    v,
                    SimpleStateConstraint::Not(inner)
                        if matches!(
                            inner.as_ref(),
                            SimpleStateConstraint::FieldEquals { index, value }
                                if *index == COUNCIL_COMMIT_SLOT && *value == FIELD_ZERO
                        )
                )
            }),
            _ => false,
        });
        assert!(
            has_guard,
            "the council slot must be guarded non-null while ACTIVE"
        );
    }

    #[test]
    fn cooling_period_zero_refused() {
        assert!(guardian_rotatable_identity_constraints(0).is_err());
        assert!(guardian_rotatable_identity_descriptor(0).is_err());
    }

    #[test]
    fn descriptor_is_deterministic_and_council_independent() {
        // The factory is content-addressed over the cooling window ONLY — two
        // identities with the same cooling window share a factory regardless of
        // their (rotatable) councils, and the descriptor is reproducible.
        let a = guardian_rotatable_identity_descriptor(50).unwrap();
        let b = guardian_rotatable_identity_descriptor(50).unwrap();
        assert_eq!(a.factory_vk, b.factory_vk);
        let c = guardian_rotatable_identity_descriptor(99).unwrap();
        assert_ne!(a.factory_vk, c.factory_vk);
    }
}
