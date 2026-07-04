//! **THE SDK CARRIER-WITNESS ATTACH SITES (v12 big-bang parallel lane).**
//!
//! The four v12 carrier fold arms (`dregg_circuit_prove::ivc_turn_chain::prove_chain_core_rotated`
//! — factory / hatchery / sovereign / membership) consume a
//! [`CarrierWitness`](dregg_circuit_prove::joint_turn_aggregation::CarrierWitness) attached to the
//! turn's [`RotatedParticipantLeg`], exactly as the deployed custom arm consumes
//! `CarrierWitness::Custom`. The CUSTOM wire's retention shape (the mirror this module follows):
//!
//! * the turn-build path RETAINS the prover-side re-provable material OUTSIDE the on-wire `Turn`
//!   (`custom_proof_bind::BoundCustomProof` keeps `witness_values`/`num_rows` only when built
//!   locally — a wire-rehydrated proof carries `None` there);
//! * the leg-mint site projects the retained material into the carrier bundle via the FAIL-CLOSED
//!   projection (`CustomWitnessBundle::from_bound_custom_proof` → `None` off-wire) and attaches it
//!   with [`RotatedParticipantLeg::with_carrier_witness`];
//! * a leg with NO witness (`carrier_witness: None`) takes the RE-EXEC RUNG — the chain still
//!   proves, the carrier claim is checked by a re-executing validator, NEVER fabricated.
//!
//! This module is the SDK twin of that wire for the four v12 carriers: the per-carrier RETENTION
//! projections (turn-build-time, from the data the cipherclerk validated) + the leg ATTACH that
//! routes through the fold lane's `from_retained_*` production projections
//! (`FactoryWitnessBundle::from_retained_backing`, `HatcheryWitnessBundle::from_retained_attestation`,
//! `SovereignWitnessBundle::from_retained_authority`, `MembershipWitnessBundle::from_retained_membership`
//! — all fail-closed `None` off-wire).
//!
//! ⚑ FAIL-CLOSED LAW: absent material → `None` → the leg keeps `carrier_witness: None` (the
//! re-exec rung). No default/zeroed bundle is EVER minted — a zeroed tuple would be a fabricated
//! backing the executor never validated, and the fold's in-circuit `connect` would bind a lie.

use dregg_cell::program::AuthorizedSet;
use dregg_cell::{Cell, CellMode, CellProgram, FactoryCreationParams, StateConstraint};
use dregg_circuit::effect_vm::bytes32_to_8_limbs;
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::factory_leaf_adapter::FactoryBackingWitness;
use dregg_circuit_prove::hatchery_leaf_adapter::HatcheryAttestationWitness;
use dregg_circuit_prove::joint_turn_aggregation::{
    CarrierWitness, DslWitnessBundle, FactoryWitnessBundle, HatcheryWitnessBundle,
    MembershipWitnessBundle, RotatedParticipantLeg, SovereignWitnessBundle,
};
use dregg_circuit_prove::membership_leaf_adapter::SenderMembershipWitness;
use dregg_circuit_prove::sovereign_leaf_adapter::{KEY_COMMIT_LEN, SovereignAuthorityWitness};

use crate::error::SdkError;
use crate::hatchery_mint::MintedKind;

// ─────────────────────────────────────────────────────────────────────────
// The retained material — what the turn-build holds that the wire does not.
// ─────────────────────────────────────────────────────────────────────────

/// The sovereign carrier's TURN-BUILD retention: the parts of the authority tuple the
/// cipherclerk validates at build (`key_commit` from the cell's `public_key`, the signed replay
/// `sequence`). The 8-felt `anchor`/`new_commit` halves are NOT retained here — they are read off
/// the minted WIDE leg's own published anchors at attach time
/// ([`RotatedParticipantLeg::wide_old_root8`] / [`wide_new_root8`](RotatedParticipantLeg::wide_new_root8)),
/// so the leaf's tuple is anchored to the leg it binds, never to a stale copy.
#[derive(Clone, Copy, Debug)]
pub struct RetainedSovereignAuthority {
    /// `canonical_32_to_felts_4(owner_pubkey)` — the deployed `SOVEREIGN_WITNESS_KEY_COMMIT[4]`
    /// teeth value ([`dregg_turn::executor::TurnExecutor::pubkey_to_witness_key_commit`]).
    pub key_commit: [BabyBear; KEY_COMMIT_LEN],
    /// The per-cell monotonic sequence the owner signed (the replay counter the off-AIR
    /// `execute.rs` sovereign-witness loop verifies).
    pub sequence: u64,
}

/// Per-turn retained carrier material — the SDK-side record the turn-build fills for the (at most
/// one) carrier lane the turn exercises. `Default` = nothing retained = the re-exec rung.
///
/// The record deliberately carries all four lanes as independent `Option`s (a turn-build site
/// retains what it VALIDATED); [`Self::attach_to_leg`] refuses an ambiguous record (>1 lane
/// `Some`) LOUDLY rather than silently picking — the caller selects the lane its leg publishes.
#[derive(Clone, Debug, Default)]
pub struct RetainedCarrierMaterial {
    /// Factory creation-backing (`CreateCellFromFactory` lead): the validated
    /// `(factory_vk, child_vk, derivation_digest)` tuple.
    pub factory: Option<FactoryBackingWitness>,
    /// Hatchery contract-attestation (a hatchery-mint lead): the `HpresProof::Attested`
    /// `(contract_hash, invariant_digest)` tuple.
    pub hatchery: Option<HatcheryAttestationWitness>,
    /// Sovereign authority (the owner-signed sovereign-witness turn).
    pub sovereign: Option<RetainedSovereignAuthority>,
    /// Sender-membership (`SenderAuthorized { PublicRoot }`-caveated turn): the
    /// `(sender_leaf, authorized_root)` tuple the caveat check verified.
    pub membership: Option<SenderMembershipWitness>,
    /// DSL/Dfa route (a `Witnessed{Dfa}`-caveated turn): the re-provable predicate-transition
    /// bundle the turn-build proved locally ([`retain_dfa_route`] — the `DfaProofWire` on the
    /// wire carries only `(public_inputs, stark)`, never the trace witness, so a rehydrated
    /// turn cannot fill this lane).
    pub dsl: Option<DslWitnessBundle>,
}

impl RetainedCarrierMaterial {
    /// `true` iff nothing was retained — the turn takes the re-exec rung.
    pub fn is_empty(&self) -> bool {
        self.factory.is_none()
            && self.hatchery.is_none()
            && self.sovereign.is_none()
            && self.membership.is_none()
            && self.dsl.is_none()
    }

    /// **THE ATTACH SITE** — the four-carrier mirror of the custom wire's
    /// `mint_custom_wide_rotated_participant_leg` bundle attach. Projects the retained material
    /// through the fold lane's `from_retained_*` production projections and attaches the (single)
    /// resulting [`CarrierWitness`] to `leg` via
    /// [`RotatedParticipantLeg::with_carrier_witness`].
    ///
    /// * Nothing retained → the leg is returned UNCHANGED (`carrier_witness` stays `None`): the
    ///   sanctioned re-exec rung, identical to today's non-carrier turns.
    /// * More than one lane retained → `Err` (LOUD): a leg publishes ONE carrier's claim slots;
    ///   silently picking would attach a witness the leg's pins may not back. The caller narrows
    ///   the record to the lane its leg publishes.
    /// * Sovereign retained but the leg is not WIDE (no 8-felt anchors) → `Err` (fail-closed):
    ///   the authority tuple's `anchor`/`new_commit` MUST be the leg's own published anchors —
    ///   fabricating them would bind a tuple no deployed leg carries.
    pub fn attach_to_leg(
        &self,
        leg: RotatedParticipantLeg,
    ) -> Result<RotatedParticipantLeg, SdkError> {
        let mut witness: Option<CarrierWitness> = None;
        let set = |w: CarrierWitness, slot: &mut Option<CarrierWitness>| {
            if let Some(prev) = slot {
                return Err(SdkError::InvalidWitness(format!(
                    "carrier-witness attach: ambiguous retained material ({} AND {} both \
                     retained) — a leg publishes ONE carrier's claim slots; narrow the \
                     retention to the lane this leg publishes",
                    prev.carrier_name(),
                    w.carrier_name(),
                )));
            }
            *slot = Some(w);
            Ok(())
        };

        if let Some(b) = FactoryWitnessBundle::from_retained_backing(self.factory.as_ref()) {
            set(CarrierWitness::Factory(b), &mut witness)?;
        }
        if let Some(b) = HatcheryWitnessBundle::from_retained_attestation(self.hatchery.as_ref()) {
            set(CarrierWitness::Hatchery(b), &mut witness)?;
        }
        if let Some(sov) = self.sovereign.as_ref() {
            // The anchors come off the leg being attached to (fail-closed if the leg is not the
            // wide 8-felt-anchored form — a narrow leg has no faithful anchors to bind).
            let anchor = leg.wide_old_root8().ok_or_else(|| {
                SdkError::InvalidWitness(
                    "carrier-witness attach: sovereign authority retained but the leg carries \
                     no wide 8-felt BEFORE anchor (non-wide leg) — fail-closed, not fabricated"
                        .into(),
                )
            })?;
            let new_commit = leg.wide_new_root8().ok_or_else(|| {
                SdkError::InvalidWitness(
                    "carrier-witness attach: sovereign authority retained but the leg carries \
                     no wide 8-felt AFTER anchor (non-wide leg) — fail-closed, not fabricated"
                        .into(),
                )
            })?;
            let sequence = u32::try_from(sov.sequence).map_err(|_| {
                SdkError::InvalidWitness(format!(
                    "carrier-witness attach: sovereign sequence {} exceeds the felt-carried \
                     u32 range — fail-closed, not truncated",
                    sov.sequence
                ))
            })?;
            let authority = SovereignAuthorityWitness {
                key_commit: sov.key_commit,
                sequence: BabyBear::new(sequence),
                anchor,
                new_commit,
            };
            let b = SovereignWitnessBundle::from_retained_authority(Some(&authority))
                .expect("Some retained authority projects to Some bundle");
            set(CarrierWitness::Sovereign(b), &mut witness)?;
        }
        if let Some(b) = MembershipWitnessBundle::from_retained_membership(self.membership.as_ref())
        {
            set(CarrierWitness::Membership(b), &mut witness)?;
        }
        if let Some(b) = DslWitnessBundle::from_retained_dsl(self.dsl.as_ref()) {
            set(CarrierWitness::Dsl(b), &mut witness)?;
        }

        Ok(match witness {
            Some(w) => leg.with_carrier_witness(w),
            // Nothing retained: the re-exec rung — the leg is untouched, carrier_witness stays
            // as minted (None on every deployed mint recipe).
            None => leg,
        })
    }
}

// ─────────────────────────────────────────────────────────────────────────
// The per-carrier RETENTION projections (turn-build-time).
// ─────────────────────────────────────────────────────────────────────────

/// Retain the FACTORY creation-backing witness from a `CreateCellFromFactory` effect's validated
/// creation data — the SDK twin of the STEP-2.5 carrier-material capture
/// (`cipherclerk::prove_sovereign_turn_rotated`'s `after_material`, which threads
/// `params.program_vk` onto the committed AFTER `child_vk8` octet).
///
/// * `child_vk` = `bytes32_to_8_limbs(params.program_vk)` — the SAME canonical limb mapping the
///   commitment octet carries (`cell/src/commitment.rs`), so the retained tuple's `child_vk`
///   equals the leg's committed claim by construction (the fold's `connect` requires it).
/// * `derivation_digest` = `bytes32_to_8_limbs(ChildVkStrategy::compute_param_hash(params))` —
///   the canonical validated-params commitment (the SAME `param_hash` the executor's
///   `derive_child_vk` consumes and `Provenance::derivation_param_hash` records). The adapter
///   binds the tuple internally (`factory_leaf_adapter` — full in-AIR re-derivation is that
///   module's NAMED seam); this slot carries the executor-shared params commitment, never an
///   invented value.
///
/// **Fail-closed `None`:** `params.program_vk == None` — the DERIVED-VK strategy resolves the
/// effective child VK executor-side (`apply_create_cell_from_factory`'s `effective_vk` from the
/// descriptor's `base_vk`), which the ledgerless SDK cannot recompute. Such a turn takes the
/// re-exec rung unless the caller supplies the resolved VK (the same caller-supplies note as
/// STEP-2.5).
pub fn retain_factory_backing(
    factory_vk: &[u8; 32],
    params: &FactoryCreationParams,
) -> Option<FactoryBackingWitness> {
    let program_vk = params.program_vk?;
    let param_hash = dregg_cell::ChildVkStrategy::compute_param_hash(params);
    Some(FactoryBackingWitness {
        factory_vk: bytes32_to_8_limbs(factory_vk),
        child_vk: bytes32_to_8_limbs(&program_vk),
        derivation_digest: bytes32_to_8_limbs(&param_hash),
    })
}

/// Retain the HATCHERY contract-attestation witness from a minted kind — the SDK twin of
/// [`MintedKind::carrier_material`] (which threads the `Attested` content hash onto the committed
/// AFTER `contract_hash8` octet).
///
/// * `contract_hash` = `bytes32_to_8_limbs(attested content hash)` — the SAME canonical limb
///   mapping the commitment octet carries, so the retained tuple equals the leg's committed claim.
/// * `invariant_digest` = `bytes32_to_8_limbs(kind.child_vk())` — the invariant carrier the
///   contract certifies (the child program VK that bakes the kind's constraints; the same VK the
///   factory half of a hatchery mint publishes on ITS leg — "the invariant half rides factory's
///   leg").
///
/// **Fail-closed `None`:** `HpresProof::Pending` — an unattested kind has NO contract to bind;
/// the mint takes the re-exec rung (and its committed `contract_hash8` octet is zero, so a
/// fabricated bundle could not fold anyway).
pub fn retain_hatchery_attestation(kind: &MintedKind) -> Option<HatcheryAttestationWitness> {
    let contract_hash = kind.hpres.contract_hash()?;
    Some(HatcheryAttestationWitness {
        contract_hash: bytes32_to_8_limbs(&contract_hash),
        invariant_digest: bytes32_to_8_limbs(&kind.child_vk()),
    })
}

/// Retain the SOVEREIGN authority material from an owner-signed sovereign-witness turn-build —
/// the `(key_commit, sequence)` half of the authority tuple
/// (`sovereign_leaf_adapter::SovereignAuthorityWitness`); the 8-felt anchors are read off the
/// minted leg at attach ([`RetainedCarrierMaterial::attach_to_leg`]).
///
/// `key_commit` is [`dregg_turn::executor::TurnExecutor::pubkey_to_witness_key_commit`] over the
/// cell's `public_key` — the SAME 4-felt compress the deployed `SOVEREIGN_WITNESS_KEY_COMMIT`
/// teeth carry, so the retained claim equals the leg's published teeth for an honest turn.
///
/// **Fail-closed `None`:** the cell is not `CellMode::Sovereign` — a hosted cell's turn carries
/// no sovereign-witness authority to bind.
pub fn retain_sovereign_authority(
    cell: &Cell,
    sequence: u64,
) -> Option<RetainedSovereignAuthority> {
    if cell.mode != CellMode::Sovereign {
        return None;
    }
    Some(RetainedSovereignAuthority {
        key_commit: dregg_turn::executor::TurnExecutor::pubkey_to_witness_key_commit(
            cell.public_key(),
        ),
        sequence,
    })
}

/// Retain the SENDER-MEMBERSHIP witness for a turn against a cell whose program declares
/// `SenderAuthorized { AuthorizedSet::PublicRoot { set_root_index } }` — the SAME
/// `(sender_leaf, authorized_root)` pair the executor's `MerkleMembershipStarkVerifier` pins:
///
/// * `sender_leaf` = [`dregg_commit::typed::compress_member`]`(sender_pk)` — the canonical
///   chip-native membership compress (the in-AIR keystone's leaf domain).
/// * `authorized_root` = the root felt read from the cell's `fields[set_root_index]` slot in the
///   verifier's canonical form (the felt's 4-byte little-endian low bytes —
///   `membership_verifier::root_felt_from_slot`;
///   [`dregg_turn::executor::membership_verifier::authorized_set_root_bytes`] emits the matching
///   slot encoding).
///
/// **Fail-closed `None`:** the cell's program declares no `SenderAuthorized { PublicRoot }`
/// constraint (nothing to bind — `BlindedSet`/`CredentialSet` ride their own witnessed-predicate
/// verifiers, not this carrier), or the declared slot index is out of range.
pub fn retain_sender_membership(
    sender_pk: &[u8; 32],
    cell: &Cell,
) -> Option<SenderMembershipWitness> {
    let set_root_index = public_root_slot_index(&cell.program)?;
    let slot = cell.state.fields.get(set_root_index as usize)?;
    // The verifier's `root_felt_from_slot`: the root is ALREADY a felt, published in the slot as
    // its canonical 4-byte little-endian form (low 4 bytes; the rest zero) — read, don't compress.
    let authorized_root = BabyBear::new(u32::from_le_bytes([slot[0], slot[1], slot[2], slot[3]]));
    Some(SenderMembershipWitness {
        sender_leaf: dregg_commit::typed::compress_member(sender_pk),
        authorized_root,
    })
}

/// Retain the DSL/Dfa ROUTE witness for a `Witnessed{Dfa}`-caveated turn — the dsl mirror of
/// how custom retains its proof wire (`BoundCustomProof` keeps `witness_values`/`num_rows`
/// only when built locally). The retention site is the turn-build that PROVES the
/// `DfaProofWire` (`dregg_turn::executor::membership_verifier::prove_dfa_transition` consumes
/// exactly these arguments), which is the only place the trace witness exists: the wire
/// itself carries only `(public_inputs, stark)` bytes, so a wire-rehydrated turn has nothing
/// to retain here (the re-exec rung — the off-AIR `DslCircuitDfaVerifier` still verifies it).
///
/// * `program` is resolved from the HOST-TRUSTED `ProgramRegistry` by the caveat's
///   `vk_hash` commitment — the SAME fail-closed lookup the off-AIR verifier performs, so a
///   self-declared circuit is never retained (**fail-closed `None`** when unregistered).
/// * `wire_public_inputs` are the `DfaProofWire.public_inputs`; the fold's binding requires
///   `custom_proof_pi_commitment(wire_public_inputs)` == the leg's published rc, which holds
///   by construction when the SAME inputs fed `dfa_route_commitment` into the leg's caveat
///   manifest (`RotatedCaveatManifest::dfa_rc`).
///
/// The fold arm additionally refuses the ZERO rc sentinel, so retaining this lane for a
/// turn that carries no Dfa caveat cannot fold a vacuous claim — it is refused loudly.
pub fn retain_dfa_route(
    programs: &dregg_circuit::dsl::circuit::ProgramRegistry,
    vk_hash: &[u8; 32],
    witness_values: &std::collections::HashMap<String, Vec<BabyBear>>,
    num_rows: usize,
    wire_public_inputs: &[BabyBear],
) -> Option<DslWitnessBundle> {
    let program = programs.get(vk_hash)?;
    Some(DslWitnessBundle {
        program: program.clone(),
        witness_values: witness_values.clone(),
        num_rows,
        public_inputs: wire_public_inputs.to_vec(),
    })
}

/// The `SenderAuthorized { PublicRoot { set_root_index } }` slot index declared by `program`,
/// scanning both the flat predicate form and every transition case. `None` when no such
/// constraint is declared.
fn public_root_slot_index(program: &CellProgram) -> Option<u8> {
    let scan = |cs: &[StateConstraint]| {
        cs.iter().find_map(|c| match c {
            StateConstraint::SenderAuthorized {
                set: AuthorizedSet::PublicRoot { set_root_index },
            } => Some(*set_root_index),
            _ => None,
        })
    };
    match program {
        CellProgram::Predicate(cs) => scan(cs),
        CellProgram::Cases(cases) => cases.iter().find_map(|case| scan(&case.constraints)),
        _ => None,
    }
}
