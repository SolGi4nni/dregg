//! Verifier-minted acceptance authority for live exact FNSP-v3 note-spend admission.
//!
//! This module joins three independently owned facts without changing executor dispatch:
//!
//! 1. the signed [`Effect::NoteSpend`] supplies the historical root, nullifier, value, asset, and
//!    strict v3 carrier;
//! 2. a validated exact AAFI transition plus a durable actor anchor supply every accumulator and
//!    outer-state lane; and
//! 3. the code-owned exact-v3 verifier receives only the carrier's inner proof bytes and the
//!    resulting canonical 76-lane statement.
//!
//! The public entry point has no predicate, action, resource, descriptor, VK, or verifier argument.
//! The executor never re-verifies or accepts a raw v3 statement: node orchestration installs the
//! opaque token returned here into its one-shot exact-v3 admission slot, and strict dispatch joins
//! every authenticated effect coordinate to that exact token before applying the spend.

use core::fmt;
use std::error::Error;
use std::sync::{Arc, OnceLock};

use crate::ProofVerifier;
use crate::action::Effect;
use crate::faithful_note_spend_exact_v3::{
    FAITHFUL_NOTE_SPEND_EXACT_V3_ACTION, FAITHFUL_NOTE_SPEND_EXACT_V3_PREDICATE,
    FAITHFUL_NOTE_SPEND_EXACT_V3_PUBLIC_INPUT_COUNT, FAITHFUL_NOTE_SPEND_EXACT_V3_RESOURCE,
    FaithfulNoteSpendExactV3Error, FaithfulNoteSpendExactV3ProofCarrier,
    FaithfulNoteSpendExactV3PublicStatement, FaithfulNoteSpendExactV3StateInputs,
};
use crate::faithful_note_spend_exact_v3_anchor::ExactFnspV3DurableAnchor;
use dregg_circuit::exact_nullifier_aafi::{ValidatedExactAafiTransition, exact_state_commit};

/// The ONE process-wide exact-v3 proof authority.
///
/// The concrete verifier (`FaithfulNoteSpendExactV3Verifier`) checks a HidingFRI
/// proof against a `dregg-circuit-prove` descriptor, so it lives in
/// `dregg-turn-prover`, not here. This slot is how the core reaches it.
///
/// `OnceLock` is load-bearing, not convenience: the authority is **install-once,
/// never replaceable**, so the public mint below still takes NO verifier argument
/// and no caller can swap a permissive verifier in for a single call. Absent an
/// installed authority the mint FAILS CLOSED
/// ([`FaithfulNoteSpendExactV3AcceptanceError::ProofAuthorityNotInstalled`]) —
/// exactly the posture the deleted `#[cfg(not(feature = "prover"))]` build had,
/// now a runtime fact instead of a cfg fact.
static EXACT_V3_PROOF_AUTHORITY: OnceLock<Arc<dyn ProofVerifier>> = OnceLock::new();

/// Install the code-owned exact FNSP-v3 proof authority for this process.
///
/// Call this once at startup; `dregg_turn_prover::install_code_owned_exact_fnsp_v3_verifier`
/// is the production caller and installs the real
/// `FaithfulNoteSpendExactV3Verifier`. Returns `Err` if an authority is already
/// installed — installation is irreversible on purpose, so a later crate cannot
/// downgrade proof authority after the node has begun accepting turns.
pub fn install_exact_fnsp_v3_proof_authority(
    verifier: Arc<dyn ProofVerifier>,
) -> Result<(), ExactFnspV3ProofAuthorityAlreadyInstalled> {
    EXACT_V3_PROOF_AUTHORITY
        .set(verifier)
        .map_err(|_| ExactFnspV3ProofAuthorityAlreadyInstalled)
}

/// Whether an exact-v3 proof authority has been installed in this process.
pub fn exact_fnsp_v3_proof_authority_installed() -> bool {
    EXACT_V3_PROOF_AUTHORITY.get().is_some()
}

/// Refusal of a second [`install_exact_fnsp_v3_proof_authority`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExactFnspV3ProofAuthorityAlreadyInstalled;

impl fmt::Display for ExactFnspV3ProofAuthorityAlreadyInstalled {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("an exact FNSP-v3 proof authority is already installed")
    }
}

impl Error for ExactFnspV3ProofAuthorityAlreadyInstalled {}

const PI_HEIGHT: usize = 0;
const PI_HISTORICAL_ROOT: usize = 4;
const PI_NULLIFIER: usize = 12;
const PI_VALUE: usize = 28;
const PI_ASSET_TYPE: usize = 32;
const PI_SUCCESSOR_ROOT: usize = 36;
const PI_PRIOR_ROOT: usize = 44;
const PI_PRE_COUNT: usize = 52;
const PI_POST_COUNT: usize = 56;
const PI_BEFORE_COMMIT: usize = 60;
const PI_AFTER_COMMIT: usize = 68;
const PI_END: usize = 76;
const ACCEPTED_SIGNED_PROOF_DIGEST_DOMAIN: &[u8] =
    b"DREGG/FNSP-V3/ACCEPTED-SIGNED-SPENDING-PROOF/V1";

/// Opaque evidence that the code-owned exact FNSP-v3 verifier accepted one canonical statement.
///
/// Fields and construction are private.  The token contains no proof bytes and cannot be minted by
/// a caller from an arbitrary statement.  The live executor admission and persisted
/// compare-and-swap consume this token linearly and inspect [`Self::binding`] before advancing
/// durable exact state.
#[derive(Debug, PartialEq, Eq)]
pub struct AcceptedFaithfulNoteSpendExactV3 {
    public: FaithfulNoteSpendExactV3PublicStatement,
    prior_fns3: [u32; 8],
    successor_fns3: [u32; 8],
    value_commitment: Option<[u8; 32]>,
    signed_spending_proof_digest: [u8; 32],
}

impl AcceptedFaithfulNoteSpendExactV3 {
    /// Read-only, typed view of the exact statement which passed proof verification.
    pub fn binding(&self) -> FaithfulNoteSpendExactV3AcceptanceBinding<'_> {
        FaithfulNoteSpendExactV3AcceptanceBinding {
            public: &self.public,
            prior_fns3: &self.prior_fns3,
            successor_fns3: &self.successor_fns3,
            value_commitment: self.value_commitment,
        }
    }

    /// Canonical 76 BabyBear public lanes passed to the strict verifier.
    pub fn public_input_lanes(&self) -> &[u32; FAITHFUL_NOTE_SPEND_EXACT_V3_PUBLIC_INPUT_COUNT] {
        self.public.as_u32_array()
    }

    /// Domain-separated BLAKE3 digest of the exact full carrier bytes embedded in the signed
    /// `Effect::NoteSpend` which produced this accepted token.
    ///
    /// This binds bytes not represented in the 76 public lanes, while retaining no proof bytes in
    /// the token itself.
    pub fn signed_spending_proof_digest(&self) -> [u8; 32] {
        self.signed_spending_proof_digest
    }

    /// Fail-closed equality check for the node candidate's embedded signed proof carrier.
    ///
    /// Coordinate equality is not enough: two carriers with the same root height produce the same
    /// public lanes even when their inner proof bytes differ.  The node must require this method to
    /// return `true` for the authenticated `Effect` immediately before finalization.
    pub fn matches_signed_effect(&self, signed_effect: &Effect) -> bool {
        let Effect::NoteSpend { spending_proof, .. } = signed_effect else {
            return false;
        };
        self.matches_signed_spending_proof(spending_proof)
    }

    /// Crate-internal zero-copy join used by the executor after it has already destructured the
    /// authenticated effect.  External callers retain the safer whole-effect matcher above.
    pub(crate) fn matches_signed_spending_proof(&self, spending_proof: &[u8]) -> bool {
        self.signed_spending_proof_digest == signed_spending_proof_digest(spending_proof)
    }
}

/// Borrowed typed view of an accepted statement's durable-CAS binding.
///
/// This is deliberately not constructible outside this module.  Every accessor decodes the
/// canonical lanes retained in the accepted token; the view cannot drift from what the proof
/// verifier checked.  FNS3 is retained separately because it is the exact `(root8, count64)` state
/// commitment embedded in the durable rotated frame, not an additional public lane.
#[derive(Clone, Copy, Debug)]
pub struct FaithfulNoteSpendExactV3AcceptanceBinding<'a> {
    public: &'a FaithfulNoteSpendExactV3PublicStatement,
    prior_fns3: &'a [u32; 8],
    successor_fns3: &'a [u32; 8],
    value_commitment: Option<[u8; 32]>,
}

impl FaithfulNoteSpendExactV3AcceptanceBinding<'_> {
    fn lanes(&self) -> &[u32; PI_END] {
        self.public.as_u32_array()
    }

    pub fn historical_root_height(&self) -> u64 {
        read_u64_u16(&self.lanes()[PI_HEIGHT..PI_HISTORICAL_ROOT])
    }

    pub fn historical_note_root(&self) -> [u8; 32] {
        read_root8_bytes(&self.lanes()[PI_HISTORICAL_ROOT..PI_NULLIFIER])
    }

    pub fn nullifier(&self) -> [u8; 32] {
        read_bytes32_u16(&self.lanes()[PI_NULLIFIER..PI_VALUE])
    }

    pub fn value(&self) -> u64 {
        read_u64_u16(&self.lanes()[PI_VALUE..PI_ASSET_TYPE])
    }

    pub fn asset_type(&self) -> u64 {
        read_u64_u16(&self.lanes()[PI_ASSET_TYPE..PI_SUCCESSOR_ROOT])
    }

    /// The optional value commitment carried by the authenticated effect accepted by the
    /// verifier seam.  It is not an exact-AIR public lane today, so retaining it here is the
    /// executor-side equality tooth which prevents a same-proof effect-coordinate splice.
    pub fn value_commitment(&self) -> Option<[u8; 32]> {
        self.value_commitment
    }

    pub fn successor_root(&self) -> [u32; 8] {
        self.lanes()[PI_SUCCESSOR_ROOT..PI_PRIOR_ROOT]
            .try_into()
            .expect("fixed exact FNSP-v3 successor root")
    }

    pub fn prior_root(&self) -> [u32; 8] {
        self.lanes()[PI_PRIOR_ROOT..PI_PRE_COUNT]
            .try_into()
            .expect("fixed exact FNSP-v3 prior root")
    }

    pub fn prior_count(&self) -> u64 {
        read_u64_u16(&self.lanes()[PI_PRE_COUNT..PI_POST_COUNT])
    }

    pub fn successor_count(&self) -> u64 {
        read_u64_u16(&self.lanes()[PI_POST_COUNT..PI_BEFORE_COMMIT])
    }

    pub fn prior_fns3(&self) -> [u32; 8] {
        *self.prior_fns3
    }

    pub fn successor_fns3(&self) -> [u32; 8] {
        *self.successor_fns3
    }

    pub fn before_outer_commit(&self) -> [u32; 8] {
        self.lanes()[PI_BEFORE_COMMIT..PI_AFTER_COMMIT]
            .try_into()
            .expect("fixed exact FNSP-v3 BEFORE commitment")
    }

    pub fn after_outer_commit(&self) -> [u32; 8] {
        self.lanes()[PI_AFTER_COMMIT..PI_END]
            .try_into()
            .expect("fixed exact FNSP-v3 AFTER commitment")
    }
}

/// Verify one exact FNSP-v3 note spend against independently validated transition and durable
/// state.
///
/// `signed_effect` must be the effect recovered from the already-authenticated turn envelope.  The
/// executor cutover will call this only after turn signature/authentication checks; this seam does
/// not accept an unsigned proof-controlled statement as a substitute.
///
/// This function itself is mutation-free: it does not mutate the exact accumulator or install a
/// caller-selected verifier.  The verifier is the ONE install-once process authority
/// ([`install_exact_fnsp_v3_proof_authority`]); with none installed this fails closed with
/// [`FaithfulNoteSpendExactV3AcceptanceError::ProofAuthorityNotInstalled`].  Live exact-v3
/// dispatch accepts only this opaque result; the v2 route remains independent.
///
/// # Fail-closed live-orchestration preconditions
///
/// The node caller must additionally establish facts which are deliberately outside this
/// narrow proof seam:
///
/// - `signed_effect` came from the authenticated `SignedTurn` being finalized;
/// - the binding's `(historical_root_height, historical_note_root)` names an accepted durable
///   history entry;
/// - `durable_anchor` was rebuilt from the finalized turn agent's actual `Cell` and current durable
///   rotation context, not merely from an arbitrary same-shaped actor; and
/// - under the persistence lock, the current exact root/count/FNS3 and outer BEFORE commitment
///   equal the accepted binding before atomically committing its successor/AFTER values.
///
/// Until those comparisons and the CAS are wired, possession of the returned token is not by
/// itself authorization to mutate durable state.
pub fn verify_faithful_note_spend_exact_v3_acceptance(
    signed_effect: &Effect,
    transition: &ValidatedExactAafiTransition,
    durable_anchor: &ExactFnspV3DurableAnchor,
) -> Result<AcceptedFaithfulNoteSpendExactV3, FaithfulNoteSpendExactV3AcceptanceError> {
    let Some(authority) = EXACT_V3_PROOF_AUTHORITY.get() else {
        return Err(FaithfulNoteSpendExactV3AcceptanceError::ProofAuthorityNotInstalled);
    };
    verify_with_code_owned_identity(
        authority.as_ref(),
        signed_effect,
        transition,
        durable_anchor,
    )
}

/// Private verifier-injection seam used to prove ordering and exact argument transport in hostile
/// tests.  Production callers can reach only the public function above, which fixes the concrete
/// exact-v3 verifier and every identity string in code.
fn verify_with_code_owned_identity(
    verifier: &dyn ProofVerifier,
    signed_effect: &Effect,
    transition: &ValidatedExactAafiTransition,
    durable_anchor: &ExactFnspV3DurableAnchor,
) -> Result<AcceptedFaithfulNoteSpendExactV3, FaithfulNoteSpendExactV3AcceptanceError> {
    let Effect::NoteSpend {
        nullifier,
        value,
        spending_proof,
        value_commitment,
        ..
    } = signed_effect
    else {
        return Err(FaithfulNoteSpendExactV3Error::NotNoteSpend.into());
    };

    // Join the signed turn fields to the independently validated host transition before parsing or
    // verifying the proof.  Asset type has no field in the exact accumulator transition and stays
    // proof-bound in the 76-lane statement.
    if nullifier.0 != transition.inserted_raw() {
        return Err(FaithfulNoteSpendExactV3AcceptanceError::SignedNullifierMismatch);
    }
    if *value != transition.inserted_value() {
        return Err(
            FaithfulNoteSpendExactV3AcceptanceError::SignedValueMismatch {
                signed: *value,
                transition: transition.inserted_value(),
            },
        );
    }

    // Decode before statement construction so the proof submitted to the verifier is exactly the
    // canonical carrier's inner payload.  Generic/v2/malformed carriers never reach verification.
    let carrier = FaithfulNoteSpendExactV3ProofCarrier::decode(spending_proof)?;

    // This must precede verifier invocation.  It checks both prior and successor FNS3 octets at
    // every scattered durable-state offset, preventing mixed transition/anchor statements.
    let state = FaithfulNoteSpendExactV3StateInputs::derive_from_durable_anchor(
        transition,
        durable_anchor,
    )?;
    let public =
        FaithfulNoteSpendExactV3PublicStatement::from_signed_effect(signed_effect, &state)?;
    let public_wire = public.encode_public_inputs();

    if !verifier.verify_with_predicate(
        FAITHFUL_NOTE_SPEND_EXACT_V3_PREDICATE,
        carrier.inner_proof_bytes(),
        FAITHFUL_NOTE_SPEND_EXACT_V3_ACTION,
        FAITHFUL_NOTE_SPEND_EXACT_V3_RESOURCE,
        &public_wire,
    ) {
        return Err(FaithfulNoteSpendExactV3AcceptanceError::ProofRejected);
    }
    Ok(AcceptedFaithfulNoteSpendExactV3 {
        public,
        prior_fns3: exact_state_commit(transition.prior_root(), transition.prior_count())
            .map(|felt| felt.as_u32()),
        successor_fns3: exact_state_commit(
            transition.successor_root(),
            transition.successor_count(),
        )
        .map(|felt| felt.as_u32()),
        value_commitment: *value_commitment,
        // Compute this only after strict proof verification succeeds.  It binds the opaque token
        // to the exact canonical carrier bytes recovered from the authenticated signed effect.
        signed_spending_proof_digest: signed_spending_proof_digest(spending_proof),
    })
}

fn signed_spending_proof_digest(spending_proof: &[u8]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(ACCEPTED_SIGNED_PROOF_DIGEST_DOMAIN);
    hasher.update(
        &u64::try_from(spending_proof.len())
            .expect("exact FNSP-v3 carrier length fits u64")
            .to_le_bytes(),
    );
    hasher.update(spending_proof);
    *hasher.finalize().as_bytes()
}

fn read_u64_u16(lanes: &[u32]) -> u64 {
    debug_assert_eq!(lanes.len(), 4);
    lanes
        .iter()
        .copied()
        .enumerate()
        .fold(0, |value, (lane, limb)| {
            value | u64::from(limb) << (16 * lane)
        })
}

fn read_root8_bytes(lanes: &[u32]) -> [u8; 32] {
    debug_assert_eq!(lanes.len(), 8);
    let mut out = [0u8; 32];
    for (lane, value) in lanes.iter().copied().enumerate() {
        out[lane * 4..lane * 4 + 4].copy_from_slice(&value.to_le_bytes());
    }
    out
}

fn read_bytes32_u16(lanes: &[u32]) -> [u8; 32] {
    debug_assert_eq!(lanes.len(), 16);
    let mut out = [0u8; 32];
    for (lane, value) in lanes.iter().copied().enumerate() {
        let value = u16::try_from(value).expect("canonical exact FNSP-v3 u16 lane");
        out[lane * 2..lane * 2 + 2].copy_from_slice(&value.to_le_bytes());
    }
    out
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FaithfulNoteSpendExactV3AcceptanceError {
    /// Carrier, signed-statement, or independently derived state was invalid.
    Statement(FaithfulNoteSpendExactV3Error),
    /// The signed nullifier did not name the exact key inserted by the validated transition.
    SignedNullifierMismatch,
    /// The signed released value did not equal the exact value inserted by the transition.
    SignedValueMismatch { signed: u64, transition: u64 },
    /// The strict code-owned exact-v3 HidingFRI verifier refused the inner proof.
    ProofRejected,
    /// FAIL-CLOSED: no exact-v3 proof authority is installed in this process, so
    /// no proof can be checked and no acceptance token can be minted. This is a
    /// verify-only deployment that never called
    /// [`install_exact_fnsp_v3_proof_authority`] (the `dregg-turn-prover` startup
    /// hook), NOT a statement about the submitted proof.
    ProofAuthorityNotInstalled,
}

impl From<FaithfulNoteSpendExactV3Error> for FaithfulNoteSpendExactV3AcceptanceError {
    fn from(error: FaithfulNoteSpendExactV3Error) -> Self {
        Self::Statement(error)
    }
}

impl fmt::Display for FaithfulNoteSpendExactV3AcceptanceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Statement(error) => write!(f, "exact FNSP-v3 statement refused: {error}"),
            Self::SignedNullifierMismatch => f.write_str(
                "exact FNSP-v3 signed nullifier does not match the validated transition",
            ),
            Self::SignedValueMismatch { signed, transition } => write!(
                f,
                "exact FNSP-v3 signed value {signed} does not match transition value {transition}"
            ),
            Self::ProofRejected => f.write_str("exact FNSP-v3 proof rejected"),
            Self::ProofAuthorityNotInstalled => {
                f.write_str("no exact FNSP-v3 proof authority is installed in this process")
            }
        }
    }
}

impl Error for FaithfulNoteSpendExactV3AcceptanceError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Statement(error) => Some(error),
            Self::SignedNullifierMismatch
            | Self::SignedValueMismatch { .. }
            | Self::ProofRejected
            | Self::ProofAuthorityNotInstalled => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;

    use crate::action::{Effect, Event};
    use crate::builder::{ActionBuilder, TurnBuilder};
    use crate::executor::{ComputronCosts, ExactFnspV3AdmissionError, TurnExecutor};
    use crate::faithful_note_spend::FaithfulNoteSpendProofCarrier;
    use crate::faithful_note_spend_exact_v3::{
        FAITHFUL_NOTE_SPEND_EXACT_V3_PUBLIC_INPUT_COUNT,
        FAITHFUL_NOTE_SPEND_EXACT_V3_PUBLIC_WIRE_BYTES,
    };
    use crate::faithful_note_spend_exact_v3_anchor::derive_exact_fnsp_v3_durable_anchor;
    use dregg_cell::commitment::{RotationCarrierMaterial, V9RotationContext, digest8_to_bytes32};
    use dregg_cell::{
        AuthRequired, Cell, CellId, FIELD_ZERO, Ledger, NoteCommitment, Nullifier, Permissions,
    };
    use dregg_circuit::Faithful8;
    use dregg_circuit::exact_nullifier_aafi::{
        Digest8, ExactNullifierAafi, validate_exact_aafi_witness,
    };
    use dregg_circuit::field::BabyBear;

    const INNER_PROOF: &[u8] = &[0xde, 0xad, 0xbe, 0xef];

    fn actor() -> Cell {
        let mut cell = Cell::new([7u8; 32], [9u8; 32]);
        assert!(cell.state.credit_balance(500));
        cell.state.set_nonce(11);
        cell.permissions = Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        };
        cell
    }

    fn context(prior_fns3: Digest8) -> V9RotationContext {
        V9RotationContext {
            cells_root: BabyBear::new(101),
            nullifier_root: Faithful8::from_bytes32(&digest8_to_bytes32(prior_fns3)),
            commitments_root: Faithful8::ZERO,
            revoked_root: Faithful8::ZERO,
            iroot: BabyBear::new(202),
            material: RotationCarrierMaterial::default(),
        }
    }

    fn canonical_note_spend(nullifier: [u8; 32], value: u64, proof: Vec<u8>) -> Effect {
        let mut note_tree_root = [0u8; 32];
        for lane in 0..8 {
            note_tree_root[lane * 4..lane * 4 + 4]
                .copy_from_slice(&(100 + lane as u32).to_le_bytes());
        }
        Effect::NoteSpend {
            nullifier: Nullifier(nullifier),
            note_tree_root,
            value,
            asset_type: 0x0123_4567_89ab_cdef,
            spending_proof: proof,
            value_commitment: None,
        }
    }

    fn fixture(
        key: [u8; 32],
        value: u64,
    ) -> (
        ValidatedExactAafiTransition,
        ExactFnspV3DurableAnchor,
        Effect,
    ) {
        let witness = ExactNullifierAafi::new()
            .prepare_insert(key, value)
            .expect("fresh exact insertion");
        let transition = validate_exact_aafi_witness(&witness).expect("valid transition");
        let anchor = derive_exact_fnsp_v3_durable_anchor(
            &actor(),
            &context(witness.prior_state_commit),
            witness.prior_state_commit,
            witness.successor_state_commit,
        )
        .expect("durable anchor");
        let carrier =
            FaithfulNoteSpendExactV3ProofCarrier::new(0x1122_3344_5566_7788, INNER_PROOF.to_vec())
                .expect("carrier");
        (
            transition,
            anchor,
            canonical_note_spend(key, value, carrier.encode()),
        )
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct VerificationCall {
        predicate: String,
        proof: Vec<u8>,
        action: String,
        resource: String,
        public: Vec<u8>,
    }

    #[derive(Default)]
    struct RecordingVerifier {
        calls: Mutex<Vec<VerificationCall>>,
        accept: bool,
    }

    impl RecordingVerifier {
        fn accepting() -> Self {
            Self {
                calls: Mutex::new(Vec::new()),
                accept: true,
            }
        }

        fn calls(&self) -> Vec<VerificationCall> {
            self.calls.lock().expect("recording verifier lock").clone()
        }
    }

    impl ProofVerifier for RecordingVerifier {
        fn verify(&self, _proof: &[u8], _action: &str, _resource: &str, _vk: &[u8]) -> bool {
            panic!("exact v3 acceptance must not use generic verification")
        }

        fn verify_with_predicate(
            &self,
            predicate: &str,
            proof: &[u8],
            action: &str,
            resource: &str,
            public: &[u8],
        ) -> bool {
            self.calls
                .lock()
                .expect("recording verifier lock")
                .push(VerificationCall {
                    predicate: predicate.to_owned(),
                    proof: proof.to_vec(),
                    action: action.to_owned(),
                    resource: resource.to_owned(),
                    public: public.to_vec(),
                });
            self.accept
        }
    }

    fn accepted_fixture(key: [u8; 32], value: u64) -> (AcceptedFaithfulNoteSpendExactV3, Effect) {
        let (transition, anchor, effect) = fixture(key, value);
        let accepted = verify_with_code_owned_identity(
            &RecordingVerifier::accepting(),
            &effect,
            &transition,
            &anchor,
        )
        .expect("test verifier mints the opaque exact-v3 acceptance");
        (accepted, effect)
    }

    fn apply_direct(
        executor: &TurnExecutor,
        effect: &Effect,
    ) -> Result<(), (crate::TurnError, Vec<usize>)> {
        let actor = actor();
        let actor_id = actor.id();
        let mut ledger = Ledger::new();
        ledger.insert_cell(actor).expect("insert direct-test actor");
        let mut journal = crate::journal::LedgerJournal::new();
        executor.apply_effect(
            effect,
            &mut ledger,
            &[0],
            &actor_id,
            &actor_id,
            &mut journal,
            [0u8; 32],
        )
    }

    fn cleartext_turn(actor_id: CellId, nonce: u64, effects: Vec<Effect>) -> crate::Turn {
        let mut action =
            ActionBuilder::new_unchecked_for_tests(actor_id, "exact-note-spend", actor_id);
        for effect in effects {
            action = action.effect(effect);
        }
        let mut turn = TurnBuilder::new(actor_id, nonce);
        turn.add_action(action.build());
        turn.fee(0).build()
    }

    fn matching_note_create(value: u64, asset_type: u64, seed: u8) -> Effect {
        Effect::NoteCreate {
            commitment: NoteCommitment([seed; 32]),
            value,
            asset_type,
            encrypted_note: vec![seed, seed.wrapping_add(1)],
            value_commitment: None,
            range_proof: None,
        }
    }

    fn assert_exact_coordinate_mismatch_retains_pending(
        mutate: impl FnOnce(&mut Effect),
        expected_reason: &str,
    ) {
        let (accepted, original) = accepted_fixture([0x5a; 32], 7);
        let executor = TurnExecutor::new(ComputronCosts::zero());
        executor
            .install_exact_fnsp_v3_admission(accepted)
            .expect("install exact-v3 admission");

        let mut mutated = original.clone();
        mutate(&mut mutated);
        let (error, _) = apply_direct(&executor, &mutated)
            .expect_err("a coordinate splice must not cross exact-v3 admission");
        let crate::TurnError::InvalidEffect { reason } = error else {
            panic!("expected InvalidEffect coordinate refusal, got {error:?}");
        };
        assert!(
            reason.contains(expected_reason),
            "expected {expected_reason:?} refusal, got {reason:?}"
        );

        // A mismatch is not a consumption event. The original authenticated effect can still use
        // the same non-Clone token exactly once.
        apply_direct(&executor, &original).expect("matching effect still consumes pending token");
        assert!(
            executor
                .take_consumed_exact_fnsp_v3_admission()
                .expect("read consumed slot")
                .is_none(),
            "effect success alone is staged, never extractable before whole-turn commit"
        );
    }

    #[test]
    fn exact_v3_requires_installed_opaque_admission() {
        let (_, effect) = accepted_fixture([0x51; 32], 51);
        let executor = TurnExecutor::new(ComputronCosts::zero());
        let (error, _) = apply_direct(&executor, &effect)
            .expect_err("exact-v3 carrier without opaque admission must reject");
        let crate::TurnError::InvalidEffect { reason } = error else {
            panic!("expected InvalidEffect missing-admission refusal, got {error:?}");
        };
        assert!(reason.contains("requires an installed accepted proof"));
        assert!(executor.note_nullifiers.lock().unwrap().is_empty());
    }

    #[test]
    fn exact_v3_compares_every_effect_coordinate_carrier_digest_and_height() {
        assert_exact_coordinate_mismatch_retains_pending(
            |effect| {
                let Effect::NoteSpend { nullifier, .. } = effect else {
                    unreachable!()
                };
                *nullifier = Nullifier([0x99; 32]);
            },
            "nullifier",
        );
        assert_exact_coordinate_mismatch_retains_pending(
            |effect| {
                let Effect::NoteSpend { note_tree_root, .. } = effect else {
                    unreachable!()
                };
                note_tree_root[0..4].copy_from_slice(&123u32.to_le_bytes());
            },
            "historical root",
        );
        assert_exact_coordinate_mismatch_retains_pending(
            |effect| {
                let Effect::NoteSpend { value, .. } = effect else {
                    unreachable!()
                };
                *value += 1;
            },
            "value does not match",
        );
        assert_exact_coordinate_mismatch_retains_pending(
            |effect| {
                let Effect::NoteSpend { asset_type, .. } = effect else {
                    unreachable!()
                };
                *asset_type ^= 1;
            },
            "asset type",
        );
        assert_exact_coordinate_mismatch_retains_pending(
            |effect| {
                let Effect::NoteSpend {
                    value_commitment, ..
                } = effect
                else {
                    unreachable!()
                };
                *value_commitment = Some([0x42; 32]);
            },
            "value commitment",
        );
        assert_exact_coordinate_mismatch_retains_pending(
            |effect| {
                let Effect::NoteSpend { spending_proof, .. } = effect else {
                    unreachable!()
                };
                *spending_proof = FaithfulNoteSpendExactV3ProofCarrier::new(
                    0x1122_3344_5566_7788,
                    vec![0xba, 0xad, 0xf0, 0x0d],
                )
                .expect("same-height swapped carrier")
                .encode();
            },
            "carrier digest",
        );
        assert_exact_coordinate_mismatch_retains_pending(
            |effect| {
                let Effect::NoteSpend { spending_proof, .. } = effect else {
                    unreachable!()
                };
                *spending_proof = FaithfulNoteSpendExactV3ProofCarrier::new(
                    0x1122_3344_5566_7789,
                    INNER_PROOF.to_vec(),
                )
                .expect("different-height carrier")
                .encode();
            },
            "root height",
        );
    }

    #[test]
    fn exact_v3_slot_is_replacement_free_and_one_shot() {
        let (first, effect) = accepted_fixture([0x52; 32], 52);
        let (second, _) = accepted_fixture([0x53; 32], 53);
        let executor = TurnExecutor::new(ComputronCosts::zero());
        executor
            .install_exact_fnsp_v3_admission(first)
            .expect("first install");
        assert_eq!(
            executor.install_exact_fnsp_v3_admission(second),
            Err(ExactFnspV3AdmissionError::PendingAlreadyInstalled)
        );

        apply_direct(&executor, &effect).expect("first application consumes pending authority");
        let (error, _) = apply_direct(&executor, &effect)
            .expect_err("the applied token cannot authorize a second effect");
        let crate::TurnError::InvalidEffect { reason } = error else {
            panic!("expected InvalidEffect one-shot refusal, got {error:?}");
        };
        assert!(reason.contains("already applied"));
        assert!(
            executor
                .take_consumed_exact_fnsp_v3_admission()
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn strict_v3_dispatch_leaves_v2_path_unchanged() {
        let (pending_exact, exact_effect) = accepted_fixture([0x5e; 32], 94);
        let key = [0x54; 32];
        let value = 54;
        let mut planned = dregg_cell::nullifier_set::NullifierSet::new();
        planned
            .insert(Nullifier(key), value)
            .expect("fresh v2 planned insertion");
        let carrier = FaithfulNoteSpendProofCarrier::new(
            7,
            planned.faithful_root8_exact().to_bytes32(),
            vec![0xaa, 0xbb],
        )
        .expect("canonical v2 carrier");
        let effect = canonical_note_spend(key, value, carrier.encode());
        let executor = TurnExecutor::with_proof_verifier(
            ComputronCosts::zero(),
            Box::new(RecordingVerifier::accepting()),
        );
        executor
            .install_exact_fnsp_v3_admission(pending_exact)
            .expect("install unrelated pending exact-v3 authority");

        apply_direct(&executor, &effect).expect("v2 still uses its legacy verifier/successor path");
        assert!(
            executor
                .note_nullifiers
                .lock()
                .unwrap()
                .contains(&Nullifier(key))
        );
        assert!(
            executor
                .take_consumed_exact_fnsp_v3_admission()
                .unwrap()
                .is_none(),
            "v2 must never touch the exact-v3 slot"
        );
        apply_direct(&executor, &exact_effect)
            .expect("v2 leaves the installed exact-v3 token pending and usable");
    }

    #[test]
    fn genuine_execute_commits_receipt_nonce_and_only_then_promotes_exact_token() {
        let key = [0x55; 32];
        let value = 55;
        let (accepted, spend) = accepted_fixture(key, value);
        let asset_type = match &spend {
            Effect::NoteSpend { asset_type, .. } => *asset_type,
            _ => unreachable!(),
        };
        let actor = actor();
        let actor_id = actor.id();
        let mut ledger = Ledger::new();
        ledger.insert_cell(actor).expect("insert execution actor");
        let turn = cleartext_turn(
            actor_id,
            11,
            vec![spend.clone(), matching_note_create(value, asset_type, 0xc1)],
        );
        let executor = TurnExecutor::new(ComputronCosts::zero());
        executor
            .install_exact_fnsp_v3_admission(accepted)
            .expect("install accepted exact proof");

        let (_, receipt, _) = executor.execute(&turn, &mut ledger).unwrap_committed();
        assert_eq!(receipt.turn_hash, turn.hash());
        assert_eq!(receipt.agent, actor_id);
        assert_eq!(ledger.get(&actor_id).unwrap().state.nonce(), 12);
        assert!(
            executor
                .note_nullifiers
                .lock()
                .unwrap()
                .contains(&Nullifier(key))
        );
        assert!(
            executor
                .take_consumed_exact_fnsp_v3_admission()
                .unwrap()
                .is_none(),
            "Rust effect/receipt success is still unextractable before final producer commit"
        );
        assert!(
            executor
                .promote_applied_exact_fnsp_v3_admission_after_commit()
                .expect("final producer commits exact admission")
        );
        let consumed = executor
            .take_consumed_exact_fnsp_v3_admission()
            .unwrap()
            .expect("committed exact token is extractable exactly once");
        assert!(consumed.matches_signed_effect(&spend));
        assert!(
            executor
                .take_consumed_exact_fnsp_v3_admission()
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn later_turn_failure_rolls_applied_token_back_to_pending() {
        let key = [0x56; 32];
        let value = 56;
        let (accepted, spend) = accepted_fixture(key, value);
        let asset_type = match &spend {
            Effect::NoteSpend { asset_type, .. } => *asset_type,
            _ => unreachable!(),
        };
        let actor = actor();
        let actor_id = actor.id();
        let mut ledger = Ledger::new();
        ledger.insert_cell(actor).expect("insert rollback actor");
        let executor = TurnExecutor::new(ComputronCosts::zero());
        executor
            .install_exact_fnsp_v3_admission(accepted)
            .expect("install accepted exact proof");

        // The exact effect succeeds, then whole-turn note conservation rejects because there is
        // no matching output. Both the nullifier and linear token must roll back.
        let rejected = cleartext_turn(actor_id, 11, vec![spend.clone()]);
        let (error, _) = executor.execute(&rejected, &mut ledger).unwrap_rejected();
        assert!(matches!(
            error,
            crate::TurnError::NoteConservationViolation { .. }
        ));
        assert!(
            !executor
                .note_nullifiers
                .lock()
                .unwrap()
                .contains(&Nullifier(key))
        );
        assert_eq!(
            ledger.get(&actor_id).unwrap().state.nonce(),
            12,
            "executor policy intentionally charges the nonce even when the forest/final gate fails"
        );
        assert!(
            executor
                .take_consumed_exact_fnsp_v3_admission()
                .unwrap()
                .is_none(),
            "a rejected turn must expose no consumed token"
        );
        assert!(
            !executor
                .promote_applied_exact_fnsp_v3_admission_after_commit()
                .unwrap(),
            "rollback leaves no applied token available for false promotion"
        );

        // The same pending authority is retryable as one balanced atomic turn.
        let retry = cleartext_turn(
            actor_id,
            12,
            vec![spend, matching_note_create(value, asset_type, 0xc2)],
        );
        executor.execute(&retry, &mut ledger).unwrap_committed();
        assert!(
            executor
                .promote_applied_exact_fnsp_v3_admission_after_commit()
                .unwrap()
        );
        assert!(
            executor
                .take_consumed_exact_fnsp_v3_admission()
                .unwrap()
                .is_some()
        );
    }

    #[test]
    fn outer_producer_rejection_cannot_extract_inner_rust_commit() {
        let key = [0x57; 32];
        let value = 57;
        let (accepted, spend) = accepted_fixture(key, value);
        let asset_type = match &spend {
            Effect::NoteSpend { asset_type, .. } => *asset_type,
            _ => unreachable!(),
        };
        let actor = actor();
        let actor_id = actor.id();
        let mut ledger = Ledger::new();
        ledger
            .insert_cell(actor)
            .expect("insert producer-veto actor");
        let turn = cleartext_turn(
            actor_id,
            11,
            vec![spend, matching_note_create(value, asset_type, 0xc3)],
        );
        let executor = TurnExecutor::new(ComputronCosts::zero());
        executor
            .install_exact_fnsp_v3_admission(accepted)
            .expect("install accepted exact proof");

        executor.execute(&turn, &mut ledger).unwrap_committed();
        assert!(
            executor
                .take_consumed_exact_fnsp_v3_admission()
                .unwrap()
                .is_none(),
            "an inner Rust commit is not final-producer authority"
        );
        executor
            .restore_exact_fnsp_v3_admission_after_rejection()
            .expect("outer producer rejection restores staged authority");
        assert!(
            executor
                .take_consumed_exact_fnsp_v3_admission()
                .unwrap()
                .is_none(),
            "outer/Lean rejection can never expose a consumed token"
        );
        let (replacement, _) = accepted_fixture([0x58; 32], 58);
        assert_eq!(
            executor.install_exact_fnsp_v3_admission(replacement),
            Err(ExactFnspV3AdmissionError::PendingAlreadyInstalled),
            "restoration preserves the original opaque token rather than dropping it"
        );
    }

    #[test]
    fn acceptance_passes_only_inner_proof_and_exact_durable_76_lanes() {
        let (transition, anchor, effect) = fixture([0x5a; 32], 0x8877_6655_4433_2211);
        let verifier = RecordingVerifier::accepting();

        let accepted = verify_with_code_owned_identity(&verifier, &effect, &transition, &anchor)
            .expect("capturing strict verifier accepts fixture");
        let calls = verifier.calls();
        assert_eq!(calls.len(), 1);
        let call = &calls[0];
        assert_eq!(call.predicate, FAITHFUL_NOTE_SPEND_EXACT_V3_PREDICATE);
        assert_eq!(call.action, FAITHFUL_NOTE_SPEND_EXACT_V3_ACTION);
        assert_eq!(call.resource, FAITHFUL_NOTE_SPEND_EXACT_V3_RESOURCE);
        assert_eq!(call.proof, INNER_PROOF);
        assert_ne!(
            call.proof,
            match &effect {
                Effect::NoteSpend { spending_proof, .. } => spending_proof.as_slice(),
                _ => unreachable!(),
            }
        );
        assert_eq!(
            call.public.len(),
            FAITHFUL_NOTE_SPEND_EXACT_V3_PUBLIC_WIRE_BYTES
        );

        let lanes: Vec<u32> = call
            .public
            .chunks_exact(4)
            .map(|chunk| u32::from_le_bytes(chunk.try_into().expect("public lane")))
            .collect();
        assert_eq!(lanes.len(), FAITHFUL_NOTE_SPEND_EXACT_V3_PUBLIC_INPUT_COUNT);
        assert_eq!(&lanes[60..76], &anchor.expected_outer_public_inputs());
        assert_eq!(
            &lanes[36..44],
            &transition.successor_root().map(|felt| felt.as_u32())
        );
        assert_eq!(
            &lanes[44..52],
            &transition.prior_root().map(|felt| felt.as_u32())
        );

        // The opaque token retains exactly the statement which reached verification and augments
        // it only with the independently recomputed FNS3 pair needed by the future durable CAS.
        assert_eq!(accepted.public_input_lanes().as_slice(), lanes.as_slice());
        let binding = accepted.binding();
        assert_eq!(binding.historical_root_height(), 0x1122_3344_5566_7788);
        let Effect::NoteSpend {
            nullifier,
            note_tree_root,
            value,
            asset_type,
            ..
        } = &effect
        else {
            unreachable!()
        };
        assert_eq!(binding.historical_note_root(), *note_tree_root);
        assert_eq!(binding.nullifier(), nullifier.0);
        assert_eq!(binding.value(), *value);
        assert_eq!(binding.asset_type(), *asset_type);
        assert_eq!(
            binding.prior_root(),
            transition.prior_root().map(|felt| felt.as_u32())
        );
        assert_eq!(
            binding.successor_root(),
            transition.successor_root().map(|felt| felt.as_u32())
        );
        assert_eq!(binding.prior_count(), transition.prior_count());
        assert_eq!(binding.successor_count(), transition.successor_count());
        assert_eq!(
            binding.prior_fns3(),
            exact_state_commit(transition.prior_root(), transition.prior_count())
                .map(|felt| felt.as_u32())
        );
        assert_eq!(
            binding.successor_fns3(),
            exact_state_commit(transition.successor_root(), transition.successor_count())
                .map(|felt| felt.as_u32())
        );
        assert_eq!(
            binding.before_outer_commit(),
            anchor.before_commit().map(|felt| felt.as_u32())
        );
        assert_eq!(
            binding.after_outer_commit(),
            anchor.after_commit().map(|felt| felt.as_u32())
        );
    }

    #[test]
    fn acceptance_refuses_non_note_malformed_and_v2_before_verification() {
        let (transition, anchor, _) = fixture([0x5a; 32], 7);
        let verifier = RecordingVerifier::accepting();
        let non_note = Effect::EmitEvent {
            cell: CellId::from_bytes([0; 32]),
            event: Event {
                topic: [0; 32],
                data: vec![FIELD_ZERO],
            },
        };
        assert!(matches!(
            verify_with_code_owned_identity(&verifier, &non_note, &transition, &anchor),
            Err(FaithfulNoteSpendExactV3AcceptanceError::Statement(
                FaithfulNoteSpendExactV3Error::NotNoteSpend
            ))
        ));

        let malformed = canonical_note_spend([0x5a; 32], 7, b"not-an-fnsp-carrier".to_vec());
        assert!(matches!(
            verify_with_code_owned_identity(&verifier, &malformed, &transition, &anchor),
            Err(FaithfulNoteSpendExactV3AcceptanceError::Statement(
                FaithfulNoteSpendExactV3Error::Truncated { .. }
            ))
        ));

        let v2 = FaithfulNoteSpendProofCarrier::new(7, Faithful8::ZERO.to_bytes32(), vec![9])
            .expect("v2 carrier")
            .encode();
        assert!(matches!(
            verify_with_code_owned_identity(
                &verifier,
                &canonical_note_spend([0x5a; 32], 7, v2),
                &transition,
                &anchor,
            ),
            Err(FaithfulNoteSpendExactV3AcceptanceError::Statement(
                FaithfulNoteSpendExactV3Error::UnsupportedVersion(2)
            ))
        ));
        assert!(verifier.calls().is_empty());
    }

    #[test]
    fn signed_nullifier_and_value_must_join_transition_before_carrier_or_verifier() {
        let (transition, anchor, effect) = fixture([0x5a; 32], 7);
        let verifier = RecordingVerifier::accepting();

        let mut wrong_nullifier = effect.clone();
        if let Effect::NoteSpend {
            nullifier,
            spending_proof,
            ..
        } = &mut wrong_nullifier
        {
            *nullifier = Nullifier([0x99; 32]);
            *spending_proof = b"malformed is never parsed".to_vec();
        }
        assert_eq!(
            verify_with_code_owned_identity(&verifier, &wrong_nullifier, &transition, &anchor,),
            Err(FaithfulNoteSpendExactV3AcceptanceError::SignedNullifierMismatch)
        );

        let mut wrong_value = effect;
        if let Effect::NoteSpend {
            value,
            spending_proof,
            ..
        } = &mut wrong_value
        {
            *value = 8;
            *spending_proof = b"malformed is never parsed".to_vec();
        }
        assert_eq!(
            verify_with_code_owned_identity(&verifier, &wrong_value, &transition, &anchor),
            Err(
                FaithfulNoteSpendExactV3AcceptanceError::SignedValueMismatch {
                    signed: 8,
                    transition: 7,
                }
            )
        );
        assert!(verifier.calls().is_empty());
    }

    #[test]
    fn accepted_token_refuses_same_coordinate_swapped_or_malformed_signed_proof() {
        let (transition, anchor, effect) = fixture([0x5a; 32], 7);
        let verifier = RecordingVerifier::accepting();
        let accepted = verify_with_code_owned_identity(&verifier, &effect, &transition, &anchor)
            .expect("fixture proof accepted by recording verifier");
        assert!(accepted.matches_signed_effect(&effect));
        let Effect::NoteSpend { spending_proof, .. } = &effect else {
            unreachable!()
        };
        assert_eq!(
            accepted.signed_spending_proof_digest(),
            signed_spending_proof_digest(spending_proof)
        );

        // A different canonical carrier with the same height makes the exact same 76 public lanes:
        // the proof payload is intentionally opaque to the statement.  The token digest is the
        // independent join which prevents those signed bytes from being swapped at finalization.
        let swapped_carrier = FaithfulNoteSpendExactV3ProofCarrier::new(
            0x1122_3344_5566_7788,
            vec![0xba, 0xad, 0xf0, 0x0d],
        )
        .expect("canonical swapped carrier");
        let mut swapped = effect.clone();
        if let Effect::NoteSpend { spending_proof, .. } = &mut swapped {
            *spending_proof = swapped_carrier.encode();
        }
        let state =
            FaithfulNoteSpendExactV3StateInputs::derive_from_durable_anchor(&transition, &anchor)
                .expect("matching state producers");
        let swapped_public =
            FaithfulNoteSpendExactV3PublicStatement::from_signed_effect(&swapped, &state)
                .expect("swapped carrier remains canonical");
        assert_eq!(
            accepted.public_input_lanes(),
            swapped_public.as_u32_array(),
            "proof payload is absent from the coordinate statement"
        );
        assert!(!accepted.matches_signed_effect(&swapped));

        let mut malformed = effect;
        if let Effect::NoteSpend { spending_proof, .. } = &mut malformed {
            *spending_proof = b"malformed signed carrier".to_vec();
        }
        assert!(!accepted.matches_signed_effect(&malformed));
        assert!(!accepted.matches_signed_effect(&Effect::EmitEvent {
            cell: CellId::from_bytes([0; 32]),
            event: Event {
                topic: [0; 32],
                data: vec![FIELD_ZERO],
            },
        }));
    }

    #[test]
    fn mixed_transition_and_anchor_refuses_before_proof_verification() {
        let (transition_a, _, effect) = fixture([0x31; 32], 31);
        let (_, anchor_b, _) = fixture([0x32; 32], 32);
        let verifier = RecordingVerifier::accepting();

        let no_token =
            verify_with_code_owned_identity(&verifier, &effect, &transition_a, &anchor_b);
        assert!(matches!(
            no_token,
            Err(FaithfulNoteSpendExactV3AcceptanceError::Statement(
                FaithfulNoteSpendExactV3Error::StateProducerMismatch { .. }
            ))
        ));
        assert!(verifier.calls().is_empty());
    }

    /// ⚑ FAIL-CLOSED: core `dregg-turn` alone cannot mint an acceptance token.
    ///
    /// This test used to assert `ProofRejected` — the code-owned exact-v3 HidingFRI
    /// verifier refusing a dummy inner proof. That verifier now lives in
    /// `dregg-turn-prover` (it needs `dregg-circuit-prove`), and core `turn` links
    /// no prover, so the honest expectation for THIS crate is that the mint refuses
    /// for want of an authority — never that it silently succeeds.
    ///
    /// The other half — "with the real verifier installed, a dummy inner proof is
    /// REJECTED (not accepted, not short-circuited)" — is
    /// `turn-prover/tests/exact_v3_authority_installed.rs`
    /// (`installed_authority_reaches_the_real_verifier_and_refuses_a_bogus_proof`).
    /// Both halves together are the old assertion, plus the crate boundary.
    #[test]
    fn core_alone_cannot_mint_an_acceptance_no_proof_authority_is_installed() {
        assert!(
            !exact_fnsp_v3_proof_authority_installed(),
            "core dregg-turn links no prover, so no authority can be installed here"
        );
        let (transition, anchor, effect) = fixture([0x5a; 32], 0x8877_6655_4433_2211);
        assert_eq!(
            verify_faithful_note_spend_exact_v3_acceptance(&effect, &transition, &anchor),
            Err(FaithfulNoteSpendExactV3AcceptanceError::ProofAuthorityNotInstalled)
        );
    }
}
