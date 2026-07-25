//! Transportable private role assignment for a four-seat Descent/MMO raid.
//!
//! One Tier-1 producer owns the private suitability scores and independent
//! admissibility matrix, constructs the real Lean-emitted HidingFri proof, and
//! publishes only `(session, rule, input_root, roles[4])`.  The public roles are
//! a permutation, admissible for the hidden matrix, globally maximize total
//! suitability over all 24 assignments, and use the lexicographically first
//! optimum on ties.
//!
//! [`RaidAssignmentSession`] owns the public one-shot lifecycle: it pins the
//! expected session and canonical verifier identity, verifies transported proof
//! bytes, and refuses replay without mutating an accepted assignment.  This is
//! not distributed private-input assembly—the producer sees all inputs—and the
//! standalone receipt is not claimed as an `Effect::Custom` cell transition.
//!
//! ## A SEAT HERE IS A NUMBER, NOT A PLAYER
//!
//! Nothing in the public statement identifies anybody.  `roles[i]` says "the
//! `i`th row of some private matrix got this role"; WHOSE row that was is not a
//! fact this proof carries.  A consumer that reads `roles[0]` as "the first
//! player who joined" is asserting that binding itself, and a receipt minted
//! over another group's matrix satisfies the relation just as well.
//!
//! The one public input a consumer can push identity through is [`session`],
//! which the AIR binds.  Derive it from the roster — a canonical ordering of the
//! authenticated identities plus whatever each of them committed to — and the
//! statement itself then denotes exactly that group in exactly that seat order,
//! recomputable by anyone from public data with no host records in the loop.
//! `dreggnet_party::crew` is the worked instance of that pattern
//! (`CrewRoll::proof_session` / `CrewRoll::accept`); a host that instead keeps an
//! operation id it rechecks on restart is trusting its own bookkeeping, which is
//! a weaker and separately-stated claim.
//!
//! [`session`]: RaidAssignmentSession::session

use dregg_circuit_prove::private_raid_assignment as proof;
use serde::{Deserialize, Serialize};

pub const RAID_SEATS: usize = proof::SEAT_COUNT;
pub const RAID_ROLES: usize = proof::ROLE_COUNT;

/// Public role IDs used by the fixed Lean relation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum RaidRole {
    Bulwark = 0,
    Striker = 1,
    Mender = 2,
    Pathfinder = 3,
}

impl TryFrom<u8> for RaidRole {
    type Error = RaidAssignmentError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(Self::Bulwark),
            1 => Ok(Self::Striker),
            2 => Ok(Self::Mender),
            3 => Ok(Self::Pathfinder),
            _ => Err(RaidAssignmentError::InvalidStatement(format!(
                "role {value} is outside the fixed four-role roster"
            ))),
        }
    }
}

/// Stable storage/network representation.  Public inputs use the exact
/// descriptor ABI; proof bytes are opaque and interpreted only by the pinned
/// verifier.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RaidAssignmentWireReceipt {
    pub verifier_key: [u8; 32],
    pub public_inputs: Vec<u32>,
    pub proof_bytes: Vec<u8>,
}

impl RaidAssignmentWireReceipt {
    pub fn to_postcard(&self) -> Result<Vec<u8>, RaidAssignmentError> {
        postcard::to_allocvec(self).map_err(|error| {
            RaidAssignmentError::WireFormat(format!(
                "cannot encode private raid assignment receipt: {error}"
            ))
        })
    }

    pub fn from_postcard(bytes: &[u8]) -> Result<Self, RaidAssignmentError> {
        postcard::from_bytes(bytes).map_err(|error| {
            RaidAssignmentError::WireFormat(format!(
                "cannot decode private raid assignment receipt: {error}"
            ))
        })
    }

    pub fn into_receipt(self) -> Result<RaidAssignmentReceipt, RaidAssignmentError> {
        if self.verifier_key != proof::canonical_vk_hash() {
            return Err(RaidAssignmentError::VerifierMismatch);
        }
        let statement = proof::PublicStatement::try_from_u32s(&self.public_inputs)
            .map_err(RaidAssignmentError::InvalidStatement)?;
        if self.proof_bytes.is_empty() {
            return Err(RaidAssignmentError::WireFormat(
                "private raid assignment proof is empty".to_string(),
            ));
        }
        Ok(RaidAssignmentReceipt {
            statement,
            proof_bytes: self.proof_bytes,
            verifier_key: self.verifier_key,
        })
    }
}

/// An owning public receipt: exact public statement, canonical verifier
/// identity, and opaque hiding proof.  It contains no scores, admissibility
/// bits, blinding, or aggregate score.
#[derive(Clone, PartialEq, Eq)]
pub struct RaidAssignmentReceipt {
    statement: proof::PublicStatement,
    proof_bytes: Vec<u8>,
    verifier_key: [u8; 32],
}

impl std::fmt::Debug for RaidAssignmentReceipt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RaidAssignmentReceipt")
            .field("statement", &self.statement)
            .field("verifier_key", &self.verifier_key)
            .field("proof_len", &self.proof_bytes.len())
            .finish()
    }
}

impl RaidAssignmentReceipt {
    fn from_proof(
        zk_proof: &proof::PrivateRaidZkProof,
        statement: proof::PublicStatement,
    ) -> Result<Self, RaidAssignmentError> {
        // A producer cannot emit an owning receipt it has not itself checked.
        proof::verify_zk(zk_proof, statement).map_err(RaidAssignmentError::InvalidProof)?;
        Ok(Self {
            statement,
            proof_bytes: zk_proof
                .to_postcard()
                .map_err(RaidAssignmentError::InvalidProof)?,
            verifier_key: proof::canonical_vk_hash(),
        })
    }

    pub const fn statement(&self) -> proof::PublicStatement {
        self.statement
    }

    pub fn proof_bytes(&self) -> &[u8] {
        &self.proof_bytes
    }

    pub const fn verifier_key(&self) -> [u8; 32] {
        self.verifier_key
    }

    pub fn to_wire(&self) -> RaidAssignmentWireReceipt {
        RaidAssignmentWireReceipt {
            verifier_key: self.verifier_key,
            public_inputs: self.statement.as_u32_vec(),
            proof_bytes: self.proof_bytes.clone(),
        }
    }

    pub fn to_postcard(&self) -> Result<Vec<u8>, RaidAssignmentError> {
        self.to_wire().to_postcard()
    }

    pub fn from_postcard(bytes: &[u8]) -> Result<Self, RaidAssignmentError> {
        RaidAssignmentWireReceipt::from_postcard(bytes)?.into_receipt()
    }
}

/// Produce a real hiding receipt from the private four-by-four raid matrix.
/// Scores must be in `0..=3`; `admissible[seat][role]` independently controls
/// whether that seat may receive that role.
pub fn prove_private_assignment(
    session: u32,
    scores: [[u8; RAID_ROLES]; RAID_SEATS],
    admissible: [[bool; RAID_ROLES]; RAID_SEATS],
) -> Result<RaidAssignmentReceipt, RaidAssignmentError> {
    let witness = proof::PrivateRaidWitness::try_new_fresh(scores, admissible)
        .map_err(RaidAssignmentError::InvalidPrivateInput)?;
    let (zk_proof, statement) =
        proof::prove_zk(session, &witness).map_err(RaidAssignmentError::InvalidProof)?;
    RaidAssignmentReceipt::from_proof(&zk_proof, statement)
}

/// Public application value minted only after proof verification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RaidPartyAssignment {
    session: u32,
    input_root: [u32; proof::DIGEST_WIDTH],
    roles: [RaidRole; RAID_SEATS],
}

impl RaidPartyAssignment {
    pub const fn session(self) -> u32 {
        self.session
    }

    pub const fn input_root(self) -> [u32; proof::DIGEST_WIDTH] {
        self.input_root
    }

    pub const fn roles(self) -> [RaidRole; RAID_SEATS] {
        self.roles
    }

    pub fn role_for_seat(self, seat: usize) -> Option<RaidRole> {
        self.roles.get(seat).copied()
    }
}

/// One public raid-assignment slot. Exactly one verified assignment may land
/// for its session; subsequent submissions are explicit replay refusals.
#[derive(Clone, Debug)]
pub struct RaidAssignmentSession {
    session: u32,
    assignment: Option<RaidPartyAssignment>,
}

impl RaidAssignmentSession {
    pub fn new(session: u32) -> Result<Self, RaidAssignmentError> {
        // Validate canonicality without inventing another modulus check.
        proof::PublicStatement {
            session,
            rule: proof::RULE_ID,
            input_root: [0; proof::DIGEST_WIDTH],
            roles: [0, 1, 2, 3],
        }
        .validate()
        .map_err(RaidAssignmentError::InvalidStatement)?;
        Ok(Self {
            session,
            assignment: None,
        })
    }

    pub const fn session(&self) -> u32 {
        self.session
    }

    pub const fn assignment(&self) -> Option<&RaidPartyAssignment> {
        self.assignment.as_ref()
    }

    /// Verify and land one assignment atomically.  Every refusal leaves the
    /// session's previous value byte-for-byte unchanged.
    pub fn accept(
        &mut self,
        receipt: &RaidAssignmentReceipt,
    ) -> Result<RaidPartyAssignment, RaidAssignmentError> {
        if self.assignment.is_some() {
            return Err(RaidAssignmentError::Replay);
        }
        if receipt.verifier_key != proof::canonical_vk_hash() {
            return Err(RaidAssignmentError::VerifierMismatch);
        }
        if receipt.statement.session != self.session {
            return Err(RaidAssignmentError::SessionMismatch {
                expected: self.session,
                claimed: receipt.statement.session,
            });
        }
        let verified =
            proof::verify_postcard(&receipt.proof_bytes, &receipt.statement.as_u32_vec())
                .map_err(RaidAssignmentError::InvalidProof)?;
        let mut roles = [RaidRole::Bulwark; RAID_SEATS];
        for (seat, role) in verified.roles().into_iter().enumerate() {
            roles[seat] = RaidRole::try_from(role)?;
        }
        let assignment = RaidPartyAssignment {
            session: verified.session(),
            input_root: verified.input_root(),
            roles,
        };
        self.assignment = Some(assignment);
        Ok(assignment)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RaidAssignmentError {
    InvalidPrivateInput(String),
    InvalidStatement(String),
    InvalidProof(String),
    WireFormat(String),
    VerifierMismatch,
    SessionMismatch { expected: u32, claimed: u32 },
    Replay,
}

impl std::fmt::Display for RaidAssignmentError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidPrivateInput(reason) => {
                write!(f, "private raid input refused: {reason}")
            }
            Self::InvalidStatement(reason) => {
                write!(f, "private raid public statement refused: {reason}")
            }
            Self::InvalidProof(reason) => write!(f, "private raid proof refused: {reason}"),
            Self::WireFormat(reason) => write!(f, "private raid receipt refused: {reason}"),
            Self::VerifierMismatch => write!(f, "private raid verifier identity mismatch"),
            Self::SessionMismatch { expected, claimed } => write!(
                f,
                "private raid session mismatch: expected {expected}, claimed {claimed}"
            ),
            Self::Replay => write!(f, "private raid assignment session is already filled"),
        }
    }
}

impl std::error::Error for RaidAssignmentError {}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture() -> (
        [[u8; RAID_ROLES]; RAID_SEATS],
        [[bool; RAID_ROLES]; RAID_SEATS],
    ) {
        (
            [[3, 2, 0, 0], [3, 0, 1, 0], [0, 0, 3, 1], [0, 1, 0, 3]],
            [
                [false, true, true, true],
                [true, true, true, true],
                [true, true, true, true],
                [true, true, true, true],
            ],
        )
    }

    #[test]
    fn private_raid_receipt_roundtrips_and_mints_global_role_assignment() {
        let (scores, admissible) = fixture();
        let receipt = prove_private_assignment(808, scores, admissible).unwrap();
        assert_eq!(receipt.statement().roles, [1, 0, 2, 3]);
        assert_eq!(receipt.verifier_key(), proof::canonical_vk_hash());
        assert!(!receipt.proof_bytes().is_empty());

        let bytes = receipt.to_postcard().unwrap();
        let restored = RaidAssignmentReceipt::from_postcard(&bytes).unwrap();
        assert_eq!(restored, receipt);
        let mut session = RaidAssignmentSession::new(808).unwrap();
        let assignment = session.accept(&restored).unwrap();
        assert_eq!(
            assignment.roles(),
            [
                RaidRole::Striker,
                RaidRole::Bulwark,
                RaidRole::Mender,
                RaidRole::Pathfinder,
            ]
        );
        assert_eq!(assignment.input_root(), receipt.statement().input_root);
    }

    #[test]
    fn private_raid_session_replay_and_every_transport_tamper_refuse_atomically() {
        let (scores, admissible) = fixture();
        let receipt = prove_private_assignment(909, scores, admissible).unwrap();
        let wire = receipt.to_wire();

        let mut variants = Vec::new();
        let mut wrong_session = wire.clone();
        wrong_session.public_inputs[0] += 1;
        variants.push((wrong_session, "session"));
        let mut wrong_root = wire.clone();
        wrong_root.public_inputs[2] ^= 1;
        variants.push((wrong_root, "root"));
        let mut wrong_roles = wire.clone();
        wrong_roles.public_inputs.swap(10, 11);
        variants.push((wrong_roles, "roles"));
        let mut wrong_proof = wire.clone();
        let at = wrong_proof.proof_bytes.len() / 2;
        wrong_proof.proof_bytes[at] ^= 1;
        variants.push((wrong_proof, "proof"));

        for (wire, label) in variants {
            let attempted = wire.into_receipt().unwrap();
            let mut session = RaidAssignmentSession::new(909).unwrap();
            assert!(session.accept(&attempted).is_err(), "{label} tamper landed");
            assert_eq!(session.assignment(), None, "{label} tamper mutated state");
        }

        let mut wrong_vk = wire.clone();
        wrong_vk.verifier_key[0] ^= 1;
        assert!(matches!(
            wrong_vk.into_receipt(),
            Err(RaidAssignmentError::VerifierMismatch)
        ));
        let mut duplicate_role = wire.clone();
        duplicate_role.public_inputs[11] = duplicate_role.public_inputs[10];
        assert!(duplicate_role.into_receipt().is_err());

        let mut session = RaidAssignmentSession::new(909).unwrap();
        let landed = session.accept(&receipt).unwrap();
        assert!(matches!(
            session.accept(&receipt),
            Err(RaidAssignmentError::Replay)
        ));
        assert_eq!(session.assignment(), Some(&landed));
    }
}
