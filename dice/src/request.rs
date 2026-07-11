//! Request / evidence structures and the receipt-shaped request commitment.

use serde::{Deserialize, Serialize};

use crate::event::EventId;
use crate::util::absorb_len_prefixed;

/// The derivation version this build produces. Bound into evidence so a verifier
/// rejects evidence from an incompatible derivation.
pub const DERIVATION_VERSION: u32 = 1;

/// Domain tag for the receipt-shaped request commitment.
pub const DOMAIN_REQUEST_COMMITMENT: &[u8] = b"dregg-dice/request-commitment/v1";

/// Everything that must be bound *before* the randomness result is known.
///
/// Mirrors the design's randomness-context inputs: the game/sequence/pre-state/
/// action, the purpose (`event_kind`), and how many draws (`draw_count`) the
/// event consumes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RandomnessRequest {
    /// The committed game identity (opaque bytes; production binds a VRF key
    /// epoch + ruleset hash into this).
    pub game_binding: Vec<u8>,
    /// Transition sequence number.
    pub seq: u64,
    /// Committed pre-state root this draw resolves against.
    pub pre_state_root: [u8; 32],
    /// Commitment to the finalized typed action.
    pub action_hash: [u8; 32],
    /// Purpose tag, domain-separating subsystems (`"combat/hit"`, `"loot"`, …).
    pub event_kind: String,
    /// Number of indexed draws this event consumes.
    pub draw_count: u32,
}

impl RandomnessRequest {
    /// The [`EventId`] this request derives — the seed's binding context.
    pub fn event_id(&self) -> EventId {
        EventId::derive(
            &self.game_binding,
            self.seq,
            &self.pre_state_root,
            &self.action_hash,
            &self.event_kind,
            self.draw_count,
        )
    }

    /// A receipt-shaped commitment the game engine would store **before** the
    /// result exists. It binds the full request (via its `EventId`) so the stored
    /// receipt fixes the game, sequence, pre-state, action, purpose, and draw
    /// count in advance.
    ///
    /// The actual `attested-dm` `LedgerEntry` integration — carrying this
    /// alongside the transition receipt — is a documented follow-up, not part of
    /// this crate.
    pub fn commitment(&self) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        absorb_len_prefixed(&mut h, DOMAIN_REQUEST_COMMITMENT);
        h.update(self.event_id().as_bytes());
        *h.finalize().as_bytes()
    }
}

/// A public-randomness beacon's genesis-pinned parameters.
///
/// These are committed **before** any draw (folded into
/// [`RandomnessRequest::game_binding`] via
/// [`Hybrid::genesis_binding`](crate::Hybrid::genesis_binding)), so the server
/// cannot swap in a different beacon, a favourable chain, or a favourable
/// schedule after the fact. The pure verifier re-derives the genesis binding from
/// these and rejects a mismatch.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BeaconParams {
    /// Beacon identity (e.g. `b"hashchain/test"` or `b"drand/quicknet"`).
    pub beacon_id: Vec<u8>,
    /// How a round's output is verified.
    pub kind: BeaconKind,
    /// How the round used for an event is derived from its sequence number.
    pub schedule: BeaconSchedule,
}

/// How a beacon round's output is verified.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum BeaconKind {
    /// A forward-secure hash-chain beacon (the shipped, testable model).
    ///
    /// `anchor = H^length(root)` is published at genesis. Round `R` reveals
    /// `H^(length-R)(root)`; a verifier checks `H^R(output) == anchor`. Preimage
    /// resistance makes a future round's output unpredictable at commit time, and
    /// the anchor is genesis-pinned. This is **not** a threshold-BLS beacon — it
    /// trusts a single operator not to precompute the chain against a target
    /// outcome; a real [`Drand`](BeaconKind::Drand) beacon is the production path.
    HashChain {
        /// `H^length(root)` — pinned at genesis.
        anchor: [u8; 32],
        /// Chain length; legal rounds are `1..=length`.
        length: u64,
    },
    /// A drand-style threshold-BLS beacon. Shape only: verifying a round is a BLS
    /// pairing check of the round signature against the pinned group public key
    /// under drand's ciphersuite. Wiring the live drand group key + round fetch is
    /// the remaining gap for escape hatch #2; the verifier fails closed here.
    Drand {
        /// The drand chain's group public key (BLS12-381).
        group_public_key: Vec<u8>,
        /// The drand ciphersuite / scheme identifier.
        scheme: String,
    },
}

/// How the beacon round for an event is derived from its sequence number.
///
/// The round is a deterministic function of the receipt `seq`, so the server
/// cannot pick a favourable already-published round (escape hatch #2, schedule
/// layer): `round = base_round + seq * stride`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BeaconSchedule {
    /// Round used for `seq == 0`.
    pub base_round: u64,
    /// Rounds advanced per unit of `seq`.
    pub stride: u64,
}

impl BeaconSchedule {
    /// The beacon round bound to `seq`.
    pub fn expected_round(&self, seq: u64) -> u64 {
        self.base_round
            .saturating_add(seq.saturating_mul(self.stride))
    }
}

/// The beacon opening recorded in hybrid evidence: which params, which round, and
/// the claimed round output.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BeaconEvidence {
    /// The genesis-pinned beacon parameters (re-checked against `game_binding`).
    pub params: BeaconParams,
    /// The schedule-bound round this event draws from.
    pub round: u64,
    /// The beacon's output for `round`.
    pub output: [u8; 32],
}

/// Which side of the hybrid finalization produced this evidence.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Finalization {
    /// The normal path: the server published its LB-VRF proof; the seed mixes the
    /// VRF output with the beacon output.
    ServerProvided,
    /// The timeout path: the server withheld its LB-VRF proof past the deadline, so
    /// anyone finalized from the beacon alone. The seed is determined (no reroll)
    /// and the server-missed fault is recorded here for all to see.
    ServerMissed,
}

/// Source-specific evidence needed to re-derive and check a seed.
///
/// Each variant carries exactly what its verifier needs. This slice fully
/// implements [`Deterministic`](EvidenceKind::Deterministic),
/// [`CommitReveal`](EvidenceKind::CommitReveal), a mock
/// [`Beacon`](EvidenceKind::Beacon), the real post-quantum
/// [`LbVrf`](EvidenceKind::LbVrf) (backed by the `pqvrf` LB-VRF), and the
/// [`Hybrid`](EvidenceKind::Hybrid) endpoint (genesis-committed LB-VRF key-chain +
/// delayed schedule-bound beacon, with a timeout-finalization marker).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum EvidenceKind {
    /// A test/offline deterministic source keyed on a caller-supplied context.
    Deterministic {
        /// Contribution folded into the seed alongside the event id.
        context: [u8; 32],
    },
    /// Two-party commit-reveal. The server commits to `server_reveal` first, then
    /// both contributions feed the seed.
    CommitReveal {
        /// `H(DOMAIN_COMMIT || server_reveal)` — published before the reveal.
        server_commitment: [u8; 32],
        /// The opened server contribution.
        server_reveal: [u8; 32],
        /// The player's contribution.
        player_contribution: [u8; 32],
    },
    /// A public randomness beacon output (mocked here — this slice does not
    /// verify the beacon's own signature/finality; that needs the beacon infra).
    Beacon {
        /// Beacon identity.
        beacon_id: Vec<u8>,
        /// The future round fixed by the request acknowledgement.
        round: u64,
        /// The beacon's output for that round.
        output: [u8; 32],
    },
    /// A post-quantum **LB-VRF** output + proof (Esgin et al. FC 2021, Set I; the
    /// `pqvrf` crate). The VRF input is the draw's [`EventId`] bytes; the verifier
    /// re-runs `pqvrf::verify(&pk, event_id, &output, &proof)` and, on success,
    /// derives the seed over the *verified* output. Uniqueness of the accepted
    /// output for a given `(pk, input)` reduces to Module-SIS, so a forged output
    /// or proof is rejected — the one-output-per-input guarantee. All three fields
    /// are the `pqvrf` structures in their canonical little-endian byte encoding
    /// (see `ServerVrf`'s codec); a wrong length is rejected as malformed.
    LbVrf {
        /// The LB-VRF public key `t = A*s` (canonical LE bytes).
        public_key: Vec<u8>,
        /// The LB-VRF output `v` (canonical LE bytes).
        output: Vec<u8>,
        /// The LB-VRF proof `(z, c)` (canonical LE bytes), re-checked by `pqvrf::verify`.
        proof: Vec<u8>,
    },
    /// The hybrid endpoint: a **genesis-committed LB-VRF key-chain** mixed with a
    /// **delayed, schedule-bound public beacon**, with a timeout-finalization marker.
    ///
    /// Normal path (`ServerProvided`): the seed mixes the epoch's LB-VRF output over
    /// the event id with the schedule-bound beacon round output. The epoch key
    /// (epoch = `seq`) is proven to be the one committed in the genesis key-chain
    /// root (`epoch_proof`), so a per-turn key swap is rejected (hatch #1). Timeout
    /// path (`ServerMissed`): the VRF fields are ignored and the seed is determined
    /// by the beacon alone — a withheld proof yields no reroll and the fault is
    /// visible (hatch #5).
    Hybrid {
        /// Which finalization produced this evidence.
        finalization: Finalization,
        /// The genesis-committed LB-VRF key-chain Merkle root (pinned in
        /// `game_binding` together with the beacon params).
        key_chain_root: [u8; 32],
        /// The epoch (`= seq`) LB-VRF public key (canonical LE bytes; empty on the
        /// `ServerMissed` path, where it is ignored).
        vrf_public_key: Vec<u8>,
        /// The epoch LB-VRF output (canonical LE bytes; empty on `ServerMissed`).
        vrf_output: Vec<u8>,
        /// The epoch LB-VRF proof (canonical LE bytes; empty on `ServerMissed`).
        vrf_proof: Vec<u8>,
        /// Merkle membership path proving `vrf_public_key` is the key committed at
        /// leaf `seq` of `key_chain_root` (empty on `ServerMissed`).
        epoch_proof: Vec<[u8; 32]>,
        /// The delayed-beacon opening.
        beacon: BeaconEvidence,
    },
}

/// The randomness evidence recorded alongside a transition, mirroring the
/// design's `randomness_context`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RandomnessEvidence {
    /// Derivation version the evidence was produced under.
    pub derivation_version: u32,
    /// The source-specific opening.
    pub source: EvidenceKind,
    /// A commitment to the exact draw transcript
    /// ([`DrawStream::transcript_commitment`](crate::DrawStream::transcript_commitment)).
    /// The verifier recomputes this from the re-derived seed and rejects a
    /// mismatch — the grinding tooth.
    pub draw_transcript_commitment: [u8; 32],
}
