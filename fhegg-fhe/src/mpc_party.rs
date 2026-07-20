//! Party-owned execution of the output-boundary boolean MPC.
//!
//! Unlike [`crate::mpc::cross_curves`], the coordinator in this module never
//! receives a vector containing all shares of a curve coefficient. Each party
//! enters with only its own mod-`t` arithmetic rows (the exact output shape of
//! [`crate::boundary::MaskedBoundaryParty::derive_mod_t_share`]), peer-distributes
//! fresh boolean shares of those rows, and retains exactly one boolean share of
//! every input wire and one share of every Beaver triple. For an AND gate, it sends only
//! `d_i = x_i xor a_i` and `e_i = y_i xor b_i`; the coordinator XORs a full
//! quorum and broadcasts the opened, one-time-padded `(d,e)`. Only the final
//! index and volume shares are reconstructed.
//!
//! The crossing circuit is the same lowest-index-stable balanced volume-argmax as
//! [`crate::mpc::mpc_crossing`]: compute every `min(D[p], S[p])` under sharing,
//! then reduce adjacent candidates in a balanced tournament, keeping the left
//! candidate on equality. Odd candidates are carried without a secret branch.
//! [`PartyMpcSession::equality`] selects a second, scalar circuit over the same
//! ingress and Beaver engine: reduce two mod-`t` shared operands, compare every
//! shared bit, and reconstruct only the final equality bit. This is intended for
//! invariant and certificate decisions whose refusal path must not reveal the
//! rejected residue.
//! [`PartyMpcSession::less_than`] selects the corresponding strict-comparison
//! circuit and reconstructs only `left < right`. This is the reusable private
//! ordering organ for allocation, preference, matchmaking, and range windows;
//! neither operand nor their difference appears in its public transcript.
//!
//! # Security and deployment scope
//!
//! This is a process-shaped semi-honest runtime, not a malicious-secure network
//! protocol. [`trusted_dealer_triples`] is explicitly trusted preprocessing, but
//! receives only public circuit shape and never receives input rows or aggregate
//! curves. Input sharing is performed independently by each party over direct
//! peer channels. The in-memory channels are unauthenticated and there are no MACs, signatures,
//! replay storage, crash recovery, or dealer-free triple generation. The
//! coordinator enforces a full `n`-party quorum and strict message order, but it
//! cannot prove a malicious party used its assigned input/triple shares.
//!
//! The implementation opens one scalar Beaver gate per channel round. The
//! transcript therefore distinguishes actual scalar opening rounds from the
//! smaller batched circuit depth exposed by [`crate::mpc::crossing_rounds`].

use std::fmt;
use std::sync::mpsc::{self, Receiver, RecvTimeoutError, Sender};
use std::time::{Duration, Instant};

use rand::Rng;

use crate::mpc::{crossing_rounds, index_bits, Crossing};

/// Bounded authenticated process transport for the scalar equality runtime.
/// Transport authentication does not upgrade the semi-honest MPC arithmetic
/// to malicious security.
pub mod transport;

/// Maximum canonical reveal-only equality transcript accepted at a process
/// boundary.  The current scalar equality circuits are far smaller; this is an
/// allocation/exhaustion ceiling, not a claim about a particular game shape.
pub const MAX_DECISION_TRANSCRIPT_BYTES: usize = 16 * 1024 * 1024;
const DECISION_TRANSCRIPT_MAGIC: &[u8; 8] = b"FHDTR001";
const DECISION_TRANSCRIPT_FIXED_BYTES: usize = 8 + 8 + 1 + 5 * 8;
const MASKED_OPENING_WIRE_BYTES: usize = 8 + 1 + 1;
/// Maximum protected Beaver-material custody accepted at a party process
/// boundary. This is secret preprocessing, never a coordinator artifact.
pub const MAX_TRIPLE_MATERIAL_BYTES: usize = 16 * 1024 * 1024;
const TRIPLE_MATERIAL_MAGIC: &[u8; 8] = b"FHTRI001";
const TRIPLE_MATERIAL_FIXED_BYTES: usize = 8 + 32 + 8 * 7 + 4 + 1;

/// Public circuit/session parameters. The nonce is a routing/replay-domain tag,
/// not an authenticator; a deployment must bind it to an authenticated roster.
/// Constructing a session records the protocol precondition that the honest
/// mod-t reconstruction of every curve coefficient is `< 2^value_bits`. The
/// circuit performs exact mod-t reduction but does not maliciously range-check
/// that upstream fold/wrap-bound promise before truncating to `value_bits`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartyMpcSession {
    nonce: [u8; 32],
    n_parties: usize,
    buckets: usize,
    value_bits: usize,
    plaintext_modulus: u64,
    quorum_timeout: Duration,
    circuit: CircuitKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CircuitKind {
    Crossing,
    Equality,
    LessThan,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SessionBinding {
    nonce: [u8; 32],
    n_parties: usize,
    buckets: usize,
    value_bits: usize,
    plaintext_modulus: u64,
    circuit: CircuitKind,
}

impl PartyMpcSession {
    pub fn new(
        nonce: [u8; 32],
        n_parties: usize,
        buckets: usize,
        value_bits: usize,
        plaintext_modulus: u64,
        quorum_timeout: Duration,
    ) -> Result<Self> {
        Self::new_for(
            nonce,
            n_parties,
            buckets,
            value_bits,
            plaintext_modulus,
            quorum_timeout,
            CircuitKind::Crossing,
        )
    }

    /// A scalar decision session. Each party supplies one mod-`t` additive
    /// share of a left and right operand; the circuit reconstructs neither and
    /// reveals only whether the two residues are equal.
    pub fn equality(
        nonce: [u8; 32],
        n_parties: usize,
        value_bits: usize,
        plaintext_modulus: u64,
        quorum_timeout: Duration,
    ) -> Result<Self> {
        Self::new_for(
            nonce,
            n_parties,
            1,
            value_bits,
            plaintext_modulus,
            quorum_timeout,
            CircuitKind::Equality,
        )
    }

    /// A scalar strict-comparison session. Each party supplies one mod-`t`
    /// additive share of the left and right operand; the circuit reveals only
    /// whether `left < right` over their declared canonical bit width.
    pub fn less_than(
        nonce: [u8; 32],
        n_parties: usize,
        value_bits: usize,
        plaintext_modulus: u64,
        quorum_timeout: Duration,
    ) -> Result<Self> {
        Self::new_for(
            nonce,
            n_parties,
            1,
            value_bits,
            plaintext_modulus,
            quorum_timeout,
            CircuitKind::LessThan,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn new_for(
        nonce: [u8; 32],
        n_parties: usize,
        buckets: usize,
        value_bits: usize,
        plaintext_modulus: u64,
        quorum_timeout: Duration,
        circuit: CircuitKind,
    ) -> Result<Self> {
        if n_parties < 2 {
            return Err(PartyMpcError::InvalidParameters(
                "distributed MPC requires at least two parties",
            ));
        }
        if buckets == 0 {
            return Err(PartyMpcError::InvalidParameters(
                "crossing requires at least one bucket",
            ));
        }
        if !(1..=63).contains(&value_bits) {
            return Err(PartyMpcError::InvalidParameters(
                "value width must be between 1 and 63 bits",
            ));
        }
        if plaintext_modulus < (1u64 << value_bits) {
            return Err(PartyMpcError::InvalidParameters(
                "plaintext modulus must cover the declared output range",
            ));
        }
        sum_width(n_parties, plaintext_modulus)?;
        if index_bits(buckets) > usize::BITS as usize {
            return Err(PartyMpcError::InvalidParameters(
                "bucket index does not fit usize",
            ));
        }
        if quorum_timeout.is_zero() {
            return Err(PartyMpcError::InvalidParameters(
                "quorum timeout must be non-zero",
            ));
        }
        let session = Self {
            nonce,
            n_parties,
            buckets,
            value_bits,
            plaintext_modulus,
            quorum_timeout,
            circuit,
        };
        exact_and_gates(&session)?;
        Ok(session)
    }

    pub fn nonce(&self) -> [u8; 32] {
        self.nonce
    }

    pub fn n_parties(&self) -> usize {
        self.n_parties
    }

    pub fn buckets(&self) -> usize {
        self.buckets
    }

    pub fn value_bits(&self) -> usize {
        self.value_bits
    }

    pub fn plaintext_modulus(&self) -> u64 {
        self.plaintext_modulus
    }

    pub fn ingress_bits(&self) -> usize {
        sum_width(self.n_parties, self.plaintext_modulus)
            .expect("validated arithmetic ingress shape")
    }

    pub fn exact_and_gates(&self) -> usize {
        // Construction validated the checked arithmetic.
        exact_and_gates(self).expect("validated session shape")
    }

    fn binding(&self) -> SessionBinding {
        SessionBinding {
            nonce: self.nonce,
            n_parties: self.n_parties,
            buckets: self.buckets,
            value_bits: self.value_bits,
            plaintext_modulus: self.plaintext_modulus,
            circuit: self.circuit,
        }
    }
}

/// Protocol phase named in quorum/ordering errors.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProtocolPhase {
    InputIngress,
    BeaverGate(usize),
    OutputReveal,
}

/// Fail-closed runtime errors. Authentication and malicious-share validity are
/// outside this runtime's stated scope; structural/session checks are not.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PartyMpcError {
    InvalidParameters(&'static str),
    ShapeMismatch,
    ValueOverflow {
        bucket: usize,
        value: u64,
        bits: usize,
    },
    SessionMismatch,
    PartyMismatch {
        material: usize,
        channel: usize,
    },
    DuplicateParty {
        party: usize,
        phase: ProtocolPhase,
    },
    InvalidParty {
        party: usize,
        n_parties: usize,
    },
    NonCanonicalBit,
    UnexpectedMessage {
        expected: ProtocolPhase,
    },
    QuorumTimeout {
        phase: ProtocolPhase,
        have: usize,
        need: usize,
    },
    ChannelClosed {
        phase: ProtocolPhase,
    },
    TripleExhausted,
    InvalidOutput,
    MalformedTranscriptWire,
    MalformedTripleMaterialWire,
    ArithmeticOverflow,
}

impl fmt::Display for PartyMpcError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "distributed MPC error: {self:?}")
    }
}

impl std::error::Error for PartyMpcError {}

pub type Result<T> = std::result::Result<T, PartyMpcError>;

#[derive(Clone, Copy)]
struct LocalTriple {
    a: u8,
    b: u8,
    c: u8,
}

/// Opaque party-owned arithmetic ingress. It is constructed from only this
/// party's two mod-`t` rows and independently generated sharing randomness. It
/// implements neither `Clone` nor `Debug` and exposes no share accessor.
pub struct PartyArithmeticInput {
    session: PartyMpcSession,
    party: usize,
    demand_by_recipient: Vec<Vec<Vec<u8>>>,
    supply_by_recipient: Vec<Vec<Vec<u8>>>,
}

/// Opaque scalar-equality ingress. Each party owns only its two local mod-`t`
/// additive shares; the wrapper prevents accidentally running those operands
/// through the crossing circuit (which reveals a volume).
pub struct PartyEqualityInput(PartyArithmeticInput);

/// Opaque scalar-comparison ingress. As with equality, each party owns only
/// its two local mod-`t` shares and exposes no operand accessor.
pub struct PartyComparisonInput(PartyArithmeticInput);

/// Opaque party-owned Beaver preprocessing. The trusted dealer that constructs
/// it receives only [`PartyMpcSession`], never an input row or aggregate curve.
pub struct TripleMaterial {
    session: PartyMpcSession,
    party: usize,
    triples: Vec<LocalTriple>,
}

impl TripleMaterial {
    /// Canonical protected custody for one party's trusted-dealer Beaver row.
    ///
    /// The wire binds the complete MPC session, party index, and exact gate
    /// count. It contains secret triple shares and must be handled like a key,
    /// never published or delivered to the coordinator.
    pub fn to_wire_bytes(&self) -> Result<Vec<u8>> {
        let encoded_len = TRIPLE_MATERIAL_FIXED_BYTES
            .checked_add(
                self.triples
                    .len()
                    .checked_mul(3)
                    .ok_or(PartyMpcError::ArithmeticOverflow)?,
            )
            .ok_or(PartyMpcError::ArithmeticOverflow)?;
        if encoded_len > MAX_TRIPLE_MATERIAL_BYTES
            || self.triples.len() != self.session.exact_and_gates()
            || self
                .triples
                .iter()
                .any(|triple| triple.a > 1 || triple.b > 1 || triple.c > 1)
        {
            return Err(PartyMpcError::MalformedTripleMaterialWire);
        }
        let mut out = Vec::with_capacity(encoded_len);
        out.extend_from_slice(TRIPLE_MATERIAL_MAGIC);
        out.extend_from_slice(&self.session.nonce);
        put_triple_usize(&mut out, self.session.n_parties)?;
        put_triple_usize(&mut out, self.session.buckets)?;
        put_triple_usize(&mut out, self.session.value_bits)?;
        out.extend_from_slice(&self.session.plaintext_modulus.to_be_bytes());
        out.extend_from_slice(&self.session.quorum_timeout.as_secs().to_be_bytes());
        out.extend_from_slice(&self.session.quorum_timeout.subsec_nanos().to_be_bytes());
        out.push(match self.session.circuit {
            CircuitKind::Crossing => 0,
            CircuitKind::Equality => 1,
            CircuitKind::LessThan => 2,
        });
        put_triple_usize(&mut out, self.party)?;
        put_triple_usize(&mut out, self.triples.len())?;
        for triple in &self.triples {
            out.extend_from_slice(&[triple.a, triple.b, triple.c]);
        }
        debug_assert_eq!(out.len(), encoded_len);
        Ok(out)
    }

    /// Strictly decode protected preprocessing for one expected session and
    /// party. A custody file cannot be replayed under a different timeout,
    /// circuit, nonce, shape, or party slot.
    pub fn from_wire_bytes(
        expected_session: &PartyMpcSession,
        expected_party: usize,
        bytes: &[u8],
    ) -> Result<Self> {
        if bytes.len() < TRIPLE_MATERIAL_FIXED_BYTES || bytes.len() > MAX_TRIPLE_MATERIAL_BYTES {
            return Err(PartyMpcError::MalformedTripleMaterialWire);
        }
        let mut input = TripleWireReader::new(bytes);
        if input.take(TRIPLE_MATERIAL_MAGIC.len())? != TRIPLE_MATERIAL_MAGIC {
            return Err(PartyMpcError::MalformedTripleMaterialWire);
        }
        let nonce: [u8; 32] = input
            .take(32)?
            .try_into()
            .map_err(|_| PartyMpcError::MalformedTripleMaterialWire)?;
        let n_parties = input.usize()?;
        let buckets = input.usize()?;
        let value_bits = input.usize()?;
        let plaintext_modulus = input.u64()?;
        let timeout_secs = input.u64()?;
        let timeout_nanos = input.u32()?;
        let circuit = match input.byte()? {
            0 => CircuitKind::Crossing,
            1 => CircuitKind::Equality,
            2 => CircuitKind::LessThan,
            _ => return Err(PartyMpcError::MalformedTripleMaterialWire),
        };
        let party = input.usize()?;
        let count = input.usize()?;
        let expected_len = TRIPLE_MATERIAL_FIXED_BYTES
            .checked_add(
                count
                    .checked_mul(3)
                    .ok_or(PartyMpcError::ArithmeticOverflow)?,
            )
            .ok_or(PartyMpcError::ArithmeticOverflow)?;
        if expected_len != bytes.len()
            || timeout_nanos >= 1_000_000_000
            || party != expected_party
            || party >= n_parties
        {
            return Err(PartyMpcError::MalformedTripleMaterialWire);
        }
        let session = PartyMpcSession::new_for(
            nonce,
            n_parties,
            buckets,
            value_bits,
            plaintext_modulus,
            Duration::new(timeout_secs, timeout_nanos),
            circuit,
        )
        .map_err(|_| PartyMpcError::MalformedTripleMaterialWire)?;
        if &session != expected_session || count != session.exact_and_gates() {
            return Err(PartyMpcError::SessionMismatch);
        }
        let mut triples = Vec::with_capacity(count);
        for _ in 0..count {
            let a = input.byte()?;
            let b = input.byte()?;
            let c = input.byte()?;
            if a > 1 || b > 1 || c > 1 {
                return Err(PartyMpcError::MalformedTripleMaterialWire);
            }
            triples.push(LocalTriple { a, b, c });
        }
        input.finish()?;
        let material = Self {
            session,
            party,
            triples,
        };
        if material.to_wire_bytes()? != bytes {
            return Err(PartyMpcError::MalformedTripleMaterialWire);
        }
        Ok(material)
    }
}

fn put_triple_usize(out: &mut Vec<u8>, value: usize) -> Result<()> {
    out.extend_from_slice(
        &u64::try_from(value)
            .map_err(|_| PartyMpcError::ArithmeticOverflow)?
            .to_be_bytes(),
    );
    Ok(())
}

struct TripleWireReader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> TripleWireReader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn take(&mut self, len: usize) -> Result<&'a [u8]> {
        let end = self
            .offset
            .checked_add(len)
            .filter(|end| *end <= self.bytes.len())
            .ok_or(PartyMpcError::MalformedTripleMaterialWire)?;
        let value = &self.bytes[self.offset..end];
        self.offset = end;
        Ok(value)
    }

    fn byte(&mut self) -> Result<u8> {
        Ok(self.take(1)?[0])
    }

    fn u32(&mut self) -> Result<u32> {
        Ok(u32::from_be_bytes(
            self.take(4)?
                .try_into()
                .map_err(|_| PartyMpcError::MalformedTripleMaterialWire)?,
        ))
    }

    fn u64(&mut self) -> Result<u64> {
        Ok(u64::from_be_bytes(
            self.take(8)?
                .try_into()
                .map_err(|_| PartyMpcError::MalformedTripleMaterialWire)?,
        ))
    }

    fn usize(&mut self) -> Result<usize> {
        usize::try_from(self.u64()?).map_err(|_| PartyMpcError::MalformedTripleMaterialWire)
    }

    fn finish(self) -> Result<()> {
        if self.offset == self.bytes.len() {
            Ok(())
        } else {
            Err(PartyMpcError::MalformedTripleMaterialWire)
        }
    }
}

/// One masked Beaver opening broadcast by the coordinator. Both bits are
/// one-time padded by a fresh triple and are safe public transcript fields in
/// the stated semi-honest/trusted-preprocessing model.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MaskedOpening {
    pub gate: usize,
    pub d: u8,
    pub e: u8,
}

/// Public transcript of a distributed run. Per-party submissions are counted,
/// not retained; the public message is the XOR-opened masked `(d,e)` pair.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DistributedTranscript {
    pub masked: Vec<MaskedOpening>,
    pub revealed_pstar: Vec<u8>,
    pub revealed_vstar: Vec<u8>,
    pub and_gates: usize,
    /// Actual channel opening rounds in this scalar-gate implementation.
    pub scalar_opening_rounds: usize,
    /// Dependency depth if independent same-depth gates are batched, including
    /// balanced A2B sums, exact mod-t reductions, and the crossing.
    pub modeled_batched_rounds: usize,
    pub gate_share_messages: usize,
    pub output_share_messages: usize,
}

impl DistributedTranscript {
    /// Strict reveal/schema tooth for the exact session shape.
    pub fn is_reveal_only(&self, session: &PartyMpcSession) -> bool {
        if session.circuit != CircuitKind::Crossing {
            return false;
        }
        let gates = session.exact_and_gates();
        let canonical = |bits: &[u8]| bits.iter().all(|&bit| bit <= 1);
        self.masked.len() == gates
            && self
                .masked
                .iter()
                .enumerate()
                .all(|(gate, opening)| opening.gate == gate && opening.d <= 1 && opening.e <= 1)
            && self.revealed_pstar.len() == index_bits(session.buckets)
            && self.revealed_vstar.len() == session.value_bits
            && canonical(&self.revealed_pstar)
            && canonical(&self.revealed_vstar)
            && self.and_gates == gates
            && self.scalar_opening_rounds == gates
            && self.modeled_batched_rounds == modeled_batched_rounds(session)
            && gates
                .checked_mul(session.n_parties)
                .is_some_and(|count| self.gate_share_messages == count)
            && self.output_share_messages == session.n_parties
    }
}

/// Public transcript for a scalar equality decision. The two operands and
/// their residues never appear; only Beaver-masked gate openings and one final
/// bit do.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DecisionTranscript {
    pub masked: Vec<MaskedOpening>,
    pub revealed_equal: u8,
    pub and_gates: usize,
    pub scalar_opening_rounds: usize,
    pub modeled_batched_rounds: usize,
    pub gate_share_messages: usize,
    pub output_share_messages: usize,
}

impl DecisionTranscript {
    pub fn is_reveal_only(&self, session: &PartyMpcSession) -> bool {
        if session.circuit != CircuitKind::Equality {
            return false;
        }
        let gates = session.exact_and_gates();
        self.masked.len() == gates
            && self
                .masked
                .iter()
                .enumerate()
                .all(|(gate, opening)| opening.gate == gate && opening.d <= 1 && opening.e <= 1)
            && self.revealed_equal <= 1
            && self.and_gates == gates
            && self.scalar_opening_rounds == gates
            && self.modeled_batched_rounds == modeled_batched_rounds(session)
            && gates
                .checked_mul(session.n_parties)
                .is_some_and(|count| self.gate_share_messages == count)
            && self.output_share_messages == session.n_parties
    }

    /// Canonical public transport for the reveal-only equality transcript.
    /// No operand, residue, Boolean share, or Beaver triple is present.
    pub fn to_wire_bytes(&self) -> Result<Vec<u8>> {
        if self.masked.len() != self.and_gates
            || self.scalar_opening_rounds != self.and_gates
            || self.revealed_equal > 1
            || self
                .masked
                .iter()
                .enumerate()
                .any(|(gate, opening)| opening.gate != gate || opening.d > 1 || opening.e > 1)
        {
            return Err(PartyMpcError::MalformedTranscriptWire);
        }
        let encoded_len = DECISION_TRANSCRIPT_FIXED_BYTES
            .checked_add(
                self.masked
                    .len()
                    .checked_mul(MASKED_OPENING_WIRE_BYTES)
                    .ok_or(PartyMpcError::ArithmeticOverflow)?,
            )
            .ok_or(PartyMpcError::ArithmeticOverflow)?;
        if encoded_len > MAX_DECISION_TRANSCRIPT_BYTES {
            return Err(PartyMpcError::MalformedTranscriptWire);
        }
        let mut out = Vec::with_capacity(encoded_len);
        out.extend_from_slice(DECISION_TRANSCRIPT_MAGIC);
        put_transcript_usize(&mut out, self.masked.len())?;
        for opening in &self.masked {
            put_transcript_usize(&mut out, opening.gate)?;
            out.push(opening.d);
            out.push(opening.e);
        }
        out.push(self.revealed_equal);
        put_transcript_usize(&mut out, self.and_gates)?;
        put_transcript_usize(&mut out, self.scalar_opening_rounds)?;
        put_transcript_usize(&mut out, self.modeled_batched_rounds)?;
        put_transcript_usize(&mut out, self.gate_share_messages)?;
        put_transcript_usize(&mut out, self.output_share_messages)?;
        debug_assert_eq!(out.len(), encoded_len);
        Ok(out)
    }

    /// Strict inverse of [`Self::to_wire_bytes`].  Exact circuit/session shape
    /// remains the relying party's job via [`Self::is_reveal_only`].
    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self> {
        if bytes.len() < DECISION_TRANSCRIPT_FIXED_BYTES
            || bytes.len() > MAX_DECISION_TRANSCRIPT_BYTES
        {
            return Err(PartyMpcError::MalformedTranscriptWire);
        }
        let mut input = TranscriptWireReader::new(bytes);
        if input.take(DECISION_TRANSCRIPT_MAGIC.len())? != DECISION_TRANSCRIPT_MAGIC {
            return Err(PartyMpcError::MalformedTranscriptWire);
        }
        let count = input.usize()?;
        let expected_len = DECISION_TRANSCRIPT_FIXED_BYTES
            .checked_add(
                count
                    .checked_mul(MASKED_OPENING_WIRE_BYTES)
                    .ok_or(PartyMpcError::ArithmeticOverflow)?,
            )
            .ok_or(PartyMpcError::ArithmeticOverflow)?;
        if expected_len != bytes.len() || expected_len > MAX_DECISION_TRANSCRIPT_BYTES {
            return Err(PartyMpcError::MalformedTranscriptWire);
        }
        let mut masked = Vec::with_capacity(count);
        for expected_gate in 0..count {
            let gate = input.usize()?;
            let d = input.byte()?;
            let e = input.byte()?;
            if gate != expected_gate || d > 1 || e > 1 {
                return Err(PartyMpcError::MalformedTranscriptWire);
            }
            masked.push(MaskedOpening { gate, d, e });
        }
        let revealed_equal = input.byte()?;
        let and_gates = input.usize()?;
        let scalar_opening_rounds = input.usize()?;
        let modeled_batched_rounds = input.usize()?;
        let gate_share_messages = input.usize()?;
        let output_share_messages = input.usize()?;
        input.finish()?;
        if revealed_equal > 1 || and_gates != count || scalar_opening_rounds != count {
            return Err(PartyMpcError::MalformedTranscriptWire);
        }
        let transcript = Self {
            masked,
            revealed_equal,
            and_gates,
            scalar_opening_rounds,
            modeled_batched_rounds,
            gate_share_messages,
            output_share_messages,
        };
        if transcript.to_wire_bytes()? != bytes {
            return Err(PartyMpcError::MalformedTranscriptWire);
        }
        Ok(transcript)
    }
}

fn put_transcript_usize(out: &mut Vec<u8>, value: usize) -> Result<()> {
    let value = u64::try_from(value).map_err(|_| PartyMpcError::ArithmeticOverflow)?;
    out.extend_from_slice(&value.to_be_bytes());
    Ok(())
}

struct TranscriptWireReader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> TranscriptWireReader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn take(&mut self, len: usize) -> Result<&'a [u8]> {
        let end = self
            .offset
            .checked_add(len)
            .filter(|end| *end <= self.bytes.len())
            .ok_or(PartyMpcError::MalformedTranscriptWire)?;
        let value = &self.bytes[self.offset..end];
        self.offset = end;
        Ok(value)
    }

    fn byte(&mut self) -> Result<u8> {
        Ok(self.take(1)?[0])
    }

    fn usize(&mut self) -> Result<usize> {
        let raw = u64::from_be_bytes(
            self.take(8)?
                .try_into()
                .map_err(|_| PartyMpcError::MalformedTranscriptWire)?,
        );
        usize::try_from(raw).map_err(|_| PartyMpcError::MalformedTranscriptWire)
    }

    fn finish(self) -> Result<()> {
        if self.offset == self.bytes.len() {
            Ok(())
        } else {
            Err(PartyMpcError::MalformedTranscriptWire)
        }
    }
}

/// Public transcript for a scalar strict comparison. Only Beaver-masked gate
/// openings and the final `left < right` bit are retained.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComparisonTranscript {
    pub masked: Vec<MaskedOpening>,
    pub revealed_less_than: u8,
    pub and_gates: usize,
    pub scalar_opening_rounds: usize,
    pub modeled_batched_rounds: usize,
    pub gate_share_messages: usize,
    pub output_share_messages: usize,
}

impl ComparisonTranscript {
    pub fn is_reveal_only(&self, session: &PartyMpcSession) -> bool {
        if session.circuit != CircuitKind::LessThan {
            return false;
        }
        let gates = session.exact_and_gates();
        self.masked.len() == gates
            && self
                .masked
                .iter()
                .enumerate()
                .all(|(gate, opening)| opening.gate == gate && opening.d <= 1 && opening.e <= 1)
            && self.revealed_less_than <= 1
            && self.and_gates == gates
            && self.scalar_opening_rounds == gates
            && self.modeled_batched_rounds == modeled_batched_rounds(session)
            && gates
                .checked_mul(session.n_parties)
                .is_some_and(|count| self.gate_share_messages == count)
            && self.output_share_messages == session.n_parties
    }
}

/// Coordinator result. No curve coefficient or Beaver mask is present.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DistributedRun {
    pub crossing: Crossing,
    pub transcript: DistributedTranscript,
}

/// Coordinator result for the scalar decision circuit. No operand, residue,
/// or bit decomposition is retained.
#[derive(Debug, PartialEq, Eq)]
pub struct DistributedDecisionRun {
    equal: bool,
    session_nonce: [u8; 32],
    pub transcript: DecisionTranscript,
}

impl DistributedDecisionRun {
    pub fn is_equal(&self) -> bool {
        self.equal
    }

    pub fn session_nonce(&self) -> [u8; 32] {
        self.session_nonce
    }
}

/// Coordinator result for strict comparison. No operand, residue, bit
/// decomposition, or difference is retained.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DistributedComparisonRun {
    less_than: bool,
    session_nonce: [u8; 32],
    pub transcript: ComparisonTranscript,
}

impl DistributedComparisonRun {
    pub fn is_less_than(&self) -> bool {
        self.less_than
    }

    pub fn session_nonce(&self) -> [u8; 32] {
        self.session_nonce
    }
}

/// Party completion report. A party never reconstructs the public result; it
/// sends its final shares and exits after consuming the expected gate schedule.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartyReport {
    pub party: usize,
    pub and_gates: usize,
    pub peer_input_messages_sent: usize,
    pub peer_input_messages_received: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CurveKind {
    Demand,
    Supply,
}

struct PeerInputMessage {
    session: SessionBinding,
    from: usize,
    to: usize,
    curve: CurveKind,
    bucket: usize,
    bits: Vec<u8>,
}

enum PartyMessage {
    GateShare {
        session: SessionBinding,
        party: usize,
        gate: usize,
        d: u8,
        e: u8,
    },
    OutputShare {
        session: SessionBinding,
        party: usize,
        pstar: Vec<u8>,
        vstar: Vec<u8>,
    },
    DecisionShare {
        session: SessionBinding,
        party: usize,
        equal: u8,
    },
    ComparisonShare {
        session: SessionBinding,
        party: usize,
        less_than: u8,
    },
}

enum CoordinatorMessage {
    GateOpened {
        session: SessionBinding,
        gate: usize,
        d: u8,
        e: u8,
    },
}

/// Opaque channel endpoint owned by exactly one party thread.
pub struct PartyChannels {
    party: usize,
    to_coordinator: Sender<PartyMessage>,
    from_coordinator: Receiver<CoordinatorMessage>,
    to_peers: Vec<Sender<PeerInputMessage>>,
    from_peers: Receiver<PeerInputMessage>,
}

/// Opaque coordinator router. It has no API for party material or input shares.
pub struct CoordinatorChannels {
    from_parties: Receiver<PartyMessage>,
    to_parties: Vec<Sender<CoordinatorMessage>>,
}

/// Construct unauthenticated in-process channels for the session roster.
pub fn local_channels(session: &PartyMpcSession) -> (CoordinatorChannels, Vec<PartyChannels>) {
    let (party_tx, party_rx) = mpsc::channel();
    let mut peer_txs = Vec::with_capacity(session.n_parties);
    let mut peer_rxs = Vec::with_capacity(session.n_parties);
    for _ in 0..session.n_parties {
        let (peer_tx, peer_rx) = mpsc::channel();
        peer_txs.push(peer_tx);
        peer_rxs.push(Some(peer_rx));
    }
    let mut coordinator_txs = Vec::with_capacity(session.n_parties);
    let mut parties = Vec::with_capacity(session.n_parties);
    for party in 0..session.n_parties {
        let (coordinator_tx, coordinator_rx) = mpsc::channel();
        coordinator_txs.push(coordinator_tx);
        parties.push(PartyChannels {
            party,
            to_coordinator: party_tx.clone(),
            from_coordinator: coordinator_rx,
            to_peers: peer_txs.clone(),
            from_peers: peer_rxs[party].take().expect("one peer receiver per party"),
        });
    }
    drop(party_tx);
    (
        CoordinatorChannels {
            from_parties: party_rx,
            to_parties: coordinator_txs,
        },
        parties,
    )
}

impl PartyArithmeticInput {
    /// Prepare peer-distributed boolean ingress from only this party's local
    /// mod-`t` rows. No trusted dealer or coordinator receives these values.
    pub fn new<R: Rng>(
        session: &PartyMpcSession,
        party: usize,
        demand_mod_t: &[u64],
        supply_mod_t: &[u64],
        rng: &mut R,
    ) -> Result<Self> {
        if session.circuit != CircuitKind::Crossing {
            return Err(PartyMpcError::SessionMismatch);
        }
        Self::prepare(session, party, demand_mod_t, supply_mod_t, rng)
    }

    fn prepare<R: Rng>(
        session: &PartyMpcSession,
        party: usize,
        demand_mod_t: &[u64],
        supply_mod_t: &[u64],
        rng: &mut R,
    ) -> Result<Self> {
        if party >= session.n_parties {
            return Err(PartyMpcError::InvalidParty {
                party,
                n_parties: session.n_parties,
            });
        }
        if demand_mod_t.len() != session.buckets || supply_mod_t.len() != session.buckets {
            return Err(PartyMpcError::ShapeMismatch);
        }
        for (bucket, &value) in demand_mod_t.iter().chain(supply_mod_t).enumerate() {
            if value >= session.plaintext_modulus {
                return Err(PartyMpcError::ValueOverflow {
                    bucket: bucket % session.buckets,
                    value,
                    bits: session.ingress_bits(),
                });
            }
        }
        let w = session.ingress_bits();
        let demand_by_recipient = demand_mod_t
            .iter()
            .map(|&value| split_int(value, w, session.n_parties, rng))
            .collect();
        let supply_by_recipient = supply_mod_t
            .iter()
            .map(|&value| split_int(value, w, session.n_parties, rng))
            .collect();
        Ok(Self {
            session: session.clone(),
            party,
            demand_by_recipient,
            supply_by_recipient,
        })
    }
}

impl PartyEqualityInput {
    /// Prepare direct-peer boolean ingress from this party's local shares of
    /// two scalar operands. The public target `k` is represented canonically
    /// by giving party zero share `k` and every other party share zero.
    pub fn new<R: Rng>(
        session: &PartyMpcSession,
        party: usize,
        left_mod_t_share: u64,
        right_mod_t_share: u64,
        rng: &mut R,
    ) -> Result<Self> {
        if session.circuit != CircuitKind::Equality {
            return Err(PartyMpcError::SessionMismatch);
        }
        PartyArithmeticInput::prepare(
            session,
            party,
            &[left_mod_t_share],
            &[right_mod_t_share],
            rng,
        )
        .map(Self)
    }
}

impl PartyComparisonInput {
    /// Prepare direct-peer boolean ingress for a strict comparison of two
    /// secret-shared canonical integers.
    pub fn new<R: Rng>(
        session: &PartyMpcSession,
        party: usize,
        left_mod_t_share: u64,
        right_mod_t_share: u64,
        rng: &mut R,
    ) -> Result<Self> {
        if session.circuit != CircuitKind::LessThan {
            return Err(PartyMpcError::SessionMismatch);
        }
        PartyArithmeticInput::prepare(
            session,
            party,
            &[left_mod_t_share],
            &[right_mod_t_share],
            rng,
        )
        .map(Self)
    }
}

/// Trusted Beaver-triple preprocessing over public shape only. This function's
/// signature makes an aggregate curve or party input row unnameable.
pub fn trusted_dealer_triples<R: Rng>(
    session: &PartyMpcSession,
    rng: &mut R,
) -> Result<Vec<TripleMaterial>> {
    let n = session.n_parties;
    let gates = session.exact_and_gates();
    let mut triples = (0..n)
        .map(|_| Vec::with_capacity(gates))
        .collect::<Vec<_>>();
    for _ in 0..gates {
        let a = rng.gen_range(0..=1);
        let b_clear = rng.gen_range(0..=1);
        let a_shares = split_bit(a, n, rng);
        let b_shares = split_bit(b_clear, n, rng);
        let c_shares = split_bit(a & b_clear, n, rng);
        for party in 0..n {
            triples[party].push(LocalTriple {
                a: a_shares[party],
                b: b_shares[party],
                c: c_shares[party],
            });
        }
    }

    Ok((0..n)
        .map(|party| TripleMaterial {
            session: session.clone(),
            party,
            triples: std::mem::take(&mut triples[party]),
        })
        .collect())
}

/// Execute one party's circuit. This function reconstructs neither input nor
/// output; all secret state remains in this call until it is dropped.
pub fn run_party(
    input: PartyArithmeticInput,
    preprocessing: TripleMaterial,
    channels: PartyChannels,
) -> Result<PartyReport> {
    if input.session.circuit != CircuitKind::Crossing {
        return Err(PartyMpcError::SessionMismatch);
    }
    if input.session != preprocessing.session {
        return Err(PartyMpcError::SessionMismatch);
    }
    if input.party != preprocessing.party {
        return Err(PartyMpcError::PartyMismatch {
            material: input.party,
            channel: preprocessing.party,
        });
    }
    if input.party != channels.party {
        return Err(PartyMpcError::PartyMismatch {
            material: input.party,
            channel: channels.party,
        });
    }
    let PartyArithmeticInput {
        session,
        party,
        demand_by_recipient,
        supply_by_recipient,
    } = input;
    let TripleMaterial { triples, .. } = preprocessing;
    let (demand_sources, supply_sources, peer_messages) = exchange_arithmetic_ingress(
        &session,
        party,
        demand_by_recipient,
        supply_by_recipient,
        &channels,
    )?;
    let mut engine = LocalEngine {
        session: &session,
        party,
        channels,
        triples,
        next_gate: 0,
    };

    let mut level = Vec::with_capacity(session.buckets);
    let idx_bits = index_bits(session.buckets);
    for bucket in 0..session.buckets {
        let demand = reduce_mod_t_local(&demand_sources[bucket], &mut engine)?;
        let supply = reduce_mod_t_local(&supply_sources[bucket], &mut engine)?;
        let volume = secure_min_local(&demand, &supply, &mut engine)?;
        let index = local_const_int(bucket, idx_bits, party);
        level.push((volume, index));
    }

    while level.len() > 1 {
        let mut next = Vec::with_capacity((level.len() + 1) / 2);
        let mut candidates = level.into_iter();
        while let Some(left) = candidates.next() {
            if let Some(right) = candidates.next() {
                let left_wins = geq_local(&left.0, &right.0, &mut engine)?;
                let value = select_local(&left_wins, &left.0, &right.0, &mut engine)?;
                let index = select_local(&left_wins, &left.1, &right.1, &mut engine)?;
                next.push((value, index));
            } else {
                next.push(left);
            }
        }
        level = next;
    }

    let (vstar, pstar) = level.pop().expect("validated non-empty circuit");
    if engine.next_gate != session.exact_and_gates() {
        return Err(PartyMpcError::UnexpectedMessage {
            expected: ProtocolPhase::OutputReveal,
        });
    }
    engine
        .channels
        .to_coordinator
        .send(PartyMessage::OutputShare {
            session: session.binding(),
            party,
            pstar,
            vstar,
        })
        .map_err(|_| PartyMpcError::ChannelClosed {
            phase: ProtocolPhase::OutputReveal,
        })?;
    Ok(PartyReport {
        party,
        and_gates: engine.next_gate,
        peer_input_messages_sent: peer_messages,
        peer_input_messages_received: peer_messages,
    })
}

/// Execute one party's scalar equality circuit. The party sends exactly one
/// final XOR share; only the coordinator can reconstruct the decision after a
/// full quorum, and no operand is opened.
pub fn run_party_equality(
    input: PartyEqualityInput,
    preprocessing: TripleMaterial,
    channels: PartyChannels,
) -> Result<PartyReport> {
    let PartyEqualityInput(input) = input;
    if input.session.circuit != CircuitKind::Equality {
        return Err(PartyMpcError::SessionMismatch);
    }
    if input.session != preprocessing.session {
        return Err(PartyMpcError::SessionMismatch);
    }
    if input.party != preprocessing.party {
        return Err(PartyMpcError::PartyMismatch {
            material: input.party,
            channel: preprocessing.party,
        });
    }
    if input.party != channels.party {
        return Err(PartyMpcError::PartyMismatch {
            material: input.party,
            channel: channels.party,
        });
    }
    let PartyArithmeticInput {
        session,
        party,
        demand_by_recipient: left_by_recipient,
        supply_by_recipient: right_by_recipient,
    } = input;
    let TripleMaterial { triples, .. } = preprocessing;
    let (left_sources, right_sources, peer_messages) = exchange_arithmetic_ingress(
        &session,
        party,
        left_by_recipient,
        right_by_recipient,
        &channels,
    )?;
    if left_sources.len() != 1 || right_sources.len() != 1 {
        return Err(PartyMpcError::ShapeMismatch);
    }
    let mut engine = LocalEngine {
        session: &session,
        party,
        channels,
        triples,
        next_gate: 0,
    };
    let left = reduce_mod_t_local(&left_sources[0], &mut engine)?;
    let right = reduce_mod_t_local(&right_sources[0], &mut engine)?;
    let equal = equal_local(&left, &right, &mut engine)?;
    if engine.next_gate != session.exact_and_gates() {
        return Err(PartyMpcError::UnexpectedMessage {
            expected: ProtocolPhase::OutputReveal,
        });
    }
    engine
        .channels
        .to_coordinator
        .send(PartyMessage::DecisionShare {
            session: session.binding(),
            party,
            equal,
        })
        .map_err(|_| PartyMpcError::ChannelClosed {
            phase: ProtocolPhase::OutputReveal,
        })?;
    Ok(PartyReport {
        party,
        and_gates: engine.next_gate,
        peer_input_messages_sent: peer_messages,
        peer_input_messages_received: peer_messages,
    })
}

/// Execute one party's strict-comparison circuit. The only reconstructed value
/// is the final `left < right` bit after a full quorum.
pub fn run_party_comparison(
    input: PartyComparisonInput,
    preprocessing: TripleMaterial,
    channels: PartyChannels,
) -> Result<PartyReport> {
    let PartyComparisonInput(input) = input;
    if input.session.circuit != CircuitKind::LessThan {
        return Err(PartyMpcError::SessionMismatch);
    }
    if input.session != preprocessing.session {
        return Err(PartyMpcError::SessionMismatch);
    }
    if input.party != preprocessing.party {
        return Err(PartyMpcError::PartyMismatch {
            material: input.party,
            channel: preprocessing.party,
        });
    }
    if input.party != channels.party {
        return Err(PartyMpcError::PartyMismatch {
            material: input.party,
            channel: channels.party,
        });
    }
    let PartyArithmeticInput {
        session,
        party,
        demand_by_recipient: left_by_recipient,
        supply_by_recipient: right_by_recipient,
    } = input;
    let TripleMaterial { triples, .. } = preprocessing;
    let (left_sources, right_sources, peer_messages) = exchange_arithmetic_ingress(
        &session,
        party,
        left_by_recipient,
        right_by_recipient,
        &channels,
    )?;
    if left_sources.len() != 1 || right_sources.len() != 1 {
        return Err(PartyMpcError::ShapeMismatch);
    }
    let mut engine = LocalEngine {
        session: &session,
        party,
        channels,
        triples,
        next_gate: 0,
    };
    let left = reduce_mod_t_local(&left_sources[0], &mut engine)?;
    let right = reduce_mod_t_local(&right_sources[0], &mut engine)?;
    let greater_or_equal = geq_local(&left, &right, &mut engine)?;
    let less_than = greater_or_equal ^ local_const(1, party);
    if engine.next_gate != session.exact_and_gates() {
        return Err(PartyMpcError::UnexpectedMessage {
            expected: ProtocolPhase::OutputReveal,
        });
    }
    engine
        .channels
        .to_coordinator
        .send(PartyMessage::ComparisonShare {
            session: session.binding(),
            party,
            less_than,
        })
        .map_err(|_| PartyMpcError::ChannelClosed {
            phase: ProtocolPhase::OutputReveal,
        })?;
    Ok(PartyReport {
        party,
        and_gates: engine.next_gate,
        peer_input_messages_sent: peer_messages,
        peer_input_messages_received: peer_messages,
    })
}

impl CoordinatorChannels {
    /// Route a complete full-quorum run and reconstruct only `(p*, V*)`.
    pub fn coordinate(self, session: &PartyMpcSession) -> Result<DistributedRun> {
        if session.circuit != CircuitKind::Crossing {
            return Err(PartyMpcError::SessionMismatch);
        }
        if self.to_parties.len() != session.n_parties {
            return Err(PartyMpcError::ShapeMismatch);
        }
        let gates = session.exact_and_gates();
        let mut masked = Vec::with_capacity(gates);
        for gate in 0..gates {
            let phase = ProtocolPhase::BeaverGate(gate);
            let deadline = Instant::now()
                .checked_add(session.quorum_timeout)
                .ok_or(PartyMpcError::ArithmeticOverflow)?;
            let mut seen = vec![false; session.n_parties];
            let mut d = 0u8;
            let mut e = 0u8;
            let mut have = 0usize;
            while have < session.n_parties {
                let message =
                    recv_before(&self.from_parties, deadline, phase, have, session.n_parties)?;
                let PartyMessage::GateShare {
                    session: message_session,
                    party,
                    gate: message_gate,
                    d: d_share,
                    e: e_share,
                } = message
                else {
                    return Err(PartyMpcError::UnexpectedMessage { expected: phase });
                };
                validate_message_header(session, message_session, party)?;
                if message_gate != gate {
                    return Err(PartyMpcError::UnexpectedMessage { expected: phase });
                }
                if d_share > 1 || e_share > 1 {
                    return Err(PartyMpcError::NonCanonicalBit);
                }
                if std::mem::replace(&mut seen[party], true) {
                    return Err(PartyMpcError::DuplicateParty { party, phase });
                }
                d ^= d_share;
                e ^= e_share;
                have += 1;
            }
            masked.push(MaskedOpening { gate, d, e });
            for sender in &self.to_parties {
                sender
                    .send(CoordinatorMessage::GateOpened {
                        session: session.binding(),
                        gate,
                        d,
                        e,
                    })
                    .map_err(|_| PartyMpcError::ChannelClosed { phase })?;
            }
        }

        let phase = ProtocolPhase::OutputReveal;
        let deadline = Instant::now()
            .checked_add(session.quorum_timeout)
            .ok_or(PartyMpcError::ArithmeticOverflow)?;
        let p_bits = index_bits(session.buckets);
        let mut pstar = vec![0u8; p_bits];
        let mut vstar = vec![0u8; session.value_bits];
        let mut seen = vec![false; session.n_parties];
        let mut have = 0usize;
        while have < session.n_parties {
            let message =
                recv_before(&self.from_parties, deadline, phase, have, session.n_parties)?;
            let PartyMessage::OutputShare {
                session: message_session,
                party,
                pstar: p_share,
                vstar: v_share,
            } = message
            else {
                return Err(PartyMpcError::UnexpectedMessage { expected: phase });
            };
            validate_message_header(session, message_session, party)?;
            if std::mem::replace(&mut seen[party], true) {
                return Err(PartyMpcError::DuplicateParty { party, phase });
            }
            if p_share.len() != p_bits
                || v_share.len() != session.value_bits
                || p_share.iter().chain(&v_share).any(|&bit| bit > 1)
            {
                return Err(PartyMpcError::InvalidOutput);
            }
            for (out, share) in pstar.iter_mut().zip(p_share) {
                *out ^= share;
            }
            for (out, share) in vstar.iter_mut().zip(v_share) {
                *out ^= share;
            }
            have += 1;
        }

        let index = decode_bits(&pstar)? as usize;
        let volume = decode_bits(&vstar)?;
        if index >= session.buckets || (volume == 0 && index != 0) {
            return Err(PartyMpcError::InvalidOutput);
        }
        let crossing = Crossing {
            p_star: (volume != 0).then_some(index),
            v_star: volume,
        };
        let transcript = DistributedTranscript {
            masked,
            revealed_pstar: pstar,
            revealed_vstar: vstar,
            and_gates: gates,
            scalar_opening_rounds: gates,
            modeled_batched_rounds: modeled_batched_rounds(session),
            gate_share_messages: gates
                .checked_mul(session.n_parties)
                .ok_or(PartyMpcError::ArithmeticOverflow)?,
            output_share_messages: session.n_parties,
        };
        if !transcript.is_reveal_only(session) {
            return Err(PartyMpcError::InvalidOutput);
        }
        Ok(DistributedRun {
            crossing,
            transcript,
        })
    }

    /// Route a complete scalar-decision run and reconstruct one equality bit.
    /// The coordinator has no endpoint for either party-owned operand share.
    pub fn coordinate_equality(self, session: &PartyMpcSession) -> Result<DistributedDecisionRun> {
        if session.circuit != CircuitKind::Equality {
            return Err(PartyMpcError::SessionMismatch);
        }
        if self.to_parties.len() != session.n_parties {
            return Err(PartyMpcError::ShapeMismatch);
        }
        let gates = session.exact_and_gates();
        let mut masked = Vec::with_capacity(gates);
        for gate in 0..gates {
            let phase = ProtocolPhase::BeaverGate(gate);
            let deadline = Instant::now()
                .checked_add(session.quorum_timeout)
                .ok_or(PartyMpcError::ArithmeticOverflow)?;
            let mut seen = vec![false; session.n_parties];
            let mut d = 0u8;
            let mut e = 0u8;
            let mut have = 0usize;
            while have < session.n_parties {
                let message =
                    recv_before(&self.from_parties, deadline, phase, have, session.n_parties)?;
                let PartyMessage::GateShare {
                    session: message_session,
                    party,
                    gate: message_gate,
                    d: d_share,
                    e: e_share,
                } = message
                else {
                    return Err(PartyMpcError::UnexpectedMessage { expected: phase });
                };
                validate_message_header(session, message_session, party)?;
                if message_gate != gate {
                    return Err(PartyMpcError::UnexpectedMessage { expected: phase });
                }
                if d_share > 1 || e_share > 1 {
                    return Err(PartyMpcError::NonCanonicalBit);
                }
                if std::mem::replace(&mut seen[party], true) {
                    return Err(PartyMpcError::DuplicateParty { party, phase });
                }
                d ^= d_share;
                e ^= e_share;
                have += 1;
            }
            masked.push(MaskedOpening { gate, d, e });
            for sender in &self.to_parties {
                sender
                    .send(CoordinatorMessage::GateOpened {
                        session: session.binding(),
                        gate,
                        d,
                        e,
                    })
                    .map_err(|_| PartyMpcError::ChannelClosed { phase })?;
            }
        }

        let phase = ProtocolPhase::OutputReveal;
        let deadline = Instant::now()
            .checked_add(session.quorum_timeout)
            .ok_or(PartyMpcError::ArithmeticOverflow)?;
        let mut equal = 0u8;
        let mut seen = vec![false; session.n_parties];
        let mut have = 0usize;
        while have < session.n_parties {
            let message =
                recv_before(&self.from_parties, deadline, phase, have, session.n_parties)?;
            let PartyMessage::DecisionShare {
                session: message_session,
                party,
                equal: share,
            } = message
            else {
                return Err(PartyMpcError::UnexpectedMessage { expected: phase });
            };
            validate_message_header(session, message_session, party)?;
            if std::mem::replace(&mut seen[party], true) {
                return Err(PartyMpcError::DuplicateParty { party, phase });
            }
            if share > 1 {
                return Err(PartyMpcError::InvalidOutput);
            }
            equal ^= share;
            have += 1;
        }

        let transcript = DecisionTranscript {
            masked,
            revealed_equal: equal,
            and_gates: gates,
            scalar_opening_rounds: gates,
            modeled_batched_rounds: modeled_batched_rounds(session),
            gate_share_messages: gates
                .checked_mul(session.n_parties)
                .ok_or(PartyMpcError::ArithmeticOverflow)?,
            output_share_messages: session.n_parties,
        };
        if !transcript.is_reveal_only(session) {
            return Err(PartyMpcError::InvalidOutput);
        }
        Ok(DistributedDecisionRun {
            equal: equal == 1,
            session_nonce: session.nonce,
            transcript,
        })
    }

    /// Route a complete strict-comparison run and reconstruct only the
    /// `left < right` bit. The coordinator has no operand-share endpoint.
    pub fn coordinate_comparison(
        self,
        session: &PartyMpcSession,
    ) -> Result<DistributedComparisonRun> {
        if session.circuit != CircuitKind::LessThan {
            return Err(PartyMpcError::SessionMismatch);
        }
        if self.to_parties.len() != session.n_parties {
            return Err(PartyMpcError::ShapeMismatch);
        }
        let gates = session.exact_and_gates();
        let mut masked = Vec::with_capacity(gates);
        for gate in 0..gates {
            let phase = ProtocolPhase::BeaverGate(gate);
            let deadline = Instant::now()
                .checked_add(session.quorum_timeout)
                .ok_or(PartyMpcError::ArithmeticOverflow)?;
            let mut seen = vec![false; session.n_parties];
            let mut d = 0u8;
            let mut e = 0u8;
            let mut have = 0usize;
            while have < session.n_parties {
                let message =
                    recv_before(&self.from_parties, deadline, phase, have, session.n_parties)?;
                let PartyMessage::GateShare {
                    session: message_session,
                    party,
                    gate: message_gate,
                    d: d_share,
                    e: e_share,
                } = message
                else {
                    return Err(PartyMpcError::UnexpectedMessage { expected: phase });
                };
                validate_message_header(session, message_session, party)?;
                if message_gate != gate {
                    return Err(PartyMpcError::UnexpectedMessage { expected: phase });
                }
                if d_share > 1 || e_share > 1 {
                    return Err(PartyMpcError::NonCanonicalBit);
                }
                if std::mem::replace(&mut seen[party], true) {
                    return Err(PartyMpcError::DuplicateParty { party, phase });
                }
                d ^= d_share;
                e ^= e_share;
                have += 1;
            }
            masked.push(MaskedOpening { gate, d, e });
            for sender in &self.to_parties {
                sender
                    .send(CoordinatorMessage::GateOpened {
                        session: session.binding(),
                        gate,
                        d,
                        e,
                    })
                    .map_err(|_| PartyMpcError::ChannelClosed { phase })?;
            }
        }

        let phase = ProtocolPhase::OutputReveal;
        let deadline = Instant::now()
            .checked_add(session.quorum_timeout)
            .ok_or(PartyMpcError::ArithmeticOverflow)?;
        let mut less_than = 0u8;
        let mut seen = vec![false; session.n_parties];
        let mut have = 0usize;
        while have < session.n_parties {
            let message =
                recv_before(&self.from_parties, deadline, phase, have, session.n_parties)?;
            let PartyMessage::ComparisonShare {
                session: message_session,
                party,
                less_than: share,
            } = message
            else {
                return Err(PartyMpcError::UnexpectedMessage { expected: phase });
            };
            validate_message_header(session, message_session, party)?;
            if std::mem::replace(&mut seen[party], true) {
                return Err(PartyMpcError::DuplicateParty { party, phase });
            }
            if share > 1 {
                return Err(PartyMpcError::InvalidOutput);
            }
            less_than ^= share;
            have += 1;
        }

        let transcript = ComparisonTranscript {
            masked,
            revealed_less_than: less_than,
            and_gates: gates,
            scalar_opening_rounds: gates,
            modeled_batched_rounds: modeled_batched_rounds(session),
            gate_share_messages: gates
                .checked_mul(session.n_parties)
                .ok_or(PartyMpcError::ArithmeticOverflow)?,
            output_share_messages: session.n_parties,
        };
        if !transcript.is_reveal_only(session) {
            return Err(PartyMpcError::InvalidOutput);
        }
        Ok(DistributedComparisonRun {
            less_than: less_than == 1,
            session_nonce: session.nonce,
            transcript,
        })
    }
}

/// Simulate the public broadcast transcript from only the intended output and
/// public circuit shape. This does not claim to simulate authenticated transport,
/// malicious behavior, or a corrupted party's retained local state.
pub fn simulate_public_transcript<R: Rng>(
    crossing: &Crossing,
    session: &PartyMpcSession,
    rng: &mut R,
) -> Result<DistributedTranscript> {
    if session.circuit != CircuitKind::Crossing {
        return Err(PartyMpcError::SessionMismatch);
    }
    let gates = session.exact_and_gates();
    let masked = (0..gates)
        .map(|gate| MaskedOpening {
            gate,
            d: rng.gen_range(0..=1),
            e: rng.gen_range(0..=1),
        })
        .collect();
    let index = crossing.p_star.unwrap_or(0);
    if index >= session.buckets
        || crossing.p_star.is_some() != (crossing.v_star != 0)
        || (session.value_bits < 64 && crossing.v_star >= (1u64 << session.value_bits))
    {
        return Err(PartyMpcError::InvalidOutput);
    }
    let transcript = DistributedTranscript {
        masked,
        revealed_pstar: encode_bits(index as u64, index_bits(session.buckets)),
        revealed_vstar: encode_bits(crossing.v_star, session.value_bits),
        and_gates: gates,
        scalar_opening_rounds: gates,
        modeled_batched_rounds: modeled_batched_rounds(session),
        gate_share_messages: gates
            .checked_mul(session.n_parties)
            .ok_or(PartyMpcError::ArithmeticOverflow)?,
        output_share_messages: session.n_parties,
    };
    Ok(transcript)
}

/// Simulate the public scalar-decision transcript from only the intended bit
/// and public circuit shape. This is the same semi-honest simulation claim as
/// [`simulate_public_transcript`].
pub fn simulate_decision_transcript<R: Rng>(
    equal: bool,
    session: &PartyMpcSession,
    rng: &mut R,
) -> Result<DecisionTranscript> {
    if session.circuit != CircuitKind::Equality {
        return Err(PartyMpcError::SessionMismatch);
    }
    let gates = session.exact_and_gates();
    let transcript = DecisionTranscript {
        masked: (0..gates)
            .map(|gate| MaskedOpening {
                gate,
                d: rng.gen_range(0..=1),
                e: rng.gen_range(0..=1),
            })
            .collect(),
        revealed_equal: u8::from(equal),
        and_gates: gates,
        scalar_opening_rounds: gates,
        modeled_batched_rounds: modeled_batched_rounds(session),
        gate_share_messages: gates
            .checked_mul(session.n_parties)
            .ok_or(PartyMpcError::ArithmeticOverflow)?,
        output_share_messages: session.n_parties,
    };
    if !transcript.is_reveal_only(session) {
        return Err(PartyMpcError::InvalidOutput);
    }
    Ok(transcript)
}

/// Simulate the public comparison transcript from only the intended bit and
/// public circuit shape, under the same semi-honest claim as the equality
/// simulator.
pub fn simulate_comparison_transcript<R: Rng>(
    less_than: bool,
    session: &PartyMpcSession,
    rng: &mut R,
) -> Result<ComparisonTranscript> {
    if session.circuit != CircuitKind::LessThan {
        return Err(PartyMpcError::SessionMismatch);
    }
    let gates = session.exact_and_gates();
    let transcript = ComparisonTranscript {
        masked: (0..gates)
            .map(|gate| MaskedOpening {
                gate,
                d: rng.gen_range(0..=1),
                e: rng.gen_range(0..=1),
            })
            .collect(),
        revealed_less_than: u8::from(less_than),
        and_gates: gates,
        scalar_opening_rounds: gates,
        modeled_batched_rounds: modeled_batched_rounds(session),
        gate_share_messages: gates
            .checked_mul(session.n_parties)
            .ok_or(PartyMpcError::ArithmeticOverflow)?,
        output_share_messages: session.n_parties,
    };
    if !transcript.is_reveal_only(session) {
        return Err(PartyMpcError::InvalidOutput);
    }
    Ok(transcript)
}

type LocalSourceInts = Vec<Vec<Vec<u8>>>;

/// Direct peer ingress: every source party XOR-shares each bit of each local
/// mod-t arithmetic share independently to all recipients. The coordinator has
/// no peer-channel endpoint and therefore cannot collect these boolean shares.
fn exchange_arithmetic_ingress(
    session: &PartyMpcSession,
    party: usize,
    demand_by_recipient: Vec<Vec<Vec<u8>>>,
    supply_by_recipient: Vec<Vec<Vec<u8>>>,
    channels: &PartyChannels,
) -> Result<(LocalSourceInts, LocalSourceInts, usize)> {
    let expected = 2usize
        .checked_mul(session.buckets)
        .and_then(|count| count.checked_mul(session.n_parties))
        .ok_or(PartyMpcError::ArithmeticOverflow)?;
    let send_curve = |curve: CurveKind, rows: Vec<Vec<Vec<u8>>>| -> Result<()> {
        if rows.len() != session.buckets {
            return Err(PartyMpcError::ShapeMismatch);
        }
        for (bucket, recipients) in rows.into_iter().enumerate() {
            if recipients.len() != session.n_parties {
                return Err(PartyMpcError::ShapeMismatch);
            }
            for (to, bits) in recipients.into_iter().enumerate() {
                channels.to_peers[to]
                    .send(PeerInputMessage {
                        session: session.binding(),
                        from: party,
                        to,
                        curve,
                        bucket,
                        bits,
                    })
                    .map_err(|_| PartyMpcError::ChannelClosed {
                        phase: ProtocolPhase::InputIngress,
                    })?;
            }
        }
        Ok(())
    };
    send_curve(CurveKind::Demand, demand_by_recipient)?;
    send_curve(CurveKind::Supply, supply_by_recipient)?;

    let mut demand = vec![vec![None; session.n_parties]; session.buckets];
    let mut supply = vec![vec![None; session.n_parties]; session.buckets];
    let deadline = Instant::now()
        .checked_add(session.quorum_timeout.saturating_mul(2))
        .ok_or(PartyMpcError::ArithmeticOverflow)?;
    for received in 0..expected {
        let remaining = deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            return Err(PartyMpcError::QuorumTimeout {
                phase: ProtocolPhase::InputIngress,
                have: received,
                need: expected,
            });
        }
        let message = channels
            .from_peers
            .recv_timeout(remaining)
            .map_err(|error| match error {
                RecvTimeoutError::Timeout => PartyMpcError::QuorumTimeout {
                    phase: ProtocolPhase::InputIngress,
                    have: received,
                    need: expected,
                },
                RecvTimeoutError::Disconnected => PartyMpcError::ChannelClosed {
                    phase: ProtocolPhase::InputIngress,
                },
            })?;
        if message.session != session.binding() {
            return Err(PartyMpcError::SessionMismatch);
        }
        if message.from >= session.n_parties {
            return Err(PartyMpcError::InvalidParty {
                party: message.from,
                n_parties: session.n_parties,
            });
        }
        if message.to != party {
            return Err(PartyMpcError::UnexpectedMessage {
                expected: ProtocolPhase::InputIngress,
            });
        }
        if message.bucket >= session.buckets
            || message.bits.len() != session.ingress_bits()
            || message.bits.iter().any(|&bit| bit > 1)
        {
            return Err(PartyMpcError::ShapeMismatch);
        }
        let slot = match message.curve {
            CurveKind::Demand => &mut demand[message.bucket][message.from],
            CurveKind::Supply => &mut supply[message.bucket][message.from],
        };
        if slot.replace(message.bits).is_some() {
            return Err(PartyMpcError::DuplicateParty {
                party: message.from,
                phase: ProtocolPhase::InputIngress,
            });
        }
    }

    let finish = |rows: Vec<Vec<Option<Vec<u8>>>>| -> Result<LocalSourceInts> {
        rows.into_iter()
            .map(|sources| {
                sources
                    .into_iter()
                    .map(|source| source.ok_or(PartyMpcError::ShapeMismatch))
                    .collect()
            })
            .collect()
    };
    Ok((finish(demand)?, finish(supply)?, expected))
}

struct LocalEngine<'a> {
    session: &'a PartyMpcSession,
    party: usize,
    channels: PartyChannels,
    triples: Vec<LocalTriple>,
    next_gate: usize,
}

impl LocalEngine<'_> {
    fn and(&mut self, x: u8, y: u8) -> Result<u8> {
        if x > 1 || y > 1 {
            return Err(PartyMpcError::NonCanonicalBit);
        }
        let gate = self.next_gate;
        let triple = *self
            .triples
            .get(gate)
            .ok_or(PartyMpcError::TripleExhausted)?;
        let d_share = x ^ triple.a;
        let e_share = y ^ triple.b;
        self.channels
            .to_coordinator
            .send(PartyMessage::GateShare {
                session: self.session.binding(),
                party: self.party,
                gate,
                d: d_share,
                e: e_share,
            })
            .map_err(|_| PartyMpcError::ChannelClosed {
                phase: ProtocolPhase::BeaverGate(gate),
            })?;
        let phase = ProtocolPhase::BeaverGate(gate);
        let message = self
            .channels
            .from_coordinator
            // The coordinator owns the authoritative quorum deadline. Give
            // parties one extra quorum interval so a missing peer is reported
            // as `QuorumTimeout { have, need }`; once the coordinator returns,
            // dropping its senders releases these waits immediately.
            .recv_timeout(self.session.quorum_timeout.saturating_mul(2))
            .map_err(|error| match error {
                RecvTimeoutError::Timeout => PartyMpcError::QuorumTimeout {
                    phase,
                    have: 0,
                    need: self.session.n_parties,
                },
                RecvTimeoutError::Disconnected => PartyMpcError::ChannelClosed { phase },
            })?;
        let CoordinatorMessage::GateOpened {
            session: message_session,
            gate: opened_gate,
            d,
            e,
        } = message;
        if message_session != self.session.binding() {
            return Err(PartyMpcError::SessionMismatch);
        }
        if opened_gate != gate {
            return Err(PartyMpcError::UnexpectedMessage { expected: phase });
        }
        if d > 1 || e > 1 {
            return Err(PartyMpcError::NonCanonicalBit);
        }
        let mut z = triple.c ^ (d & triple.b) ^ (e & triple.a);
        if self.party == 0 {
            z ^= d & e;
        }
        self.next_gate += 1;
        Ok(z)
    }
}

/// Exact distributed A2B/mod-t bridge for one coefficient. `sources[i]` is this
/// party's boolean share of source party `i`'s private mod-t arithmetic share.
/// The source integers are summed by a balanced adder tree, then reduced by
/// `n-1` oblivious conditional subtractions. No sum/comparison bit is opened.
///
/// Protocol precondition: the mod-t reconstruction is a valid aggregate curve
/// coefficient `< 2^value_bits`. This is the upstream fold/wrap-bound promise;
/// the semi-honest runtime does not range-check malicious inputs. Truncation is
/// exact under that promise, and is not presented as a malicious validity gate.
fn reduce_mod_t_local(sources: &[Vec<u8>], engine: &mut LocalEngine<'_>) -> Result<Vec<u8>> {
    let session = engine.session;
    let w = session.ingress_bits();
    if sources.len() != session.n_parties
        || sources
            .iter()
            .any(|source| source.len() != w || source.iter().any(|&bit| bit > 1))
    {
        return Err(PartyMpcError::ShapeMismatch);
    }

    // Public balanced tree: all adders at one level are independent, and an odd
    // source carries unchanged. The scalar engine executes them serially today;
    // `modeled_batched_rounds` pins the actual dependency depth of this tree.
    let mut level = sources.to_vec();
    while level.len() > 1 {
        let mut next = Vec::with_capacity((level.len() + 1) / 2);
        let mut values = level.into_iter();
        while let Some(left) = values.next() {
            if let Some(right) = values.next() {
                next.push(secure_add_local(&left, &right, engine)?);
            } else {
                next.push(left);
            }
        }
        level = next;
    }
    let mut acc = level.pop().expect("n_parties >= 2");

    let modulus = local_const_int_u64(session.plaintext_modulus, w, engine.party);
    let neg_modulus = local_const_int_u64((1u64 << w) - session.plaintext_modulus, w, engine.party);
    for _ in 0..session.n_parties - 1 {
        let ge = geq_local(&acc, &modulus, engine)?;
        let subtracted = secure_add_local(&acc, &neg_modulus, engine)?;
        acc = select_local(&ge, &subtracted, &acc, engine)?;
    }
    acc.truncate(session.value_bits);
    Ok(acc)
}

/// Secret-shared `(x+y) mod 2^w`. One AND per carry bit; the final carry is
/// discarded. This matches the one-process bridge but operates on one local
/// share per party process.
fn secure_add_local(x: &[u8], y: &[u8], engine: &mut LocalEngine<'_>) -> Result<Vec<u8>> {
    if x.len() != y.len() || x.is_empty() {
        return Err(PartyMpcError::ShapeMismatch);
    }
    let mut carry = local_const(0, engine.party);
    let mut sum = Vec::with_capacity(x.len());
    for bit in 0..x.len() {
        sum.push(x[bit] ^ y[bit] ^ carry);
        if bit + 1 < x.len() {
            let product = engine.and(x[bit] ^ carry, y[bit] ^ carry)?;
            carry ^= product;
        }
    }
    Ok(sum)
}

fn geq_local(a: &[u8], b: &[u8], engine: &mut LocalEngine<'_>) -> Result<u8> {
    if a.len() != b.len() || a.is_empty() {
        return Err(PartyMpcError::ShapeMismatch);
    }
    let mut gt = local_const(0, engine.party);
    let mut eq = local_const(1, engine.party);
    for bit in (0..a.len()).rev() {
        let not_b = b[bit] ^ local_const(1, engine.party);
        let this_gt = engine.and(a[bit], not_b)?;
        let contribution = engine.and(eq, this_gt)?;
        gt ^= contribution;
        let eq_bit = a[bit] ^ b[bit] ^ local_const(1, engine.party);
        eq = engine.and(eq, eq_bit)?;
    }
    Ok(gt ^ eq)
}

/// Equality of two secret-shared integers. The running prefix remains shared;
/// the only reconstruction happens after the full circuit returns its final
/// share to the coordinator.
fn equal_local(a: &[u8], b: &[u8], engine: &mut LocalEngine<'_>) -> Result<u8> {
    if a.len() != b.len() || a.is_empty() {
        return Err(PartyMpcError::ShapeMismatch);
    }
    let mut equal = local_const(1, engine.party);
    for (&a_bit, &b_bit) in a.iter().zip(b) {
        let same = a_bit ^ b_bit ^ local_const(1, engine.party);
        equal = engine.and(equal, same)?;
    }
    Ok(equal)
}

fn secure_min_local(a: &[u8], b: &[u8], engine: &mut LocalEngine<'_>) -> Result<Vec<u8>> {
    let ge = geq_local(a, b, engine)?;
    let lt = ge ^ local_const(1, engine.party);
    a.iter()
        .zip(b)
        .map(|(&a_bit, &b_bit)| {
            let selected = engine.and(lt, a_bit ^ b_bit)?;
            Ok(b_bit ^ selected)
        })
        .collect()
}

fn select_local(
    condition: &u8,
    a: &[u8],
    b: &[u8],
    engine: &mut LocalEngine<'_>,
) -> Result<Vec<u8>> {
    if a.len() != b.len() {
        return Err(PartyMpcError::ShapeMismatch);
    }
    a.iter()
        .zip(b)
        .map(|(&a_bit, &b_bit)| {
            let selected = engine.and(*condition, a_bit ^ b_bit)?;
            Ok(b_bit ^ selected)
        })
        .collect()
}

fn local_const(bit: u8, party: usize) -> u8 {
    if party == 0 {
        bit & 1
    } else {
        0
    }
}

fn local_const_int(value: usize, bits: usize, party: usize) -> Vec<u8> {
    (0..bits)
        .map(|bit| local_const(((value >> bit) & 1) as u8, party))
        .collect()
}

fn local_const_int_u64(value: u64, bits: usize, party: usize) -> Vec<u8> {
    (0..bits)
        .map(|bit| local_const(((value >> bit) & 1) as u8, party))
        .collect()
}

fn split_bit<R: Rng>(secret: u8, n: usize, rng: &mut R) -> Vec<u8> {
    let mut shares = vec![0u8; n];
    let mut parity = 0u8;
    for share in shares.iter_mut().take(n - 1) {
        *share = rng.gen_range(0..=1);
        parity ^= *share;
    }
    shares[n - 1] = (secret & 1) ^ parity;
    shares
}

/// Bitwise XOR sharing of one source party's local arithmetic share, returned as
/// `recipient -> bits`. Every recipient receives only its one fresh share.
fn split_int<R: Rng>(value: u64, bits: usize, n: usize, rng: &mut R) -> Vec<Vec<u8>> {
    let mut recipients = vec![Vec::with_capacity(bits); n];
    for bit in 0..bits {
        let shares = split_bit(((value >> bit) & 1) as u8, n, rng);
        for (recipient, share) in recipients.iter_mut().zip(shares) {
            recipient.push(share);
        }
    }
    recipients
}

fn crossing_and_gates(k: usize, b: usize) -> Result<usize> {
    let idx = index_bits(k);
    let per_bucket = 4usize
        .checked_mul(b)
        .ok_or(PartyMpcError::ArithmeticOverflow)?;
    let minima = k
        .checked_mul(per_bucket)
        .ok_or(PartyMpcError::ArithmeticOverflow)?;
    let tournament_node = per_bucket
        .checked_add(idx)
        .ok_or(PartyMpcError::ArithmeticOverflow)?;
    let tournament = k
        .saturating_sub(1)
        .checked_mul(tournament_node)
        .ok_or(PartyMpcError::ArithmeticOverflow)?;
    minima
        .checked_add(tournament)
        .ok_or(PartyMpcError::ArithmeticOverflow)
}

fn exact_and_gates(session: &PartyMpcSession) -> Result<usize> {
    let w = session.ingress_bits();
    // Per coefficient: n-1 balanced-tree additions at w-1 ANDs each, followed
    // by n-1 reductions of geq(3w) + subtraction(w-1) + select(w).
    let initial_add = w
        .checked_sub(1)
        .and_then(|gates| gates.checked_mul(session.n_parties - 1))
        .ok_or(PartyMpcError::ArithmeticOverflow)?;
    let one_reduction = 3usize
        .checked_mul(w)
        .and_then(|count| count.checked_add(w - 1))
        .and_then(|count| count.checked_add(w))
        .ok_or(PartyMpcError::ArithmeticOverflow)?;
    let reductions = one_reduction
        .checked_mul(session.n_parties - 1)
        .ok_or(PartyMpcError::ArithmeticOverflow)?;
    let per_coefficient = initial_add
        .checked_add(reductions)
        .ok_or(PartyMpcError::ArithmeticOverflow)?;
    let ingress = 2usize
        .checked_mul(session.buckets)
        .and_then(|count| count.checked_mul(per_coefficient))
        .ok_or(PartyMpcError::ArithmeticOverflow)?;
    let decision = match session.circuit {
        CircuitKind::Crossing => crossing_and_gates(session.buckets, session.value_bits)?,
        CircuitKind::Equality => session.value_bits,
        CircuitKind::LessThan => 3usize
            .checked_mul(session.value_bits)
            .ok_or(PartyMpcError::ArithmeticOverflow)?,
    };
    ingress
        .checked_add(decision)
        .ok_or(PartyMpcError::ArithmeticOverflow)
}

fn modeled_batched_rounds(session: &PartyMpcSession) -> usize {
    let w = session.ingress_bits();
    let sum_depth = ceil_log2_public(session.n_parties) * (w - 1);
    let reduction_depth = (session.n_parties - 1) * (w + 1);
    let decision_depth = match session.circuit {
        CircuitKind::Crossing => crossing_rounds(session.buckets, session.value_bits),
        CircuitKind::Equality => session.value_bits,
        CircuitKind::LessThan => session.value_bits,
    };
    sum_depth + reduction_depth + decision_depth
}

fn sum_width(n: usize, modulus: u64) -> Result<usize> {
    let max_sum = (n as u128)
        .checked_mul(u128::from(modulus.saturating_sub(1)))
        .ok_or(PartyMpcError::ArithmeticOverflow)?;
    let bits = (128 - max_sum.leading_zeros() as usize).max(1);
    if bits >= 64 {
        return Err(PartyMpcError::InvalidParameters(
            "mod-t arithmetic-share sum must fit below 64 bits",
        ));
    }
    Ok(bits)
}

fn ceil_log2_public(n: usize) -> usize {
    usize::BITS as usize - n.saturating_sub(1).leading_zeros() as usize
}

fn validate_message_header(
    session: &PartyMpcSession,
    message_session: SessionBinding,
    party: usize,
) -> Result<()> {
    if message_session != session.binding() {
        return Err(PartyMpcError::SessionMismatch);
    }
    if party >= session.n_parties {
        return Err(PartyMpcError::InvalidParty {
            party,
            n_parties: session.n_parties,
        });
    }
    Ok(())
}

fn recv_before(
    receiver: &Receiver<PartyMessage>,
    deadline: Instant,
    phase: ProtocolPhase,
    have: usize,
    need: usize,
) -> Result<PartyMessage> {
    let remaining = deadline.saturating_duration_since(Instant::now());
    if remaining.is_zero() {
        return Err(PartyMpcError::QuorumTimeout { phase, have, need });
    }
    receiver
        .recv_timeout(remaining)
        .map_err(|error| match error {
            RecvTimeoutError::Timeout => PartyMpcError::QuorumTimeout { phase, have, need },
            RecvTimeoutError::Disconnected => PartyMpcError::ChannelClosed { phase },
        })
}

fn encode_bits(value: u64, bits: usize) -> Vec<u8> {
    (0..bits).map(|bit| ((value >> bit) & 1) as u8).collect()
}

fn decode_bits(bits: &[u8]) -> Result<u64> {
    let mut value = 0u64;
    for (bit, &share) in bits.iter().enumerate() {
        if share > 1 || bit >= 64 {
            return Err(PartyMpcError::InvalidOutput);
        }
        value |= (share as u64) << bit;
    }
    Ok(value)
}
