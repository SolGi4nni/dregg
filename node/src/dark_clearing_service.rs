//! **THE ENCRYPTED CALL AUCTION, ON THE NODE'S OWN SURFACE.**
//!
//! Until this module existed, every piece of the fhEgg dark-clearing tower lived in
//! `fhegg-fhe` / `dreggnet-market` and was reachable only from a test binary. A user of a
//! running `dregg-node` could not submit an encrypted order at all. This module is the wiring,
//! not a new mechanism: it stands up the EXACT path
//! [`fhegg_fhe`]'s `dark_clearing_quorum_e2e` exercises —
//!
//! 1. a real Shamir BFV **DKG** (`threshold::quorum`) over `KEY_CUSTODIANS` dealers with an
//!    `OPENING_THRESHOLD`-of-`KEY_CUSTODIANS` opening rule;
//! 2. **authenticated encrypted ingress** ([`fhegg_fhe::order_ingress`]): the trader encrypts its
//!    own unary price-bucket row under the collective public key IN ITS OWN PROCESS and signs the
//!    envelope; this node parses a strict wire, verifies the Ed25519 attribution against a pinned
//!    roster, and refuses a reused `(trader, sequence)`;
//! 3. the **carry-free additive fold** ([`fhegg_fhe::additive`]) of those ciphertexts into the
//!    encrypted demand/supply curves — no secret key is involved and nothing is decrypted;
//! 4. the **masked quorum boundary** ([`fhegg_fhe::boundary`]): live custodians open only a
//!    one-time-padded curve, and each mask owner derives a private mod-`t` share of it;
//! 5. the **distributed MPC crossing** ([`fhegg_fhe::mpc_party`]), which reveals `(p*, V*)` and
//!    nothing else — no per-bucket volume, no curve, no order;
//! 6. an **attested clearing receipt** ([`fhegg_fhe::attestation`]) binding the exact ordered
//!    ciphertext inputs, the BFV custody identity, the reveal-only transcript and the outcome,
//!    co-signed by the computation roster and checked against a replay guard.
//!
//! # SUBSTRATE, said out loud
//!
//! **No AIR, constraint, gadget, or `air_accepts` predicate is authored here.** The only circuit
//! object this module touches is the **Lean-emitted** fixed-family descriptor
//! `dark-bazaar-private-n4k4` (authored in `metatheory/Market/DarkBazaarPrivateDescriptor.lean`,
//! emitted to `circuit/descriptors/by-name/dark-bazaar-private-n4k4.json`, consumed by
//! [`dregg_circuit_prove::dark_bazaar_private`]). This module READS that artifact to learn the
//! proven family and refuses anything outside it. It never writes a constraint.
//!
//! # WHAT THIS DOES AND DOES NOT GIVE YOU — read before believing the word "dark"
//!
//! **It gives you:** an HTTP/MCP surface that never receives, stores, logs, or returns a
//! plaintext order. The order is encrypted in the trader's process under a collective key whose
//! secret exists only as Shamir shares; the node folds ciphertexts; the only values ever opened
//! are the one-time-padded curves (which are information-theoretically blinded to the opener) and
//! the final `(p*, V*)`.
//!
//! **It does NOT give you a distributed deployment.** Every custodian, every mask owner and every
//! MPC party in this module runs INSIDE THIS NODE PROCESS. What survives co-location is the
//! *reconstruction structure* — a short opening set does not open anything, the crossing is a
//! genuine boolean MPC, the receipt is genuinely quorum-signed. What does NOT survive it is any
//! no-single-viewer claim: this process holds every share and could reconstruct. The
//! `dark_pool_offering` module in `dreggnet-market` carries the same caveat for the same reason,
//! in the same words. Nothing here is a Tier-0 house-blind clear.
//!
//! **Preprocessing is a trusted dealer.** [`fhegg_fhe::mpc_party::trusted_dealer_triples`] is
//! shape-only trusted preprocessing dealt by this process. `fhegg-fhe` has a certified
//! preprocessing path; this module does not use it, because with all parties co-located it would
//! certify nothing that co-location has not already given away. Named, not hidden.
//!
//! **The 4-bit quantity bound is a DECLARATION, not a range proof.** The submitted envelope
//! carries `plain_bound`, which this node refuses above [`FAMILY_MAX_QTY`]. A malicious trader
//! can declare `plain_bound = 15` and encrypt something larger; catching that needs a lattice
//! range proof, which is not in this path. The `N = 4` order count and `K = 4` bucket count ARE
//! structurally enforced.
//!
//! **The order's SIDE is plaintext on the submitted wire.** `fhegg-fhe`'s ingress envelope carries
//! a side tag because the additive fold must partition demand from supply. This node never
//! republishes it: no response of this module returns a side, a limit, a quantity, a trader index,
//! or a ciphertext. But whoever holds the wire bytes — the submitter, and any transport that sees
//! them — learns one bit per order.
//!
//! # FAIL CLOSED
//!
//! Three named dependencies gate every accept, and each refusal says which one:
//!
//! * [`ClearingDependency::Committee`] — the BFV key-custody quorum. No committee, or fewer live
//!   custodians than the opening threshold: refuse.
//! * [`ClearingDependency::VerifiedCore`] — the Lean-emitted family descriptor
//!   ([`EMITTED_FAMILY_DESCRIPTOR`]) must parse and its emitted shape must agree with the family
//!   this surface advertises. A drifted, renamed, or unparseable emission: refuse, on every entry
//!   point. **Scope, stated at current resolution:** that descriptor is the whole of the verified
//!   core this path depends on. The BFV/MPC clear calls no Lean `@[export]`, so this module does
//!   NOT require the linked Lean archive — a refusal keyed to an archive nothing in the path uses
//!   would detect nothing. The node reports its archive state as a disclosure
//!   ([`ClearingSessionWire::lean_archive_linked`]) instead of pretending it is a gate.
//! * [`ClearingDependency::Certificate`] — the attested clearing receipt's computation-integrity
//!   quorum evidence must assemble and `verify_full` must accept it against a replay guard. A
//!   short or forged signature set: refuse, and no result is recorded.
//!
//! There is no degraded mode. There is no plaintext fallback. A refusal is a refusal.

use std::collections::BTreeMap;
use std::sync::Arc;
use std::time::Duration;

use axum::{
    Json, Router,
    body::Bytes,
    extract::{DefaultBodyLimit, Path, State},
    http::{HeaderMap, StatusCode},
    routing::{get, post},
};
use serde::{Deserialize, Serialize};

use ed25519_dalek::SigningKey;
use fhe::bfv::PublicKey as BfvPublicKey;
use fhe_traits::{DeserializeParametrized, Serialize as FheSerialize};

use fhegg_fhe::additive::CollectiveOrderFoldEngine;
use fhegg_fhe::attestation::{
    AttestedClearingReceipt, AuthenticatedQuorumVerifier, BfvPublicIdentity,
    ComputationIntegrityEvidence, ComputationIntegrityResidual, ExpectedClearingContext,
    InMemoryReplayGuard,
};
use fhegg_fhe::boundary::{
    MaskedBoundaryParty, MaskedDecryptCoordinator, MaskedDecryptSession, MaskedOpening,
};
use fhegg_fhe::mpc_party::{
    PartyArithmeticInput, PartyMpcSession, local_channels, run_party, trusted_dealer_triples,
};
use fhegg_fhe::order_ingress::{
    AuthenticatedOrderBook, OrderIngressSession, SignedOrderSubmission,
};
use fhegg_fhe::threshold::quorum::{
    PrivateDealerShare, QuorumKeygenSession, QuorumOpeningSession, QuorumParty, deal,
    finish_public_key,
};
use fhegg_fhe::threshold::{BfvParams, CollectivePublicKey, MIN_SMUDGE_BITS};

use crate::state::NodeState;

// ─── THE PROVEN FAMILY ────────────────────────────────────────────────────────
//
// Read off the Lean-emitted `dark-bazaar-private-n4k4` relation, NOT invented here.

/// The Lean-emitted fixed-family relation this surface is gated to.
pub const CLEARING_FAMILY: &str = "dark-bazaar-private-n4k4";

/// `N` — the exact number of orders the proven family admits.
pub const FAMILY_ORDERS: usize = dregg_circuit_prove::dark_bazaar_private::ORDER_COUNT;

/// `K` — the exact number of price buckets the proven family admits.
pub const FAMILY_BUCKETS: usize = dregg_circuit_prove::dark_bazaar_private::PRICE_COUNT;

/// The 4-bit quantity ceiling of the proven family. Enforced here only against the
/// envelope's DECLARED `plain_bound`; see the module header.
pub const FAMILY_MAX_QTY: u64 = dregg_circuit_prove::dark_bazaar_private::MAX_QTY as u64;

/// BFV key-custody roster size (Shamir dealers).
pub const KEY_CUSTODIANS: usize = 4;
/// Live custodians required to open anything. Strictly below [`KEY_CUSTODIANS`]: this is the
/// crash-tolerant path, so one custodian may be offline.
pub const OPENING_THRESHOLD: usize = 3;
/// Mask owners / MPC parties. Equals [`OPENING_THRESHOLD`] — the live set does the crossing.
pub const LIVE_PARTIES: usize = 3;
/// Value width of the MPC crossing's secret-shared bucket volumes.
const CROSSING_VALUE_BITS: usize = 16;
/// Liveness deadline of the in-process MPC quorum. Not a security parameter.
const MPC_QUORUM_TIMEOUT: Duration = Duration::from_secs(60);

const RECEIPT_DOMAIN: &str = "dregg-node/dark-clearing/receipt/v1";
const SESSION_NONCE_DOMAIN: &str = "dregg-node/dark-clearing/session-nonce/v1";
const DEMAND_NONCE_DOMAIN: &str = "dregg-node/dark-clearing/boundary-demand/v1";
const SUPPLY_NONCE_DOMAIN: &str = "dregg-node/dark-clearing/boundary-supply/v1";
const MPC_NONCE_DOMAIN: &str = "dregg-node/dark-clearing/mpc/v1";

/// One BFV ciphertext at the degree-4096 fold set, plus envelope. Generous, but bounded.
pub const MAX_ORDER_ENVELOPE_BYTES: usize = 4 * 1024 * 1024;

/// The exact security account a frontend must paint beside this surface. Every response carries
/// it; it is not optional decoration.
pub const CLEARING_DISCLOSURE: &str = "Encrypted call auction, gated to the Lean-emitted \
dark-bazaar-private-n4k4 family (N=4 orders, K=4 price buckets, 4-bit quantities). Orders are \
encrypted in the trader's own process under a Shamir BFV collective key and folded here as \
ciphertexts; only the one-time-padded curves and the final (p*, V*) are ever opened, and no \
endpoint of this surface returns an order, a side, a limit, a quantity, a trader index, a \
ciphertext, or a per-bucket volume. DISCLOSED AND NOT HIDDEN: every key custodian, mask owner \
and MPC party runs inside THIS node process, so the no-single-viewer property does not survive \
co-location — this process holds every share and could reconstruct; the MPC preprocessing is a \
trusted dealer dealt by this same process; the 4-bit quantity ceiling is enforced only against \
the envelope's declared plain_bound and is a declaration, not a range proof; and the ingress \
envelope carries a plaintext side tag (the additive fold must partition demand from supply), so \
whoever holds the submitted wire bytes learns one bit per order.";

// ─── REFUSALS ─────────────────────────────────────────────────────────────────

/// The three named dependencies a refusal can cite. A refusal that cites one of these is a
/// FAIL-CLOSED refusal: the mechanism was unavailable, and nothing degraded.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ClearingDependency {
    /// The BFV key-custody quorum.
    Committee,
    /// The Lean-emitted family descriptor ([`EMITTED_FAMILY_DESCRIPTOR`]).
    VerifiedCore,
    /// The attested clearing receipt's computation-integrity quorum evidence.
    Certificate,
}

impl ClearingDependency {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Committee => "committee",
            Self::VerifiedCore => "verified_core",
            Self::Certificate => "certificate",
        }
    }
}

/// Why the dark-clearing surface refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClearingRefusal {
    /// A named dependency was unavailable. Fail-closed.
    Dependency {
        dependency: ClearingDependency,
        detail: String,
    },
    /// The request is outside the Lean-emitted proven family.
    OutsideFamily(String),
    /// The authenticated encrypted ingress refused the envelope (roster, signature, session,
    /// replayed source, or a non-canonical ciphertext).
    Ingress(String),
    /// No such clearing session on this node.
    NoSuchSession,
    /// The session already cleared; its outcome is immutable.
    AlreadyCleared,
    /// The book is not yet complete.
    BookIncomplete { accepted: usize, required: usize },
    /// The session exists and has not cleared, so there is no result to read.
    NotCleared { accepted: usize, required: usize },
    /// A malformed request that never reached the crypto.
    BadRequest(String),
}

impl ClearingRefusal {
    fn committee(detail: impl ToString) -> Self {
        Self::Dependency {
            dependency: ClearingDependency::Committee,
            detail: detail.to_string(),
        }
    }
    fn verified_core(detail: impl ToString) -> Self {
        Self::Dependency {
            dependency: ClearingDependency::VerifiedCore,
            detail: detail.to_string(),
        }
    }
    fn certificate(detail: impl ToString) -> Self {
        Self::Dependency {
            dependency: ClearingDependency::Certificate,
            detail: detail.to_string(),
        }
    }

    /// The named dependency, when this refusal is a fail-closed dependency refusal.
    pub fn dependency(&self) -> Option<ClearingDependency> {
        match self {
            Self::Dependency { dependency, .. } => Some(*dependency),
            _ => None,
        }
    }

    fn wire_kind(&self) -> &'static str {
        match self {
            Self::Dependency { dependency, .. } => dependency.as_str(),
            Self::OutsideFamily(_) => "outside_family",
            Self::Ingress(_) => "ingress",
            Self::NoSuchSession => "no_such_session",
            Self::AlreadyCleared => "already_cleared",
            Self::BookIncomplete { .. } => "book_incomplete",
            Self::NotCleared { .. } => "not_cleared",
            Self::BadRequest(_) => "bad_request",
        }
    }

    fn detail(&self) -> String {
        match self {
            Self::Dependency { detail, .. } => detail.clone(),
            Self::OutsideFamily(why) | Self::Ingress(why) | Self::BadRequest(why) => why.clone(),
            Self::NoSuchSession => "no such dark-clearing session on this node".to_string(),
            Self::AlreadyCleared => {
                "this session already cleared; its outcome is immutable".to_string()
            }
            Self::BookIncomplete { accepted, required } => format!(
                "the proven family clears exactly {required} orders; {accepted} accepted so far"
            ),
            Self::NotCleared { accepted, required } => format!(
                "this session has not cleared ({accepted} of {required} orders accepted); there \
                 is no result to read, and a refused clear publishes nothing"
            ),
        }
    }

    fn status(&self) -> StatusCode {
        match self {
            // A missing dependency is an unavailability, not a client error.
            Self::Dependency { .. } => StatusCode::SERVICE_UNAVAILABLE,
            Self::OutsideFamily(_) | Self::BadRequest(_) => StatusCode::BAD_REQUEST,
            Self::Ingress(_) => StatusCode::FORBIDDEN,
            Self::NoSuchSession => StatusCode::NOT_FOUND,
            Self::AlreadyCleared | Self::BookIncomplete { .. } | Self::NotCleared { .. } => {
                StatusCode::CONFLICT
            }
        }
    }
}

impl std::fmt::Display for ClearingRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.wire_kind(), self.detail())
    }
}

impl std::error::Error for ClearingRefusal {}

/// The wire shape of every refusal. `dependency` is `true` exactly when this is one of the three
/// fail-closed dependency refusals, so a client never has to string-match to know.
#[derive(Clone, Debug, Serialize)]
pub struct ClearingRefusalWire {
    pub refused: String,
    pub detail: String,
    pub dependency: bool,
    pub family: &'static str,
    pub disclosure: &'static str,
}

impl From<&ClearingRefusal> for ClearingRefusalWire {
    fn from(refusal: &ClearingRefusal) -> Self {
        Self {
            refused: refusal.wire_kind().to_string(),
            detail: refusal.detail(),
            dependency: refusal.dependency().is_some(),
            family: CLEARING_FAMILY,
            disclosure: CLEARING_DISCLOSURE,
        }
    }
}

type ClearingApiError = (StatusCode, Json<ClearingRefusalWire>);

fn api_error(refusal: ClearingRefusal) -> ClearingApiError {
    (refusal.status(), Json(ClearingRefusalWire::from(&refusal)))
}

// ─── THE VERIFIED-CORE GATE ───────────────────────────────────────────────────

/// The family shape this surface enforces, as read off the Lean-emitted descriptor.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct FamilyShape {
    /// `N` — how many order slots the emitted family commits to.
    pub order_slots: usize,
    /// `K` — how many price buckets the emitted family commits to.
    pub price_buckets: usize,
    /// The 4-bit quantity ceiling. Named `_declared` because that is all this surface can check
    /// about it: the envelope declares a plaintext bound, and no range proof backs the
    /// declaration.
    pub max_qty_declared: u64,
    /// The emitted descriptor's own name — the Lean artifact's identity, not a label chosen here.
    pub descriptor_name: &'static str,
    pub descriptor_trace_width: usize,
}

/// **The verified-core gate.** Parse the Lean-emitted family descriptor `json` and require it to
/// agree with the family constants this surface advertises.
///
/// This is a real gate and it is refutable: hand it a drifted descriptor and it refuses. The node
/// passes the checked-in emitted artifact; the unit tests pass mutated ones and observe the red.
///
/// Honest scope: the descriptor is the FAMILY authority, not the CLEARING authority. The BFV/MPC
/// clear below does not consume this descriptor — the fixed-family STARK relation emitted from it
/// is a separate composition. What this gate buys is that the shape this surface advertises as
/// "the proven family" is exactly the shape Lean emitted, and cannot drift silently.
pub fn verified_family_from_descriptor(json: &str) -> Result<FamilyShape, ClearingRefusal> {
    let descriptor = dregg_circuit::descriptor_ir2::parse_vm_descriptor2(json).map_err(|e| {
        ClearingRefusal::verified_core(format!(
            "the Lean-emitted {CLEARING_FAMILY} descriptor did not parse: {e}"
        ))
    })?;
    let expected_name = "dark-bazaar-private-n4k4::wide-poseidon2-v2";
    if descriptor.name != expected_name {
        return Err(ClearingRefusal::verified_core(format!(
            "the emitted descriptor names '{}', not '{expected_name}' — the family this surface \
             advertises is not the family Lean emitted",
            descriptor.name
        )));
    }
    // `descriptor()` is `dregg-circuit-prove`'s own drift gate over the SAME artifact (trace
    // width + public-input count). Running it here means a drifted emission is refused at the
    // node's door, not discovered at proving time.
    let pinned = dregg_circuit_prove::dark_bazaar_private::descriptor().map_err(|e| {
        ClearingRefusal::verified_core(format!(
            "the pinned {CLEARING_FAMILY} descriptor gate refused the emitted artifact: {e}"
        ))
    })?;
    if pinned.trace_width != descriptor.trace_width
        || pinned.public_input_count != descriptor.public_input_count
    {
        return Err(ClearingRefusal::verified_core(
            "the supplied descriptor disagrees with the pinned emitted artifact".to_string(),
        ));
    }
    if FAMILY_ORDERS == 0 || FAMILY_BUCKETS == 0 {
        return Err(ClearingRefusal::verified_core(
            "the emitted family is degenerate (zero orders or zero buckets)".to_string(),
        ));
    }
    Ok(FamilyShape {
        order_slots: FAMILY_ORDERS,
        price_buckets: FAMILY_BUCKETS,
        max_qty_declared: FAMILY_MAX_QTY,
        descriptor_name: expected_name,
        descriptor_trace_width: descriptor.trace_width,
    })
}

/// The Lean-emitted artifact the live surface gates on.
///
/// **Say the scope out loud.** The verified core this path depends on is THIS ARTIFACT and
/// nothing more: the BFV/MPC clear below calls no Lean `@[export]`, so requiring the linked Lean
/// archive here would be a gate with no mechanical relationship to what it gates — a refusal that
/// detects nothing. The node still DISCLOSES whether its archive is linked
/// ([`ClearingSessionWire::lean_archive_linked`]), because a reader deserves to know; it is a
/// disclosure, not a gate.
pub const EMITTED_FAMILY_DESCRIPTOR: &str =
    dregg_circuit_prove::dark_bazaar_private::DARK_BAZAAR_PRIVATE_DESCRIPTOR_JSON;

// ─── RECEIPTS ─────────────────────────────────────────────────────────────────

/// One link of this surface's receipt chain. **Every accept leaves one.**
///
/// Deliberately austere: it carries digests and counts, never an order, a side, a limit, a
/// quantity, a trader index or a ciphertext.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ClearingReceipt {
    /// `session_open` | `order_accepted` | `cleared`.
    pub kind: String,
    /// Hex session nonce — the public identity of the clearing session.
    pub session: String,
    /// Sequence within this node's dark-clearing receipt chain.
    pub sequence: u64,
    /// Orders accepted into the book at the moment this receipt was cut.
    pub accepted_orders: usize,
    /// Hex blake3 of the exact bytes this receipt is about (the submitted envelope, or the
    /// attested clearing receipt's canonical envelope). `None` for a session open.
    pub subject_digest: Option<String>,
    pub previous_receipt_hash: Option<String>,
    pub receipt_hash: String,
    pub family: &'static str,
}

fn hex32(bytes: &[u8; 32]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn parse_hex32(label: &str, s: &str) -> Result<[u8; 32], ClearingRefusal> {
    if s.len() != 64 {
        return Err(ClearingRefusal::BadRequest(format!(
            "{label} must be 64 hex characters"
        )));
    }
    let mut out = [0u8; 32];
    for (i, chunk) in s.as_bytes().chunks(2).enumerate() {
        let hi = (chunk[0] as char)
            .to_digit(16)
            .ok_or_else(|| ClearingRefusal::BadRequest(format!("{label} is not hexadecimal")))?;
        let lo = (chunk[1] as char)
            .to_digit(16)
            .ok_or_else(|| ClearingRefusal::BadRequest(format!("{label} is not hexadecimal")))?;
        out[i] = ((hi << 4) | lo) as u8;
    }
    Ok(out)
}

// ─── THE PUBLIC SESSION MATERIAL ──────────────────────────────────────────────

/// Everything a trader needs to encrypt an order, and nothing else. All of it is public by
/// construction: the collective public key encrypts without a secret and without a quorum.
#[derive(Clone, Debug, Serialize)]
pub struct ClearingSessionWire {
    pub session: String,
    pub family: &'static str,
    pub shape: FamilyShape,
    /// Base64 of `CollectivePublicKey::pk.to_bytes()`.
    pub collective_public_key_b64: String,
    pub collective_public_key_digest: String,
    pub bfv_degree: u64,
    pub bfv_plaintext_modulus: u64,
    /// Total key-custody roster.
    pub key_custodians: usize,
    /// Live custodians required to open anything.
    pub opening_threshold: usize,
    /// The pinned ordered trader roster, hex Ed25519 verifying keys. A submission signed by
    /// anything else is refused.
    ///
    /// PARTICIPATION METADATA, disclosed on purpose: this says WHO holds a seat (it is the
    /// opener's own input, and a trader needs it to learn its seat index). It says nothing about
    /// what anyone ordered. Anyone who can read this endpoint can see the seating chart.
    pub trader_roster: Vec<String>,
    pub accepted_orders: usize,
    pub cleared: bool,
    /// Whether THIS node has the verified Lean archive linked. Reported, not required: nothing in
    /// the clearing path calls a Lean export, so gating on it would detect nothing. The family
    /// gate that IS load-bearing runs against the Lean-EMITTED descriptor
    /// ([`EMITTED_FAMILY_DESCRIPTOR`]).
    pub lean_archive_linked: bool,
    pub disclosure: &'static str,
}

/// The cleared result. **This is the entire reveal.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ClearedResultWire {
    pub session: String,
    pub family: &'static str,
    /// `p*` — the clearing price bucket, or `null` when the book never clears.
    pub p_star: Option<usize>,
    /// `V*` — the cleared volume.
    pub v_star: u64,
    /// Hex claim digest of the attested clearing receipt.
    pub claim_digest: String,
    /// Hex canonical envelope digest of the attested clearing receipt.
    pub envelope_digest: String,
    /// Hex roster digest of the computation-integrity quorum that co-signed the claim.
    pub quorum_roster_digest: String,
    pub quorum_threshold: usize,
    /// Custody identity the claim binds (roster size / opening threshold).
    pub bfv_custodians: u64,
    pub bfv_opening_threshold: u64,
    /// Number of ordered input bindings the claim covers (two per accepted order: the
    /// authenticated source message and the exact ciphertext).
    pub bound_inputs: usize,
    /// Whether `verify_full` accepted this receipt against the replay guard.
    pub certificate_verified: bool,
    pub disclosure: &'static str,
}

// ─── SESSION STATE ────────────────────────────────────────────────────────────

struct ClearingSession {
    nonce: [u8; 32],
    params: BfvParams,
    keygen: QuorumKeygenSession,
    collective: CollectivePublicKey,
    custodians: Vec<QuorumParty>,
    ingress: OrderIngressSession,
    trader_roster: Vec<[u8; 32]>,
    /// `None` once the book has been consumed by a clear.
    book: Option<AuthenticatedOrderBook>,
    accepted: usize,
    /// Sides seen, so the "at least one bid and one ask" family precondition refuses with a
    /// legible reason instead of surfacing as an internal fold error.
    bids: usize,
    asks: usize,
    /// The in-process computation-integrity roster. Node-local by construction (see the module
    /// header); the signing keys never leave this struct.
    quorum_keys: Vec<SigningKey>,
    cleared: Option<ClearedResultWire>,
}

impl ClearingSession {
    fn wire(&self, shape: FamilyShape) -> ClearingSessionWire {
        ClearingSessionWire {
            session: hex32(&self.nonce),
            family: CLEARING_FAMILY,
            shape,
            collective_public_key_b64: b64(&self.collective.pk.to_bytes()),
            collective_public_key_digest: hex32(
                blake3::hash(&self.collective.pk.to_bytes()).as_bytes(),
            ),
            bfv_degree: self.params.degree() as u64,
            bfv_plaintext_modulus: self.params.plaintext_modulus(),
            key_custodians: KEY_CUSTODIANS,
            opening_threshold: OPENING_THRESHOLD,
            trader_roster: self.trader_roster.iter().map(hex32).collect(),
            accepted_orders: self.accepted,
            cleared: self.cleared.is_some(),
            lean_archive_linked: dregg_lean_ffi::lean_available(),
            disclosure: CLEARING_DISCLOSURE,
        }
    }
}

fn b64(bytes: &[u8]) -> String {
    use base64::Engine as _;
    base64::engine::general_purpose::STANDARD.encode(bytes)
}

/// The node's dark-clearing substrate: the live sessions and this surface's receipt chain.
pub struct NodeDarkClearing {
    sessions: BTreeMap<[u8; 32], ClearingSession>,
    receipts: Vec<ClearingReceipt>,
    replay: InMemoryReplayGuard,
    /// The Lean-emitted family descriptor every entry point gates on. A field rather than a
    /// constant so the gate can be OBSERVED FIRING at the HTTP layer
    /// ([`Self::force_family_descriptor`]) — a gate nobody has watched go red is not a gate.
    family_descriptor: &'static str,
}

impl Default for NodeDarkClearing {
    fn default() -> Self {
        Self {
            sessions: BTreeMap::new(),
            receipts: Vec::new(),
            replay: InMemoryReplayGuard::default(),
            family_descriptor: EMITTED_FAMILY_DESCRIPTOR,
        }
    }
}

impl NodeDarkClearing {
    pub fn new() -> Self {
        Self::default()
    }

    /// **The verified-core gate**, run on every entry point.
    fn gate(&self) -> Result<FamilyShape, ClearingRefusal> {
        verified_family_from_descriptor(self.family_descriptor)
    }

    /// The dark-clearing receipt chain head.
    pub fn receipt_head(&self) -> Option<&ClearingReceipt> {
        self.receipts.last()
    }

    pub fn receipt_count(&self) -> usize {
        self.receipts.len()
    }

    fn cut_receipt(
        &mut self,
        kind: &str,
        session: [u8; 32],
        accepted_orders: usize,
        subject_digest: Option<[u8; 32]>,
    ) -> ClearingReceipt {
        let previous = self.receipts.last().map(|r| r.receipt_hash.clone());
        let sequence = self.receipts.len() as u64;
        let mut hasher = blake3::Hasher::new_derive_key(RECEIPT_DOMAIN);
        hasher.update(kind.as_bytes());
        hasher.update(&session);
        hasher.update(&sequence.to_be_bytes());
        hasher.update(&(accepted_orders as u64).to_be_bytes());
        hasher.update(&subject_digest.unwrap_or([0u8; 32]));
        hasher.update(&[u8::from(subject_digest.is_some())]);
        if let Some(previous) = &previous {
            hasher.update(previous.as_bytes());
        }
        let receipt = ClearingReceipt {
            kind: kind.to_string(),
            session: hex32(&session),
            sequence,
            accepted_orders,
            subject_digest: subject_digest.as_ref().map(hex32),
            previous_receipt_hash: previous,
            receipt_hash: hex32(hasher.finalize().as_bytes()),
            family: CLEARING_FAMILY,
        };
        self.receipts.push(receipt.clone());
        receipt
    }

    /// **Open a clearing session.** Runs the real Shamir BFV DKG and pins the trader roster.
    ///
    /// Blocking: the DKG is seconds of lattice work. Callers on an async runtime must run this
    /// under `spawn_blocking`.
    pub fn open_session(
        &mut self,
        trader_roster: Vec<[u8; 32]>,
    ) -> Result<(ClearingSessionWire, ClearingReceipt), ClearingRefusal> {
        let shape = self.gate()?;

        if trader_roster.len() != shape.order_slots {
            return Err(ClearingRefusal::OutsideFamily(format!(
                "the {CLEARING_FAMILY} family seats exactly {} traders; {} were named",
                shape.order_slots,
                trader_roster.len()
            )));
        }

        let params = BfvParams::fold_set();
        let (keygen, custodians, collective) = run_quorum_dkg(&params)?;

        let mut nonce_seed = [0u8; 32];
        getrandom::fill(&mut nonce_seed).map_err(|e| {
            ClearingRefusal::committee(format!("no OS entropy for the session nonce: {e}"))
        })?;
        let nonce = blake3::derive_key(SESSION_NONCE_DOMAIN, &nonce_seed);

        let ingress = OrderIngressSession::new(nonce, shape.price_buckets, &params, &collective)
            .map_err(|e| {
                ClearingRefusal::committee(format!("the ingress session was refused: {e}"))
            })?;
        let book = AuthenticatedOrderBook::new(ingress.clone(), trader_roster.clone())
            .map_err(|e| ClearingRefusal::Ingress(format!("the trader roster was refused: {e}")))?;

        let mut quorum_keys = Vec::with_capacity(LIVE_PARTIES);
        for _ in 0..LIVE_PARTIES {
            let mut seed = [0u8; 32];
            getrandom::fill(&mut seed).map_err(|e| {
                ClearingRefusal::committee(format!("no OS entropy for a quorum signing key: {e}"))
            })?;
            quorum_keys.push(SigningKey::from_bytes(&seed));
        }

        let session = ClearingSession {
            nonce,
            params,
            keygen,
            collective,
            custodians,
            ingress,
            trader_roster,
            book: Some(book),
            accepted: 0,
            bids: 0,
            asks: 0,
            quorum_keys,
            cleared: None,
        };
        let wire = session.wire(shape);
        self.sessions.insert(nonce, session);
        let receipt = self.cut_receipt("session_open", nonce, 0, None);
        Ok((wire, receipt))
    }

    /// The public session material. Returns nothing secret.
    pub fn session_wire(&self, session: &[u8; 32]) -> Result<ClearingSessionWire, ClearingRefusal> {
        let shape = self.gate()?;
        let s = self
            .sessions
            .get(session)
            .ok_or(ClearingRefusal::NoSuchSession)?;
        Ok(s.wire(shape))
    }

    /// **Submit one trader-encrypted, trader-signed order.** The wire is the exact
    /// `SignedOrderSubmission` envelope; no plaintext order field is present in it, is accepted
    /// by this function, or is returned by it.
    pub fn submit_order(
        &mut self,
        session: &[u8; 32],
        envelope: &[u8],
    ) -> Result<ClearingReceipt, ClearingRefusal> {
        let shape = self.gate()?;
        let s = self
            .sessions
            .get_mut(session)
            .ok_or(ClearingRefusal::NoSuchSession)?;
        if s.cleared.is_some() {
            return Err(ClearingRefusal::AlreadyCleared);
        }
        if s.custodians.len() < OPENING_THRESHOLD {
            return Err(ClearingRefusal::committee(format!(
                "{} live custodians is below the {OPENING_THRESHOLD}-of-{KEY_CUSTODIANS} \
                 opening threshold",
                s.custodians.len()
            )));
        }
        if s.accepted >= shape.order_slots {
            return Err(ClearingRefusal::OutsideFamily(format!(
                "the {CLEARING_FAMILY} family admits exactly {} orders and the book is full",
                shape.order_slots
            )));
        }

        let submission = SignedOrderSubmission::from_wire_bytes(envelope, &s.ingress, &s.params)
            .map_err(|e| ClearingRefusal::Ingress(format!("{e}")))?;

        // The 4-bit family ceiling, against the envelope's DECLARED bound. A declaration, not a
        // range proof — see the module header.
        let declared = submission.ciphertext().plain_bound;
        if declared > shape.max_qty_declared {
            return Err(ClearingRefusal::OutsideFamily(format!(
                "the envelope declares a plaintext bound of {declared}, above the \
                 {CLEARING_FAMILY} 4-bit ceiling of {}",
                shape.max_qty_declared
            )));
        }

        let side_is_bid = matches!(submission.side(), fhegg_fhe::Side::Bid);
        let digest = *blake3::hash(envelope).as_bytes();

        let book = s
            .book
            .as_mut()
            .ok_or_else(|| ClearingRefusal::committee("this session's book was consumed"))?;
        book.accept(submission)
            .map_err(|e| ClearingRefusal::Ingress(format!("{e}")))?;
        s.accepted += 1;
        if side_is_bid {
            s.bids += 1;
        } else {
            s.asks += 1;
        }
        let accepted = s.accepted;
        let nonce = s.nonce;
        Ok(self.cut_receipt("order_accepted", nonce, accepted, Some(digest)))
    }

    /// **Clear the book.** Folds the encrypted rows, opens only the masked curves through a live
    /// custodian quorum, runs the MPC crossing, and issues an attested, quorum-co-signed receipt.
    ///
    /// The ONLY values this returns are `(p*, V*)` and digests.
    ///
    /// Blocking: seconds of lattice + MPC work. Run under `spawn_blocking`.
    pub fn clear(
        &mut self,
        session: &[u8; 32],
    ) -> Result<(ClearedResultWire, ClearingReceipt), ClearingRefusal> {
        let shape = self.gate()?;
        let s = self
            .sessions
            .get_mut(session)
            .ok_or(ClearingRefusal::NoSuchSession)?;
        if s.cleared.is_some() {
            return Err(ClearingRefusal::AlreadyCleared);
        }
        if s.custodians.len() < OPENING_THRESHOLD {
            return Err(ClearingRefusal::committee(format!(
                "{} live custodians is below the {OPENING_THRESHOLD}-of-{KEY_CUSTODIANS} \
                 opening threshold",
                s.custodians.len()
            )));
        }
        if s.accepted != shape.order_slots {
            return Err(ClearingRefusal::BookIncomplete {
                accepted: s.accepted,
                required: shape.order_slots,
            });
        }
        if s.bids == 0 || s.asks == 0 {
            return Err(ClearingRefusal::OutsideFamily(
                "a uniform-price call auction needs at least one bid and one ask; this book has \
                 only one side"
                    .to_string(),
            ));
        }
        // NOTE: the computation-integrity roster is deliberately NOT pre-checked here. The
        // object that refuses a short roster is `AuthenticatedQuorumVerifier` itself, below —
        // a pre-check would make the real verifier's refusal unreachable and would be a gate
        // testing itself instead of the mechanism.

        let book = s
            .book
            .take()
            .ok_or_else(|| ClearingRefusal::committee("this session's book was consumed"))?;
        let (rows, ordered_inputs) = book.finish().into_parts();

        // (3) THE CARRY-FREE ADDITIVE FOLD. CPU-only on purpose: a node daemon must not depend
        //     on a GPU device coming up, and the fold's correctness is identical either way.
        let folded = CollectiveOrderFoldEngine::cpu_only()
            .fold_rows(rows, shape.price_buckets, s.params.plaintext_modulus())
            .map_err(|e| {
                ClearingRefusal::committee(format!("the encrypted book did not fold: {e}"))
            })?;

        // (4) THE MASKED QUORUM BOUNDARY. Only a one-time-padded curve is ever opened.
        let live: Vec<usize> = (0..OPENING_THRESHOLD).collect();
        let (demand_masks, demand_opening) = masked_curve(
            blake3::derive_key(DEMAND_NONCE_DOMAIN, &s.nonce),
            folded.d_ct,
            &s.params,
            &s.keygen,
            &s.collective,
            &mut s.custodians,
            &live,
            shape.price_buckets,
        )?;
        let (supply_masks, supply_opening) = masked_curve(
            blake3::derive_key(SUPPLY_NONCE_DOMAIN, &s.nonce),
            folded.s_ct,
            &s.params,
            &s.keygen,
            &s.collective,
            &mut s.custodians,
            &live,
            shape.price_buckets,
        )?;

        // (5) THE DISTRIBUTED MPC CROSSING. Reveals (p*, V*) and nothing else.
        let mpc_session = PartyMpcSession::new(
            blake3::derive_key(MPC_NONCE_DOMAIN, &s.nonce),
            LIVE_PARTIES,
            shape.price_buckets,
            CROSSING_VALUE_BITS,
            s.params.plaintext_modulus(),
            MPC_QUORUM_TIMEOUT,
        )
        .map_err(|e| {
            ClearingRefusal::committee(format!("the MPC crossing session was refused: {e:?}"))
        })?;

        let mut inputs = Vec::with_capacity(LIVE_PARTIES);
        for (party, (demand, supply)) in demand_masks.into_iter().zip(supply_masks).enumerate() {
            let demand_share = demand.derive_mod_t_share(&demand_opening).map_err(|e| {
                ClearingRefusal::committee(format!("a demand mask share was refused: {e:?}"))
            })?;
            let supply_share = supply.derive_mod_t_share(&supply_opening).map_err(|e| {
                ClearingRefusal::committee(format!("a supply mask share was refused: {e:?}"))
            })?;
            let mut rng = rand::rngs::OsRng;
            inputs.push(
                PartyArithmeticInput::new(
                    &mpc_session,
                    party,
                    &demand_share,
                    &supply_share,
                    &mut rng,
                )
                .map_err(|e| {
                    ClearingRefusal::committee(format!("MPC ingress was refused: {e:?}"))
                })?,
            );
        }

        let mut triple_rng = rand::rngs::OsRng;
        let triples = trusted_dealer_triples(&mpc_session, &mut triple_rng).map_err(|e| {
            ClearingRefusal::committee(format!("MPC preprocessing was refused: {e:?}"))
        })?;
        let (coordinator, endpoints) = local_channels(&mpc_session);
        let party_threads: Vec<_> = inputs
            .into_iter()
            .zip(triples)
            .zip(endpoints)
            .map(|((input, triples), endpoint)| {
                std::thread::spawn(move || run_party(input, triples, endpoint))
            })
            .collect();
        let distributed = coordinator.coordinate(&mpc_session).map_err(|e| {
            ClearingRefusal::committee(format!("the MPC quorum did not clear: {e:?}"))
        })?;
        for thread in party_threads {
            thread
                .join()
                .map_err(|_| ClearingRefusal::committee("an MPC party thread panicked"))?
                .map_err(|e| ClearingRefusal::committee(format!("an MPC party refused: {e:?}")))?;
        }
        if !distributed.transcript.is_reveal_only(&mpc_session) {
            return Err(ClearingRefusal::certificate(
                "the MPC transcript is not reveal-only; refusing to publish an outcome that may \
                 carry more than (p*, V*)"
                    .to_string(),
            ));
        }

        // (6) THE ATTESTED CLEARING RECEIPT + ITS QUORUM CERTIFICATE.
        let verifier = AuthenticatedQuorumVerifier::new(
            s.quorum_keys
                .iter()
                .map(|key| key.verifying_key().to_bytes())
                .collect(),
            LIVE_PARTIES,
        )
        .map_err(|e| {
            ClearingRefusal::certificate(format!("the computation roster was refused: {e:?}"))
        })?;
        let bfv = BfvPublicIdentity::from_quorum_public(&s.params, &s.keygen, &s.collective);
        let context = ExpectedClearingContext {
            session: &mpc_session,
            ordered_roster: verifier.ordered_roster(),
            bfv: &bfv,
            ordered_inputs: &ordered_inputs,
            transcript: &distributed.transcript,
            crossing: &distributed.crossing,
        };
        let mut receipt = AttestedClearingReceipt::issue(
            &context,
            ComputationIntegrityEvidence::BindingOnly(
                ComputationIntegrityResidual::OutputOnlySelfAssertion,
            ),
        )
        .map_err(|e| {
            ClearingRefusal::certificate(format!("the clearing claim did not issue: {e}"))
        })?;
        let claim = receipt.claim_digest();
        let mut signatures = Vec::with_capacity(LIVE_PARTIES);
        for (party, key) in s.quorum_keys.iter().enumerate() {
            signatures.push(verifier.sign_claim(&claim, party, key).map_err(|e| {
                ClearingRefusal::certificate(format!("party {party} could not sign: {e:?}"))
            })?);
        }
        receipt.computation_integrity =
            verifier
                .assemble_evidence(&claim, &signatures)
                .map_err(|e| {
                    ClearingRefusal::certificate(format!(
                        "the computation-integrity quorum evidence did not assemble: {e:?}"
                    ))
                })?;
        receipt
            .verify_full(&context, &verifier, &mut self.replay)
            .map_err(|e| {
                ClearingRefusal::certificate(format!(
                    "the attested clearing receipt did not verify: {e}"
                ))
            })?;

        let result = ClearedResultWire {
            session: hex32(&s.nonce),
            family: CLEARING_FAMILY,
            p_star: distributed.crossing.p_star,
            v_star: distributed.crossing.v_star,
            claim_digest: hex32(&claim),
            envelope_digest: hex32(&receipt.envelope_digest()),
            quorum_roster_digest: hex32(&verifier.roster_digest()),
            quorum_threshold: verifier.threshold(),
            bfv_custodians: bfv.n_parties,
            bfv_opening_threshold: bfv.opening_threshold,
            bound_inputs: ordered_inputs.len(),
            certificate_verified: true,
            disclosure: CLEARING_DISCLOSURE,
        };
        let envelope_digest = receipt.envelope_digest();
        let nonce = s.nonce;
        let accepted = s.accepted;
        s.cleared = Some(result.clone());
        let chain = self.cut_receipt("cleared", nonce, accepted, Some(envelope_digest));
        Ok((result, chain))
    }

    /// Read a cleared result. Returns `(p*, V*)` and digests, and nothing else.
    pub fn cleared(&self, session: &[u8; 32]) -> Result<ClearedResultWire, ClearingRefusal> {
        let s = self
            .sessions
            .get(session)
            .ok_or(ClearingRefusal::NoSuchSession)?;
        s.cleared.clone().ok_or(ClearingRefusal::NotCleared {
            accepted: s.accepted,
            required: FAMILY_ORDERS,
        })
    }

    /// TEST/OPS SEAM — point the family gate at a different descriptor so the `verified_core`
    /// refusal can be observed firing THROUGH THE HTTP SURFACE. Only a descriptor that agrees
    /// with the emitted family passes [`verified_family_from_descriptor`], so this seam can make
    /// the surface refuse and can never make it accept something it otherwise would not.
    pub fn force_family_descriptor(&mut self, json: &'static str) {
        self.family_descriptor = json;
    }

    /// TEST/OPS SEAM — drop live custodians so the committee dependency can be observed
    /// refusing. It removes real custody parties; it cannot be used to weaken an accept.
    pub fn force_custodians_offline(&mut self, session: &[u8; 32], keep: usize) -> bool {
        match self.sessions.get_mut(session) {
            Some(s) => {
                s.custodians.truncate(keep);
                true
            }
            None => false,
        }
    }

    /// TEST/OPS SEAM — drop computation-integrity signers so the certificate dependency can be
    /// observed refusing. Removing signers can only make a clear refuse.
    pub fn force_quorum_signers(&mut self, session: &[u8; 32], keep: usize) -> bool {
        match self.sessions.get_mut(session) {
            Some(s) => {
                s.quorum_keys.truncate(keep);
                true
            }
            None => false,
        }
    }
}

/// The real Shamir BFV distributed key generation: every dealer deals, every recipient assembles.
fn run_quorum_dkg(
    params: &BfvParams,
) -> Result<(QuorumKeygenSession, Vec<QuorumParty>, CollectivePublicKey), ClearingRefusal> {
    let mut crp_seed = [0u8; 32];
    getrandom::fill(&mut crp_seed)
        .map_err(|e| ClearingRefusal::committee(format!("no OS entropy for the DKG CRP: {e}")))?;
    let session = QuorumKeygenSession::from_seed(KEY_CUSTODIANS, OPENING_THRESHOLD, crp_seed)
        .map_err(|e| ClearingRefusal::committee(format!("the DKG session was refused: {e:?}")))?;
    let mut public = Vec::with_capacity(KEY_CUSTODIANS);
    let mut inboxes: Vec<Vec<PrivateDealerShare>> =
        (0..KEY_CUSTODIANS).map(|_| Vec::new()).collect();
    for dealer in 0..KEY_CUSTODIANS {
        let (contribution, private) = deal(&session, dealer, params)
            .map_err(|e| ClearingRefusal::committee(format!("dealer {dealer} failed: {e:?}")))?
            .into_parts();
        public.push(contribution);
        for share in private {
            let recipient = share.recipient();
            inboxes[recipient].push(share);
        }
    }
    let collective = finish_public_key(&session, &public, params).map_err(|e| {
        ClearingRefusal::committee(format!("the collective public key did not close: {e:?}"))
    })?;
    let mut parties = Vec::with_capacity(KEY_CUSTODIANS);
    for (party, inbox) in inboxes.into_iter().enumerate() {
        parties.push(
            QuorumParty::assemble(&session, party, inbox, params).map_err(|e| {
                ClearingRefusal::committee(format!("custodian {party} did not assemble: {e:?}"))
            })?,
        );
    }
    Ok((session, parties, collective))
}

/// Mask one encrypted curve and open ONLY the one-time-padded result through the live quorum.
#[allow(clippy::too_many_arguments)]
fn masked_curve(
    nonce: [u8; 32],
    target: fhegg_fhe::bfv_lean::LeanCiphertext,
    params: &BfvParams,
    keygen: &QuorumKeygenSession,
    collective: &CollectivePublicKey,
    custodians: &mut [QuorumParty],
    live: &[usize],
    buckets: usize,
) -> Result<(Vec<MaskedBoundaryParty>, MaskedOpening), ClearingRefusal> {
    let mask_session =
        MaskedDecryptSession::from_public(nonce, LIVE_PARTIES, buckets, target, params).map_err(
            |e| ClearingRefusal::committee(format!("the boundary mask session was refused: {e:?}")),
        )?;
    let mut coordinator = MaskedDecryptCoordinator::new(mask_session.clone(), params.clone());
    let mut mask_states = Vec::with_capacity(LIVE_PARTIES);
    for party in 0..LIVE_PARTIES {
        let (state, contribution) =
            MaskedBoundaryParty::prepare(&mask_session, party, params, collective).map_err(
                |e| ClearingRefusal::committee(format!("mask owner {party} refused: {e:?}")),
            )?;
        coordinator.accept(contribution).map_err(|e| {
            ClearingRefusal::committee(format!("mask contribution {party} refused: {e:?}"))
        })?;
        mask_states.push(state);
    }
    let masked = coordinator
        .finish()
        .map_err(|e| ClearingRefusal::committee(format!("the masked curve refused: {e:?}")))?;
    let opening = QuorumOpeningSession::new(keygen.clone(), nonce, live.to_vec()).map_err(|e| {
        ClearingRefusal::committee(format!("the live opening roster was refused: {e:?}"))
    })?;
    let mut framed = Vec::with_capacity(live.len());
    for &party in live {
        let custodian = custodians
            .get_mut(party)
            .ok_or_else(|| ClearingRefusal::committee(format!("custodian {party} is not live")))?;
        framed.push(
            custodian
                .partial_decrypt(&opening, masked.ciphertext(), MIN_SMUDGE_BITS, params)
                .map_err(|e| {
                    ClearingRefusal::committee(format!(
                        "custodian {party} did not emit a share: {e:?}"
                    ))
                })?
                .to_wire_bytes(),
        );
    }
    let opened = masked
        .open_quorum_framed(&opening, &framed, params)
        .map_err(|e| {
            ClearingRefusal::committee(format!("the live quorum did not open the curve: {e:?}"))
        })?;
    Ok((mask_states, opened))
}

/// Reconstruct a `CollectivePublicKey` a trader received over the wire. Exposed so a client (and
/// the tests) can encrypt against the exact published key without re-deriving it.
pub fn collective_public_key_from_bytes(
    bytes: &[u8],
    params: &BfvParams,
) -> Result<CollectivePublicKey, String> {
    let pk = BfvPublicKey::from_bytes(bytes, params.arc())
        .map_err(|e| format!("collective public key did not parse: {e}"))?;
    Ok(CollectivePublicKey { pk })
}

// ─── HTTP SURFACE ─────────────────────────────────────────────────────────────

#[derive(Debug, Deserialize)]
pub struct OpenSessionRequest {
    /// Exactly `FAMILY_ORDERS` hex Ed25519 verifying keys, in roster order.
    pub traders: Vec<String>,
}

#[derive(Debug, Serialize)]
pub struct OpenSessionResponse {
    pub session: ClearingSessionWire,
    pub receipt: ClearingReceipt,
}

#[derive(Debug, Serialize)]
pub struct SubmitOrderResponse {
    pub receipt: ClearingReceipt,
    pub accepted_orders: usize,
    pub required_orders: usize,
    pub family: &'static str,
    pub disclosure: &'static str,
}

#[derive(Debug, Serialize)]
pub struct ClearResponse {
    pub result: ClearedResultWire,
    pub receipt: ClearingReceipt,
}

/// The dark-clearing routes. Merged into the node's PROTECTED router, so every one of them is
/// behind the node's bearer gate.
pub fn routes() -> Router<NodeState> {
    Router::new()
        .route("/market/dark-clearing/session", post(post_open_session))
        .route("/market/dark-clearing/session/{session}", get(get_session))
        .route(
            "/market/dark-clearing/session/{session}/order",
            post(post_order),
        )
        .route(
            "/market/dark-clearing/session/{session}/clear",
            post(post_clear),
        )
        .route(
            "/market/dark-clearing/session/{session}/result",
            get(get_result),
        )
        .route("/api/market/dark-clearing/session", post(post_open_session))
        .route(
            "/api/market/dark-clearing/session/{session}",
            get(get_session),
        )
        .route(
            "/api/market/dark-clearing/session/{session}/order",
            post(post_order),
        )
        .route(
            "/api/market/dark-clearing/session/{session}/clear",
            post(post_clear),
        )
        .route(
            "/api/market/dark-clearing/session/{session}/result",
            get(get_result),
        )
        .layer(DefaultBodyLimit::max(MAX_ORDER_ENVELOPE_BYTES))
}

async fn post_open_session(
    State(state): State<NodeState>,
    Json(req): Json<OpenSessionRequest>,
) -> Result<Json<OpenSessionResponse>, ClearingApiError> {
    let mut roster = Vec::with_capacity(req.traders.len());
    for (index, key) in req.traders.iter().enumerate() {
        roster.push(parse_hex32(&format!("traders[{index}]"), key).map_err(api_error)?);
    }
    // The DKG is seconds of lattice work: hold the lock across a BLOCKING task so it never runs
    // on an async worker thread.
    let mut guard = state.dark_clearing().write_owned().await;
    let (session, receipt) = tokio::task::spawn_blocking(move || guard.open_session(roster))
        .await
        .map_err(|e| {
            api_error(ClearingRefusal::committee(format!(
                "session task failed: {e}"
            )))
        })?
        .map_err(api_error)?;
    Ok(Json(OpenSessionResponse { session, receipt }))
}

async fn get_session(
    State(state): State<NodeState>,
    Path(session): Path<String>,
) -> Result<Json<ClearingSessionWire>, ClearingApiError> {
    let nonce = parse_hex32("session", &session).map_err(api_error)?;
    let guard = state.dark_clearing();
    let guard = guard.read().await;
    guard.session_wire(&nonce).map(Json).map_err(api_error)
}

async fn post_order(
    State(state): State<NodeState>,
    Path(session): Path<String>,
    headers: HeaderMap,
    body: Bytes,
) -> Result<Json<SubmitOrderResponse>, ClearingApiError> {
    if headers
        .get(axum::http::header::CONTENT_TYPE)
        .and_then(|value| value.to_str().ok())
        != Some("application/octet-stream")
    {
        return Err(api_error(ClearingRefusal::BadRequest(
            "an encrypted order must be submitted as application/octet-stream".to_string(),
        )));
    }
    if body.len() > MAX_ORDER_ENVELOPE_BYTES {
        return Err(api_error(ClearingRefusal::BadRequest(format!(
            "the encrypted order envelope exceeds the {MAX_ORDER_ENVELOPE_BYTES}-byte bound"
        ))));
    }
    let nonce = parse_hex32("session", &session).map_err(api_error)?;
    let guard = state.dark_clearing();
    let mut guard = guard.write().await;
    let receipt = guard.submit_order(&nonce, &body).map_err(api_error)?;
    let accepted = receipt.accepted_orders;
    Ok(Json(SubmitOrderResponse {
        receipt,
        accepted_orders: accepted,
        required_orders: FAMILY_ORDERS,
        family: CLEARING_FAMILY,
        disclosure: CLEARING_DISCLOSURE,
    }))
}

async fn post_clear(
    State(state): State<NodeState>,
    Path(session): Path<String>,
) -> Result<Json<ClearResponse>, ClearingApiError> {
    let nonce = parse_hex32("session", &session).map_err(api_error)?;
    let mut guard = state.dark_clearing().write_owned().await;
    let (result, receipt) = tokio::task::spawn_blocking(move || guard.clear(&nonce))
        .await
        .map_err(|e| {
            api_error(ClearingRefusal::committee(format!(
                "clear task failed: {e}"
            )))
        })?
        .map_err(api_error)?;
    Ok(Json(ClearResponse { result, receipt }))
}

async fn get_result(
    State(state): State<NodeState>,
    Path(session): Path<String>,
) -> Result<Json<ClearedResultWire>, ClearingApiError> {
    let nonce = parse_hex32("session", &session).map_err(api_error)?;
    let guard = state.dark_clearing();
    let guard = guard.read().await;
    guard.cleared(&nonce).map(Json).map_err(api_error)
}

#[cfg(test)]
mod tests {
    use super::*;

    use axum::body::Body;
    use axum::http::Request;
    use ed25519_dalek::SigningKey as TraderKey;
    use fhegg_fhe::{Order, Side, reference_clear};
    use http_body_util::BodyExt;
    use tower::ServiceExt;

    /// Every key that must never appear on this surface. A response carrying one of these is a
    /// leak, not a nit.
    const FORBIDDEN_KEYS: [&str; 12] = [
        "side",
        "limit",
        "qty",
        "quantity",
        "order",
        "orders",
        "ciphertext",
        "envelope",
        "trader",
        "demand",
        "supply",
        "curve",
    ];

    fn assert_no_order_fields(label: &str, value: &serde_json::Value) {
        fn walk(label: &str, path: &str, value: &serde_json::Value) {
            match value {
                serde_json::Value::Object(map) => {
                    for (key, child) in map {
                        assert!(
                            !FORBIDDEN_KEYS.contains(&key.as_str()),
                            "{label}: `{path}.{key}` leaks an order field onto the surface"
                        );
                        walk(label, &format!("{path}.{key}"), child);
                    }
                }
                serde_json::Value::Array(items) => {
                    for (i, child) in items.iter().enumerate() {
                        walk(label, &format!("{path}[{i}]"), child);
                    }
                }
                _ => {}
            }
        }
        walk(label, "$", value);
    }

    async fn fresh_state() -> (NodeState, tempfile::TempDir) {
        let tmp = tempfile::tempdir().expect("tempdir");
        let mut seed = [0u8; 32];
        seed[0] = 0xDC;
        let state =
            NodeState::with_cclerk(tmp.path(), vec![], seed).expect("NodeState::with_cclerk");
        {
            let mut s = state.write().await;
            s.unlocked = true;
        }
        (state, tmp)
    }

    async fn post_json(
        state: &NodeState,
        uri: &str,
        body: serde_json::Value,
    ) -> (StatusCode, serde_json::Value) {
        let app = routes().with_state(state.clone());
        let resp = app
            .oneshot(
                Request::builder()
                    .uri(uri)
                    .method("POST")
                    .header("content-type", "application/json")
                    .body(Body::from(body.to_string()))
                    .unwrap(),
            )
            .await
            .unwrap();
        let status = resp.status();
        let bytes = resp.into_body().collect().await.unwrap().to_bytes();
        (
            status,
            serde_json::from_slice(&bytes).unwrap_or(serde_json::json!({})),
        )
    }

    async fn post_bytes(
        state: &NodeState,
        uri: &str,
        body: Vec<u8>,
    ) -> (StatusCode, serde_json::Value) {
        let app = routes().with_state(state.clone());
        let resp = app
            .oneshot(
                Request::builder()
                    .uri(uri)
                    .method("POST")
                    .header("content-type", "application/octet-stream")
                    .body(Body::from(body))
                    .unwrap(),
            )
            .await
            .unwrap();
        let status = resp.status();
        let bytes = resp.into_body().collect().await.unwrap().to_bytes();
        (
            status,
            serde_json::from_slice(&bytes).unwrap_or(serde_json::json!({})),
        )
    }

    async fn get_json(state: &NodeState, uri: &str) -> (StatusCode, serde_json::Value) {
        let app = routes().with_state(state.clone());
        let resp = app
            .oneshot(
                Request::builder()
                    .uri(uri)
                    .method("GET")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        let status = resp.status();
        let bytes = resp.into_body().collect().await.unwrap().to_bytes();
        (
            status,
            serde_json::from_slice(&bytes).unwrap_or(serde_json::json!({})),
        )
    }

    /// The four orders every live test clears. `reference_clear` is the shared plaintext rule;
    /// the encrypted path must land on the same `(p*, V*)` without any of these values ever
    /// reaching the node.
    fn family_orders() -> [Order; FAMILY_ORDERS] {
        [
            Order {
                side: Side::Bid,
                limit: 2,
                qty: 7,
            },
            Order {
                side: Side::Ask,
                limit: 1,
                qty: 4,
            },
            Order {
                side: Side::Bid,
                limit: 1,
                qty: 5,
            },
            Order {
                side: Side::Ask,
                limit: 2,
                qty: 6,
            },
        ]
    }

    fn trader_keys() -> Vec<TraderKey> {
        (0..FAMILY_ORDERS)
            .map(|i| TraderKey::from_bytes(&[0x51 + i as u8; 32]))
            .collect()
    }

    /// Build a session over HTTP and return `(session hex, the exact public material a trader
    /// needs)`.
    async fn open_session(state: &NodeState, keys: &[TraderKey]) -> (String, serde_json::Value) {
        let traders: Vec<String> = keys
            .iter()
            .map(|k| hex32(&k.verifying_key().to_bytes()))
            .collect();
        let (status, body) = post_json(
            state,
            "/market/dark-clearing/session",
            serde_json::json!({ "traders": traders }),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "session open: {body}");
        let session = body["session"]["session"].as_str().unwrap().to_string();
        (session, body)
    }

    /// TRADER-SIDE. Everything in this function happens in the caller's process; the plaintext
    /// `Order` is consumed by `encrypt_and_sign` and never crosses the wire.
    fn seal_order(
        session_wire: &serde_json::Value,
        trader: usize,
        order: &Order,
        key: &TraderKey,
    ) -> Vec<u8> {
        use base64::Engine as _;
        let params = BfvParams::fold_set();
        let pk_bytes = base64::engine::general_purpose::STANDARD
            .decode(
                session_wire["session"]["collective_public_key_b64"]
                    .as_str()
                    .expect("the node publishes the collective public key"),
            )
            .expect("base64");
        let collective =
            collective_public_key_from_bytes(&pk_bytes, &params).expect("collective key parses");
        let nonce = parse_hex32(
            "session",
            session_wire["session"]["session"].as_str().unwrap(),
        )
        .expect("session hex");
        let ingress = OrderIngressSession::new(nonce, FAMILY_BUCKETS, &params, &collective)
            .expect("the trader rebuilds the same ingress session");
        SignedOrderSubmission::encrypt_and_sign(
            &ingress,
            trader,
            0,
            order,
            &params,
            &collective,
            key,
        )
        .expect("trader-local signed encryption")
        .0
        .to_wire_bytes()
    }

    /// **THE HEADLINE.** A user submits four encrypted orders over the node's own HTTP surface
    /// and reads back exactly `(p*, V*)` — the same `(p*, V*)` the shared plaintext rule gives,
    /// with no plaintext order ever reaching the node.
    #[tokio::test(flavor = "multi_thread", worker_threads = 4)]
    async fn encrypted_orders_clear_over_http_and_reveal_only_p_star_and_v_star() {
        let (state, _tmp) = fresh_state().await;
        let keys = trader_keys();
        let (session, wire) = open_session(&state, &keys).await;
        assert_no_order_fields("session open", &wire);
        assert_eq!(wire["session"]["shape"]["order_slots"], 4u64);
        assert_eq!(wire["session"]["shape"]["price_buckets"], 4u64);
        assert_eq!(wire["session"]["shape"]["max_qty_declared"], 15u64);
        assert_eq!(wire["session"]["key_custodians"], KEY_CUSTODIANS as u64);
        assert_eq!(
            wire["session"]["opening_threshold"],
            OPENING_THRESHOLD as u64
        );

        let orders = family_orders();
        let expected = reference_clear(&orders, FAMILY_BUCKETS);

        for (trader, (order, key)) in orders.iter().zip(keys.iter()).enumerate() {
            let envelope = seal_order(&wire, trader, order, key);
            // The node's GLOBAL request-body limit is 1 MiB; an envelope that did not fit it
            // would be unsubmittable in production however generous this route's own bound is.
            assert!(
                envelope.len() < 1_024 * 1_024,
                "one encrypted order envelope is {} bytes — above the node's global body limit",
                envelope.len()
            );
            let (status, body) = post_bytes(
                &state,
                &format!("/market/dark-clearing/session/{session}/order"),
                envelope.clone(),
            )
            .await;
            assert_eq!(status, StatusCode::OK, "order {trader}: {body}");
            assert_no_order_fields("order accept", &body);
            assert_eq!(body["accepted_orders"], (trader + 1) as u64);
            // The receipt commits to the EXACT submitted envelope.
            assert_eq!(
                body["receipt"]["subject_digest"].as_str().unwrap(),
                hex32(blake3::hash(&envelope).as_bytes())
            );
            assert_eq!(body["receipt"]["kind"], "order_accepted");
        }

        let (status, body) = post_json(
            &state,
            &format!("/market/dark-clearing/session/{session}/clear"),
            serde_json::json!({}),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "clear: {body}");
        assert_no_order_fields("clear", &body);
        assert_eq!(
            body["result"]["p_star"].as_u64().map(|p| p as usize),
            expected.p_star,
            "the encrypted crossing must land on the shared uniform-price rule"
        );
        assert_eq!(
            body["result"]["v_star"].as_u64().unwrap(),
            u64::from(expected.v_star)
        );
        assert_eq!(body["result"]["certificate_verified"], true);
        assert_eq!(body["result"]["bound_inputs"], (2 * FAMILY_ORDERS) as u64);
        assert_eq!(body["result"]["quorum_threshold"], LIVE_PARTIES as u64);
        assert_eq!(body["result"]["bfv_custodians"], KEY_CUSTODIANS as u64);
        assert_eq!(
            body["result"]["bfv_opening_threshold"],
            OPENING_THRESHOLD as u64
        );
        assert_eq!(body["receipt"]["kind"], "cleared");

        let (status, read) = get_json(
            &state,
            &format!("/market/dark-clearing/session/{session}/result"),
        )
        .await;
        assert_eq!(status, StatusCode::OK, "result: {read}");
        assert_no_order_fields("result", &read);
        assert_eq!(read, body["result"]);

        // The receipt chain: open + 4 accepts + 1 clear, each committing to the previous.
        let guard = state.dark_clearing();
        let guard = guard.read().await;
        assert_eq!(guard.receipt_count(), 1 + FAMILY_ORDERS + 1);
        assert_eq!(guard.receipt_head().unwrap().kind, "cleared");
    }

    /// **NO NON-PARTICIPANT READ.** A signer outside the pinned roster cannot submit; a roster
    /// trader cannot submit as another seat; and no route of this surface hands anyone another
    /// trader's order, envelope, or ciphertext — because no such route exists.
    #[tokio::test(flavor = "multi_thread", worker_threads = 4)]
    async fn a_non_participant_can_neither_submit_nor_read_another_order() {
        let (state, _tmp) = fresh_state().await;
        let keys = trader_keys();
        let (session, wire) = open_session(&state, &keys).await;
        let orders = family_orders();

        // Trader 0 submits honestly.
        let envelope = seal_order(&wire, 0, &orders[0], &keys[0]);
        let (status, _) = post_bytes(
            &state,
            &format!("/market/dark-clearing/session/{session}/order"),
            envelope.clone(),
        )
        .await;
        assert_eq!(status, StatusCode::OK);

        // An OUTSIDER — a key that is on no roster seat — signs for seat 1.
        let outsider = TraderKey::from_bytes(&[0x99; 32]);
        let forged = seal_order(&wire, 1, &orders[1], &outsider);
        let (status, body) = post_bytes(
            &state,
            &format!("/market/dark-clearing/session/{session}/order"),
            forged,
        )
        .await;
        assert_eq!(
            status,
            StatusCode::FORBIDDEN,
            "a non-roster signer must not be seated: {body}"
        );
        assert_eq!(body["refused"], "ingress");

        // A SEATED trader signing for someone else's seat.
        let impersonation = seal_order(&wire, 2, &orders[2], &keys[3]);
        let (status, body) = post_bytes(
            &state,
            &format!("/market/dark-clearing/session/{session}/order"),
            impersonation,
        )
        .await;
        assert_eq!(
            status,
            StatusCode::FORBIDDEN,
            "seat 2 may only be filled by seat 2's key: {body}"
        );
        assert_eq!(body["refused"], "ingress");

        // REPLAY of trader 0's exact envelope.
        let (status, body) = post_bytes(
            &state,
            &format!("/market/dark-clearing/session/{session}/order"),
            envelope,
        )
        .await;
        assert_eq!(status, StatusCode::FORBIDDEN, "a replayed source: {body}");
        assert_eq!(body["refused"], "ingress");

        // THE READ SURFACE. Everything this session will ever disclose, and none of it is an
        // order. There is no per-order, per-trader, or ciphertext route to call.
        let (status, view) =
            get_json(&state, &format!("/market/dark-clearing/session/{session}")).await;
        assert_eq!(status, StatusCode::OK);
        assert_no_order_fields("session read", &view);
        assert_eq!(view["accepted_orders"], 1u64);
        for probe in [
            format!("/market/dark-clearing/session/{session}/order/0"),
            format!("/market/dark-clearing/session/{session}/orders"),
            format!("/market/dark-clearing/session/{session}/book"),
            format!("/market/dark-clearing/session/{session}/curves"),
        ] {
            let (status, _) = get_json(&state, &probe).await;
            assert_eq!(
                status,
                StatusCode::NOT_FOUND,
                "`{probe}` must not exist — an order-revealing route is a defect, not a feature"
            );
        }
    }

    /// **THE COMMITTEE DEPENDENCY, RED.** Drop the live custodians below the opening threshold
    /// and the clear refuses, naming `committee`, with no outcome recorded and no degraded path.
    #[tokio::test(flavor = "multi_thread", worker_threads = 4)]
    async fn clearing_refuses_fail_closed_when_the_committee_is_short() {
        let (state, _tmp) = fresh_state().await;
        let keys = trader_keys();
        let (session, wire) = open_session(&state, &keys).await;
        let orders = family_orders();
        for (trader, (order, key)) in orders.iter().zip(keys.iter()).enumerate() {
            let envelope = seal_order(&wire, trader, order, key);
            let (status, body) = post_bytes(
                &state,
                &format!("/market/dark-clearing/session/{session}/order"),
                envelope,
            )
            .await;
            assert_eq!(status, StatusCode::OK, "order {trader}: {body}");
        }

        // Two of four custodians remain: below the 3-of-4 opening threshold.
        let nonce = parse_hex32("session", &session).unwrap();
        {
            let clearing = state.dark_clearing();
            let mut guard = clearing.write().await;
            assert!(guard.force_custodians_offline(&nonce, 2));
        }

        let (status, body) = post_json(
            &state,
            &format!("/market/dark-clearing/session/{session}/clear"),
            serde_json::json!({}),
        )
        .await;
        assert_eq!(status, StatusCode::SERVICE_UNAVAILABLE, "{body}");
        assert_eq!(body["refused"], "committee");
        assert_eq!(body["dependency"], true);

        // Nothing was recorded, and no result appeared.
        let (status, body) = get_json(
            &state,
            &format!("/market/dark-clearing/session/{session}/result"),
        )
        .await;
        assert_eq!(
            status,
            StatusCode::CONFLICT,
            "a refused clear yields no result"
        );
        assert_eq!(body["refused"], "not_cleared");
        // A further order submission is refused for the same named dependency.
        let (status, body) = post_bytes(
            &state,
            &format!("/market/dark-clearing/session/{session}/order"),
            vec![0u8; 8],
        )
        .await;
        assert_eq!(status, StatusCode::SERVICE_UNAVAILABLE, "{body}");
        assert_eq!(body["refused"], "committee");
    }

    /// **THE CERTIFICATE DEPENDENCY, RED.** Short the computation-integrity roster and the real
    /// `AuthenticatedQuorumVerifier` refuses. The clear runs its whole crypto path and then
    /// declines to publish an unattested outcome.
    #[tokio::test(flavor = "multi_thread", worker_threads = 4)]
    async fn clearing_refuses_fail_closed_without_a_quorum_certificate() {
        let (state, _tmp) = fresh_state().await;
        let keys = trader_keys();
        let (session, wire) = open_session(&state, &keys).await;
        let orders = family_orders();
        for (trader, (order, key)) in orders.iter().zip(keys.iter()).enumerate() {
            let envelope = seal_order(&wire, trader, order, key);
            let (status, body) = post_bytes(
                &state,
                &format!("/market/dark-clearing/session/{session}/order"),
                envelope,
            )
            .await;
            assert_eq!(status, StatusCode::OK, "order {trader}: {body}");
        }

        let nonce = parse_hex32("session", &session).unwrap();
        {
            let clearing = state.dark_clearing();
            let mut guard = clearing.write().await;
            assert!(guard.force_quorum_signers(&nonce, 2));
        }

        let (status, body) = post_json(
            &state,
            &format!("/market/dark-clearing/session/{session}/clear"),
            serde_json::json!({}),
        )
        .await;
        assert_eq!(status, StatusCode::SERVICE_UNAVAILABLE, "{body}");
        assert_eq!(body["refused"], "certificate");
        assert_eq!(body["dependency"], true);

        let (status, body) = get_json(
            &state,
            &format!("/market/dark-clearing/session/{session}/result"),
        )
        .await;
        assert_eq!(
            status,
            StatusCode::CONFLICT,
            "an unattested clear must publish nothing"
        );
        assert_eq!(body["refused"], "not_cleared");
    }

    /// **THE FAMILY GATE.** A roster that is not exactly the Lean-emitted `N` is refused, and so
    /// is an envelope whose declared plaintext bound exceeds the 4-bit ceiling.
    #[tokio::test(flavor = "multi_thread", worker_threads = 4)]
    async fn a_book_outside_the_emitted_family_is_refused() {
        let (state, _tmp) = fresh_state().await;
        let keys = trader_keys();

        for count in [3usize, 5] {
            let traders: Vec<String> = (0..count)
                .map(|i| {
                    hex32(
                        &TraderKey::from_bytes(&[0x30 + i as u8; 32])
                            .verifying_key()
                            .to_bytes(),
                    )
                })
                .collect();
            let (status, body) = post_json(
                &state,
                "/market/dark-clearing/session",
                serde_json::json!({ "traders": traders }),
            )
            .await;
            assert_eq!(status, StatusCode::BAD_REQUEST, "{count} traders: {body}");
            assert_eq!(body["refused"], "outside_family");
        }

        let (session, wire) = open_session(&state, &keys).await;
        // qty 16 is one above the 4-bit ceiling the emitted family fixes.
        let too_big = Order {
            side: Side::Bid,
            limit: 1,
            qty: 16,
        };
        let envelope = seal_order(&wire, 0, &too_big, &keys[0]);
        let (status, body) = post_bytes(
            &state,
            &format!("/market/dark-clearing/session/{session}/order"),
            envelope,
        )
        .await;
        assert_eq!(status, StatusCode::BAD_REQUEST, "{body}");
        assert_eq!(body["refused"], "outside_family");
        assert!(
            body["detail"].as_str().unwrap().contains("4-bit"),
            "the refusal must name the family bound it enforced: {}",
            body["detail"]
        );

        // An incomplete book does not clear.
        let (status, body) = post_json(
            &state,
            &format!("/market/dark-clearing/session/{session}/clear"),
            serde_json::json!({}),
        )
        .await;
        assert_eq!(status, StatusCode::CONFLICT, "{body}");
        assert_eq!(body["refused"], "book_incomplete");
    }

    /// **THE VERIFIED-CORE DEPENDENCY, RED, THROUGH THE HTTP SURFACE.** Point the family gate at
    /// a drifted emission and every entry point refuses `verified_core` — open, submit, clear and
    /// read alike. This is the same gate the live surface runs; only its input differs.
    #[tokio::test(flavor = "multi_thread", worker_threads = 4)]
    async fn every_entry_point_refuses_fail_closed_on_a_drifted_emitted_family() {
        let (state, _tmp) = fresh_state().await;
        let keys = trader_keys();
        // GREEN FIRST, so the red below is a change of behaviour and not a broken harness.
        let (session, _wire) = open_session(&state, &keys).await;

        // A renamed emission: same bytes, different family identity.
        static RENAMED: std::sync::OnceLock<String> = std::sync::OnceLock::new();
        let renamed: &'static str = RENAMED.get_or_init(|| {
            EMITTED_FAMILY_DESCRIPTOR.replacen(
                "dark-bazaar-private-n4k4::wide-poseidon2-v2",
                "dark-bazaar-private-n4k4::impostor",
                1,
            )
        });
        {
            let clearing = state.dark_clearing();
            let mut guard = clearing.write().await;
            guard.force_family_descriptor(renamed);
        }

        let traders: Vec<String> = keys
            .iter()
            .map(|k| hex32(&k.verifying_key().to_bytes()))
            .collect();
        let (status, body) = post_json(
            &state,
            "/market/dark-clearing/session",
            serde_json::json!({ "traders": traders }),
        )
        .await;
        assert_eq!(status, StatusCode::SERVICE_UNAVAILABLE, "open: {body}");
        assert_eq!(body["refused"], "verified_core");
        assert_eq!(body["dependency"], true);

        for (method, uri) in [
            ("GET", format!("/market/dark-clearing/session/{session}")),
            (
                "POST",
                format!("/market/dark-clearing/session/{session}/clear"),
            ),
        ] {
            let (status, body) = if method == "GET" {
                get_json(&state, &uri).await
            } else {
                post_json(&state, &uri, serde_json::json!({})).await
            };
            assert_eq!(
                status,
                StatusCode::SERVICE_UNAVAILABLE,
                "{method} {uri}: {body}"
            );
            assert_eq!(body["refused"], "verified_core");
        }

        let (status, body) = post_bytes(
            &state,
            &format!("/market/dark-clearing/session/{session}/order"),
            vec![0u8; 16],
        )
        .await;
        assert_eq!(status, StatusCode::SERVICE_UNAVAILABLE, "{body}");
        assert_eq!(body["refused"], "verified_core");
    }

    /// The archive is REPORTED, never required — and this test says out loud which state the
    /// build it runs in is in, so a reader is never left guessing.
    #[tokio::test(flavor = "multi_thread", worker_threads = 4)]
    async fn the_lean_archive_is_disclosed_and_is_not_a_gate() {
        let linked = dregg_lean_ffi::lean_available();
        eprintln!("dark-clearing: this build's Lean archive linked = {linked}");
        let (state, _tmp) = fresh_state().await;
        let keys = trader_keys();
        let (_session, wire) = open_session(&state, &keys).await;
        assert_eq!(
            wire["session"]["lean_archive_linked"],
            serde_json::Value::Bool(linked),
            "the surface must report this node's archive state honestly"
        );
    }

    /// The verified-core gate is a GATE: hand it a drifted emitted descriptor and it goes red,
    /// naming `verified_core`. This is the same code path the live surface runs, with a mutated
    /// artifact instead of the checked-in one.
    #[test]
    fn verified_core_gate_refuses_a_drifted_emitted_descriptor() {
        let good = EMITTED_FAMILY_DESCRIPTOR;
        assert!(
            verified_family_from_descriptor(good).is_ok(),
            "the checked-in Lean-emitted descriptor must pass its own gate"
        );

        let renamed = good.replacen(
            "dark-bazaar-private-n4k4::wide-poseidon2-v2",
            "dark-bazaar-private-n4k4::impostor",
            1,
        );
        let refusal = verified_family_from_descriptor(&renamed)
            .expect_err("a renamed family must not pass as the proven family");
        assert_eq!(refusal.dependency(), Some(ClearingDependency::VerifiedCore));

        let widened = good.replacen("\"trace_width\":181", "\"trace_width\":182", 1);
        let refusal = verified_family_from_descriptor(&widened)
            .expect_err("a drifted trace width must not pass");
        assert_eq!(refusal.dependency(), Some(ClearingDependency::VerifiedCore));

        let refusal = verified_family_from_descriptor("{not json")
            .expect_err("an unparseable descriptor must not pass");
        assert_eq!(refusal.dependency(), Some(ClearingDependency::VerifiedCore));
    }

    /// The family this surface advertises is the family Lean emitted, not a number typed here.
    #[test]
    fn advertised_family_is_the_emitted_family() {
        let shape = verified_family_from_descriptor(EMITTED_FAMILY_DESCRIPTOR)
            .expect("the emitted descriptor parses");
        assert_eq!(shape.order_slots, 4);
        assert_eq!(shape.price_buckets, 4);
        assert_eq!(shape.max_qty_declared, 15, "4-bit quantities");
        assert_eq!(shape.order_slots, FAMILY_ORDERS);
        assert_eq!(shape.price_buckets, FAMILY_BUCKETS);
    }

    /// A refusal's wire form must be self-describing: a client can tell a fail-closed dependency
    /// refusal from a shape refusal without string-matching a message.
    #[test]
    fn refusal_wire_marks_dependency_refusals() {
        for (refusal, expect_dependency, kind) in [
            (ClearingRefusal::committee("x"), true, "committee"),
            (ClearingRefusal::verified_core("x"), true, "verified_core"),
            (ClearingRefusal::certificate("x"), true, "certificate"),
            (
                ClearingRefusal::OutsideFamily("x".into()),
                false,
                "outside_family",
            ),
            (ClearingRefusal::Ingress("x".into()), false, "ingress"),
        ] {
            let wire = ClearingRefusalWire::from(&refusal);
            assert_eq!(wire.dependency, expect_dependency);
            assert_eq!(wire.refused, kind);
            assert_eq!(wire.family, CLEARING_FAMILY);
            assert!(!wire.disclosure.is_empty());
            assert_eq!(
                refusal.status() == StatusCode::SERVICE_UNAVAILABLE,
                expect_dependency,
                "a dependency refusal is an unavailability, not a client error"
            );
        }
    }

    /// The receipt chain is a chain: each link commits to the previous hash.
    #[test]
    fn receipts_chain() {
        let mut clearing = NodeDarkClearing::new();
        let session = [7u8; 32];
        let first = clearing.cut_receipt("session_open", session, 0, None);
        assert!(first.previous_receipt_hash.is_none());
        let second = clearing.cut_receipt("order_accepted", session, 1, Some([1u8; 32]));
        assert_eq!(
            second.previous_receipt_hash.as_deref(),
            Some(first.receipt_hash.as_str())
        );
        assert_ne!(first.receipt_hash, second.receipt_hash);
        assert_eq!(clearing.receipt_count(), 2);
        assert_eq!(
            clearing.receipt_head().map(|r| r.sequence),
            Some(1),
            "the head is the latest link"
        );
    }

    /// No response type of this surface can carry an order field. This is a structural check on
    /// the serialized shapes, so a future field named `side`/`limit`/`qty`/`ciphertext` on any of
    /// them turns this test red.
    #[test]
    fn no_response_shape_can_carry_an_order() {
        let receipt = ClearingReceipt {
            kind: "order_accepted".into(),
            session: hex32(&[3u8; 32]),
            sequence: 1,
            accepted_orders: 1,
            subject_digest: Some(hex32(&[4u8; 32])),
            previous_receipt_hash: None,
            receipt_hash: hex32(&[5u8; 32]),
            family: CLEARING_FAMILY,
        };
        let result = ClearedResultWire {
            session: hex32(&[3u8; 32]),
            family: CLEARING_FAMILY,
            p_star: Some(2),
            v_star: 7,
            claim_digest: hex32(&[6u8; 32]),
            envelope_digest: hex32(&[7u8; 32]),
            quorum_roster_digest: hex32(&[8u8; 32]),
            quorum_threshold: LIVE_PARTIES,
            bfv_custodians: KEY_CUSTODIANS as u64,
            bfv_opening_threshold: OPENING_THRESHOLD as u64,
            bound_inputs: 8,
            certificate_verified: true,
            disclosure: CLEARING_DISCLOSURE,
        };
        for value in [
            serde_json::to_value(&receipt).unwrap(),
            serde_json::to_value(&result).unwrap(),
        ] {
            let object = value.as_object().expect("a JSON object");
            for forbidden in [
                "side",
                "limit",
                "qty",
                "quantity",
                "order",
                "orders",
                "ciphertext",
                "trader",
                "trader_index",
                "demand",
                "supply",
                "curve",
            ] {
                assert!(
                    !object.contains_key(forbidden),
                    "a dark-clearing response must never carry `{forbidden}`"
                );
            }
        }
    }
}
