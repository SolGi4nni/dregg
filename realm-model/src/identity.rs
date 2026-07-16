//! §9.5 — Canonical identity, surfaces DERIVE from it (not the reverse).
//!
//! > Do NOT make the first Discord ID the world identity. [...] The surface IDs
//! > (Discord user, WeChat OpenID, a web session) DERIVE from / bind to it, not
//! > the reverse.
//!
//! The object a `shared_world` key-ceremony participant should resolve TO.
//!
//! ## The direction is the whole point
//!
//! A [`CanonicalIdentity`] is a durable object minted from a principal key. It
//! exists FIRST. A [`SurfaceRef`] (a Discord user id, a web session, a WeChat
//! OpenID) is bound onto an already-existing canonical identity: the binding is
//! a real cell whose *entire state* is the canonical id it points at. Resolving
//! a surface reads that cell → the canonical id. There is deliberately NO
//! `identity_from_surface(discord_id)` constructor: a surface can only be bound
//! to a canonical identity that was minted independently, so the surface is
//! DERIVED (points at) and the canonical identity is PRIMARY.
//!
//! Because the binding cell's state literally holds the canonical id, two
//! different surfaces bound to the same identity resolve to the SAME 32 bytes —
//! that is "one identity across surfaces", cell-backed and non-vacuous.

use dregg_cell::CellId;
use dregg_turn::pq::{MlDsaTurnKey, ml_dsa_verify};
use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};

/// Field slots the canonical-identity cell stamps. The identity cell is a
/// DURABLE CELL whose state NAMES the current key (ember's DECIDED hybrid-PQ
/// identity): its `id` is the stable durable principal, its state advances as
/// keys succeed one another. The id NEVER changes on rotation — that is the
/// durable-principal property surviving a key change.
pub mod field {
    /// The succession epoch: 1 at genesis, +1 on every rotation/recovery. The
    /// "height" of the succession chain.
    pub const EPOCH: usize = 0;
    /// The commitment to the CURRENT key ([`commit_hybrid`] of the current
    /// ed25519 + ML-DSA public keys). A resolver reads THIS to reach the current
    /// key; a succession advances it under authority.
    pub const KEY_COMMIT: usize = 1;
    /// The number of registered guardians (recovery quorum size N).
    pub const GUARDIAN_COUNT: usize = 2;
    /// The recovery threshold K (K-of-N guardians may co-sign a recovery).
    pub const GUARDIAN_THRESHOLD: usize = 3;
}

/// Domain-separation for the current-key commitment stamped on an identity cell.
const HYBRID_COMMIT_CTX: &str = "realm-model:hybrid-key-commit-v1";
/// Domain-separation for the canonical succession/recovery signing message.
const SUCCESSION_MSG_CTX: &[u8] = b"realm-model:succession-v1";

/// The commitment to a hybrid (ed25519 + ML-DSA-65) public key pair — the value
/// an identity cell stores in [`field::KEY_COMMIT`]. A succession supplies the
/// signer's raw public keys; the gate recomputes this commitment and checks it
/// against the cell's committed value, so a stranger cannot substitute their own
/// keys (the anti-forgery tooth — the cell commits to keys, not raw sigs).
pub fn commit_hybrid(ed_pk: &[u8; 32], ml_pk: &[u8]) -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key(HYBRID_COMMIT_CTX);
    h.update(ed_pk);
    h.update(&(ml_pk.len() as u64).to_le_bytes());
    h.update(ml_pk);
    *h.finalize().as_bytes()
}

/// Derive the deterministic 32-byte hybrid seed for a principal-seed string —
/// the single 32-byte seed BOTH the ed25519 AND the ML-DSA-65 key derive from
/// (exactly the sdk-ts / sdk-py posture: `ML-DSA.KeyGen(ξ = seed)`). Public so a
/// caller (or a driven test) that knows the principal seed can reconstruct the
/// current key to sign a succession.
pub fn hybrid_seed(principal_seed: &str) -> [u8; 32] {
    *blake3::hash(format!("realm-identity-seed:{principal_seed}").as_bytes()).as_bytes()
}

/// A hybrid identity key: ed25519 + ML-DSA-65, BOTH derived from ONE 32-byte
/// seed — the shipped hybrid signer posture (`turn/src/pq.rs`
/// [`MlDsaTurnKey::from_ed25519_seed`], `ML-DSA.KeyGen(ξ = seed)`, ctx
/// `dregg-hybrid-turn-v1`; ed25519 from the same seed bytes). A succession turn
/// is signed by BOTH halves (quantum-safe identity: forging a succession
/// requires breaking ed25519 discrete-log AND module-lattice SIS/LWE).
#[derive(Clone)]
pub struct HybridKey {
    ed: SigningKey,
    ml: MlDsaTurnKey,
    ed_pk: [u8; 32],
    ml_pk: Vec<u8>,
}

impl core::fmt::Debug for HybridKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "HybridKey(commit={})", hex32(&self.commitment()))
    }
}

impl HybridKey {
    /// Derive BOTH keys from one 32-byte seed (the whole point — one seed, a
    /// classical AND a post-quantum key that agree with no separate ceremony).
    pub fn from_seed(seed: &[u8; 32]) -> Self {
        let ed = SigningKey::from_bytes(seed);
        let ml = MlDsaTurnKey::from_ed25519_seed(seed);
        let ed_pk = ed.verifying_key().to_bytes();
        let ml_pk = ml.public_bytes();
        HybridKey {
            ed,
            ml,
            ed_pk,
            ml_pk,
        }
    }

    /// Derive from a principal-seed string (via [`hybrid_seed`]).
    pub fn from_principal_seed(principal_seed: &str) -> Self {
        Self::from_seed(&hybrid_seed(principal_seed))
    }

    /// The ed25519 public key.
    pub fn ed_pk(&self) -> [u8; 32] {
        self.ed_pk
    }

    /// The serialized ML-DSA-65 public key.
    pub fn ml_pk(&self) -> &[u8] {
        &self.ml_pk
    }

    /// This key's commitment (what an identity cell stores in [`field::KEY_COMMIT`]).
    pub fn commitment(&self) -> [u8; 32] {
        commit_hybrid(&self.ed_pk, &self.ml_pk)
    }

    /// Hybrid-sign `message`: BOTH the ed25519 and the ML-DSA-65 halves over the
    /// SAME canonical message, carrying the signer's public keys so the verifier
    /// is self-contained (the shipped hybrid-envelope shape). `None` only on the
    /// vanishingly rare internal ML-DSA failure.
    pub fn sign(&self, message: &[u8]) -> Option<HybridSig> {
        let ed_sig = self.ed.sign(message).to_bytes();
        let ml_sig = self.ml.sign(message)?;
        Some(HybridSig {
            ed_pk: self.ed_pk,
            ml_pk: self.ml_pk.clone(),
            ed_sig,
            ml_sig,
        })
    }
}

/// A hybrid signature: the signer's public keys + BOTH signature halves over one
/// canonical message. Self-contained (carries the keys), exactly like the hybrid
/// turn envelope during the staged rollout.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HybridSig {
    pub ed_pk: [u8; 32],
    pub ml_pk: Vec<u8>,
    pub ed_sig: [u8; 64],
    pub ml_sig: Vec<u8>,
}

impl HybridSig {
    /// The commitment to the SIGNER's key pair — checked against the identity
    /// cell's committed key (or membership in the guardian set). This is what
    /// stops a stolen-identity forgery: a wrong key produces a wrong commitment.
    pub fn signer_commitment(&self) -> [u8; 32] {
        commit_hybrid(&self.ed_pk, &self.ml_pk)
    }

    /// Verify BOTH halves over `message` (`classical ∧ pq`). A present-but-invalid
    /// half fails the whole check (fail-closed) — the shipped hybrid posture.
    pub fn verify(&self, message: &[u8]) -> bool {
        let Ok(vk) = VerifyingKey::from_bytes(&self.ed_pk) else {
            return false;
        };
        let ed_ok = vk
            .verify(message, &Signature::from_bytes(&self.ed_sig))
            .is_ok();
        let pq_ok = ml_dsa_verify(&self.ml_pk, message, &self.ml_sig);
        ed_ok && pq_ok
    }
}

/// How a succession was authorized — recorded on the chain so an auditor can see
/// whether the current key or a guardian quorum moved the identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SuccessionKind {
    /// Genesis (the birth key; no predecessor signed it).
    Genesis,
    /// A rotation signed by the OLD (then-current) key.
    SelfSigned,
    /// A recovery co-signed by a guardian threshold (the old key did NOT sign —
    /// a lost key is not a lost identity).
    GuardianRecovery,
}

/// One link in an identity's succession chain: the key commitment moved from
/// `from` to `to` at `epoch`, under `kind`. A resolver following the chain from
/// genesis reaches the current key; the chain OUTLIVES any single key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SuccessionRecord {
    pub epoch: u64,
    pub from: [u8; 32],
    pub to: [u8; 32],
    pub kind: SuccessionKind,
}

/// The canonical message BOTH halves sign for a succession — binds the identity
/// cell, the epoch being advanced FROM, the outgoing + incoming key commitments,
/// and the succession kind, so a signature over one succession cannot be
/// replayed onto another (different identity, epoch, target key, or kind).
pub fn succession_message(
    identity: &CellId,
    epoch: u64,
    from: &[u8; 32],
    to: &[u8; 32],
    kind: SuccessionKind,
) -> Vec<u8> {
    let mut h = blake3::Hasher::new();
    h.update(SUCCESSION_MSG_CTX);
    h.update(identity.as_bytes());
    h.update(&epoch.to_le_bytes());
    h.update(from);
    h.update(to);
    h.update(&[match kind {
        SuccessionKind::Genesis => 0,
        SuccessionKind::SelfSigned => 1,
        SuccessionKind::GuardianRecovery => 2,
    }]);
    h.finalize().as_bytes().to_vec()
}

fn hex32(b: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for x in b {
        s.push_str(&format!("{x:02x}"));
    }
    s
}

/// The extended-field key a guardian commitment is listed under on the identity
/// cell (high bit forces `>= STATE_SLOTS`, into the committed `fields_map`). The
/// stored VALUE is the full commitment, so membership is a full-32-byte equality
/// (`get(key(G)) == G`), never an 8-byte-key coincidence — non-vacuous, exactly
/// like the ruleset catalog.
pub(crate) fn guardian_ext_key(commit: &[u8; 32]) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&commit[..8]);
    0x8000_0000_0000_0000u64 | u64::from_le_bytes(b)
}

/// A surface an actor arrives on. Engine-general: the model does not privilege
/// any one (there is no "Discord is the account"); each is a peer binding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Surface {
    Discord,
    Web,
    Telegram,
    WeChat,
    Native,
    /// An engine-general escape hatch for a surface the enum does not name yet.
    Other,
}

/// A reference to an actor AS SEEN on one surface: `(surface, surface-local id)`.
/// e.g. `(Discord, "user#12345")`, `(Web, "session-abcdef")`. This is the
/// per-surface identity `dreggnet-offerings`' viewer currently IS — the thing
/// this model resolves to a canonical identity.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SurfaceRef {
    pub surface: Surface,
    pub local: String,
}

impl SurfaceRef {
    pub fn new(surface: Surface, local: impl Into<String>) -> Self {
        SurfaceRef {
            surface,
            local: local.into(),
        }
    }

    /// The deterministic seed of the BINDING cell for this surface ref. A
    /// binding cell's state holds the canonical id it derives from.
    pub(crate) fn binding_seed(&self) -> String {
        format!("realm-surface-binding:{:?}:{}", self.surface, self.local)
    }
}

/// The canonical, durable principal. Usable across games, surfaces, and realms.
/// Its `id` is a stable cell handle; surface bindings, assets, authorship,
/// guilds, votes, and runs all resolve THROUGH this — the "one identity spine"
/// (§6) reduced to its irreducible core.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CanonicalIdentity {
    /// The durable cell handle. STABLE across surface rebindings AND key
    /// rotation/recovery — the id never changes when the key succeeds (the
    /// durable-principal property; ember's DECIDED hybrid-PQ succession). The
    /// CURRENT key lives in the cell's [`field::KEY_COMMIT`] state, not the id.
    pub id: CellId,
    /// The ed25519 public key of the BIRTH key (the first key of the succession
    /// chain). Informational — after a rotation the current key is named by the
    /// cell's [`field::KEY_COMMIT`], reached via the resolver.
    pub principal_pk: [u8; 32],
    /// The commitment ([`commit_hybrid`]) to the BIRTH hybrid key pair — the
    /// genesis anchor of the succession chain.
    pub birth_key_commit: [u8; 32],
    /// A human-meaningful label for the principal (NOT a surface id).
    pub label: String,
}
