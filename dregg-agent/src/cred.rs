//! The credential core — an attenuable, offline-verifiable, ed25519
//! caveat-chain authorization token.
//!
//! This is a faithful, wire-compatible port of breadstuffs
//! `dregg-auth::credential` (the `dga1_…` token scheme whose semantics are the
//! machine-checked ones in `metatheory/Dregg2/`). It is reproduced here rather
//! than depended-on so the dregg workspace builds **offline** and pulls **no
//! AGPL dregg git** into its default closure (the same licensing discipline the
//! `dregg-bridge` crate keeps for its dregg-verify lane). The construction is
//! identical: same BLAKE3 domain-separation contexts, same postcard/base64url
//! wire form (`dga1_` / `dgd1_`), so a credential minted by the breadstuffs
//! `dregg-auth` CLI / cipherclerk verifies here byte-for-byte, and vice versa.
//!
//! ## The shape (and its Lean counterparts)
//!
//! A [`Credential`] is a nonce plus an append-only ed25519 block chain. Each
//! block carries its caveats and the verifying key the *next* block signs
//! under; the root block verifies under the issuer's key. This is the biscuit
//! public-key delegation chain of `Dregg2.Authority.BiscuitGraph`.
//!
//! * **admit = the meet**: a credential admits a request iff *all* caveats of
//!   *all* blocks are satisfied (`Token.admits`, fail-closed);
//! * **attenuate = append**: [`Credential::attenuate`] appends one block
//!   (`Token.attenuate`); `attenuate_subset` proves the admitted set can only
//!   SHRINK. There is no removal API, and the signature chain + the
//!   proof-of-possession check make block removal unforgeable on the wire.

use base64::Engine;
use base64::engine::general_purpose::URL_SAFE_NO_PAD;
use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};
use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// Domain-separation contexts (versioned with the wire prefix; bump together).
// IDENTICAL strings to breadstuffs dregg-auth so signed digests agree.
// ---------------------------------------------------------------------------
const BLOCK_CTX: &str = "dregg-auth v1 block";
const TAIL_CTX: &str = "dregg-auth v1 tail";
const DISCHARGE_CTX: &str = "dregg-auth v1 discharge";

/// Version prefix of an encoded credential.
pub const CREDENTIAL_PREFIX: &str = "dga1_";
/// Version prefix of an encoded discharge.
pub const DISCHARGE_PREFIX: &str = "dgd1_";

// ===========================================================================
// Keys
// ===========================================================================

/// A public (verifying) key — 32 ed25519 bytes. What a verifier holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PublicKey(pub [u8; 32]);

impl PublicKey {
    /// Render as lowercase hex (the publishable form).
    pub fn to_hex(&self) -> String {
        hex(&self.0)
    }
    /// Parse from the hex form.
    pub fn from_hex(s: &str) -> Result<Self, KeyError> {
        Ok(PublicKey(unhex32(s.trim())?))
    }
}

/// A key could not be parsed.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[error("invalid key: {0}")]
pub struct KeyError(pub String);

fn fresh_signing_key() -> SigningKey {
    let mut seed = [0u8; 32];
    getrandom::fill(&mut seed).expect("operating-system randomness is available");
    SigningKey::from_bytes(&seed)
}

/// The minting authority: an ed25519 keypair. The private half mints; the
/// public half ([`RootKey::public`]) is all a verifier ever needs — offline.
pub struct RootKey {
    key: SigningKey,
}

impl RootKey {
    /// Generate a fresh root from operating-system randomness.
    pub fn generate() -> Self {
        Self {
            key: fresh_signing_key(),
        }
    }
    /// Deterministic construction from a 32-byte seed (tests, derivation).
    pub fn from_seed(seed: [u8; 32]) -> Self {
        Self {
            key: SigningKey::from_bytes(&seed),
        }
    }
    /// Reconstruct a root from a hex-encoded 32-byte seed.
    pub fn from_seed_hex(s: &str) -> Result<Self, KeyError> {
        Ok(Self::from_seed(unhex32(s.trim())?))
    }
    /// The 32-byte secret seed (store it where the root keeps secrets).
    pub fn secret_bytes(&self) -> [u8; 32] {
        self.key.to_bytes()
    }
    /// The hex secret seed.
    pub fn secret_hex(&self) -> String {
        hex(&self.key.to_bytes())
    }
    /// The public key verifiers use.
    pub fn public(&self) -> PublicKey {
        PublicKey(self.key.verifying_key().to_bytes())
    }
    /// Mint a root credential carrying `caveats` (the root grant).
    pub fn mint(&self, caveats: impl IntoIterator<Item = Caveat>) -> Credential {
        let mut nonce = [0u8; 32];
        getrandom::fill(&mut nonce).expect("operating-system randomness is available");
        let caveats: Vec<Caveat> = caveats.into_iter().collect();
        let next = fresh_signing_key();
        let next_pub = next.verifying_key().to_bytes();
        let msg = block_digest(&nonce, &caveats, &next_pub);
        let sig = self.key.sign(&msg).to_bytes();
        Credential {
            nonce,
            blocks: vec![Block {
                caveats,
                next_pub,
                sig,
            }],
            proof: next,
        }
    }
}

/// A third-party gateway's keypair: it signs [`Discharge`] tokens for the
/// caveats that name its [`GatewayKey::public`] key.
pub struct GatewayKey {
    key: SigningKey,
}

impl GatewayKey {
    pub fn generate() -> Self {
        Self {
            key: fresh_signing_key(),
        }
    }
    pub fn from_seed(seed: [u8; 32]) -> Self {
        Self {
            key: SigningKey::from_bytes(&seed),
        }
    }
    pub fn public(&self) -> PublicKey {
        PublicKey(self.key.verifying_key().to_bytes())
    }
    /// Issue a discharge for `caveat_id`, **bound** to the credential whose
    /// [`Credential::tail`] is `bound_to`.
    pub fn discharge(
        &self,
        caveat_id: impl Into<Vec<u8>>,
        bound_to: [u8; 32],
        caveats: impl IntoIterator<Item = Pred>,
    ) -> Discharge {
        let caveat_id = caveat_id.into();
        let caveats: Vec<Pred> = caveats.into_iter().collect();
        let msg = discharge_digest(&caveat_id, &caveats, Some(&bound_to));
        let sig = self.key.sign(&msg).to_bytes();
        Discharge {
            caveat_id,
            caveats,
            binding: Some(bound_to),
            sig,
        }
    }
}

// ===========================================================================
// Predicate algebra (Dregg2.Exec.PredAlgebra.Pred)
// ===========================================================================

/// Why a predicate could not be evaluated: the context failed to bind data the
/// predicate mentions. Always a refusal at the top level — missing data is
/// never `false` (so [`Pred::Not`] can never convert absence into authority).
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum Unbound {
    #[error("the context supplies no clock, and the caveat is temporal")]
    Clock,
    #[error("the context does not bind attribute `{0}`")]
    Attr(String),
}

/// A first-party caveat predicate over the verification [`Context`]. Variant
/// order is load-bearing — it IS the postcard discriminant, so it must match
/// breadstuffs `dregg-auth` exactly for wire compatibility.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Pred {
    /// Top — admits everything. Lean: `Pred.tt`.
    True,
    /// Bottom — admits nothing. Lean: `Pred.ff`.
    False,
    /// Attribute equality. Lean: `SimpleConstraint.fieldEquals`.
    AttrEq { key: String, value: String },
    /// Attribute prefix containment. Lean: `SimpleConstraint.prefixOf`.
    AttrPrefix { key: String, prefix: String },
    /// Admit iff `clock >= at` (vesting). Lean: `TemporalAtom.afterHeight`.
    NotBefore { at: u64 },
    /// Admit iff `clock <= at` (expiry). Lean: `TemporalAtom.beforeHeight`.
    NotAfter { at: u64 },
    /// Admit iff `not_before <= clock <= not_after`. Lean: `withinWindow`.
    Within { not_before: u64, not_after: u64 },
    /// n-ary conjunction (empty ⇒ true). Lean: `Pred.allOf`.
    AllOf(Vec<Pred>),
    /// n-ary disjunction (empty ⇒ FALSE, fail-closed). Lean: `Pred.anyOf`.
    AnyOf(Vec<Pred>),
    /// Negation at every level. Lean: `Pred.not`.
    Not(Box<Pred>),
}

impl Pred {
    /// Evaluate against a context — the executable mirror of the Lean
    /// `Pred.eval` fold; three-valued only in that unbound data yields
    /// `Err(Unbound)` rather than `false` (fail-closed even under `Not`).
    pub fn eval(&self, ctx: &Context) -> Result<bool, Unbound> {
        match self {
            Pred::True => Ok(true),
            Pred::False => Ok(false),
            Pred::AttrEq { key, value } => match ctx.lookup_attr(key) {
                Some(v) => Ok(v == value),
                None => Err(Unbound::Attr(key.clone())),
            },
            Pred::AttrPrefix { key, prefix } => match ctx.lookup_attr(key) {
                Some(v) => Ok(v.starts_with(prefix.as_str())),
                None => Err(Unbound::Attr(key.clone())),
            },
            Pred::NotBefore { at } => Ok(*at <= ctx.clock().ok_or(Unbound::Clock)?),
            Pred::NotAfter { at } => Ok(ctx.clock().ok_or(Unbound::Clock)? <= *at),
            Pred::Within {
                not_before,
                not_after,
            } => {
                let clock = ctx.clock().ok_or(Unbound::Clock)?;
                Ok(*not_before <= clock && clock <= *not_after)
            }
            Pred::AllOf(ps) => {
                for p in ps {
                    if !p.eval(ctx)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Pred::AnyOf(ps) => {
                for p in ps {
                    if p.eval(ctx)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Pred::Not(p) => Ok(!p.eval(ctx)?),
        }
    }

    /// One-line human prose for this predicate.
    pub fn explain(&self) -> String {
        match self {
            Pred::True => "always".to_string(),
            Pred::False => "never".to_string(),
            Pred::AttrEq { key, value } => format!("attribute `{key}` = `{value}`"),
            Pred::AttrPrefix { key, prefix } => {
                format!("attribute `{key}` starts with `{prefix}`")
            }
            Pred::NotBefore { at } => format!("not before clock {at} (vesting gate)"),
            Pred::NotAfter { at } => format!("not after clock {at} (expiry gate)"),
            Pred::Within {
                not_before,
                not_after,
            } => {
                format!("within clock window [{not_before}, {not_after}]")
            }
            Pred::AllOf(ps) if ps.is_empty() => "all of () — no constraint".to_string(),
            Pred::AllOf(ps) => format!("all of ({})", explain_list(ps)),
            Pred::AnyOf(ps) if ps.is_empty() => "any of () — refuses (fail-closed)".to_string(),
            Pred::AnyOf(ps) => format!("any of ({})", explain_list(ps)),
            Pred::Not(p) => format!("not ({})", p.explain()),
        }
    }
}

fn explain_list(ps: &[Pred]) -> String {
    ps.iter().map(Pred::explain).collect::<Vec<_>>().join("; ")
}

// ===========================================================================
// Caveat + Context (Dregg2.Authority.Caveat)
// ===========================================================================

/// One caveat installed on a credential block. Variant order IS the postcard
/// discriminant — must match breadstuffs `dregg-auth` (FirstParty=0, ThirdParty=1).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Caveat {
    /// A first-party caveat: a [`Pred`] over the verification context.
    FirstParty(Pred),
    /// A third-party caveat: verification additionally requires a [`Discharge`]
    /// token signed by `gateway` and **bound to this exact credential**.
    ThirdParty {
        gateway: [u8; 32],
        caveat_id: Vec<u8>,
        hint: String,
    },
}

impl Caveat {
    pub fn explain(&self) -> String {
        match self {
            Caveat::FirstParty(p) => format!("requires {}", p.explain()),
            Caveat::ThirdParty {
                gateway,
                caveat_id,
                hint,
            } => format!(
                "requires third-party approval from gateway {} for caveat id {}{}",
                hex(&gateway[..8]),
                hex(caveat_id),
                if hint.is_empty() {
                    String::new()
                } else {
                    format!(" ({hint:?})")
                }
            ),
        }
    }
}

/// The verification context — the request facts a caveat is evaluated against,
/// plus the presented third-party discharges. Supplied entirely by the caller:
/// verification is offline and deterministic.
#[derive(Clone, Debug, Default)]
pub struct Context {
    clock: Option<u64>,
    attrs: std::collections::BTreeMap<String, String>,
    discharges: Vec<Discharge>,
}

impl Context {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn at(mut self, clock: u64) -> Self {
        self.clock = Some(clock);
        self
    }
    pub fn attr(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.attrs.insert(key.into(), value.into());
        self
    }
    pub fn discharge(mut self, d: Discharge) -> Self {
        self.discharges.push(d);
        self
    }
    fn clock(&self) -> Option<u64> {
        self.clock
    }
    fn lookup_attr(&self, key: &str) -> Option<&str> {
        self.attrs.get(key).map(String::as_str)
    }
    fn discharges(&self) -> &[Discharge] {
        &self.discharges
    }
}

// ===========================================================================
// The chain (Dregg2.Authority.BiscuitGraph)
// ===========================================================================

#[derive(Clone, Debug)]
struct Block {
    caveats: Vec<Caveat>,
    next_pub: [u8; 32],
    sig: [u8; 64],
}

/// An attenuable, offline-verifiable credential — the token. Bearer semantics:
/// whoever holds the encoded form holds the authority it names (narrowed by its
/// caveats) *and* the ability to attenuate further (the carried tail key).
pub struct Credential {
    nonce: [u8; 32],
    blocks: Vec<Block>,
    /// The tail private key (matching the last block's `next_pub`).
    proof: SigningKey,
}

impl std::fmt::Debug for Credential {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Credential")
            .field("nonce", &hex(&self.nonce))
            .field("blocks", &self.blocks.len())
            .field("proof", &"<bearer key redacted>")
            .finish()
    }
}

impl Credential {
    /// Append caveats — the ONLY mutation, and it can only narrow
    /// (`Token.attenuate`, `attenuate_subset`).
    #[must_use = "attenuate returns the narrowed credential"]
    pub fn attenuate(mut self, caveats: impl IntoIterator<Item = Caveat>) -> Credential {
        let caveats: Vec<Caveat> = caveats.into_iter().collect();
        let next = fresh_signing_key();
        let next_pub = next.verifying_key().to_bytes();
        let prev_sig = self
            .blocks
            .last()
            .expect("a credential has a root block")
            .sig;
        let msg = block_digest(&prev_sig, &caveats, &next_pub);
        let sig = self.proof.sign(&msg).to_bytes();
        self.blocks.push(Block {
            caveats,
            next_pub,
            sig,
        });
        self.proof = next;
        self
    }

    /// The credential's **tail**: BLAKE3 of the final block signature. Since
    /// every block signs over its parent's signature, the tail commits the
    /// whole chain. A [`Discharge`] binds to this.
    pub fn tail(&self) -> [u8; 32] {
        let last = self.blocks.last().expect("a credential has a root block");
        let mut h = blake3::Hasher::new_derive_key(TAIL_CTX);
        h.update(&last.sig);
        *h.finalize().as_bytes()
    }

    /// The credential's tail commitment as lowercase hex — the canonical,
    /// per-credential identifier a revocation deny-set keys on (the cloud-side
    /// analogue of `Effect::RevokeCapability`: kill THIS exact session token).
    pub fn tail_hex(&self) -> String {
        hex(&self.tail())
    }

    /// The value of the first first-party `AttrEq { key, .. }` caveat across all
    /// blocks, if any. Used to read the stable `acct` account-id claim a session
    /// credential carries (the re-anchor: the subject is a key-derived account
    /// id, not the credential tail). Returns the value the *root* block stamped
    /// (attenuation can only append narrower caveats, never change this).
    pub fn first_attr(&self, key: &str) -> Option<String> {
        for (_, caveat) in self.caveats() {
            if let Caveat::FirstParty(Pred::AttrEq { key: k, value }) = caveat {
                if k == key {
                    return Some(value.clone());
                }
            }
        }
        None
    }

    fn caveats(&self) -> impl Iterator<Item = (usize, &Caveat)> {
        self.blocks
            .iter()
            .enumerate()
            .flat_map(|(i, b)| b.caveats.iter().map(move |c| (i, c)))
    }

    /// Verify against the issuer's public key + a caller-supplied [`Context`] —
    /// fully offline, fail-closed: (1) proof-of-possession, (2) the ed25519
    /// signature chain from `root` down, (3) the meet of every caveat.
    pub fn verify(&self, root: &PublicKey, ctx: &Context) -> Result<(), Refusal> {
        let last = self.blocks.last().expect("a credential has a root block");
        if self.proof.verifying_key().to_bytes() != last.next_pub {
            return Err(Refusal::ProofMismatch);
        }
        let mut vkey =
            VerifyingKey::from_bytes(&root.0).map_err(|_| Refusal::MalformedKey { block: 0 })?;
        let mut prev: Option<[u8; 64]> = None;
        for (i, block) in self.blocks.iter().enumerate() {
            let msg = match prev {
                None => block_digest(&self.nonce, &block.caveats, &block.next_pub),
                Some(ps) => block_digest(&ps, &block.caveats, &block.next_pub),
            };
            let sig = Signature::from_bytes(&block.sig);
            vkey.verify(&msg, &sig)
                .map_err(|_| Refusal::BadSignature { block: i })?;
            vkey = VerifyingKey::from_bytes(&block.next_pub)
                .map_err(|_| Refusal::MalformedKey { block: i })?;
            prev = Some(block.sig);
        }
        let tail = self.tail();
        for (block, caveat) in self.caveats() {
            match caveat {
                Caveat::FirstParty(p) => match p.eval(ctx) {
                    Ok(true) => {}
                    Ok(false) => {
                        return Err(Refusal::CaveatRefused {
                            block,
                            requires: p.explain(),
                        });
                    }
                    Err(unbound) => {
                        return Err(Refusal::ContextIncomplete {
                            block,
                            requires: p.explain(),
                            unbound,
                        });
                    }
                },
                Caveat::ThirdParty {
                    gateway, caveat_id, ..
                } => {
                    verify_discharged(gateway, caveat_id, &tail, ctx, block)?;
                }
            }
        }
        Ok(())
    }

    /// Human-readable terms, block by block, ending with the canonical tail tag.
    pub fn explain(&self) -> String {
        let mut out = format!("credential ({} block(s))\n", self.blocks.len());
        for (i, block) in self.blocks.iter().enumerate() {
            let role = if i == 0 { "root grant" } else { "attenuation" };
            out.push_str(&format!("  block {i} ({role}): "));
            if block.caveats.is_empty() {
                out.push_str("no caveats (key rotation only)");
            } else {
                out.push_str(
                    &block
                        .caveats
                        .iter()
                        .map(Caveat::explain)
                        .collect::<Vec<_>>()
                        .join("; "),
                );
            }
            out.push('\n');
        }
        out.push_str(&format!("  [tail {}]", hex(&self.tail())));
        out
    }
}

fn verify_discharged(
    gateway: &[u8; 32],
    caveat_id: &[u8],
    tail: &[u8; 32],
    ctx: &Context,
    block: usize,
) -> Result<(), Refusal> {
    let mut first_failure: Option<Refusal> = None;
    let mut saw_candidate = false;
    for d in ctx.discharges() {
        if d.caveat_id != caveat_id {
            continue;
        }
        saw_candidate = true;
        match d.verify_against(gateway, tail, ctx) {
            Ok(()) => return Ok(()),
            Err(r) => {
                first_failure.get_or_insert(r);
            }
        }
    }
    if saw_candidate {
        Err(first_failure.expect("a candidate that did not succeed recorded a failure"))
    } else {
        Err(Refusal::MissingDischarge {
            block,
            caveat_id: hex(caveat_id),
            gateway: hex(&gateway[..8]),
        })
    }
}

/// A third-party discharge token: a gateway's signed, **bound** approval.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Discharge {
    caveat_id: Vec<u8>,
    caveats: Vec<Pred>,
    binding: Option<[u8; 32]>,
    sig: [u8; 64],
}

impl Discharge {
    pub fn from_parts(
        caveat_id: Vec<u8>,
        caveats: Vec<Pred>,
        binding: Option<[u8; 32]>,
        sig: [u8; 64],
    ) -> Self {
        Self {
            caveat_id,
            caveats,
            binding,
            sig,
        }
    }
    pub fn caveat_id(&self) -> &[u8] {
        &self.caveat_id
    }
    fn verify_against(
        &self,
        gateway: &[u8; 32],
        tail: &[u8; 32],
        ctx: &Context,
    ) -> Result<(), Refusal> {
        match self.binding {
            None => {
                return Err(Refusal::UnboundDischarge {
                    caveat_id: hex(&self.caveat_id),
                });
            }
            Some(bound) if &bound != tail => {
                return Err(Refusal::DischargeBoundElsewhere {
                    caveat_id: hex(&self.caveat_id),
                });
            }
            Some(_) => {}
        }
        let vkey = VerifyingKey::from_bytes(gateway).map_err(|_| Refusal::MalformedGatewayKey)?;
        let msg = discharge_digest(&self.caveat_id, &self.caveats, self.binding.as_ref());
        let sig = Signature::from_bytes(&self.sig);
        vkey.verify(&msg, &sig)
            .map_err(|_| Refusal::DischargeBadSignature {
                caveat_id: hex(&self.caveat_id),
            })?;
        for p in &self.caveats {
            match p.eval(ctx) {
                Ok(true) => {}
                Ok(false) => {
                    return Err(Refusal::DischargeCaveatRefused {
                        caveat_id: hex(&self.caveat_id),
                        requires: p.explain(),
                    });
                }
                Err(unbound) => {
                    return Err(Refusal::DischargeContextIncomplete {
                        caveat_id: hex(&self.caveat_id),
                        requires: p.explain(),
                        unbound,
                    });
                }
            }
        }
        Ok(())
    }
}

/// Why a credential (or its discharge) was refused.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum Refusal {
    #[error("refused: proof-of-possession key does not match the credential tail")]
    ProofMismatch,
    #[error("refused: block {block} signature does not verify under its parent key")]
    BadSignature { block: usize },
    #[error("refused: block {block} carries a malformed verification key")]
    MalformedKey { block: usize },
    #[error("refused: third-party caveat names a malformed gateway key")]
    MalformedGatewayKey,
    #[error("refused: block {block} requires {requires}")]
    CaveatRefused { block: usize, requires: String },
    #[error("refused: block {block} requires {requires}, but {unbound}")]
    ContextIncomplete {
        block: usize,
        requires: String,
        unbound: Unbound,
    },
    #[error(
        "refused: block {block} requires a discharge for caveat id {caveat_id} from gateway {gateway}…, and none was presented"
    )]
    MissingDischarge {
        block: usize,
        caveat_id: String,
        gateway: String,
    },
    #[error("refused: discharge for caveat id {caveat_id} is unbound (fail-closed)")]
    UnboundDischarge { caveat_id: String },
    #[error(
        "refused: discharge for caveat id {caveat_id} is bound to a different credential (no cross-credential replay)"
    )]
    DischargeBoundElsewhere { caveat_id: String },
    #[error("refused: discharge for caveat id {caveat_id} is not signed by the named gateway")]
    DischargeBadSignature { caveat_id: String },
    #[error("refused: discharge for caveat id {caveat_id} requires {requires}")]
    DischargeCaveatRefused { caveat_id: String, requires: String },
    #[error("refused: discharge for caveat id {caveat_id} requires {requires}, but {unbound}")]
    DischargeContextIncomplete {
        caveat_id: String,
        requires: String,
        unbound: Unbound,
    },
}

// ===========================================================================
// Signed digests (BLAKE3, domain-separated — identical to breadstuffs)
// ===========================================================================

fn block_digest(prev: &[u8], caveats: &[Caveat], next_pub: &[u8; 32]) -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key(BLOCK_CTX);
    h.update(prev);
    h.update(&postcard::to_stdvec(caveats).expect("caveat encoding is total"));
    h.update(next_pub);
    *h.finalize().as_bytes()
}

fn discharge_digest(caveat_id: &[u8], caveats: &[Pred], binding: Option<&[u8; 32]>) -> [u8; 32] {
    #[derive(Serialize)]
    struct Body<'a> {
        caveat_id: &'a [u8],
        caveats: &'a [Pred],
        binding: Option<&'a [u8; 32]>,
    }
    let mut h = blake3::Hasher::new_derive_key(DISCHARGE_CTX);
    h.update(
        &postcard::to_stdvec(&Body {
            caveat_id,
            caveats,
            binding,
        })
        .expect("discharge encoding is total"),
    );
    *h.finalize().as_bytes()
}

// ===========================================================================
// Wire format (postcard + dga1_/dgd1_ base64url — identical to breadstuffs)
// ===========================================================================

/// A credential or discharge failed to decode.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum WireError {
    #[error("unknown wire prefix (expected `{expected}`)")]
    Prefix { expected: &'static str },
    #[error("payload is not base64url: {0}")]
    Base64(String),
    #[error("payload does not match the v1 schema: {0}")]
    Schema(String),
    #[error("malformed credential: {0}")]
    Malformed(&'static str),
}

#[derive(Serialize, Deserialize)]
struct BlockWire {
    caveats: Vec<Caveat>,
    next_pub: [u8; 32],
    sig: Vec<u8>,
}

#[derive(Serialize, Deserialize)]
struct CredentialWire {
    nonce: [u8; 32],
    blocks: Vec<BlockWire>,
    proof_seed: [u8; 32],
}

#[derive(Serialize, Deserialize)]
struct DischargeWire {
    caveat_id: Vec<u8>,
    caveats: Vec<Pred>,
    binding: Option<[u8; 32]>,
    sig: Vec<u8>,
}

fn sig64(v: &[u8]) -> Result<[u8; 64], WireError> {
    v.try_into()
        .map_err(|_| WireError::Malformed("signature is not 64 bytes"))
}

impl Credential {
    /// Encode to the `dga1_…` string form. **Bearer** — carries the tail key.
    pub fn encode(&self) -> String {
        let wire = CredentialWire {
            nonce: self.nonce,
            blocks: self
                .blocks
                .iter()
                .map(|b| BlockWire {
                    caveats: b.caveats.clone(),
                    next_pub: b.next_pub,
                    sig: b.sig.to_vec(),
                })
                .collect(),
            proof_seed: self.proof.to_bytes(),
        };
        let bytes = postcard::to_stdvec(&wire).expect("credential encoding is total");
        format!("{CREDENTIAL_PREFIX}{}", URL_SAFE_NO_PAD.encode(bytes))
    }

    /// Decode from the `dga1_…` string form. Structural validation only —
    /// authorization is decided by [`Credential::verify`].
    pub fn decode(s: &str) -> Result<Credential, WireError> {
        let body = s
            .trim()
            .strip_prefix(CREDENTIAL_PREFIX)
            .ok_or(WireError::Prefix {
                expected: CREDENTIAL_PREFIX,
            })?;
        let bytes = URL_SAFE_NO_PAD
            .decode(body)
            .map_err(|e| WireError::Base64(e.to_string()))?;
        let wire: CredentialWire =
            postcard::from_bytes(&bytes).map_err(|e| WireError::Schema(e.to_string()))?;
        if wire.blocks.is_empty() {
            return Err(WireError::Malformed("a credential has at least one block"));
        }
        let blocks = wire
            .blocks
            .iter()
            .map(|b| {
                Ok(Block {
                    caveats: b.caveats.clone(),
                    next_pub: b.next_pub,
                    sig: sig64(&b.sig)?,
                })
            })
            .collect::<Result<Vec<_>, WireError>>()?;
        let proof = SigningKey::from_bytes(&wire.proof_seed);
        let tail_pub = blocks.last().expect("non-empty checked above").next_pub;
        if proof.verifying_key().to_bytes() != tail_pub {
            return Err(WireError::Malformed(
                "carried proof key does not match the tail block (stripped or reassembled chain)",
            ));
        }
        Ok(Credential {
            nonce: wire.nonce,
            blocks,
            proof,
        })
    }
}

impl Discharge {
    pub fn encode(&self) -> String {
        let wire = DischargeWire {
            caveat_id: self.caveat_id.clone(),
            caveats: self.caveats.clone(),
            binding: self.binding,
            sig: self.sig.to_vec(),
        };
        let bytes = postcard::to_stdvec(&wire).expect("discharge encoding is total");
        format!("{DISCHARGE_PREFIX}{}", URL_SAFE_NO_PAD.encode(bytes))
    }
    pub fn decode(s: &str) -> Result<Discharge, WireError> {
        let body = s
            .trim()
            .strip_prefix(DISCHARGE_PREFIX)
            .ok_or(WireError::Prefix {
                expected: DISCHARGE_PREFIX,
            })?;
        let bytes = URL_SAFE_NO_PAD
            .decode(body)
            .map_err(|e| WireError::Base64(e.to_string()))?;
        let wire: DischargeWire =
            postcard::from_bytes(&bytes).map_err(|e| WireError::Schema(e.to_string()))?;
        Ok(Discharge::from_parts(
            wire.caveat_id,
            wire.caveats,
            wire.binding,
            sig64(&wire.sig)?,
        ))
    }
}

// ===========================================================================
// Small hex helpers (no extra dep)
// ===========================================================================

pub(crate) fn hex(bytes: &[u8]) -> String {
    const LUT: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        s.push(LUT[(b >> 4) as usize] as char);
        s.push(LUT[(b & 0x0f) as usize] as char);
    }
    s
}

pub(crate) fn unhex32(s: &str) -> Result<[u8; 32], KeyError> {
    if s.len() != 64 || !s.is_ascii() {
        return Err(KeyError("expected 64 hex characters".into()));
    }
    let mut out = [0u8; 32];
    for (i, chunk) in s.as_bytes().chunks_exact(2).enumerate() {
        let hi = (chunk[0] as char)
            .to_digit(16)
            .ok_or_else(|| KeyError("non-hex character".into()))?;
        let lo = (chunk[1] as char)
            .to_digit(16)
            .ok_or_else(|| KeyError("non-hex character".into()))?;
        out[i] = ((hi << 4) | lo) as u8;
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip_mint_encode_decode_verify() {
        let root = RootKey::from_seed([7u8; 32]);
        let cred = root.mint([Caveat::FirstParty(Pred::AttrEq {
            key: "cap".into(),
            value: "ops-admin".into(),
        })]);
        let wire = cred.encode();
        assert!(wire.starts_with("dga1_"));
        let decoded = Credential::decode(&wire).unwrap();
        let ctx = Context::new().attr("cap", "ops-admin");
        assert!(decoded.verify(&root.public(), &ctx).is_ok());
        let wrong = Context::new().attr("cap", "grafana-view");
        assert!(decoded.verify(&root.public(), &wrong).is_err());
    }

    #[test]
    fn attenuation_only_narrows() {
        let root = RootKey::from_seed([9u8; 32]);
        // Root grants ops-admin OR grafana-view.
        let cred = root.mint([Caveat::FirstParty(Pred::AnyOf(vec![
            Pred::AttrEq {
                key: "cap".into(),
                value: "ops-admin".into(),
            },
            Pred::AttrEq {
                key: "cap".into(),
                value: "grafana-view".into(),
            },
        ]))]);
        // Both surfaces open on the root.
        assert!(
            cred.verify(&root.public(), &Context::new().attr("cap", "ops-admin"))
                .is_ok()
        );
        // Attenuate to grafana-only.
        let narrowed = cred.attenuate([Caveat::FirstParty(Pred::AttrEq {
            key: "cap".into(),
            value: "grafana-view".into(),
        })]);
        // grafana-view still opens.
        assert!(
            narrowed
                .verify(&root.public(), &Context::new().attr("cap", "grafana-view"))
                .is_ok()
        );
        // ops-admin no longer reachable — no amplification.
        assert!(
            narrowed
                .verify(&root.public(), &Context::new().attr("cap", "ops-admin"))
                .is_err()
        );
    }

    #[test]
    fn forged_root_key_rejected() {
        let root = RootKey::from_seed([1u8; 32]);
        let attacker = RootKey::from_seed([2u8; 32]);
        let cred = root.mint([Caveat::FirstParty(Pred::True)]);
        // Verifying under the wrong root public key fails the signature chain.
        assert!(matches!(
            cred.verify(&attacker.public(), &Context::new()),
            Err(Refusal::BadSignature { .. })
        ));
    }

    #[test]
    fn expiry_enforced() {
        let root = RootKey::from_seed([3u8; 32]);
        let cred = root.mint([Caveat::FirstParty(Pred::NotAfter { at: 1_000 })]);
        assert!(cred.verify(&root.public(), &Context::new().at(999)).is_ok());
        assert!(
            cred.verify(&root.public(), &Context::new().at(1_001))
                .is_err()
        );
        // No clock bound at all ⇒ fail-closed.
        assert!(cred.verify(&root.public(), &Context::new()).is_err());
    }
}
