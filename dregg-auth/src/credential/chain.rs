//! The credential itself: an ed25519 block chain whose blocks carry caveats.
//!
//! ## The shape (and its Lean counterparts)
//!
//! A [`Credential`] is a nonce plus an append-only chain of blocks. Each block
//! carries (a) the caveats it installs and (b) the verification key under which
//! the *next* block's signature is checked; the root block's signature is
//! checked under the issuer's key. This is exactly the biscuit public-key
//! delegation chain of `Dregg2.Authority.BiscuitGraph` (block `n+1` verifies
//! under block `n`'s `vkey`; offline attenuation by anyone holding the tail
//! key), and the caveat semantics are `Dregg2.Authority.Caveat`:
//!
//! * **admit = the meet**: a credential admits a request iff *all* caveats of
//!   *all* blocks are satisfied — `Token.admits`, fail-closed;
//! * **attenuate = append**: [`Credential::attenuate`] appends one block —
//!   `Token.attenuate`, and `attenuate_narrows`/`attenuate_subset` prove the
//!   admitted-request set can only SHRINK. There is no removal API, and the
//!   signature chain makes block removal detectable (`BiscuitGraph`'s
//!   forged-block tooth): each non-root block signs over its parent's
//!   signature, and presentation requires possession of the tail key
//!   ([`Credential::verify`] checks the carried proof key against the last
//!   block's `next_pub`), which a holder of a *narrowed* credential never has
//!   for any prefix of the chain. Amplification is inexpressible in the API
//!   and unforgeable on the wire.
//!
//! Third-party caveats follow the macaroon discharge protocol of
//! `Dregg2.Authority.MacaroonDischarge`: a [`Discharge`] is its own signed
//! object, **bound** to the exact credential it discharges via the BLAKE3 hash
//! of that credential's [tail](Credential::tail). An unbound discharge is
//! rejected unconditionally (`unbound_discharge_rejected`); a discharge bound
//! to a different credential is rejected (`binding_not_replayable_to_other_root`
//! — the no-cross-root-replay tooth that defeats "strip caveats, reuse the old
//! approval").

use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};
use serde::Serialize;

use super::caveat::{Caveat, Context};
use super::hex;
use super::pq;
use super::pred::{Pred, Unbound};

/// Domain-separation contexts for every BLAKE3 derivation (versioned with the
/// wire prefix; bump together).
const BLOCK_CTX: &str = "dregg-auth v1 block";
const TAIL_CTX: &str = "dregg-auth v1 tail";
const DISCHARGE_CTX: &str = "dregg-auth v1 discharge";

/// A public (verifying) key — 32 ed25519 bytes. What a verifier holds; safe to
/// publish anywhere.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PublicKey(pub [u8; 32]);

impl PublicKey {
    /// Render as lowercase hex (the publishable form).
    pub fn to_hex(&self) -> String {
        hex(&self.0)
    }

    /// Parse from the hex form.
    pub fn from_hex(s: &str) -> Result<Self, KeyError> {
        Ok(PublicKey(super::unhex32(s.trim())?))
    }
}

/// A key could not be parsed.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[error("invalid key: {0}")]
pub struct KeyError(pub(crate) String);

/// The **enrolled hybrid root** a verifier holds for [`Credential::verify_hybrid`]:
/// the ed25519 root public key AND the root authority's ML-DSA-65 public key
/// (1952 bytes, FIPS 204). Both are the trust anchor; the PQ half is enrolled,
/// never derived from the ed25519 half and never asserted by the credential
/// itself. Obtain it from [`RootKey::public_hybrid`]; publish it wherever the
/// classical [`PublicKey`] is published.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HybridRootPublic {
    /// The classical ed25519 root public key.
    pub ed25519: PublicKey,
    /// The root authority's serialized ML-DSA-65 public key.
    pub ml_dsa: Vec<u8>,
}

fn fresh_signing_key() -> SigningKey {
    let mut seed = [0u8; 32];
    getrandom::getrandom(&mut seed).expect("operating-system randomness is available");
    SigningKey::from_bytes(&seed)
}

/// The minting authority: an ed25519 keypair. The private half mints
/// ([`RootKey::mint`]); the public half ([`RootKey::public`]) is all any
/// verifier ever needs — offline, cross-vat, exactly the biscuit half of the
/// `Dregg2.Authority.Caveat.TokenKind` split (`biscuit_crossvat`: public-key
/// tokens verify off-island; HMAC macaroons do not).
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

    /// Deterministic construction from a 32-byte seed (tests, derivation
    /// pipelines — the golden-vector discipline).
    pub fn from_seed(seed: [u8; 32]) -> Self {
        Self {
            key: SigningKey::from_bytes(&seed),
        }
    }

    /// The 32-byte secret seed (store it where the root keeps secrets).
    pub fn secret_bytes(&self) -> [u8; 32] {
        self.key.to_bytes()
    }

    /// The public key verifiers use.
    pub fn public(&self) -> PublicKey {
        PublicKey(self.key.verifying_key().to_bytes())
    }

    /// The **enrolled hybrid root** verifiers hold for the post-quantum path:
    /// the ed25519 public key plus this root's ML-DSA-65 public key (derived
    /// from the same seed). Pass it to [`Credential::verify_hybrid`]. This is
    /// the PQ trust anchor — the ML-DSA half a credential's chain roots at, and
    /// which no credential may assert for itself.
    pub fn public_hybrid(&self) -> HybridRootPublic {
        HybridRootPublic {
            ed25519: self.public(),
            ml_dsa: pq::ml_dsa_public_from_seed(&self.key.to_bytes()).to_vec(),
        }
    }

    /// Mint a root credential carrying `caveats` (the root grant).
    ///
    /// Lean: constructing the `Token` with its initial caveat list
    /// (`Dregg2.Authority.Caveat.Token`); the signature chain seed is the
    /// `BiscuitGraph` root block, verified under this key.
    pub fn mint(&self, caveats: impl IntoIterator<Item = Caveat>) -> Credential {
        let mut nonce = [0u8; 32];
        getrandom::getrandom(&mut nonce).expect("operating-system randomness is available");
        let caveats: Vec<Caveat> = caveats.into_iter().collect();
        let next = fresh_signing_key();
        let next_pub = next.verifying_key().to_bytes();
        let next_pub_ml_dsa = pq::ml_dsa_public_from_seed(&next.to_bytes()).to_vec();
        let msg = block_digest(&nonce, &caveats, &next_pub, &next_pub_ml_dsa);
        let sig = self.key.sign(&msg).to_bytes();
        let sig_ml_dsa = pq::ml_dsa_sign(&self.key.to_bytes(), &msg)
            .expect("ml-dsa signing is available")
            .to_vec();
        Credential {
            nonce,
            blocks: vec![Block {
                caveats,
                next_pub,
                next_pub_ml_dsa,
                sig,
                sig_ml_dsa,
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
    /// Generate a fresh gateway key.
    pub fn generate() -> Self {
        Self {
            key: fresh_signing_key(),
        }
    }

    /// Deterministic construction from a 32-byte seed.
    pub fn from_seed(seed: [u8; 32]) -> Self {
        Self {
            key: SigningKey::from_bytes(&seed),
        }
    }

    /// The 32-byte secret seed.
    pub fn secret_bytes(&self) -> [u8; 32] {
        self.key.to_bytes()
    }

    /// The public key third-party caveats name.
    pub fn public(&self) -> PublicKey {
        PublicKey(self.key.verifying_key().to_bytes())
    }

    /// Issue a discharge for `caveat_id`, **bound** to the credential whose
    /// [`Credential::tail`] is `bound_to`, optionally carrying the gateway's
    /// own first-party conditions (e.g. an expiry on the approval).
    ///
    /// Binding is a *required* argument: this API cannot construct the unbound
    /// discharge the Lean proves must be rejected
    /// (`MacaroonDischarge.unbound_discharge_rejected`). The holder finishes
    /// attenuating, reads the tail, and requests a discharge bound to it —
    /// `MacaroonDischarge.bindTo`, gateway-side.
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

/// One block of the chain: the caveats it installs, the key the *next* block
/// verifies under, and this block's signature (checked under the parent's key;
/// the root block under the issuer's key). Lean: `BiscuitGraph.Block`
/// (`authority`/`vkey`/`sig`), with `authority` carried as caveats narrowing
/// the admitted-request set instead of a rights `Finset`.
#[derive(Clone, Debug)]
pub(crate) struct Block {
    pub(crate) caveats: Vec<Caveat>,
    pub(crate) next_pub: [u8; 32],
    /// The ML-DSA-65 public key of the *next* block's signer — the PQ half of
    /// the carried attenuation key. Covered by THIS block's ed25519 ∧ ML-DSA
    /// signatures (it is hashed into `block_digest`), so a self-inserted PQ key
    /// not authorized by the parent fails: the chain's PQ integrity roots at
    /// the enrolled [`HybridRootPublic`], never a self-asserted per-block key.
    pub(crate) next_pub_ml_dsa: Vec<u8>,
    pub(crate) sig: [u8; 64],
    /// The ML-DSA-65 signature over the SAME `block_digest` the ed25519 `sig`
    /// covers — the hybrid half. Verified in [`Credential::verify_hybrid`].
    pub(crate) sig_ml_dsa: Vec<u8>,
}

/// An attenuable, offline-verifiable credential — the token.
///
/// Bearer semantics: whoever holds the encoded form holds the authority it
/// names (narrowed by its caveats) *and* the ability to attenuate further
/// (the carried tail key). Hand a sub-agent strictly less by attenuating
/// before handing it over; the recipient cannot recover the wider parent
/// (see the module docs on the non-widening discipline).
pub struct Credential {
    pub(crate) nonce: [u8; 32],
    pub(crate) blocks: Vec<Block>,
    /// The tail private key (matching the last block's `next_pub`): proof of
    /// possession at presentation, signing key for the next attenuation.
    pub(crate) proof: SigningKey,
}

impl std::fmt::Debug for Credential {
    /// Debug shows the chain, never the bearer (proof) key.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Credential")
            .field("nonce", &hex(&self.nonce))
            .field("blocks", &self.blocks)
            .field("proof", &"<bearer key redacted>")
            .finish()
    }
}

impl Credential {
    /// Append caveats — the ONLY mutation, and it can only narrow.
    ///
    /// Lean: `Token.attenuate` (append a caveat), with the keystone theorems
    /// `attenuate_narrows` (anything the child admits, the parent already
    /// admitted) and `attenuate_subset` (the admitted-request set shrinks).
    /// Widening is inexpressible: there is no API that removes or weakens a
    /// caveat, and the signature chain + proof-of-possession make removal
    /// unforgeable on the wire. Attenuating by [`Pred::True`] is the identity
    /// edge (`attenuate_trivial`).
    ///
    /// Offline: no contact with the issuer — the `BiscuitGraph` property.
    #[must_use = "attenuate returns the narrowed credential"]
    pub fn attenuate(mut self, caveats: impl IntoIterator<Item = Caveat>) -> Credential {
        let caveats: Vec<Caveat> = caveats.into_iter().collect();
        let next = fresh_signing_key();
        let next_pub = next.verifying_key().to_bytes();
        let next_pub_ml_dsa = pq::ml_dsa_public_from_seed(&next.to_bytes()).to_vec();
        let prev_sig = self
            .blocks
            .last()
            .expect("a credential has a root block")
            .sig;
        let msg = block_digest(&prev_sig, &caveats, &next_pub, &next_pub_ml_dsa);
        let sig = self.proof.sign(&msg).to_bytes();
        let sig_ml_dsa = pq::ml_dsa_sign(&self.proof.to_bytes(), &msg)
            .expect("ml-dsa signing is available")
            .to_vec();
        self.blocks.push(Block {
            caveats,
            next_pub,
            next_pub_ml_dsa,
            sig,
            sig_ml_dsa,
        });
        self.proof = next;
        self
    }

    /// The credential's **tail**: the BLAKE3 hash (domain-separated) of the
    /// final block signature. Since every block signs over its parent's
    /// signature, the tail commits the entire chain. This is the value a
    /// [`Discharge`] binds to — the `parent_tail` of
    /// `MacaroonDischarge.bindTo`/`verifyDischarge`.
    pub fn tail(&self) -> [u8; 32] {
        let last = self.blocks.last().expect("a credential has a root block");
        let mut h = blake3::Hasher::new_derive_key(TAIL_CTX);
        h.update(&last.sig);
        *h.finalize().as_bytes()
    }

    /// Every caveat on the chain, in installation order, with its block index.
    pub fn caveats(&self) -> impl Iterator<Item = (usize, &Caveat)> {
        self.blocks
            .iter()
            .enumerate()
            .flat_map(|(i, b)| b.caveats.iter().map(move |c| (i, c)))
    }

    /// Verify this credential against the issuer's public key and a
    /// caller-supplied [`Context`] — fully offline, deterministic.
    ///
    /// The decision is the Lean `Token.admits`: the signature chain must
    /// verify from `root` (the `BiscuitGraph` chain face), the carried proof
    /// key must match the tail (possession — what makes caveat-stripping
    /// unforgeable), and then **every** caveat of **every** block must be
    /// satisfied (`Caveat.ok` under the meet): first-party predicates hold in
    /// `ctx`, third-party caveats are discharged by a presented, *bound*,
    /// gateway-signed [`Discharge`] whose own conditions hold. Fail-closed
    /// throughout; the refusal names the first violated requirement.
    pub fn verify(&self, root: &PublicKey, ctx: &Context) -> Result<(), Refusal> {
        // 1. Proof of possession: the carried tail key matches the last
        //    block's next_pub. Without this, a recipient could strip trailing
        //    blocks and present the wider prefix.
        let last = self.blocks.last().expect("a credential has a root block");
        if self.proof.verifying_key().to_bytes() != last.next_pub {
            return Err(Refusal::ProofMismatch);
        }

        // 2. The signature chain, from the root key down (BiscuitGraph: each
        //    block verifies under its parent's vkey).
        let mut vkey =
            VerifyingKey::from_bytes(&root.0).map_err(|_| Refusal::MalformedKey { block: 0 })?;
        let mut prev: Option<[u8; 64]> = None;
        for (i, block) in self.blocks.iter().enumerate() {
            let msg = match prev {
                None => block_digest(
                    &self.nonce,
                    &block.caveats,
                    &block.next_pub,
                    &block.next_pub_ml_dsa,
                ),
                Some(ps) => {
                    block_digest(&ps, &block.caveats, &block.next_pub, &block.next_pub_ml_dsa)
                }
            };
            let sig = Signature::from_bytes(&block.sig);
            vkey.verify(&msg, &sig)
                .map_err(|_| Refusal::BadSignature { block: i })?;
            vkey = VerifyingKey::from_bytes(&block.next_pub)
                .map_err(|_| Refusal::MalformedKey { block: i })?;
            prev = Some(block.sig);
        }

        // 3. The meet of all caveats (Token.admits) — fail-closed.
        self.check_caveats(ctx)
    }

    /// Verify this credential HYBRID: the ed25519 ∧ ML-DSA-65 signature chain
    /// from the **enrolled** [`HybridRootPublic`], plus the same possession and
    /// caveat gates as [`Credential::verify`] — fully offline, deterministic,
    /// quantum-safe.
    ///
    /// This is the post-quantum verification. Where [`verify`](Self::verify)
    /// anchors only ed25519 (the classical/compat path), this anchors BOTH the
    /// ed25519 AND the ML-DSA-65 root under the verifier's enrolled hybrid root
    /// key. A block verifies only when BOTH halves check; forging an
    /// attenuation therefore requires breaking ed25519 discrete-log AND
    /// module-lattice SIS/LWE simultaneously.
    ///
    /// **Enroll + pin.** The PQ trust anchor is the enrolled `root.ml_dsa` — NOT
    /// a key the credential carries for itself. Each block's carried next
    /// ML-DSA key is covered by its parent's (hybrid) signatures back to the
    /// enrolled root, so a self-inserted ML-DSA key — or a PQ half signed under
    /// a key the parent never authorized — fails closed. A missing or malformed
    /// PQ half is a [`Refusal::BadPqSignature`], never a silent downgrade.
    pub fn verify_hybrid(&self, root: &HybridRootPublic, ctx: &Context) -> Result<(), Refusal> {
        // 1. Proof of possession, BOTH halves: the carried tail key (ed25519
        //    and ML-DSA, both derived from the same held seed) must match the
        //    last block's next keys. Without the PQ half, a quantum forger who
        //    broke ed25519 could still not present a stripped prefix.
        let last = self.blocks.last().expect("a credential has a root block");
        if self.proof.verifying_key().to_bytes() != last.next_pub {
            return Err(Refusal::ProofMismatch);
        }
        if pq::ml_dsa_public_from_seed(&self.proof.to_bytes()).as_slice()
            != last.next_pub_ml_dsa.as_slice()
        {
            return Err(Refusal::PqProofMismatch);
        }

        // 2. The hybrid signature chain, anchored at the ENROLLED hybrid root
        //    (ed25519 ∧ ML-DSA). Each block advances to its carried next hybrid
        //    key, which the just-verified signatures pinned.
        let mut vkey = VerifyingKey::from_bytes(&root.ed25519.0)
            .map_err(|_| Refusal::MalformedKey { block: 0 })?;
        let mut pq_vkey: Vec<u8> = root.ml_dsa.clone();
        let mut prev: Option<[u8; 64]> = None;
        for (i, block) in self.blocks.iter().enumerate() {
            let msg = match prev {
                None => block_digest(
                    &self.nonce,
                    &block.caveats,
                    &block.next_pub,
                    &block.next_pub_ml_dsa,
                ),
                Some(ps) => {
                    block_digest(&ps, &block.caveats, &block.next_pub, &block.next_pub_ml_dsa)
                }
            };
            let sig = Signature::from_bytes(&block.sig);
            vkey.verify(&msg, &sig)
                .map_err(|_| Refusal::BadSignature { block: i })?;
            // The PQ half over the SAME digest, under the parent-pinned key.
            if !pq::ml_dsa_verify(&pq_vkey, &msg, &block.sig_ml_dsa) {
                return Err(Refusal::BadPqSignature { block: i });
            }
            vkey = VerifyingKey::from_bytes(&block.next_pub)
                .map_err(|_| Refusal::MalformedKey { block: i })?;
            pq_vkey = block.next_pub_ml_dsa.clone();
            prev = Some(block.sig);
        }

        // 3. The meet of all caveats (Token.admits) — fail-closed.
        self.check_caveats(ctx)
    }

    /// The meet of all caveats (`Token.admits`) — fail-closed, shared by
    /// [`verify`](Self::verify) and [`verify_hybrid`](Self::verify_hybrid). The
    /// signature/possession gates differ; the authorization decision does not.
    fn check_caveats(&self, ctx: &Context) -> Result<(), Refusal> {
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

    /// Human-readable terms of this credential, block by block, ending with
    /// the canonical `[tail …]` tag (the `sdk/src/explain.rs` convention: a
    /// prose body plus a full-hash faithfulness tag — two credentials that
    /// render identically share the tail, hence the same signed chain).
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

/// Check one third-party caveat against the presented discharges — the
/// executable `MacaroonDischarge.verifyDischarge`, fail-closed in this order:
/// matching id, then BINDING (unbound ⇒ reject; bound elsewhere ⇒ reject),
/// then the gateway signature, then the discharge's own conditions.
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

/// A third-party discharge token: the gateway's signed, **bound** approval of
/// one third-party caveat.
///
/// Lean: `MacaroonDischarge.Discharge` — its own object (`dkey`/`nonce`/`fp`/
/// `boundTo`), here signed under the gateway's ed25519 key instead of chained
/// HMAC (the public-key/biscuit side of the `TokenKind` split, so discharges
/// verify offline too). `binding` is `boundTo`: `Some(tail)` iff bound;
/// verification rejects `None` unconditionally
/// (`unbound_discharge_rejected` — an unbound discharge could be replayed
/// against a less-attenuated credential).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Discharge {
    pub(crate) caveat_id: Vec<u8>,
    pub(crate) caveats: Vec<Pred>,
    pub(crate) binding: Option<[u8; 32]>,
    pub(crate) sig: [u8; 64],
}

impl Discharge {
    /// Assemble a discharge from raw parts (interop / adversarial testing —
    /// e.g. a foreign gateway implementation). Nothing is checked here; an
    /// assembled discharge still has to pass [`Credential::verify`]'s binding
    /// and signature gates, which is exactly what makes this constructor safe
    /// to expose.
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

    /// The caveat id this discharge answers.
    pub fn caveat_id(&self) -> &[u8] {
        &self.caveat_id
    }

    fn verify_against(
        &self,
        gateway: &[u8; 32],
        tail: &[u8; 32],
        ctx: &Context,
    ) -> Result<(), Refusal> {
        // Binding first — fail-closed (`unbound_discharge_rejected`), and the
        // no-cross-root-replay tooth (`binding_not_replayable_to_other_root`).
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
        // The gateway signature over (id, conditions, binding).
        let vkey = VerifyingKey::from_bytes(gateway).map_err(|_| Refusal::MalformedGatewayKey)?;
        let msg = discharge_digest(&self.caveat_id, &self.caveats, self.binding.as_ref());
        let sig = Signature::from_bytes(&self.sig);
        vkey.verify(&msg, &sig)
            .map_err(|_| Refusal::DischargeBadSignature {
                caveat_id: hex(&self.caveat_id),
            })?;
        // The gateway's own first-party conditions (the Lean `fp` list) — the
        // same fail-closed meet.
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

    /// Human-readable terms of this discharge.
    pub fn explain(&self) -> String {
        let conditions = if self.caveats.is_empty() {
            "unconditional".to_string()
        } else {
            self.caveats
                .iter()
                .map(Pred::explain)
                .collect::<Vec<_>>()
                .join("; ")
        };
        let binding = match &self.binding {
            Some(b) => format!("bound to credential tail {}", hex(b)),
            None => "UNBOUND (will be refused)".to_string(),
        };
        format!(
            "discharge for caveat id {}: {conditions}; {binding}",
            hex(&self.caveat_id)
        )
    }
}

/// Why a credential (or its discharge) was refused. Every variant carries the
/// human-readable terms — the explain discipline: a denial always says *which*
/// requirement failed.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum Refusal {
    /// The carried proof key does not match the last block — a stripped or
    /// reassembled chain (the possession check that makes caveat removal
    /// unforgeable).
    #[error("refused: proof-of-possession key does not match the credential tail")]
    ProofMismatch,
    /// A block's signature did not verify under its parent's key — a forged
    /// or tampered chain (the `BiscuitGraph` forged-block tooth).
    #[error("refused: block {block} signature does not verify under its parent key")]
    BadSignature {
        /// Index of the offending block.
        block: usize,
    },
    /// A block's ML-DSA-65 (PQ) signature did not verify under the
    /// parent-pinned (or enrolled-root) ML-DSA key — a forged, tampered, or
    /// self-inserted PQ half, OR a missing/malformed one (fail-closed). This is
    /// the post-quantum forged-block tooth of [`Credential::verify_hybrid`].
    #[error(
        "refused: block {block} ML-DSA signature does not verify under its parent-pinned PQ key"
    )]
    BadPqSignature {
        /// Index of the offending block.
        block: usize,
    },
    /// The carried proof key's ML-DSA-65 half does not match the last block's
    /// pinned PQ key — a stripped or reassembled chain caught by the PQ
    /// possession check (the quantum-safe analog of [`Refusal::ProofMismatch`]).
    #[error("refused: proof-of-possession ML-DSA key does not match the credential tail")]
    PqProofMismatch,
    /// A chained verification key (or the root key) is not a valid ed25519
    /// point.
    #[error("refused: block {block} carries a malformed verification key")]
    MalformedKey {
        /// Index of the offending block.
        block: usize,
    },
    /// A third-party caveat names a malformed gateway key.
    #[error("refused: third-party caveat names a malformed gateway key")]
    MalformedGatewayKey,
    /// A first-party caveat evaluated to false (`Token.admits` meet violated).
    #[error("refused: block {block} requires {requires}")]
    CaveatRefused {
        /// Block whose caveat refused.
        block: usize,
        /// The violated caveat's human-readable terms.
        requires: String,
    },
    /// A caveat mentions data the context does not bind — refused outright,
    /// never treated as false (fail-closed under negation).
    #[error("refused: block {block} requires {requires}, but {unbound}")]
    ContextIncomplete {
        /// Block whose caveat could not be evaluated.
        block: usize,
        /// The caveat's human-readable terms.
        requires: String,
        /// What the context failed to bind.
        unbound: Unbound,
    },
    /// A third-party caveat has no presented discharge with its id.
    #[error(
        "refused: block {block} requires a discharge for caveat id {caveat_id} from gateway {gateway}…, and none was presented"
    )]
    MissingDischarge {
        /// Block carrying the third-party caveat.
        block: usize,
        /// Hex of the undischarged caveat id.
        caveat_id: String,
        /// Hex prefix of the gateway key.
        gateway: String,
    },
    /// The discharge carries no binding — rejected unconditionally
    /// (`MacaroonDischarge.unbound_discharge_rejected`: an unbound discharge
    /// could be replayed against a less-attenuated credential).
    #[error("refused: discharge for caveat id {caveat_id} is unbound (fail-closed)")]
    UnboundDischarge {
        /// Hex of the discharge's caveat id.
        caveat_id: String,
    },
    /// The discharge is bound to a *different* credential's tail — the
    /// no-cross-root-replay tooth
    /// (`MacaroonDischarge.binding_not_replayable_to_other_root`).
    #[error(
        "refused: discharge for caveat id {caveat_id} is bound to a different credential (no cross-credential replay)"
    )]
    DischargeBoundElsewhere {
        /// Hex of the discharge's caveat id.
        caveat_id: String,
    },
    /// The discharge signature does not verify under the gateway key the
    /// caveat names.
    #[error("refused: discharge for caveat id {caveat_id} is not signed by the named gateway")]
    DischargeBadSignature {
        /// Hex of the discharge's caveat id.
        caveat_id: String,
    },
    /// One of the discharge's own conditions (the Lean `fp` list) refused.
    #[error("refused: discharge for caveat id {caveat_id} requires {requires}")]
    DischargeCaveatRefused {
        /// Hex of the discharge's caveat id.
        caveat_id: String,
        /// The violated condition's human-readable terms.
        requires: String,
    },
    /// A discharge condition mentions data the context does not bind.
    #[error("refused: discharge for caveat id {caveat_id} requires {requires}, but {unbound}")]
    DischargeContextIncomplete {
        /// Hex of the discharge's caveat id.
        caveat_id: String,
        /// The condition's human-readable terms.
        requires: String,
        /// What the context failed to bind.
        unbound: Unbound,
    },
}

/// The signed digest of one block: BLAKE3 (domain-separated) over
/// `seed-or-parent-sig || postcard(caveats) || next_pub || next_pub_ml_dsa`.
/// Fixed-width fields at both ends make the concatenation unambiguous; postcard
/// is deterministic for a given type, so the encoding is canonical. The next
/// block's ML-DSA-65 public key is INSIDE the digest, so BOTH of this block's
/// signatures (ed25519 and ML-DSA) cover — and thereby PIN — the child's PQ
/// key: a self-inserted PQ key not authorized by this parent cannot verify.
fn block_digest(
    prev: &[u8],
    caveats: &[Caveat],
    next_pub: &[u8; 32],
    next_pub_ml_dsa: &[u8],
) -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key(BLOCK_CTX);
    h.update(prev);
    h.update(&postcard::to_stdvec(caveats).expect("caveat encoding is total"));
    h.update(next_pub);
    h.update(next_pub_ml_dsa);
    *h.finalize().as_bytes()
}

/// The signed digest of a discharge: BLAKE3 (domain-separated) over the
/// postcard encoding of `(caveat_id, caveats, binding)`. The binding is INSIDE
/// the signed body, so re-binding to a new credential requires a fresh gateway
/// signature (`MacaroonDischarge.rebinding_requires_mac_query`, with ed25519
/// unforgeability standing where the keyed-hash portal stood).
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

#[cfg(test)]
mod hybrid_pq_tests {
    //! The HYBRID (ed25519 ∧ ML-DSA-65) chain verify, its enroll+pin root, and
    //! the adversarial teeth: an attacker's PQ half, a missing PQ half, a
    //! swapped carried PQ key, a wrong enrolled root, and PQ possession.
    use super::*;

    fn read_caveat() -> Caveat {
        Caveat::FirstParty(Pred::AttrEq {
            key: "tool".into(),
            value: "read".into(),
        })
    }
    fn ok_ctx() -> Context {
        Context::new().at(10).attr("tool", "read")
    }

    #[test]
    fn honest_hybrid_chain_passes() {
        let root = RootKey::from_seed([21u8; 32]);
        let cred = root.mint([read_caveat()]).attenuate([read_caveat()]);
        // Both the classical and the enrolled-hybrid path admit the honest chain.
        assert_eq!(cred.verify(&root.public(), &ok_ctx()), Ok(()));
        assert_eq!(cred.verify_hybrid(&root.public_hybrid(), &ok_ctx()), Ok(()));
    }

    #[test]
    fn attacker_ml_dsa_half_rejected_ed25519_still_valid() {
        let root = RootKey::from_seed([22u8; 32]);
        let mut cred = root.mint([read_caveat()]).attenuate([read_caveat()]);

        // Attacker forges the PQ half of the attenuation block (block 1) under
        // their OWN ML-DSA key, over the exact honest digest — the ed25519
        // chain is untouched and remains valid.
        let attacker_seed = [0xAAu8; 32];
        let prev_sig = cred.blocks[0].sig;
        let (caveats, next_pub, next_pub_ml_dsa) = {
            let b1 = &cred.blocks[1];
            (b1.caveats.clone(), b1.next_pub, b1.next_pub_ml_dsa.clone())
        };
        let digest = block_digest(&prev_sig, &caveats, &next_pub, &next_pub_ml_dsa);
        cred.blocks[1].sig_ml_dsa = pq::ml_dsa_sign(&attacker_seed, &digest).unwrap().to_vec();

        // The ed25519 chain is still valid: the classical path passes.
        assert_eq!(cred.verify(&root.public(), &ok_ctx()), Ok(()));
        // The HYBRID path REJECTS: block 1's PQ key is pinned by block 0 to the
        // honest key, which the attacker's ML-DSA signature does not match.
        assert_eq!(
            cred.verify_hybrid(&root.public_hybrid(), &ok_ctx()),
            Err(Refusal::BadPqSignature { block: 1 })
        );
    }

    #[test]
    fn missing_pq_half_fails_closed() {
        let root = RootKey::from_seed([23u8; 32]);
        let mut cred = root.mint([read_caveat()]).attenuate([read_caveat()]);
        cred.blocks[1].sig_ml_dsa = Vec::new();
        assert_eq!(
            cred.verify_hybrid(&root.public_hybrid(), &ok_ctx()),
            Err(Refusal::BadPqSignature { block: 1 })
        );
    }

    #[test]
    fn swapping_the_carried_pq_key_breaks_the_signature() {
        // The PIN is enforced by BOTH halves: the ed25519 signature also covers
        // the child's carried ML-DSA key, so swapping in an attacker PQ key at
        // block 0 cannot keep even the ed25519 chain valid.
        let root = RootKey::from_seed([24u8; 32]);
        let mut cred = root.mint([read_caveat()]).attenuate([read_caveat()]);
        cred.blocks[0].next_pub_ml_dsa = pq::ml_dsa_public_from_seed(&[0xBBu8; 32]).to_vec();
        assert_eq!(
            cred.verify(&root.public(), &ok_ctx()),
            Err(Refusal::BadSignature { block: 0 })
        );
        assert_eq!(
            cred.verify_hybrid(&root.public_hybrid(), &ok_ctx()),
            Err(Refusal::BadSignature { block: 0 })
        );
    }

    #[test]
    fn pq_roots_at_enrolled_root_not_self_asserted() {
        // The PQ chain roots at the ENROLLED hybrid root, never a self-asserted
        // key. A verifier enrolling the wrong ML-DSA root rejects at block 0.
        let root = RootKey::from_seed([25u8; 32]);
        let attacker_root = RootKey::from_seed([26u8; 32]);
        let cred = root.mint([read_caveat()]);
        // Correct ed25519 root, attacker's ML-DSA root: the PQ half rejects.
        let mixed = HybridRootPublic {
            ed25519: root.public(),
            ml_dsa: attacker_root.public_hybrid().ml_dsa,
        };
        assert_eq!(
            cred.verify_hybrid(&mixed, &ok_ctx()),
            Err(Refusal::BadPqSignature { block: 0 })
        );
        // An entirely wrong enrolled root: the ed25519 half rejects first.
        assert_eq!(
            cred.verify_hybrid(&attacker_root.public_hybrid(), &ok_ctx()),
            Err(Refusal::BadSignature { block: 0 })
        );
    }

    #[test]
    fn pq_possession_mismatch_rejected() {
        // The tail block's carried ML-DSA key must match the held proof seed —
        // the quantum-safe possession gate. Swap it and the gate fails closed.
        let root = RootKey::from_seed([27u8; 32]);
        let mut cred = root.mint([read_caveat()]);
        cred.blocks[0].next_pub_ml_dsa = pq::ml_dsa_public_from_seed(&[0xCCu8; 32]).to_vec();
        assert_eq!(
            cred.verify_hybrid(&root.public_hybrid(), &ok_ctx()),
            Err(Refusal::PqProofMismatch)
        );
    }

    #[test]
    fn hybrid_survives_the_wire_roundtrip() {
        let root = RootKey::from_seed([28u8; 32]);
        let cred = root.mint([read_caveat()]).attenuate([read_caveat()]);
        let decoded = Credential::decode(&cred.encode()).expect("decode");
        assert_eq!(
            decoded.verify_hybrid(&root.public_hybrid(), &ok_ctx()),
            Ok(())
        );
    }
}
