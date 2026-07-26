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

use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
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
    /// This root's own memoised ML-DSA-65 key — see [`pq::MlDsaSeedMemo`]. The
    /// root signs the PQ half of every block it mints and publishes the same key
    /// as its enrolled anchor ([`RootKey::public_hybrid`]); without this, a root
    /// that minted `k` credentials ran the ~200 ms Lean keygen `k + 1` times for
    /// one unchanging key.
    pq: pq::MlDsaSeedMemo,
}

impl RootKey {
    /// Generate a fresh root from operating-system randomness.
    pub fn generate() -> Self {
        Self {
            key: fresh_signing_key(),
            pq: pq::MlDsaSeedMemo::empty(),
        }
    }

    /// Deterministic construction from a 32-byte seed (tests, derivation
    /// pipelines — the golden-vector discipline).
    pub fn from_seed(seed: [u8; 32]) -> Self {
        Self {
            key: SigningKey::from_bytes(&seed),
            pq: pq::MlDsaSeedMemo::empty(),
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
            ml_dsa: self.pq.public_from_seed(&self.key.to_bytes()).to_vec(),
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
        // ONE keygen for the fresh tail identity, and the credential that will own
        // that identity keeps it: the block needs the public bytes, the holder
        // needs the key, and they are the same derivation.
        // The tail-identity keygen — see `credential::pq::ml_dsa_verify` for why the install is
        // here. `mint` and `attenuate` each MINT A NEW identity, so this derivation is not served
        // by any memo and `dregg-pq` aborts on it when no verified core is installed.
        #[cfg(test)]
        dregg_pq_testkit::install_or_panic();
        let next_pq = std::sync::Arc::new(dregg_pq::MlDsaKey::from_ed25519_seed(&next.to_bytes()));
        let next_pub_ml_dsa = pq::pk_bytes(&next_pq).to_vec();
        let msg = block_digest(&nonce, &caveats, &next_pub, &next_pub_ml_dsa);
        let sig = self.key.sign(&msg).to_bytes();
        // The root's own PQ half comes from the root's memo, so minting a second
        // credential from this root does not re-run the keygen.
        let sig_ml_dsa = self
            .pq
            .sign(&self.key.to_bytes(), &msg)
            .expect("ml-dsa signing is available")
            .to_vec();
        let cred = Credential {
            nonce,
            blocks: vec![Block {
                caveats,
                next_pub,
                next_pub_ml_dsa,
                sig,
                sig_ml_dsa,
            }],
            proof: next,
            pq: pq::MlDsaSeedMemo::empty(),
        };
        cred.pq.install(&cred.proof.to_bytes(), next_pq);
        cred
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
    /// The memoised ML-DSA-65 half of [`Self::proof`] — see [`pq::MlDsaSeedMemo`].
    ///
    /// The tail seed is this credential's PQ identity, and it is read on three
    /// paths: the PQ half of an attenuation signature, the PQ possession gate of
    /// [`Credential::verify_hybrid`], and (transitively) anything that presents
    /// the credential twice. Each read used to be a fresh ~200 ms Lean keygen of
    /// one unchanging key.
    ///
    /// [`Credential::attenuate`] RE-KEYS this credential in place, so the memo's
    /// seed binding is load-bearing here rather than defensive: after an
    /// attenuation the stored binding no longer matches the live `proof`, the
    /// entry is refused, and the new key is derived. A narrowed credential can
    /// never sign or present under its parent's PQ key.
    pub(crate) pq: pq::MlDsaSeedMemo,
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
        // ONE keygen for the fresh tail identity; it becomes this credential's
        // memo below, so the next attenuation or hybrid verify pays nothing.
        // The tail-identity keygen — see `credential::pq::ml_dsa_verify` for why the install is
        // here. `mint` and `attenuate` each MINT A NEW identity, so this derivation is not served
        // by any memo and `dregg-pq` aborts on it when no verified core is installed.
        #[cfg(test)]
        dregg_pq_testkit::install_or_panic();
        let next_pq = std::sync::Arc::new(dregg_pq::MlDsaKey::from_ed25519_seed(&next.to_bytes()));
        let next_pub_ml_dsa = pq::pk_bytes(&next_pq).to_vec();
        let prev_sig = self
            .blocks
            .last()
            .expect("a credential has a root block")
            .sig;
        let msg = block_digest(&prev_sig, &caveats, &next_pub, &next_pub_ml_dsa);
        let sig = self.proof.sign(&msg).to_bytes();
        // The OUTGOING tail signs this block; served from the memo when this
        // credential has already used its PQ half (a mint, a verify, an earlier
        // attenuation).
        let sig_ml_dsa = self
            .pq
            .sign(&self.proof.to_bytes(), &msg)
            .expect("ml-dsa signing is available")
            .to_vec();
        self.blocks.push(Block {
            caveats,
            next_pub,
            next_pub_ml_dsa,
            sig,
            sig_ml_dsa,
        });
        // Re-key, both halves together. Installing under the NEW seed's binding is
        // what makes the parent's entry unreachable rather than merely unused.
        self.proof = next;
        self.pq.install(&self.proof.to_bytes(), next_pq);
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
            vkey.verify_strict(&msg, &sig)
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
    ///
    /// **The gate ORDER is a cost decision, and it is load-bearing.** The PQ
    /// possession gate derives an ML-DSA key from the carried tail seed —
    /// 174–227 ms of Lean-verified keygen at the FFI boundary — and it used to run
    /// FIRST, on bytes nobody had authenticated yet. That made it reachable by any
    /// stranger: a caller mints their own chain and chooses BOTH the tail seed and
    /// the last block's `next_pub`, so the cheap gate above it is trivially
    /// satisfiable with no relationship to the enrolled root. It now runs AFTER
    /// the chain, so unauthenticated garbage dies on an ed25519 `verify_strict` in
    /// tens of microseconds and the derivation is reachable only behind a chain
    /// that verifies from the verifier's ENROLLED root.
    ///
    /// Both gates are conjunctive and both must still pass to admit, so the
    /// admitted set is unchanged — what moves is only which refusal is reported
    /// for a credential that fails BOTH. That case is exactly what tells the two
    /// orders apart, and `a_doubly_broken_credential_refuses_on_the_chain_not_the_keygen`
    /// pins it, with no stopwatch anywhere;
    /// `refusing_a_strangers_chain_costs_no_ml_dsa_keygen` states the resulting
    /// bound on what an unauthenticated caller can buy.
    pub fn verify_hybrid(&self, root: &HybridRootPublic, ctx: &Context) -> Result<(), Refusal> {
        // 1. Proof of possession, CLASSICAL half: the carried tail key must match
        //    the last block's `next_pub`. One scalar-basepoint multiply, so it
        //    stays in front of everything.
        let last = self.blocks.last().expect("a credential has a root block");
        if self.proof.verifying_key().to_bytes() != last.next_pub {
            return Err(Refusal::ProofMismatch);
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
            vkey.verify_strict(&msg, &sig)
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

        // 3. Proof of possession, POST-QUANTUM half: the held tail seed must
        //    derive the ML-DSA key the last block pins. Without it, a quantum
        //    forger who broke ed25519 could still not present a stripped prefix.
        //    Reached only now, behind a chain that verified from the enrolled
        //    root — see the gate-order note above. Memoised in `self.pq`, so a
        //    credential this process minted or attenuated already holds the key
        //    and pays nothing here.
        if self.pq.public_from_seed(&self.proof.to_bytes()).as_slice()
            != last.next_pub_ml_dsa.as_slice()
        {
            return Err(Refusal::PqProofMismatch);
        }

        // 4. The meet of all caveats (Token.admits) — fail-closed.
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
        vkey.verify_strict(&msg, &sig)
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
        // the quantum-safe possession gate, ISOLATED: the block is re-signed
        // under the root after the swap, so the whole chain still verifies and
        // the possession gate is the only thing left that can refuse. (Swapping
        // the key WITHOUT re-signing also breaks block 0's ed25519 signature —
        // that is `swapping_the_carried_pq_key_breaks_the_signature`, a different
        // tooth. Conflating them made this test pass for the wrong reason and
        // made it sensitive to which gate runs first.)
        let root = RootKey::from_seed([27u8; 32]);
        let mut cred = root.mint([read_caveat()]);
        cred.blocks[0].next_pub_ml_dsa = pq::ml_dsa_public_from_seed(&[0xCCu8; 32]).to_vec();
        let msg = block_digest(
            &cred.nonce,
            &cred.blocks[0].caveats,
            &cred.blocks[0].next_pub,
            &cred.blocks[0].next_pub_ml_dsa,
        );
        cred.blocks[0].sig = root.key.sign(&msg).to_bytes();
        cred.blocks[0].sig_ml_dsa = pq::ml_dsa_sign(&root.key.to_bytes(), &msg)
            .expect("ml-dsa signing is available")
            .to_vec();

        // The chain itself is sound now — the classical path admits it.
        assert_eq!(cred.verify(&root.public(), &ok_ctx()), Ok(()));
        // The hybrid path still refuses: the holder does not possess the ML-DSA
        // key the tail block pins.
        assert_eq!(
            cred.verify_hybrid(&root.public_hybrid(), &ok_ctx()),
            Err(Refusal::PqProofMismatch)
        );
    }

    #[test]
    fn refusing_a_strangers_chain_costs_no_ml_dsa_keygen() {
        // THE COST GATE. What an unauthenticated caller can make a verifier do.
        //
        // A stranger holds no credential from the enrolled root, so they mint
        // their own. They choose the tail seed AND the tail block's `next_pub` /
        // `next_pub_ml_dsa`, so every POSSESSION check passes for them —
        // possession says nothing about authority, only about self-consistency.
        // The gate that refuses is the chain, anchored at the ENROLLED root.
        //
        // `BadSignature { block: 0 }` is the assertion because it names WHERE the
        // verifier stopped: block 0's ed25519 `verify_strict`, tens of
        // microseconds in, having derived no ML-DSA key and verified no ML-DSA
        // signature. That is the whole cost of refusing a stranger.
        let enrolled = RootKey::from_seed([0x51u8; 32]);
        let stranger = RootKey::from_seed([0x52u8; 32]);
        let forged = stranger.mint([read_caveat()]).attenuate([read_caveat()]);

        // Internally consistent — it verifies perfectly under the stranger's own
        // root, so nothing about its SHAPE is refusable and no structural check
        // can be the thing that stops it.
        assert_eq!(
            forged.verify_hybrid(&stranger.public_hybrid(), &ok_ctx()),
            Ok(())
        );
        assert_eq!(
            forged.verify_hybrid(&enrolled.public_hybrid(), &ok_ctx()),
            Err(Refusal::BadSignature { block: 0 })
        );
    }

    #[test]
    fn a_doubly_broken_credential_refuses_on_the_chain_not_the_keygen() {
        // THE ORDER, pinned by the only input that can tell the two orders apart:
        // one that fails BOTH the chain gate and the PQ possession gate.
        //
        // Possession-first (what this module used to do) reports
        // `PqProofMismatch` — and reaches it by RUNNING the ~200 ms keygen on
        // unauthenticated bytes. Chain-first reports `BadSignature { block: 0 }`,
        // because step 2 returns before step 3 exists to run. Move the possession
        // check back in front and this test goes red on the refusal, with no
        // stopwatch anywhere.
        let enrolled = RootKey::from_seed([0x53u8; 32]);
        let stranger = RootKey::from_seed([0x54u8; 32]);
        let mut forged = stranger.mint([read_caveat()]);
        // …and break possession too: the tail block now pins a PQ key the holder
        // does not have.
        forged.blocks[0].next_pub_ml_dsa = pq::ml_dsa_public_from_seed(&[0xDDu8; 32]).to_vec();

        assert_eq!(
            forged.verify_hybrid(&enrolled.public_hybrid(), &ok_ctx()),
            Err(Refusal::BadSignature { block: 0 }),
            "a credential that fails both gates must refuse on the CHAIN — the \
             possession gate derives an ML-DSA key and must never run on bytes \
             the enrolled root has not vouched for"
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

#[cfg(test)]
mod ml_dsa_memo_tests {
    //! THE MEMOISED PQ HALF — each identity derives its ML-DSA-65 key ONCE, and
    //! the memo is bound to the seed that produced it.
    //!
    //! Liveness is proven by OBJECT IDENTITY (`Arc::ptr_eq`), never by a
    //! stopwatch: a timing assertion flakes on a loaded box and says nothing about
    //! which key was served. These go red if the memo is removed and cannot go
    //! green by accident.
    //!
    //! The falsifier — that two identities never share a derived key — is driven
    //! on the wire in `tests/mldsa_key_memo.rs`, where only the public API is in
    //! scope. Here we check the mechanism the falsifier depends on.
    use super::*;
    use std::sync::Arc;

    fn read_caveat() -> Caveat {
        Caveat::FirstParty(Pred::AttrEq {
            key: "tool".into(),
            value: "read".into(),
        })
    }

    #[test]
    fn a_root_derives_its_pq_key_once() {
        let root = RootKey::from_seed([0x61u8; 32]);
        let seed = root.key.to_bytes();
        let first = root.pq.key_for(&seed);
        let second = root.pq.key_for(&seed);
        assert!(
            Arc::ptr_eq(&first, &second),
            "a root must serve ONE derived ML-DSA key, not two equal ones — \
             delete the memo and this goes red"
        );
        // …and it is the key the root publishes as its enrolled anchor.
        assert_eq!(root.public_hybrid().ml_dsa, first.public_bytes());
    }

    #[test]
    fn a_minted_credential_already_holds_its_tail_key() {
        // `mint` derives the fresh tail key once, for the block; the credential
        // that OWNS that tail identity keeps it, so the first hybrid verify pays
        // nothing.
        let root = RootKey::from_seed([0x62u8; 32]);
        let cred = root.mint([read_caveat()]);
        let held = cred.pq.key_for(&cred.proof.to_bytes());
        assert!(
            Arc::ptr_eq(&held, &cred.pq.key_for(&cred.proof.to_bytes())),
            "the minted credential must not re-derive its own tail key"
        );
        assert_eq!(
            held.public_bytes(),
            cred.blocks[0].next_pub_ml_dsa,
            "the key the credential holds must be the one its block pins"
        );
    }

    #[test]
    fn attenuation_rekeys_the_memo_and_the_parent_entry_is_unreachable() {
        // THE SEED-BINDING WALL, load-bearing rather than defensive: `attenuate`
        // re-keys a credential IN PLACE. A memo that keyed on the object rather
        // than on the seed would keep serving the parent's PQ key and the child
        // would sign under an identity it no longer has.
        let root = RootKey::from_seed([0x63u8; 32]);
        let cred = root.mint([read_caveat()]);
        let parent_seed = cred.proof.to_bytes();
        let parent_key = cred.pq.key_for(&parent_seed);

        let cred = cred.attenuate([read_caveat()]);
        let child_seed = cred.proof.to_bytes();
        assert_ne!(parent_seed, child_seed, "attenuation must re-key");

        let child_key = cred.pq.key_for(&child_seed);
        assert!(
            !Arc::ptr_eq(&parent_key, &child_key),
            "the child must not be served its parent's derived key"
        );
        assert_eq!(
            child_key.public_bytes(),
            cred.blocks[1].next_pub_ml_dsa,
            "the child holds exactly the key its own block pins"
        );

        // Asking the CHILD's memo for the PARENT's seed must MISS and re-derive —
        // the entry is gone, not merely shadowed. A fresh object, equal bytes.
        let rederived = cred.pq.key_for(&parent_seed);
        assert!(!Arc::ptr_eq(&rederived, &parent_key));
        assert_eq!(rederived.public_bytes(), parent_key.public_bytes());
    }

    #[test]
    fn the_memo_serves_a_bit_identical_key() {
        // The memo changes latency, not what is signed or BY WHICH KEY.
        let root = RootKey::from_seed([0x64u8; 32]);
        let seed = root.key.to_bytes();
        dregg_pq_testkit::install_or_panic();
        let fresh = dregg_pq::MlDsaKey::from_ed25519_seed(&seed);
        assert_eq!(
            root.pq.public_from_seed(&seed).as_slice(),
            fresh.public_bytes(),
            "the memoised key must be bit-identical to a fresh derivation"
        );

        // ⚑ THE SIGNATURE IS NOT HEDGED HERE, AND FINDING THAT OUT COST AN ABORTING TEST BINARY.
        // This assertion used to be `assert_ne!` under the note "the credential-chain PQ signature
        // is HEDGED from OS entropy, so two signatures over one message differ by construction",
        // with the escape hatch "if it ever becomes deterministic, tighten this to byte-equality
        // rather than dropping the check". That is exactly what happened, and the escape hatch is
        // being taken.
        //
        // The two ML-DSA backends DIFFER OBSERVABLY here. `dregg_pq::MlDsaKey::try_sign` on the
        // `fips204` crate is hedged (it draws `rnd` from the OS), so two signatures over one
        // message differ. The Lean-verified REAL sign core — which this binary now installs, and
        // which a deployed node installs — is the DETERMINISTIC FIPS 204 variant, so they are
        // byte-identical. Nothing here noticed for as long as this binary aborted on its first PQ
        // op and asserted nothing at all.
        //
        // Byte-equality is the stronger claim and it is the one that holds on the deployed backend,
        // so it is what is checked. If a future build reaches this on the crate fallback instead,
        // `install_or_panic` above will have failed first.
        let msg = [0x9au8; 32];
        let memoised = root
            .pq
            .sign(&seed, &msg)
            .expect("ml-dsa signing is available");
        let independent = pq::ml_dsa_sign(&seed, &msg).expect("ml-dsa signing is available");
        assert_eq!(
            memoised, independent,
            "the verified Lean sign core is deterministic, so the memoised and independently \
             derived keys must produce byte-identical signatures over one message"
        );
        let key = fresh.public_bytes();
        assert!(pq::ml_dsa_verify(&key, &msg, &memoised));
        assert!(pq::ml_dsa_verify(&key, &msg, &independent));
    }

    #[test]
    fn a_decoded_credential_starts_with_an_empty_memo_and_fills_it_once() {
        // A credential off the wire has no derivation to inherit — the first
        // hybrid use pays, and only the first.
        let root = RootKey::from_seed([0x65u8; 32]);
        let cred = root.mint([read_caveat()]);
        let decoded = Credential::decode(&cred.encode()).expect("decode");

        let first = decoded.pq.key_for(&decoded.proof.to_bytes());
        let second = decoded.pq.key_for(&decoded.proof.to_bytes());
        assert!(
            Arc::ptr_eq(&first, &second),
            "a decoded credential must derive its tail PQ key ONCE"
        );
        assert_eq!(first.public_bytes(), cred.blocks[0].next_pub_ml_dsa);
    }
}

#[cfg(test)]
mod strict_smallorder_tests {
    //! The strictness tooth for the credential-chain ed25519 verify.
    //!
    //! `Credential::verify` roots the chain at the ISSUER key the *verifier*
    //! supplies (pinned config: `Policy::public_key_hex`, `HostAuthority::public`,
    //! `ShareAuthority::public` — never read from the wire), so under an honest
    //! pinned root this is defense-in-depth, not a live wire forgery. But the
    //! chain verify feeds an ATTACKER-CHOSEN verifying key into `dalek` at every
    //! block after the root (each `block.next_pub` is credential bytes), and a
    //! future caller that ever sourced the root from the wire would inherit the
    //! full small-order universal-forgery vector. This tooth pins that the verify
    //! path is `verify_strict` — fail-closed on a small-order key with NO secret —
    //! by EXHIBITING the forgery both ways in one place.
    use super::*;

    /// The edwards25519 identity point, compressed: `y = 1`, sign bit 0. Order 1,
    /// hence small-order — the canonical weak key `verify_strict` must reject.
    fn identity_point() -> [u8; 32] {
        let mut b = [0u8; 32];
        b[0] = 1;
        b
    }

    /// The no-secret universal forgery under a small-order key: `R = identity`,
    /// `s = 0`. For a small-order `A`, `h·A = identity`, so the cofactored check
    /// `s·B = R + h·A` becomes `identity = identity` for EVERY message.
    fn forged_sig() -> [u8; 64] {
        let mut sig = [0u8; 64];
        sig[0] = 1; // R = compressed identity; s stays all-zero.
        sig
    }

    /// Build a one-block credential whose block-0 signature is the no-secret
    /// forgery above, presentable (possession passes: `next_pub` is our own key)
    /// and caveat-free (so only the signature gate decides).
    fn forged_credential() -> Credential {
        let proof = SigningKey::from_bytes(&[7u8; 32]);
        let next_pub = proof.verifying_key().to_bytes();
        Credential {
            nonce: [0u8; 32],
            blocks: vec![Block {
                caveats: Vec::new(),
                next_pub,
                next_pub_ml_dsa: Vec::new(),
                sig: forged_sig(),
                sig_ml_dsa: Vec::new(),
            }],
            proof,
            pq: Default::default(),
        }
    }

    #[test]
    fn cofactored_verify_accepts_the_no_secret_forgery_strict_refuses_it() {
        // The exhibit: exactly what `Credential::verify` computes for block 0.
        let root = identity_point();
        let cred = forged_credential();
        let msg = block_digest(
            &cred.nonce,
            &cred.blocks[0].caveats,
            &cred.blocks[0].next_pub,
            &cred.blocks[0].next_pub_ml_dsa,
        );
        let vkey = VerifyingKey::from_bytes(&root).expect("identity decompresses");
        let sig = Signature::from_bytes(&cred.blocks[0].sig);

        // (a) The COFACTORED trait verify — what the module used before this tooth —
        //     ACCEPTS the forgery made with no secret. (fn-local, indented import:
        //     the ed25519_strict_guard's column-0 detector ignores it.)
        {
            use ed25519_dalek::Verifier;
            assert!(
                vkey.verify(&msg, &sig).is_ok(),
                "cofactored verify must accept the small-order (R=identity, s=0) forgery — \
                 if this fails the exhibit is wrong, not the fix"
            );
        }

        // (b) `verify_strict` — the deployed path — REFUSES it (small-order A and R).
        assert!(vkey.verify_strict(&msg, &sig).is_err());

        // (c) End to end through the real credential verify: fail-closed with the
        //     block-0 signature refusal. Reverting the verify site to the cofactored
        //     `.verify` turns this Err into Ok(()) — the tooth goes RED.
        assert_eq!(
            cred.verify(&PublicKey(root), &Context::new()),
            Err(Refusal::BadSignature { block: 0 })
        );
    }
}
