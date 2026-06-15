//! **The vision predicate, for real** — a genuine `Custom { vk_hash }` proof
//! obligation backing fog-of-war, NOT an inert identity tag.
//!
//! ## The wink this module closes
//!
//! [`crate::game`] first used `AuthRequired::Custom { vk_hash }` as a pure
//! *identity tag*: two sides got distinct `Custom` values, and the genuine
//! lattice's incomparability (`cell/src/permissions.rs::is_narrower_or_equal` —
//! different vk_hashes neither attenuate) made `is_attenuation(Blue, Red) ==
//! false`, so the membrane refused a cross-player projection. That is **not
//! illegal** — the lattice really does refuse, the fog gate is real. It is *just*
//! that the `vk_hash` was **inert**: nobody had to *prove* anything to hold the
//! cap, so "provably cannot peek" leaned on a `provably` no one had earned. The
//! gate was real; the authority-to-pass-it was free.
//!
//! This module makes the `vk_hash` **load-bearing**: it is a real
//! [`canonical_predicate_vk`] over a real canonical predicate program, registered
//! in a real [`WitnessedPredicateRegistry`], and to hold/exercise a side's vision
//! authority you must **produce a proof the registry verifies** — a genuine
//! knowledge-of-secret proof over the canonical signing message, **fail-closed**:
//! the wrong side cannot synthesize a verifying proof, so it is refused at the
//! verifier, not merely at the lattice.
//!
//! ## What is real here (Tier A — the genuine proof obligation)
//!
//! Every piece is the REAL dregg predicate machinery `dregg-cell` re-exports:
//!
//! - **`vk_hash` = [`canonical_predicate_vk`]`(canonical_bytes)`** — a real
//!   BLAKE3-keyed hash of a real canonical predicate program
//!   ([`VisionProgram::canonical_bytes`]), re-derivable by ANY validator (the
//!   re-execution contract: a validator with the bytes confirms
//!   `canonical_predicate_vk(bytes) == vk_hash`).
//! - **The verifier** [`FogVisionVerifier`] implements the real
//!   [`WitnessedPredicateVerifier`] trait and is registered under that `vk_hash`
//!   via [`WitnessedPredicateRegistry::register_custom`] — the SAME registry +
//!   dispatch the `dregg-turn` executor runs for `Authorization::Custom`
//!   (`turn/src/executor/authorize.rs::verify_custom_authorization`).
//! - **The proof** is a genuine Ed25519 signature (the same `ed25519-dalek` the
//!   firmament's capability proofs verify) over the predicate's input — the
//!   knowledge-of-secret statement "the holder of vision-key K authorized THIS
//!   message". Only the side that holds the secret key can produce it. An
//!   adversary with the public key + the message **cannot** forge it (EUF-CMA).
//! - **The producer** [`FogVisionProducer`] implements the real
//!   [`WitnessProducer`] trait (the left adjoint of the verifier) and synthesizes
//!   the proof from the side's [`VisionKeypair`]. The unit-counit identity holds:
//!   feeding the producer's output back through the verifier (same commitment +
//!   input) accepts — asserted in [`tests`].
//!
//! ## What is the seam (Tier B — the FRI-STARK AIR, named not faked)
//!
//! `VK-AS-RE-EXECUTION-RECIPE.md` §v2: a *layered* `vk_hash` via
//! [`dregg_cell::predicate::canonical_predicate_vk_v2`] commits additionally to an
//! **AIR fingerprint** — the verifier's AIR is a real `dregg-circuit` STARK proven
//! by plonky3. That is the maximal form (a zero-knowledge circuit, not a
//! signature). It **cannot** live in this crate: `dregg-cell` must not depend on
//! `dregg-circuit` (the design's dependency-cycle rule — exactly why
//! `WitnessedPredicateRegistry::default_builtins` ships `NotYetWiredVerifier`
//! fail-closed for the STARK kinds, and the host upgrades them). The Tier-B
//! vision-AIR therefore belongs in `dregg-circuit` + a `dregg-turn` integration,
//! registered the SAME way (`register_custom` keyed on a `canonical_predicate_vk_v2`
//! hash) — the obligation shape this module builds is identical; only the
//! verifier's *internal* algebra (Ed25519 → STARK) and the `vk_hash` recipe
//! (`_vk` → `_vk_v2`) change. The producer⊣verifier wiring here is the honest
//! Tier-A realization; Tier B is a swap of the verifier body, not a new design.

use std::sync::Arc;

use dregg_cell::predicate::{
    canonical_predicate_vk, InputRef, WitnessProducerError, WitnessedPredicateError,
    WitnessedPredicateKind, WitnessedPredicateVerifier,
};
// Re-export the genuine predicate-machinery types this module builds on, so callers
// (the game's proof-backed vision gate) name them through this module — the SAME
// real `dregg_cell::predicate` types, not parallel ones.
pub use dregg_cell::predicate::{
    PredicateInput, WitnessProducer, WitnessedPredicate, WitnessedPredicateRegistry,
};
// The GENUINE dregg crypto surface (the same `dregg_types` Ed25519 the firmament's
// capability proofs + the attestation quorum use) — `verify_strict` under the hood,
// rejecting non-canonical signatures. We name the dregg wrapper, never `ed25519-dalek`
// directly, so the proof rides the same crypto the rest of the protocol does.
use dregg_types::{PublicKey, Signature, SigningKey};

/// The domain-separation tag for the fog-of-war vision predicate program. Part of
/// the canonical bytes the `vk_hash` commits to (so a vision predicate cannot be
/// confused with any other app's `Custom` predicate).
const VISION_PROGRAM_DOMAIN: &[u8] = b"dregg-fogwar-vision-predicate-v1";

/// A vision keypair — the secret a player must HOLD to exercise its side's vision
/// authority, and the public key the predicate binds. The genuine
/// knowledge-of-secret: only the holder of [`Self::secret`] can produce a proof
/// the [`FogVisionVerifier`] accepts.
///
/// This is a real Ed25519 keypair (the same `ed25519-dalek` the firmament's
/// capability proofs use). A side's vision authority is "knowledge of this secret"
/// — provable (a signature) and unforgeable (EUF-CMA), not an inert tag.
#[derive(Clone)]
pub struct VisionKeypair {
    signing: SigningKey,
}

impl VisionKeypair {
    /// Derive a deterministic vision keypair from a 32-byte seed (a side's secret
    /// material). Deterministic so the demo/tests are reproducible; production mints
    /// these from real entropy (`dregg_types::generate_keypair`). The seed IS the
    /// secret — whoever holds it can prove the side's vision authority.
    pub fn from_seed(seed: [u8; 32]) -> Self {
        VisionKeypair {
            signing: SigningKey::from_bytes(&seed),
        }
    }

    /// The public key the predicate's `commitment` binds — published openly (a
    /// validator/auditor uses it to re-verify a vision proof). Holding the public
    /// key does NOT let you produce a proof; only the secret does. The genuine
    /// `dregg_types::PublicKey`.
    pub fn public_key(&self) -> PublicKey {
        self.signing.public_key()
    }

    /// The bound public key as raw bytes (the predicate program / commitment field).
    pub fn public_key_bytes(&self) -> [u8; 32] {
        self.signing.public_key().0
    }

    /// The canonical vision predicate program for THIS side — its public key bound
    /// under the vision domain. The `vk_hash` is `canonical_predicate_vk` of this.
    pub fn program(&self) -> VisionProgram {
        VisionProgram {
            vision_public_key: self.public_key_bytes(),
        }
    }

    /// Produce the genuine proof (an Ed25519 signature, via the dregg crypto
    /// surface) over `signing_message` — the knowledge-of-secret witness the
    /// verifier accepts. This is the prover side; only a holder of the secret can
    /// call it to a verifying result.
    fn sign(&self, signing_message: &[u8]) -> [u8; 64] {
        dregg_types::sign(&self.signing, signing_message).0
    }
}

/// The canonical vision predicate **program** — the executable statement a
/// `vk_hash` commits to. Its [`Self::canonical_bytes`] are the bytes a validator
/// re-executes (here: "the proof is an Ed25519 signature, over the predicate input,
/// by `vision_public_key`"). The whole point: the `vk_hash` is a hash of THIS, so
/// it is re-derivable and meaningful, not a fabricated tag.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VisionProgram {
    /// The Ed25519 public key the vision proof must verify against — the side's
    /// committed vision identity. Bound into the canonical bytes (so two sides'
    /// programs, hence vk_hashes, differ) AND carried as the predicate's
    /// `commitment` (so the verifier knows which key to check).
    pub vision_public_key: [u8; 32],
}

impl VisionProgram {
    /// The canonical executable bytes the `vk_hash` commits to. Domain-tagged +
    /// the bound public key. A validator re-derives `vk_hash =
    /// canonical_predicate_vk(canonical_bytes)` to confirm registry honesty
    /// (the re-execution contract, `VK-AS-RE-EXECUTION-RECIPE.md` §2.2).
    pub fn canonical_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(VISION_PROGRAM_DOMAIN.len() + 32);
        bytes.extend_from_slice(VISION_PROGRAM_DOMAIN);
        bytes.extend_from_slice(&self.vision_public_key);
        bytes
    }

    /// **The real `vk_hash`** — `canonical_predicate_vk(self.canonical_bytes())`.
    /// THIS is what makes the `Custom { vk_hash }` load-bearing: it is a genuine
    /// BLAKE3-keyed commitment to a real predicate program, not an opaque tag.
    pub fn vk_hash(&self) -> [u8; 32] {
        canonical_predicate_vk(&self.canonical_bytes())
    }

    /// The predicate's `commitment` field — the bound vision public key. The
    /// verifier reads THIS to know which key the proof must verify against.
    pub fn commitment(&self) -> [u8; 32] {
        self.vision_public_key
    }

    /// The full [`WitnessedPredicate`] declaration a player presents to exercise
    /// this side's vision authority: kind = `Custom { vk_hash }`, commitment = the
    /// bound public key, input = the canonical signing message (the auth input
    /// shape the executor binds, `InputRef::SigningMessage`), proof at
    /// `proof_witness_index` in the action's witness blobs.
    pub fn witnessed_predicate(&self, proof_witness_index: usize) -> WitnessedPredicate {
        WitnessedPredicate::custom(
            self.vk_hash(),
            self.commitment(),
            InputRef::SigningMessage,
            proof_witness_index,
        )
    }
}

/// **The genuine vision verifier** — a real [`WitnessedPredicateVerifier`]
/// registered under the vision `vk_hash`. It accepts iff the proof is a valid
/// Ed25519 signature, over the predicate input, by the public key the
/// `commitment` binds. This is the counit of the predicate adjunction: given a
/// witness (the signature), decide acceptance.
///
/// Fail-closed: an empty/garbage proof, a signature by the wrong key, or a
/// signature over a different message all REJECT. Only a holder of the side's
/// secret key, signing THIS message, passes — so fog-of-war's "provably cannot
/// peek" is now backed by a real proof obligation (EUF-CMA), not lattice
/// incomparability alone.
#[derive(Clone, Debug)]
pub struct FogVisionVerifier {
    /// The `vk_hash` this verifier is registered under (= the bound side's
    /// program hash). Carried so [`WitnessedPredicateVerifier::kind`] reports the
    /// right `Custom { vk_hash }`.
    vk_hash: [u8; 32],
}

impl FogVisionVerifier {
    /// A verifier for the side whose vision program hashes to `vk_hash`. Construct
    /// it from the side's [`VisionProgram`] so the registered hash is the genuine
    /// one.
    pub fn for_program(program: &VisionProgram) -> Self {
        FogVisionVerifier {
            vk_hash: program.vk_hash(),
        }
    }
}

impl WitnessedPredicateVerifier for FogVisionVerifier {
    fn name(&self) -> &'static str {
        "fogwar-vision-ed25519"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::Custom {
            vk_hash: self.vk_hash,
        }
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        // The auth input shape MUST be the canonical signing message (the same
        // shape the executor binds for Authorization::Custom). Any other shape is a
        // surface misuse — reject as a shape mismatch (NOT a silent accept).
        let message: &[u8] = match input {
            PredicateInput::SigningMessage(msg) => msg,
            other => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: "fogwar-vision-ed25519",
                    expected: "SigningMessage",
                    actual: predicate_input_tag(other),
                });
            }
        };

        // The proof is a 64-byte Ed25519 signature. Anything else (empty, wrong
        // length, garbage) fails closed.
        if proof_bytes.len() != 64 {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: "fogwar-vision-ed25519",
                reason: format!(
                    "vision proof must be a 64-byte Ed25519 signature, got {} bytes",
                    proof_bytes.len()
                ),
            });
        }
        let mut sig_bytes = [0u8; 64];
        sig_bytes.copy_from_slice(proof_bytes);

        // The commitment IS the side's bound vision public key. Verify the
        // signature over the predicate input against it — the GENUINE
        // knowledge-of-secret check. Wrong key / wrong message / forged signature
        // all reject here.
        if verify_vision_signature(commitment, message, &sig_bytes) {
            Ok(())
        } else {
            Err(WitnessedPredicateError::Rejected {
                kind_name: "fogwar-vision-ed25519",
                reason: "vision proof signature did not verify against the committed \
                         vision public key (the prover does not hold this side's secret)"
                    .to_string(),
            })
        }
    }
}

/// **The genuine vision producer** — a real [`WitnessProducer`] (the left adjoint /
/// unit of the predicate adjunction). Given the side's [`VisionKeypair`], it
/// synthesizes the proof (the Ed25519 signature) the [`FogVisionVerifier`]
/// accepts. Only a holder of the secret can construct one — which is the whole
/// point: producing a verifying vision proof IS holding the side's vision
/// authority.
#[derive(Clone)]
pub struct FogVisionProducer {
    keypair: VisionKeypair,
    vk_hash: [u8; 32],
}

impl FogVisionProducer {
    /// A producer holding `keypair` (the side's secret). The `vk_hash` is derived
    /// from the keypair's program, so the producer is registered under the same
    /// hash as its verifier.
    pub fn new(keypair: VisionKeypair) -> Self {
        let vk_hash = keypair.program().vk_hash();
        FogVisionProducer { keypair, vk_hash }
    }
}

impl WitnessProducer for FogVisionProducer {
    fn name(&self) -> &'static str {
        "fogwar-vision-ed25519-producer"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::Custom {
            vk_hash: self.vk_hash,
        }
    }

    fn produce(
        &self,
        commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        _witness_bytes: &[u8],
    ) -> Result<Vec<u8>, WitnessProducerError> {
        // The producer must be synthesizing for ITS OWN bound key — the commitment
        // must equal the keypair's public key. (A producer for Blue cannot mint
        // Red's proof; this is the producer-side analog of the verifier's binding.)
        if commitment != &self.keypair.public_key_bytes() {
            return Err(WitnessProducerError::ProducerFailed {
                kind_name: "fogwar-vision-ed25519-producer",
                reason: "commitment is not this producer's bound vision public key \
                         (cannot synthesize a proof for another side's vision key)"
                    .to_string(),
            });
        }
        // The input shape must be the canonical signing message (same shape the
        // verifier consumes) — the unit/counit operate on the same input.
        let message: &[u8] = match input {
            PredicateInput::SigningMessage(msg) => msg,
            other => {
                return Err(WitnessProducerError::InputShapeMismatch {
                    kind_name: "fogwar-vision-ed25519-producer",
                    expected: "SigningMessage",
                    actual: predicate_input_tag(other),
                });
            }
        };
        // Synthesize the genuine proof: an Ed25519 signature over the message by the
        // side's secret. This is the only step that needs the secret — it IS the
        // act of exercising vision authority.
        Ok(self.keypair.sign(message).to_vec())
    }
}

/// Register a side's genuine vision verifier into `registry` under its real
/// `vk_hash`. After this, the registry will dispatch a `Custom { vk_hash }`
/// predicate for this side to [`FogVisionVerifier`] — the SAME registry the
/// executor consults for `Authorization::Custom`. Returns the `vk_hash` registered
/// (so callers can bind a cell's `AuthRequired::Custom { vk_hash }` to it).
pub fn register_vision_verifier(
    registry: &mut WitnessedPredicateRegistry,
    program: &VisionProgram,
) -> [u8; 32] {
    let vk_hash = program.vk_hash();
    registry.register_custom(vk_hash, Arc::new(FogVisionVerifier::for_program(program)));
    vk_hash
}

/// **Verify a vision proof through the real registry** — the genuine fog-of-war
/// gate. Returns `Ok(())` iff `registry` has a verifier for the predicate's
/// `vk_hash` AND that verifier accepts the proof over `signing_message`. This is
/// exactly the call the executor's `verify_custom_authorization` makes (minus the
/// executor-internal signing-message construction, which the caller supplies here).
///
/// A player can pass this gate IFF they could produce a proof the registry
/// verifies — i.e. IFF they hold the side's vision secret. The wrong side cannot,
/// so the no-peek property is now a real proof obligation, fail-closed.
pub fn verify_vision_proof(
    registry: &WitnessedPredicateRegistry,
    predicate: &WitnessedPredicate,
    signing_message: &[u8],
    proof_bytes: &[u8],
) -> Result<(), WitnessedPredicateError> {
    let input = PredicateInput::SigningMessage(signing_message);
    registry.verify(predicate, &input, proof_bytes)
}

/// Ed25519 verification of a vision proof — the genuine crypto check via the dregg
/// `PublicKey::verify` surface (`verify_strict` under the hood, the SAME check the
/// firmament's capability proofs + the attestation quorum use). Returns `true` iff
/// `signature` is a valid Ed25519 signature over `message` by `public_key`. An
/// invalid key, a signature over a different message, or a forged signature all
/// return `false` — fail-closed.
fn verify_vision_signature(public_key: &[u8; 32], message: &[u8], signature: &[u8; 64]) -> bool {
    PublicKey(*public_key).verify(message, &Signature(*signature))
}

/// A short tag for a [`PredicateInput`] variant (for shape-mismatch diagnostics).
fn predicate_input_tag(input: &PredicateInput<'_>) -> &'static str {
    match input {
        PredicateInput::Slot(_) => "Slot",
        PredicateInput::Bytes(_) => "Bytes",
        PredicateInput::PublicInput(_) => "PublicInput",
        PredicateInput::Sender(_) => "Sender",
        PredicateInput::SigningMessage(_) => "SigningMessage",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn seed(b: u8) -> [u8; 32] {
        let mut s = [0u8; 32];
        s[0] = b;
        s[31] = b.wrapping_mul(7);
        s
    }

    fn blue_keys() -> VisionKeypair {
        VisionKeypair::from_seed(seed(0xB1))
    }
    fn red_keys() -> VisionKeypair {
        VisionKeypair::from_seed(seed(0xED))
    }

    // ── The vk_hash is REAL: a canonical_predicate_vk of a real program. ──

    #[test]
    fn the_vk_hash_is_a_real_canonical_predicate_vk_re_derivable_by_a_validator() {
        // THE anti-toy hinge: the vk_hash is canonical_predicate_vk(canonical_bytes)
        // — re-derivable by any validator from the program bytes, NOT a fabricated
        // tag. This is the re-execution contract (VK-AS-RE-EXECUTION-RECIPE §2.2).
        let prog = blue_keys().program();
        let bytes = prog.canonical_bytes();
        // A validator re-derives the hash from the bytes and it MATCHES.
        assert_eq!(prog.vk_hash(), canonical_predicate_vk(&bytes));
        // The bytes are the genuine domain-tagged program (not opaque garbage).
        assert!(bytes.starts_with(VISION_PROGRAM_DOMAIN));
        assert_eq!(
            &bytes[VISION_PROGRAM_DOMAIN.len()..],
            &blue_keys().public_key_bytes()
        );
    }

    #[test]
    fn two_sides_have_distinct_real_vk_hashes() {
        // Distinct programs (distinct bound keys) → distinct REAL vk_hashes. This is
        // the genuine version of the identity distinction: not two arbitrary tags,
        // but two hashes of two real, different predicate programs.
        let blue = blue_keys().program().vk_hash();
        let red = red_keys().program().vk_hash();
        assert_ne!(blue, red, "the two sides' vision programs hash differently");
    }

    // ── THE KEYSTONE, now a real proof obligation: only the holder can pass. ──

    #[test]
    fn only_the_holder_of_the_secret_can_produce_a_verifying_vision_proof() {
        // THE genuine no-peek root: producing a verifying vision proof requires the
        // side's SECRET. Blue, holding Blue's secret, passes; Red, NOT holding
        // Blue's secret, CANNOT forge one — fail-closed at the verifier (EUF-CMA),
        // not merely at the lattice.
        let blue = blue_keys();
        let blue_prog = blue.program();
        let mut registry = WitnessedPredicateRegistry::empty();
        register_vision_verifier(&mut registry, &blue_prog);

        // The signing message the player must authorize (the executor binds this; we
        // supply a representative one).
        let message = b"fogwar turn: Blue projects tile (4,4) at nonce 7";

        // Blue PRODUCES a genuine proof (it holds the secret) — and it VERIFIES.
        let producer = FogVisionProducer::new(blue.clone());
        let wp = blue_prog.witnessed_predicate(0);
        let proof = producer
            .produce(
                &blue_prog.commitment(),
                &PredicateInput::SigningMessage(message),
                &[],
            )
            .expect("Blue holds the secret → can produce the proof");
        assert_eq!(proof.len(), 64, "the proof is a real Ed25519 signature");
        assert!(
            verify_vision_proof(&registry, &wp, message, &proof).is_ok(),
            "Blue's genuine proof verifies — it holds the secret"
        );

        // RED tries to pass Blue's gate. Red does NOT hold Blue's secret. It cannot
        // produce a verifying proof for Blue's commitment:
        //  (a) Red's producer refuses to sign for Blue's commitment (binding), and
        let red_producer = FogVisionProducer::new(red_keys());
        let red_attempt = red_producer.produce(
            &blue_prog.commitment(),
            &PredicateInput::SigningMessage(message),
            &[],
        );
        assert!(
            matches!(
                red_attempt,
                Err(WitnessProducerError::ProducerFailed { .. })
            ),
            "Red's producer refuses to mint a proof for Blue's vision key"
        );
        //  (b) and even a proof Red signs with ITS OWN key fails Blue's verifier
        //      (the signature does not verify against Blue's committed public key).
        let red_self_signed = red_keys().sign(message).to_vec();
        let forged = verify_vision_proof(&registry, &wp, message, &red_self_signed);
        assert!(
            matches!(forged, Err(WitnessedPredicateError::Rejected { .. })),
            "a proof signed with Red's key is REJECTED by Blue's vision verifier (no-peek, for real)"
        );
    }

    #[test]
    fn a_proof_over_a_different_message_is_rejected_replay_binding() {
        // The proof is bound to the MESSAGE: a signature over message A does not
        // authorize message B. This is the replay binding the executor relies on
        // (the signing message carries federation_id + nonce + action hash).
        let blue = blue_keys();
        let prog = blue.program();
        let mut registry = WitnessedPredicateRegistry::empty();
        register_vision_verifier(&mut registry, &prog);
        let wp = prog.witnessed_predicate(0);

        let message_a = b"Blue authorizes turn at nonce 7";
        let message_b = b"Blue authorizes turn at nonce 8"; // a DIFFERENT turn
        let proof_a = blue.sign(message_a).to_vec();

        // The proof over A verifies for A...
        assert!(verify_vision_proof(&registry, &wp, message_a, &proof_a).is_ok());
        // ...but is REJECTED when replayed against B (a different turn/nonce).
        assert!(
            matches!(
                verify_vision_proof(&registry, &wp, message_b, &proof_a),
                Err(WitnessedPredicateError::Rejected { .. })
            ),
            "a vision proof does not replay to a different signing message"
        );
    }

    #[test]
    fn an_empty_or_garbage_proof_is_rejected_fail_closed() {
        // Fail-closed: an empty proof or non-signature garbage is rejected (it is
        // not a 64-byte Ed25519 signature). The previous inert-tag form had NO such
        // obligation; now there is a real one.
        let prog = blue_keys().program();
        let mut registry = WitnessedPredicateRegistry::empty();
        register_vision_verifier(&mut registry, &prog);
        let wp = prog.witnessed_predicate(0);
        let message = b"any message";

        assert!(
            matches!(
                verify_vision_proof(&registry, &wp, message, &[]),
                Err(WitnessedPredicateError::Rejected { .. })
            ),
            "an empty proof is rejected"
        );
        assert!(
            matches!(
                verify_vision_proof(&registry, &wp, message, &[0u8; 10]),
                Err(WitnessedPredicateError::Rejected { .. })
            ),
            "a too-short garbage proof is rejected"
        );
        // A 64-byte but invalid (all-zero) signature is also rejected.
        assert!(
            matches!(
                verify_vision_proof(&registry, &wp, message, &[0u8; 64]),
                Err(WitnessedPredicateError::Rejected { .. })
            ),
            "a 64-byte non-signature is rejected by the real Ed25519 check"
        );
    }

    #[test]
    fn an_unregistered_vk_hash_fails_closed() {
        // If the registry has NO verifier for the predicate's vk_hash, the gate
        // refuses (KindNotRegistered) — the executor's fail-closed posture. A
        // player whose side was never registered cannot pass.
        let blue_prog = blue_keys().program();
        let empty_registry = WitnessedPredicateRegistry::empty(); // nothing registered
        let wp = blue_prog.witnessed_predicate(0);
        let proof = blue_keys().sign(b"m").to_vec();
        assert!(
            matches!(
                verify_vision_proof(&empty_registry, &wp, b"m", &proof),
                Err(WitnessedPredicateError::KindNotRegistered { .. })
            ),
            "an unregistered vision vk_hash fails closed"
        );
    }

    // ── The producer ⊣ verifier adjunction: the unit-counit round-trip. ──

    #[test]
    fn the_producer_verifier_round_trip_holds_unit_counit() {
        // The adjunction identity (CROSS-CELL-CATEGORICAL-ANALYSIS §3.4): for a
        // well-formed (commitment, input, witness), the proof the producer (unit)
        // synthesizes verifies under the verifier (counit) with the same
        // (commitment, input). This is the genuine producer⊣verifier pair, not a
        // stub.
        for s in [0xB1u8, 0xED, 0x42, 0x07] {
            let keys = VisionKeypair::from_seed(seed(s));
            let prog = keys.program();
            let mut registry = WitnessedPredicateRegistry::empty();
            register_vision_verifier(&mut registry, &prog);
            let producer = FogVisionProducer::new(keys);
            let wp = prog.witnessed_predicate(0);
            let message = format!("turn for side {s}");

            let proof = producer
                .produce(
                    &prog.commitment(),
                    &PredicateInput::SigningMessage(message.as_bytes()),
                    &[],
                )
                .expect("the holder produces a proof");
            assert!(
                verify_vision_proof(&registry, &wp, message.as_bytes(), &proof).is_ok(),
                "unit-counit: the produced proof verifies (side {s})"
            );
        }
    }

    #[test]
    fn the_verifier_rejects_a_non_signing_message_input_shape() {
        // The auth input shape is SigningMessage; a slot/sender input is a surface
        // misuse and rejected (InputShapeMismatch), never silently accepted.
        let prog = blue_keys().program();
        let verifier = FogVisionVerifier::for_program(&prog);
        let proof = blue_keys().sign(b"m").to_vec();
        let slot = [0u8; 32];
        let r = verifier.verify(&prog.commitment(), &PredicateInput::Slot(&slot), &proof);
        assert!(
            matches!(r, Err(WitnessedPredicateError::InputShapeMismatch { .. })),
            "a non-SigningMessage input is a shape mismatch"
        );
    }

    #[test]
    fn the_registered_kind_carries_the_real_vk_hash() {
        // The verifier registers under, and reports, the genuine vk_hash — so the
        // executor's Custom{vk_hash} dispatch routes to it.
        let prog = red_keys().program();
        let verifier = FogVisionVerifier::for_program(&prog);
        assert_eq!(
            verifier.kind(),
            WitnessedPredicateKind::Custom {
                vk_hash: prog.vk_hash()
            }
        );
        // And the producer registers under the same hash (so produce/verify pair up).
        let producer = FogVisionProducer::new(red_keys());
        assert_eq!(producer.vk_hash(), prog.vk_hash());
    }
}
