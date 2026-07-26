//! THE MEMOISED PQ HALF — `AgentCipherclerk`'s ML-DSA-65 key is derived ONCE per identity and
//! reused, and the memo is bound to the seed that produced it.
//!
//! The derivation (`MlDsaTurnKey::from_ed25519_seed` → the Lean-verified `dregg_mldsa_keygen_real`
//! core) costs ~227 ms of CPU at the FFI boundary and every hybrid signature used to pay it afresh.
//! Caching it is a memoisation of a pure function — but a memo that ever served one identity's key
//! to another would be a FORGERY ENGINE, not a slow path. These tests are the wall.
//!
//! What is checked here, and why each one can go red:
//!   1. Four distinct identities, signing INTERLEAVED so a process-global or last-writer cache would
//!      hand one of them a neighbour's key: every PQ public key stays its own across rounds.
//!   2. Cross-verification is REFUSED — A's ML-DSA half must not verify under B's public key. This
//!      is the falsifier: it is what "two identities must never share a derived key" MEANS on the
//!      wire, and a shared cache makes it fail.
//!   3. The cached key is BIT-IDENTICAL to a fresh derivation — the memo changes latency, not what
//!      is signed or by which key.
//!   4. Same seed ⇒ same PQ key still holds. The identity is deterministic in the seed on purpose
//!      (a clerk's PQ key must match a node / genesis fixture built from the same mnemonic); a cache
//!      "fix" that randomised per-clerk would break that, so it is pinned too.
//!
//! Every test runs against the VERIFIED cores, installed explicitly and ASSERTED installed — an
//! unaudited-fallback run would prove nothing about the deployed keygen.

use dregg_sdk::{AgentCipherclerk, CellId};
use dregg_turn::action::{Action, Authorization, CommitmentMode, DelegationMode};
use dregg_turn::executor::TurnExecutor;
use zeroize::Zeroizing;

const FED: [u8; 32] = [0x5c; 32];

/// Install the verified Lean PQ cores for this test process and REFUSE to run vacuously.
///
/// `AgentCipherclerk` does not install them itself (that is `AgentRuntime`'s job), so without this
/// the keygen would take `dregg-pq`'s unaudited-fallback branch and the test would be measuring the
/// `fips204` crate instead of the deployed object.
fn install_verified_cores() {
    use dregg_pq::{
        MlDsaKeygenCoreRealInstall as K, MlDsaSignCoreRealInstall as S, MlDsaVerifyCoreInstall as V,
    };
    let keygen = dregg_sdk::install_verified_mldsa_keygen_core_real();
    assert!(
        matches!(keygen, K::Installed | K::AlreadyInstalled),
        "the verified ML-DSA KEYGEN core must be installed for this test to say anything about the \
         deployed derivation; got {keygen:?}"
    );
    let sign = dregg_sdk::install_verified_mldsa_sign_core_real();
    assert!(
        matches!(sign, S::Installed | S::AlreadyInstalled),
        "the verified ML-DSA SIGN core must be installed; got {sign:?}"
    );
    let verify = dregg_sdk::install_verified_mldsa_verify_core();
    assert!(
        matches!(verify, V::Installed | V::AlreadyInstalled),
        "the verified ML-DSA VERIFY core must be installed; got {verify:?}"
    );
}

fn empty_action(target: CellId, method: u8) -> Action {
    Action {
        target,
        method: [method; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    }
}

/// Sign `method` with `clerk` and return `(canonical message, ml_dsa signature, ml_dsa public key)`.
fn hybrid_parts(clerk: &AgentCipherclerk, method: u8) -> ([u8; 32], Vec<u8>, Vec<u8>) {
    let target = clerk.cell_id("default");
    let nonce = clerk.next_turn_nonce();
    let signed = clerk.sign_action(empty_action(target, method), &FED);
    let unsigned = Action {
        authorization: Authorization::Unchecked,
        ..signed.clone()
    };
    let message = TurnExecutor::compute_signing_message(&unsigned, &FED, nonce);
    match signed.authorization {
        Authorization::HybridSignature {
            ml_dsa, ml_dsa_pk, ..
        } => (message, ml_dsa, ml_dsa_pk),
        other => panic!("the default signing path must emit a HybridSignature, got {other:?}"),
    }
}

/// THE MANDATORY ONE. Four identities, signing interleaved: no clerk may ever present, or sign
/// under, another clerk's derived ML-DSA key.
#[test]
fn two_identities_never_share_a_derived_pq_key() {
    install_verified_cores();

    let seeds: [[u8; 32]; 4] = [[0x11; 32], [0x22; 32], [0x33; 32], [0xf0; 32]];
    let clerks: Vec<AgentCipherclerk> = seeds
        .iter()
        .map(|s| AgentCipherclerk::from_key_bytes(Zeroizing::new(*s)))
        .collect();

    // The truth each clerk must keep telling: the key its OWN seed derives, computed independently
    // of the clerk and of the cache.
    let expected: Vec<Vec<u8>> = seeds
        .iter()
        .map(|s| dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(s).public_bytes())
        .collect();
    for (i, a) in expected.iter().enumerate() {
        for (j, b) in expected.iter().enumerate() {
            if i != j {
                assert_ne!(
                    a, b,
                    "distinct seeds must derive distinct ML-DSA keys ({i} vs {j})"
                );
            }
        }
    }

    // INTERLEAVED. Round 0 fills every cache; rounds 1-2 read them. A process-global memo keyed by
    // anything but the seed, or a single-slot cache shared across clerks, mis-serves here.
    let mut per_clerk_sigs: Vec<Vec<([u8; 32], Vec<u8>, Vec<u8>)>> =
        (0..clerks.len()).map(|_| Vec::new()).collect();
    for round in 0..3u8 {
        for (i, clerk) in clerks.iter().enumerate() {
            let parts = hybrid_parts(clerk, round * 16 + i as u8);
            assert_eq!(
                parts.2, expected[i],
                "clerk {i} presented a PQ public key that is not the one its own seed derives \
                 (round {round}) — the cache leaked across identities"
            );
            assert_eq!(
                clerk.ml_dsa_public_bytes(),
                expected[i],
                "clerk {i}'s cached PQ public key drifted from its seed's derivation (round {round})"
            );
            per_clerk_sigs[i].push(parts);
        }
    }

    // THE FALSIFIER, on the wire: every clerk's PQ half verifies under its OWN key and under no
    // other clerk's. This is the property a shared cache would destroy.
    for (i, sigs) in per_clerk_sigs.iter().enumerate() {
        for (message, ml_dsa, ml_dsa_pk) in sigs {
            assert!(
                dregg_turn::pq::ml_dsa_verify(ml_dsa_pk, message, ml_dsa),
                "clerk {i}'s own PQ half must verify under its own carried key"
            );
            for (j, other) in expected.iter().enumerate() {
                if i != j {
                    assert!(
                        !dregg_turn::pq::ml_dsa_verify(other, message, ml_dsa),
                        "clerk {i}'s PQ signature verified under clerk {j}'s key — two identities \
                         are sharing a derived key"
                    );
                }
            }
        }
    }
}

/// The memo must not change WHAT is signed: a cached key produces the same public key and the same
/// deterministic signature bytes as a key derived fresh for the occasion.
#[test]
fn cached_key_is_bit_identical_to_a_fresh_derivation() {
    install_verified_cores();

    let seed = [0x9a; 32];
    let clerk = AgentCipherclerk::from_key_bytes(Zeroizing::new(seed));
    let fresh = dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(&seed);

    // First call: derives. Second: reads the memo. Both must equal the independent derivation.
    assert_eq!(clerk.ml_dsa_public_bytes(), fresh.public_bytes());
    assert_eq!(clerk.ml_dsa_public_bytes(), fresh.public_bytes());

    let (message, ml_dsa, ml_dsa_pk) = hybrid_parts(&clerk, 7);
    assert_eq!(ml_dsa_pk, fresh.public_bytes());
    assert_eq!(
        ml_dsa,
        fresh
            .sign(&message)
            .expect("the verified sign core must produce a signature"),
        "the cached key's signature must be byte-for-byte the fresh key's — the PQ half is \
         deterministic and is bound into the turn hash"
    );
}

/// Determinism in the seed is the POINT of this derivation (a clerk's PQ key must match a node or
/// genesis fixture built from the same mnemonic). Two clerks on the same seed therefore SHARE a key,
/// and that is correct — pinned so a future "fix" cannot make the cache per-instance random.
#[test]
fn same_seed_still_derives_the_same_pq_key() {
    install_verified_cores();

    let seed = [0x4d; 32];
    let a = AgentCipherclerk::from_key_bytes(Zeroizing::new(seed));
    let b = AgentCipherclerk::from_key_bytes(Zeroizing::new(seed));
    assert_eq!(
        a.ml_dsa_public_bytes(),
        b.ml_dsa_public_bytes(),
        "the same ed25519 seed must derive the same ML-DSA identity"
    );
    assert_eq!(a.public_key(), b.public_key());
}
