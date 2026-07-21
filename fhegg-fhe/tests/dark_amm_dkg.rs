use std::time::Duration;

use ed25519_dalek::SigningKey;
use fhe_traits::Serialize as FheSerialize;
use fhegg_fhe::attestation::AuthenticatedQuorumVerifier;
use fhegg_fhe::dark_amm::{DarkPool, DarkPoolPublicHostMaterial};
use fhegg_fhe::dark_amm_dkg::{
    verify_collective_dkg_binding, CollectiveDkgBindingError, CollectivePartyContributionArtifact,
};
use fhegg_fhe::threshold::relin::{generate_relinearization_key, RelinKeySession};
use fhegg_fhe::threshold::{
    BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, PublicKeyContribution,
    ThresholdParty,
};
use rand_09::rngs::StdRng;
use rand_09::SeedableRng;

const N: usize = 3;
const VALUE_BITS: u64 = 19;

struct Fixture {
    params: BfvParams,
    keygen: KeygenSession,
    contributions: Vec<PublicKeyContribution>,
    collective: CollectivePublicKey,
    signers: Vec<SigningKey>,
    verifier: AuthenticatedQuorumVerifier,
    config: Vec<u8>,
    material: DarkPoolPublicHostMaterial,
}

impl Fixture {
    fn new() -> Self {
        let params = BfvParams::fold_set();
        let keygen = KeygenSession::from_seed(N, [0x31; 32]).unwrap();
        let mut parties = Vec::new();
        let mut contributions = Vec::new();
        for party in 0..N {
            let (state, contribution) =
                ThresholdParty::join_seeded(&keygen, party, &params, &[0x50 + party as u8; 32])
                    .unwrap();
            parties.push(state);
            contributions.push(contribution);
        }
        let mut coordinator = KeygenCoordinator::new(keygen.clone(), params.clone());
        for contribution in contributions.iter().cloned() {
            coordinator.accept(contribution).unwrap();
        }
        let collective = coordinator.finish().unwrap();
        let relin_session = RelinKeySession::from_public_entropy(
            &keygen,
            &collective,
            [0x72; 32],
            Duration::from_secs(10),
        )
        .unwrap();
        let relin =
            generate_relinearization_key(&relin_session, &params, &collective, &parties).unwrap();
        let mut rng = StdRng::from_seed([0x91; 32]);
        let material = DarkPool::init(
            params.arc(),
            &collective.pk,
            &relin,
            100,
            900,
            400,
            1_000,
            &mut rng,
        )
        .unwrap()
        .public_host_material()
        .unwrap();
        let signers = (0..N)
            .map(|party| SigningKey::from_bytes(&[0xa0 + party as u8; 32]))
            .collect::<Vec<_>>();
        let verifier = AuthenticatedQuorumVerifier::new(
            signers
                .iter()
                .map(|signer| signer.verifying_key().to_bytes())
                .collect(),
            2,
        )
        .unwrap();
        let config = worker_config_wire(&keygen, &verifier, 5_000);
        Self {
            params,
            keygen,
            contributions,
            collective,
            signers,
            verifier,
            config,
            material,
        }
    }

    fn artifacts(&self) -> Vec<Vec<u8>> {
        self.contributions
            .iter()
            .cloned()
            .zip(&self.signers)
            .map(|(contribution, signer)| {
                CollectivePartyContributionArtifact::issue(
                    &self.config,
                    &self.keygen,
                    &self.verifier,
                    contribution,
                    signer,
                )
                .unwrap()
                .to_wire_bytes()
            })
            .collect()
    }
}

#[test]
fn authenticated_dkg_artifacts_are_the_non_circular_collective_table_gate() {
    let fixture = Fixture::new();
    let artifacts = fixture.artifacts();
    let refs = artifacts.iter().map(Vec::as_slice).collect::<Vec<_>>();
    let verified = verify_collective_dkg_binding(
        &fixture.config,
        &fixture.keygen,
        &fixture.params,
        &fixture.verifier,
        &fixture.material,
        &refs,
    )
    .expect("the authenticated contribution roster reproduces the table key");
    assert_eq!(
        verified.collective().pk.to_bytes(),
        fixture.collective.pk.to_bytes()
    );
    assert_ne!(verified.transcript_digest(), [0; 32]);
}

#[test]
fn dkg_table_gate_refuses_order_signature_config_and_aggregate_substitution() {
    let fixture = Fixture::new();
    let artifacts = fixture.artifacts();

    let missing = artifacts[..2].iter().map(Vec::as_slice).collect::<Vec<_>>();
    assert!(matches!(
        verify_collective_dkg_binding(
            &fixture.config,
            &fixture.keygen,
            &fixture.params,
            &fixture.verifier,
            &fixture.material,
            &missing,
        ),
        Err(CollectiveDkgBindingError::ArtifactCount { have: 2, need: 3 })
    ));

    let shuffled = [
        artifacts[1].as_slice(),
        artifacts[0].as_slice(),
        artifacts[2].as_slice(),
    ];
    assert!(matches!(
        verify_collective_dkg_binding(
            &fixture.config,
            &fixture.keygen,
            &fixture.params,
            &fixture.verifier,
            &fixture.material,
            &shuffled,
        ),
        Err(CollectiveDkgBindingError::NonCanonicalPartyOrder {
            expected: 0,
            found: 1
        })
    ));

    let refs = artifacts.iter().map(Vec::as_slice).collect::<Vec<_>>();
    let alternate_config = worker_config_wire(&fixture.keygen, &fixture.verifier, 6_000);
    assert!(matches!(
        verify_collective_dkg_binding(
            &alternate_config,
            &fixture.keygen,
            &fixture.params,
            &fixture.verifier,
            &fixture.material,
            &refs,
        ),
        Err(CollectiveDkgBindingError::ConfigMismatch)
    ));

    // Preserve the public checksum after changing a signature byte: the
    // Ed25519 tooth, rather than the corruption checksum, must reject it.
    let mut forged_signature = artifacts.clone();
    let signature_start = forged_signature[1].len() - 32 - 64;
    forged_signature[1][signature_start] ^= 1;
    let checksum_start = forged_signature[1].len() - 32;
    let checksum = worker_checksum(&forged_signature[1][..checksum_start]);
    forged_signature[1][checksum_start..].copy_from_slice(&checksum);
    let forged_refs = forged_signature
        .iter()
        .map(Vec::as_slice)
        .collect::<Vec<_>>();
    assert!(matches!(
        verify_collective_dkg_binding(
            &fixture.config,
            &fixture.keygen,
            &fixture.params,
            &fixture.verifier,
            &fixture.material,
            &forged_refs,
        ),
        Err(CollectiveDkgBindingError::InvalidSignature { party: 1 })
    ));

    // A fully signed but different party-1 contribution is still not allowed
    // to nominate a different key for the already committed table material.
    let (_rogue_party, rogue_contribution) =
        ThresholdParty::join_seeded(&fixture.keygen, 1, &fixture.params, &[0xee; 32]).unwrap();
    let rogue_artifact = CollectivePartyContributionArtifact::issue(
        &fixture.config,
        &fixture.keygen,
        &fixture.verifier,
        rogue_contribution,
        &fixture.signers[1],
    )
    .unwrap()
    .to_wire_bytes();
    let substituted = [
        artifacts[0].as_slice(),
        rogue_artifact.as_slice(),
        artifacts[2].as_slice(),
    ];
    assert!(matches!(
        verify_collective_dkg_binding(
            &fixture.config,
            &fixture.keygen,
            &fixture.params,
            &fixture.verifier,
            &fixture.material,
            &substituted,
        ),
        Err(CollectiveDkgBindingError::CollectiveKeyMismatch)
    ));
}

fn worker_config_wire(
    keygen: &KeygenSession,
    verifier: &AuthenticatedQuorumVerifier,
    timeout_millis: u64,
) -> Vec<u8> {
    let mut wire = Vec::new();
    wire.extend_from_slice(b"DBWCv001");
    put_usize(&mut wire, keygen.n_parties());
    wire.extend_from_slice(&keygen.crp_seed());
    wire.extend_from_slice(&VALUE_BITS.to_le_bytes());
    wire.extend_from_slice(&timeout_millis.to_le_bytes());
    put_usize(&mut wire, verifier.threshold());
    put_usize(&mut wire, verifier.ordered_public_keys().len());
    for key in verifier.ordered_public_keys() {
        wire.extend_from_slice(key);
    }
    wire.extend_from_slice(&worker_checksum(&wire));
    wire
}

fn put_usize(out: &mut Vec<u8>, value: usize) {
    out.extend_from_slice(
        &u64::try_from(value)
            .expect("bounded fixture integer fits the canonical u64 wire")
            .to_le_bytes(),
    );
}

fn worker_checksum(content: &[u8]) -> [u8; 32] {
    let mut hash =
        blake3::Hasher::new_derive_key("dregg-dark-amm-collective-worker-input-checksum-v1");
    hash.update(
        &u64::try_from(content.len())
            .expect("bounded fixture artifact length fits the canonical u64 checksum")
            .to_le_bytes(),
    );
    hash.update(content);
    *hash.finalize().as_bytes()
}
