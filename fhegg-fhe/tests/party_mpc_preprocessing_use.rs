#![cfg(any(target_os = "linux", target_os = "macos"))]

//! End-to-end FHTRI004 protected-row consumption custody.
//!
//! The certificate still names centralized trusted preprocessing. This test
//! covers the separate host property: once an exact signed row is reserved for
//! a PartyMPC execution, neither a concurrent copy nor a restart can use it a
//! second time.

use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::PathBuf;
use std::process::Command;
use std::thread;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use dregg_pq::{
    install_verified_mldsa_keygen_core_real, install_verified_mldsa_sign_core_real,
    install_verified_mldsa_verify_core, MlDsaKey, MlDsaKeygenCoreRealInstall,
    MlDsaSignCoreRealInstall, MlDsaVerifyCoreInstall,
};
use ed25519_dalek::SigningKey;
use fhegg_fhe::mpc_party::preprocessing_use::{
    run_party_equality_with_durable_preprocessing, PreprocessingUseError, PreprocessingUseLedger,
    PreprocessingUseState,
};
use fhegg_fhe::mpc_party::{
    certified_dealer_triples, local_channels, run_party, run_party_comparison, run_party_equality,
    PartyArithmeticInput, PartyComparisonInput, PartyEqualityInput, PartyMpcError, PartyMpcSession,
    TripleMaterial,
};
use rand::rngs::StdRng;
use rand::SeedableRng;

const N: usize = 3;
const MODULUS: u64 = 257;
const CHILD: &str = "FHEGG_PREPROCESSING_USE_VERIFIED_CHILD";

#[test]
fn exact_certified_rows_are_reserved_before_runtime_and_consumed_forever() {
    if std::env::var_os(CHILD).is_none() {
        let status = Command::new(std::env::current_exe().expect("current test binary"))
            .args([
                "--exact",
                "exact_certified_rows_are_reserved_before_runtime_and_consumed_forever",
                "--nocapture",
            ])
            .env(CHILD, "1")
            .env_remove("DREGG_ALLOW_UNAUDITED_PQ")
            .status()
            .expect("spawn verified FHTRI004 custody test child");
        assert!(status.success(), "verified FHTRI004 custody child failed");
        return;
    }

    assert!(std::env::var_os("DREGG_ALLOW_UNAUDITED_PQ").is_none());
    assert!(matches!(
        install_verified_mldsa_keygen_core_real(
            dregg_lean_ffi::mldsa_keygen_real_core_available,
            |wire| dregg_lean_ffi::shadow_mldsa_keygen_real(wire).ok(),
        ),
        MlDsaKeygenCoreRealInstall::Installed | MlDsaKeygenCoreRealInstall::AlreadyInstalled
    ));
    assert!(matches!(
        install_verified_mldsa_sign_core_real(
            dregg_lean_ffi::fips204_sign_real_core_available,
            |wire| dregg_lean_ffi::shadow_fips204_sign_real(wire).ok(),
        ),
        MlDsaSignCoreRealInstall::Installed | MlDsaSignCoreRealInstall::AlreadyInstalled
    ));
    assert!(matches!(
        install_verified_mldsa_verify_core(
            dregg_lean_ffi::fips204_verify_real_core_available,
            |wire| dregg_lean_ffi::shadow_fips204_verify_real(wire).ok(),
        ),
        MlDsaVerifyCoreInstall::Installed | MlDsaVerifyCoreInstall::AlreadyInstalled
    ));

    let base =
        PartyMpcSession::equality([0xd1; 32], N, 8, MODULUS, Duration::from_secs(2)).unwrap();
    let ed25519_authority = SigningKey::from_bytes(&[0xd2; 32]);
    let ml_dsa_authority = MlDsaKey::from_ed25519_seed(&ed25519_authority.to_bytes());
    let batch = certified_dealer_triples(
        &base,
        [0xd3; 64],
        &mut StdRng::seed_from_u64(0xd4d5),
        &ed25519_authority,
        &ml_dsa_authority,
    )
    .unwrap();
    let (session, certificate, materials) = batch.into_parts();
    session.require_certified_preprocessing().unwrap();
    let wires = materials
        .iter()
        .map(|material| material.to_wire_bytes().unwrap())
        .collect::<Vec<_>>();

    // All three public runners are deliberately the uncertified/test surface.
    // A certified row is refused before circuit/session checking or ingress;
    // only the opaque durable wrapper can mint the internal authorization.
    let equality_input =
        PartyEqualityInput::new(&session, 0, 1, 1, &mut StdRng::seed_from_u64(0xd5a0)).unwrap();
    let (_, mut equality_endpoints) = local_channels(&session);
    assert!(matches!(
        run_party_equality(
            equality_input,
            TripleMaterial::from_wire_bytes(&session, 0, &wires[0]).unwrap(),
            equality_endpoints.remove(0),
        ),
        Err(PartyMpcError::CertifiedPreprocessingRequiresDurableCustody)
    ));

    let crossing_session =
        PartyMpcSession::new([0xd7; 32], N, 1, 8, MODULUS, Duration::from_secs(2)).unwrap();
    let crossing_input = PartyArithmeticInput::new(
        &crossing_session,
        0,
        &[1],
        &[1],
        &mut StdRng::seed_from_u64(0xd5a1),
    )
    .unwrap();
    let (_, mut crossing_endpoints) = local_channels(&crossing_session);
    assert!(matches!(
        run_party(
            crossing_input,
            TripleMaterial::from_wire_bytes(&session, 0, &wires[0]).unwrap(),
            crossing_endpoints.remove(0),
        ),
        Err(PartyMpcError::CertifiedPreprocessingRequiresDurableCustody)
    ));

    let comparison_session =
        PartyMpcSession::less_than([0xd8; 32], N, 8, MODULUS, Duration::from_secs(2)).unwrap();
    let comparison_input = PartyComparisonInput::new(
        &comparison_session,
        0,
        1,
        1,
        &mut StdRng::seed_from_u64(0xd5a2),
    )
    .unwrap();
    let (_, mut comparison_endpoints) = local_channels(&comparison_session);
    assert!(matches!(
        run_party_comparison(
            comparison_input,
            TripleMaterial::from_wire_bytes(&session, 0, &wires[0]).unwrap(),
            comparison_endpoints.remove(0),
        ),
        Err(PartyMpcError::CertifiedPreprocessingRequiresDurableCustody)
    ));

    let roots = (0..N).map(|_| TestDir::new()).collect::<Vec<_>>();
    let ledgers = roots
        .iter()
        .map(|root| PreprocessingUseLedger::open(&root.path).unwrap())
        .collect::<Vec<_>>();
    let reserved = materials
        .into_iter()
        .zip(&ledgers)
        .map(|(material, ledger)| ledger.reserve(material).unwrap())
        .collect::<Vec<_>>();
    let keys = reserved
        .iter()
        .map(|reservation| reservation.key().clone())
        .collect::<Vec<_>>();
    for (party, (key, ledger)) in keys.iter().zip(&ledgers).enumerate() {
        assert_eq!(key.batch_digest(), certificate.digest());
        assert_eq!(key.row_commitment(), certificate.row_commitments()[party]);
        assert_eq!(key.party(), party as u64);
        assert_eq!(
            ledger.state(key).unwrap(),
            Some(PreprocessingUseState::Reserved)
        );

        // A byte-for-byte second custody copy cannot race the already-fsynced
        // reservation into the protocol.
        let replay = TripleMaterial::from_wire_bytes(&session, party, &wires[party]).unwrap();
        assert!(matches!(
            ledger.reserve(replay),
            Err(PreprocessingUseError::AlreadyReserved { .. })
        ));
    }

    // Equal modulo t: 20+30+27 = 10+11+56 = 77.
    let left = [20, 30, 27];
    let right = [10, 11, 56];
    let inputs = (0..N)
        .map(|party| {
            PartyEqualityInput::new(
                &session,
                party,
                left[party],
                right[party],
                &mut StdRng::seed_from_u64(0xd600 + party as u64),
            )
            .unwrap()
        })
        .collect::<Vec<_>>();
    let (coordinator, endpoints) = local_channels(&session);
    let parties = inputs
        .into_iter()
        .zip(reserved)
        .zip(endpoints)
        .map(|((input, reserved), endpoint)| {
            thread::spawn(move || {
                run_party_equality_with_durable_preprocessing(input, reserved, endpoint)
            })
        })
        .collect::<Vec<_>>();
    assert!(coordinator
        .coordinate_equality(&session)
        .unwrap()
        .is_equal());
    for party in parties {
        assert_eq!(
            party.join().unwrap().unwrap().and_gates,
            session.exact_and_gates()
        );
    }

    for (party, (key, root)) in keys.iter().zip(&roots).enumerate() {
        let restarted = PreprocessingUseLedger::open(&root.path).unwrap();
        assert_eq!(
            restarted.state(key).unwrap(),
            Some(PreprocessingUseState::Consumed)
        );
        let replay = TripleMaterial::from_wire_bytes(&session, party, &wires[party]).unwrap();
        assert!(matches!(
            restarted.reserve(replay),
            Err(PreprocessingUseError::AlreadyConsumed { .. })
        ));
    }
}

struct TestDir {
    path: PathBuf,
}

impl TestDir {
    fn new() -> Self {
        // Process-global counter: a nanosecond nonce alone collides under parallel `cargo test` (same pid,
        // coarse clock) and `create_dir(...).unwrap()` panics AlreadyExists → flaky. The seq guarantees uniqueness.
        static SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let seq = SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "fhegg-fhtri004-use-{}-{seq}-{nonce}",
            std::process::id()
        ));
        fs::create_dir(&path).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
        Self { path }
    }
}

impl Drop for TestDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}
