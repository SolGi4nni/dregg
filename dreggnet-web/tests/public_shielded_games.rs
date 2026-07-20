//! Deployment-contract tooth: the aggregate feature must really propagate
//! every completed private dungeon operation into the shared catalog host.

#![cfg(feature = "public-shielded-games")]

use std::collections::BTreeSet;

use dreggnet_offerings::dungeon::{
    PRIVATE_PREFERENCE_OPERATION, PRIVATE_QUEST_OPERATION, PRIVATE_RAID_OPERATION,
    PRIVATE_SHUFFLE_COMMIT_OPERATION, PRIVATE_SHUFFLE_PROVE_OPERATION,
    PRIVATE_SHUFFLE_REVEAL_OPERATION,
};
use dreggnet_offerings::{SessionConfig, SessionId};
use dreggnet_web::{
    DARK_AMM_AUTHORITY_KEYS_ENV, DARK_AMM_AUTHORITY_THRESHOLD_ENV,
    DARK_AMM_COLLECTIVE_BASE_SESSION_ENV, DARK_AMM_COLLECTIVE_CRP_SEED_ENV,
    DARK_AMM_COLLECTIVE_MATERIAL_FILE_ENV, DARK_AMM_COLLECTIVE_PARTIES_ENV,
    DARK_AMM_COLLECTIVE_SESSION_ID_ENV, DARK_AMM_DECISION_KEYS_ENV,
    DARK_AMM_DECISION_THRESHOLD_ENV, DARK_AMM_INITIAL_ROOT_ENV, DARK_AMM_SECRET_KEY_FILE_ENV,
    FHEGG_QUORUM_KEYS_ENV, FHEGG_QUORUM_THRESHOLD_ENV, dark_amm_authority_from,
    dark_amm_decision_authority_from, validate_public_shielded_deployment_from,
};

#[test]
fn production_feature_bundle_exposes_every_shielded_dungeon_operation() {
    let mut host = dreggnet_web::demo_host();
    let session = SessionId::new("public-shielded-feature-contract");
    host.open_session(
        "dungeon",
        session.clone(),
        SessionConfig::with_seed(0x51_1E1D),
    )
    .expect("shared catalog dungeon opens");

    let operations = host
        .binary_operations("dungeon", &session)
        .expect("dungeon operations are discoverable");
    let names = operations
        .iter()
        .map(|operation| operation.name.as_str())
        .collect::<BTreeSet<_>>();
    assert_eq!(names.len(), operations.len(), "operation names are unique");
    for expected in [
        PRIVATE_RAID_OPERATION,
        PRIVATE_PREFERENCE_OPERATION,
        PRIVATE_SHUFFLE_COMMIT_OPERATION,
        PRIVATE_SHUFFLE_PROVE_OPERATION,
        PRIVATE_SHUFFLE_REVEAL_OPERATION,
        PRIVATE_QUEST_OPERATION,
    ] {
        assert!(
            names.contains(expected),
            "deployment bundle omitted {expected}"
        );
    }
    assert!(operations.iter().all(|operation| {
        !operation.input_media_type.is_empty()
            && operation.max_input_bytes > 0
            && !operation.disclosure.is_empty()
    }));
}

#[test]
fn dark_amm_exact_opening_policy_is_paired_and_strictly_parsed() {
    assert_eq!(dark_amm_authority_from(|_| None).unwrap(), None);
    for lone_name in [
        DARK_AMM_AUTHORITY_KEYS_ENV,
        DARK_AMM_AUTHORITY_THRESHOLD_ENV,
    ] {
        let error = dark_amm_authority_from(|name| {
            (name == lone_name).then(|| "configured-alone".to_string())
        })
        .expect_err("a one-sided exact-opening policy must be refused");
        assert!(error.contains("must be set together"), "{error}");
    }

    let key0 = "00".repeat(32);
    let key1 = "11".repeat(32);
    let policy = dark_amm_authority_from(|name| match name {
        DARK_AMM_AUTHORITY_KEYS_ENV => Some(format!("{key0},{key1}")),
        DARK_AMM_AUTHORITY_THRESHOLD_ENV => Some("2".to_string()),
        _ => None,
    })
    .unwrap()
    .expect("complete exact-opening authority policy parses");
    assert_eq!(policy.0, vec![[0; 32], [0x11; 32]]);
    assert_eq!(policy.1, 2);

    let decision = dark_amm_decision_authority_from(|name| match name {
        DARK_AMM_DECISION_KEYS_ENV => Some(format!("{key0},{key1}")),
        DARK_AMM_DECISION_THRESHOLD_ENV => Some("2".to_string()),
        _ => None,
    })
    .unwrap()
    .expect("independent FHDAR authority policy parses");
    assert_eq!(decision, policy);

    for (keys, threshold) in [
        ("not-hex".to_string(), "1".to_string()),
        (key0.clone(), "0".to_string()),
        (key0, "2".to_string()),
    ] {
        assert!(
            dark_amm_authority_from(|name| match name {
                DARK_AMM_AUTHORITY_KEYS_ENV => Some(keys.clone()),
                DARK_AMM_AUTHORITY_THRESHOLD_ENV => Some(threshold.clone()),
                _ => None,
            })
            .is_err()
        );
    }
}

#[test]
fn production_startup_refuses_half_configured_private_authorities() {
    validate_public_shielded_deployment_from(|_| None)
        .expect("an explicitly unconfigured operation is disabled, not forged");

    for lone_name in [
        FHEGG_QUORUM_KEYS_ENV,
        FHEGG_QUORUM_THRESHOLD_ENV,
        DARK_AMM_SECRET_KEY_FILE_ENV,
    ] {
        let error = validate_public_shielded_deployment_from(|name| {
            (name == lone_name).then(|| "configured-alone".to_string())
        })
        .expect_err("one-sided production configuration must refuse startup");
        assert!(error.contains("must be set together"), "{error}");
    }

    for lone_name in [
        DARK_AMM_INITIAL_ROOT_ENV,
        DARK_AMM_AUTHORITY_KEYS_ENV,
        DARK_AMM_AUTHORITY_THRESHOLD_ENV,
    ] {
        let error = validate_public_shielded_deployment_from(|name| {
            (name == lone_name).then(|| "configured-alone".to_string())
        })
        .expect_err("a policy pin without either custody mode must refuse startup");
        assert!(error.contains("without either"), "{error}");
    }

    for lone_collective_name in [
        DARK_AMM_COLLECTIVE_MATERIAL_FILE_ENV,
        DARK_AMM_COLLECTIVE_SESSION_ID_ENV,
        DARK_AMM_COLLECTIVE_BASE_SESSION_ENV,
        DARK_AMM_COLLECTIVE_PARTIES_ENV,
        DARK_AMM_COLLECTIVE_CRP_SEED_ENV,
        DARK_AMM_DECISION_KEYS_ENV,
        DARK_AMM_DECISION_THRESHOLD_ENV,
    ] {
        validate_public_shielded_deployment_from(|name| {
            (name == lone_collective_name).then(|| "configured-alone".to_string())
        })
        .expect_err("a partial collective public-host policy must refuse startup");
    }

    let error = validate_public_shielded_deployment_from(|name| match name {
        DARK_AMM_SECRET_KEY_FILE_ENV | DARK_AMM_COLLECTIVE_MATERIAL_FILE_ENV => {
            Some("configured".to_string())
        }
        _ => None,
    })
    .expect_err("single-key and collective custody cannot be enabled together");
    assert!(error.contains("mutually exclusive"), "{error}");
}
