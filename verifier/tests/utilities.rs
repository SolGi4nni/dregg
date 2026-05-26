//! Relocated helper-level tests for dregg-verifier utility functions.
//!
//! These exercise `parse_public_inputs_json` and `resolve_vk_hash` — small
//! pure utilities that do not merit coverage inflation in the main verifier
//! feature-test count.

use dregg_verifier::{
    EFFECT_VM_AIR_NAME, EFFECT_VM_VK_HASH_HEX, parse_public_inputs_json, resolve_vk_hash,
};

#[test]
fn test_parse_public_inputs_json() {
    let pi = parse_public_inputs_json("[1, 2, 3, 4294967295]").unwrap();
    assert_eq!(pi, vec![1, 2, 3, 4294967295]);
}

#[test]
fn test_parse_public_inputs_json_rejects_float() {
    assert!(parse_public_inputs_json("[1.5]").is_err());
}

#[test]
fn test_resolve_vk_hash_auto() {
    // "auto" is not resolved by resolve_vk_hash — it's handled upstream.
    assert!(resolve_vk_hash("auto").is_none());
}

#[test]
fn test_resolve_vk_hash_known() {
    assert_eq!(
        resolve_vk_hash(EFFECT_VM_VK_HASH_HEX),
        Some(EFFECT_VM_AIR_NAME)
    );
}

#[test]
fn test_resolve_vk_hash_air_name_encoded() {
    let encoded = hex::encode(EFFECT_VM_AIR_NAME);
    assert_eq!(resolve_vk_hash(&encoded), Some(EFFECT_VM_AIR_NAME));
}
