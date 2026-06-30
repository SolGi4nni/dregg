//! # GENTIAN TEETH — the v10 perms/vk faithful 8-felt weld bites a 1-felt collision.
//!
//! The pre-v10 commitment carried ONLY `permsHash[0]` / `vkHash[0]` (limb 0, ~31 bits) of the
//! authority digest in a dedicated rotated limb (`B_PERMS = 33` / `B_VK = 34`). A malicious prover
//! could forge a post-permissions / post-VK that COLLIDES the honest one at limb 0 yet declares a
//! wholly different authority — a ledgerless light client could not tell. The v10 weld lands the
//! SEVEN completion felts (`permsHash[1..7]` at extras 37..=43, `vkHash[1..7]` at 44..=50) and the
//! 8-wide `permsVKWeldGate` (Lean `Dregg2.Circuit.Emit.EffectVmEmitRotationV3.withPermsVK8Weld_forces`
//! / `setPermsV3_forces8_extras` / `setVKV3_forces8_extras`) FORCES every one of the 8 committed
//! limbs to its declared param. So a forge that matches limb 0 but differs in ANY completion felt is
//! UNSAT in-circuit.
//!
//! These teeth EXHIBIT the gap the 1-felt missed: a deterministic birthday search produces two
//! Permissions / VerificationKey states that COLLIDE at the 1-felt digest (`[0]`) but DIFFER as full
//! 8-felt digests. The pre-v10 1-limb commitment accepts both as identical; the v10 8-felt digest
//! distinguishes them, and (per the Lean force-lemmas) the welded descriptor rejects the forge.

use dregg_cell::cell::VerificationKey;
use dregg_cell::commitment::{perms_digest_8, vk_digest_8};
use dregg_cell::permissions::{AuthRequired, Permissions};
use std::collections::HashMap;

/// A Permissions state whose `send` field is a deterministic `Custom { vk_hash }` derived from the
/// 64-bit counter `salt` (the rest is the default authority shape). Distinct salts give distinct
/// postcard serializations, hence distinct `perms_digest_8`.
fn perms_with_salt(salt: u64) -> Permissions {
    let mut vk_hash = [0u8; 32];
    vk_hash[0..8].copy_from_slice(&salt.to_le_bytes());
    Permissions {
        send: AuthRequired::Custom { vk_hash },
        ..Permissions::default()
    }
}

/// A VerificationKey whose `data` is the 8-byte LE encoding of `salt`.
fn vk_with_salt(salt: u64) -> Option<VerificationKey> {
    Some(VerificationKey::new(salt.to_le_bytes().to_vec()))
}

/// The deterministic birthday search bound. The 1-felt digest is one BabyBear limb (~31 bits), so a
/// collision is expected within ~2^15.5 (~46k) samples; the counter is deterministic so the first
/// collision is reproducible. 4M is a generous, non-flaky ceiling.
const SEARCH_BOUND: u64 = 4_000_000;

#[test]
fn perms_digest_8_distinguishes_a_1felt_collision() {
    // index salt by the 1-felt digest (`[0]`); the first counter that re-hits a stored `[0]` is the
    // colliding pair.
    let mut seen: HashMap<u32, u64> = HashMap::new();
    let mut pair: Option<(u64, u64)> = None;
    for salt in 0..SEARCH_BOUND {
        let d0 = perms_digest_8(&perms_with_salt(salt))[0].as_u32();
        if let Some(&prev) = seen.get(&d0) {
            pair = Some((prev, salt));
            break;
        }
        seen.insert(d0, salt);
    }
    let (a, b) = pair.expect("birthday search must collide perms_digest_8[0] within the bound");

    let da = perms_digest_8(&perms_with_salt(a));
    let db = perms_digest_8(&perms_with_salt(b));

    // The 1-felt (limb 0) collides — exactly the forge the pre-v10 commitment could not catch.
    assert_eq!(
        da[0], db[0],
        "the search produced a genuine 1-felt collision"
    );
    // ...but the states are genuinely different Permissions.
    assert_ne!(
        perms_with_salt(a),
        perms_with_salt(b),
        "the colliding salts are distinct Permissions states"
    );
    // THE TOOTH: the faithful 8-felt digest DISTINGUISHES them (they differ in at least one of the 7
    // completion felts [1..8]). A forge committing `da` while declaring `db` therefore diverges in a
    // WELDED limb, so the 8-wide `permsVKWeldGate` is UNSAT (Lean `setPermsV3_forces8_extras`).
    assert_ne!(
        da, db,
        "v10: the faithful 8-felt perms digest catches the 1-felt forge"
    );
    let differ_in_completion = (1..8).any(|i| da[i] != db[i]);
    assert!(
        differ_in_completion,
        "the divergence is in the completion felts [1..8] (the v10-welded limbs 37..=43)"
    );
}

#[test]
fn vk_digest_8_distinguishes_a_1felt_collision() {
    let mut seen: HashMap<u32, u64> = HashMap::new();
    let mut pair: Option<(u64, u64)> = None;
    for salt in 0..SEARCH_BOUND {
        let d0 = vk_digest_8(&vk_with_salt(salt))[0].as_u32();
        if let Some(&prev) = seen.get(&d0) {
            pair = Some((prev, salt));
            break;
        }
        seen.insert(d0, salt);
    }
    let (a, b) = pair.expect("birthday search must collide vk_digest_8[0] within the bound");

    let da = vk_digest_8(&vk_with_salt(a));
    let db = vk_digest_8(&vk_with_salt(b));

    assert_eq!(
        da[0], db[0],
        "the search produced a genuine 1-felt collision"
    );
    assert_ne!(
        vk_with_salt(a),
        vk_with_salt(b),
        "the colliding salts are distinct verification keys"
    );
    // THE TOOTH: the faithful 8-felt vk digest distinguishes the forge the 1-felt missed (the v10
    // weld forces limbs 44..=50 to the declared param — Lean `setVKV3_forces8_extras`).
    assert_ne!(
        da, db,
        "v10: the faithful 8-felt vk digest catches the 1-felt forge"
    );
    let differ_in_completion = (1..8).any(|i| da[i] != db[i]);
    assert!(
        differ_in_completion,
        "the divergence is in the completion felts [1..8] (the v10-welded limbs 44..=50)"
    );
}
