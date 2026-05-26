//! Federation identity derivation.
//!
//! Closes finding F1 in `AUDIT-federation.md`: `federation_id` is no longer
//! random bytes from genesis but a **commitment to the committee** — the
//! domain-separated BLAKE3 hash over the sorted Ed25519 committee public keys
//! (and, optionally, the committee epoch).
//!
//! Two distinct federations with the same committee produce the same id;
//! one committee that re-keys produces a different id. This binding is what
//! lets `FederationReceipt::verify` reject receipts where the carried
//! `federation_id` does not match the committee handed to the verifier.

use crate::types::PublicKey;

/// Domain separator for the committee → federation_id mapping.
///
/// Bumping this string breaks every existing federation id — greenfield-only.
pub const FEDERATION_ID_DOMAIN: &str = "dregg-fed-id-v1";

/// Derive a federation id from the (unsorted) committee Ed25519 public keys.
///
/// The keys are sorted lexicographically so that the result is independent of
/// the genesis writer's iteration order. Equivalent to
/// [`derive_federation_id_with_epoch`] called with `epoch = 0` — committees
/// that ignore epoch rotation can use this form.
pub fn derive_federation_id(committee_pubkeys: &[PublicKey]) -> [u8; 32] {
    derive_federation_id_with_epoch(committee_pubkeys, 0)
}

/// Derive a federation id from committee Ed25519 pubkeys + a committee epoch.
///
/// Rotating any single member's key, adding or removing a member, or rotating
/// the epoch all change the result — this is how cross-federation receipt
/// swap is detected (a receipt's `federation_id` won't match the verifier's
/// recomputed id from its registered committee + epoch).
///
/// The keys are sorted lexicographically before hashing so that the
/// derivation is independent of input order. Duplicate keys (a malformed
/// committee) are NOT deduplicated — the genesis writer is responsible for
/// providing a well-formed committee; we hash what we're given so adversarial
/// duplication produces a distinguishable id rather than silently collapsing.
pub fn derive_federation_id_with_epoch(
    committee_pubkeys: &[PublicKey],
    committee_epoch: u64,
) -> [u8; 32] {
    let mut sorted: Vec<&PublicKey> = committee_pubkeys.iter().collect();
    sorted.sort_by(|a, b| a.0.cmp(&b.0));

    let mut hasher = blake3::Hasher::new_derive_key(FEDERATION_ID_DOMAIN);
    hasher.update(&(sorted.len() as u64).to_le_bytes());
    for pk in &sorted {
        hasher.update(&pk.0);
    }
    hasher.update(&committee_epoch.to_le_bytes());
    *hasher.finalize().as_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::generate_keypair;

    #[test]
    fn deterministic_and_order_independent() {
        let (_, a) = generate_keypair();
        let (_, b) = generate_keypair();
        let (_, c) = generate_keypair();

        let id1 = derive_federation_id(&[a.clone(), b.clone(), c.clone()]);
        let id2 = derive_federation_id(&[c.clone(), a.clone(), b.clone()]);
        assert_eq!(id1, id2, "federation_id must be independent of input order");
        assert_ne!(id1, [0u8; 32]);
    }

    #[test]
    fn membership_change_changes_id() {
        let (_, a) = generate_keypair();
        let (_, b) = generate_keypair();
        let (_, c) = generate_keypair();

        let id_ab = derive_federation_id(&[a.clone(), b.clone()]);
        let id_abc = derive_federation_id(&[a.clone(), b.clone(), c.clone()]);
        assert_ne!(id_ab, id_abc);
    }

    #[test]
    fn rekey_changes_id() {
        let (_, a) = generate_keypair();
        let (_, b) = generate_keypair();
        let (_, b_prime) = generate_keypair();

        let id_ab = derive_federation_id(&[a.clone(), b.clone()]);
        let id_abp = derive_federation_id(&[a.clone(), b_prime.clone()]);
        assert_ne!(id_ab, id_abp, "rekeying a member must change federation_id");
    }

    #[test]
    fn epoch_rotation_changes_id() {
        let (_, a) = generate_keypair();
        let (_, b) = generate_keypair();
        let committee = vec![a, b];
        let id0 = derive_federation_id_with_epoch(&committee, 0);
        let id1 = derive_federation_id_with_epoch(&committee, 1);
        let id7 = derive_federation_id_with_epoch(&committee, 7);
        assert_ne!(id0, id1);
        assert_ne!(id1, id7);
    }

    #[test]
    fn default_epoch_matches_explicit_zero() {
        let (_, a) = generate_keypair();
        let (_, b) = generate_keypair();
        let committee = vec![a, b];
        assert_eq!(
            derive_federation_id(&committee),
            derive_federation_id_with_epoch(&committee, 0),
        );
    }

    #[test]
    fn duplicate_member_distinguishable_from_singleton() {
        // Malformed committee with a duplicated member must not silently
        // collapse to a singleton id — we hash what we're given.
        let (_, a) = generate_keypair();
        let single = derive_federation_id(&[a.clone()]);
        let dup = derive_federation_id(&[a.clone(), a.clone()]);
        assert_ne!(single, dup);
    }
}
