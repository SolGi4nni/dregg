// PORTED dregg-native from the prior operated layer (verbatim).

//! The **account identity** — the stable, key-derived id a web cap-account
//! is anchored to (the Tier-1 account-identity re-anchor).
//!
//! ## Why this exists
//!
//! Before the weld, an account's subject was `hash(credential tail)`
//! ([`crate::subject_of`]'s legacy path): the subject was a function of the
//! *credential*, so a new credential was a new account — no rotation, no
//! recovery, no revocation that preserved the account. The fix (per
//! the session-login design) is to anchor the account to a
//! **self-certifying, key-derived identity-cell id** and demote the `dga1_`
//! credential to a *session token* under it.
//!
//! ## The id IS the substrate identity-cell id
//!
//! We do not invent a derivation: the account id is
//! [`dregg_types::CellId::derive_raw`]`(&inception_pubkey, &`[`ACCOUNT_ROOT_TOKEN`]`)`
//! — the exact `blake3::derive_key("dregg-cell-id-v1", pubkey ‖ token)` the
//! breadstuffs executor uses to address a cell. So an account and the
//! rotatable substrate **identity cell** the control plane provisions for it
//! (KERI pre-rotation via `KeyRotationGate`, guardian recovery via the HINTS
//! `ThresholdSigVerifier`) are the *same principal* — byte-for-byte. This is the
//! depend-on-the-real-substrate weld: rotation/recovery happen on the identity
//! cell, and because the account subject IS that cell's id, the account (and all
//! the resources `org`/`dregg-secrets`/`console`/`guard`/`billing` scope to it)
//! survives every rotation.
//!
//! ## The INCEPTION key, not the current key (the KERI invariant)
//!
//! The id is derived from the account's **inception** public key — the first key
//! it was created with — and is then *fixed for life*. Key rotation changes the
//! *current* authoritative key (the one a session is minted under) but NEVER the
//! inception-derived id, exactly as a KERI AID is its inception id and continuity
//! is carried by the rotation chain (the KEL), not by re-deriving from the
//! current key. Deriving from the current key would change the id on every
//! rotation and defeat the entire purpose.

use dregg_types::CellId;

/// The first-party caveat key a re-anchored session credential stamps its stable
/// account id under. [`crate::subject_of`] reads it; its absence marks a legacy
/// (tail-subject) credential.
pub const ACCT_CAVEAT_KEY: &str = "acct";

/// The published domain label whose blake3 hash IS [`account_root_token`]. The
/// control plane MUST provision an account's identity cell under that same token
/// so the account id here and the cell id there agree.
pub const ACCOUNT_ROOT_TOKEN_LABEL: &str = "dregg:account-identity:v1";

/// The fixed 32-byte domain token that binds an account id to a substrate
/// identity cell: `blake3(`[`ACCOUNT_ROOT_TOKEN_LABEL`]`)`. Deterministic and
/// published (not a secret — it is a domain separator).
pub fn account_root_token() -> [u8; 32] {
    blake3::hash(ACCOUNT_ROOT_TOKEN_LABEL.as_bytes()).into()
}

/// The stable account id for an inception public key, as lowercase hex of the
/// 32-byte substrate identity-cell id. This is the value a session credential
/// carries in its [`ACCT_CAVEAT_KEY`] caveat; the subject is `dregg:<this>`.
pub fn account_id_hex(inception_pubkey: &[u8; 32]) -> String {
    let cell = CellId::derive_raw(inception_pubkey, &account_root_token());
    hex32(cell.as_bytes())
}

/// The full subject string for an inception key — `dregg:<account-id-hex>` —
/// matching what [`crate::subject_of`] returns for a re-anchored credential.
pub fn account_subject(inception_pubkey: &[u8; 32]) -> String {
    format!("dregg:{}", account_id_hex(inception_pubkey))
}

fn hex32(bytes: &[u8; 32]) -> String {
    const LUT: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(64);
    for &b in bytes {
        s.push(LUT[(b >> 4) as usize] as char);
        s.push(LUT[(b & 0x0f) as usize] as char);
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The token is exactly `blake3(label)` — deterministic and reproducible by
    /// the control plane from the published label alone.
    #[test]
    fn account_root_token_matches_blake3_of_label() {
        let live: [u8; 32] = blake3::hash(ACCOUNT_ROOT_TOKEN_LABEL.as_bytes()).into();
        assert_eq!(account_root_token(), live);
    }

    /// The account id IS the substrate identity-cell id: deriving here agrees,
    /// byte-for-byte, with `CellId::derive_raw` over the same inputs (the same
    /// function the executor addresses cells with).
    #[test]
    fn account_id_is_the_substrate_cell_id() {
        let pk = [0x42u8; 32];
        let cell = CellId::derive_raw(&pk, &account_root_token());
        assert_eq!(account_id_hex(&pk), hex32(cell.as_bytes()));
        assert_eq!(
            account_subject(&pk),
            format!("dregg:{}", hex32(cell.as_bytes()))
        );
    }

    /// Stability + key-derivation: the same inception key always yields the same
    /// account id; a different inception key yields a different one.
    #[test]
    fn account_id_is_stable_and_key_derived() {
        let a = [0x01u8; 32];
        let b = [0x02u8; 32];
        assert_eq!(account_id_hex(&a), account_id_hex(&a));
        assert_ne!(account_id_hex(&a), account_id_hex(&b));
        // 64 hex chars = the full 32-byte cell id (not the legacy 16-char tail).
        assert_eq!(account_id_hex(&a).len(), 64);
    }
}
