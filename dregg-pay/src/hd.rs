//! SLIP-0010 ed25519 hardened derivation — the "B" (HD-deposit) address provider.
//!
//! # Approach (SLIP-0010, ed25519 curve)
//!
//! One secret [`Seed`] deterministically fans out into many Solana deposit
//! addresses, one per user. The derivation is [SLIP-0010] over the ed25519 curve,
//! the exact scheme Phantom / `solana-keygen` use for BIP-44 Solana keys:
//!
//! * **Master key** — `I = HMAC-SHA512(key = "ed25519 seed", data = seed)`; the
//!   left 32 bytes `I_L` are the master private key, the right 32 bytes `I_R` are
//!   the master chain code.
//! * **Child (hardened only)** — for a hardened index `i` (`i ≥ 2³¹`):
//!   `I = HMAC-SHA512(key = c_par, data = 0x00 ‖ k_par ‖ ser32(i))`; `I_L` is the
//!   child private key, `I_R` the child chain code.
//! * The 32-byte private key `I_L` is used **directly as the ed25519 seed** — its
//!   ed25519 public key IS the Solana address.
//!
//! Full BIP-44 path: `m / 44' / 501' / index'` (501 = Solana's SLIP-0044 coin
//! type). ed25519 SLIP-0010 has **no non-hardened derivation** — every level is
//! hardened.
//!
//! # Honesty: no watch-only trick on Solana
//!
//! On secp256k1 you can hand a watcher an *xpub* and let it derive receive
//! addresses without any private key (watch-only). ed25519 SLIP-0010 has no such
//! public child derivation: deriving a deposit address here REQUIRES the secret
//! seed. So the deposit-address provider holds custody material, and the watcher
//! side derives addresses from the same seed. This is named, not hidden — it is
//! why the "B" model is custodial.
//!
//! [SLIP-0010]: https://github.com/satoshilabs/slips/blob/master/slip-0010.md

use ed25519_dalek::SigningKey;
use hmac::{Hmac, Mac};
use sha2::Sha512;

use crate::config::{DepositAddress, PayConfig, Seed, UserId};

type HmacSha512 = Hmac<Sha512>;

/// BIP-44 purpose (`44'`).
const PURPOSE: u32 = 44;
/// SLIP-0044 coin type for Solana (`501'`).
const SOLANA_COIN_TYPE: u32 = 501;
/// The hardened offset (`2³¹`).
const HARDENED: u32 = 0x8000_0000;

/// A SLIP-0010 extended key: a 32-byte private key + a 32-byte chain code.
struct Extended {
    key: [u8; 32],
    chain_code: [u8; 32],
}

/// Master key: `HMAC-SHA512("ed25519 seed", seed)`.
fn master(seed: &[u8]) -> Extended {
    let mut mac = HmacSha512::new_from_slice(b"ed25519 seed").expect("hmac accepts any key length");
    mac.update(seed);
    split(mac.finalize().into_bytes().as_slice())
}

/// Hardened child derivation (the only kind ed25519 SLIP-0010 supports):
/// `HMAC-SHA512(c_par, 0x00 ‖ k_par ‖ ser32(i | 2³¹))`.
fn child_hardened(parent: &Extended, index: u32) -> Extended {
    let hardened = index | HARDENED;
    let mut mac =
        HmacSha512::new_from_slice(&parent.chain_code).expect("hmac accepts any key length");
    mac.update(&[0u8]);
    mac.update(&parent.key);
    mac.update(&hardened.to_be_bytes());
    split(mac.finalize().into_bytes().as_slice())
}

fn split(i: &[u8]) -> Extended {
    let mut key = [0u8; 32];
    key.copy_from_slice(&i[0..32]);
    let mut chain_code = [0u8; 32];
    chain_code.copy_from_slice(&i[32..64]);
    Extended { key, chain_code }
}

/// Derive the ed25519 [`SigningKey`] at `m / 44' / 501' / index'` from `seed`.
/// This is the CUSTODY key for a deposit address — only the sweeper needs it.
pub fn derive_signing_key(seed: &Seed, index: u32) -> SigningKey {
    let m = master(seed.as_bytes());
    let a = child_hardened(&m, PURPOSE);
    let b = child_hardened(&a, SOLANA_COIN_TYPE);
    let c = child_hardened(&b, index);
    SigningKey::from_bytes(&c.key)
}

/// Derive the Solana deposit address (ed25519 public key) at index `index`.
pub fn derive_deposit_address(seed: &Seed, index: u32) -> DepositAddress {
    let sk = derive_signing_key(seed, index);
    DepositAddress(sk.verifying_key().to_bytes())
}

/// Map a [`UserId`] to a stable 31-bit hardened derivation index.
///
/// `index = blake3("dregg-pay/hd-user-index/v1" ‖ user)[0..4] as u32 & 0x7fff_ffff`.
/// The same user always maps to the same index (hence the same address). The index
/// space is 2³¹; two distinct users colliding is a birthday event over 2³¹, which
/// for any realistic user count is negligible — but it is NOT zero. For a large
/// production deployment the operator should assign monotonic indices explicitly
/// via [`HdDeposit::at_index`] and persist the `user → index` map (the discord bot
/// does this in its sqlite store); the hash mapping is the zero-config default.
pub fn user_index(user: &UserId) -> u32 {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"dregg-pay/hd-user-index/v1");
    hasher.update(user.as_bytes());
    let digest = hasher.finalize();
    let bytes = digest.as_bytes();
    let raw = u32::from_be_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    raw & 0x7fff_ffff
}

/// The pluggable deposit-address provider. The "B" model is [`HdDeposit`]; a
/// future "C" model (a per-user PDA under an on-chain program) implements this same
/// trait and swaps in without touching the watcher / ledger / sweeper.
pub trait DepositAddressProvider {
    /// The deterministic deposit address for `user`. Same user ⇒ same address.
    fn deposit_address(&self, user: &UserId) -> DepositAddress;
}

/// The "B" HD-deposit provider: derives a deterministic per-user Solana deposit
/// address from the configured [`Seed`] via SLIP-0010 ed25519 hardened derivation.
///
/// Holds the seed (custody material). Clone-cheap (the seed is `Zeroizing<Vec>`,
/// wiped on the last drop).
#[derive(Clone)]
pub struct HdDeposit {
    seed: Seed,
}

impl HdDeposit {
    /// Build from a [`PayConfig`] (uses its seed).
    pub fn new(config: &PayConfig) -> Self {
        HdDeposit {
            seed: config.seed.clone(),
        }
    }

    /// Build directly from a seed.
    pub fn from_seed(seed: Seed) -> Self {
        HdDeposit { seed }
    }

    /// The deposit address at an EXPLICIT index — the production path when the
    /// operator assigns monotonic indices and persists the `user → index` map
    /// (collision-free by construction).
    pub fn at_index(&self, index: u32) -> DepositAddress {
        derive_deposit_address(&self.seed, index)
    }

    /// The custody signing key for `user`'s deposit address — used only by the
    /// sweeper. Requires the seed (there is no watch-only path on ed25519).
    pub fn signing_key(&self, user: &UserId) -> SigningKey {
        derive_signing_key(&self.seed, user_index(user))
    }

    /// The custody signing key at an explicit index.
    pub fn signing_key_at(&self, index: u32) -> SigningKey {
        derive_signing_key(&self.seed, index)
    }
}

impl DepositAddressProvider for HdDeposit {
    fn deposit_address(&self, user: &UserId) -> DepositAddress {
        derive_deposit_address(&self.seed, user_index(user))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::SPL_TOKEN_PROGRAM_ID;
    use ed25519_dalek::{Signer, Verifier};

    fn test_seed() -> Seed {
        // A THROWAWAY test seed. NEVER a real key.
        Seed::new(*b"dregg-pay throwaway test seed 000000000000000000000000000000")
    }

    #[test]
    fn spl_token_program_id_is_canonical() {
        assert_eq!(
            bs58::encode(SPL_TOKEN_PROGRAM_ID).into_string(),
            "TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA"
        );
    }

    #[test]
    fn derivation_is_deterministic_and_per_user_unique() {
        let hd = HdDeposit::from_seed(test_seed());
        let alice = UserId::from("alice");
        let bob = UserId::from("bob");
        // Same user ⇒ same address, every time.
        assert_eq!(hd.deposit_address(&alice), hd.deposit_address(&alice));
        // Different users ⇒ different addresses (correct attribution).
        assert_ne!(hd.deposit_address(&alice), hd.deposit_address(&bob));
    }

    #[test]
    fn different_seed_yields_different_address() {
        let a = HdDeposit::from_seed(test_seed());
        let b = HdDeposit::from_seed(Seed::new(
            *b"a completely different throwaway seed value...",
        ));
        let alice = UserId::from("alice");
        assert_ne!(a.deposit_address(&alice), b.deposit_address(&alice));
    }

    #[test]
    fn derived_key_signs_and_verifies() {
        // The sweeper's custody proof: the derived key is a real ed25519 keypair
        // whose public key matches the deposit address. No funds, no network.
        let hd = HdDeposit::from_seed(test_seed());
        let user = UserId::from("alice");
        let sk = hd.signing_key(&user);
        let addr = hd.deposit_address(&user);
        assert_eq!(sk.verifying_key().to_bytes(), addr.to_bytes());
        let msg = b"sweep alice deposit to treasury";
        let sig = sk.sign(msg);
        assert!(sk.verifying_key().verify(msg, &sig).is_ok());
    }
}
