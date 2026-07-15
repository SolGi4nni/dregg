//! Small shared primitives the gateway is built on: **poison-safe locking** and
//! **unguessable token minting**.
//!
//! ## Poison-safe locking
//!
//! Every store in the gateway is behind a [`std::sync::Mutex`]. The retired code did
//! `.lock().expect("poisoned")` on every access — so a single panic *while a lock was
//! held* would poison the mutex and permanently brick that store for every subsequent
//! request (a self-inflicted denial of service). [`lock`] recovers the guard from a
//! poisoned mutex ([`std::sync::PoisonError::into_inner`]) instead: a transient panic
//! degrades one request, it does not take the store down. No `parking_lot`; the std
//! recovery path is sufficient and dependency-free.
//!
//! ## Unguessable tokens
//!
//! Machine ids (and idempotency / request ids) are minted from OS randomness
//! ([`getrandom`]) as fixed-width lowercase hex, NOT a sequential `AtomicU64` counter.
//! A 128-bit id is not enumerable or guessable, so cross-tenant enumeration is not a
//! fallback attack even before ownership is checked (defence in depth alongside the
//! per-record owner enforcement in [`crate::machines`]).

use std::sync::{Mutex, MutexGuard};

/// Acquire `mutex`, recovering the guard even if the mutex was poisoned by a panic in
/// a prior critical section. A poisoned store is degraded, never bricked.
pub fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

/// `n` bytes of OS randomness. Panics only if the OS RNG is unavailable, which on a
/// hosting node is a fatal-environment condition, not a runtime error to paper over.
pub fn random_bytes<const N: usize>() -> [u8; N] {
    let mut buf = [0u8; N];
    getrandom::fill(&mut buf).expect("operating-system randomness is available");
    buf
}

/// Lowercase hex of `bytes`.
pub fn hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        use std::fmt::Write as _;
        let _ = write!(s, "{b:02x}");
    }
    s
}

/// An unguessable id with `prefix`: `<prefix>` + 128 bits of OS randomness as 32 hex
/// chars (e.g. `mch_9f3a...`). Not a sequential counter — not enumerable.
pub fn mint_token(prefix: &str) -> String {
    format!("{prefix}{}", hex(&random_bytes::<16>()))
}

/// A 64-bit request/correlation id as 16 hex chars — enough entropy to correlate a
/// request across a log line without being a global sequence a caller can predict.
pub fn request_id() -> String {
    hex(&random_bytes::<8>())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    #[test]
    fn lock_recovers_a_poisoned_mutex() {
        let m = Arc::new(Mutex::new(0u32));
        let m2 = Arc::clone(&m);
        // Poison the mutex: panic while the guard is held.
        let _ = std::thread::spawn(move || {
            let _g = m2.lock().unwrap();
            panic!("poison it");
        })
        .join();
        assert!(m.lock().is_err(), "the std mutex is now poisoned");
        // The poison-safe lock still hands back a usable guard.
        *lock(&m) += 1;
        assert_eq!(*lock(&m), 1);
    }

    #[test]
    fn minted_ids_are_unique_and_wide() {
        let a = mint_token("mch_");
        let b = mint_token("mch_");
        assert_ne!(a, b, "two mints collide with negligible probability");
        assert!(a.starts_with("mch_"));
        assert_eq!(a.len(), "mch_".len() + 32, "128 bits = 32 hex chars");
        // Not a low, guessable counter value.
        assert_ne!(a, "mch_0000000000000000000000000000000000");
    }

    #[test]
    fn request_ids_are_16_hex() {
        let id = request_id();
        assert_eq!(id.len(), 16);
        assert!(id.chars().all(|c| c.is_ascii_hexdigit()));
    }
}
