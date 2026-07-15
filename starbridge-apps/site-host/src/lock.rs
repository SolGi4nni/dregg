//! Poison-recovering mutex access.
//!
//! The registry, the lease book, and the storage backends are all guarded by
//! `std::sync::Mutex`. A plain `.lock().expect("… poisoned")` turns ONE panic while
//! the lock is held into a permanent self-DoS: the mutex is poisoned and every later
//! publish AND serve panics forever, with no recovery and no isolation — a
//! single-point brick of the whole hosting plane.
//!
//! [`lock_recover`] recovers instead: on poison it takes the guard anyway (via
//! [`std::sync::PoisonError::into_inner`]). The protected data is a `BTreeMap` / a
//! counter / a lease book — a panic mid-mutation leaves it structurally valid (at
//! worst a single entry half-updated), so continuing to serve every OTHER site is the
//! right posture for a hosting service, not bricking.

use std::sync::{Mutex, MutexGuard};

/// Lock `m`, recovering from poison (a prior panic while held) rather than
/// propagating it. See the module docs for why a hosting plane must not brick on one
/// poisoned lock.
pub fn lock_recover<'a, T>(m: &'a Mutex<T>) -> MutexGuard<'a, T> {
    m.lock().unwrap_or_else(|poisoned| poisoned.into_inner())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    #[test]
    fn a_poisoned_lock_still_serves() {
        let m = Arc::new(Mutex::new(vec![1, 2, 3]));
        // Poison the mutex: panic while holding the guard.
        let m2 = Arc::clone(&m);
        let _ = std::thread::spawn(move || {
            let _g = m2.lock().unwrap();
            panic!("poison it");
        })
        .join();
        assert!(m.lock().is_err(), "the mutex is now poisoned");
        // Recovery still yields the (structurally intact) data.
        let g = lock_recover(&m);
        assert_eq!(&*g, &[1, 2, 3], "recovered the data despite poison");
    }
}
