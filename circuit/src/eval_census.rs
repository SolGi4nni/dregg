//! **Feature-gated invocation census for the descriptor interpreters** (`eval-count`).
//!
//! `Ir2Air::eval` / `Ir2UniAir::eval` are the interpreted constraint walk: every invocation
//! re-walks the descriptor's boxed expression trees against whatever `AirBuilder` p3 hands it —
//! once per SIMD pack-chunk of each instance's quotient domain on the prover's folder, once per
//! symbolic pass, once at zeta on the verifier's folder. Operation counts (permutations,
//! field ops) are IDENTICAL whether that walk is interpreted or compiled, so the existing count
//! instruments are blind to it by construction; this census exists to make the *invocation
//! geometry* itself a measured number rather than a derivation nobody checked.
//!
//! Off by default and compiled out entirely: the deployed prover carries no instrumentation
//! (the clock-arm discipline of `tests/hbox_rig.rs` — the uninstrumented config must stay
//! uninstrumented). Enable with `--features eval-count`; the recorder is a mutex over a
//! `BTreeMap`, bumped once per `Air::eval` INVOCATION (never per node), so a counting run is
//! still cheap — but it is a COUNT-arm instrument and its wall clock is not a result.

use std::collections::BTreeMap;
use std::sync::Mutex;

/// `(instance label, builder type name) → Air::eval invocation count`.
static CENSUS: Mutex<BTreeMap<(String, &'static str), u64>> = Mutex::new(BTreeMap::new());

/// Record one `Air::eval` invocation of `instance` under builder type `AB`.
pub fn record<AB>(instance: &str) {
    let key = (instance.to_string(), core::any::type_name::<AB>());
    *CENSUS.lock().unwrap().entry(key).or_insert(0) += 1;
}

/// Drain the census: every `(instance, builder-type)` pair with its invocation count,
/// sorted by key. Clears the counters.
pub fn take() -> Vec<((String, &'static str), u64)> {
    let mut m = CENSUS.lock().unwrap();
    let out = std::mem::take(&mut *m);
    out.into_iter().collect()
}
