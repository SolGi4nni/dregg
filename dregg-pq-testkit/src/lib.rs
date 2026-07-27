//! `dregg-pq-testkit` — install the Lean-verified post-quantum cores in a TEST process.
//!
//! # What this is for
//!
//! `dregg-pq` is a light leaf: it never links the Lean archive, and it answers a PQ
//! operation only through a function pointer some host installed. With no core installed
//! and no declared bypass it does the only correct thing — `process::abort()`
//! (`dregg-pq/src/audit.rs`). That is right in production and it is right in a test.
//!
//! The consequence is that a test binary in a crate which cannot link the archive
//! (`dregg-blocklace`, `dregg-token`, `dregg-turn`, `dregg-cell-crypto`,
//! `dregg-lightclient`, `dregg-auth` — all deliberately light) dies as a bare SIGABRT
//! the first time it derives, signs with, or verifies an ML-DSA key. Whether it died was
//! decided by test ORDER, i.e. by `--test-threads`: at 1 thread an earlier test that
//! happened to construct a heavier object could install the cores and carry the rest.
//!
//! This crate is the ONE place a test process gets those cores. A crate adds it to
//! `[dev-dependencies]` and calls [`install`] before its first PQ operation.
//!
//! # This does not weaken the gate, and it is not a bypass
//!
//! `DREGG_ALLOW_UNAUDITED_PQ` does not appear in this crate and must not. That variable
//! routes the operation onto the unaudited `fips204` / `ml-kem` crates, which is the exact
//! substitution the gate exists to prevent. What [`install`] does is the opposite: it makes
//! the extracted, Lean-verified cores the authority in the test process, so the tests run
//! against the SAME objects a deployed node runs against instead of against a third-party
//! crate.
//!
//! Every install is EXPORT-GATED (`*_core_available()` is checked inside `dregg-pq`'s
//! shared install functions). An archive that does not export a core installs nothing for
//! that direction and the refusal at the point of use still stands — so a stale or
//! marshal-only archive still fails the test loudly rather than quietly downgrading it.
//! [`installed`] reports, per direction, whether a core is actually live, so a test that
//! wants to assert it got the verified object can.
//!
//! # Why a crate rather than a dev-dep on `dregg-lean-ffi` in each crate
//!
//! The install is seven calls whose arguments are `dregg-lean-ffi` symbol names. Copied
//! into six crates' test helpers, a seventh core (or a renamed export) means six edits and
//! five of them silently stay on the old set. `node/src/lib.rs::install_verified_pq_cores`
//! and `sdk/src/runtime.rs` are already two copies of this list; this is the one a test
//! reaches for, and `grep -rl dregg-pq-testkit` answers "which test binaries link the
//! archive for PQ" in one command.
//!
//! # Cost
//!
//! Measured, not assumed. A test binary that DOES call [`install`] links the PQ closure out
//! of the archive; one that merely has this crate in `[dev-dependencies]` and never calls it
//! links nothing extra — the linker pulls archive members by reference, and an unreferenced
//! `dregg_lean_ffi` pulls none. Measured on macOS at `4f39452c1`: `dregg-pq`'s own lib-test
//! binary, which has had a `dregg-lean-ffi` dev-dep since `f52d8ed91` and does not use it,
//! is 2.2 MB with zero Lean runtime symbols; `dregg-pq`'s `mldsa_lean_verify` test, which
//! does use it, is 126.8 MB with 234. So the cost is per-BINARY-that-calls, not per-crate.

use std::sync::Once;

/// Which of the six PQ directions have a Lean-verified core live in this process.
///
/// A `false` is not a failure of this crate — it means the linked archive does not export
/// that core, and the direction will still REFUSE at the point of use. A test that depends
/// on a direction should assert on it rather than discover it as a SIGABRT.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Installed {
    /// `ml_dsa_verify` — the accept/reject gate.
    pub mldsa_verify: bool,
    /// `MlDsaKey::sign` / `try_sign` — the deployed full-byte signer.
    pub mldsa_sign: bool,
    /// `MlDsaKey::from_ed25519_seed` — the identity-key derivation.
    pub mldsa_keygen: bool,
    /// `ml_kem768_encaps`.
    pub mlkem_encaps: bool,
    /// `ml_kem768_decaps`.
    pub mlkem_decaps: bool,
    /// `ml_kem768_keygen`.
    pub mlkem_keygen: bool,
}

impl Installed {
    /// The three ML-DSA directions — the ones an identity/signature test needs. `false` on
    /// any of them means a PQ signing or verifying test in this process will abort.
    pub fn mldsa_complete(self) -> bool {
        self.mldsa_verify && self.mldsa_sign && self.mldsa_keygen
    }
}

/// Install every Lean-verified PQ core this process's archive exports, once.
///
/// Idempotent, thread-safe, and safe to call from the top of every test. Call it BEFORE the
/// first PQ operation on the calling thread: `dregg-pq`'s installs are `OnceLock`s, so an
/// operation that beats the install takes the no-core path and aborts.
pub fn install() -> Installed {
    static ONCE: Once = Once::new();
    ONCE.call_once(|| {
        use dregg_pq::*;
        let _ = install_verified_mldsa_verify_core(
            dregg_lean_ffi::fips204_verify_real_core_available,
            |w| dregg_lean_ffi::shadow_fips204_verify_real(w).ok(),
        );
        let _ = install_verified_mldsa_sign_core_real(
            dregg_lean_ffi::fips204_sign_real_core_available,
            |w| dregg_lean_ffi::shadow_fips204_sign_real(w).ok(),
        );
        let _ = install_verified_mldsa_keygen_core_real(
            dregg_lean_ffi::mldsa_keygen_real_core_available,
            |w| dregg_lean_ffi::shadow_mldsa_keygen_real(w).ok(),
        );
        let _ = install_verified_mlkem_encaps_core(
            dregg_lean_ffi::mlkem_encaps_real_core_available,
            |w| dregg_lean_ffi::shadow_mlkem_encaps_real(w).ok(),
        );
        let _ = install_verified_mlkem_decaps_core(
            dregg_lean_ffi::mlkem_decaps_real_core_available,
            |w| dregg_lean_ffi::shadow_mlkem_decaps_real(w).ok(),
        );
        let _ = install_verified_mlkem_keygen_core(
            dregg_lean_ffi::mlkem_keygen_real_core_available,
            |w| dregg_lean_ffi::shadow_mlkem_keygen_real(w).ok(),
        );
    });
    installed()
}

/// What is live RIGHT NOW, independent of who installed it.
pub fn installed() -> Installed {
    Installed {
        mldsa_verify: dregg_pq::lean_verify_core_real_installed(),
        mldsa_sign: dregg_pq::lean_sign_core_real_installed(),
        mldsa_keygen: dregg_pq::lean_keygen_core_real_installed(),
        mlkem_encaps: dregg_pq::mlkem_encaps_real_core_installed(),
        mlkem_decaps: dregg_pq::mlkem_decaps_real_core_installed(),
        mlkem_keygen: dregg_pq::mlkem_keygen_real_core_installed(),
    }
}

/// [`install`], and PANIC with the missing directions named if the three ML-DSA cores did
/// not come up.
///
/// For a test whose subject IS the PQ path: without this the same condition surfaces later
/// as an uncatchable SIGABRT from inside `dregg-pq`, with the stack somewhere in the code
/// under test rather than at the archive that is actually wrong.
pub fn install_or_panic() -> Installed {
    let got = install();
    assert!(
        got.mldsa_complete(),
        "dregg-pq-testkit: the linked Lean archive does not export all three ML-DSA cores \
         (verify={} sign={} keygen={}). Any ML-DSA operation in this test process will be \
         REFUSED by dregg-pq's audit gate (an uncatchable process abort). Rebuild against a \
         HEAD-matching archive: dregg-lean-ffi's build script produces one, and \
         scripts/fetch-lean-seed.sh pulls the published platform-native seed.",
        got.mldsa_verify,
        got.mldsa_sign,
        got.mldsa_keygen,
    );
    got
}

/// Run [`install`] at PROCESS START, from one line at the top of a test file.
///
/// # When this, and not a call at the gateway
///
/// The adopters above put `install_or_panic()` at their own crate's entry into `dregg-pq`
/// (`turn/src/pq.rs`, `blocklace/src/pq.rs`, …) under `#[cfg(test)]`. That works when the
/// crate OWNS the gateway. It does not work for an INTEGRATION test (`tests/*.rs`), because
/// the crate under test is compiled as a DEPENDENCY there: `cfg(test)` is false in its
/// `src/`, so a `#[cfg(test)]` install one crate down is INERT. And the gateway is often not
/// in the test crate at all — `dregg-redteam` reaches ML-DSA only through
/// `dregg_blocklace::finality::Block::new`, `dregg-teasting` only through its own
/// `SimulationHarness`/`SimFederation` helpers, `realm-model` only through
/// `dregg_turn::pq::MlDsaTurnKey`.
///
/// Hanging the install on "every helper the file happens to use" makes coverage a property
/// of a hand-audited call list, and a missed one is a bare SIGABRT that takes the whole
/// binary. A process-start initializer makes it a property of the BINARY: it runs before
/// libtest starts, so no test can beat it and `--test-threads` cannot change the outcome.
/// This is the same mechanism, and for the same reason, as `dregg-node`'s
/// `pq_test_bootstrap` (`node/src/lib.rs`).
///
/// # It does not weaken the gate
///
/// [`install`] is export-gated per direction, so an archive that exports nothing installs
/// nothing and every PQ operation still hits `dregg-pq`'s refusal at the point of use. What
/// this adds is that the incomplete-archive case is REPORTED, on stderr, at process start —
/// before libtest's output capture exists to swallow it, which is what makes the current
/// failure mode a bare exit-134 with no text.
///
/// It deliberately does NOT panic like [`install_or_panic`]: a panic out of an
/// `extern "C"` initializer aborts before `main`, i.e. it replaces one uninformative abort
/// with another. A test whose SUBJECT is the PQ path should still call [`install_or_panic`]
/// itself and assert on [`Installed`].
///
/// ```no_run
/// // NO_RUN: the expansion registers a `.init_array` / `__mod_init_func` entry, so the
/// // verified PQ cores are installed process-globally BEFORE `main` — irreversible for
/// // the life of the process.
/// // tests/blocklace_attacks.rs
/// dregg_pq_testkit::install_at_process_start!();
/// # fn main() {}
/// ```
#[macro_export]
macro_rules! install_at_process_start {
    () => {
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        #[allow(dead_code)]
        mod dregg_pq_testkit_process_start {
            extern "C" fn install() {
                let got = $crate::install();
                if !got.mldsa_complete() {
                    // stderr, at process start: libtest has not installed its output capture
                    // yet, so unlike a message printed from inside a test this one survives.
                    eprintln!(
                        "dregg-pq-testkit: the linked Lean archive does not export all three \
                         ML-DSA cores (verify={} sign={} keygen={}). Every ML-DSA operation in \
                         this test binary will be REFUSED by dregg-pq's audit gate — an \
                         uncatchable process abort that takes the whole binary, not one test. \
                         Rebuild against a HEAD-matching archive (dregg-lean-ffi's build script \
                         produces one; scripts/fetch-lean-seed.sh pulls the published \
                         platform-native seed).",
                        got.mldsa_verify, got.mldsa_sign, got.mldsa_keygen,
                    );
                }
            }

            #[used]
            #[cfg_attr(target_os = "linux", unsafe(link_section = ".init_array"))]
            #[cfg_attr(target_os = "macos", unsafe(link_section = "__DATA,__mod_init_func"))]
            static INSTALL_VERIFIED_PQ_CORES: extern "C" fn() = install;
        }
    };
}
