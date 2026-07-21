//! Refusal gate for the UNAUDITED post-quantum fallback path.
//!
//! # The hole this closes
//!
//! `dregg-pq` is a LIGHT leaf: it never links the 546 MB Lean archive. The
//! Lean-verified ML-DSA / ML-KEM cores are INJECTED as `fn` pointers by a host
//! that *can* link it (see `install_verified_mldsa_verify_core` and friends).
//! Until such a host installs them, every operation in this crate is answered by
//! the `fips204` 0.4 / `ml-kem` 0.2.3 RustCrypto crates — which are NOT audited
//! and are NOT the proven objects this project's assurance claims rest on.
//!
//! That fallback used to be SILENT. The failure mode it produced is the worst
//! one available to us: nothing errors, every signature still verifies, every
//! handshake still completes, the build is green — and the accept/reject
//! authority in the deployed binary is code nobody audited. It is reached by
//! ordinary accidents, not by sabotage:
//!
//!   * the git-tracked `dregg-lean-ffi/libdregg_lean.a` seed exports ZERO of the
//!     three PQ cores (`nm`-established), so a FRESH CLONE takes this path;
//!   * `dregg-lean-ffi`'s build script degrades to that seed on a `lake build`
//!     failure, a `leanc` failure, or a splice failure — each reported only as a
//!     `cargo:warning=`, which cargo hides for dependency build scripts;
//!   * a host binary that simply never calls the install functions.
//!
//! In all three the process runs unaudited crypto with no signal at all.
//!
//! # The mechanism, and why this one
//!
//! Reaching an unaudited primitive is FATAL unless the operator has explicitly
//! accepted it by setting `DREGG_ALLOW_UNAUDITED_PQ=1`.
//!
//! * **Why not fail the build/link?** Impossible in principle *here*. `dregg-pq`
//!   does not link the archive; whether a host will install verified cores is
//!   unknowable at this crate's compile time. The build-time half of this gate
//!   therefore lives where the archive IS linked — `dregg-lean-ffi`'s build
//!   script, which nm-probes the final archive for the three core exports and
//!   fails the build when they are missing. The two halves are complementary:
//!   that one catches a bad ARTIFACT, this one catches a host that never
//!   installed (or a call that beat the install).
//!
//! * **Why `abort()` and not `panic!`?** A panic is CATCHABLE, and in exactly the
//!   deployed shape we care about it gets swallowed: a `tokio` task panic kills
//!   only that task, so a serving node would log one backtrace per request and
//!   keep answering — quiet substitution restored, with extra steps. Likewise
//!   `catch_unwind`, and `panic = "abort"` is not something a leaf can assume.
//!   `process::abort()` cannot be caught, cannot be unwound past, and cannot be
//!   swallowed by a task boundary. The message goes to stderr directly (not
//!   through `log`/`tracing`, which may be unconfigured or filtered at startup).
//!
//! * **Why an env opt-in rather than unconditional refusal?** An unconditional
//!   refusal would break legitimate work that has no verified core available and
//!   does not claim assurance: this crate's own fallback unit tests, differential
//!   KATs that deliberately drive the crate path, and non-PQ / marshal-only
//!   builds. The opt-in keeps those possible while making the DEFAULT the safe
//!   one — absence of the variable is fatal, so nobody reaches unaudited crypto
//!   by inaction. Opting in is a deliberate, greppable, auditable act that also
//!   prints a warning on first use.

use std::sync::OnceLock;

/// The one environment variable that permits this process to answer a
/// post-quantum operation with an UNAUDITED crate primitive. Must be exactly
/// `"1"`. Anything else (including unset, empty, `"true"`, `"yes"`) is refusal.
pub const ALLOW_UNAUDITED_PQ_ENV: &str = "DREGG_ALLOW_UNAUDITED_PQ";

/// Whether the operator explicitly accepted the unaudited fallback. Read ONCE
/// per process and cached: a later `set_var` cannot flip an already-refused
/// process into a permitting one (and `set_var` is `unsafe` as of Rust 2024).
fn unaudited_fallback_permitted() -> bool {
    static PERMITTED: OnceLock<bool> = OnceLock::new();
    *PERMITTED.get_or_init(|| std::env::var(ALLOW_UNAUDITED_PQ_ENV).as_deref() == Ok("1"))
}

/// Abort the process, naming the operation and the unaudited crate that would
/// otherwise have answered it, plus the exact install call that would have
/// routed it to the verified Lean core.
///
/// Never returns. Not a panic — see the module docs.
#[cold]
#[inline(never)]
fn refuse_unaudited(op: &str, unaudited_crate: &str, install_fn: &str) -> ! {
    // Straight to the fd. No `log`/`tracing` (may be unconfigured or filtered),
    // no allocation-heavy formatting machinery beyond what `eprintln!` needs.
    eprintln!(
        "\n\
         ================================================================================\n\
         FATAL: dregg-pq refused to run UNAUDITED post-quantum crypto.\n\
         ================================================================================\n\
         operation            : {op}\n\
         would have been run by: the UNAUDITED `{unaudited_crate}` crate\n\
         required instead      : the Lean-verified core, installed via\n\
                                 dregg_pq::{install_fn}(..)\n\
         \n\
         No verified core is installed in this process, so this operation would have\n\
         been answered by a primitive that is NOT part of the audited, proven TCB.\n\
         Rather than substitute it silently, the process is aborting.\n\
         \n\
         LIKELY CAUSE (in descending order of how often it is the real one):\n\
           1. The linked libdregg_lean.a does not EXPORT the verified PQ cores. The\n\
              git-tracked dregg-lean-ffi/libdregg_lean.a seed exports ZERO of them;\n\
              a correct archive is produced by dregg-lean-ffi's build script. Check:\n\
                nm -g --defined-only <archive> | grep dregg_fips204_verify_real\n\
           2. dregg-lean-ffi's build script degraded to that seed (a `lake build`,\n\
              `leanc`, or archive-splice failure). Cargo HIDES dependency build-script\n\
              warnings; re-run with `cargo build -vv` to see them.\n\
           3. This binary never calls the install functions at startup.\n\
         \n\
         TO PROCEED ANYWAY (accepting UNAUDITED crypto, and forfeiting every assurance\n\
         claim that depends on the verified cores) set:\n\
           {ALLOW_UNAUDITED_PQ_ENV}=1\n\
         Do NOT set it in production, in a validator, or in anything whose output is\n\
         presented as verified.\n\
         ================================================================================\n"
    );
    std::process::abort()
}

/// Abort for an installed-but-FAULTED verified core.
///
/// Reached only when a Lean-verified core WAS installed for a security-critical operation but returned
/// garbage at runtime (a `None`/`"ERR"` reply, a wrong-length or non-hex field). Unlike
/// [`guard_unaudited_fallback`], there is no opt-out: a faulting verified core is an integrity failure, not
/// a policy choice, so falling back to the unaudited crate for (e.g.) the node IDENTITY key would silently
/// re-admit exactly what the verified path removed. Uncatchable abort — see the module docs on `abort()`.
#[cold]
#[inline(never)]
pub(crate) fn abort_verified_core_fault(op: &str, export_sym: &str) -> ! {
    eprintln!(
        "\n\
         ================================================================================\n\
         FATAL: dregg-pq verified core FAULTED (installed but returned garbage).\n\
         ================================================================================\n\
         operation      : {op}\n\
         verified export: {export_sym}\n\
         \n\
         A Lean-verified core was installed for this operation but produced no usable answer\n\
         (an FFI/archive fault, an \"ERR\" reply, or a wrong-length/non-hex field). Falling back\n\
         to the unaudited crate here would silently re-admit what the verified path removed, so\n\
         the process is aborting instead. There is NO opt-out for a faulting core.\n\
         ================================================================================\n"
    );
    std::process::abort()
}

/// Gate the unaudited fallback for one operation.
///
/// Call this at the top of every branch that is about to answer a
/// security-critical PQ operation with a crate primitive instead of the
/// Lean-verified core. Returns normally ONLY if the operator opted in; otherwise
/// it aborts the process and never returns.
///
/// `op` names the operation (e.g. `"ML-DSA-65 verify"`), `unaudited_crate` names
/// the crate that would answer it (e.g. `"fips204 0.4"`), and `install_fn` names
/// the `dregg_pq` install function that routes it to the verified core.
#[inline]
pub(crate) fn guard_unaudited_fallback(op: &str, unaudited_crate: &str, install_fn: &str) {
    if unaudited_fallback_permitted() {
        warn_once_permitted();
        return;
    }
    #[cfg(test)]
    if test_override_active() {
        return;
    }
    refuse_unaudited(op, unaudited_crate, install_fn)
}

/// Announce the opt-in exactly once per process, so an operator who set the
/// variable (or inherited it from a script) still sees that this process is
/// running unaudited crypto.
fn warn_once_permitted() {
    static WARNED: OnceLock<()> = OnceLock::new();
    if WARNED.set(()).is_ok() {
        eprintln!(
            "WARNING: {ALLOW_UNAUDITED_PQ_ENV}=1 — dregg-pq is answering post-quantum \
             operations with UNAUDITED crate primitives (fips204 / ml-kem). The Lean-verified \
             cores are NOT the authority in this process. Any assurance claim that depends on \
             them is VOID for this run."
        );
    }
}

/// Refuse an operation for which NO verified core EXISTS AT ALL.
///
/// Distinct from [`refuse_unaudited`] on purpose. That one says "a verified core
/// exists; this process did not install it" and names the install call. Saying
/// that about KEY GENERATION would be a LIE: as of this writing the project has
/// no Lean-verified ML-DSA / ML-KEM keygen core, exported or otherwise --
/// `nm -g --defined-only libdregg_lean.a | grep dregg_` yields verify / sign /
/// encaps / decaps and NOTHING for keygen, and `metatheory/Dregg2/Crypto/`
/// contains no keygen `@[export]` (the only `keygen` in the Lean tree is
/// `ThresholdSignerRefinement.ThresholdSignerApi.keygen`, an ABSTRACT TS-UF-0
/// game field -- public matrix, group key, threshold -- not an executable
/// FIPS 203/204 key generator).
///
/// So there is no install call to point at, and no amount of correct deployment
/// makes this path go away. The message must say that plainly rather than imply
/// a fixable misconfiguration.
///
/// Never returns. Not a panic -- see the module docs.
#[cold]
#[inline(never)]
fn warn_once_no_verified_core(op: &str, unaudited_crate: &str, consumes: &str) {
    // Fire exactly once per process. A per-callsite `static` is not possible (this is a
    // shared fn), so one process-global gate covers all keygen sites -- the fact ("this
    // process's keys are crate-generated") is a per-process property, not a per-call one.
    static WARNED: OnceLock<()> = OnceLock::new();
    if WARNED.set(()).is_err() {
        return;
    }
    eprintln!(
        "\n\
         ================================================================================\n\
         WARNING: dregg-pq is GENERATING KEYS with an UNAUDITED primitive.\n\
         ================================================================================\n\
         operation              : {op}\n\
         run by                 : the UNAUDITED `{unaudited_crate}` crate\n\
         verified core available: NONE. This project has NO Lean-verified keygen core.\n\
         \n\
         This is NOT a misconfiguration and NOT a missing install call. Unlike verify /\n\
         sign / encaps / decaps -- each of which HAS an extracted, proved Lean core that a\n\
         host installs -- key generation has no verified implementation in this project at\n\
         all. Nothing you can link or install routes this operation to a proven object.\n\
         \n\
         WHY THIS IS A WARNING, NOT AN ABORT: the only refuse-escape is the GLOBAL\n\
         {ALLOW_UNAUDITED_PQ_ENV}=1 opt-in, which ALSO disables the sign/verify/encaps/\n\
         decaps refuse-gates. Aborting keygen -- which no install could ever satisfy --\n\
         would force EVERY deployment to set that flag and thereby disarm ALL gates. That\n\
         is strictly worse than proceeding here behind this loud, un-hideable, greppable\n\
         warning while the other gates stay armed. (Decision recorded in\n\
         DEPLOYED-WEAKNESSES.md; reversible to a keygen-specific opt-in if fail-closed\n\
         keygen is wanted before a verified core exists.)\n\
         \n\
         WHAT THIS MEANS: the output is SECRET KEY MATERIAL ({consumes}). A verified\n\
         sign/verify path over keys minted by an unaudited generator is a PARTIAL assurance\n\
         story: the proofs cover the transform, not the secret it operates on. Key quality\n\
         (seed expansion, rejection sampling, the CSPRNG draw) is exactly where a defect is\n\
         silent and unrecoverable -- a signature made under a weak key verifies perfectly\n\
         through the verified core. This holds for EVERY key dregg-pq has ever minted, on\n\
         every host, and is closed only by a Lean-verified ML-DSA/ML-KEM KeyGen core.\n\
         ================================================================================\n"
    );
}

/// Gate an operation whose ONLY implementation is an unaudited crate primitive,
/// because no verified core for it exists in the project.
///
/// Unlike [`guard_unaudited_fallback`] (which ABORTS when an *installable* verified
/// core is absent), this gap is STRUCTURAL: no verified keygen core exists to install,
/// so aborting could only be escaped via the global opt-out that disarms every other
/// gate too. This therefore always RETURNS, emitting a loud once-per-process warning
/// (see [`warn_once_no_verified_core`]); keygen proceeds on the crate, loudly and
/// greppably, while the sign/verify/encaps/decaps refuse-gates stay armed.
///
/// `consumes` names what the unaudited output becomes (e.g. `"an ML-DSA-65
/// secret key"`), so the warning states the exposure and not just the call site.
#[inline]
pub(crate) fn guard_no_verified_core(op: &str, unaudited_crate: &str, consumes: &str) {
    if unaudited_fallback_permitted() {
        warn_once_permitted();
        warn_once_keygen_unverified();
        return;
    }
    #[cfg(test)]
    if test_override_active() {
        return;
    }
    warn_once_no_verified_core(op, unaudited_crate, consumes)
}

/// Announce, once per process, that the PQ KEYS this process is using were
/// generated by an unaudited crate -- a claim SEPARATE from and not covered by
/// [`warn_once_permitted`], which is about operations.
///
/// An operator who set the opt-in for a legitimate reason (a fallback KAT, a
/// non-PQ build) still needs to see that KEY MATERIAL specifically left the
/// verified TCB, because that is the fact which outlives the process: keys
/// persist, get enrolled, get pinned.
fn warn_once_keygen_unverified() {
    static WARNED: OnceLock<()> = OnceLock::new();
    if WARNED.set(()).is_ok() {
        eprintln!(
            "WARNING: dregg-pq generated POST-QUANTUM KEY MATERIAL with an UNAUDITED crate \
             (fips204 / ml-kem). There is NO Lean-verified keygen core in this project, so \
             this is true of EVERY key dregg-pq has ever minted, on every host. The verified \
             sign/verify/encaps/decaps cores operate on keys they did not produce and do not \
             attest; any assurance claim about this process's KEYS is VOID."
        );
    }
}

/// Test-only opt-in for this crate's UNIT tests.
///
/// Those tests deliberately exercise the crate fallback (there is no archive to
/// link from a `dregg-pq` unit-test binary), so without an opt-in every one of
/// them would abort. They cannot use the env var: `unaudited_fallback_permitted`
/// caches its read in a `OnceLock`, and cargo runs tests in PARALLEL THREADS of
/// one process, so a test setting the variable could not win the race against a
/// sibling test that already tripped the read. This is a plain atomic instead —
/// set on the test's own thread strictly before its first PQ op, so there is no
/// race to lose. It DEFAULTS TO TRUE: a `dregg-pq` unit-test binary cannot link
/// the archive at all, so by construction every unit test runs on the crate
/// fallback — that is the honest description of this test binary, not a hole.
///
/// ★ THIS DOES NOT WEAKEN THE SHIPPED GATE. It is `#[cfg(test)]`, so it exists
/// only inside `dregg-pq`'s own unit-test binary — not in the shipped `rlib`,
/// not for integration tests, not for any downstream crate. And the gate's real
/// SHIPPING behaviour is not left untested by it: `tests/unaudited_refusal.rs`
/// spawns a genuine subprocess with no core installed and no opt-in, and asserts
/// the abort actually happens with the naming message. The override lets the
/// tests that are about KEM/DSA BEHAVIOUR run; the subprocess test covers the
/// gate itself, on the same code path a deployed binary takes.
#[cfg(test)]
static TEST_OVERRIDE: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(true);

#[cfg(test)]
fn test_override_active() -> bool {
    TEST_OVERRIDE.load(std::sync::atomic::Ordering::Relaxed)
}

/// Re-assert the unit-test opt-in (it is already the default; this exists so a
/// test that deliberately clears it can restore it).
#[cfg(test)]
#[allow(dead_code)]
pub(crate) fn allow_unaudited_for_tests() {
    TEST_OVERRIDE.store(true, std::sync::atomic::Ordering::Relaxed);
}
