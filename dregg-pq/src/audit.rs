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
//!   * a stale or incomplete `dregg-lean-ffi/libdregg_lean.a` seed can omit one
//!     or more of the six PQ cores, so a FRESH CLONE takes this path;
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
//!   script, which nm-probes the final archive for the six core exports and
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
//!   through `log`/`tracing`, which may be unconfigured or filtered at startup)
//!   — and "directly" now means a raw write to FILE DESCRIPTOR 2, not `eprintln!`.
//!   `eprintln!` goes through `std::io::stderr()`, which honours
//!   `std::io::set_output_capture`, which is what libtest installs around every
//!   test — so under `cargo test` the banner landed in a per-test capture buffer
//!   that `abort()` never flushes, and the refusal was a bare SIGABRT with no
//!   output. See [`eprintln_fd2`].
//!
//! * **Why an env opt-in rather than unconditional refusal?** An unconditional
//!   refusal would break legitimate work that has no verified core available and
//!   does not claim assurance: this crate's own fallback unit tests, differential
//!   KATs that deliberately drive the crate path, and non-PQ / marshal-only
//!   builds. The opt-in keeps those possible while making the DEFAULT the safe
//!   one — absence of the variable is fatal, so nobody reaches unaudited crypto
//!   by inaction. Opting in is a deliberate, greppable, auditable act that also
//!   prints a warning on first use.
//!
//! # ⚑ THE DECLARED-BYPASS DISCIPLINE (the residual this gate still had)
//!
//! Everything above was already true and already tested (`tests/unaudited_refusal.rs`
//! drives the abort as a real subprocess on four arms). Three things were NOT:
//!
//!   1. **`DREGG_ALLOW_UNAUDITED_PQ=1` was IRREVOCABLE.** The tree-wide "I demand
//!      the verified artifact" switch — `DREGG_REQUIRE_LEAN=1`, which
//!      `turn::require_verified_conservation_gate`, `node::finality_gate` and
//!      `node::coord_gate` all honour by revoking their declared bypasses — had **no
//!      effect on any PQ path at all**. An operator could demand the verified
//!      artifact and still have the unaudited `fips204` crate deciding
//!      accept/reject. [`unaudited_pq_bypass_allowed`] now makes it revoke the
//!      opt-in, so the two switches cannot contradict each other silently.
//!   2. **The bypass was UNREGISTERED.** No row in
//!      `scripts/ci-invariants/gate-dataflow.tsv`, so invariant 6 never looked at
//!      the PQ sites. It is registered now, at the named
//!      `mldsa::mldsa_verify_disposition` (twin#13).
//!   3. **The provenance was ONE process-global warning.** `warn_once_permitted`
//!      fires once, for the whole process, naming no operation — so an operator
//!      could not tell WHICH of the six PQ directions the unaudited crate answered,
//!      or how often. [`PqSite`] + [`pq_provenance`] now count both answers per
//!      site (verified core vs unaudited crate) and warn once PER SITE.
//!
//! This crate stays a light leaf: it exports the COUNTERS, and a host that has a
//! metrics recorder (`node::metrics::publish_pq_provenance`) turns them into
//! Prometheus series.

use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};

/// The one environment variable that permits this process to answer a
/// post-quantum operation with an UNAUDITED crate primitive. Must be exactly
/// `"1"`. Anything else (including unset, empty, `"true"`, `"yes"`) is refusal.
pub const ALLOW_UNAUDITED_PQ_ENV: &str = "DREGG_ALLOW_UNAUDITED_PQ";

/// The TREE-WIDE "I demand the verified artifact" switch. The same variable
/// `dregg-lean-ffi`'s build gate, `turn`'s `require_verified_conservation_gate`,
/// `node::finality_gate`'s `require_verified_lean_gate` and `node::coord_gate` read.
/// Setting it REVOKES [`ALLOW_UNAUDITED_PQ_ENV`] — see [`unaudited_pq_bypass_allowed`].
pub const REQUIRE_LEAN_ENV: &str = "DREGG_REQUIRE_LEAN";

/// Whether the operator explicitly accepted the unaudited fallback. Read ONCE
/// per process and cached: a later `set_var` cannot flip an already-refused
/// process into a permitting one (and `set_var` is `unsafe` as of Rust 2024).
fn unaudited_fallback_permitted() -> bool {
    static PERMITTED: OnceLock<bool> = OnceLock::new();
    *PERMITTED.get_or_init(|| std::env::var(ALLOW_UNAUDITED_PQ_ENV).as_deref() == Ok("1"))
}

/// `DREGG_REQUIRE_LEAN=1` — the operator demands the verified artifact, so NO declared
/// bypass around a verified core may be taken. Read once per process and cached, the same
/// way [`unaudited_fallback_permitted`] is, and accepting the same spellings
/// `node::coord_gate::require_verified_lean_gate` accepts (`1`/`true`/`on`/`yes`).
///
/// ⚑ BEFORE THIS EXISTED, `DREGG_REQUIRE_LEAN=1` HAD NO EFFECT ON ANY PQ PATH. A build
/// that demanded the verified artifact and got an archive without the six PQ exports ran
/// `fips204`/`ml-kem` anyway as long as `DREGG_ALLOW_UNAUDITED_PQ=1` was also set — two
/// switches with contradictory meanings, and the permissive one silently won.
pub(crate) fn require_verified_lean_gate() -> bool {
    static REQUIRED: OnceLock<bool> = OnceLock::new();
    *REQUIRED.get_or_init(|| {
        std::env::var_os(REQUIRE_LEAN_ENV)
            .is_some_and(|v| matches!(v.to_string_lossy().trim(), "1" | "true" | "on" | "yes"))
    })
}

/// Whether the unaudited crate fallback is ACCEPTED in this process — the operator's
/// [`ALLOW_UNAUDITED_PQ_ENV`] opt-in, or this crate's own declared `#[cfg(test)]` override
/// (see [`TEST_OVERRIDE`]; it is `false` in every non-test build).
///
/// ONE EXPRESSION with ONE body for every cfg, deliberately: the `#[cfg(test)]` arm used to
/// be a second `return` inside [`guard_unaudited_fallback`], which made the test binary's
/// disposition structurally different from the shipped one. Now the override is an INPUT to
/// the same predicate production takes (the shape `coord/src/atomic.rs` was corrected to).
pub(crate) fn unaudited_pq_accepted() -> bool {
    unaudited_fallback_permitted() || test_override_active()
}

/// FAIL-CLOSED CLASS (twin#13, the PQ sibling of `belt_gate_bypass_allowed` /
/// `coord_gate_bypass_allowed`): whether a post-quantum operation may be answered by the
/// UNAUDITED `fips204`/`ml-kem` crate primitive instead of the Lean-verified core.
///
/// ONE DECLARED BYPASS, and nothing else: there is NO verified core installed in this
/// process at all (`dregg-pq` is a light leaf — an archive-less build, the wasm/zkVM guest,
/// a host that cannot link the 156 MB archive) **and** the operator explicitly accepted the
/// unaudited primitive (`DREGG_ALLOW_UNAUDITED_PQ=1`). `require_lean`
/// (`DREGG_REQUIRE_LEAN=1`) REVOKES it.
///
/// Deliberately NOT a bypass: a verified core IS installed and it produced no usable answer
/// (`None` from the FFI, an `"ERR"` reply, a wrong-length/non-hex field). That is an
/// integrity failure of the archive, not a policy choice, and it must never route to the
/// crate — `verified_core_installed == true` makes this predicate `false` for exactly that
/// reason.
///
/// ⚑ ONE BOOLEAN EXPRESSION, DELIBERATELY, AND IT CALLS NOTHING. `gate-dataflow.py`
/// short-circuits on the first region line naming a declared discriminator and then looks
/// for a refusal in the region PLUS the inlined bodies of the helpers it calls (depth ≤ 2).
/// A `return false` inside a bypass predicate — or a helper call whose body contains a bare
/// `false` — is itself a REFUSAL token the checker finds, so the caller's real refusal arm
/// never gets read and a mutant that reverts it stays GREEN. MEASURED at the finality site
/// (commit `1736835f69`) and at the coord site. Keep this an expression over its arguments.
pub(crate) fn unaudited_pq_bypass_allowed(
    verified_core_installed: bool,
    unaudited_accepted_by_operator: bool,
    require_lean: bool,
) -> bool {
    !require_lean && !verified_core_installed && unaudited_accepted_by_operator
}

/// One of the SIX post-quantum directions that can be answered either by a Lean-verified
/// core or by an UNAUDITED crate primitive. Exists so the provenance is legible PER
/// DIRECTION: a single process-global "unaudited crypto is live" warning cannot tell an
/// operator whether it was a *verify* (an accept/reject gate) or a *keygen* (no verdict to
/// fail open on) that the crate answered.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PqSite {
    /// `ml_dsa_verify` — THE ACCEPT/REJECT GATE. The only one of the six whose answer is a
    /// security VERDICT rather than a produced value.
    MlDsaVerify,
    /// `MlDsaKey::try_sign` / `try_sign_deterministic` — produces signature bytes.
    MlDsaSign,
    /// `MlDsaKey::from_ed25519_seed` — expands the IDENTITY seed.
    MlDsaKeygen,
    /// `hybrid_kem::initiate` / `ml_kem768_encaps` — produces `(ct, ss)`.
    MlKemEncaps,
    /// `HybridResponder::finish` / `ml_kem768_decaps` — recovers `ss` (CAN fail).
    MlKemDecaps,
    /// `ml_kem768_keygen` — mints an ephemeral session keypair.
    MlKemKeygen,
}

impl PqSite {
    /// All six, in a fixed order — the array a host iterates to publish one metric series
    /// per site.
    pub const ALL: [PqSite; 6] = [
        PqSite::MlDsaVerify,
        PqSite::MlDsaSign,
        PqSite::MlDsaKeygen,
        PqSite::MlKemEncaps,
        PqSite::MlKemDecaps,
        PqSite::MlKemKeygen,
    ];

    /// The stable metric/label name for this site (`snake_case`, safe as a Prometheus label
    /// value and greppable in a log).
    pub fn label(self) -> &'static str {
        match self {
            PqSite::MlDsaVerify => "ml_dsa_verify",
            PqSite::MlDsaSign => "ml_dsa_sign",
            PqSite::MlDsaKeygen => "ml_dsa_keygen",
            PqSite::MlKemEncaps => "ml_kem_encaps",
            PqSite::MlKemDecaps => "ml_kem_decaps",
            PqSite::MlKemKeygen => "ml_kem_keygen",
        }
    }

    /// Whether this site's answer is a security ACCEPT/REJECT VERDICT (as opposed to a
    /// produced value). Only `ml_dsa_verify` is: a keygen has no verdict to fail open on.
    /// Used by hosts to decide which series is a SAFETY alarm and which is provenance.
    pub fn is_accept_reject_gate(self) -> bool {
        matches!(self, PqSite::MlDsaVerify)
    }

    fn idx(self) -> usize {
        match self {
            PqSite::MlDsaVerify => 0,
            PqSite::MlDsaSign => 1,
            PqSite::MlDsaKeygen => 2,
            PqSite::MlKemEncaps => 3,
            PqSite::MlKemDecaps => 4,
            PqSite::MlKemKeygen => 5,
        }
    }
}

/// Per-site count of operations answered by the UNAUDITED crate primitive.
static UNAUDITED_ANSWERS: [AtomicU64; 6] = [const { AtomicU64::new(0) }; 6];
/// Per-site count of operations answered by the Lean-VERIFIED core.
static VERIFIED_ANSWERS: [AtomicU64; 6] = [const { AtomicU64::new(0) }; 6];
/// Per-site count of REFUSALS taken because a verified core was installed and FAULTED.
static VERIFIED_CORE_FAULTS: [AtomicU64; 6] = [const { AtomicU64::new(0) }; 6];
/// Per-site one-shot latch for the "the unaudited crate answered THIS direction" warning.
static UNAUDITED_WARNED: [AtomicBool; 6] = [const { AtomicBool::new(false) }; 6];
/// Per-site one-shot latch for the "an installed verified core FAULTED" warning. A broken archive
/// faults on every call, so this line must be latched or it drowns out the thing it reports.
static FAULT_WARNED: [AtomicBool; 6] = [const { AtomicBool::new(false) }; 6];

/// THE PROVENANCE SNAPSHOT: for each of the six PQ directions,
/// `(site, answered_by_verified_core, answered_by_unaudited_crate, verified_core_faults)`.
///
/// This is the answer to "which implementation answered a given verification?" — a question
/// a one-shot startup `warn!` cannot answer. A host with a metrics recorder publishes it as
/// one series per site (`node::metrics::publish_pq_provenance`); a host without one can
/// still print it. A non-zero `unaudited` on [`PqSite::MlDsaVerify`] means the accept/reject
/// authority in this process is the `fips204` crate, right now, for that many verifications.
pub fn pq_provenance() -> [(PqSite, u64, u64, u64); 6] {
    PqSite::ALL.map(|site| {
        (
            site,
            VERIFIED_ANSWERS[site.idx()].load(Ordering::Relaxed),
            UNAUDITED_ANSWERS[site.idx()].load(Ordering::Relaxed),
            VERIFIED_CORE_FAULTS[site.idx()].load(Ordering::Relaxed),
        )
    })
}

/// Whether ANY post-quantum operation in this process has been answered by an unaudited
/// crate primitive. The single boolean a health endpoint / startup banner can surface.
pub fn any_unaudited_pq_answer() -> bool {
    PqSite::ALL
        .iter()
        .any(|s| UNAUDITED_ANSWERS[s.idx()].load(Ordering::Relaxed) > 0)
}

/// Record that the Lean-VERIFIED core answered `site`.
pub(crate) fn note_verified_answer(site: PqSite) {
    VERIFIED_ANSWERS[site.idx()].fetch_add(1, Ordering::Relaxed);
}

/// Write `msg` (plus a newline) to FILE DESCRIPTOR 2, stepping around `std::io::stderr()`.
///
/// ⚑ `eprintln!` IS NOT "straight to the fd", and every message in this module depended on
/// believing that it was. `std::io::stderr()` honours `std::io::set_output_capture`, and that is
/// precisely what libtest installs around each test it runs — so under `cargo test` the refusal
/// banner went into a per-test capture buffer that `process::abort()` never flushes. In the one
/// context where this gate fires most often (a test binary that reaches an ML-DSA primitive before
/// anything installed a core) the process died as a bare SIGABRT with NO OUTPUT AT ALL. Recovering
/// the reason took reading a macOS `.ips` crash report for the stack; `--nocapture` was the only
/// way to see the banner this module was written to make impossible to miss.
///
/// A raw `write(2)` is not intercepted, so the message survives libtest, and the subprocess arms in
/// `tests/unaudited_refusal.rs` — which read these needles off a pipe — see byte-identical text.
fn eprintln_fd2(msg: &str) {
    #[cfg(unix)]
    {
        use std::io::Write;
        use std::os::fd::FromRawFd;
        // SAFETY: fd 2 is stderr for the whole life of the process. `ManuallyDrop` keeps the
        // `File` from closing it on drop, so this borrows the descriptor rather than owning it.
        let mut fd2 = std::mem::ManuallyDrop::new(unsafe { std::fs::File::from_raw_fd(2) });
        // One write, so a concurrent writer cannot split the banner down the middle.
        let _ = fd2.write_all(format!("{msg}\n").as_bytes());
        let _ = fd2.flush();
    }
    #[cfg(not(unix))]
    {
        eprintln!("{msg}");
    }
}

/// Record that the UNAUDITED crate answered `site`, and say so ONCE PER SITE.
///
/// The per-site latch is the point: [`warn_once_permitted`] fires once for the whole
/// process and names no operation, so a node that answered one keygen from the crate and a
/// million verifies from the crate printed the SAME single line. This one names the
/// direction, the crate, and the install call that would have routed it to Lean.
pub(crate) fn note_unaudited_answer(
    site: PqSite,
    op: &str,
    unaudited_crate: &str,
    install_fn: &str,
) {
    // The process-level announcement stays: `tests/unaudited_refusal.rs::
    // explicit_opt_in_permits_and_announces` pins it, and it is the line that says "this WHOLE
    // process is unaudited" as opposed to "this direction is". It is gated on the env var actually
    // being set, so this crate's own `#[cfg(test)]` binary does not print a line naming a variable
    // nobody set.
    if unaudited_fallback_permitted() {
        warn_once_permitted();
    }
    UNAUDITED_ANSWERS[site.idx()].fetch_add(1, Ordering::Relaxed);
    if !UNAUDITED_WARNED[site.idx()].swap(true, Ordering::Relaxed) {
        let verdict = if site.is_accept_reject_gate() {
            " ⚑ THIS IS AN ACCEPT/REJECT GATE: the security verdict in this process is the \
             unaudited crate's, not the verified core's."
        } else {
            ""
        };
        // Name WHICH declared bypass permitted it. Conflating the operator's env opt-in with this
        // crate's cfg(test) override would make the line a small lie in exactly the binary where a
        // reader is most likely to be checking what the gate does.
        let permitted_by = if unaudited_fallback_permitted() {
            "the operator set DREGG_ALLOW_UNAUDITED_PQ=1"
        } else {
            "dregg-pq's own #[cfg(test)] override is active (this is a dregg-pq unit-test binary, \
             which cannot link the archive at all)"
        };
        eprintln_fd2(&format!(
            "WARNING: dregg-pq PQ PROVENANCE [{label}] — the UNAUDITED `{unaudited_crate}` crate \
             answered `{op}` in this process: no Lean-verified core is installed for it, and \
             {permitted_by}, so the DECLARED bypass held. Route it to the verified core with \
             dregg_pq::{install_fn}(..), or set {REQUIRE_LEAN_ENV}=1 to make this a REFUSAL instead \
             of a bypass. Any assurance claim resting on the verified core is VOID for `{op}` in \
             this process.{verdict}",
            label = site.label(),
        ));
    }
}

/// Record that a verified core was installed for `site` and FAULTED (so the site refused rather
/// than routing to the crate), and say so ONCE PER SITE.
///
/// The one-shot latch matters here: a broken archive faults on EVERY call, so an unlatched line
/// would be one stderr write per verification — which is how a real signal becomes noise an
/// operator filters out. The COUNT is the rate signal (`pq_provenance`); the line is the
/// explanation.
pub(crate) fn note_verified_core_fault(site: PqSite) {
    VERIFIED_CORE_FAULTS[site.idx()].fetch_add(1, Ordering::Relaxed);
    if !FAULT_WARNED[site.idx()].swap(true, Ordering::Relaxed) {
        eprintln_fd2(&format!(
            "ERROR: dregg-pq PQ PROVENANCE [{label}] — a Lean-verified core IS installed for this \
             direction and it FAULTED (no usable answer out of the FFI). The operation REFUSES; the \
             unaudited crate is NOT consulted, because falling back here would silently re-admit \
             exactly the authority the install removed. There is NO opt-out for a faulting core — \
             this is a BROKEN ARCHIVE, not a policy choice. Watch \
             dregg_pq_verified_core_faults_total{{site=\"{label}\"}} for the rate.",
            label = site.label(),
        ));
    }
}

/// Abort the process, naming the operation and the unaudited crate that would
/// otherwise have answered it, plus the exact install call that would have
/// routed it to the verified Lean core.
///
/// Never returns. Not a panic — see the module docs.
#[cold]
#[inline(never)]
pub(crate) fn refuse_unaudited(op: &str, unaudited_crate: &str, install_fn: &str) -> ! {
    // WHICH refusal this is. The two are very different operator situations and the old
    // message could only describe one of them: if the opt-in IS set and we are refusing
    // anyway, "TO PROCEED ANYWAY set DREGG_ALLOW_UNAUDITED_PQ=1" is advice the operator has
    // already taken, and reading it would send them looking for a bug that is not there.
    let revoked_by_require_lean = require_verified_lean_gate() && unaudited_pq_accepted();
    if revoked_by_require_lean {
        eprintln_fd2(&format!(
            "\n\
             ================================================================================\n\
             FATAL: dregg-pq refused UNAUDITED post-quantum crypto — {REQUIRE_LEAN_ENV}=1\n\
             REVOKED the {ALLOW_UNAUDITED_PQ_ENV}=1 bypass.\n\
             ================================================================================\n\
             operation             : {op}\n\
             would have been run by: the UNAUDITED `{unaudited_crate}` crate\n\
             required instead      : the Lean-verified core, installed via\n\
                                     dregg_pq::{install_fn}(..)\n\
             \n\
             BOTH of these are set, and they contradict each other:\n\
               {ALLOW_UNAUDITED_PQ_ENV}=1   (accept unaudited crate primitives)\n\
               {REQUIRE_LEAN_ENV}=1  (demand the verified artifact — no bypasses)\n\
             The DEMAND WINS. This is the declared revocation, not a malfunction: an operator\n\
             who asks for the verified artifact must not be silently opted out of it by a\n\
             second variable. Pick one:\n\
               * link an archive that EXPORTS the six verified PQ cores and install them, or\n\
               * unset {REQUIRE_LEAN_ENV} to take the declared unaudited bypass deliberately.\n\
             ================================================================================\n"
        ));
        std::process::abort()
    }
    refuse_unaudited_no_optin(op, unaudited_crate, install_fn)
}

/// The original refusal message: no verified core AND no opt-in. Kept verbatim (it is what
/// `tests/unaudited_refusal.rs` pins, needle by needle).
#[cold]
#[inline(never)]
fn refuse_unaudited_no_optin(op: &str, unaudited_crate: &str, install_fn: &str) -> ! {
    // Straight to the fd. No `log`/`tracing` (may be unconfigured or filtered),
    // no allocation-heavy formatting machinery beyond what `eprintln!` needs.
    eprintln_fd2(&format!(
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
           1. The linked libdregg_lean.a does not EXPORT all six verified PQ cores;\n\
              a correct archive is produced by dregg-lean-ffi's build script. Check:\n\
                nm -g --defined-only <archive> | grep -E \
                  'dregg_(fips204_(verify|sign)_real|mldsa_keygen_real|mlkem_(keygen|encaps|decaps)_real)'\n\
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
    ));
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
pub(crate) fn abort_verified_core_fault(site: PqSite, op: &str, export_sym: &str) -> ! {
    note_verified_core_fault(site);
    eprintln_fd2(&format!(
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
    ));
    std::process::abort()
}

/// Gate the unaudited fallback for one operation.
///
/// Call this at the top of every branch that is about to answer a
/// security-critical PQ operation with a crate primitive instead of the
/// Lean-verified core. Returns normally ONLY if the operator opted in; otherwise
/// it aborts the process and never returns.
///
/// `site` names the PQ direction (so the provenance is counted and warned PER DIRECTION),
/// `op` names the operation (e.g. `"ML-DSA-65 verify"`), `unaudited_crate` names the crate
/// that would answer it (e.g. `"fips204 0.4"`), and `install_fn` names the `dregg_pq` install
/// function that routes it to the verified core.
///
/// THE DISPOSITION IS [`unaudited_pq_bypass_allowed`], the one declared, single-expression
/// bypass predicate every PQ site shares. `verified_core_installed` is passed as `false`
/// because every caller reaches this only on the branch where its `OnceLock` was empty; a
/// site whose core IS installed and faulted must NOT come here (it refuses — see
/// [`abort_verified_core_fault`] and `mldsa::mldsa_verify_disposition`).
#[inline]
pub(crate) fn guard_unaudited_fallback(
    site: PqSite,
    op: &str,
    unaudited_crate: &str,
    install_fn: &str,
) {
    if unaudited_pq_bypass_allowed(false, unaudited_pq_accepted(), require_verified_lean_gate()) {
        note_unaudited_answer(site, op, unaudited_crate, install_fn);
        return;
    }
    refuse_unaudited(op, unaudited_crate, install_fn)
}

/// Warn (loudly, once) that a KEY-GENERATION operation is proceeding WITHOUT a
/// Lean-verified core installed, and RETURN so the caller mints from the crate
/// primitive.
///
/// This is the keygen sibling of [`guard_unaudited_fallback`]. Encaps/decaps
/// ABORT when no verified core is installed (they operate on secret material an
/// adversary supplies the other half of); keygen WARNS and PROCEEDS, because a
/// process that cannot link the verified archive still needs to be able to mint a
/// key to function at all, and refusing would brick every such node. The deployed,
/// archive-linked processes install the verified core and never reach this branch;
/// this warning is the honest record when one is missing.
///
/// ⚑ `DREGG_REQUIRE_LEAN=1` DOES **NOT** CONVERT THIS WARNING INTO A REFUSAL, and that is a
/// DECLARED decision rather than an oversight. The revocation applies to the ACCEPT/REJECT and
/// secret-recovery directions ([`guard_unaudited_fallback`]); this one mints an EPHEMERAL
/// per-session ML-KEM keypair, and refusing it bricks `responder_offer` — i.e. every CaPTP /
/// session handshake — on any process that cannot link the archive. The direction that mints
/// LONG-LIVED key material, `MlDsaKey::from_ed25519_seed` (the node IDENTITY key), routes
/// through [`guard_unaudited_fallback`] and therefore DOES refuse. What this call now adds is
/// the per-site count + label ([`pq_provenance`]) so the waiver is legible in metrics rather
/// than only in one line of boot stderr.
///
/// `op` names the operation, `unaudited_crate` names the crate that answers it,
/// and `guards` describes what the freshly-minted key protects — all surfaced in
/// the one-shot warning so an operator can see the exact assurance being waived.
#[inline]
pub(crate) fn guard_no_verified_core(site: PqSite, op: &str, unaudited_crate: &str, guards: &str) {
    UNAUDITED_ANSWERS[site.idx()].fetch_add(1, Ordering::Relaxed);
    static WARNED: OnceLock<()> = OnceLock::new();
    if WARNED.set(()).is_ok() {
        eprintln_fd2(&format!(
            "WARNING: dregg-pq is generating a post-quantum key ({op}) with the UNAUDITED \
             `{unaudited_crate}` crate primitive because NO Lean-verified core is installed in \
             this process. The verified core is NOT the authority for this key ({guards}). \
             Deployed, archive-linked processes install the verified core; this process cannot \
             link it. Any assurance claim resting on the verified core is VOID for keys minted here."
        ));
    }
}

/// Announce the opt-in exactly once per process, so an operator who set the
/// variable (or inherited it from a script) still sees that this process is
/// running unaudited crypto.
fn warn_once_permitted() {
    static WARNED: OnceLock<()> = OnceLock::new();
    if WARNED.set(()).is_ok() {
        eprintln_fd2(&format!(
            "WARNING: {ALLOW_UNAUDITED_PQ_ENV}=1 — dregg-pq is answering post-quantum \
             operations with UNAUDITED crate primitives (fips204 / ml-kem). The Lean-verified \
             cores are NOT the authority in this process. Any assurance claim that depends on \
             them is VOID for this run."
        ));
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
/// ⚑ AND IT IS AN INPUT TO THE ONE DISPOSITION, NOT A SECOND `return`. It used to be an
/// extra `#[cfg(test)] if test_override_active() { return; }` arm inside
/// [`guard_unaudited_fallback`], which meant the test binary's gate-absent DISPOSITION was
/// structurally a different function from the shipped one — the divergence class
/// `coord/src/atomic.rs::evaluate_votes_no_gate` was corrected for. It now flows through
/// [`unaudited_pq_accepted`], whose body is IDENTICAL under every cfg, so what the tests
/// exercise is the production predicate with one input flipped.
///
/// `DREGG_REQUIRE_LEAN=1` revokes it exactly as it revokes the operator opt-in — uniformly,
/// with no test-only exemption. So `DREGG_REQUIRE_LEAN=1 cargo test -p dregg-pq` aborts on
/// the first PQ operation, and that is the CORRECT answer: this unit-test binary cannot link
/// the archive, so there is no verified core for the demand to be satisfied by. The
/// subprocess tests in `tests/unaudited_refusal.rs` set their own env explicitly and are
/// unaffected.
#[cfg(test)]
static TEST_OVERRIDE: AtomicBool = AtomicBool::new(true);

#[cfg(test)]
fn test_override_active() -> bool {
    TEST_OVERRIDE.load(Ordering::Relaxed)
}

/// The NON-TEST body of the declared test override: there is no override in any shipped
/// build. Same signature, same call site, so [`unaudited_pq_accepted`] has ONE body for
/// every cfg.
#[cfg(not(test))]
#[inline]
fn test_override_active() -> bool {
    false
}

/// Re-assert the unit-test opt-in (it is already the default; this exists so a
/// test that deliberately clears it can restore it).
#[cfg(test)]
#[allow(dead_code)]
pub(crate) fn allow_unaudited_for_tests() {
    TEST_OVERRIDE.store(true, std::sync::atomic::Ordering::Relaxed);
}
