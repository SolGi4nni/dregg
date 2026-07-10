//! `dregg-lean-ffi` library — marshal codec + optional Lean kernel shadow execution.
//!
//! When `libdregg_lean.a` is present at build time (`cfg(lean_lib_present)`), the crate
//! links the verified Lean kernel and exposes `shadow_exec_full_forest_auth`. When the
//! archive is absent the crate still builds (marshal-only); `lean_available()` is false.

#[path = "marshal.rs"]
pub mod marshal;

/// THE NO-COPY (`lean_object*`) boundary — construct/read the Lean inductives directly across the
/// FFI, no JSON serialize/parse in either direction (the JSON path in `marshal` is the oracle).
#[path = "lean_direct.rs"]
pub mod lean_direct;

pub use lean_direct::{
    direct_available, identity_floor_median, shadow_exec_direct, shadow_exec_direct_profiled,
    WireTurnHdr,
};

/// The VERIFIED DISTRIBUTED exports (federation strand-admission, etc.) — kept in a module distinct
/// from the executor-facing marshal/lib plumbing.
#[path = "distributed_ffi.rs"]
pub mod distributed_ffi;

pub use distributed_ffi::{
    decode_tau_order, distributed_exports_available, shadow_captp_pipeline_resolve,
    shadow_captp_process_drop, shadow_captp_validate_handoff, shadow_coord_2pc_decide,
    shadow_coord_causal_order, shadow_coord_shared_budget, shadow_strand_admit, shadow_tau_order,
    strand_admit_available, tau_order_available, verified_2pc_decide, verified_admits,
    verified_handoff_non_amplifying, verified_happened_before, verified_tau_order, Decision2pc,
};
pub use marshal::{AdmissionReason, TurnStatus, WireState};

// STORAGE-IN-LEAN EXTRACTION — force-link circuit's `dregg_poseidon2_2to1` into the binary. The
// leanc-compiled storage content-root logic (`Dregg2.Storage.Deployed.poseidon2Hash`) calls it via
// `@[extern "dregg_poseidon2_2to1"]`, but NO Rust code references circuit, so without this `#[used]`
// pointer the linker dead-strips the whole `dregg_circuit` rlib and the symbol goes undefined.
#[cfg(dregg_storage_content_root_present)]
#[used]
static _FORCE_LINK_POSEIDON2: unsafe extern "C" fn(u64, u64) -> u64 =
    dregg_circuit::storage_ffi::dregg_poseidon2_2to1;

/// Decoded Lean gated-forest verdict (T9 output envelope).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShadowVerdict {
    /// `true` ONLY when the gated forest BODY committed (`status == BodyCommitted`). A
    /// prologue-only result (forged credential / violated caveat / failed effect → the fee was
    /// charged as anti-spam but the body rolled back) is `committed == false` — the turn is
    /// REJECTED, NOT accepted (boundary-P1 bug 2).
    pub committed: bool,
    pub loglen: u64,
    /// The three-way status (boundary-P1 bug 2). `None` only for the legacy no-`status` wire.
    pub status: Option<TurnStatus>,
    /// The theorem-backed admission reason — the legible "why" of a refused turn. `None` for the
    /// legacy no-`reason` wire. When the turn was refused at admission (`status == Rejected`),
    /// this names the FIRST failing gate; on an admitted turn it is `Some(Admitted)`.
    pub reason: Option<AdmissionReason>,
    pub divergence_note: Option<String>,
}

impl ShadowVerdict {
    /// Whether the prologue (fee/nonce) was committed but the BODY FAILED — the fee was charged
    /// as anti-spam but the turn is REJECTED (must NOT be treated as accepted).
    pub fn prologue_only(&self) -> bool {
        self.status == Some(TurnStatus::PrologueCommittedBodyFailed)
    }
    /// Whether the body genuinely committed (the turn is ACCEPTED).
    pub fn body_committed(&self) -> bool {
        // Fall back to `committed` for the legacy no-`status` wire.
        match self.status {
            Some(s) => s == TurnStatus::BodyCommitted,
            None => self.committed,
        }
    }
    /// The human-readable refusal reason, if the turn was rejected at admission and the wire
    /// carried a (non-`Admitted`) reason. `None` for an admitted turn, a body-rollback (whose
    /// "why" is the body's, not admission's), or a legacy no-`reason` wire.
    pub fn admission_refusal(&self) -> Option<AdmissionReason> {
        match self.reason {
            Some(r) if !r.is_admitted() => Some(r),
            _ => None,
        }
    }
}

/// Whether the Lean static archive was linked and runtime init succeeded.
pub fn lean_available() -> bool {
    lean_init_once().is_ok()
}

/// Marshal a wire string through `dregg_exec_full_forest_auth_str` and return the raw
/// output wire. Requires `lean_available()`.
pub fn shadow_exec_full_forest_auth(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    lean_forest_auth(wire)
}

/// Handler-cutover shadow path — admission ∘ `execHandlerTurn` on the same wire.
///
/// Available only when the linked archive exports `dregg_exec_handler_turn`
/// (cfg `dregg_handler_present`, set by build.rs). The forest-auth gate
/// ([`shadow_exec_full_forest_auth`]) is the load-bearing path and is always present.
pub fn shadow_exec_handler_turn(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    lean_handler_turn(wire)
}

/// Whether the linked archive exports the verified finality-gate
/// (`dregg_blocklace_finalize`). When false, the node cannot Lean-gate finality and falls back to
/// the un-gated path. Distinct from [`lean_available`] (which is about the executor exports): a
/// stale archive can have the executor but lack the finality gate.
pub fn finality_gate_available() -> bool {
    ffi::finality_gate_present() && lean_init_once().is_ok()
}

/// Run the verified PER-ASSET kernel step `@[export] dregg_record_kernel_step` (the PROVED
/// `Exec.recKExec`) over a single-column cell state.
///
/// The input/output wire is the canonical JSON the export reads:
///   * in:  `{"cells":[[ID,{"rec":[["balance",{"int":N}],…]}],…],"actor":N,"src":N,"dst":N,"amt":N}`
///   * out: `{"cells":CELLS,"ok":B}`
///
/// This is the verified executor the intent crate's `verified_settle` routes each ring leg
/// through, ONE call per leg over that leg's asset-projected column (`Dregg2.Intent.RingFFI`'s
/// `projAsset`). By the Lean keystone `ffi_export_realises_settleRing_leg`, the export's `ok` bit
/// and the post-state `balance` column ARE the verified per-asset executor's, so folding the legs
/// through this entry computes EXACTLY `settleRing` — not a Rust mirror.
///
/// Requires [`lean_available`]; returns `Err` if the archive was not linked.
pub fn shadow_record_kernel_step(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    lean_record_kernel_step(wire)
}

/// Verified FINALITY GATE — run the verified `BlocklaceFinality.tauOrder` rule over a wire-encoded
/// `(wavelength, participants, lace)` and return the verified finalized `(creator, seq)` order
/// (`"F=<c>:<s>,..."`) or `"ERR"` (fail-closed on a malformed wire).
///
/// The node calls this at the live commit point: it computes finality FROM the verified rule and
/// admits a turn to the executor ONLY when the verified rule finalizes it. The wire grammar mirrors
/// `Dregg2.Distributed.FinalityGate.encodeLaceWire` byte-for-byte (`finality_gate` module).
pub fn shadow_blocklace_finalize(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    lean_blocklace_finalize(wire)
}

/// Whether the linked archive exports the verified flow-refinement decision gate
/// (`dregg_decide_refines`, the C-ABI entry over the PROVED `decideRefines`). When false, the deploy
/// gate (`dregg-deploy::refine`) falls back to its in-process σ-free mirror. Distinct from
/// [`lean_available`] (the executor exports): a stale archive can have the executor but lack this gate.
pub fn decide_refines_gate_available() -> bool {
    ffi::decide_refines_present() && lean_init_once().is_ok()
}

/// Run the verified FLOW-REFINEMENT DECISION `@[export] dregg_decide_refines` (the PROVED
/// `Dregg2.Deos.FlowRefine.decideRefines`, sound+complete for the online-simulation refinement order
/// `≤ᶠ` per `decideRefines_iff`) over a wire-encoded pair of σ-free `Proc`s.
///
/// The input/output wire is the canonical grammar the export reads:
///   * in:  `"A=<preorder-tokens>;B=<preorder-tokens>"` (each `Proc` as a space-separated preorder
///     token stream: `d` done · `e<n>` emit ℓ · `c` ch(2) · `s` seqp(2)).
///   * out: `"1"` (A ≤ᶠ B) · `"0"` (A ⋠ B) · `"ERR"` (fail-closed on a malformed wire).
///
/// `dregg-deploy/src/refine.rs` routes its safe-upgrade / intent-conformance decision through this
/// entry when [`decide_refines_gate_available`], so the deploy gate runs the verified procedure
/// rather than a Rust mirror of it. Requires the archive to export the gate; returns `Err` otherwise.
pub fn shadow_decide_refines(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    lean_decide_refines(wire)
}

/// Whether the linked archive exports the extracted, Lean-verified ML-DSA verify core
/// (`dregg_fips204_verify`, the C-ABI entry over `Dregg2.Crypto.Fips204Verify.verifyFFI` =
/// `Fips204Spec.verifyB` at the deployed ML-DSA-65 parameters). When false, a caller must fall back to
/// the `fips204` crate verify. Distinct from [`lean_available`]: a stale archive can lack this export.
pub fn fips204_verify_core_available() -> bool {
    ffi::fips204_verify_present() && lean_init_once().is_ok()
}

/// Run the VERIFIED, extracted ML-DSA verify core `@[export] dregg_fips204_verify` (the executable
/// `Dregg2.Crypto.Fips204Verify.verifyCore`, proved equal to the `Fips204Spec.verifyB` predicate and to
/// discharge `DreggPqRefinement.Fips204Correct` for the verify direction). This runs the SECURITY-CRITICAL
/// verify as a Lean-verified object (leanc-native) — a forged signature REJECTS.
///
/// Wire grammar the export reads:
///   * in:  `"thi μ c̃ z h"` (five decimal ints — the deployed-parameter public high part, message,
///     challenge digest, response, hint).
///   * out: `"1"` (accept) · `"0"` (reject; also the fail-closed answer for a malformed wire).
///
/// `dregg-pq` routes its ML-DSA verify through this entry when [`fips204_verify_core_available`], so the
/// verify runs the verified Lean core rather than a trusted primitive. Returns `Err` if the archive lacks
/// the export.
pub fn shadow_fips204_verify(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi::lean_fips204_verify(wire)
}

/// Whether the linked archive exports the extracted, Lean-verified REAL, FULL-BYTE ML-DSA verify core
/// (`dregg_fips204_verify_real`, BRICK 8 — the C-ABI entry over `Dregg2.Crypto.Fips204Verify.verifyRealFFI`
/// = the FULL-DIMENSION `MlDsaVerifyReal.verifyCore` over the real 1952/3309-byte key/signature). When
/// false, a caller must fall back to the `fips204` crate verify. Distinct from [`lean_available`]: a stale
/// archive can lack this export.
pub fn fips204_verify_real_core_available() -> bool {
    ffi::fips204_verify_real_present() && lean_init_once().is_ok()
}

/// Run the VERIFIED, extracted REAL, FULL-BYTE ML-DSA verify core `@[export] dregg_fips204_verify_real`
/// (the executable `Dregg2.Crypto.Fips204Verify.verifyRealFFI` over `MlDsaVerifyReal.verifyCore`). This
/// runs the SECURITY-CRITICAL verify of a REAL ML-DSA-65 key + signature as a Lean-verified object
/// (leanc-native) — a forged/tampered signature REJECTS, PROVED by `verify_accepts_real` /
/// `verify_rejects_tampered`.
///
/// Wire grammar the export reads:
///   * in:  `"hex(pk) hex(msg) hex(ctx) hex(sig)"` (four space-separated lowercase-hex fields; an empty
///     field, e.g. `ctx = ε`, is the empty token between two spaces).
///   * out: `"1"` (accept) · `"0"` (reject; also the fail-closed answer for a malformed wire).
///
/// `dregg-pq::ml_dsa_verify` routes its verify through this entry (installed via
/// `dregg_pq::install_lean_verify_core_real`), so the deployed verify runs the verified Lean core over the
/// real bytes rather than the trusted `fips204` primitive. Returns `Err` if the archive lacks the export.
pub fn shadow_fips204_verify_real(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi::lean_fips204_verify_real(wire)
}

/// Whether the linked archive exports the extracted, Lean-verified ML-DSA sign core
/// (`dregg_fips204_sign`, the C-ABI entry over `Dregg2.Crypto.Fips204Verify.signFFI` = the extracted
/// `signCore`, the Fiat–Shamir-with-aborts signer at the deployed ML-DSA-65 parameters). When false, a
/// caller must fall back to the `fips204` crate sign. Distinct from [`lean_available`]: a stale archive
/// can lack this export.
pub fn fips204_sign_core_available() -> bool {
    ffi::fips204_sign_present() && lean_init_once().is_ok()
}

/// Run the VERIFIED, extracted ML-DSA sign core `@[export] dregg_fips204_sign` (the executable
/// `Dregg2.Crypto.Fips204Verify.signCore`, proved to agree with the spec `Fips204Spec.MlDsaParams.sign`
/// and — together with `verifyCore` — to discharge `DreggPqRefinement.Fips204Correct` FULLY). This runs
/// the SIGNING direction as a Lean-verified object (leanc-native).
///
/// Wire grammar the export reads:
///   * in:  `"s1 s2 t0 μ y"` (five decimal ints — the deployed-parameter secret `(s₁,s₂,t₀)`, message,
///     and the sampled randomness/mask `y`).
///   * out: `"c̃ z h"` (an accepted signature — three decimal ints) · `"REJECT"` (a rejected sample or a
///     malformed wire; the caller resamples `y`, the Dilithium rejection loop).
///
/// `dregg-pq` routes its ML-DSA sign path through this entry when [`fips204_sign_core_available`], so the
/// signing runs the verified Lean core rather than a trusted primitive. Returns `Err` if the archive
/// lacks the export.
pub fn shadow_fips204_sign(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi::lean_fips204_sign(wire)
}

/// Whether the linked archive exports the extracted, Lean-verified ML-KEM (FIPS 203) encaps core
/// (`dregg_fips203_encaps`, the C-ABI entry over `Dregg2.Crypto.Fips203Kem.encapsFFI`). When false, a
/// caller must fall back to the `ml-kem` crate encaps. Distinct from [`lean_available`]: a stale archive
/// can lack this export.
pub fn fips203_encaps_core_available() -> bool {
    ffi::fips203_encaps_present() && lean_init_once().is_ok()
}

/// Run the VERIFIED, extracted ML-KEM encaps core `@[export] dregg_fips203_encaps` (the executable
/// `Dregg2.Crypto.Fips203Kem.encapsCore`, proved equal to `MlKemIndCca.foEncaps` and — with the decaps
/// core — to discharge `DreggKemRefinement.Fips203Correct`).
///
/// Wire grammar the export reads:
///   * in:  `"A t m"` (three decimal ints — the deployed-parameter public key `(A,t)` and message bit `m`).
///   * out: `"u v K"` (the ciphertext `(u,v)` and the encapsulated shared secret `K = H(m)`);
///     `"ERR"` for a malformed wire.
///
/// `dregg-pq` routes its ML-KEM encaps through this entry when [`fips203_encaps_core_available`]. Returns
/// `Err` if the archive lacks the export.
pub fn shadow_fips203_encaps(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi::lean_fips203_encaps(wire)
}

/// Whether the linked archive exports the extracted, Lean-verified ML-KEM (FIPS 203) decaps core
/// (`dregg_fips203_decaps`, the C-ABI entry over `Dregg2.Crypto.Fips203Kem.decapsFFI`). When false, a
/// caller must fall back to the `ml-kem` crate decaps. Distinct from [`lean_available`]: a stale archive
/// can lack this export.
pub fn fips203_decaps_core_available() -> bool {
    ffi::fips203_decaps_present() && lean_init_once().is_ok()
}

/// Run the VERIFIED, extracted ML-KEM decaps core `@[export] dregg_fips203_decaps` (the executable
/// `Dregg2.Crypto.Fips203Kem.decapsCore`, proved equal to `MlKemIndCca.foDecaps` — the re-encryption
/// check + implicit reject). This runs the SECURITY-CRITICAL decaps as a Lean-verified object: a
/// tampered ciphertext implicit-rejects to a DIFFERENT (message-independent) secret, it does not leak.
///
/// Wire grammar the export reads:
///   * in:  `"A t s z u v"` (six decimal ints — the encapsulation key `(A,t)`, secret `s`, implicit-reject
///     seed `z`, ciphertext `(u,v)`).
///   * out: the recovered shared secret `K` as a decimal string (`H(m′)` on a matching re-encryption, else
///     the implicit-reject secret `J(z‖c)`); `"ERR"` for a malformed wire.
///
/// `dregg-pq` routes its ML-KEM decaps through this entry when [`fips203_decaps_core_available`]. Returns
/// `Err` if the archive lacks the export.
pub fn shadow_fips203_decaps(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi::lean_fips203_decaps(wire)
}

/// Parse a shadow output wire into a [`ShadowVerdict`], surfacing marshal/parse errors.
pub fn decode_shadow_verdict(output: &str) -> Result<ShadowVerdict, String> {
    match marshal::unmarshal_result(output) {
        Ok(r) => Ok(ShadowVerdict {
            // `committed` is the body-committed bit (status:2). The Lean export's `ok` already
            // narrows to BodyCommitted, but we recompute from `status` when present so a
            // prologue-only result (status:1) is NEVER reported as committed.
            committed: match r.status {
                Some(s) => s == TurnStatus::BodyCommitted,
                None => r.committed,
            },
            loglen: r.loglen,
            status: r.status,
            reason: r.reason,
            divergence_note: None,
        }),
        Err(e) => Err(e.to_string()),
    }
}

/// The verified Lean executor's verdict PAIRED WITH the full post-state it produced.
///
/// THE SWAP (authority inversion): `decode_shadow_verdict` keeps only the {committed, loglen,
/// status} bits and THROWS AWAY the `state` the verified executor produced — which is exactly the
/// gap that forces the legacy Rust `TurnExecutor` to remain the state PRODUCER. This decoder keeps
/// the post-state `WireState` so a caller can reconstitute the authoritative ledger from the
/// VERIFIED executor's output (see `dregg_turn::lean_apply::wire_state_to_ledger`).
///
/// `decode_shadow_verdict` is left intact (veto-only callers are unaffected); this is the additive
/// state-producing path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShadowState {
    /// The veto-shaped verdict bits (same as [`decode_shadow_verdict`]).
    pub verdict: ShadowVerdict,
    /// The FULL post-state the verified executor committed (on `committed`/rollback the echoed
    /// pre-state). This is the state-producer payload the swap installs as authoritative.
    pub state: WireState,
}

/// Parse a shadow output wire into a [`ShadowState`] — the verdict bits AND the produced
/// post-state. This is the state-PRODUCING decode (THE SWAP), as opposed to the veto-only
/// [`decode_shadow_verdict`] which discards `.state`.
pub fn decode_shadow_state(output: &str) -> Result<ShadowState, String> {
    match marshal::unmarshal_result(output) {
        Ok(r) => {
            let committed = match r.status {
                Some(s) => s == TurnStatus::BodyCommitted,
                None => r.committed,
            };
            Ok(ShadowState {
                verdict: ShadowVerdict {
                    committed,
                    loglen: r.loglen,
                    status: r.status,
                    reason: r.reason,
                    divergence_note: None,
                },
                state: r.state,
            })
        }
        Err(e) => Err(e.to_string()),
    }
}

// =============================================================================
// Lean FFI (present only when libdregg_lean.a was linked at build time)
// =============================================================================

#[cfg(lean_lib_present)]
mod ffi {
    use std::ffi::CString;
    use std::os::raw::c_char;
    use std::sync::OnceLock;

    extern "C" {
        fn dregg_ffi_init() -> i32;
        /// The SINGLE-THREADED / libuv-thread-free init (the pg-Tier-D-embeddable
        /// path — see `docs/EMBEDDABLE-LEAN-RUNTIME.md` + `src/lean_init_st.cpp`).
        /// Runs the libuv-free initializer chain so NO libuv event-loop thread is
        /// spawned. Same once-per-process contract as `dregg_ffi_init`.
        fn dregg_ffi_init_st() -> i32;
        fn dregg_exec_full_forest_auth_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        fn dregg_record_kernel_step_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_handler_present)]
        fn dregg_exec_handler_turn_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_finalize_gate_present)]
        fn dregg_blocklace_finalize_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_decide_refines_present)]
        fn dregg_decide_refines_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_storage_content_root_present)]
        fn dregg_storage_content_root_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_fips204_verify_present)]
        fn dregg_fips204_verify_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_fips204_verify_real_present)]
        fn dregg_fips204_verify_real_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_fips204_sign_present)]
        fn dregg_fips204_sign_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_fips203_encaps_present)]
        fn dregg_fips203_encaps_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_fips203_decaps_present)]
        fn dregg_fips203_decaps_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
    }

    static INIT: OnceLock<Result<(), String>> = OnceLock::new();
    static INIT_ST: OnceLock<Result<(), String>> = OnceLock::new();

    pub fn lean_init_once() -> Result<(), String> {
        INIT.get_or_init(|| {
            let rc = unsafe { dregg_ffi_init() };
            if rc == 0 {
                Ok(())
            } else {
                Err(format!("dregg_ffi_init failed (rc={rc})"))
            }
        })
        .clone()
    }

    /// Single-threaded / libuv-thread-free init (the pg-Tier-D-embeddable path).
    /// Drives `dregg_ffi_init_st`, which never starts the libuv event-loop thread.
    /// A process must pick ONE init flavor: the Lean module initializers are
    /// once-per-process, so a caller using the single-threaded path must NOT also
    /// call [`lean_init_once`] (that would run `lean_initialize_runtime_module` and
    /// spawn the very thread this path omits, and re-init the modules). These are
    /// separate `OnceLock`s so a test can drive the ST path in isolation.
    pub fn lean_init_st_once() -> Result<(), String> {
        INIT_ST
            .get_or_init(|| {
                let rc = unsafe { dregg_ffi_init_st() };
                if rc == 0 {
                    Ok(())
                } else {
                    Err(format!("dregg_ffi_init_st failed (rc={rc})"))
                }
            })
            .clone()
    }

    fn lean_string_bridge(
        wire: &str,
        f: unsafe extern "C" fn(*const c_char, *mut c_char, usize) -> usize,
        err_label: &str,
    ) -> Result<String, String> {
        let c_in = CString::new(wire).map_err(|e| format!("wire has interior NUL: {e}"))?;
        let mut cap = wire.len() * 2 + 1024;
        loop {
            let mut buf = vec![0u8; cap];
            let full = unsafe { f(c_in.as_ptr(), buf.as_mut_ptr() as *mut c_char, cap) };
            if full == usize::MAX {
                return Err(format!("{err_label}: unusable output buffer"));
            }
            if full < cap {
                let nul = buf.iter().position(|&b| b == 0).unwrap_or(full);
                return String::from_utf8(buf[..nul].to_vec())
                    .map_err(|e| format!("result not UTF-8: {e}"));
            }
            cap = full + 1;
        }
    }

    pub fn lean_forest_auth(wire: &str) -> Result<String, String> {
        lean_string_bridge(
            wire,
            dregg_exec_full_forest_auth_str,
            "dregg_exec_full_forest_auth_str",
        )
    }

    pub fn lean_record_kernel_step(wire: &str) -> Result<String, String> {
        lean_string_bridge(
            wire,
            dregg_record_kernel_step_str,
            "dregg_record_kernel_step_str",
        )
    }

    #[cfg(dregg_handler_present)]
    pub fn lean_handler_turn(wire: &str) -> Result<String, String> {
        lean_string_bridge(
            wire,
            dregg_exec_handler_turn_str,
            "dregg_exec_handler_turn_str",
        )
    }

    #[cfg(not(dregg_handler_present))]
    pub fn lean_handler_turn(_wire: &str) -> Result<String, String> {
        Err("dregg_exec_handler_turn not exported by the linked archive (rebuild to enable)".into())
    }

    #[cfg(dregg_finalize_gate_present)]
    pub fn finality_gate_present() -> bool {
        true
    }

    #[cfg(not(dregg_finalize_gate_present))]
    pub fn finality_gate_present() -> bool {
        false
    }

    #[cfg(dregg_finalize_gate_present)]
    pub fn lean_blocklace_finalize(wire: &str) -> Result<String, String> {
        lean_string_bridge(
            wire,
            dregg_blocklace_finalize_str,
            "dregg_blocklace_finalize_str",
        )
    }

    #[cfg(not(dregg_finalize_gate_present))]
    pub fn lean_blocklace_finalize(_wire: &str) -> Result<String, String> {
        Err(
            "dregg_blocklace_finalize not exported by the linked archive (rebuild to enable)"
                .into(),
        )
    }

    #[cfg(dregg_decide_refines_present)]
    pub fn decide_refines_present() -> bool {
        true
    }

    #[cfg(not(dregg_decide_refines_present))]
    pub fn decide_refines_present() -> bool {
        false
    }

    #[cfg(dregg_decide_refines_present)]
    pub fn lean_decide_refines(wire: &str) -> Result<String, String> {
        lean_string_bridge(wire, dregg_decide_refines_str, "dregg_decide_refines_str")
    }

    #[cfg(not(dregg_decide_refines_present))]
    pub fn lean_decide_refines(_wire: &str) -> Result<String, String> {
        Err("dregg_decide_refines not exported by the linked archive (rebuild to enable)".into())
    }

    /// STORAGE-IN-LEAN EXTRACTION — run the VERIFIED Lean content-root over the deployed Poseidon2.
    /// Input: space-separated object int-triples; output: the content root as a decimal string.
    #[cfg(dregg_storage_content_root_present)]
    pub fn lean_storage_content_root(wire: &str) -> Result<String, String> {
        lean_string_bridge(
            wire,
            dregg_storage_content_root_str,
            "dregg_storage_content_root_str",
        )
    }

    /// FIPS-204-VERIFY EXTRACTION — run the VERIFIED Lean ML-DSA verify core (leanc-native).
    /// Input: `"thi μ c̃ z h"` (five decimal ints); output: `"1"` (accept) / `"0"` (reject). This is
    /// the SECURITY-CRITICAL verify direction as a Lean-verified object: the extracted `verifyCore`
    /// (= `Fips204Spec.verifyB` at the deployed ML-DSA-65 parameters), proved to reject forgeries.
    #[cfg(dregg_fips204_verify_present)]
    pub fn lean_fips204_verify(wire: &str) -> Result<String, String> {
        lean_string_bridge(wire, dregg_fips204_verify_str, "dregg_fips204_verify_str")
    }

    #[cfg(not(dregg_fips204_verify_present))]
    pub fn lean_fips204_verify(_wire: &str) -> Result<String, String> {
        Err("dregg_fips204_verify not exported by the linked archive (rebuild to enable)".into())
    }

    /// `true` iff the linked archive carries the extracted ML-DSA verify core.
    #[cfg(dregg_fips204_verify_present)]
    pub fn fips204_verify_present() -> bool {
        true
    }

    #[cfg(not(dregg_fips204_verify_present))]
    pub fn fips204_verify_present() -> bool {
        false
    }

    /// FIPS-204-VERIFY-REAL extraction (BRICK 8) — run the VERIFIED Lean ML-DSA verify core over the REAL,
    /// FULL-BYTE key/signature (leanc-native). Input: `"hex(pk) hex(msg) hex(ctx) hex(sig)"` (four
    /// space-separated lowercase-hex fields); output: `"1"` (accept) / `"0"` (reject, and the fail-closed
    /// answer for a malformed wire). This is the FULL-DIMENSION `MlDsaVerifyReal.verifyCore` (n=256 ring /
    /// NTT / SampleInBall / ExpandA / real 1952/3309-byte codec, proved to accept a genuine crate
    /// signature and reject tampers) — the object `dregg-pq::ml_dsa_verify` routes through to take the
    /// `fips204` crate OUT of the verify TCB.
    #[cfg(dregg_fips204_verify_real_present)]
    pub fn lean_fips204_verify_real(wire: &str) -> Result<String, String> {
        lean_string_bridge(
            wire,
            dregg_fips204_verify_real_str,
            "dregg_fips204_verify_real_str",
        )
    }

    #[cfg(not(dregg_fips204_verify_real_present))]
    pub fn lean_fips204_verify_real(_wire: &str) -> Result<String, String> {
        Err(
            "dregg_fips204_verify_real not exported by the linked archive (rebuild to enable)"
                .into(),
        )
    }

    /// `true` iff the linked archive carries the extracted REAL, full-byte ML-DSA verify core.
    #[cfg(dregg_fips204_verify_real_present)]
    pub fn fips204_verify_real_present() -> bool {
        true
    }

    #[cfg(not(dregg_fips204_verify_real_present))]
    pub fn fips204_verify_real_present() -> bool {
        false
    }

    /// FIPS-204-SIGN EXTRACTION — run the VERIFIED Lean ML-DSA sign core (leanc-native).
    /// Input: `"s1 s2 t0 μ y"` (secret + message + the sampled randomness/mask); output: the signature
    /// wire `"c̃ z h"` (an accepted iteration) or `"REJECT"` (a rejected sample / malformed wire, retry).
    /// This is the SIGNING direction as a Lean-verified object: the extracted `signCore` (the
    /// Fiat–Shamir-with-aborts signer at the deployed ML-DSA-65 parameters), proved to round-trip
    /// through `verifyCore`.
    #[cfg(dregg_fips204_sign_present)]
    pub fn lean_fips204_sign(wire: &str) -> Result<String, String> {
        lean_string_bridge(wire, dregg_fips204_sign_str, "dregg_fips204_sign_str")
    }

    #[cfg(not(dregg_fips204_sign_present))]
    pub fn lean_fips204_sign(_wire: &str) -> Result<String, String> {
        Err("dregg_fips204_sign not exported by the linked archive (rebuild to enable)".into())
    }

    /// `true` iff the linked archive carries the extracted ML-DSA sign core.
    #[cfg(dregg_fips204_sign_present)]
    pub fn fips204_sign_present() -> bool {
        true
    }

    #[cfg(not(dregg_fips204_sign_present))]
    pub fn fips204_sign_present() -> bool {
        false
    }

    /// FIPS-203-ENCAPS EXTRACTION — run the VERIFIED Lean ML-KEM encaps core (leanc-native).
    /// Input: `"A t m"` (three decimal ints); output: `"u v K"` (ciphertext + encapsulated secret).
    #[cfg(dregg_fips203_encaps_present)]
    pub fn lean_fips203_encaps(wire: &str) -> Result<String, String> {
        lean_string_bridge(wire, dregg_fips203_encaps_str, "dregg_fips203_encaps_str")
    }

    #[cfg(not(dregg_fips203_encaps_present))]
    pub fn lean_fips203_encaps(_wire: &str) -> Result<String, String> {
        Err("dregg_fips203_encaps not exported by the linked archive (rebuild to enable)".into())
    }

    /// `true` iff the linked archive carries the extracted ML-KEM encaps core.
    #[cfg(dregg_fips203_encaps_present)]
    pub fn fips203_encaps_present() -> bool {
        true
    }

    #[cfg(not(dregg_fips203_encaps_present))]
    pub fn fips203_encaps_present() -> bool {
        false
    }

    /// FIPS-203-DECAPS EXTRACTION — run the VERIFIED Lean ML-KEM decaps core (leanc-native).
    /// Input: `"A t s z u v"`; output: the recovered shared secret K (implicit reject folded in;
    /// "ERR" only on a malformed wire). The SECURITY-CRITICAL direction as a Lean-verified object.
    #[cfg(dregg_fips203_decaps_present)]
    pub fn lean_fips203_decaps(wire: &str) -> Result<String, String> {
        lean_string_bridge(wire, dregg_fips203_decaps_str, "dregg_fips203_decaps_str")
    }

    #[cfg(not(dregg_fips203_decaps_present))]
    pub fn lean_fips203_decaps(_wire: &str) -> Result<String, String> {
        Err("dregg_fips203_decaps not exported by the linked archive (rebuild to enable)".into())
    }

    /// `true` iff the linked archive carries the extracted ML-KEM decaps core.
    #[cfg(dregg_fips203_decaps_present)]
    pub fn fips203_decaps_present() -> bool {
        true
    }

    #[cfg(not(dregg_fips203_decaps_present))]
    pub fn fips203_decaps_present() -> bool {
        false
    }

    #[cfg(all(test, dregg_fips204_verify_present))]
    mod fips204_verify_extraction {
        use super::*;
        /// THE ROUND-TRIP: the verified Lean ML-DSA verify core runs (leanc-compiled native). An honest
        /// deployed-parameter signature ACCEPTS ("1"); a tampered `c̃`/`z` and an out-of-range `z` REJECT
        /// ("0") — the extracted `verifyCore` is the real gate, not `fun _ => true`.
        #[test]
        fn verified_ml_dsa_verify_runs_in_lean() {
            lean_init_once().expect("init the Lean runtime");
            // Honest: thi=3, μ=7, sig=(c̃=7, z=45, h=0) — the `realParams` round-trip.
            assert_eq!(lean_fips204_verify("3 7 7 45 0").expect("round-trip"), "1");
            // Tampered c̃ (breaks the challenge fixed-point) REJECTS.
            assert_eq!(lean_fips204_verify("3 7 8 45 0").unwrap(), "0");
            // Out-of-range z (fails ‖z‖ < γ₁−β) REJECTS.
            assert_eq!(lean_fips204_verify("3 7 7 100000000 0").unwrap(), "0");
            // Malformed wire fails CLOSED.
            assert_eq!(lean_fips204_verify("garbage").unwrap(), "0");
        }
    }

    #[cfg(all(test, dregg_fips204_sign_present))]
    mod fips204_sign_extraction {
        use super::*;
        /// THE SIGN → VERIFY ROUND-TRIP: the verified Lean ML-DSA SIGN core runs (leanc-compiled native)
        /// and its accepted output VERIFIES through the extracted verify core — the full `Fips204Correct`
        /// round-trip across two extracted objects. The honest secret `(5,1,3)` with mask `y=40`, message
        /// `μ=7` SIGNS to `"7 45 0"`, which verifies as `"1"` under `thi = 5+1−3 = 3`. A bad-mask sample
        /// (`lowGap` fails) and an out-of-norm response are honestly `"REJECT"` (retry, not faked); a
        /// malformed wire fails closed.
        #[test]
        fn verified_ml_dsa_sign_verify_roundtrips_in_lean() {
            lean_init_once().expect("init the Lean runtime");
            // Honest accepted iteration ⇒ the signature wire.
            let sig = lean_fips204_sign("5 1 3 7 40").expect("sign round-trip");
            assert_eq!(sig, "7 45 0", "honest sign emits the signature wire");
            // ROUND-TRIP: the accepted signature, prefixed `thi μ`, VERIFIES via the extracted verify core.
            assert_eq!(
                lean_fips204_verify(&format!("3 7 {sig}")).expect("verify"),
                "1",
                "the extracted sign output round-trips through verifyCore"
            );
            // Rejected samples are honest "REJECT" (retry): bad mask (lowGap fails) / out-of-norm z.
            assert_eq!(lean_fips204_sign("5 1 3 7 261888").unwrap(), "REJECT");
            assert_eq!(lean_fips204_sign("5 1 3 7 1000000").unwrap(), "REJECT");
            // Malformed wire fails CLOSED.
            assert_eq!(lean_fips204_sign("garbage").unwrap(), "REJECT");
        }
    }

    #[cfg(all(test, dregg_fips204_verify_real_present))]
    mod fips204_verify_real_extraction {
        use super::*;
        /// BRICK 8 smoke test: the REAL, full-byte ML-DSA verify export links and runs (leanc-native), and
        /// a malformed byte wire fails CLOSED ("0"). The real-vector accept/reject is exercised end-to-end
        /// with genuine `fips204` crate keys/signatures in `dregg-pq`'s `mldsa_lean_verify` gate (which has
        /// the crate as a dev-dep); here we only confirm the bridge is wired and fail-closed on garbage.
        #[test]
        fn verified_real_ml_dsa_verify_bridge_links_and_fails_closed() {
            lean_init_once().expect("init the Lean runtime");
            // Non-hex fields fail closed (parser rejects before verifyCore).
            assert_eq!(lean_fips204_verify_real("zz zz zz zz").unwrap(), "0");
            // Wrong field count fails closed (not exactly four space-separated fields).
            assert_eq!(lean_fips204_verify_real("00 00").unwrap(), "0");
            // Odd-length hex fails closed (decodeHexChars rejects an unpaired nibble).
            assert_eq!(lean_fips204_verify_real("0 0 0 0").unwrap(), "0");
        }
    }

    #[cfg(all(test, dregg_fips203_encaps_present, dregg_fips203_decaps_present))]
    mod fips203_kem_extraction {
        use super::*;
        /// THE ENCAPS → DECAPS ROUND-TRIP: the verified Lean ML-KEM cores run (leanc-compiled native).
        /// The honest deployed data `(A,t,s)=(1,2,1)`, message bit `m=1` ENCAPS to `"1 1667 3"` (ct=(1,1667),
        /// K=3); DECAPS of that ciphertext recovers `"3"` — the extracted encaps→decaps round trip that
        /// discharges `Fips203Correct`. A TAMPERED ciphertext implicit-rejects to a DIFFERENT
        /// (message-independent) secret (`"3536"` ≠ `"3"`) — the re-encryption check is the real gate,
        /// not `fun _ => K`. A malformed wire fails closed.
        #[test]
        fn verified_ml_kem_encaps_decaps_roundtrips_in_lean() {
            lean_init_once().expect("init the Lean runtime");
            // Honest encaps ⇒ the ciphertext + secret wire.
            let enc = lean_fips203_encaps("1 2 1").expect("encaps round-trip");
            assert_eq!(
                enc, "1 1667 3",
                "honest encaps emits the ciphertext + secret"
            );
            // ROUND-TRIP: decaps of the honest ciphertext recovers the encapsulated secret K=3.
            assert_eq!(
                lean_fips203_decaps("1 2 1 0 1 1667").expect("decaps"),
                "3",
                "the extracted encaps output round-trips through decapsCore"
            );
            // TAMPERED ciphertext: implicit reject to a DIFFERENT secret (the parties diverge).
            assert_eq!(
                lean_fips203_decaps("1 2 1 0 1 1767").unwrap(),
                "3536",
                "a tampered ciphertext implicit-rejects to a different secret"
            );
            assert_ne!(
                lean_fips203_decaps("1 2 1 0 1 1767").unwrap(),
                lean_fips203_decaps("1 2 1 0 1 1667").unwrap(),
                "tampering the ML-KEM ciphertext breaks key agreement"
            );
            // Malformed wires fail CLOSED.
            assert_eq!(lean_fips203_encaps("garbage").unwrap(), "ERR");
            assert_eq!(lean_fips203_decaps("garbage").unwrap(), "ERR");
        }
    }

    #[cfg(all(test, dregg_storage_content_root_present))]
    mod storage_extraction {
        use super::*;
        /// THE ROUND-TRIP: the verified Lean content-root logic runs (leanc-compiled native),
        /// calling the fast Rust Poseidon2 through `@[extern "dregg_poseidon2_2to1"]` — the real
        /// "Lean is the runtime" for storage, end to end.
        #[test]
        fn verified_content_root_runs_in_lean_calling_rust_poseidon2() {
            lean_init_once().expect("init the Lean runtime");
            let r1 = lean_storage_content_root("1 2 3").expect("round-trip");
            assert!(
                !r1.is_empty() && r1 != "0",
                "a real content root felt: {r1}"
            );
            assert_eq!(
                r1,
                lean_storage_content_root("1 2 3").unwrap(),
                "deterministic"
            );
            assert_ne!(
                r1,
                lean_storage_content_root("1 2 4").unwrap(),
                "the root binds the object set"
            );
        }
    }
}

#[cfg(not(lean_lib_present))]
mod ffi {
    pub fn lean_init_once() -> Result<(), String> {
        Err("libdregg_lean.a was not present at build time".into())
    }

    pub fn lean_init_st_once() -> Result<(), String> {
        Err("libdregg_lean.a was not present at build time".into())
    }

    pub fn lean_forest_auth(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    pub fn lean_record_kernel_step(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    pub fn lean_handler_turn(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    pub fn finality_gate_present() -> bool {
        false
    }

    pub fn lean_blocklace_finalize(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    pub fn decide_refines_present() -> bool {
        false
    }

    pub fn lean_decide_refines(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    pub fn fips204_verify_present() -> bool {
        false
    }

    pub fn lean_fips204_verify(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    /// `true` iff the linked archive carries the extracted REAL, full-byte ML-DSA verify
    /// core. Unlinked stub: the archive is absent, so the real core is never present.
    pub fn fips204_verify_real_present() -> bool {
        false
    }

    pub fn lean_fips204_verify_real(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    pub fn fips204_sign_present() -> bool {
        false
    }

    pub fn lean_fips204_sign(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    pub fn fips203_encaps_present() -> bool {
        false
    }

    pub fn lean_fips203_encaps(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    pub fn fips203_decaps_present() -> bool {
        false
    }

    pub fn lean_fips203_decaps(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }
}

fn lean_init_once() -> Result<(), String> {
    ffi::lean_init_once()
}

fn lean_init_st_once() -> Result<(), String> {
    ffi::lean_init_st_once()
}

fn ensure_lean_init() -> Result<(), String> {
    lean_init_once()
}

/// Initialize the Lean runtime in the **single-threaded / libuv-thread-free** mode
/// (the pg-Tier-D-embeddable path — see `docs/EMBEDDABLE-LEAN-RUNTIME.md`). Unlike
/// [`lean_available`], this init does NOT start the libuv event-loop thread, so the
/// runtime executes entirely on the caller's thread — the property a single-threaded
/// host (a postgres backend) requires. Returns `true` on a successful init.
///
/// A process must commit to ONE init flavor: do not mix this with [`lean_available`]
/// / [`shadow_exec_full_forest_auth`] (the default multi-thread path) in the same
/// process — the Lean module initializers run once per process.
pub fn init_single_threaded() -> bool {
    lean_init_st_once().is_ok()
}

/// Run the gated complete-turn executor (`execFullForestG`) after a **single-threaded**
/// init (no libuv event-loop thread). Semantically identical to
/// [`shadow_exec_full_forest_auth`]; the only difference is the runtime init flavor.
pub fn shadow_exec_full_forest_auth_single_threaded(wire: &str) -> Result<String, String> {
    lean_init_st_once()?;
    lean_forest_auth(wire)
}

fn lean_forest_auth(wire: &str) -> Result<String, String> {
    ffi::lean_forest_auth(wire)
}

fn lean_record_kernel_step(wire: &str) -> Result<String, String> {
    ffi::lean_record_kernel_step(wire)
}

fn lean_handler_turn(wire: &str) -> Result<String, String> {
    ffi::lean_handler_turn(wire)
}

fn lean_blocklace_finalize(wire: &str) -> Result<String, String> {
    ffi::lean_blocklace_finalize(wire)
}

fn lean_decide_refines(wire: &str) -> Result<String, String> {
    ffi::lean_decide_refines(wire)
}
