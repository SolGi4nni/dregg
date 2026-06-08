//! `distributed_ffi` — the FFI bridge onto the VERIFIED DISTRIBUTED exports (consensus + federation)
//! that live in `Dregg2.Distributed.*`, kept in a module DISTINCT from the executor-facing
//! `marshal.rs` / `lib.rs` plumbing.
//!
//! # What this is
//!
//! The executor exports (`dregg_exec_full_forest_auth`, `dregg_record_kernel_step`) and the finality
//! gate (`dregg_blocklace_finalize`) are wired in `lib.rs`. This module adds the FEDERATION-side
//! verified export:
//!
//!   * [`shadow_strand_admit`] — the VERIFIED hybrid stake-OR-vouch Sybil-admission gate
//!     (`Dregg2.Distributed.StrandAdmission.admitGate`, `@[export] dregg_strand_admit`). The
//!     federation calls it at the admission point to compute the F-4 verdict FROM the verified Lean
//!     rule itself; the Lean theorem `strand_admit_eq_admitted` proves the export's `"1"`/`"0"` IS
//!     the verified `admitted` predicate, so gating live admission on it gates it on the verified
//!     rule by construction. The Rust `AdmissionRegistry::admitted` stays as the DIFFERENTIAL sibling
//!     (Lean == Rust on the same registry), not the decider.
//!
//! # Wire grammar (mirrors `StrandAdmission.encodeAdmitWire` byte-for-byte)
//!
//! ```text
//! INPUT  := "N=" <vouch-threshold> ";m=" <min-bond>
//!           ";S=" <seed,seed,...>
//!           ";V=" <voucher:candidate,voucher:candidate,...>
//!           ";Bo=" <owner:amount,owner:amount,...>
//!           ";q=" <queried-strand>
//! OUTPUT := "1" (admitted) | "0" (not admitted) | "ERR" (malformed ⇒ fail-closed NOT admitted)
//! ```
//!
//! Strands/seeds/owners are the small `AuthorId` participant indices the caller interns (the same
//! interning the finality gate uses — the abstract `AuthorId` is a `Nat` in Lean, a `[u8;32]`
//! pubkey in the federation; the caller maps pubkey → index and back).
//!
//! # Availability + fail-safety
//!
//! [`strand_admit_available`] is true only when the linked archive exports `dregg_strand_admit`
//! (cfg `dregg_strand_admit_present`, set by build.rs) AND runtime init succeeded. When unavailable
//! (stale/marshal-only archive) the federation falls back to its Rust gate. A wire that round-trips
//! to `ERR` is fail-closed (the caller treats `ERR` / any non-`"1"` as NOT admitted).

use crate::{ensure_lean_init, lean_init_once};

/// Whether the linked archive exports the verified strand-admission gate (`dregg_strand_admit`).
/// When false, the federation cannot Lean-back its F-4 admission gate and falls back to the Rust
/// `AdmissionRegistry::admitted`. Distinct from `lean_available()` (executor exports) and
/// `finality_gate_available()` (the finality gate): a stale archive can have some exports but lack
/// this one.
pub fn strand_admit_available() -> bool {
    ffi::strand_admit_present() && lean_init_once().is_ok()
}

/// Run the VERIFIED strand-admission gate `@[export] dregg_strand_admit` (the PROVED
/// `StrandAdmission.admitted`) over a wire-encoded `(registry, strand)` and return the raw verdict
/// wire (`"1"` / `"0"` / `"ERR"`). Requires [`strand_admit_available`]; returns `Err` when the
/// archive did not export it.
pub fn shadow_strand_admit(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi::lean_strand_admit(wire)
}

/// Decode a verdict wire to a Boolean admission decision. `"1"` ⇒ admitted; ANYTHING ELSE
/// (`"0"`, `"ERR"`, a malformed reply) ⇒ NOT admitted (fail-closed). The verified Lean side emits
/// exactly `"1"`/`"0"`/`"ERR"`; the catch-all keeps the Rust side fail-closed regardless.
pub fn verdict_admits(verdict: &str) -> bool {
    verdict == "1"
}

/// The end-to-end verified admission query: encode is the caller's job (the federation builds the
/// wire from its interned registry); this runs the gate and decodes the verdict to a Boolean, FAILING
/// CLOSED (not admitted) on any FFI error or `ERR` sentinel. Returns `Ok(bool)` when the gate ran (the
/// bool is the verified verdict) and `Err` only when the archive lacks the export (so the caller can
/// fall back to the Rust gate, distinguishing "archive missing" from "rule says reject").
pub fn verified_admits(wire: &str) -> Result<bool, String> {
    let out = shadow_strand_admit(wire)?;
    Ok(verdict_admits(&out))
}

// =============================================================================
// dregg_tau_order — the RAW finalized TOTAL-ORDER export (consensus side)
// =============================================================================

/// Whether the linked archive exports the verified RAW total-order gate (`dregg_tau_order`). It is
/// co-located with `dregg_blocklace_finalize` in `Dregg2.Distributed.FinalityGate`, so it is present
/// exactly when the finality gate is — but probed independently so a future split cannot silently
/// route the node to a missing symbol. When false the caller falls back to the projection export
/// (`shadow_blocklace_finalize`) or the un-gated Rust `tau`.
pub fn tau_order_available() -> bool {
    ffi_tau::tau_order_present() && lean_init_once().is_ok()
}

/// Run the VERIFIED raw total-order gate `@[export] dregg_tau_order` (the PROVED
/// `BlocklaceFinality.tauOrder`, carried by `tau_order_export_eq`) over a wire-encoded
/// `(wavelength, participants, lace)` and return the raw output wire (`"T=<id>,<id>,..."` — the
/// verified finalized total order as the ordered BlockId list — or `"ERR"` fail-closed). Requires
/// [`tau_order_available`]; returns `Err` when the archive did not export it (so the caller can fall
/// back). Unlike [`crate::shadow_blocklace_finalize`] (which returns the `(creator, seq)` PROJECTION),
/// this returns the FULL ordered id list, order-faithful to `tauOrder`.
pub fn shadow_tau_order(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi_tau::lean_tau_order(wire)
}

/// Decode a `"T=<id>,<id>,..."` raw-order wire to the ordered `Vec<u64>` of finalized BlockIds. This
/// is the Rust inverse of the Lean `encodeOrderWire`; `decodeOrderWire` mirrors it (the round-trip is
/// `#guard`-witnessed Lean-side). Returns `None` on the `"ERR"` sentinel or any malformed body
/// (fail-closed — the caller finalizes nothing on a parse failure).
pub fn decode_tau_order(wire: &str) -> Option<Vec<u64>> {
    let body = wire.strip_prefix("T=")?;
    if body.is_empty() {
        return Some(Vec::new());
    }
    body.split(',').map(|p| p.parse::<u64>().ok()).collect()
}

/// The end-to-end verified total-order query: run the raw-order gate and decode it to the ordered
/// BlockId list, FAILING CLOSED on `ERR`/malformed (an empty order). Returns `Ok(Vec)` when the gate
/// ran and `Err` only when the archive lacks the export (so the caller can fall back to the Rust
/// `tau` / the projection gate).
pub fn verified_tau_order(wire: &str) -> Result<Vec<u64>, String> {
    let out = shadow_tau_order(wire)?;
    Ok(decode_tau_order(&out).unwrap_or_default())
}

// =============================================================================
// Lean FFI (present only when the archive exported `dregg_strand_admit`)
// =============================================================================

#[cfg(all(lean_lib_present, dregg_strand_admit_present))]
mod ffi {
    use std::ffi::CString;
    use std::os::raw::c_char;

    extern "C" {
        fn dregg_strand_admit_str(in_utf8: *const c_char, out: *mut c_char, out_cap: usize)
            -> usize;
    }

    pub fn strand_admit_present() -> bool {
        true
    }

    pub fn lean_strand_admit(wire: &str) -> Result<String, String> {
        let c_in = CString::new(wire).map_err(|e| format!("wire has interior NUL: {e}"))?;
        let mut cap = wire.len() * 2 + 256;
        loop {
            let mut buf = vec![0u8; cap];
            let full = unsafe {
                dregg_strand_admit_str(c_in.as_ptr(), buf.as_mut_ptr() as *mut c_char, cap)
            };
            if full == usize::MAX {
                return Err("dregg_strand_admit_str: unusable output buffer".into());
            }
            if full < cap {
                let nul = buf.iter().position(|&b| b == 0).unwrap_or(full);
                return String::from_utf8(buf[..nul].to_vec())
                    .map_err(|e| format!("result not UTF-8: {e}"));
            }
            cap = full + 1;
        }
    }
}

#[cfg(not(all(lean_lib_present, dregg_strand_admit_present)))]
mod ffi {
    pub fn strand_admit_present() -> bool {
        false
    }

    pub fn lean_strand_admit(_wire: &str) -> Result<String, String> {
        Err("dregg_strand_admit not exported by the linked archive (rebuild to enable)".into())
    }
}

// The raw total-order export (`dregg_tau_order`) is gated INDEPENDENTLY on the finality-gate cfg
// (`dregg_finalize_gate_present`) — it lives in the same Lean module as `dregg_blocklace_finalize`,
// so build.rs sets the same cfg for it. Kept as a SEPARATE ffi sub-module so the strand-admit and
// finality-gate exports can be present/absent independently.
#[cfg(all(lean_lib_present, dregg_finalize_gate_present))]
mod ffi_tau {
    use std::ffi::CString;
    use std::os::raw::c_char;

    extern "C" {
        fn dregg_tau_order_str(in_utf8: *const c_char, out: *mut c_char, out_cap: usize) -> usize;
    }

    pub fn tau_order_present() -> bool {
        true
    }

    pub fn lean_tau_order(wire: &str) -> Result<String, String> {
        let c_in = CString::new(wire).map_err(|e| format!("wire has interior NUL: {e}"))?;
        let mut cap = wire.len() * 2 + 256;
        loop {
            let mut buf = vec![0u8; cap];
            let full =
                unsafe { dregg_tau_order_str(c_in.as_ptr(), buf.as_mut_ptr() as *mut c_char, cap) };
            if full == usize::MAX {
                return Err("dregg_tau_order_str: unusable output buffer".into());
            }
            if full < cap {
                let nul = buf.iter().position(|&b| b == 0).unwrap_or(full);
                return String::from_utf8(buf[..nul].to_vec())
                    .map_err(|e| format!("result not UTF-8: {e}"));
            }
            cap = full + 1;
        }
    }
}

#[cfg(not(all(lean_lib_present, dregg_finalize_gate_present)))]
mod ffi_tau {
    pub fn tau_order_present() -> bool {
        false
    }

    pub fn lean_tau_order(_wire: &str) -> Result<String, String> {
        Err("dregg_tau_order not exported by the linked archive (rebuild to enable)".into())
    }
}

// =============================================================================
// dregg_captp_* / dregg_coord_* — the VERIFIED CapTP + COORDINATION decision exports
// (`Dregg2.Exec.DistributedExports`). The captp/coord runtime invokes these so it computes its
// verdict FROM the verified Lean rule itself (dreggrs Rust → differential sibling).
// =============================================================================

/// Whether the linked archive exports the verified CapTP+coord decision gates
/// (`dregg_captp_validate_handoff` and its five siblings — all in one module, present/absent
/// together). When false the captp/coord runtime cannot Lean-back its decisions and falls back to
/// the native Rust gates.
pub fn distributed_exports_available() -> bool {
    ffi_dist::distributed_exports_present() && lean_init_once().is_ok()
}

/// Run the VERIFIED §6 non-amplification gate `@[export] dregg_captp_validate_handoff` (the PROVED
/// `handoffNonAmplifyingC`, carried by `captp_validate_handoff_eq`) over a wire-encoded
/// `(heldPerm, grantedPerm, heldEff, grantedEff)` and return the raw verdict (`"1"` non-amplifying /
/// `"0"` amplifying / `"ERR"`). Requires [`distributed_exports_available`].
pub fn shadow_captp_validate_handoff(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi_dist::lean_captp_validate_handoff(wire)
}

/// The end-to-end verified handoff non-amplification query: run the gate and decode to a Boolean,
/// FAILING CLOSED (AMPLIFIES — reject) on any FFI error / `ERR` / `"0"`. Returns `Ok(true)` only when
/// the verified rule says the handoff is non-amplifying (granted ⊆ held); `Err` only when the archive
/// lacks the export (so the caller can fall back to the Rust gate, distinguishing "archive missing"
/// from "rule says amplifies").
pub fn verified_handoff_non_amplifying(wire: &str) -> Result<bool, String> {
    let out = shadow_captp_validate_handoff(wire)?;
    Ok(out == "1")
}

/// Run the VERIFIED GC session-refcount gate `@[export] dregg_captp_process_drop` (the PROVED
/// `CapTPGCConcrete.processDrop`, carried by `captp_process_drop_eq`) over a wire-encoded
/// `(holder-table, fed, session)` and return the raw verdict wire (`"S=<tag>;t=<postTotal>"` —
/// tag 0=stillHeld 1=canRevoke 2=invalid — or `"ERR"` fail-closed). Requires
/// [`distributed_exports_available`].
pub fn shadow_captp_process_drop(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi_dist::lean_captp_process_drop(wire)
}

/// Run the VERIFIED promise-pipelining resolve/break gate `@[export] dregg_captp_pipeline_resolve`
/// (the PROVED FIFO drain, carried by `captp_pipeline_resolve_eq`) over a wire-encoded
/// `(queue, event)` and return the raw verdict wire (`"D=<drained>;q=<postCount>"` or `"ERR"`).
/// Requires [`distributed_exports_available`].
pub fn shadow_captp_pipeline_resolve(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi_dist::lean_captp_pipeline_resolve(wire)
}

/// Run the VERIFIED 2PC coordinator gate `@[export] dregg_coord_2pc_decide` (the PROVED
/// `TwoPhaseCommit.evaluate`, carried by `coord_2pc_decide_eq`) over a wire-encoded
/// `(yes, no, n, threshold)` tally and return the raw decision tag (`"0"`=Commit `"1"`=Abort
/// `"2"`=Pending; malformed ⇒ `"2"` fail-safe). Requires [`distributed_exports_available`].
pub fn shadow_coord_2pc_decide(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi_dist::lean_coord_2pc_decide(wire)
}

/// The end-to-end verified 2PC decision: run the gate and decode the decision tag to a `Decision2pc`,
/// FAILING SAFE (Pending) on any FFI error / `ERR`. The verified `evaluate` never yields a conflicting
/// Commit+Abort (`evaluate_not_commit_and_abort`), so gating the coordinator on this is gating it on
/// the 2PC agreement safety by construction.
pub fn verified_2pc_decide(wire: &str) -> Result<Decision2pc, String> {
    let out = shadow_coord_2pc_decide(wire)?;
    Ok(match out.as_str() {
        "0" => Decision2pc::Commit,
        "1" => Decision2pc::Abort,
        _ => Decision2pc::Pending,
    })
}

/// The 2PC decision a verified verdict decodes to (mirrors `coord::atomic::Decision`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Decision2pc {
    Commit,
    Abort,
    Pending,
}

/// Run the VERIFIED causal-order gate `@[export] dregg_coord_causal_order` (the decidable
/// `CausalOrder` happened-before, carried by `coord_causal_order_eq`) over a wire-encoded
/// `(dag, a, b)` and return the raw verdict (`"1"` a-happened-before-b / `"0"` not; malformed ⇒
/// `"0"` fail-closed). Requires [`distributed_exports_available`].
pub fn shadow_coord_causal_order(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi_dist::lean_coord_causal_order(wire)
}

/// The end-to-end verified happened-before query: run the gate and decode to a Boolean, FAILING
/// CLOSED (no causal edge) on any FFI error / `ERR` / `"0"`.
pub fn verified_happened_before(wire: &str) -> Result<bool, String> {
    let out = shadow_coord_causal_order(wire)?;
    Ok(out == "1")
}

/// Run the VERIFIED shared-budget tau-resolution gate `@[export] dregg_coord_shared_budget` (the
/// PROVED `SharedBudgetDynamics.resolveOrdered`, carried by `coord_shared_budget_eq`) over a
/// wire-encoded `(balance, tau-ordered-amounts)` and return the raw verdict wire
/// (`"R=<verdicts>;b=<remaining>;a=<accepted>"` or `"ERR"`). Requires [`distributed_exports_available`].
pub fn shadow_coord_shared_budget(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi_dist::lean_coord_shared_budget(wire)
}

#[cfg(all(lean_lib_present, dregg_distributed_exports_present))]
mod ffi_dist {
    use std::ffi::CString;
    use std::os::raw::c_char;

    extern "C" {
        fn dregg_captp_validate_handoff_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        fn dregg_captp_process_drop_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        fn dregg_captp_pipeline_resolve_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        fn dregg_coord_2pc_decide_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        fn dregg_coord_causal_order_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        fn dregg_coord_shared_budget_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
    }

    pub fn distributed_exports_present() -> bool {
        true
    }

    /// Drive a `*_str` bridge over a wire string with the standard grow-on-truncation loop.
    fn run(
        f: unsafe extern "C" fn(*const c_char, *mut c_char, usize) -> usize,
        wire: &str,
        name: &str,
    ) -> Result<String, String> {
        let c_in = CString::new(wire).map_err(|e| format!("wire has interior NUL: {e}"))?;
        let mut cap = wire.len() * 2 + 256;
        loop {
            let mut buf = vec![0u8; cap];
            let full = unsafe { f(c_in.as_ptr(), buf.as_mut_ptr() as *mut c_char, cap) };
            if full == usize::MAX {
                return Err(format!("{name}: unusable output buffer"));
            }
            if full < cap {
                let nul = buf.iter().position(|&b| b == 0).unwrap_or(full);
                return String::from_utf8(buf[..nul].to_vec())
                    .map_err(|e| format!("result not UTF-8: {e}"));
            }
            cap = full + 1;
        }
    }

    pub fn lean_captp_validate_handoff(wire: &str) -> Result<String, String> {
        run(dregg_captp_validate_handoff_str, wire, "dregg_captp_validate_handoff_str")
    }
    pub fn lean_captp_process_drop(wire: &str) -> Result<String, String> {
        run(dregg_captp_process_drop_str, wire, "dregg_captp_process_drop_str")
    }
    pub fn lean_captp_pipeline_resolve(wire: &str) -> Result<String, String> {
        run(dregg_captp_pipeline_resolve_str, wire, "dregg_captp_pipeline_resolve_str")
    }
    pub fn lean_coord_2pc_decide(wire: &str) -> Result<String, String> {
        run(dregg_coord_2pc_decide_str, wire, "dregg_coord_2pc_decide_str")
    }
    pub fn lean_coord_causal_order(wire: &str) -> Result<String, String> {
        run(dregg_coord_causal_order_str, wire, "dregg_coord_causal_order_str")
    }
    pub fn lean_coord_shared_budget(wire: &str) -> Result<String, String> {
        run(dregg_coord_shared_budget_str, wire, "dregg_coord_shared_budget_str")
    }
}

#[cfg(not(all(lean_lib_present, dregg_distributed_exports_present)))]
mod ffi_dist {
    pub fn distributed_exports_present() -> bool {
        false
    }
    fn unavailable(name: &str) -> Result<String, String> {
        Err(format!("{name} not exported by the linked archive (rebuild to enable)"))
    }
    pub fn lean_captp_validate_handoff(_wire: &str) -> Result<String, String> {
        unavailable("dregg_captp_validate_handoff")
    }
    pub fn lean_captp_process_drop(_wire: &str) -> Result<String, String> {
        unavailable("dregg_captp_process_drop")
    }
    pub fn lean_captp_pipeline_resolve(_wire: &str) -> Result<String, String> {
        unavailable("dregg_captp_pipeline_resolve")
    }
    pub fn lean_coord_2pc_decide(_wire: &str) -> Result<String, String> {
        unavailable("dregg_coord_2pc_decide")
    }
    pub fn lean_coord_causal_order(_wire: &str) -> Result<String, String> {
        unavailable("dregg_coord_causal_order")
    }
    pub fn lean_coord_shared_budget(_wire: &str) -> Result<String, String> {
        unavailable("dregg_coord_shared_budget")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tau_order_decoder_is_fail_closed_and_exact() {
        // empty order round-trips to []; a populated `T=` wire decodes to the exact ordered ids.
        assert_eq!(decode_tau_order("T="), Some(Vec::new()));
        assert_eq!(decode_tau_order("T=10,20,30"), Some(vec![10, 20, 30]));
        // ERR / malformed bodies fail closed (None).
        assert_eq!(decode_tau_order("ERR"), None);
        assert_eq!(decode_tau_order("T=10,bad,30"), None);
        assert_eq!(decode_tau_order("nope"), None);
    }

    /// THE LIVE RAW-ORDER GATE DIFFERENTIAL — the verified Lean export `dregg_tau_order` returns the
    /// nine-id total order on the SAME 3-node lace the Lean `trace3` `#guard`s pin
    /// (`(tauOrder trace3 …).length == 9`, the golden `(creator,seq)` order
    /// `[(1,0),(2,0),(3,0),(1,1),(2,1),(3,1),(1,2),(2,2),(3,2)]`). We feed the SAME `encodeLaceWire`
    /// grammar the Lean `#guard`s use (ids 10..32, creators 1..3, the fully-connected DAG) and assert
    /// the export returns exactly nine ordered ids. Self-skips when the archive lacks the export.
    #[test]
    fn verified_tau_order_matches_trace3() {
        if !tau_order_available() {
            eprintln!("SKIP: Lean tau-order export not linked (tau_order_available()==false)");
            return;
        }
        // The Lean `trace3` lace, encoded with `encodeLaceWire 3 [1,2,3] trace3`:
        // round 1 ids 10/20/30 (genesis), round 2 ids 11/21/31 (ref all of r1), round 3 ids 12/22/32.
        let wire = "w=3;P=1,2,3;B=10:1:0:|20:2:0:|30:3:0:|\
                    11:1:1:10.20.30|21:2:1:10.20.30|31:3:1:10.20.30|\
                    12:1:2:11.21.31|22:2:2:11.21.31|32:3:2:11.21.31";
        let order = verified_tau_order(wire).expect("raw-order gate ran");
        assert_eq!(order.len(), 9, "3-node lace finalizes a nine-id total order");
        // the order is a permutation of all nine present ids (the verified `tauOrder` emits exactly
        // the finalized ids, no dups, all present).
        let mut sorted = order.clone();
        sorted.sort_unstable();
        assert_eq!(
            sorted,
            vec![10, 11, 12, 20, 21, 22, 30, 31, 32],
            "the verified total order is exactly the nine present blocks"
        );
        // a malformed wire is fail-closed to an EMPTY order (ERR ⇒ []).
        assert!(verified_tau_order("not a wire").expect("gate ran on garbage").is_empty());
    }

    #[test]
    fn verdict_decoder_is_fail_closed() {
        assert!(verdict_admits("1"));
        assert!(!verdict_admits("0"));
        assert!(!verdict_admits("ERR"));
        assert!(!verdict_admits(""));
        assert!(!verdict_admits("garbage"));
    }

    /// THE LIVE F-4 GATE DIFFERENTIAL — the verified Lean gate (`dregg_strand_admit`) reproduces the
    /// `fedDemo` admit/reject verdicts the Lean `#guard`s pin (seeds {0,1}, N=2, minBond=100; strand 2
    /// vouched by both seeds; strand 3 bonded at floor; strand 4 below floor; strand 5 a fresh Sybil).
    /// This is the runtime face of the F-4 closure: the SAME verified rule the federation gate calls
    /// admits exactly the right strands. Self-skips when the archive lacks the export.
    #[test]
    fn verified_gate_matches_feddemo() {
        if !strand_admit_available() {
            eprintln!("SKIP: Lean strand-admit export not linked (strand_admit_available()==false)");
            return;
        }
        // fedDemo, with 0-based participant indices: seeds {0,1}, vouch 0->2, 1->2, bonds 3:100, 4:50.
        let base = "N=2;m=100;S=0,1;V=0:2,1:2;Bo=3:100,4:50";
        let admit = |q: u32| -> bool {
            verified_admits(&format!("{base};q={q}")).expect("gate ran")
        };
        assert!(admit(0), "seed 0 admitted");
        assert!(admit(1), "seed 1 admitted");
        assert!(admit(2), "vouched strand admitted");
        assert!(admit(3), "bonded-at-floor strand admitted");
        assert!(!admit(4), "below-floor bond rejected");
        assert!(!admit(5), "fresh Sybil rejected (F-4)");
        // malformed wire ⇒ ERR ⇒ fail-closed NOT admitted.
        assert!(!verified_admits("not a wire").expect("gate ran on garbage (returns ERR)"));
    }

    /// THE LIVE CapTP+coord DECISION DIFFERENTIAL — the six verified `dregg_captp_*`/`dregg_coord_*`
    /// gates reproduce the verdicts the Lean `#guard`s pin. This is the runtime face of the STRONG-FORM
    /// swap: the SAME verified rules the captp/coord runtime invokes produce exactly these verdicts.
    /// Self-skips when the archive lacks the exports.
    #[test]
    fn verified_distributed_gates_match_guards() {
        if !distributed_exports_available() {
            eprintln!(
                "SKIP: Lean distributed exports not linked (distributed_exports_available()==false)"
            );
            return;
        }

        // §1 handoff non-amplification: held=signature granted=signature, unrestricted ⇒ "1".
        assert!(verified_handoff_non_amplifying("h=1;g=1;he=x;ge=x").expect("handoff gate ran"));
        // held=signature granted=none (loosens) ⇒ AMPLIFIES.
        assert!(!verified_handoff_non_amplifying("h=1;g=0;he=x;ge=x").expect("ran"));
        // held mask 6, granted 2 ⊆ 6 ⇒ "1"; granted 1 (not ⊆) ⇒ amplifies.
        assert!(verified_handoff_non_amplifying("h=0;g=0;he=6;ge=2").expect("ran"));
        assert!(!verified_handoff_non_amplifying("h=0;g=0;he=6;ge=1").expect("ran"));
        // malformed ⇒ fail-closed (amplifies — reject).
        assert!(!verified_handoff_non_amplifying("garbage").expect("ran"));

        // §2 GC process_drop on the demoTable: byzantine session 99 vs fed 10 ⇒ invalid, total 2.
        let demo = "H=10:1:42=1|20:1:99=1";
        assert_eq!(
            shadow_captp_process_drop(&format!("{demo};f=10;s=99")).expect("drop gate ran"),
            "S=2;t=2"
        );
        // honest fed 10 on its session 42 ⇒ stillHeld, total 1.
        assert_eq!(
            shadow_captp_process_drop(&format!("{demo};f=10;s=42")).expect("ran"),
            "S=0;t=1"
        );

        // §3 pipeline resolve: fulfill drains FIFO [100,101]; break drains nothing.
        assert_eq!(
            shadow_captp_pipeline_resolve("Q=100,101;e=f").expect("pipeline gate ran"),
            "D=100,101;q=0"
        );
        assert_eq!(shadow_captp_pipeline_resolve("Q=100,101;e=b").expect("ran"), "D=;q=0");

        // §4 2PC decide: 3-of-3 all yes ⇒ Commit; 2 yes 1 no ⇒ Abort; 2 yes 0 no ⇒ Pending.
        assert_eq!(verified_2pc_decide("y=3;n=0;N=3;t=3").expect("2pc gate ran"), Decision2pc::Commit);
        assert_eq!(verified_2pc_decide("y=2;n=1;N=3;t=3").expect("ran"), Decision2pc::Abort);
        assert_eq!(verified_2pc_decide("y=2;n=0;N=3;t=3").expect("ran"), Decision2pc::Pending);
        // malformed ⇒ fail-safe Pending.
        assert_eq!(verified_2pc_decide("garbage").expect("ran"), Decision2pc::Pending);

        // §5 causal order on chain 1→2→3: 1 happened-before 3 (transitive); 3 NOT before 1.
        let chain = "G=1:|2:1|3:2";
        assert!(verified_happened_before(&format!("{chain};a=1;b=3")).expect("causal gate ran"));
        assert!(!verified_happened_before(&format!("{chain};a=3;b=1")).expect("ran"));
        // self is not before self (irreflexive).
        assert!(!verified_happened_before(&format!("{chain};a=2;b=2")).expect("ran"));

        // §6 shared budget tau-resolution: pool 1000, debits [400,400,400] ⇒ A,B accept C reject.
        assert_eq!(
            shadow_coord_shared_budget("B=1000;D=400,400,400").expect("budget gate ran"),
            "R=1,1,0;b=200;a=800"
        );
        // a single over-budget debit is rejected, balance untouched.
        assert_eq!(shadow_coord_shared_budget("B=100;D=200").expect("ran"), "R=0;b=100;a=0");
    }
}
