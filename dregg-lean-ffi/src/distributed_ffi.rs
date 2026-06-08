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
}
