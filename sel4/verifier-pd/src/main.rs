//! `dregg-verifier-pd` — the dregg proof verifier as an seL4 Microkit
//! protection domain.
//!
//! This is the seL4-native form of `verifier/src/main.rs`. Where the host
//! binary reads a proof file / stdin, runs `verify_*`, and `process::exit`s
//! with the verdict code, this PD:
//!
//!   1. reads a `BilateralBundle` (postcard) from the `proof_in` shared page,
//!   2. runs `dregg_verifier::verify_bilateral_bundle*` (the same audited
//!      verify core — NO Lean, NO IO loop, pure plonky3-STARK + crypto),
//!   3. writes a one-byte verdict + reason into the `verdict_out` page,
//!   4. signals its scheduler over the notification channel, then waits.
//!
//! The PD holds caps to exactly two pages (proof_in READ-ONLY, verdict_out
//! READ-WRITE) and one notification. It has NO prover authority, NO storage
//! cap, NO NIC cap. That capability partition — declared in sel4/dregg.system
//! — IS the "completely separate OS process, no shared mutable state, no
//! callbacks into a prover" guarantee that `verifier/src/lib.rs` promises,
//! now enforced by the seL4 kernel rather than by convention.
//!
//! STATUS (2026-06-13): SCAFFOLD. The `sel4_microkit` runtime is gated behind
//! `cfg(target_os = "sel4")` so this file is a coherent, reviewable program but
//! does not require the seL4 toolchain to be present to read. The verify-core
//! call it wraps is the real, host-proven Lean-free path.

#![cfg_attr(target_os = "sel4", no_std)]
#![cfg_attr(target_os = "sel4", no_main)]

extern crate alloc;

use alloc::format;

// ── Exit/verdict codes (mirror dregg_verifier::exit_code) ───────────────────
// Re-exported so the scheduler PD reads a stable byte contract from verdict_out.
const VERDICT_VERIFIED: u8 = 0;
const VERDICT_REJECTED: u8 = 1;
const VERDICT_ERROR: u8 = 2;

/// The shared-page contract written into `verdict_out`. Byte 0 is the verdict
/// code; bytes 1..N are a UTF-8 reason (truncated to the page). The scheduler
/// PD reads byte 0 and treats anything non-zero as "do not commit".
fn write_verdict(verdict_out: &mut [u8], code: u8, reason: &str) {
    verdict_out[0] = code;
    let rb = reason.as_bytes();
    let n = core::cmp::min(rb.len(), verdict_out.len().saturating_sub(1));
    verdict_out[1..1 + n].copy_from_slice(&rb[..n]);
}

/// The pure verification step — identical shape to the host CLI's
/// `run_bilateral_pair`, but reading from a buffer instead of a file. This is
/// the load-bearing reuse: `dregg_verifier` is called exactly as on the host.
///
/// Returns the verdict byte to publish.
fn run_verify(proof_in: &[u8], verdict_out: &mut [u8]) -> u8 {
    // The bundle arrives as the postcard wire form the SDKs share. The verify
    // core takes JSON in its highest-level entry; for the PD we use the
    // bytes-oriented bundle path. (Wiring detail: the exact entry —
    // `verify_bilateral_bundle_json` vs a postcard variant — is chosen when the
    // ingress contract is fixed; both are in `dregg_verifier`'s public API and
    // neither touches Lean or IO.)
    match core::str::from_utf8(proof_in) {
        Ok(json) => {
            // `verify_bilateral_bundle_json` returns a pure `BilateralVerdict`
            // (a struct over the bundle — `verified: bool` + `reason`). The
            // caller maps it to the exit-code byte contract, exactly as the
            // host `run_bilateral_pair` does.
            let verdict = dregg_verifier::verify_bilateral_bundle_json(json);
            let v = if verdict.verified { VERDICT_VERIFIED } else { VERDICT_REJECTED };
            write_verdict(verdict_out, v, &verdict.reason);
            v
        }
        Err(e) => {
            write_verdict(verdict_out, VERDICT_ERROR, &format!("utf8: {e}"));
            VERDICT_ERROR
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
//  seL4 / Microkit entry point (only compiled for the seL4 target).
// ════════════════════════════════════════════════════════════════════════════
#[cfg(target_os = "sel4")]
mod sel4_entry {
    use super::*;

    // The Microkit runtime fills these from the `setvar_vaddr` mappings in
    // dregg.system (proof_in_vaddr / verdict_out_vaddr). The PD never calls a
    // POSIX read(); the bytes are simply *there* at a fixed virtual address.
    extern "C" {
        static proof_in_vaddr: *mut u8;
        static verdict_out_vaddr: *mut u8;
    }

    const PROOF_IN_SIZE: usize = 0x100000; // matches the memory_region size
    const VERDICT_OUT_SIZE: usize = 0x1000;

    // sel4_microkit::protection_domain wires the entry, the heap, and the
    // notification dispatch. Channel id 1 (verifier end) is the "bundle staged"
    // signal from the scheduler; on notification we verify and signal back.
    //
    // #[sel4_microkit::protection_domain(heap_size = 0x40000)]
    // fn init() -> impl sel4_microkit::Handler { Verifier }
    //
    // struct Verifier;
    // impl sel4_microkit::Handler for Verifier {
    //     fn notified(&mut self, ch: sel4_microkit::Channel) -> Result<(), Infallible> {
    //         if ch == VERIFY_REQUEST {
    //             let proof = unsafe { core::slice::from_raw_parts(proof_in_vaddr, PROOF_IN_SIZE) };
    //             let verdict = unsafe { core::slice::from_raw_parts_mut(verdict_out_vaddr, VERDICT_OUT_SIZE) };
    //             let _ = run_verify(proof, verdict);
    //             VERIFY_REQUEST.notify(); // "verdict ready" — the ONE-WAY edge
    //         }
    //         Ok(())
    //     }
    // }
}

// ════════════════════════════════════════════════════════════════════════════
//  Host stub: lets the crate be read/checked on a normal target. On the seL4
//  target this `main` is absent (#![no_main]); the Microkit macro supplies the
//  entry instead.
// ════════════════════════════════════════════════════════════════════════════
#[cfg(not(target_os = "sel4"))]
fn main() {
    // A host smoke shape: a real driver would feed a known-good bundle and
    // assert VERDICT_VERIFIED. Kept minimal — the *real* host proof of the
    // Lean-free verify core is `cargo build -p dregg-verifier --features
    // no-lean-link` (see sel4/README.md §verification).
    let mut verdict = [0u8; 0x1000];
    let code = run_verify(b"{}", &mut verdict);
    core::hint::black_box(code);
}
