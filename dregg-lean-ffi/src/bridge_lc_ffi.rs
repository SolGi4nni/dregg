//! `bridge_lc_ffi` — the FFI route-through onto the VERIFIED ETHEREUM light-client VERIFY-LOGIC
//! gate (`Dregg2.Bridge.LightClientEthGate.dregg_eth_lc_verify`, `@[export] dregg_eth_lc_verify`).
//!
//! # What this is (the light-client twin-deletion, crypto-carrier boundary)
//!
//! `eth-lightclient/src/{lib,finality,execution}.rs` decides the SAME accept/reject that
//! `Dregg2.Bridge.LightClientEth.verifyFinalizedUpdate` proves `eth_no_forgery` over — a Rust
//! TWIN of the proven Lean rules that can drift ("proven over a re-authoring, not the emitted
//! object"; `docs/FORMAL-ASSURANCE-LIGHTCLIENT-CIRCUITS-2026-07-25.md`). This module routes the
//! Rust VERIFY-LOGIC through the Lean gate, exactly as `distributed_ffi::verified_finalization_quorum`
//! routes the collector's quorum decision through `dregg_finalization_quorum`.
//!
//! The subtlety the gate is designed around: light-client verify invokes HEAVY crypto (BLS12-381
//! aggregate verify + SHA-256 SSZ Merkle folds). So ONLY the verification LOGIC crosses to Lean —
//! the quorum counting / ≥ 2/3 multiply-form threshold / committee-size + bitfield checks / Nomad
//! zero-participant floor / branch-DEPTH admissibility (6|7 finality, 4 execution). The crypto
//! PRIMITIVES stay in Rust as NAMED verified-FFI carriers and are supplied to the gate as their
//! boolean RESULTS:
//!
//!   * `bls_ok`      — `blst` (audited; the ETH-client reference; Galois SAW proofs cover the
//!                     field/curve arithmetic; a verified-pairing EverCrypt-grade leaf is the
//!                     honest research frontier). The `EthLeaf.blsSound` carrier.
//!   * `finality_ok` / `exec_ok` — the SHA-256 branch-reconstruction comparisons (HACL*/EverCrypt
//!                     SHA-256 is the project-default verified realization, replacing RustCrypto
//!                     `sha2`). The `EthLeaf.hashPairCR` carrier.
//!
//! `LightClientEthGate.ethVerifyDecision_refines` PROVES the gate's decision over these
//! projections is DEFINITIONALLY `verifyFinalizedUpdate`, so gating a node on `dregg_eth_lc_verify`
//! gates it on the decision `eth_no_forgery` is proven over. The Rust `verify_finalized_update`
//! becomes the crypto-primitive computer + a differential sibling, NOT the decider.
//!
//! # The ONE trusted projection (named, not hidden)
//!
//! `participant_count` is the popcount of the 512-bit field, computed by the Rust caller
//! (`SyncAggregate::count`) and supplied on the wire — precisely as `dregg_finalization_quorum`
//! trusts the collector to intern+dedup its `(signer,root)` tally and verifies the quorum DECISION
//! over it. The popcount is a mechanically-faithful `count_ones` sum; the VERIFIED content is the
//! threshold/floor decision. HARDENING (named): ship the raw bits and count in Lean.
//!
//! # Wire grammar (mirrors `LightClientEthGate.decodeEthWire` byte-for-byte)
//!
//! ```text
//! INPUT  := "cl=" cl ";bl=" bl ";pc=" pc ";bls=" B ";fl=" fl ";fr=" B ";el=" el ";er=" B
//! B      := "0" | "1"
//! OUTPUT := "1" (ACCEPT) | "0" (REJECT) | "ERR" (malformed ⇒ fail-closed REJECT)
//! ```
//! (`cl`=committee length, `bl`=bitfield length, `pc`=participant popcount, `bls`=BLS aggregate
//! result, `fl`=finality-branch depth, `fr`=finality reconstruct result, `el`=execution-branch
//! depth, `er`=execution reconstruct result.)
//!
//! # Availability + fail-safety
//!
//! [`eth_lc_verify_available`] is true only when the linked archive exports `dregg_eth_lc_verify`
//! (cfg `dregg_eth_lc_verify_present`, set by build.rs) AND runtime init succeeded. When
//! unavailable (stale / marshal-only / cold-seed archive) the caller FAILS CLOSED — the ETH
//! light-client verdict is `Err`, never a silent Rust-twin accept. A wire that round-trips to
//! `"ERR"` / anything but `"1"` is a REJECT.

use crate::{ensure_lean_init, lean_init_once};

/// The verified decision the ETH light-client verify LOGIC reduces to. `Accept` iff the Lean gate
/// returned `"1"`; every other outcome (`"0"`, `"ERR"`, malformed, archive-absent) is fail-closed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EthLcVerdict {
    /// The verified gate ACCEPTED the update's projections (→ `verifyFinalizedUpdate = true`,
    /// hence — with the named crypto carriers sound — `EthValidAt`).
    Accept,
    /// The verified gate REJECTED (sub-quorum / wrong depth / failed crypto result / malformed).
    Reject,
}

/// Whether the linked archive exports the verified ETH light-client verify gate
/// (`dregg_eth_lc_verify`, spliced from `Dregg2.Bridge.LightClientEthGate`). When false the caller
/// must FAIL CLOSED (there is no sound Rust twin to fall back to — the whole point is that the Rust
/// logic is the twin being deleted).
pub fn eth_lc_verify_available() -> bool {
    ffi_eth_lc::eth_lc_verify_present() && lean_init_once().is_ok()
}

/// Build the ETH light-client verify wire from the combinatorial facts + the three crypto-primitive
/// RESULTS. Mirrors `LightClientEthGate.decodeEthWire`'s grammar exactly. `bls_ok` is the `blst`
/// aggregate-verify result over the participating subset + signing root; `finality_ok` / `exec_ok`
/// are the SHA-256 branch-reconstruction == root results.
pub fn eth_lc_verify_wire(
    committee_len: usize,
    bitfield_len: usize,
    participant_count: usize,
    bls_ok: bool,
    finality_len: usize,
    finality_ok: bool,
    exec_len: usize,
    exec_ok: bool,
) -> String {
    let b = |x: bool| if x { '1' } else { '0' };
    format!(
        "cl={committee_len};bl={bitfield_len};pc={participant_count};bls={};fl={finality_len};fr={};el={exec_len};er={}",
        b(bls_ok),
        b(finality_ok),
        b(exec_ok),
    )
}

/// Run the VERIFIED gate `@[export] dregg_eth_lc_verify` over a pre-built wire and return the raw
/// output (`"1"` / `"0"` / `"ERR"`). Requires [`eth_lc_verify_available`]; returns `Err` when the
/// archive did not export it (so the caller distinguishes "archive missing" from "rejected" and
/// FAILS CLOSED either way).
pub fn shadow_eth_lc_verify(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi_eth_lc::lean_eth_lc_verify(wire)
}

/// The end-to-end verified ETH light-client verify query: build the wire from the projections, run
/// the gate, and decode to [`EthLcVerdict`]. Returns `Ok(Accept)` ONLY on the gate's `"1"`; every
/// other gate output (`"0"`, `"ERR"`, malformed) is `Ok(Reject)` (fail-closed). `Err` is returned
/// ONLY when the archive lacks the export — the caller must treat that as REJECT (fail-closed),
/// NOT fall back to a Rust twin.
///
/// Because `LightClientEthGate.ethVerifyDecision_refines` proves the gate's decision over these
/// projections IS `verifyFinalizedUpdate`, an `Ok(Accept)` here is — with the named `blsSound` /
/// `hashPairCR` carriers sound — exactly the `EthValidAt` no-forgery conclusion, by construction.
#[allow(clippy::too_many_arguments)]
pub fn verified_eth_lc_verify(
    committee_len: usize,
    bitfield_len: usize,
    participant_count: usize,
    bls_ok: bool,
    finality_len: usize,
    finality_ok: bool,
    exec_len: usize,
    exec_ok: bool,
) -> Result<EthLcVerdict, String> {
    let wire = eth_lc_verify_wire(
        committee_len,
        bitfield_len,
        participant_count,
        bls_ok,
        finality_len,
        finality_ok,
        exec_len,
        exec_ok,
    );
    let out = shadow_eth_lc_verify(&wire)?;
    Ok(if out == "1" {
        EthLcVerdict::Accept
    } else {
        EthLcVerdict::Reject
    })
}

#[cfg(all(lean_lib_present, dregg_eth_lc_verify_present))]
mod ffi_eth_lc {
    use std::ffi::CString;
    use std::os::raw::c_char;

    extern "C" {
        fn dregg_eth_lc_verify_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
    }

    pub fn eth_lc_verify_present() -> bool {
        true
    }

    pub fn lean_eth_lc_verify(wire: &str) -> Result<String, String> {
        let c_in = CString::new(wire).map_err(|e| format!("wire has interior NUL: {e}"))?;
        let mut cap = wire.len() * 2 + 256;
        loop {
            let mut buf = vec![0u8; cap];
            let full = unsafe {
                dregg_eth_lc_verify_str(c_in.as_ptr(), buf.as_mut_ptr() as *mut c_char, cap)
            };
            if full == usize::MAX {
                return Err("dregg_eth_lc_verify_str: unusable output buffer".into());
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

#[cfg(not(all(lean_lib_present, dregg_eth_lc_verify_present)))]
mod ffi_eth_lc {
    pub fn eth_lc_verify_present() -> bool {
        false
    }

    pub fn lean_eth_lc_verify(_wire: &str) -> Result<String, String> {
        Err("dregg_eth_lc_verify not exported by the linked archive (rebuild to enable)".into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wire_grammar_matches_lean_decodeEthWire() {
        // The exact accepting witness `LightClientEthGate.eth_decision_discriminates` /
        // `#guard`s use, so a differential run (when the archive is present) is byte-identical.
        assert_eq!(
            eth_lc_verify_wire(512, 512, 512, true, 6, true, 4, true),
            "cl=512;bl=512;pc=512;bls=1;fl=6;fr=1;el=4;er=1"
        );
        assert_eq!(
            eth_lc_verify_wire(512, 512, 341, true, 6, true, 4, true),
            "cl=512;bl=512;pc=341;bls=1;fl=6;fr=1;el=4;er=1"
        );
    }

    #[test]
    fn fails_closed_when_export_absent() {
        // On a cold-seed / marshal-only archive the gate is unavailable and the verdict query
        // errs (the caller must treat that as REJECT — never a silent Rust-twin accept).
        if !eth_lc_verify_available() {
            assert!(verified_eth_lc_verify(512, 512, 512, true, 6, true, 4, true).is_err());
        }
    }
}
