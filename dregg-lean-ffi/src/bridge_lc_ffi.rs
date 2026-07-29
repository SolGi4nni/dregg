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

// ============================================================================
// Ethereum COMMITTEE ROTATION (verified route-through) — the TRUST-ROOT gate
// ============================================================================
//
// `dregg_eth_lc_verify` decides whether the client may follow the CHAIN. It decides NOTHING about
// whether the client may change WHOSE SIGNATURES IT TRUSTS. That second decision —
// `eth-lightclient::verify_committee_update`, reached from
// `WeakSubjectivityStore::{bootstrap_committee, advance}` — used to be hand-written Rust: a branch
// depth admissibility rule (5 Altair..Deneb | 6 Electra+) `&&`-ed with a SHA-256 fold, deciding
// which 512 public keys the light client would trust from then on. The verify gate was honest and
// there was a door beside it.
//
// `Dregg2.Bridge.LightClientEthGate.committeeRotationDecision` is that rule in Lean;
// `committeeRotationDecision_refines` proves (by `rfl`) the exported decision IS
// `verifyCommitteeRotation`, and `committeeRotationDecision_binding` is the payoff: given the named
// SHA-256 CR carrier, one beacon state root commits ONE next committee, so an accepted rotation
// cannot fork the trust anchor. Rust keeps the SSZ committee-root computation and the branch fold
// and supplies their RESULT — the same `hashPairCR` carrier boundary the finality/execution
// branches already use.
//
// ```text
// INPUT  := "nl=" nl ";nr=" B          (nl = branch depth, nr = reconstruction result)
// B      := "0" | "1"
// OUTPUT := "1" (ROTATE) | "0" (REFUSE) | "ERR" (malformed ⇒ fail-closed REFUSE)
// ```
//
// Absent export ⇒ `Err`, and `verify_committee_update` refuses: the trusted committee simply does
// not advance. There is deliberately no Rust fallback — the Rust rule WAS the twin.

/// The verified decision the ETH committee-rotation LOGIC reduces to. `Rotate` iff the Lean gate
/// returned `"1"`; every other outcome (`"0"`, `"ERR"`, malformed, archive-absent) is fail-closed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EthCommitteeRotationVerdict {
    /// The verified gate ACCEPTED the rotation projections (→ `verifyCommitteeRotation = true`,
    /// hence — with the named `hashPairCR` carrier sound — the offered committee is the unique
    /// `next_sync_committee` the trusted beacon state commits).
    Rotate,
    /// The verified gate REFUSED (inadmissible branch depth, or the branch did not reconstruct).
    Refuse,
}

/// Whether the linked archive exports the verified ETH committee-rotation gate
/// (`dregg_eth_committee_rotation`, spliced from `Dregg2.Bridge.LightClientEthGate`). Probed
/// INDEPENDENTLY of [`eth_lc_verify_available`]: an archive predating this export carries the
/// verify gate and not the rotation gate, and treating them as one would let a stale seed advertise
/// a trust-root gate it cannot render.
pub fn eth_committee_rotation_available() -> bool {
    ffi_eth_committee::eth_committee_rotation_present() && lean_init_once().is_ok()
}

/// Build the committee-rotation wire. Mirrors `LightClientEthGate.decodeCommitteeWire`'s grammar
/// exactly. `branch_len` is the supplied `next_sync_committee_branch` depth; `reconstruct_ok` is the
/// SHA-256 fold RESULT (the committee's SSZ root folded up the branch at subtree index 23, compared
/// against the trusted beacon state root).
pub fn eth_committee_rotation_wire(branch_len: usize, reconstruct_ok: bool) -> String {
    format!(
        "nl={branch_len};nr={}",
        if reconstruct_ok { '1' } else { '0' }
    )
}

/// Run the VERIFIED gate `@[export] dregg_eth_committee_rotation` over a pre-built wire and return
/// the raw output (`"1"` / `"0"` / `"ERR"`). `Err` only when the archive lacks the export.
pub fn shadow_eth_committee_rotation(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi_eth_committee::lean_eth_committee_rotation(wire)
}

/// The end-to-end verified committee-rotation query: build the wire, run the gate, decode. `Err`
/// ONLY when the archive lacks the export — the caller must treat that as REFUSE (fail-closed),
/// never as an excuse to install the committee anyway.
pub fn verified_eth_committee_rotation(
    branch_len: usize,
    reconstruct_ok: bool,
) -> Result<EthCommitteeRotationVerdict, String> {
    let wire = eth_committee_rotation_wire(branch_len, reconstruct_ok);
    let out = shadow_eth_committee_rotation(&wire)?;
    Ok(if out == "1" {
        EthCommitteeRotationVerdict::Rotate
    } else {
        EthCommitteeRotationVerdict::Refuse
    })
}

#[cfg(all(lean_lib_present, dregg_eth_committee_rotation_present))]
mod ffi_eth_committee {
    use std::ffi::CString;
    use std::os::raw::c_char;

    extern "C" {
        fn dregg_eth_committee_rotation_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
    }

    pub fn eth_committee_rotation_present() -> bool {
        true
    }

    pub fn lean_eth_committee_rotation(wire: &str) -> Result<String, String> {
        let c_in = CString::new(wire).map_err(|e| format!("wire has interior NUL: {e}"))?;
        let mut cap = wire.len() * 2 + 256;
        loop {
            let mut buf = vec![0u8; cap];
            let full = unsafe {
                dregg_eth_committee_rotation_str(
                    c_in.as_ptr(),
                    buf.as_mut_ptr() as *mut c_char,
                    cap,
                )
            };
            if full == usize::MAX {
                return Err("dregg_eth_committee_rotation_str: unusable output buffer".into());
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

#[cfg(not(all(lean_lib_present, dregg_eth_committee_rotation_present)))]
mod ffi_eth_committee {
    pub fn eth_committee_rotation_present() -> bool {
        false
    }

    pub fn lean_eth_committee_rotation(_wire: &str) -> Result<String, String> {
        Err(
            "dregg_eth_committee_rotation not exported by the linked archive (rebuild to enable)"
                .into(),
        )
    }
}

// ============================================================================
// Tendermint / Cosmos light-client verify (verified route-through)
// ============================================================================
//
// Routes the Cosmos/Tendermint verify LOGIC through the Lean gate
// `Dregg2.Bridge.LightClientTendermintGate.dregg_tm_lc_verify`, exactly as `verified_eth_lc_verify`
// routes the ETH verify. `cosmos-lightclient/src/lib.rs`'s `verify_cosmos_header` (delegating to the
// audited informalsystems `ProdVerifier`) decides the SAME accept/reject that
// `LightClientTendermint.tmVerify` proves `tmNoForgery` over — a Rust TWIN that can drift. The gate
// is the twin-deletion boundary: the STAKE-WEIGHTED verify LOGIC crosses to Lean (chain-id match /
// adjacent-height advance / time window / the STRICT `> 2/3` multiply-form threshold
// `2·totalPower < 3·signedPower`), while the crypto PRIMITIVES stay in Rust as NAMED verified-FFI
// carriers supplied as their RESULTS:
//
//   * `signed_power` — the summed voting power of validators whose per-validator Ed25519 commit
//                      signature verified (the `CryptoLeaf.sigSound` carrier; ed25519-dalek /
//                      informalsystems verification). `total_power` is the full stake sum (no crypto).
//   * `epoch_bind_ok` / `self_bind_ok` — the SHA-256 validator-set hash-and-compare results (the
//                      `CryptoLeaf.hashCR` carrier): the trusted `next_validators_hash` equals the
//                      hash of the untrusted validator set (adjacent-advance epoch binding), and the
//                      header self-binds its validator set.
//
// `LightClientTendermintGate.tmVerifyDecision_refines` PROVES the gate's decision over these
// projections is DEFINITIONALLY `tmVerify` (axiom-free `rfl`), so gating a node on
// `dregg_tm_lc_verify` gates it on the decision `tmNoForgery` is proven over. Scope (honest):
// `tmVerify` formalizes the ADJACENT-advance rule set; the non-adjacent skipping / trust-overlap
// shape is the named follow-up (extended by the identical method once `tmVerify` gains the overlap
// conjunct). Fail-closed: archive-absent ⇒ `Err` ⇒ caller REJECTS (no Rust-twin fallback).
//
// Wire grammar (mirrors `LightClientTendermintGate.decodeTmWire` byte-for-byte):
// ```text
// INPUT := "ci=" ci ";tci=" tci ";h=" h ";th=" th ";ht=" ht ";t=" t ";nw=" nw ";cd=" cd
//        ";tp=" tp ";eb=" B ";vb=" B ";tot=" tot ";sp=" sp
// B     := "0" | "1"
// ```

/// The verified decision the Tendermint light-client verify LOGIC reduces to. `Accept` iff the Lean
/// gate (`dregg_tm_lc_verify`) returned `"1"`; every other outcome (`"0"`, `"ERR"`, malformed,
/// archive-absent) is fail-closed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TmLcVerdict {
    /// The verified gate ACCEPTED the update's projections (→ `tmVerify = true`, hence — with the
    /// named ed25519 `sigSound` / SHA-256 `hashCR` carriers sound — `TmForeignValid`).
    Accept,
    /// The verified gate REJECTED (sub-quorum / wrong epoch / stale-or-future time / failed crypto
    /// result / malformed).
    Reject,
}

/// Whether the linked archive exports the verified Tendermint light-client verify gate
/// (`dregg_tm_lc_verify`, spliced from `Dregg2.Bridge.LightClientTendermintGate`). When false the
/// caller must FAIL CLOSED (there is no sound Rust twin to fall back to).
pub fn tm_lc_verify_available() -> bool {
    ffi_tm_lc::tm_lc_verify_present() && lean_init_once().is_ok()
}

/// Build the Tendermint verify wire from the stake-weighted combinatorial facts + the three crypto
/// RESULTS. Mirrors `LightClientTendermintGate.decodeTmWire`'s grammar exactly. `epoch_bind_ok` /
/// `self_bind_ok` are the SHA-256 validator-set hash-and-compare results; `signed_power` is the
/// Ed25519-verified stake sum; `total_power` the full stake sum.
#[allow(clippy::too_many_arguments)]
pub fn tm_lc_verify_wire(
    chain_id: u64,
    trusted_chain_id: u64,
    height: u64,
    trusted_height: u64,
    header_time: u64,
    time: u64,
    now: u64,
    clock_drift: u64,
    trusting_period: u64,
    epoch_bind_ok: bool,
    self_bind_ok: bool,
    total_power: u64,
    signed_power: u64,
) -> String {
    let b = |x: bool| if x { '1' } else { '0' };
    format!(
        "ci={chain_id};tci={trusted_chain_id};h={height};th={trusted_height};ht={header_time};t={time};nw={now};cd={clock_drift};tp={trusting_period};eb={};vb={};tot={total_power};sp={signed_power}",
        b(epoch_bind_ok),
        b(self_bind_ok),
    )
}

/// Run the VERIFIED gate `@[export] dregg_tm_lc_verify` over a pre-built wire and return the raw
/// output (`"1"` / `"0"` / `"ERR"`). Requires [`tm_lc_verify_available`]; returns `Err` when the
/// archive did not export it (so the caller distinguishes "archive missing" from "rejected" and
/// FAILS CLOSED either way).
pub fn shadow_tm_lc_verify(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi_tm_lc::lean_tm_lc_verify(wire)
}

/// The end-to-end verified Tendermint light-client verify query: build the wire from the
/// projections, run the gate, and decode to [`TmLcVerdict`]. Returns `Ok(Accept)` ONLY on the gate's
/// `"1"`; every other gate output (`"0"`, `"ERR"`, malformed) is `Ok(Reject)` (fail-closed). `Err` is
/// returned ONLY when the archive lacks the export — the caller must treat that as REJECT
/// (fail-closed), NOT fall back to a Rust twin.
///
/// Because `LightClientTendermintGate.tmVerifyDecision_refines` proves the gate's decision over these
/// projections IS `tmVerify`, an `Ok(Accept)` here is — with the named `sigSound` / `hashCR` carriers
/// sound — exactly the `TmForeignValid` no-forgery conclusion, by construction.
#[allow(clippy::too_many_arguments)]
pub fn verified_tm_lc_verify(
    chain_id: u64,
    trusted_chain_id: u64,
    height: u64,
    trusted_height: u64,
    header_time: u64,
    time: u64,
    now: u64,
    clock_drift: u64,
    trusting_period: u64,
    epoch_bind_ok: bool,
    self_bind_ok: bool,
    total_power: u64,
    signed_power: u64,
) -> Result<TmLcVerdict, String> {
    let wire = tm_lc_verify_wire(
        chain_id,
        trusted_chain_id,
        height,
        trusted_height,
        header_time,
        time,
        now,
        clock_drift,
        trusting_period,
        epoch_bind_ok,
        self_bind_ok,
        total_power,
        signed_power,
    );
    let out = shadow_tm_lc_verify(&wire)?;
    Ok(if out == "1" {
        TmLcVerdict::Accept
    } else {
        TmLcVerdict::Reject
    })
}

#[cfg(all(lean_lib_present, dregg_tm_lc_verify_present))]
mod ffi_tm_lc {
    use std::ffi::CString;
    use std::os::raw::c_char;

    extern "C" {
        fn dregg_tm_lc_verify_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
    }

    pub fn tm_lc_verify_present() -> bool {
        true
    }

    pub fn lean_tm_lc_verify(wire: &str) -> Result<String, String> {
        let c_in = CString::new(wire).map_err(|e| format!("wire has interior NUL: {e}"))?;
        let mut cap = wire.len() * 2 + 256;
        loop {
            let mut buf = vec![0u8; cap];
            let full = unsafe {
                dregg_tm_lc_verify_str(c_in.as_ptr(), buf.as_mut_ptr() as *mut c_char, cap)
            };
            if full == usize::MAX {
                return Err("dregg_tm_lc_verify_str: unusable output buffer".into());
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

#[cfg(not(all(lean_lib_present, dregg_tm_lc_verify_present)))]
mod ffi_tm_lc {
    pub fn tm_lc_verify_present() -> bool {
        false
    }

    pub fn lean_tm_lc_verify(_wire: &str) -> Result<String, String> {
        Err("dregg_tm_lc_verify not exported by the linked archive (rebuild to enable)".into())
    }
}

// ============================================================================
// Tendermint / Cosmos NON-ADJACENT (skipping) light-client verify
// ============================================================================
//
// The second Cosmos gate, `Dregg2.Bridge.LightClientTendermintSkip.dregg_tm_skip_verify`. It is a
// SEPARATE rule set, not a relaxation of the adjacent one, and the two cover DISJOINT height
// ranges (`tmSkip_height_disjoint_from_adjacent`):
//
//   * the `next_validators_hash` epoch binding is ABSENT — a skip target's validator set was
//     never committed by the trusted header, which is the whole nature of skipping;
//   * in its place comes the TRUST-OVERLAP threshold, in the audited verifier's own strict
//     multiply form `trustNum · trustedTotal < trustDen · trustedSigned`
//     (`TrustThresholdFraction::is_enough_power signed total = signed·den > total·num`), i.e.
//     strictly more than `trust_threshold` (canonically 1/3) of the TRUSTED epoch's voting power
//     signed the target — ON TOP of the full strict `> 2/3` over the target's own set;
//   * the height conjunct is `trusted.height + 1 < height`, the exact condition under which
//     `validate_against_trusted` takes its `else` branch and requires `is_monotonic_height`.
//
// The crypto boundary is identical to the adjacent gate's: the per-validator Ed25519 verification
// feeds BOTH tallies (`voting_power_in_sets` walks each validator set looking that validator's
// vote up in the one commit) and the SHA-256 validator-set hashing feeds `self_bind_ok`. The gate
// re-derives no crypto. `tmSkipVerifyDecision_refines` PROVES the composed decision over these
// projections is DEFINITIONALLY `tmSkipVerify` (`rfl`), so an `Accept` here is — with the named
// `sigSound` / `hashCR` carriers sound — exactly `TmSkipForeignValid`, whose fourth conjunct is
// the trust-overlap anchor. Fail-closed: archive-absent ⇒ `Err` ⇒ caller REJECTS.
//
// Wire grammar (mirrors `decodeTmSkipWire` byte-for-byte, SIXTEEN fields — deliberately not a
// superset of the adjacent gate's thirteen, so a mis-routed wire is `"ERR"`, never a verdict about
// the wrong rule set):
// ```text
// INPUT := "ci=" ci ";tci=" tci ";h=" h ";th=" th ";ht=" ht ";t=" t ";nw=" nw ";cd=" cd
//        ";tp=" tp ";vb=" B ";tn=" tn ";td=" td ";ttot=" ttot ";tsp=" tsp ";tot=" tot ";sp=" sp
// B     := "0" | "1"
// ```

/// The verified decision the Tendermint SKIPPING verify LOGIC reduces to. `Accept` iff the Lean
/// gate (`dregg_tm_skip_verify`) returned `"1"`; every other outcome is fail-closed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TmSkipVerdict {
    /// The verified gate ACCEPTED the skip's projections (→ `tmSkipVerify = true`, hence — with
    /// the named carriers sound — `TmSkipForeignValid`, trust-overlap conjunct included).
    Accept,
    /// The verified gate REJECTED (sub-quorum / sub-overlap / adjacent-or-backward height /
    /// stale-or-future time / failed crypto result / malformed).
    Reject,
}

/// Whether the linked archive exports the verified Tendermint SKIPPING gate
/// (`dregg_tm_skip_verify`). Probed INDEPENDENTLY of [`tm_lc_verify_available`]: every archive
/// spliced before 2026-07-29 exports the adjacent gate and not this one, and conflating them
/// would advertise a skip gate that cannot render a verdict. When false the caller must FAIL
/// CLOSED (there is no sound Rust twin to fall back to).
pub fn tm_skip_verify_available() -> bool {
    ffi_tm_skip::tm_skip_verify_present() && lean_init_once().is_ok()
}

/// Build the Tendermint SKIPPING wire. Mirrors `decodeTmSkipWire`'s grammar exactly.
/// `trusted_total_power` / `trusted_signed_power` are the OVERLAP tally over the TRUSTED
/// next-validator set; `total_power` / `signed_power` the tally over the untrusted set.
#[allow(clippy::too_many_arguments)]
pub fn tm_skip_verify_wire(
    chain_id: u64,
    trusted_chain_id: u64,
    height: u64,
    trusted_height: u64,
    header_time: u64,
    time: u64,
    now: u64,
    clock_drift: u64,
    trusting_period: u64,
    self_bind_ok: bool,
    trust_num: u64,
    trust_den: u64,
    trusted_total_power: u64,
    trusted_signed_power: u64,
    total_power: u64,
    signed_power: u64,
) -> String {
    let b = |x: bool| if x { '1' } else { '0' };
    format!(
        "ci={chain_id};tci={trusted_chain_id};h={height};th={trusted_height};ht={header_time};t={time};nw={now};cd={clock_drift};tp={trusting_period};vb={};tn={trust_num};td={trust_den};ttot={trusted_total_power};tsp={trusted_signed_power};tot={total_power};sp={signed_power}",
        b(self_bind_ok),
    )
}

/// Run the VERIFIED gate `@[export] dregg_tm_skip_verify` over a pre-built wire and return the raw
/// output (`"1"` / `"0"` / `"ERR"`). `Err` only when the archive did not export it — so the caller
/// distinguishes "archive missing" from "rejected" and FAILS CLOSED either way.
pub fn shadow_tm_skip_verify(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi_tm_skip::lean_tm_skip_verify(wire)
}

/// The end-to-end verified Tendermint SKIPPING query: build the wire, run the gate, decode to
/// [`TmSkipVerdict`]. `Ok(Accept)` ONLY on the gate's `"1"`; every other gate output (`"0"`,
/// `"ERR"`, malformed) is `Ok(Reject)`. `Err` is returned ONLY when the archive lacks the export
/// — the caller must treat that as REJECT, NOT fall back to a Rust twin.
#[allow(clippy::too_many_arguments)]
pub fn verified_tm_skip_verify(
    chain_id: u64,
    trusted_chain_id: u64,
    height: u64,
    trusted_height: u64,
    header_time: u64,
    time: u64,
    now: u64,
    clock_drift: u64,
    trusting_period: u64,
    self_bind_ok: bool,
    trust_num: u64,
    trust_den: u64,
    trusted_total_power: u64,
    trusted_signed_power: u64,
    total_power: u64,
    signed_power: u64,
) -> Result<TmSkipVerdict, String> {
    let wire = tm_skip_verify_wire(
        chain_id,
        trusted_chain_id,
        height,
        trusted_height,
        header_time,
        time,
        now,
        clock_drift,
        trusting_period,
        self_bind_ok,
        trust_num,
        trust_den,
        trusted_total_power,
        trusted_signed_power,
        total_power,
        signed_power,
    );
    let out = shadow_tm_skip_verify(&wire)?;
    Ok(if out == "1" {
        TmSkipVerdict::Accept
    } else {
        TmSkipVerdict::Reject
    })
}

#[cfg(all(lean_lib_present, dregg_tm_skip_verify_present))]
mod ffi_tm_skip {
    use std::ffi::CString;
    use std::os::raw::c_char;

    extern "C" {
        fn dregg_tm_skip_verify_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
    }

    pub fn tm_skip_verify_present() -> bool {
        true
    }

    pub fn lean_tm_skip_verify(wire: &str) -> Result<String, String> {
        let c_in = CString::new(wire).map_err(|e| format!("wire has interior NUL: {e}"))?;
        let mut cap = wire.len() * 2 + 256;
        loop {
            let mut buf = vec![0u8; cap];
            let full = unsafe {
                dregg_tm_skip_verify_str(c_in.as_ptr(), buf.as_mut_ptr() as *mut c_char, cap)
            };
            if full == usize::MAX {
                return Err("dregg_tm_skip_verify_str: unusable output buffer".into());
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

#[cfg(not(all(lean_lib_present, dregg_tm_skip_verify_present)))]
mod ffi_tm_skip {
    pub fn tm_skip_verify_present() -> bool {
        false
    }

    pub fn lean_tm_skip_verify(_wire: &str) -> Result<String, String> {
        Err("dregg_tm_skip_verify not exported by the linked archive (rebuild to enable)".into())
    }
}

// ============================================================================
// EVM state-inclusion (EIP-1186 / MPT) light-client verify (verified route-through)
// ============================================================================
//
// Routes the EVM proof-of-holdings verify LOGIC through the Lean gate
// `Dregg2.Bridge.LightClientMptGate.dregg_mpt_lc_verify`. `eth-lightclient/src/evm.rs`'s
// `verify_erc20_holding` (composing `verify_evm_account_proof` + `verify_evm_storage_slot`) decides
// the SAME accept/reject that `LightClientMpt.mptVerify` proves `mpt_noForgery` / `mpt_balance_binding`
// over — a Rust TWIN that can drift. The gate is the twin-deletion boundary: the higher-level BINDING
// LOGIC crosses to Lean (the Nomad-law zero floor `claimed_balance ≠ 0`, and the anchor bindings —
// the update's carried `state_root` / `token` / `mapping_slot` must equal the TRUSTED ones), while
// the keccak-interleaved Merkle-Patricia path walk stays in Rust (alloy-trie's audited
// `verify_proof`) as a NAMED verified-FFI carrier supplied as its RESULTS:
//
//   * `account_proof_ok`  — the account trie opens `keccak(token)` to the RLP-encoded
//                           `[nonce,balance,storageRoot,codeHash]` account under `state_root`.
//   * `storage_proof_ok`  — the storage trie opens the holder's derived slot key
//                           (`keccak256(pad32(holder) ‖ pad32(slot))`) to the claimed balance under
//                           that account's OWN `storageHash`.
//
// Each is the boolean outcome of alloy-trie `verify_proof` (the `CryptoLeaf.hashCR` / keccak256-CR
// carrier). `LightClientMptGate.mptVerifyDecision_refines` PROVES the gate's decision over these
// projections is DEFINITIONALLY `mptVerify` (`rfl`; it inherits exactly `mptVerify`'s `propext`, from
// the compiled path-walk `childAt`/`getElem?`, and adds NO axiom of its own), so gating a node on
// `dregg_mpt_lc_verify` gates it on the decision `mpt_noForgery` AND `mpt_balance_binding` are proven
// over. Fail-closed: archive-absent ⇒ `Err` ⇒ caller REJECTS (no Rust-twin fallback).
//
// The digest/identifier projections are the model's `Nat` DECIMAL encodings (a production instance
// derives them from the 32-byte keccak values / U256 balance); they are passed as `&str` because the
// state root is a full 256-bit digest that does not fit a fixed integer. The keccak carrier lives
// entirely inside the two path-walk booleans.
//
// Wire grammar (mirrors `LightClientMptGate.decodeMptWire` byte-for-byte):
// ```text
// INPUT := "bal=" bal ";sr=" sr ";tsr=" tsr ";tk=" tk ";ttk=" ttk ";ms=" ms ";tms=" tms
//        ";ap=" B ";sp=" B
// B     := "0" | "1"
// ```

/// The verified decision the EVM-inclusion light-client verify LOGIC reduces to. `Accept` iff the
/// Lean gate (`dregg_mpt_lc_verify`) returned `"1"`; every other outcome is fail-closed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MptLcVerdict {
    /// The verified gate ACCEPTED (→ `mptVerify = true`, hence — with the named keccak256 `hashCR`
    /// carrier sound — `MptForeignValid`, and balance-binding across accepted holdings).
    Accept,
    /// The verified gate REJECTED (zero balance / wrong anchor / failed path-walk result / malformed).
    Reject,
}

/// Whether the linked archive exports the verified EVM-inclusion light-client verify gate
/// (`dregg_mpt_lc_verify`, spliced from `Dregg2.Bridge.LightClientMptGate`). When false the caller
/// must FAIL CLOSED (there is no sound Rust twin to fall back to).
pub fn mpt_lc_verify_available() -> bool {
    ffi_mpt_lc::mpt_lc_verify_present() && lean_init_once().is_ok()
}

/// Build the EVM-inclusion verify wire from the zero-floor / anchor facts + the two keccak
/// path-walk RESULTS. Mirrors `LightClientMptGate.decodeMptWire`'s grammar exactly. The numeric
/// projections are decimal encodings of the model's `Nat` digests/identifiers (`&str` because a
/// 256-bit state root does not fit a fixed integer); `account_proof_ok` / `storage_proof_ok` are the
/// alloy-trie `verify_proof` results for the two tiers.
#[allow(clippy::too_many_arguments)]
pub fn mpt_lc_verify_wire(
    claimed_balance: &str,
    state_root: &str,
    trusted_state_root: &str,
    token: &str,
    trusted_token: &str,
    mapping_slot: &str,
    trusted_mapping_slot: &str,
    account_proof_ok: bool,
    storage_proof_ok: bool,
) -> String {
    let b = |x: bool| if x { '1' } else { '0' };
    format!(
        "bal={claimed_balance};sr={state_root};tsr={trusted_state_root};tk={token};ttk={trusted_token};ms={mapping_slot};tms={trusted_mapping_slot};ap={};sp={}",
        b(account_proof_ok),
        b(storage_proof_ok),
    )
}

/// Run the VERIFIED gate `@[export] dregg_mpt_lc_verify` over a pre-built wire and return the raw
/// output (`"1"` / `"0"` / `"ERR"`). Requires [`mpt_lc_verify_available`]; returns `Err` when the
/// archive did not export it (fail-closed either way).
pub fn shadow_mpt_lc_verify(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi_mpt_lc::lean_mpt_lc_verify(wire)
}

/// The end-to-end verified EVM-inclusion light-client verify query: build the wire from the
/// projections, run the gate, and decode to [`MptLcVerdict`]. Returns `Ok(Accept)` ONLY on the gate's
/// `"1"`; every other gate output is `Ok(Reject)` (fail-closed). `Err` ONLY when the archive lacks the
/// export — the caller must treat that as REJECT (fail-closed), NOT fall back to a Rust twin.
///
/// Because `LightClientMptGate.mptVerifyDecision_refines` proves the gate's decision over these
/// projections IS `mptVerify`, an `Ok(Accept)` here is — with the named keccak256 `hashCR` carrier
/// sound — exactly the `MptForeignValid` no-forgery conclusion (and the accepted holding is
/// balance-bound), by construction.
#[allow(clippy::too_many_arguments)]
pub fn verified_mpt_lc_verify(
    claimed_balance: &str,
    state_root: &str,
    trusted_state_root: &str,
    token: &str,
    trusted_token: &str,
    mapping_slot: &str,
    trusted_mapping_slot: &str,
    account_proof_ok: bool,
    storage_proof_ok: bool,
) -> Result<MptLcVerdict, String> {
    let wire = mpt_lc_verify_wire(
        claimed_balance,
        state_root,
        trusted_state_root,
        token,
        trusted_token,
        mapping_slot,
        trusted_mapping_slot,
        account_proof_ok,
        storage_proof_ok,
    );
    let out = shadow_mpt_lc_verify(&wire)?;
    Ok(if out == "1" {
        MptLcVerdict::Accept
    } else {
        MptLcVerdict::Reject
    })
}

#[cfg(all(lean_lib_present, dregg_mpt_lc_verify_present))]
mod ffi_mpt_lc {
    use std::ffi::CString;
    use std::os::raw::c_char;

    extern "C" {
        fn dregg_mpt_lc_verify_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
    }

    pub fn mpt_lc_verify_present() -> bool {
        true
    }

    pub fn lean_mpt_lc_verify(wire: &str) -> Result<String, String> {
        let c_in = CString::new(wire).map_err(|e| format!("wire has interior NUL: {e}"))?;
        let mut cap = wire.len() * 2 + 256;
        loop {
            let mut buf = vec![0u8; cap];
            let full = unsafe {
                dregg_mpt_lc_verify_str(c_in.as_ptr(), buf.as_mut_ptr() as *mut c_char, cap)
            };
            if full == usize::MAX {
                return Err("dregg_mpt_lc_verify_str: unusable output buffer".into());
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

#[cfg(not(all(lean_lib_present, dregg_mpt_lc_verify_present)))]
mod ffi_mpt_lc {
    pub fn mpt_lc_verify_present() -> bool {
        false
    }

    pub fn lean_mpt_lc_verify(_wire: &str) -> Result<String, String> {
        Err("dregg_mpt_lc_verify not exported by the linked archive (rebuild to enable)".into())
    }
}

// ============================================================================
// Mina (Ouroboros Samasika / Pickles) light-client verify (verified route-through)
// ============================================================================
//
// Routes the Mina finality decision through the Lean gate
// `Dregg2.Bridge.LightClientMinaGate.dregg_mina_lc_verify`, exactly as `verified_eth_lc_verify`
// routes the ETH verify. What it replaces is NOT a Rust twin of a proven rule set — it is an
// UNVERIFIED and, measured on the shipped code, largely absent check:
// `bridge/src/mina_observer.rs::observe_settlement` took the MAXIMUM `blockHeight` out of whatever
// `bestChain` returned, subtracted the settlement's submitted height, and accepted on the
// difference. The returned blocks were never checked to form a chain, and with the shipped
// `best_chain_length` far below a mainnet `confirmation_depth` the settlement's own block was not
// even in the window.
//
// The twin-deletion boundary is drawn where the other three gates draw theirs: the ANCHORED-SEGMENT
// LOGIC crosses to Lean (non-empty segment; `anchor_height <= submitted_height`, without which the
// depth is measured from outside the exhibited evidence; the WITNESSED depth meeting the Samasika
// requirement), while the crypto/codec PRIMITIVES stay in Rust as NAMED carriers supplied as their
// RESULTS:
//
//   * `link_ok`    — the Poseidon parent-linkage fold result over the exhibited headers (the
//                    `LINK_OK` carrier; `Dregg2.Circuit.Emit.LightClientMinaHashFold` DERIVES it
//                    from the chain rather than trusting a bit, and its terminal value IS the tip
//                    state hash).
//   * `pickles_ok` — the per-block Pickles/Kimchi Wrap-proof results (the IPA/FRI arc). ⚑ NO
//                    LONGER A CONSTANT: until 2026-07-29 the observer passed a compile-time
//                    `NEUTRAL_PICKLES_OK = true` here because it never fetched
//                    `protocolStateProof`. It now decodes every block's proof and asks
//                    `verified_mina_wrap_shape_ok` (below) for the PREAMBLE verdict. The arithmetic
//                    of a Wrap verify is still not in this bit — see that function's header for
//                    exactly what is and is not, and why the rest is fixture-bound.
//   * `canon_ok`   — the state-row canonicality results (`< p`). Poseidon's `absorbAt` enters every
//                    input through `(state + x) % p`, so a non-canonical field element is invisible
//                    at the digest and an anchor `A + p` reaches the same tip as `A`. DERIVED in
//                    Lean by the authored width gate `minaRowWidthGates` (254 bits, exact because
//                    `p > 2^254`).
//
// `LightClientMinaGate.minaVerifyDecision_refines` PROVES the gate's decision over these projections
// is DEFINITIONALLY `minaVerify` (axiom-FREE `rfl`), so gating the observer on
// `dregg_mina_lc_verify` gates it on the decision `mina_no_forgery` is proven over — and
// `minaVerifyDecision_depth_witnessed` turns an accept into "the confirmation depth is backed by
// that many exhibited, parent-linked, Pickles-proved blocks".
//
// ⚑ NOT decided by this gate, and not by anything else in the tree: FORK CHOICE. Samasika's chain
// selection (VRF-weighted density, long-range) is formalized nowhere, so two k-deep proved segments
// under different anchors are indistinguishable here. This is an anchored-segment verifier.
//
// ⚑ THIS EXPORT WAS ABSENT FROM EVERY ARCHIVE UNTIL 2026-07-29, under two successive wrong
// diagnoses. Neither "the gate is not rooted in `Dregg2.lean`" (it was, line 1536) nor "the
// committed SEED is stale" was the cause. The seed is not committed — `dregg-lean-ffi/.gitignore:7`
// ignores `*.a` and the file has never been tracked — and it carries NO splice-only export in any
// case. The cause was that `build.rs` builds one Lake target, `Dregg2.FFI`, and splices exactly
// `metatheory/Dregg2/FFI.lean`'s import closure; a module rooted only in `Dregg2.lean` elaborates
// but emits no `:c` facet. FIXED by importing both Mina gates in `Dregg2/FFI.lean`; the remedy for
// any archive still lacking them is a plain `cargo build`, which re-lake-builds and re-splices.
// Absent, this stays fail-CLOSED and loud: the observer refuses every settlement with
// `ObserveError::VerifiedGateUnavailable`.
//
// Wire grammar (mirrors `LightClientMinaGate.decodeMinaWire` byte-for-byte):
// ```text
// INPUT := "sl=" sl ";ah=" ah ";sh=" sh ";wd=" wd ";rd=" rd ";lk=" B ";pk=" B ";cn=" B
// B     := "0" | "1"
// ```

/// The verified decision the Mina anchored-segment finality claim reduces to. `Accept` iff the Lean
/// gate (`dregg_mina_lc_verify`) returned `"1"`; every other outcome (`"0"`, `"ERR"`, malformed,
/// archive-absent) is fail-closed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MinaLcVerdict {
    /// The verified gate ACCEPTED the projections (→ `minaVerify = true`, hence — with the named
    /// Pickles carrier sound — `MinaValidAt`, including the WITNESSED confirmation depth).
    Accept,
    /// The verified gate REJECTED (empty segment / submitted height below the anchor / depth not
    /// witnessed / failed linkage, Pickles or canonicality result / malformed).
    Reject,
}

/// Whether the linked archive exports the verified Mina light-client gate (`dregg_mina_lc_verify`,
/// spliced from `Dregg2.Bridge.LightClientMinaGate`). When false the caller must FAIL CLOSED —
/// there is no Rust twin to fall back to, and the pre-gate Rust path was not a check.
pub fn mina_lc_verify_available() -> bool {
    ffi_mina_lc::mina_lc_verify_present() && lean_init_once().is_ok()
}

/// Build the Mina verify wire from the exhibited-segment facts + the three carrier RESULTS. Mirrors
/// `LightClientMinaGate.decodeMinaWire`'s grammar exactly.
pub fn mina_lc_verify_wire(
    segment_len: u64,
    anchor_height: u64,
    submitted_height: u64,
    witnessed_depth: u64,
    required_depth: u64,
    link_ok: bool,
    pickles_ok: bool,
    canon_ok: bool,
) -> String {
    let b = |x: bool| if x { '1' } else { '0' };
    format!(
        "sl={segment_len};ah={anchor_height};sh={submitted_height};wd={witnessed_depth};rd={required_depth};lk={};pk={};cn={}",
        b(link_ok),
        b(pickles_ok),
        b(canon_ok),
    )
}

/// Run the VERIFIED gate `@[export] dregg_mina_lc_verify` over a pre-built wire and return the raw
/// output (`"1"` / `"0"` / `"ERR"`). Requires [`mina_lc_verify_available`]; returns `Err` when the
/// archive did not export it (so the caller distinguishes "archive missing" from "rejected" and
/// FAILS CLOSED either way).
pub fn shadow_mina_lc_verify(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi_mina_lc::lean_mina_lc_verify(wire)
}

/// The end-to-end verified Mina light-client query: build the wire from the projections, run the
/// gate, and decode to [`MinaLcVerdict`]. Returns `Ok(Accept)` ONLY on the gate's `"1"`; every other
/// gate output is `Ok(Reject)` (fail-closed). `Err` is returned ONLY when the archive lacks the
/// export — the caller must treat that as a REFUSAL, never as a skipped check.
pub fn verified_mina_lc_verify(
    segment_len: u64,
    anchor_height: u64,
    submitted_height: u64,
    witnessed_depth: u64,
    required_depth: u64,
    link_ok: bool,
    pickles_ok: bool,
    canon_ok: bool,
) -> Result<MinaLcVerdict, String> {
    let wire = mina_lc_verify_wire(
        segment_len,
        anchor_height,
        submitted_height,
        witnessed_depth,
        required_depth,
        link_ok,
        pickles_ok,
        canon_ok,
    );
    let out = shadow_mina_lc_verify(&wire)?;
    Ok(if out == "1" {
        MinaLcVerdict::Accept
    } else {
        MinaLcVerdict::Reject
    })
}

#[cfg(all(lean_lib_present, dregg_mina_lc_verify_present))]
mod ffi_mina_lc {
    use std::ffi::CString;
    use std::os::raw::c_char;

    extern "C" {
        fn dregg_mina_lc_verify_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
    }

    pub fn mina_lc_verify_present() -> bool {
        true
    }

    pub fn lean_mina_lc_verify(wire: &str) -> Result<String, String> {
        let c_in = CString::new(wire).map_err(|e| format!("wire has interior NUL: {e}"))?;
        let mut cap = wire.len() * 2 + 256;
        loop {
            let mut buf = vec![0u8; cap];
            let full = unsafe {
                dregg_mina_lc_verify_str(c_in.as_ptr(), buf.as_mut_ptr() as *mut c_char, cap)
            };
            if full == usize::MAX {
                return Err("dregg_mina_lc_verify_str: unusable output buffer".into());
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

#[cfg(not(all(lean_lib_present, dregg_mina_lc_verify_present)))]
mod ffi_mina_lc {
    pub fn mina_lc_verify_present() -> bool {
        false
    }

    pub fn lean_mina_lc_verify(_wire: &str) -> Result<String, String> {
        Err("dregg_mina_lc_verify not exported by the linked archive (rebuild to enable)".into())
    }
}

// ============================================================================
// Mina PER-BLOCK Pickles Wrap-proof PREAMBLE gate (verified route-through)
// ============================================================================
//
// This is what supplies the `pk` bit above, and it exists because that bit used to be a
// compile-time `true` named `NEUTRAL_PICKLES_OK`. The observer now fetches every block's
// `protocolStateProof`, decodes the binprot `Mina_base.Proof.Stable.V2` in Rust (a CODEC —
// `bridge/src/mina_pickles.rs`: no field arithmetic, no group arithmetic, both Lean-authored),
// and hands the resulting COUNTS here. `Dregg2.Bridge.PicklesWrapShapeGate.picklesWrapShapeOk`
// renders the verdict, and `picklesWrapShapeOk_is_shapeOkRec` proves that verdict IS
// `KimchiVerify.shapeOkRec` — the `verifier.rs:810-830` preamble — conjoined with two length
// agreements a recursive Wrap proof owes. `real_block_wrap_shape_accepts` pins the accept on the
// REAL devnet block 539508, and `real_block_wrap_shape_refused_by_freeze` pins that the retired
// `prevLen = 0` form REFUSES it.
//
// ⚑ SAY THE RESOLUTION OUT LOUD, because "the observer now checks the Pickles proof" is exactly
// the sentence that will be over-read. What an accept here means is: THE PREAMBLE PASSES. It is
// the first seven lines of `to_batch`. It does NOT mean the proof verifies, and the rest of the
// verify is NOT reachable from a deployed observer today, for two independent reasons:
//
//   1. DATA. Every arithmetic check this tree has on a real Mina block (`MinaRealBlockGate` C5/C8,
//      `MinaRealBlockTranscript` C3, the `MinaWrap*` group and opening rungs) is `by decide` over
//      LITERAL constants dumped by `metatheory/fixtures/pickles-extractors`, which links openmina
//      + o1-labs `proof-systems` to get the verifier index, the SRS, `endo_r`, the linearization
//      and the 40-element public input. None of that is on the wire — the proof's
//      `messages_for_next_step_proof.app_state` is literally `()` — and that dependency graph is
//      deliberately outside this workspace's lockfile.
//   2. COST. Those theorems are kernel `decide`s, not functions of a proof. Measured on ONE block
//      (`docs/MINA-REAL-BLOCK-GATE.md` §6.1): 82 s for C5/C8, 153 s + 75 s for the opening rung,
//      ~3.5 h of serial kernel and ~28 GB peak for the terminal `⟨s, srs.g⟩` MSM. A per-block cost
//      in hours is not a light client at any scale.
//
// So the honest shape of the residual is: the preamble is RUNTIME-EVALUABLE and now runs; the
// arithmetic is FIXTURE-BOUND and does not. The next rung that is genuinely runtime-evaluable is
// curve membership of the ~58 group elements the decoder already parses — compiled Lean over
// `ZMod`, microseconds per point — and it is deliberately NOT done in Rust.
//
// Wire grammar (mirrors `PicklesWrapShapeGate.decodeWrapShapeWire` byte-for-byte):
// ```text
// INPUT := "ip=" ip ";pc=" pc ";pv=" pv ";pl=" pl ";w=" w ";s=" s ";cf=" cf ";tc=" tc
//        ";ck=" ck ";ir=" ir ";pr=" pr
// ```

/// The verified verdict on a single block's Wrap-proof preamble. `Accept` iff the Lean gate
/// (`dregg_mina_wrap_shape_ok`) returned `"1"`; every other outcome (`"0"`, `"ERR"`, malformed,
/// archive-absent) is fail-closed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MinaWrapShapeVerdict {
    /// The gate ACCEPTED: the decoded proof has the shape the pinned verifier index demands.
    Accept,
    /// The gate REJECTED.
    Reject,
}

/// Whether the linked archive exports the verified per-block Wrap-preamble gate
/// (`dregg_mina_wrap_shape_ok`, spliced from `Dregg2.Bridge.PicklesWrapShapeGate`). When false the
/// caller must FAIL CLOSED — there is no Rust twin of this decision and reverting to
/// `NEUTRAL_PICKLES_OK` is the exact regression this replaced.
pub fn mina_wrap_shape_ok_available() -> bool {
    ffi_mina_wrap_shape::mina_wrap_shape_ok_present() && lean_init_once().is_ok()
}

/// Build the Wrap-preamble wire. `idx_*` are the PINNED verifier-index parameters (trusted
/// config); everything else is read out of the block's own proof by the Rust decoder.
#[allow(clippy::too_many_arguments)]
pub fn mina_wrap_shape_wire(
    idx_prev_challenges: usize,
    proof_prev_challenges: usize,
    proof_prev_challenge_vectors: usize,
    idx_public_len: usize,
    w_comm: usize,
    s_evals: usize,
    coefficients: usize,
    t_comm: usize,
    idx_chunk_size: usize,
    idx_ipa_rounds: usize,
    proof_ipa_rounds: usize,
) -> String {
    format!(
        "ip={idx_prev_challenges};pc={proof_prev_challenges};pv={proof_prev_challenge_vectors};\
         pl={idx_public_len};w={w_comm};s={s_evals};cf={coefficients};tc={t_comm};\
         ck={idx_chunk_size};ir={idx_ipa_rounds};pr={proof_ipa_rounds}"
    )
}

/// Run the VERIFIED gate `@[export] dregg_mina_wrap_shape_ok` over a pre-built wire and return the
/// raw output (`"1"` / `"0"` / `"ERR"`). Returns `Err` when the archive did not export it.
pub fn shadow_mina_wrap_shape_ok(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi_mina_wrap_shape::lean_mina_wrap_shape_ok(wire)
}

/// The end-to-end verified per-block Wrap-preamble query. `Ok(Accept)` ONLY on the gate's `"1"`;
/// every other gate output is `Ok(Reject)` (fail-closed). `Err` ONLY when the archive lacks the
/// export — the caller must treat that as a REFUSAL, never as a skipped check.
#[allow(clippy::too_many_arguments)]
pub fn verified_mina_wrap_shape_ok(
    idx_prev_challenges: usize,
    proof_prev_challenges: usize,
    proof_prev_challenge_vectors: usize,
    idx_public_len: usize,
    w_comm: usize,
    s_evals: usize,
    coefficients: usize,
    t_comm: usize,
    idx_chunk_size: usize,
    idx_ipa_rounds: usize,
    proof_ipa_rounds: usize,
) -> Result<MinaWrapShapeVerdict, String> {
    let wire = mina_wrap_shape_wire(
        idx_prev_challenges,
        proof_prev_challenges,
        proof_prev_challenge_vectors,
        idx_public_len,
        w_comm,
        s_evals,
        coefficients,
        t_comm,
        idx_chunk_size,
        idx_ipa_rounds,
        proof_ipa_rounds,
    );
    let out = shadow_mina_wrap_shape_ok(&wire)?;
    Ok(if out == "1" {
        MinaWrapShapeVerdict::Accept
    } else {
        MinaWrapShapeVerdict::Reject
    })
}

#[cfg(all(lean_lib_present, dregg_mina_wrap_shape_ok_present))]
mod ffi_mina_wrap_shape {
    use std::ffi::CString;
    use std::os::raw::c_char;

    extern "C" {
        fn dregg_mina_wrap_shape_ok_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
    }

    pub fn mina_wrap_shape_ok_present() -> bool {
        true
    }

    pub fn lean_mina_wrap_shape_ok(wire: &str) -> Result<String, String> {
        let c_in = CString::new(wire).map_err(|e| format!("wire has interior NUL: {e}"))?;
        let mut cap = wire.len() * 2 + 256;
        loop {
            let mut buf = vec![0u8; cap];
            let full = unsafe {
                dregg_mina_wrap_shape_ok_str(c_in.as_ptr(), buf.as_mut_ptr() as *mut c_char, cap)
            };
            if full == usize::MAX {
                return Err("dregg_mina_wrap_shape_ok_str: unusable output buffer".into());
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

#[cfg(not(all(lean_lib_present, dregg_mina_wrap_shape_ok_present)))]
mod ffi_mina_wrap_shape {
    pub fn mina_wrap_shape_ok_present() -> bool {
        false
    }

    pub fn lean_mina_wrap_shape_ok(_wire: &str) -> Result<String, String> {
        Err(
            "dregg_mina_wrap_shape_ok not exported by the linked archive (rebuild to enable)"
                .into(),
        )
    }
}

// ===========================================================================
// MINA — the PER-ADJACENT-PAIR Pickles PROOF-CHAIN gate (`dregg_mina_proof_chain_ok`)
// ===========================================================================
//
// ⚑ WHAT THIS BINDS, AND WHAT IT STILL DOES NOT.
//
// `mina_observer`'s per-step table carried a residual that made the whole per-block Pickles rung
// weaker than it looked: **the proof↔block binding — NOTHING CHECKED IT.** An endpoint could
// serve block A's proof under block B's header and every check passed — the Lean finality gate,
// the depth witness, the Base58Check decode and canonicality, the parent linkage, and the
// byte-exact `Mina_base.Proof.Stable.V2` decode feeding `dregg_mina_wrap_shape_ok`. In its cheap
// form that is not a subtle attack: ONE real Mina proof, replayed under 290 fabricated headers,
// manufactured any confirmation depth for free, and the "availability obligation" the
// `NEUTRAL_PICKLES_OK` retirement claimed to buy cost an adversary exactly one proof.
//
// The obstruction is structural and it does NOT go away here. A Wrap proof's
// `messages_for_next_step_proof.app_state` is literally `()` on the wire, so the proof does not
// carry the block it proves. The block enters only as the verifier-SUPPLIED `app_state`, hashed
// with the VK's `dlog_plonk_index` and the accumulators into ONE Poseidon digest that is
// **public-input slot 12 of 40**; the other 39 slots are functions of the proof alone. Turning
// slot 12 into a COMPARISON means assembling the whole public input, and six of those 40 words
// (`combined_inner_product`, `b`, `zeta_to_srs_length`, `zeta_to_domain_size`, `perm`, `xi`) are
// DROPPED from the wire proof and recoverable only by `expand_deferred` — the front half of a
// Kimchi verifier — plus a 40-point MSM and two sponges. That rung is
// `docs/MINA-REAL-BLOCK-GATE.md` §6 and it is NOT this.
//
// What IS closeable, and is closed here, is the OTHER binding. Pickles recursion makes block N's
// Step proof verify block N−1's Wrap proof, so block N's own bytes carry two fingerprints of its
// parent's proof, in the clear, comparable with zero arithmetic:
//
//   * `messages_for_next_step_proof.challenge_polynomial_commitments[0]` = the parent's
//     `bulletproof.challenge_polynomial_commitment` (`sg`), and
//   * `messages_for_next_step_proof.old_bulletproof_challenges[0]` = the parent's
//     `deferred_values.bulletproof_challenges` (16 of them).
//
// MEASURED on 40 consecutive real devnet blocks (539761…539800, 39 adjacent pairs): 39/39 on
// BOTH fingerprints, 40/40 distinct `sg`, 0 self-naming blocks, 0 non-adjacent coincidences.
//
// So an accepted segment must exhibit a GENUINE CONSECUTIVE RUN of real Mina Wrap proofs, in
// order, of the length claimed. Replay, shuffle, splice and pad are all refusals, and depth past
// the real chain's own production is a refusal. It is still NOT a proof↔`stateHash` binding: an
// adversary holding a genuine run can re-label the headers those proofs are served under.
//
// Wire grammar (mirrors `PicklesProofChainGate.decodeChainWire` byte-for-byte):
// ```text
// INPUT := "px=" Nat ";py=" Nat ";pc=" Nat("," Nat)*15
//        ";cx=" Nat ";cy=" Nat ";cc=" Nat("," Nat)*15
// ```

/// The verified verdict on one ADJACENT PAIR of exhibited blocks. `Accept` iff the Lean gate
/// (`dregg_mina_proof_chain_ok`) returned `"1"`; every other outcome (`"0"`, `"ERR"`, malformed,
/// archive-absent) is fail-closed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MinaProofChainVerdict {
    /// The gate ACCEPTED: the child's proof names the parent's proof, on both fingerprints.
    Accept,
    /// The gate REJECTED — the pair is UNBOUND, and an unbound pair is a refusal.
    Reject,
}

/// Whether the linked archive exports the verified proof-chain gate (`dregg_mina_proof_chain_ok`,
/// spliced from `Dregg2.Bridge.PicklesProofChainGate`). When false the caller must FAIL CLOSED:
/// there is no Rust twin of this decision, and a proof-chain check that silently does not run is
/// indistinguishable from the pre-2026-07-29 state in which no proof was bound to anything.
pub fn mina_proof_chain_ok_available() -> bool {
    ffi_mina_proof_chain::mina_proof_chain_ok_present() && lean_init_once().is_ok()
}

/// Render a 16-element challenge vector as the `,`-separated decimal list the wire carries.
fn chal_list(v: &[u128; 16]) -> String {
    let mut out = String::with_capacity(16 * 40);
    for (i, c) in v.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push_str(&c.to_string());
    }
    out
}

/// Build the proof-chain wire from the PARENT block's own fingerprint (`parent_sg_x`,
/// `parent_sg_y`, `parent_bp_challenges`) and the CHILD block's exhibited claim about it
/// (`child_acc_x`, `child_acc_y`, `child_acc_challenges`). The coordinates are decimal strings of
/// the decoded little-endian field elements — [`crate`]'s callers get them from
/// `bridge::mina_pickles::decimal_of_le32`, which is a base conversion, not field arithmetic.
pub fn mina_proof_chain_wire(
    parent_sg_x: &str,
    parent_sg_y: &str,
    parent_bp_challenges: &[u128; 16],
    child_acc_x: &str,
    child_acc_y: &str,
    child_acc_challenges: &[u128; 16],
) -> String {
    format!(
        "px={parent_sg_x};py={parent_sg_y};pc={};cx={child_acc_x};cy={child_acc_y};cc={}",
        chal_list(parent_bp_challenges),
        chal_list(child_acc_challenges),
    )
}

/// Run the VERIFIED gate `@[export] dregg_mina_proof_chain_ok` over a pre-built wire and return
/// the raw output (`"1"` / `"0"` / `"ERR"`). Returns `Err` when the archive did not export it.
pub fn shadow_mina_proof_chain_ok(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi_mina_proof_chain::lean_mina_proof_chain_ok(wire)
}

/// The end-to-end verified proof-chain query for one adjacent pair. `Ok(Accept)` ONLY on the
/// gate's `"1"`; every other gate output is `Ok(Reject)` (fail-closed). `Err` ONLY when the
/// archive lacks the export — the caller must treat that as a REFUSAL with its own distinct
/// error, never as a skipped check and never as a proved `no`.
pub fn verified_mina_proof_chain_ok(
    parent_sg_x: &str,
    parent_sg_y: &str,
    parent_bp_challenges: &[u128; 16],
    child_acc_x: &str,
    child_acc_y: &str,
    child_acc_challenges: &[u128; 16],
) -> Result<MinaProofChainVerdict, String> {
    let wire = mina_proof_chain_wire(
        parent_sg_x,
        parent_sg_y,
        parent_bp_challenges,
        child_acc_x,
        child_acc_y,
        child_acc_challenges,
    );
    let out = shadow_mina_proof_chain_ok(&wire)?;
    Ok(if out == "1" {
        MinaProofChainVerdict::Accept
    } else {
        MinaProofChainVerdict::Reject
    })
}

#[cfg(all(lean_lib_present, dregg_mina_proof_chain_ok_present))]
mod ffi_mina_proof_chain {
    use std::ffi::CString;
    use std::os::raw::c_char;

    extern "C" {
        fn dregg_mina_proof_chain_ok_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
    }

    pub fn mina_proof_chain_ok_present() -> bool {
        true
    }

    pub fn lean_mina_proof_chain_ok(wire: &str) -> Result<String, String> {
        let c_in = CString::new(wire).map_err(|e| format!("wire has interior NUL: {e}"))?;
        let mut cap = 256;
        loop {
            let mut buf = vec![0u8; cap];
            let full = unsafe {
                dregg_mina_proof_chain_ok_str(c_in.as_ptr(), buf.as_mut_ptr() as *mut c_char, cap)
            };
            if full == usize::MAX {
                return Err("dregg_mina_proof_chain_ok_str: unusable output buffer".into());
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

#[cfg(not(all(lean_lib_present, dregg_mina_proof_chain_ok_present)))]
mod ffi_mina_proof_chain {
    pub fn mina_proof_chain_ok_present() -> bool {
        false
    }

    pub fn lean_mina_proof_chain_ok(_wire: &str) -> Result<String, String> {
        Err(
            "dregg_mina_proof_chain_ok not exported by the linked archive (rebuild to enable)"
                .into(),
        )
    }
}

// ===========================================================================
// MINA — the PER-BLOCK proof↔`stateHash` DERIVATION (`dregg_mina_state_hash_word_ok`)
// ===========================================================================
//
// ⚑ WHAT THE BLOCK ACTUALLY IS, INSIDE A WRAP VERIFICATION.
//
// A Wrap proof's `messages_for_next_step_proof.app_state` is `()` on the wire. The block enters
// ONLY as the verifier-supplied `app_state`, and `blockchain_snark_state.ml:384` fixes that to one
// `Fp` element — the protocol-state hash. It is absorbed into a 93-element Poseidon over `Fp`
//
//     word12 = Poseidon_fp( index_to_field_elements(dlog_plonk_index)  // 56, the Wrap VK
//                         ‖ [state_hash]                               //  1, THE BLOCK
//                         ‖ (sg₀,chals₀ ‖ sg₁,chals₁) )                // 36, this proof
//
// and that digest is public-input WORD 12 OF 40. Word 11 is the analogous
// `messages_for_next_wrap_proof` digest, a 32-element Poseidon over `Fq`.
//
// MEASURED 2026-07-29 by `metatheory/fixtures/pickles-extractors/src/bin/state_hash_binding_export.rs`
// over six real devnet blocks (539795…539799 consecutive, plus the anchor 539508):
//   * `kimchi::verifier::verify` under each block's OWN `stateHash`  — 6/6 `Ok`;
//   * the same proofs under every FOREIGN `stateHash`                — 30/30 `Err`;
//   * public-input words other than 12 that move when only the header is swapped — ZERO.
// So a foreign header is refused by o1-labs' own verifier, and word 12 is the sole carrier.
//
// ⚑ WHAT THIS BINDING DOES NOT DO, AND THE MEASUREMENT THAT SETTLED IT.
//
// `docs/MINA-REAL-BLOCK-GATE.md` §8.5 proposed a cheap closed loop — word 12 → the 40 words →
// `public_comm` → the Fq-sponge → β, γ, α′, ζ′, "which ARE on the wire". THEY ARE NOT. The same
// run measured every adjacent pair of the six blocks: the child's
// `deferred_values.plonk.{beta,gamma,alpha,zeta}` matched the parent's Wrap oracles on 0/5, and
// the child's `sponge_digest_before_evaluations` matched the parent's Wrap `fq_digest` on 0/5. A
// Wrap statement's `deferred_values` describe the STEP proof it wrapped, not the previous Wrap.
// The only equation in `kimchi::verifier::verify` a wrong word 12 falsifies is therefore the
// TERMINAL IPA OPENING, whose honest per-block cost includes the 2^15-point `⟨s, srs.g⟩` MSM
// (rung 5h, unrooted at `228e51de7` for exactly that reason).
//
// So this is a DERIVATION with a decision over it, not a Wrap verification, and no caller may
// describe it as one. What it buys: the observer no longer treats a `stateHash` as a free-floating
// Base58 string — it hashes it, per block, in compiled Lean, and the digest it produces is welded
// (`Dregg2.Circuit.Emit.MinaWrapPublicInputFromHeader`) to the 40-word public input the whole
// in-kernel ladder is stated over, and (`word12_preimage_carries_the_chain_accumulator`) to the
// accumulator `dregg_mina_proof_chain_ok` compares against the parent block's own `sg`.
//
// Wire grammar (mirrors `MinaStateHashWordGate.decodeHeaderWire` byte-for-byte):
// ```text
// INPUT := "sh=" Nat ";acc=" Nat("," Nat)*35 ";mnw=" Nat("," Nat)*31 ";w12=" Nat ";w11=" Nat
// ```

/// The verified verdict on one exhibited block's header. `Accept` iff the Lean gate
/// (`dregg_mina_state_hash_word_ok`) returned `"1"`; every other outcome (`"0"`, `"ERR"`,
/// malformed, archive-absent) is fail-closed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MinaStateHashWordVerdict {
    /// The gate ACCEPTED: the served header and the served proof hash to the two public-input
    /// words the verification consumed.
    Accept,
    /// The gate REJECTED — the exhibited words are not this header's, and that is a refusal.
    Reject,
}

/// Whether the linked archive exports the verified header-derivation gate
/// (`dregg_mina_state_hash_word_ok`, spliced from `Dregg2.Bridge.MinaStateHashWordGate`). When
/// false the caller must FAIL CLOSED: there is no Rust twin of this Poseidon, and a derivation
/// that silently does not run is indistinguishable from the pre-2026-07-29 state in which no
/// arithmetic ever touched the served `stateHash`.
pub fn mina_state_hash_word_ok_available() -> bool {
    ffi_mina_state_hash_word::mina_state_hash_word_ok_present() && lean_init_once().is_ok()
}

/// Render a `,`-separated decimal list.
fn dec_list(v: &[String]) -> String {
    v.join(",")
}

/// Build the header-derivation wire. Every argument is a decoder READ rendered as a decimal (a
/// base conversion, not field arithmetic): `state_hash` is the Base58Check-decoded `stateHash`;
/// `acc_comm` is `[x₀, y₀, x₁, y₁]` of `messages_for_next_step_proof.challenge_polynomial_commitments`;
/// `acc_chals` is its `2 × 16` **RAW 128-bit** prechallenges; `mnw_comm` is `[x, y]` of
/// `messages_for_next_wrap_proof.challenge_polynomial_commitment`; `mnw_chals` is its `2 × 15`
/// raw prechallenges; `word12`/`word11` are the public-input words the caller claims the
/// verification consumed.
///
/// ⚑ The prechallenges go over RAW. The endomorphism expansion
/// (`ScalarChallenge::limbs_to_field`) is the GATE's — `MinaStateHashWordGate.expandTick` /
/// `expandTock` over `KimchiVerify.endoMap` — so there is no field arithmetic on this side of the
/// boundary to drift from the Lean.
pub fn mina_state_hash_word_wire(
    state_hash: &str,
    acc_comm: &[String],
    acc_chals: &[String],
    mnw_comm: &[String],
    mnw_chals: &[String],
    word12: &str,
    word11: &str,
) -> String {
    format!(
        "sh={state_hash};ac={};ah={};wc={};wh={};w12={word12};w11={word11}",
        dec_list(acc_comm),
        dec_list(acc_chals),
        dec_list(mnw_comm),
        dec_list(mnw_chals),
    )
}

/// Run the VERIFIED gate `@[export] dregg_mina_state_hash_word_ok` over a pre-built wire and
/// return the raw output (`"1"` / `"0"` / `"ERR"`). `Err` when the archive did not export it.
pub fn shadow_mina_state_hash_word_ok(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi_mina_state_hash_word::lean_mina_state_hash_word_ok(wire)
}

/// The end-to-end verified header-derivation query for one block. `Ok(Accept)` ONLY on the gate's
/// `"1"`; every other gate output is `Ok(Reject)` (fail-closed). `Err` ONLY when the archive lacks
/// the export — the caller must treat that as a REFUSAL with its own distinct error.
#[allow(clippy::too_many_arguments)]
pub fn verified_mina_state_hash_word_ok(
    state_hash: &str,
    acc_comm: &[String],
    acc_chals: &[String],
    mnw_comm: &[String],
    mnw_chals: &[String],
    word12: &str,
    word11: &str,
) -> Result<MinaStateHashWordVerdict, String> {
    let wire = mina_state_hash_word_wire(
        state_hash, acc_comm, acc_chals, mnw_comm, mnw_chals, word12, word11,
    );
    let out = shadow_mina_state_hash_word_ok(&wire)?;
    Ok(if out == "1" {
        MinaStateHashWordVerdict::Accept
    } else {
        MinaStateHashWordVerdict::Reject
    })
}

#[cfg(all(lean_lib_present, dregg_mina_state_hash_word_ok_present))]
mod ffi_mina_state_hash_word {
    use std::ffi::CString;
    use std::os::raw::c_char;

    extern "C" {
        fn dregg_mina_state_hash_word_ok_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
    }

    pub fn mina_state_hash_word_ok_present() -> bool {
        true
    }

    pub fn lean_mina_state_hash_word_ok(wire: &str) -> Result<String, String> {
        let c_in = CString::new(wire).map_err(|e| format!("wire has interior NUL: {e}"))?;
        let mut cap = 256;
        loop {
            let mut buf = vec![0u8; cap];
            let full = unsafe {
                dregg_mina_state_hash_word_ok_str(
                    c_in.as_ptr(),
                    buf.as_mut_ptr() as *mut c_char,
                    cap,
                )
            };
            if full == usize::MAX {
                return Err("dregg_mina_state_hash_word_ok_str: unusable output buffer".into());
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

#[cfg(not(all(lean_lib_present, dregg_mina_state_hash_word_ok_present)))]
mod ffi_mina_state_hash_word {
    pub fn mina_state_hash_word_ok_present() -> bool {
        false
    }

    pub fn lean_mina_state_hash_word_ok(_wire: &str) -> Result<String, String> {
        Err(
            "dregg_mina_state_hash_word_ok not exported by the linked archive (rebuild to enable)"
                .into(),
        )
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
        // Same posture for the TRUST-ROOT gate: no export ⇒ no rotation verdict ⇒ the light
        // client's trusted sync committee cannot advance at all.
        if !eth_committee_rotation_available() {
            assert!(verified_eth_committee_rotation(6, true).is_err());
        }
    }

    #[test]
    fn committee_rotation_wire_grammar_matches_lean_decodeCommitteeWire() {
        // The exact wires `LightClientEthGate`'s rotation `#guard`s use.
        assert_eq!(eth_committee_rotation_wire(5, true), "nl=5;nr=1");
        assert_eq!(eth_committee_rotation_wire(6, true), "nl=6;nr=1");
        assert_eq!(eth_committee_rotation_wire(7, false), "nl=7;nr=0");
    }

    /// The TRUST-ROOT gate discriminates through the real C shim + Lean archive. An always-accept
    /// rotation gate (the pre-gate Rust twin's failure mode — install any committee) fails the
    /// negative arms; an always-reject / always-`"ERR"` one fails the positive arms.
    #[test]
    fn committee_rotation_gate_discriminates_through_the_real_ffi() {
        if !crate::demand_lean(
            eth_committee_rotation_available(),
            "dregg_eth_committee_rotation ETH committee-rotation (trust-root) gate",
        ) {
            return;
        }
        // ACCEPT — both fork depths, branch reconstructing.
        assert_eq!(
            verified_eth_committee_rotation(5, true),
            Ok(EthCommitteeRotationVerdict::Rotate),
            "an Altair..Deneb depth-5 rotation that reconstructs must ROTATE"
        );
        assert_eq!(
            verified_eth_committee_rotation(6, true),
            Ok(EthCommitteeRotationVerdict::Rotate)
        );
        // REJECT — the branch does not reconstruct (a committee the state does not commit).
        assert_eq!(
            verified_eth_committee_rotation(6, false),
            Ok(EthCommitteeRotationVerdict::Refuse)
        );
        // REJECT — inadmissible depths, including 7, which the OTHER gate's finality conjunct
        // accepts. Two gates, two rules; the rotation path must not inherit the wrong one.
        for depth in [0usize, 1, 4, 7, 8] {
            assert_eq!(
                verified_eth_committee_rotation(depth, true),
                Ok(EthCommitteeRotationVerdict::Refuse),
                "depth {depth} must not be an admissible committee-rotation depth"
            );
        }
        // NON-CONSTANCY, stated as such: two wires one field apart get different verdicts.
        assert_ne!(
            verified_eth_committee_rotation(6, true),
            verified_eth_committee_rotation(7, true),
            "the rotation gate returned the SAME verdict across the depth boundary — it is a \
             constant, not a gate"
        );
        // Fail-closed on a malformed wire, and on the OTHER gate's wire.
        assert_eq!(
            shadow_eth_committee_rotation("garbage").as_deref(),
            Ok("ERR")
        );
        assert_eq!(
            shadow_eth_committee_rotation("cl=512;bl=512;pc=512;bls=1;fl=6;fr=1;el=4;er=1")
                .as_deref(),
            Ok("ERR")
        );
    }

    // ========================================================================
    // THE TEETH: the gate DISCRIMINATES through the real C shim + Lean archive
    // ========================================================================
    //
    // Everything above this line is a wire-FORMAT mirror: it proves what bytes `*_wire` emits and
    // nothing about what decides on them. A gate that is merely REACHABLE is not a gate. These
    // three tests drive the actual `dregg_*_lc_verify_str` shim into the actual archive and pin
    // both polarities on the sharpest available boundary, so a gate that has become a constant —
    // always-accept (the un-gated relayer this whole bridge exists to close) or always-reject (a
    // dead shim that merely looks safe) — FAILS here.
    //
    // WHY NOT `#[cfg(dregg_*_present)]`: that is precisely the mechanism that hid the hole. A
    // cfg-gated test module CEASES TO EXIST when the cfg is off and the crate reports the survivors
    // as green. These are ungated and route the absence through `demand_lean`, which panics under
    // `DREGG_TEST_REQUIRE_LEAN=1` (the CI/verification lane) and prints an honest SKIP otherwise.
    // Against the pre-fix tree — no `_str` shim, no cfg — `eth_lc_verify_available()` is false and
    // the armed lane fails on the missing export instead of passing on a hollow assertion.

    #[test]
    fn eth_gate_refuses_forged_updates_through_the_real_ffi() {
        if !crate::demand_lean(
            eth_lc_verify_available(),
            "dregg_eth_lc_verify ETH light-client gate",
        ) {
            return;
        }

        // ACCEPT — a genuine full-participation depth-6 (Altair..Deneb) update. Present so the
        // test cannot be satisfied by a shim that rejects everything.
        assert_eq!(
            verified_eth_lc_verify(512, 512, 512, true, 6, true, 4, true),
            Ok(EthLcVerdict::Accept),
            "the verified gate must ACCEPT a genuine update"
        );
        // ACCEPT — the EXACT-quorum boundary (3·342 = 1026 ≥ 1024 = 2·512) at Electra depth 7.
        assert_eq!(
            verified_eth_lc_verify(512, 512, 342, true, 7, true, 4, true),
            Ok(EthLcVerdict::Accept)
        );

        // REJECT — one BELOW the threshold (3·341 = 1023 < 1024). The sharpest tooth: it shows the
        // gate computes the ≥ 2/3 multiply-form threshold, not "somebody signed".
        assert_eq!(
            verified_eth_lc_verify(512, 512, 341, true, 6, true, 4, true),
            Ok(EthLcVerdict::Reject),
            "a SUB-QUORUM update (341/512 < 2/3) must be REFUSED"
        );
        // REJECT — a FORGED aggregate signature: everything else genuine, `blst` said no.
        assert_eq!(
            verified_eth_lc_verify(512, 512, 512, false, 6, true, 4, true),
            Ok(EthLcVerdict::Reject),
            "a failed BLS aggregate verify must be REFUSED"
        );
        // REJECT — a finality branch of an inadmissible DEPTH (5): the depth check is what stops a
        // proof rooted at the wrong generalized-index from being replayed as a finality proof.
        assert_eq!(
            verified_eth_lc_verify(512, 512, 512, true, 5, true, 4, true),
            Ok(EthLcVerdict::Reject),
            "a wrong-depth finality branch must be REFUSED"
        );
        // REJECT — the finality branch does NOT reconstruct into the attested state root.
        assert_eq!(
            verified_eth_lc_verify(512, 512, 512, true, 6, false, 4, true),
            Ok(EthLcVerdict::Reject),
            "a finality branch that does not reconstruct must be REFUSED"
        );
        // REJECT — the trusted committee is not exactly `syncCommitteeSize` (511 ≠ 512). Both
        // `committeeLen` and `bitsLen` are pinned to 512 by `syncDecision`, so a short committee
        // cannot be used to shrink the denominator the 2/3 threshold divides.
        assert_eq!(
            verified_eth_lc_verify(511, 512, 512, true, 6, true, 4, true),
            Ok(EthLcVerdict::Reject),
            "a committee that is not exactly 512 keys must be REFUSED"
        );
        // REJECT — the Nomad ZERO floor (`0 < participantCount`): nobody signed.
        assert_eq!(
            verified_eth_lc_verify(512, 512, 0, true, 6, true, 4, true),
            Ok(EthLcVerdict::Reject),
            "a zero-participant update must be REFUSED"
        );
        // REJECT — wrong execution-payload branch depth (3, not 4).
        assert_eq!(
            verified_eth_lc_verify(512, 512, 512, true, 6, true, 3, true),
            Ok(EthLcVerdict::Reject),
            "a wrong-depth execution branch must be REFUSED"
        );
        // REJECT — the execution payload does not reconstruct into the finalized body root.
        assert_eq!(
            verified_eth_lc_verify(512, 512, 512, true, 6, true, 4, false),
            Ok(EthLcVerdict::Reject),
            "an execution branch that does not reconstruct must be REFUSED"
        );

        // The RAW gate outputs, so we know we are reading the Lean verdict and not a Rust default:
        // exactly `"1"` / `"0"`, and `"ERR"` (fail-closed) on a malformed wire.
        let accept_raw = shadow_eth_lc_verify("cl=512;bl=512;pc=512;bls=1;fl=6;fr=1;el=4;er=1");
        let reject_raw = shadow_eth_lc_verify("cl=512;bl=512;pc=341;bls=1;fl=6;fr=1;el=4;er=1");
        assert_eq!(accept_raw.as_deref(), Ok("1"));
        assert_eq!(reject_raw.as_deref(), Ok("0"));
        assert_eq!(shadow_eth_lc_verify("garbage").as_deref(), Ok("ERR"));

        // THE STANDING NON-CONSTANCY CANARY. The two wires above differ in ONE field (`pc`,
        // 512 vs 341) and straddle the 2/3 threshold. If the gate ever becomes a CONSTANT —
        // always-accept (the un-gated relayer), always-reject (a dead but safe-looking shim),
        // always-`"ERR"` (a wire-grammar drift that silently fail-closes everything and would
        // otherwise satisfy every REJECT assertion above) — these two collapse to the same
        // answer and this fires. It is the assertion that cannot be satisfied by a gate that
        // decides nothing, which is the failure mode every other line here shares a blind spot for.
        assert_ne!(
            accept_raw, reject_raw,
            "the ETH gate returned the SAME verdict on both sides of the 2/3 quorum threshold — \
             it is a constant, not a gate"
        );
        // …and a malformed wire decodes to REJECT at the verdict layer, never to an accept.
        assert_eq!(
            shadow_eth_lc_verify("garbage").map(|o| if o == "1" {
                EthLcVerdict::Accept
            } else {
                EthLcVerdict::Reject
            }),
            Ok(EthLcVerdict::Reject)
        );
    }

    #[test]
    fn tm_wire_grammar_matches_lean_decodeTmWire() {
        // The exact accepting witness `LightClientTendermintGate.tm_decision_discriminates` /
        // `#guard`s use, so a differential run (when the archive is present) is byte-identical.
        assert_eq!(
            tm_lc_verify_wire(5, 5, 11, 10, 50, 55, 60, 5, 100, true, true, 3, 3),
            "ci=5;tci=5;h=11;th=10;ht=50;t=55;nw=60;cd=5;tp=100;eb=1;vb=1;tot=3;sp=3"
        );
        // The exactly-2/3 sub-quorum reject witness (`sp=2`).
        assert_eq!(
            tm_lc_verify_wire(5, 5, 11, 10, 50, 55, 60, 5, 100, true, true, 3, 2),
            "ci=5;tci=5;h=11;th=10;ht=50;t=55;nw=60;cd=5;tp=100;eb=1;vb=1;tot=3;sp=2"
        );
    }

    #[test]
    fn mpt_wire_grammar_matches_lean_decodeMptWire() {
        // The exact accepting witness `LightClientMptGate.mpt_decision_discriminates` / `#guard`s use.
        assert_eq!(
            mpt_lc_verify_wire("5", "100", "100", "1", "1", "0", "0", true, true),
            "bal=5;sr=100;tsr=100;tk=1;ttk=1;ms=0;tms=0;ap=1;sp=1"
        );
        // The zero-balance-floor reject witness (`bal=0`).
        assert_eq!(
            mpt_lc_verify_wire("0", "100", "100", "1", "1", "0", "0", true, true),
            "bal=0;sr=100;tsr=100;tk=1;ttk=1;ms=0;tms=0;ap=1;sp=1"
        );
    }

    #[test]
    fn tm_mpt_fail_closed_when_export_absent() {
        // Same fail-closed posture as ETH: archive-absent ⇒ the verdict query errs (caller REJECTS).
        if !tm_lc_verify_available() {
            assert!(
                verified_tm_lc_verify(5, 5, 11, 10, 50, 55, 60, 5, 100, true, true, 3, 3).is_err()
            );
        }
        if !mpt_lc_verify_available() {
            assert!(
                verified_mpt_lc_verify("5", "100", "100", "1", "1", "0", "0", true, true).is_err()
            );
        }
    }

    #[test]
    fn tm_gate_refuses_forged_headers_through_the_real_ffi() {
        if !crate::demand_lean(
            tm_lc_verify_available(),
            "dregg_tm_lc_verify Tendermint light-client gate",
        ) {
            return;
        }

        // ACCEPT — a genuine adjacent advance, full stake signed, both hash bindings hold.
        assert_eq!(
            verified_tm_lc_verify(5, 5, 11, 10, 50, 55, 60, 5, 100, true, true, 3, 3),
            Ok(TmLcVerdict::Accept)
        );
        // REJECT — EXACTLY 2/3 signed (2·3 = 6 ≮ 3·2 = 6). The threshold is STRICT `>`, and this
        // is the case a `>=` transcription would wrongly admit.
        assert_eq!(
            verified_tm_lc_verify(5, 5, 11, 10, 50, 55, 60, 5, 100, true, true, 3, 2),
            Ok(TmLcVerdict::Reject),
            "exactly-2/3 signed power must be REFUSED (the threshold is strict)"
        );
        // REJECT — a header from a DIFFERENT chain (the cross-chain replay).
        assert_eq!(
            verified_tm_lc_verify(6, 5, 11, 10, 50, 55, 60, 5, 100, true, true, 3, 3),
            Ok(TmLcVerdict::Reject),
            "a chain-id mismatch must be REFUSED"
        );
        // REJECT — the epoch binding fails: the trusted `next_validators_hash` does not match the
        // hash of the supplied validator set (a swapped validator set).
        assert_eq!(
            verified_tm_lc_verify(5, 5, 11, 10, 50, 55, 60, 5, 100, false, true, 3, 3),
            Ok(TmLcVerdict::Reject),
            "a failed epoch binding must be REFUSED"
        );
        // REJECT — the header does not self-bind its own validator set.
        assert_eq!(
            verified_tm_lc_verify(5, 5, 11, 10, 50, 55, 60, 5, 100, true, false, 3, 3),
            Ok(TmLcVerdict::Reject),
            "a failed validator-set self binding must be REFUSED"
        );

        let accept_raw = shadow_tm_lc_verify(
            "ci=5;tci=5;h=11;th=10;ht=50;t=55;nw=60;cd=5;tp=100;eb=1;vb=1;tot=3;sp=3",
        );
        let reject_raw = shadow_tm_lc_verify(
            "ci=5;tci=5;h=11;th=10;ht=50;t=55;nw=60;cd=5;tp=100;eb=1;vb=1;tot=3;sp=2",
        );
        assert_eq!(accept_raw.as_deref(), Ok("1"));
        assert_eq!(reject_raw.as_deref(), Ok("0"));
        assert_eq!(shadow_tm_lc_verify("garbage").as_deref(), Ok("ERR"));

        // THE STANDING NON-CONSTANCY CANARY (see the ETH test): the two wires differ in ONE field
        // (`sp`, 3 vs 2) and straddle the STRICT `> 2/3` stake threshold. A constant gate — or a
        // `>=` transcription that admits the exactly-2/3 boundary — collapses them and fires this.
        assert_ne!(
            accept_raw, reject_raw,
            "the Tendermint gate returned the SAME verdict on both sides of the strict 2/3 stake \
             threshold — it is a constant, not a gate"
        );
    }

    #[test]
    fn mpt_gate_refuses_forged_holdings_through_the_real_ffi() {
        if !crate::demand_lean(
            mpt_lc_verify_available(),
            "dregg_mpt_lc_verify EVM-inclusion light-client gate",
        ) {
            return;
        }

        // ACCEPT — a genuine holding: nonzero balance, all three anchors match the trusted ones,
        // both keccak path walks opened.
        assert_eq!(
            verified_mpt_lc_verify("5", "100", "100", "1", "1", "0", "0", true, true),
            Ok(MptLcVerdict::Accept)
        );
        // REJECT — the Nomad-law ZERO floor: a zero-balance "holding" claims nothing and must not
        // be admitted as governance weight.
        assert_eq!(
            verified_mpt_lc_verify("0", "100", "100", "1", "1", "0", "0", true, true),
            Ok(MptLcVerdict::Reject),
            "a zero claimed balance must be REFUSED (the Nomad-law floor)"
        );
        // REJECT — the proof opens under a state root that is NOT the trusted anchor. This is the
        // forged-anchor attack: a perfectly valid MPT proof against an attacker-chosen root.
        assert_eq!(
            verified_mpt_lc_verify("5", "999", "100", "1", "1", "0", "0", true, true),
            Ok(MptLcVerdict::Reject),
            "a proof against an UNTRUSTED state root must be REFUSED"
        );
        // REJECT — the wrong token contract (a holding in some other ERC-20).
        assert_eq!(
            verified_mpt_lc_verify("5", "100", "100", "9", "1", "0", "0", true, true),
            Ok(MptLcVerdict::Reject),
            "a holding in the WRONG token must be REFUSED"
        );
        // REJECT — the wrong balances mapping slot (reading some other mapping's storage).
        assert_eq!(
            verified_mpt_lc_verify("5", "100", "100", "1", "1", "7", "0", true, true),
            Ok(MptLcVerdict::Reject),
            "a proof against the WRONG mapping slot must be REFUSED"
        );
        // REJECT — the account trie walk failed (no such account under the state root).
        assert_eq!(
            verified_mpt_lc_verify("5", "100", "100", "1", "1", "0", "0", false, true),
            Ok(MptLcVerdict::Reject),
            "a failed account-proof walk must be REFUSED"
        );
        // REJECT — the storage trie walk failed (the slot does not open to the claimed balance).
        assert_eq!(
            verified_mpt_lc_verify("5", "100", "100", "1", "1", "0", "0", true, false),
            Ok(MptLcVerdict::Reject),
            "a failed storage-proof walk must be REFUSED"
        );

        let accept_raw =
            shadow_mpt_lc_verify("bal=5;sr=100;tsr=100;tk=1;ttk=1;ms=0;tms=0;ap=1;sp=1");
        let reject_raw =
            shadow_mpt_lc_verify("bal=0;sr=100;tsr=100;tk=1;ttk=1;ms=0;tms=0;ap=1;sp=1");
        assert_eq!(accept_raw.as_deref(), Ok("1"));
        assert_eq!(reject_raw.as_deref(), Ok("0"));
        assert_eq!(shadow_mpt_lc_verify("garbage").as_deref(), Ok("ERR"));

        // THE STANDING NON-CONSTANCY CANARY (see the ETH test): the two wires differ in ONE field
        // (`bal`, 5 vs 0) and straddle the Nomad-law zero floor. A constant gate collapses them.
        assert_ne!(
            accept_raw, reject_raw,
            "the EVM-inclusion gate returned the SAME verdict across the zero-balance floor — \
             it is a constant, not a gate"
        );
    }

    /// ⚑ The MINA anchored-segment gate, through the REAL FFI. UNGATED on purpose — like its
    /// ETH/TM/MPT siblings it routes archive-absence through `demand_lean` (which PANICS under
    /// `DREGG_TEST_REQUIRE_LEAN=1`) rather than ceasing to exist the way a
    /// `#[cfg(dregg_mina_lc_verify_present)]` module does. The values are
    /// `LightClientMinaGate.mina_decision_discriminates`' own, so a divergence between the
    /// deployed gate and the theorem shows up here.
    #[test]
    fn mina_gate_refuses_forged_segments_through_the_real_ffi() {
        if !crate::demand_lean(
            mina_lc_verify_available(),
            "dregg_mina_lc_verify Mina anchored-segment light-client gate",
        ) {
            return;
        }

        // ACCEPT — a genuine 290-deep anchored segment above anchor 1000, settled at 1000.
        assert_eq!(
            verified_mina_lc_verify(290, 1000, 1000, 290, 290, true, true, true),
            Ok(MinaLcVerdict::Accept)
        );
        // REJECT — an EMPTY segment (zero exhibited evidence).
        assert_eq!(
            verified_mina_lc_verify(0, 1000, 1000, 290, 290, true, true, true),
            Ok(MinaLcVerdict::Reject),
            "an empty segment must be REFUSED"
        );
        // REJECT — ⚑ the SHIPPED defect's shape: a settlement claimed BELOW the pinned anchor, so
        // the "depth" comes from outside the exhibited evidence.
        assert_eq!(
            verified_mina_lc_verify(1, 1000, 0, 1001, 290, true, true, true),
            Ok(MinaLcVerdict::Reject),
            "a settlement claimed below the anchor must be REFUSED"
        );
        // REJECT — depth one short of the requirement.
        assert_eq!(
            verified_mina_lc_verify(289, 1000, 1000, 289, 290, true, true, true),
            Ok(MinaLcVerdict::Reject),
            "an under-deep settlement must be REFUSED"
        );
        // REJECT — each of the three carrier RESULTS false in turn: linkage, Pickles, canonicality.
        for (lk, pk, cn, what) in [
            (false, true, true, "a failed Poseidon linkage fold"),
            (true, false, true, "a failed Pickles Wrap proof"),
            (
                true,
                true,
                false,
                "a non-canonical state row (the `+p` anchor-substitution family)",
            ),
        ] {
            assert_eq!(
                verified_mina_lc_verify(290, 1000, 1000, 290, 290, lk, pk, cn),
                Ok(MinaLcVerdict::Reject),
                "{what} must be REFUSED"
            );
        }

        let accept_raw =
            shadow_mina_lc_verify("sl=290;ah=1000;sh=1000;wd=290;rd=290;lk=1;pk=1;cn=1");
        let reject_raw =
            shadow_mina_lc_verify("sl=289;ah=1000;sh=1000;wd=289;rd=290;lk=1;pk=1;cn=1");
        assert_eq!(accept_raw.as_deref(), Ok("1"));
        assert_eq!(reject_raw.as_deref(), Ok("0"));
        assert_eq!(shadow_mina_lc_verify("garbage").as_deref(), Ok("ERR"));
        // Fail-closed on a malformed wire, not a permissive parse: a truncated field list and a
        // non-bit flag are both "ERR", never "1".
        assert_eq!(
            shadow_mina_lc_verify("sl=290;ah=1000;sh=1000;wd=290;rd=290;lk=1;pk=1").as_deref(),
            Ok("ERR")
        );
        assert_eq!(
            shadow_mina_lc_verify("sl=290;ah=1000;sh=1000;wd=290;rd=290;lk=1;pk=1;cn=2").as_deref(),
            Ok("ERR")
        );

        // THE STANDING NON-CONSTANCY CANARY: the two wires straddle the depth requirement by ONE.
        assert_ne!(
            accept_raw, reject_raw,
            "the Mina gate returned the SAME verdict on both sides of the confirmation-depth \
             requirement — it is a constant, not a gate"
        );
    }

    /// ⚑ The per-block Pickles Wrap-PREAMBLE gate, through the REAL FFI, on the shape of a REAL
    /// devnet block (539508 — the object o1-labs' own `kimchi::verifier::verify` accepts). The
    /// accept is `PicklesWrapShapeGate.real_block_wrap_shape_accepts`' tuple and the rejects are
    /// `real_block_wrap_shape_discriminates`' single-count tampers, so an accept here is not
    /// compatible with a decision that accepts everything.
    #[test]
    fn mina_wrap_shape_gate_discriminates_through_the_real_ffi() {
        if !crate::demand_lean(
            mina_wrap_shape_ok_available(),
            "dregg_mina_wrap_shape_ok Pickles Wrap-preamble gate",
        ) {
            return;
        }

        // The real block's decoded counts: idx_prev 2 · proof_prev 2 · vectors 2 · public 40 ·
        // w_comm 15 · s_evals 6 (PERMUTS-1) · coefficients 15 · t_comm 7 · chunk_size 1 ·
        // idx IPA rounds 15 (k = log2 2^15) · proof lr.len() 15.
        const OK: [usize; 11] = [2, 2, 2, 40, 15, 6, 15, 7, 1, 15, 15];
        let call = |v: [usize; 11]| {
            verified_mina_wrap_shape_ok(
                v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], v[9], v[10],
            )
        };
        assert_eq!(
            call(OK),
            Ok(MinaWrapShapeVerdict::Accept),
            "the verified gate must ACCEPT a real Mina block's Wrap shape"
        );

        // Every single-count tamper is REFUSED — including the retired `prevLen = 0` freeze, which
        // rejected Mina itself.
        for (idx, val, what) in [
            (0usize, 0usize, "the retired `prevLen = 0` freeze"),
            (
                0,
                1,
                "the index declaring fewer accumulators than the proof carries",
            ),
            (
                1,
                1,
                "the proof carrying fewer accumulators than the index declares",
            ),
            (2, 1, "commitments and challenge vectors disagreeing"),
            (3, 0, "no public input"),
            (4, 14, "14 witness commitments"),
            (5, 5, "5 σ evaluations"),
            (6, 14, "14 coefficient columns"),
            (7, 8, "8 quotient chunks at chunk_size 1"),
            (8, 2, "a chunked index"),
            (10, 14, "a short IPA: 14 rounds against a 2^15 SRS"),
        ] {
            let mut bad = OK;
            bad[idx] = val;
            assert_eq!(
                call(bad),
                Ok(MinaWrapShapeVerdict::Reject),
                "{what} must be REFUSED"
            );
        }

        let accept_raw =
            shadow_mina_wrap_shape_ok(&mina_wrap_shape_wire(2, 2, 2, 40, 15, 6, 15, 7, 1, 15, 15));
        let reject_raw =
            shadow_mina_wrap_shape_ok(&mina_wrap_shape_wire(2, 2, 2, 40, 15, 6, 15, 7, 1, 15, 14));
        assert_eq!(accept_raw.as_deref(), Ok("1"));
        assert_eq!(reject_raw.as_deref(), Ok("0"));
        assert_eq!(shadow_mina_wrap_shape_ok("garbage").as_deref(), Ok("ERR"));

        // THE STANDING NON-CONSTANCY CANARY: the two wires differ in ONE field (`pr`, 15 vs 14).
        assert_ne!(
            accept_raw, reject_raw,
            "the Wrap-preamble gate returned the SAME verdict on a proof with one fewer IPA round \
             — it is a constant, not a gate"
        );
    }
}
