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
// ⚑ NOT decided by THIS gate: FORK CHOICE. It is an anchored-segment verifier, so two k-deep proved
// segments under different anchors are indistinguishable to it. ⚑ CORRECTED 2026-07-30: the old
// wording here was "and not by anything else in the tree ... formalized nowhere", and that is no
// longer true. `verified_mina_better_tip` / `verified_mina_head_advance` (below) run Samasika's
// `select` over binprot protocol states off the peer-to-peer wire. The scope limit on this gate is
// real; the claim about the tree was stale.
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
// INPUT := "sh=" Nat ";ac=" Nat("," Nat)*3 ";ah=" Nat("," Nat)*31 ";wc=" Nat("," Nat)
//        ";wh=" Nat("," Nat)*29 ";sg=" Nat("," Nat) ";w12=" Nat ";w11=" Nat
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
/// raw prechallenges; `sg` is `[x, y]` of THIS block's own Wrap
/// `bulletproof.challenge_polynomial_commitment` (Pallas, `Fp`); `word12`/`word11` are the
/// public-input words the caller claims the verification consumed.
///
/// ⚑ FLAG DAY 2026-07-29: the wire gained `;sg=` and is now EIGHT segments. A seven-segment wire
/// no longer decodes — `MinaStateHashWordGate.decodeHeaderWire` returns `none`, the gate answers
/// `"ERR"`, and every caller treats that as a REFUSAL. The old shape does not reinterpret.
///
/// ⚑ The prechallenges go over RAW. The endomorphism expansion
/// (`ScalarChallenge::limbs_to_field`) is the GATE's — `MinaStateHashWordGate.expandTick` /
/// `expandTock` over `KimchiVerify.endoMap` — so there is no field arithmetic on this side of the
/// boundary to drift from the Lean.
#[allow(clippy::too_many_arguments)]
pub fn mina_state_hash_word_wire(
    state_hash: &str,
    acc_comm: &[String],
    acc_chals: &[String],
    mnw_comm: &[String],
    mnw_chals: &[String],
    sg: &[String],
    word12: &str,
    word11: &str,
) -> String {
    format!(
        "sh={state_hash};ac={};ah={};wc={};wh={};sg={};w12={word12};w11={word11}",
        dec_list(acc_comm),
        dec_list(acc_chals),
        dec_list(mnw_comm),
        dec_list(mnw_chals),
        dec_list(sg),
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
    sg: &[String],
    word12: &str,
    word11: &str,
) -> Result<MinaStateHashWordVerdict, String> {
    let wire = mina_state_hash_word_wire(
        state_hash, acc_comm, acc_chals, mnw_comm, mnw_chals, sg, word12, word11,
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

// ===========================================================================
// MINA — THE ACCOUNT OPENING (`dregg_mina_account_state_ok`)
// ===========================================================================
//
// ⚑ THE FIRST THING IN THIS TREE THAT READS MINA *STATE* RATHER THAN MINA'S CHAIN.
//
// Everything above this line decides about headers, proofs and forks: `lc_verify`, `better_tip`,
// `head_advance`, `proof_chain_ok`, `state_hash_word_ok`, `wrap_shape_ok`. Not one of them can
// observe a balance, a nonce, or where a stake is delegated. dregg could follow Mina and could not
// see anything *in* it.
//
// `Blockchain_state.staged_ledger_hash.non_snark.ledger_hash` IS the Merkle root of Mina's account
// ledger, and `MinaBinprot` has decoded it since `Blockchain_state` stopped being discarded. So an
// account plus a 35-level opening against that root is a statement about Mina STATE, anchored in a
// header whose identity `MinaStateHashDerive` re-derives from the same bytes.
//
// ⚑ THE ROOT IS DECODED, NEVER SUPPLIED. There is no argument on this side by which a caller names
// the ledger hash it wants to open against: `accountInBlockLedger` runs
// `decodeProtocolStateRawChecked` over the exhibited bytes and reads the root out of the result.
// A decode refusal is a gate refusal (`the_gate_refuses_when_the_decode_refuses`), never a
// pass-through.
//
// ⚑ AND THERE IS NO RUST TWIN, deliberately. A Rust `Account.to_input` would be a re-rendering of
// openmina's `account.rs` — which of the account's fields are in the leaf preimage and in what
// order IS the whole content of the claim "this account holds this balance" — and its correctness
// would be a differential test against another implementation. `Dregg2.Bridge.MinaAccountOpening`'s
// header enumerates six ways to read that layout wrong (the `Fields.fold` order is REVERSED and
// there is no `List.rev`; the prefixes are `Mina*` not `Coda*`; `Merkle_path.t`'s tag names YOUR
// node's side, not the sibling's; `Untimed` carries `vesting_period = 1`, not 0; `txn_version` sits
// INSIDE the controller run; an `Auth_required` is THREE one-bit chunks, not one three-bit chunk) —
// every one of them still parses, still hashes, and fails the live-block guard. Rust here formats
// decimals, hex and `key=value`, and decides nothing.
//
// ⚑ WHAT AN ACCEPT MEANS, AND WHAT IT DOES NOT. It says: at the tip whose protocol-state bytes
// these are, Mina's ledger contained an account with this public key, balance, nonce and delegate
// at leaf index *i*. It says NOTHING about that tip's canonicity — that is
// `dregg_mina_better_tip` / `dregg_mina_head_advance`'s question, and whether the header is the
// block it claims to be is `MinaStateHashDerive`'s. The three compose; this one does not subsume
// them, and no caller may describe an account accept as "the account is on Mina's best chain".
//
// Wire grammar (mirrors `MinaAccountOpening.decodeAccountWire`, 15 `;`-separated segments):
// ```text
// INPUT := "blk="  lowercase hex of the Protocol_state.Value.Stable.V2 PREFIX
//        ";pk="   Nat "," Bool01     ";tk="  Nat        ";ts="  Nat      ";bal=" Nat
//        ";non="  Nat                ";rch=" Nat        ";dlg=" Nat "," Bool01
//        ";vf="   Nat                ";tm="  Bool01 "," Nat*5
//        ";perm=" Auth("|"Auth)*5 "|" Nat "|" Auth("|"Auth)*5
//        ";zk="   "" | Nat           ";idx=" Nat        ";sib=" Nat("," Nat)*
//        ";dir="  ("0"|"1")*
// ```

/// The thirteen permission controllers of a Mina account, in **DECLARATION order** — which is also
/// the absorb order, because `Permissions.Poly.to_input` ends in `|> List.rev` while
/// `Account.to_input` does not. One file, two directions; the reversal that applies to the account
/// does NOT apply here.
///
/// ⚑ Each controller is a `String` and NOT a Rust enum, on purpose. The six admissible tokens
/// (`None`, `Either`, `Proof`, `Signature`, `Impossible`, `Both`) are `Auth_required`'s OCaml
/// `to_string`, and `MinaAccountOpening.parseAuth?` is the ONE place in this repo that knows them.
/// A Rust enum would need a `to_string` table, and that table is a second reading of Mina's
/// encoding that could drift from the first. An unrecognised token is not a Rust error: the gate
/// answers `"ERR"`, which every caller treats as a refusal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MinaAccountPermissions {
    /// `edit_state`.
    pub edit_state: String,
    /// `access`.
    pub access: String,
    /// `send`.
    pub send: String,
    /// `receive`.
    pub receive: String,
    /// `set_delegate`.
    pub set_delegate: String,
    /// `set_permissions`.
    pub set_permissions: String,
    /// `set_verification_key.auth`.
    pub set_verification_key: String,
    /// `set_verification_key.txn_version` — `Mina_numbers.Txn_version`, 32 bits, absorbed BETWEEN
    /// `set_verification_key` and `set_zkapp_uri`. A decimal, not an `Auth`.
    pub txn_version: String,
    /// `set_zkapp_uri`.
    pub set_zkapp_uri: String,
    /// `edit_action_state`.
    pub edit_action_state: String,
    /// `set_token_symbol`.
    pub set_token_symbol: String,
    /// `increment_nonce`.
    pub increment_nonce: String,
    /// `set_voting_for`.
    pub set_voting_for: String,
    /// `set_timing`.
    pub set_timing: String,
}

/// One exhibited (block, account, opening) triple — everything `dregg_mina_account_state_ok`
/// decides over.
///
/// ⚑ EVERY FIELD ELEMENT IS A DECIMAL `String`. `public_key_x`, `token_id`, `receipt_chain_hash`,
/// `delegate_x`, `voting_for` and every sibling hash are elements of `Fp`, i.e. **255-bit**
/// integers. `u64` cannot hold one and `u128` cannot either; a numeric field here would silently
/// truncate a real account into a different account. `balance`/`nonce`/the timing fields are
/// bounded (64/32 bits) but are decimals too, so that one convention covers the wire.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MinaAccountOpeningInput {
    /// The binprot `Protocol_state.Value.Stable.V2` bytes as a peer served them. A PREFIX is
    /// enough — the gate decodes the protocol state and ignores whatever follows — and the bytes
    /// go over as bytes precisely so that nothing on this side interprets them.
    pub protocol_state_prefix: Vec<u8>,
    /// `public_key.x`, decimal.
    pub public_key_x: String,
    /// `public_key.is_odd`.
    pub public_key_is_odd: bool,
    /// `token_id`, decimal; the default (MINA) token is `1`.
    pub token_id: String,
    /// `token_symbol` as `Token_symbol.to_field` — the ≤ 6 bytes read LITTLE-endian. The empty
    /// symbol is `0`.
    pub token_symbol: String,
    /// `balance`, in nanomina.
    pub balance: String,
    /// `nonce`.
    pub nonce: String,
    /// `receipt_chain_hash`, decimal.
    pub receipt_chain_hash: String,
    /// `delegate.x`, decimal — `0` when the account delegates to nobody
    /// (`Public_key.Compressed.empty`).
    pub delegate_x: String,
    /// `delegate.is_odd`.
    pub delegate_is_odd: bool,
    /// `voting_for`, decimal; `State_hash.dummy` is `0`.
    pub voting_for: String,
    /// `timing = Timed _` when true. ⚑ When FALSE the five fields below are IGNORED by the gate —
    /// `Untimed` absorbs the constant `vesting_period = 1` and zeros elsewhere — so an honest
    /// caller may leave them `"0"`, and a caller that fills them cannot change the verdict.
    pub is_timed: bool,
    /// `timing.initial_minimum_balance`.
    pub initial_minimum_balance: String,
    /// `timing.cliff_time`.
    pub cliff_time: String,
    /// `timing.cliff_amount`.
    pub cliff_amount: String,
    /// `timing.vesting_period`.
    pub vesting_period: String,
    /// `timing.vesting_increment`.
    pub vesting_increment: String,
    /// The thirteen controllers plus the txn version.
    pub permissions: MinaAccountPermissions,
    /// `None` = the account has NO zkApp, and the leaf preimage then carries
    /// `Zkapp_account.default_digest`. ⚑ That is a CLAIM, not a default: an account that does have
    /// a zkApp does not open under it.
    pub zkapp_digest: Option<String>,
    /// The account's leaf index in the ledger. The opening's directions must spell it out bit by
    /// bit, LSB at the leaf — that is the second, independent answer a server gives about the same
    /// fact, and disagreement is a refusal rather than a preference.
    pub leaf_index: u64,
    /// The 35 sibling hashes, **LEAF FIRST**, as decimals.
    pub siblings: Vec<String>,
    /// The 35 `Merkle_path` tags, LEAF FIRST. ⚑ `true` means the ACCUMULATOR is the LEFT operand
    /// (`Merkle_path.t = Left of hash` names the position of YOUR node, not the sibling's). A
    /// reader who takes it as "the sibling is on the left" transposes every level; the index is the
    /// cross-check.
    pub node_is_left: Vec<bool>,
}

/// Whether the linked archive exports the verified account-opening gate
/// (`dregg_mina_account_state_ok`, spliced from `Dregg2.Bridge.MinaAccountOpening`). When false the
/// caller must FAIL CLOSED and report the absence: there is no Rust twin of this leaf hash, and a
/// balance that silently goes unchecked is indistinguishable from a balance a peer asserted.
pub fn mina_account_state_ok_available() -> bool {
    ffi_mina_account_state::mina_account_state_ok_present() && lean_init_once().is_ok()
}

/// Render `Bool01`.
fn bool01(b: bool) -> &'static str {
    if b {
        "1"
    } else {
        "0"
    }
}

/// Build the account-opening wire. Pure formatting: hex for the block bytes, decimals passed
/// through as given, `0`/`1` for every boolean, and `|` / `,` / `;` joins. No arithmetic, no
/// validation of the field values, and no local notion of what a valid account is — the grammar
/// and every refusal live in `MinaAccountOpening.decodeAccountWire`.
///
/// ⚑ The permission run puts `txn_version` between `set_verification_key` and `set_zkapp_uri`,
/// because that is where `Permissions.Poly.to_input` absorbs it. It is not appended at either end.
pub fn mina_account_opening_wire(input: &MinaAccountOpeningInput) -> String {
    let p = &input.permissions;
    let perm = [
        p.edit_state.as_str(),
        p.access.as_str(),
        p.send.as_str(),
        p.receive.as_str(),
        p.set_delegate.as_str(),
        p.set_permissions.as_str(),
        p.set_verification_key.as_str(),
        p.txn_version.as_str(),
        p.set_zkapp_uri.as_str(),
        p.edit_action_state.as_str(),
        p.set_token_symbol.as_str(),
        p.increment_nonce.as_str(),
        p.set_voting_for.as_str(),
        p.set_timing.as_str(),
    ]
    .join("|");
    let dirs: String = input.node_is_left.iter().map(|&b| bool01(b)).collect();
    format!(
        "blk={};pk={},{};tk={};ts={};bal={};non={};rch={};dlg={},{};vf={};\
         tm={},{},{},{},{},{};perm={};zk={};idx={};sib={};dir={}",
        hex_lower(&input.protocol_state_prefix),
        input.public_key_x,
        bool01(input.public_key_is_odd),
        input.token_id,
        input.token_symbol,
        input.balance,
        input.nonce,
        input.receipt_chain_hash,
        input.delegate_x,
        bool01(input.delegate_is_odd),
        input.voting_for,
        bool01(input.is_timed),
        input.initial_minimum_balance,
        input.cliff_time,
        input.cliff_amount,
        input.vesting_period,
        input.vesting_increment,
        perm,
        input.zkapp_digest.as_deref().unwrap_or(""),
        input.leaf_index,
        dec_list(&input.siblings),
        dirs,
    )
}

/// Run the VERIFIED gate `@[export] dregg_mina_account_state_ok` over a pre-built wire and return
/// the raw output (`"1"` / `"0"` / `"ERR"`). `Err` when the archive did not export it.
pub fn shadow_mina_account_state_ok(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi_mina_account_state::lean_mina_account_state_ok(wire)
}

/// The end-to-end verified account query. `Ok(true)` ONLY on the gate's `"1"`; `"0"` (the opening
/// does not reach the ledger hash in the block) and `"ERR"` (the wire or the block bytes are
/// malformed) are both `Ok(false)` — fail-closed. `Err` ONLY when the archive lacks the export,
/// which a caller must surface as an unavailable gate rather than as a negative answer about the
/// account.
pub fn verified_mina_account_state_ok(input: &MinaAccountOpeningInput) -> Result<bool, String> {
    let out = shadow_mina_account_state_ok(&mina_account_opening_wire(input))?;
    Ok(out == "1")
}

#[cfg(all(lean_lib_present, dregg_mina_account_state_ok_present))]
mod ffi_mina_account_state {
    use std::ffi::CString;
    use std::os::raw::c_char;

    extern "C" {
        fn dregg_mina_account_state_ok_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
    }

    pub fn mina_account_state_ok_present() -> bool {
        true
    }

    pub fn lean_mina_account_state_ok(wire: &str) -> Result<String, String> {
        let c_in = CString::new(wire).map_err(|e| format!("wire has interior NUL: {e}"))?;
        let mut cap = 256;
        loop {
            let mut buf = vec![0u8; cap];
            let full = unsafe {
                dregg_mina_account_state_ok_str(c_in.as_ptr(), buf.as_mut_ptr() as *mut c_char, cap)
            };
            if full == usize::MAX {
                return Err("dregg_mina_account_state_ok_str: unusable output buffer".into());
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

#[cfg(not(all(lean_lib_present, dregg_mina_account_state_ok_present)))]
mod ffi_mina_account_state {
    pub fn mina_account_state_ok_present() -> bool {
        false
    }

    pub fn lean_mina_account_state_ok(_wire: &str) -> Result<String, String> {
        Err(
            "dregg_mina_account_state_ok not exported by the linked archive (rebuild to enable)"
                .into(),
        )
    }
}

// ===========================================================================
// MINA — SAMASIKA FORK CHOICE (`dregg_mina_better_tip`) and the ROLLING VERIFIED HEAD
// (`dregg_mina_head_advance`)
// ===========================================================================
//
// `dregg_mina_lc_verify` above says in its own header what it does NOT decide: FORK CHOICE. Two
// k-deep, parent-linked, Pickles-proved segments under different anchors are indistinguishable to
// it. These two exports are that missing decision. They are authored in
// `Dregg2.Bridge.MinaForkChoiceGate` over the `select` rule formalized in
// `Dregg2.Bridge.MinaChainSelection` — short-range: the longer chain; long-range: sub-window
// density, then length, then the VRF digest, then the state hash — and Rust decides nothing here.
//
// ⚑ THE COMPARISON IS PAIRWISE AND MUST NEVER BE FOLDED OVER A CANDIDATE SET.
//
// `MinaChainSelection.beats_not_transitive` PROVES `select` has genuine 3-cycles at REAL mainnet
// constants (`decide`-checked, by two independent mechanisms). So "the best tip in a set" is not a
// function of the set: it depends on presentation order, and a peer that controls presentation
// order can walk a node around the cycle. `verified_mina_better_tip` therefore compares ONE
// candidate against the CURRENT head and nothing else. A `fold`/`max_by`/`sort_by` over candidates
// using this function is NOT an improvement over the loop — it is order-dependent by construction,
// and `MinaForkChoiceGate.head_can_be_walked_in_a_cycle` executes three legitimate Samasika
// advances that return the head to exactly where it started. Do not "clean this up" into a fold.
//
// ⚑ AND THE GUARANTEE THAT SURVIVES THAT. The head is a PREFERENCE and it can cycle; the finalized
// height is a RATCHET and it cannot decrease — `MinaForkChoiceGate.rollHead_finalized_monotone`, on
// ANY input, for ANY candidate, under ANY presentation order, including around the cycle
// (`the_cycle_moves_the_head_but_not_the_finalized_point`). That asymmetry is what makes running a
// pairwise head safe: the worst an order-controlling peer achieves is churning which tip we serve,
// never un-finalizing something. Callers must persist BOTH halves of `MinaHeadRoll` and must never
// write back a `finalized` they computed themselves.
//
// ⚑ THE WIRE CARRIES RAW BINPROT BYTES, AND THAT IS DELIBERATE. `e` and `c` are the lowercase hex
// of the `Protocol_state.Value.Stable.V2` bytes as they came off the peer, and `Dregg2.Bridge.
// MinaBinprot` decodes them IN LEAN (`decodeProtocolStateChecked`, which also refuses a block whose
// CARRIED constants disagree with the pinned mainnet ones). Rust deliberately does not know which
// bytes are `min_window_density`, which are `sub_window_densities`, or where the VRF output sits: a
// Rust decoder would be a mirror of openmina's `p2p-messages`, and its correctness would then rest
// on a differential test — a confession, not a mitigation. The only thing this side knows about a
// Mina consensus state is that it is a byte string a socket produced. A trailing remainder is
// allowed by the decoder (on the wire the protocol state is followed by the Wrap proof and the
// block body), so a caller may hand over the whole header prefix rather than slicing it.
//
// ⚑ `eh` / `ch` ARE THE ONE SUPPLIED (NOT DERIVED) INPUT, and they are a NAMED CARRIER, not a
// hidden trust. They are the two tips' state hashes as `Fp` elements in decimal, and `select` reads
// them ONLY as the FINAL tie-break, after `blockchain_length` and the VRF digest have both tied.
// They are supplied rather than recomputed because `state_hash =
// Poseidon("MinaProtoState")[previous_state_hash, body_hash]` and `Body.hash` absorbs `to_input` in
// a field ordering that is NOT the binprot ordering; re-deriving it is a separate Lean job that
// does not exist yet (`docs/MINA-LIGHT-CLIENT.md` carries it as an open row). Everything else on
// this wire — including the Blake2b VRF digest — is DERIVED from the bytes by the gate.
//
// ⚑ WHAT AN ABSENT EXPORT COSTS. There is NO Rust twin of `select` and there will not be one; a
// hand-written Samasika in Rust is exactly the drift these gates exist to delete. Absent, both
// `*_available()` go constantly false, `verified_mina_better_tip` returns `Err` (never
// `TakeCandidate`) and `verified_mina_head_advance` returns `Err` (never an advance), so the client
// keeps whatever head it already persisted and its finalized height does not move. A light client
// that cannot choose between forks is stalled; one that guesses is forked. Stalled is the refusal.
//
// Wire grammar (mirrors `MinaForkChoiceGate.decodeTipPair` / `minaHeadAdvanceGate` byte-for-byte):
// ```text
// TIP        := "eh=" Nat ";ch=" Nat ";e=" HEX ";c=" HEX
// HEX        := an even-length string of [0-9a-fA-F]
// BETTER_TIP := TIP
//            -> "1" (the CANDIDATE is canonical, drop the existing tip) | "0" | "ERR"
// HEAD_ADV   := "sg=" BIT ";fz=" Nat ";" TIP        -- `e` = the persisted head, `c` = the candidate
//            -> "adv=" BIT ";fin=" Nat | "ERR"
// ```

/// Lowercase hex, two digits per byte, no separators — the `HEX` production of the fork-choice
/// wire. This is a RENDERING of bytes the caller received, not a decode: nothing here interprets a
/// single one of them (see the section header on why the decode is Lean's).
fn hex_lower(bytes: &[u8]) -> String {
    use std::fmt::Write as _;
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        let _ = write!(s, "{b:02x}");
    }
    s
}

/// The verified Samasika verdict on ONE pair of tips. `TakeCandidate` iff the Lean gate
/// (`dregg_mina_better_tip`) returned `"1"`; `"0"`, `"ERR"`, a malformed wire, a block the binprot
/// decoder structurally refuses and an absent archive are ALL `KeepExisting` (fail-closed).
///
/// ⚑ This is a verdict about a PAIR, never about a set — `select` is not transitive
/// (`MinaChainSelection.beats_not_transitive`), so there is no "best" to compute. See the section
/// header.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MinaForkChoiceVerdict {
    /// The gate PREFERS the candidate: it is canonical and the existing tip must be dropped.
    TakeCandidate,
    /// The gate does NOT prefer the candidate — keep the existing tip. Also the answer on every
    /// refusal, because a fork choice that cannot be rendered is not a licence to switch.
    KeepExisting,
}

/// The persisted result of rolling the verified head once. Callers write BOTH fields back.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MinaHeadRoll {
    /// Whether to replace the persisted head tip with the candidate. A PREFERENCE — it can cycle
    /// under an adversarial presentation order (`MinaForkChoiceGate.head_can_be_walked_in_a_cycle`).
    pub advance: bool,
    /// The NEW finalized height. A RATCHET: `rollHead_finalized_monotone` proves this is never
    /// below the `finalized` that went in, on any input. Persist it as returned; never recompute
    /// `blockchain_length - k` on this side.
    pub finalized: u64,
}

/// Whether the linked archive exports the verified pairwise fork-choice gate
/// (`dregg_mina_better_tip`, spliced from `Dregg2.Bridge.MinaForkChoiceGate`). When false the caller
/// must FAIL CLOSED and keep the tip it has: there is no Rust twin of Samasika `select`, and the
/// pre-gate behaviour — asking a peer's `bestChain` which chain it likes — is the thing being
/// deleted, not a fallback.
pub fn mina_better_tip_available() -> bool {
    ffi_mina_better_tip::mina_better_tip_present() && lean_init_once().is_ok()
}

/// Build the pairwise fork-choice wire from two tips' RAW binprot `Protocol_state.Value.Stable.V2`
/// bytes plus their state hashes.
///
/// `existing_state_hash` / `candidate_state_hash` are decimal `Fp` elements (they exceed `u64`, so
/// they are `&str`, and they are the supplied tie-break carrier described in the section header —
/// pass the Base58Check-decoded `stateHash` as a decimal, not the Base58 string). A value that is
/// not a decimal `Nat`, or one that smuggles a `;` or `=`, does not produce a verdict computed from
/// what did parse: the gate structurally refuses it and answers `"ERR"`, which is `KeepExisting`.
pub fn mina_better_tip_wire(
    existing_state_hash: &str,
    candidate_state_hash: &str,
    existing_protocol_state: &[u8],
    candidate_protocol_state: &[u8],
) -> String {
    format!(
        "eh={existing_state_hash};ch={candidate_state_hash};e={};c={}",
        hex_lower(existing_protocol_state),
        hex_lower(candidate_protocol_state),
    )
}

/// Run the VERIFIED gate `@[export] dregg_mina_better_tip` over a pre-built wire and return the raw
/// output (`"1"` / `"0"` / `"ERR"`). Requires [`mina_better_tip_available`]; returns `Err` when the
/// archive did not export it (so the caller distinguishes "archive missing" from "not preferred"
/// and keeps its existing tip either way).
pub fn shadow_mina_better_tip(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi_mina_better_tip::lean_mina_better_tip(wire)
}

/// The end-to-end verified Samasika comparison of ONE candidate tip against the CURRENT head.
/// `Ok(TakeCandidate)` ONLY on the gate's `"1"`; every other gate output is `Ok(KeepExisting)`
/// (fail-closed). `Err` is returned ONLY when the archive lacks the export — the caller must treat
/// that as a REFUSAL to choose, never as a skipped check and never as an advance.
///
/// ⚑ Call this against the head you currently hold, once per candidate, and act on each answer
/// before considering the next. It is NOT a comparator: `select` is not transitive, so folding this
/// over a candidate set yields an order-dependent "winner" a hostile peer picks by choosing the
/// order. See the section header and `MinaChainSelection.beats_not_transitive`.
pub fn verified_mina_better_tip(
    existing_state_hash: &str,
    candidate_state_hash: &str,
    existing_protocol_state: &[u8],
    candidate_protocol_state: &[u8],
) -> Result<MinaForkChoiceVerdict, String> {
    let wire = mina_better_tip_wire(
        existing_state_hash,
        candidate_state_hash,
        existing_protocol_state,
        candidate_protocol_state,
    );
    let out = shadow_mina_better_tip(&wire)?;
    Ok(if out == "1" {
        MinaForkChoiceVerdict::TakeCandidate
    } else {
        MinaForkChoiceVerdict::KeepExisting
    })
}

/// Whether the linked archive exports the verified head-roll gate (`dregg_mina_head_advance`,
/// spliced from `Dregg2.Bridge.MinaForkChoiceGate`). When false the caller must FAIL CLOSED: the
/// head does not move and the finalized height does not rise. A client that stops following the
/// chain is visibly stalled; one that rolls its own head is silently forked.
pub fn mina_head_advance_available() -> bool {
    ffi_mina_head_advance::mina_head_advance_present() && lean_init_once().is_ok()
}

/// Build the head-roll wire: the anchored-segment verdict, the persisted finalized height, and the
/// `TIP` pair with the PERSISTED HEAD as `e` and the candidate as `c`.
///
/// `segment_ok` is the `dregg_mina_lc_verify` verdict for the candidate's segment — i.e. whether
/// [`verified_mina_lc_verify`] returned [`MinaLcVerdict::Accept`]. It is a conjunct, not a hint:
/// `rollHead_fails_closed_without_the_segment` proves `sg=0` moves nothing, so an unavailable or
/// refused segment gate supplies `false` here and NEVER a skip. Fork choice presupposes both tips
/// are valid; running `select` on an unvalidated tip is believing a stranger's arithmetic.
///
/// `finalized` is the height read back from persistence, unmodified.
pub fn mina_head_advance_wire(
    segment_ok: bool,
    finalized: u64,
    head_state_hash: &str,
    candidate_state_hash: &str,
    head_protocol_state: &[u8],
    candidate_protocol_state: &[u8],
) -> String {
    format!(
        "sg={};fz={finalized};{}",
        if segment_ok { '1' } else { '0' },
        mina_better_tip_wire(
            head_state_hash,
            candidate_state_hash,
            head_protocol_state,
            candidate_protocol_state,
        ),
    )
}

/// Run the VERIFIED gate `@[export] dregg_mina_head_advance` over a pre-built wire and return the
/// raw output (`"adv=B;fin=N"` / `"ERR"`). `Err` when the archive did not export it.
pub fn shadow_mina_head_advance(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi_mina_head_advance::lean_mina_head_advance(wire)
}

/// The end-to-end verified head roll: present ONE candidate to the persisted head and get back both
/// halves of the decision the client must persist.
///
/// The output is parsed STRICTLY — exactly `"adv=" ("0"|"1") ";fin=" u64`. The gate's `"ERR"` (a
/// malformed wire, an odd-length hex string, a byte string that is not a `Protocol_state.Value`, or
/// a block whose carried constants disagree with the pinned mainnet ones), an absent archive, and
/// any other shape all come back as `Err`. There is no arm that returns an advance it did not read,
/// and none that returns a `finalized` this side computed: on `Err` the caller keeps its persisted
/// head AND its persisted finalized height, unchanged.
///
/// ⚑ ONE CANDIDATE, ONE CALL, against the head as it stands after the previous call. Not a fold —
/// see the section header.
pub fn verified_mina_head_advance(
    segment_ok: bool,
    finalized: u64,
    head_state_hash: &str,
    candidate_state_hash: &str,
    head_protocol_state: &[u8],
    candidate_protocol_state: &[u8],
) -> Result<MinaHeadRoll, String> {
    let wire = mina_head_advance_wire(
        segment_ok,
        finalized,
        head_state_hash,
        candidate_state_hash,
        head_protocol_state,
        candidate_protocol_state,
    );
    let out = shadow_mina_head_advance(&wire)?;
    parse_mina_head_roll(&out)
}

/// Strict decode of the head-roll gate's output. Anything that is not exactly
/// `"adv=" ("0"|"1") ";fin=" u64` — including the gate's own `"ERR"` — is an `Err`, and the caller
/// persists nothing.
fn parse_mina_head_roll(out: &str) -> Result<MinaHeadRoll, String> {
    let malformed = || format!("dregg_mina_head_advance returned an undecodable output: {out:?}");
    let (adv_part, fin_part) = out.split_once(';').ok_or_else(malformed)?;
    let adv = adv_part.strip_prefix("adv=").ok_or_else(malformed)?;
    let fin = fin_part.strip_prefix("fin=").ok_or_else(malformed)?;
    let advance = match adv {
        "1" => true,
        "0" => false,
        _ => return Err(malformed()),
    };
    let finalized: u64 = fin.parse().map_err(|_| malformed())?;
    Ok(MinaHeadRoll { advance, finalized })
}

#[cfg(all(lean_lib_present, dregg_mina_better_tip_present))]
mod ffi_mina_better_tip {
    use std::ffi::CString;
    use std::os::raw::c_char;

    extern "C" {
        fn dregg_mina_better_tip_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
    }

    pub fn mina_better_tip_present() -> bool {
        true
    }

    pub fn lean_mina_better_tip(wire: &str) -> Result<String, String> {
        let c_in = CString::new(wire).map_err(|e| format!("wire has interior NUL: {e}"))?;
        let mut cap = 256;
        loop {
            let mut buf = vec![0u8; cap];
            let full = unsafe {
                dregg_mina_better_tip_str(c_in.as_ptr(), buf.as_mut_ptr() as *mut c_char, cap)
            };
            if full == usize::MAX {
                return Err("dregg_mina_better_tip_str: unusable output buffer".into());
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

#[cfg(not(all(lean_lib_present, dregg_mina_better_tip_present)))]
mod ffi_mina_better_tip {
    pub fn mina_better_tip_present() -> bool {
        false
    }

    pub fn lean_mina_better_tip(_wire: &str) -> Result<String, String> {
        Err("dregg_mina_better_tip not exported by the linked archive (rebuild to enable)".into())
    }
}

#[cfg(all(lean_lib_present, dregg_mina_head_advance_present))]
mod ffi_mina_head_advance {
    use std::ffi::CString;
    use std::os::raw::c_char;

    extern "C" {
        fn dregg_mina_head_advance_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
    }

    pub fn mina_head_advance_present() -> bool {
        true
    }

    pub fn lean_mina_head_advance(wire: &str) -> Result<String, String> {
        let c_in = CString::new(wire).map_err(|e| format!("wire has interior NUL: {e}"))?;
        let mut cap = 256;
        loop {
            let mut buf = vec![0u8; cap];
            let full = unsafe {
                dregg_mina_head_advance_str(c_in.as_ptr(), buf.as_mut_ptr() as *mut c_char, cap)
            };
            if full == usize::MAX {
                return Err("dregg_mina_head_advance_str: unusable output buffer".into());
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

#[cfg(not(all(lean_lib_present, dregg_mina_head_advance_present)))]
mod ffi_mina_head_advance {
    pub fn mina_head_advance_present() -> bool {
        false
    }

    pub fn lean_mina_head_advance(_wire: &str) -> Result<String, String> {
        Err("dregg_mina_head_advance not exported by the linked archive (rebuild to enable)".into())
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

    /// The 1,544 binprot bytes of devnet block 540186's `Protocol_state.Value.Stable.V2`, as
    /// lowercase hex — the SAME bytes `Dregg2.Bridge.MinaBinprotRealBlock.devnetBlock540186` pins
    /// and decodes. Provenance and regeneration: `goldens/REGENERATE.md`.
    const REAL_DEVNET_BLOCK_540186_HEX: &str =
        include_str!("../goldens/mina-devnet-block-540186.hex");

    /// The golden back to the bytes a peer served (whitespace-insensitive). The fork-choice API
    /// takes BYTES precisely so that nothing on this side interprets them; going hex → bytes here
    /// and bytes → hex in `hex_lower` also makes the encoder's round-trip part of the test.
    fn real_devnet_block_540186() -> Vec<u8> {
        let digits: Vec<u8> = REAL_DEVNET_BLOCK_540186_HEX
            .bytes()
            .filter(|b| !b.is_ascii_whitespace())
            .collect();
        assert_eq!(
            digits.len() % 2,
            0,
            "the golden is not an even number of hex digits"
        );
        digits
            .chunks(2)
            .map(|pair| {
                u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16)
                    .expect("the golden is not hex")
            })
            .collect()
    }

    /// ⚑ The SAMASIKA FORK-CHOICE pair, through the REAL FFI, on REAL DEVNET BYTES. UNGATED on
    /// purpose, like its four Mina siblings: archive-absence routes through `demand_lean` (which
    /// PANICS under `DREGG_TEST_REQUIRE_LEAN=1`) rather than the test ceasing to exist.
    ///
    /// The cases are `MinaBinprotRealBlock.exportedGateOnRealBytes` /`exportedRollOnRealBytes`'
    /// own, so a divergence between the deployed exports and the `native_decide` theorems shows up
    /// here — and it runs them through the Rust wire builders and the C ABI rather than inside
    /// Lean, which is the part those theorems cannot see.
    #[test]
    fn mina_fork_choice_decides_on_real_devnet_bytes_through_the_real_ffi() {
        if !crate::demand_lean(
            mina_better_tip_available() && mina_head_advance_available(),
            "dregg_mina_better_tip / dregg_mina_head_advance Samasika fork-choice gates",
        ) {
            return;
        }

        let existing = real_devnet_block_540186();
        assert_eq!(existing.len(), 1544, "the golden is not the pinned block");
        // `blockchain_length` is the 5-byte `0xfd` form beginning at offset 1067, so byte 1068 is
        // its low byte: 540186 (`0x1a`) becomes 540187 (`0x1b`). Everything else — including the
        // staking lock checkpoint — is untouched, so the pair is SHORT-range and LENGTH decides.
        let mut candidate = existing.clone();
        assert_eq!(candidate[1068], 26, "the golden is not the pinned block");
        candidate[1068] = 27;

        // A tip does not displace ITSELF (`select_irrefl`) — a peer cannot churn the head by
        // replaying it.
        assert_eq!(
            verified_mina_better_tip("1", "1", &existing, &existing),
            Ok(MinaForkChoiceVerdict::KeepExisting),
            "a tip must not displace itself"
        );
        // The one-block-longer sibling DOES.
        assert_eq!(
            verified_mina_better_tip("1", "2", &existing, &candidate),
            Ok(MinaForkChoiceVerdict::TakeCandidate),
            "a strictly longer short-range tip must be taken"
        );
        // And the REVERSE presentation does not (`select_asymm`).
        assert_eq!(
            verified_mina_better_tip("2", "1", &candidate, &existing),
            Ok(MinaForkChoiceVerdict::KeepExisting),
            "presentation order must not make both sides win"
        );

        // THE ROLL. `k = 290`, so the ratchet lands at 540187 − 290 = 539897.
        assert_eq!(
            verified_mina_head_advance(true, 0, "1", "2", &existing, &candidate),
            Ok(MinaHeadRoll {
                advance: true,
                finalized: 539897
            }),
        );
        // FAIL CLOSED — an unavailable or refusing anchored-segment gate supplies `false` and
        // NOTHING moves (`rollHead_fails_closed_without_the_segment`).
        assert_eq!(
            verified_mina_head_advance(false, 0, "1", "2", &existing, &candidate),
            Ok(MinaHeadRoll {
                advance: false,
                finalized: 0
            }),
            "an unverified segment must move nothing"
        );
        // THE RATCHET — a refused advance does not DROP an already-finalized height, and neither
        // does a genuinely verified SHORTER candidate (`rollHead_finalized_monotone`).
        assert_eq!(
            verified_mina_head_advance(false, 539897, "1", "2", &existing, &candidate),
            Ok(MinaHeadRoll {
                advance: false,
                finalized: 539897
            }),
            "a refused advance must not un-finalize"
        );
        assert_eq!(
            verified_mina_head_advance(true, 539897, "2", "1", &candidate, &existing),
            Ok(MinaHeadRoll {
                advance: false,
                finalized: 539897
            }),
            "a shorter candidate must not un-finalize"
        );

        // A REFUSAL IS NOT A VERDICT COMPUTED FROM WHAT DID PARSE. A malformed wire, and a byte
        // string that is not a `Protocol_state.Value`, both come back as `"ERR"` — which is
        // `KeepExisting` for the comparison and an `Err` (persist nothing) for the roll.
        assert_eq!(shadow_mina_better_tip("garbage").as_deref(), Ok("ERR"));
        assert_eq!(shadow_mina_head_advance("garbage").as_deref(), Ok("ERR"));
        assert_eq!(
            verified_mina_better_tip("1", "2", b"\x00", b"\x00"),
            Ok(MinaForkChoiceVerdict::KeepExisting),
            "bytes that are not a protocol state must not displace the head"
        );
        assert!(
            verified_mina_head_advance(true, 0, "1", "2", b"\x00", b"\x00").is_err(),
            "bytes that are not a protocol state must not yield a roll to persist"
        );

        // THE STANDING NON-CONSTANCY CANARY (see the ETH test): the two wires differ in exactly ONE
        // BYTE of 1,544 — the low byte of `blockchain_length` — and the gate must straddle it.
        let take_raw =
            shadow_mina_better_tip(&mina_better_tip_wire("1", "2", &existing, &candidate));
        let keep_raw =
            shadow_mina_better_tip(&mina_better_tip_wire("2", "1", &candidate, &existing));
        assert_eq!(take_raw.as_deref(), Ok("1"));
        assert_eq!(keep_raw.as_deref(), Ok("0"));
        assert_ne!(
            take_raw, keep_raw,
            "the fork-choice gate returned the SAME verdict on a chain one block longer — it is a \
             constant, not a gate"
        );
    }

    // ========================================================================
    // MINA STATE — the ACCOUNT-OPENING gate, on a LIVE devnet account
    // ========================================================================

    /// The fetched fixture: devnet block **540268**'s protocol-state prefix, the live account
    /// `B62qmGudrekyaWbKzw2b4LagLvhUjVup3vUxKf1Yj96ZiiUJKpPZHjG` at leaf index 6202, and its
    /// 35-level ledger opening. Provenance and regeneration: `goldens/REGENERATE.md` and
    /// `bridge/tools/mina-account-opening.py --from-tip-creator --with-block`.
    const REAL_DEVNET_ACCOUNT_OPENING_JSON: &str =
        include_str!("../goldens/mina-devnet-account-opening.json");

    /// The wire the Lean side pins (`MinaAccountOpeningRealBlock.honestWire`). The Rust builder is
    /// asserted BYTE-IDENTICAL to it, which is the only thing that makes "the Rust builder and the
    /// Lean parser agree on the grammar" a measurement rather than a hope.
    const REAL_DEVNET_ACCOUNT_OPENING_WIRE: &str =
        include_str!("../goldens/mina-devnet-account-opening.wire");

    /// `serde_json` is NOT a dependency of this crate and this is not a reason to add one: the
    /// fixture is a committed, tool-generated file with a fixed shape, and these four readers are
    /// ~30 lines against a ~200 KB dependency tree. Each PANICS on a shape it does not recognise,
    /// so a regenerated fixture that moved a field fails here loudly rather than defaulting.
    fn json_after(json: &str, key: &str) -> usize {
        let pat = format!("\"{key}\":");
        let at = json
            .find(&pat)
            .unwrap_or_else(|| panic!("the account golden has no `{key}` field"));
        at + pat.len()
    }

    fn json_string(json: &str, key: &str) -> String {
        let rest = &json[json_after(json, key)..];
        let open = rest
            .find('"')
            .unwrap_or_else(|| panic!("`{key}` is not string-valued"));
        let after = &rest[open + 1..];
        let end = after
            .find('"')
            .unwrap_or_else(|| panic!("`{key}` has an unterminated string"));
        after[..end].to_string()
    }

    fn json_bool(json: &str, key: &str) -> bool {
        let rest = json[json_after(json, key)..].trim_start();
        if rest.starts_with("true") {
            true
        } else if rest.starts_with("false") {
            false
        } else {
            panic!("`{key}` is not a boolean")
        }
    }

    fn json_u64(json: &str, key: &str) -> u64 {
        let rest = json[json_after(json, key)..].trim_start();
        let end = rest
            .find(|c: char| !c.is_ascii_digit())
            .unwrap_or(rest.len());
        rest[..end]
            .parse()
            .unwrap_or_else(|_| panic!("`{key}` is not a decimal"))
    }

    /// A flat `[...]` of scalars, split on `,` with quotes and whitespace stripped.
    fn json_flat_array(json: &str, key: &str) -> Vec<String> {
        let rest = &json[json_after(json, key)..];
        let open = rest
            .find('[')
            .unwrap_or_else(|| panic!("`{key}` is not an array"));
        let close = rest[open..]
            .find(']')
            .unwrap_or_else(|| panic!("`{key}` is unterminated"))
            + open;
        rest[open + 1..close]
            .split(',')
            .map(|s| s.trim().trim_matches('"').to_string())
            .collect()
    }

    fn hex_to_bytes(hex: &str) -> Vec<u8> {
        assert_eq!(hex.len() % 2, 0, "the golden block hex is odd-length");
        hex.as_bytes()
            .chunks(2)
            .map(|pair| {
                u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16)
                    .expect("the golden block is not hex")
            })
            .collect()
    }

    /// The honest input, read out of the committed fixture. Nothing here is transcribed by hand:
    /// every value comes from the file the fetcher wrote.
    fn real_devnet_account_opening() -> MinaAccountOpeningInput {
        let j = REAL_DEVNET_ACCOUNT_OPENING_JSON;
        MinaAccountOpeningInput {
            protocol_state_prefix: hex_to_bytes(&json_string(j, "hex")),
            public_key_x: json_string(j, "publicKeyX"),
            public_key_is_odd: json_bool(j, "publicKeyIsOdd"),
            token_id: json_string(j, "tokenId"),
            // `Token_symbol.to_field` of the EMPTY symbol is `0`, and the fixture carries the
            // symbol itself (`""`) rather than the field element. This is the one place the test
            // converts, and it converts only the empty case — a non-empty symbol would need the
            // ≤6-byte little-endian read, which belongs in the fetcher, not here.
            token_symbol: {
                let s = json_string(j, "tokenSymbol");
                assert!(
                    s.is_empty(),
                    "the golden account grew a token symbol ({s:?}); its `Token_symbol.to_field` \
                     must come from the fetcher, not from this test"
                );
                "0".to_string()
            },
            balance: json_string(j, "balance"),
            nonce: json_string(j, "nonce"),
            receipt_chain_hash: json_string(j, "receiptChainHash"),
            delegate_x: json_string(j, "delegateX"),
            delegate_is_odd: json_bool(j, "delegateIsOdd"),
            voting_for: json_string(j, "votingFor"),
            is_timed: json_bool(j, "isTimed"),
            initial_minimum_balance: json_string(j, "initialMinimumBalance"),
            cliff_time: json_string(j, "cliffTime"),
            cliff_amount: json_string(j, "cliffAmount"),
            vesting_period: json_string(j, "vestingPeriod"),
            vesting_increment: json_string(j, "vestingIncrement"),
            permissions: MinaAccountPermissions {
                edit_state: json_string(j, "editState"),
                access: json_string(j, "access"),
                send: json_string(j, "send"),
                receive: json_string(j, "receive"),
                set_delegate: json_string(j, "setDelegate"),
                set_permissions: json_string(j, "setPermissions"),
                set_verification_key: json_string(j, "auth"),
                txn_version: json_string(j, "txnVersion"),
                set_zkapp_uri: json_string(j, "setZkappUri"),
                edit_action_state: json_string(j, "editActionState"),
                set_token_symbol: json_string(j, "setTokenSymbol"),
                increment_nonce: json_string(j, "incrementNonce"),
                set_voting_for: json_string(j, "setVotingFor"),
                set_timing: json_string(j, "setTiming"),
            },
            // `"zkappState": null` — the account has NO zkApp, and the leaf preimage carries
            // `Zkapp_account.default_digest`.
            zkapp_digest: None,
            leaf_index: json_u64(j, "index"),
            siblings: json_flat_array(j, "siblings"),
            node_is_left: json_flat_array(j, "nodeIsLeft")
                .iter()
                .map(|s| match s.as_str() {
                    "true" => true,
                    "false" => false,
                    other => panic!("`nodeIsLeft` carries {other:?}, not a boolean"),
                })
                .collect(),
        }
    }

    /// Change the final decimal digit. A 255-bit sibling hash cannot be incremented as a `u128`,
    /// and the point is only that the value is a DIFFERENT one — `(d + 1) % 10` always is.
    fn bump_last_digit(s: &str) -> String {
        let mut cs: Vec<char> = s.chars().collect();
        let last = cs.len() - 1;
        let d = cs[last].to_digit(10).expect("not a decimal");
        cs[last] = char::from_digit((d + 1) % 10, 10).unwrap();
        cs.into_iter().collect()
    }

    /// ⚑ THE ACCOUNT-OPENING GATE, THROUGH THE REAL C ABI, ON A REAL DEVNET ACCOUNT. UNGATED on
    /// purpose like its five Mina siblings: archive-absence routes through `demand_lean` (which
    /// PANICS under `DREGG_TEST_REQUIRE_LEAN=1`) rather than the test ceasing to exist.
    ///
    /// What it measures that `MinaAccountOpeningRealBlock`'s `#guard`s cannot: those run the gate
    /// INSIDE Lean on a pinned string. This one builds the wire in Rust from the fetched JSON,
    /// asserts it is byte-identical to the string Lean pins, and then drives it through
    /// `dregg_mina_account_state_ok_str` into the linked archive. A Rust builder that disagreed
    /// with the Lean parser on one separator, one key, or the `txn_version` position would still
    /// leave every `#guard` green.
    ///
    /// The three answers are kept apart deliberately. A `"0"` asserted as `!= "1"` would be
    /// satisfied by `"ERR"`, i.e. by a harness that broke its own wire — which is a shape failure
    /// wearing a refusal's clothes. Every rejection below pins the exact string `"0"`.
    #[test]
    fn mina_account_opening_gate_decides_on_a_real_devnet_account_through_the_real_ffi() {
        if !crate::demand_lean(
            mina_account_state_ok_available(),
            "dregg_mina_account_state_ok Mina account-opening gate",
        ) {
            return;
        }

        let honest = real_devnet_account_opening();
        assert_eq!(
            honest.siblings.len(),
            35,
            "the golden is not a 35-level opening"
        );
        assert_eq!(
            honest.node_is_left.len(),
            35,
            "the golden is not a 35-level opening"
        );
        assert_eq!(
            honest.leaf_index, 6202,
            "the golden is not the pinned account"
        );
        assert_eq!(
            honest.balance, "28305375018363953",
            "the golden is not the pinned account"
        );

        // ⚑ THE CROSS-CHECK ON THE GRAMMAR ITSELF. The Rust builder and `decodeAccountWire` must
        // agree on all 15 segments, their keys, their order and their separators — including the
        // `txn_version` sitting INSIDE the permission run. Byte identity against the string the
        // Lean `#guard`s are stated over is what makes that a measurement.
        let wire = mina_account_opening_wire(&honest);
        assert_eq!(
            wire,
            REAL_DEVNET_ACCOUNT_OPENING_WIRE.trim_end(),
            "the Rust wire builder and the Lean-pinned wire disagree"
        );

        // ACCEPT — a real account, a real block, and a ledger hash decoded out of Mina's own bytes.
        assert_eq!(
            shadow_mina_account_state_ok(&wire).as_deref(),
            Ok("1"),
            "the honest opening must be ACCEPTED"
        );
        assert_eq!(verified_mina_account_state_ok(&honest), Ok(true));

        // REJECT — ONE NANOMINA. The exact string `"0"`: an `"ERR"` here would mean the harness
        // broke the wire rather than the gate refusing the account, and that must fail.
        let mut richer = honest.clone();
        richer.balance = (honest.balance.parse::<u128>().unwrap() + 1).to_string();
        assert_eq!(
            shadow_mina_account_state_ok(&mina_account_opening_wire(&richer)).as_deref(),
            Ok("0"),
            "an account one nanomina richer must be REFUSED, and refused rather than unparsed"
        );
        assert_eq!(verified_mina_account_state_ok(&richer), Ok(false));

        // REJECT — a tampered leaf-level sibling. The opening no longer folds to the ledger hash.
        let mut wrong_sibling = honest.clone();
        wrong_sibling.siblings[0] = bump_last_digit(&honest.siblings[0]);
        assert_eq!(
            shadow_mina_account_state_ok(&mina_account_opening_wire(&wrong_sibling)).as_deref(),
            Ok("0"),
            "a tampered sibling must be REFUSED"
        );

        // REJECT — a wrong index, and by the INDEX check rather than by luck: the exhibited
        // directions no longer spell 6203, so `directionsMatchIndex` fails before a hash is taken.
        let mut wrong_index = honest.clone();
        wrong_index.leaf_index = honest.leaf_index + 1;
        assert_eq!(
            shadow_mina_account_state_ok(&mina_account_opening_wire(&wrong_index)).as_deref(),
            Ok("0"),
            "an account presented at the wrong leaf index must be REFUSED"
        );

        // ERR — the THIRD answer. A structurally broken wire is a parse failure, and it must not
        // be spelled the same way as a refusal: if it were, none of the three `"0"`s above would
        // mean anything.
        assert_eq!(
            shadow_mina_account_state_ok("garbage").as_deref(),
            Ok("ERR"),
            "a wire that is not the grammar must be ERR"
        );
        assert_eq!(
            shadow_mina_account_state_ok(&wire.replace(";bal=", ";blah=")).as_deref(),
            Ok("ERR"),
            "a renamed key must be ERR, not a refusal computed from what did parse"
        );
        // THE STANDING NON-CONSTANCY CANARY: three distinct answers on three inputs. A gate that
        // has degenerated to always-accept, always-reject or always-`"ERR"` collapses at least two
        // of these together.
        let accept = shadow_mina_account_state_ok(&wire);
        let reject = shadow_mina_account_state_ok(&mina_account_opening_wire(&richer));
        let err = shadow_mina_account_state_ok("garbage");
        assert_ne!(
            accept, reject,
            "the account gate returned the SAME verdict on a balance one nanomina apart — it is a \
             constant, not a gate"
        );
        assert_ne!(
            reject, err,
            "the account gate spells REFUSAL and PARSE FAILURE the same way — the rejections above \
             carry no information"
        );
        assert_ne!(accept, err);
    }
}

// ===========================================================================
// MINA — THE PER-BLOCK DERIVATION PAIR (`dregg_mina_wrap_challenges`,
// `dregg_mina_wrap_ft_eval0`)
// ===========================================================================
//
// ⚑ WHY THIS SECTION EXISTS, and it is not "a new feature". On 2026-07-30
// `Dregg2.Bridge.MinaWrapChallenges` landed, was rooted in `Dregg2/FFI.lean`, and `build.rs`
// probed its symbol and set `dregg_mina_wrap_challenges_present`. There was no `_str` bridge in
// `lean_init.c` and no wrapper here, so the archive carried the export and **nothing in the
// process could call it**. That is the GATING-DEFAULTS-TO-SILENCE class in its purest form: no
// broken code, no red test, a gate that cannot go red because it cannot be entered.
//
// ⚑ AND THERE IS NO RUST TWIN OF EITHER, deliberately. A Rust Fq-sponge is a re-rendering of a
// transcript, and a Rust linearization is a re-rendering of a circuit's meaning; both would be
// exactly the drift `Dregg2.Bridge.MinaChainSelection`'s gate deletes for `select`. Rust here
// formats decimals and parses `key=value`. Absent exports are `Err`, never a local computation.

/// The per-block Fiat–Shamir challenges of ONE Wrap proof, as the verified gate derived them.
///
/// ⚑ Every field is the gate's output, parsed. Nothing in this struct is computed on this side,
/// and there is no constructor that fills one in from anywhere else.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MinaWrapChallenges {
    /// β — the first raw 128-bit phase-1 squeeze.
    pub beta: String,
    /// γ — the second.
    pub gamma: String,
    /// α′ — the quotient prechallenge.
    pub alpha_chal: String,
    /// ζ′ — the evaluation-point prechallenge.
    pub zeta_chal: String,
    /// `fq_sponge.digest()` reinterpreted in the scalar field — what seeds phase 2.
    pub fq_digest: String,
    /// `challenge_fq()`'s full-field output, the group map's preimage.
    pub t: String,
    /// `c′`, squeezed after `delta`.
    pub c_pre: String,
    /// ⚑ **The 15 RAW IPA prechallenges** — the vector `mina_opening_check.rs` used to have pinned
    /// for exactly one height.
    pub ipa_prechallenges: Vec<String>,
}

/// The per-block `ft_eval0` derivation's answer for ONE side of the Pasta cycle.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MinaWrapFtEval0 {
    /// ⚑ The linearization constant term, DERIVED from the six transcribed gate bodies. This is
    /// the value `Dregg2.Circuit.Emit.MinaRealBlockGate` carries as `LCT`.
    pub lin_const_term: String,
    /// `ft_eval0`.
    pub ft_eval0: String,
    /// The derived domain generator.
    pub omega: String,
    /// ζ, endomorphism-lifted.
    pub zeta: String,
    /// α, endomorphism-lifted.
    pub alpha: String,
}

/// Is the per-block challenge derivation callable in THIS build?
///
/// ⚑ A `false` is a refusal, never a licence to derive challenges some other way.
pub fn mina_wrap_challenges_available() -> bool {
    ffi_mina_wrap_challenges::present() && lean_init_once().is_ok()
}

/// Is the per-block `ft_eval0` derivation callable in THIS build?
pub fn mina_wrap_ft_eval0_available() -> bool {
    ffi_mina_wrap_ft_eval0::present() && lean_init_once().is_ok()
}

/// Run the VERIFIED gate `@[export] dregg_mina_wrap_challenges` over a pre-built wire and return
/// its raw answer. The wire grammar is `Dregg2.Bridge.MinaWrapChallenges` §4.
pub fn shadow_mina_wrap_challenges(wire: &str) -> Result<String, String> {
    lean_init_once()?;
    ffi_mina_wrap_challenges::call(wire)
}

/// Run the VERIFIED gate `@[export] dregg_mina_wrap_ft_eval0` over a pre-built wire.
pub fn shadow_mina_wrap_ft_eval0(wire: &str) -> Result<String, String> {
    lean_init_once()?;
    ffi_mina_wrap_ft_eval0::call(wire)
}

/// Split `"k=v;k=v"` into its values, checking every key IN ORDER.
///
/// ⚑ Positional AND named: a gate that grew a field, or reordered two, is a parse failure here
/// rather than a silently mis-assigned value. That is the same reason the Lean side checks its own
/// keys positionally in `parseChallengeWire`.
fn parse_kv_ordered(out: &str, keys: &[&str]) -> Result<Vec<String>, String> {
    let parts: Vec<&str> = out.split(';').collect();
    if parts.len() != keys.len() {
        return Err(format!(
            "the gate answered {} field(s), expected {} ({:?})",
            parts.len(),
            keys.len(),
            keys
        ));
    }
    let mut vals = Vec::with_capacity(keys.len());
    for (part, key) in parts.iter().zip(keys.iter()) {
        let (k, v) = part
            .split_once('=')
            .ok_or_else(|| format!("field `{part}` is not `key=value`"))?;
        if k != *key {
            return Err(format!("field {k} is not the expected `{key}`"));
        }
        vals.push(v.to_string());
    }
    Ok(vals)
}

/// Every value the gate returns must be a canonical decimal — no sign, no leading `+`, no
/// whitespace. A malformed answer is a REFUSAL; nothing downstream sees a partially-parsed one.
fn all_decimal(v: &str) -> bool {
    !v.is_empty() && v.bytes().all(|b| b.is_ascii_digit())
}

/// ⚑⚑ **THE PER-BLOCK CHALLENGE DERIVATION.** Hand the gate one Wrap proof's absorbed coordinates
/// and get its own 15 IPA prechallenges back.
///
/// Every argument is a decimal rendering of a value `bridge/src/mina_pickles.rs` decoded, except
/// `vk_digest` and `endo_r`, which are TRUSTED CONFIG and are named as such by the caller.
/// `lr` arrives FLAT (60 numbers) and is re-chunked INSIDE the archive.
#[allow(clippy::too_many_arguments)]
pub fn verified_mina_wrap_challenges(
    vk_digest: &str,
    endo_r: &str,
    prev_comm: &[String],
    public_comm: &[String],
    w_comm: &[String],
    z_comm: &[String],
    t_comm: &[String],
    cip_shifted: &str,
    lr_flat: &[String],
    delta: &[String],
) -> Result<MinaWrapChallenges, String> {
    let join = |xs: &[String]| xs.join(",");
    let wire = format!(
        "vk={vk_digest};er={endo_r};pc={};pu={};wc={};zc={};tc={};cs={cip_shifted};lr={};dl={}",
        join(prev_comm),
        join(public_comm),
        join(w_comm),
        join(z_comm),
        join(t_comm),
        join(lr_flat),
        join(delta),
    );
    let out = shadow_mina_wrap_challenges(&wire)?;
    if out == "ERR" {
        return Err(
            "the VERIFIED challenge gate REFUSED this tape: a wrong-shaped absorb sequence, a \
             non-canonical coordinate, or fewer than 15 IPA rounds. Nothing was derived"
                .to_string(),
        );
    }
    let v = parse_kv_ordered(&out, &["b", "g", "a", "z", "fq", "t", "c", "ch"])?;
    let chals: Vec<String> = v[7].split(',').map(|s| s.to_string()).collect();
    if chals.len() != 15 {
        return Err(format!(
            "the gate returned {} IPA prechallenges, and the emitted AIR witnesses 15",
            chals.len()
        ));
    }
    for x in v.iter().take(7).chain(chals.iter()) {
        if !all_decimal(x) {
            return Err(format!("the gate returned a non-decimal field `{x}`"));
        }
    }
    Ok(MinaWrapChallenges {
        beta: v[0].clone(),
        gamma: v[1].clone(),
        alpha_chal: v[2].clone(),
        zeta_chal: v[3].clone(),
        fq_digest: v[4].clone(),
        t: v[5].clone(),
        c_pre: v[6].clone(),
        ipa_prechallenges: chals,
    })
}

/// ⚑⚑ **THE PER-BLOCK `ft_eval0` DERIVATION.** `wrap_side` selects the modulus: `true` is the
/// WRAP/Tock side (`ZMod qN`), `false` the STEP/Tick side (`ZMod pN`).
///
/// `ez`/`ew` are the 43 evaluation columns at ζ and ζω in `to_absorption_sequence` order; the
/// archive slices `w`, `coefficients`, `s` and the six selectors out of them, because a caller that
/// slices is a caller that can mis-slice.
#[allow(clippy::too_many_arguments)]
pub fn verified_mina_wrap_ft_eval0(
    wrap_side: bool,
    domain_log2: u32,
    alpha_chal: &str,
    beta_chal: &str,
    gamma_chal: &str,
    zeta_chal: &str,
    ez: &[String],
    ew: &[String],
    p_zeta: &str,
    endo_r: &str,
    endo_coefficient: &str,
    shifts: &[String],
    mds: &[String],
) -> Result<MinaWrapFtEval0, String> {
    let join = |xs: &[String]| xs.join(",");
    let wire = format!(
        "m={};lg={domain_log2};al={alpha_chal};be={beta_chal};ga={gamma_chal};ze={zeta_chal};\
         ez={};ew={};pz={p_zeta};er={endo_r};en={endo_coefficient};sh={};md={}",
        if wrap_side { "q" } else { "p" },
        join(ez),
        join(ew),
        join(shifts),
        join(mds),
    );
    let out = shadow_mina_wrap_ft_eval0(&wire)?;
    if out == "ERR" {
        return Err(
            "the VERIFIED ft_eval0 gate REFUSED this side: a column list that is not 43 long, a \
             domain beyond the field's two-adicity, or a denominator with no witnessed inverse. \
             Nothing was derived"
                .to_string(),
        );
    }
    let v = parse_kv_ordered(&out, &["lct", "ft0", "om", "ze", "al"])?;
    for x in &v {
        if !all_decimal(x) {
            return Err(format!("the gate returned a non-decimal field `{x}`"));
        }
    }
    Ok(MinaWrapFtEval0 {
        lin_const_term: v[0].clone(),
        ft_eval0: v[1].clone(),
        omega: v[2].clone(),
        zeta: v[3].clone(),
        alpha: v[4].clone(),
    })
}

#[cfg(all(lean_lib_present, dregg_mina_wrap_challenges_present))]
mod ffi_mina_wrap_challenges {
    use std::ffi::CString;
    use std::os::raw::c_char;

    extern "C" {
        fn dregg_mina_wrap_challenges_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
    }

    pub fn present() -> bool {
        true
    }

    pub fn call(wire: &str) -> Result<String, String> {
        let c_in = CString::new(wire).map_err(|e| format!("wire has interior NUL: {e}"))?;
        // The answer is eight decimals plus fifteen more — comfortably under 2 KB — but the loop
        // grows anyway rather than truncating, the same contract every other bridge has.
        let mut cap = 2048;
        loop {
            let mut buf = vec![0u8; cap];
            let full = unsafe {
                dregg_mina_wrap_challenges_str(c_in.as_ptr(), buf.as_mut_ptr() as *mut c_char, cap)
            };
            if full == usize::MAX {
                return Err("dregg_mina_wrap_challenges_str: unusable output buffer".into());
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

#[cfg(not(all(lean_lib_present, dregg_mina_wrap_challenges_present)))]
mod ffi_mina_wrap_challenges {
    pub fn present() -> bool {
        false
    }

    pub fn call(_wire: &str) -> Result<String, String> {
        Err(
            "dregg_mina_wrap_challenges not exported by the linked archive (rebuild to enable). \
             There is NO Rust fallback and there must not be one"
                .into(),
        )
    }
}

#[cfg(all(lean_lib_present, dregg_mina_wrap_ft_eval0_present))]
mod ffi_mina_wrap_ft_eval0 {
    use std::ffi::CString;
    use std::os::raw::c_char;

    extern "C" {
        fn dregg_mina_wrap_ft_eval0_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
    }

    pub fn present() -> bool {
        true
    }

    pub fn call(wire: &str) -> Result<String, String> {
        let c_in = CString::new(wire).map_err(|e| format!("wire has interior NUL: {e}"))?;
        let mut cap = 2048;
        loop {
            let mut buf = vec![0u8; cap];
            let full = unsafe {
                dregg_mina_wrap_ft_eval0_str(c_in.as_ptr(), buf.as_mut_ptr() as *mut c_char, cap)
            };
            if full == usize::MAX {
                return Err("dregg_mina_wrap_ft_eval0_str: unusable output buffer".into());
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

#[cfg(not(all(lean_lib_present, dregg_mina_wrap_ft_eval0_present)))]
mod ffi_mina_wrap_ft_eval0 {
    pub fn present() -> bool {
        false
    }

    pub fn call(_wire: &str) -> Result<String, String> {
        Err(
            "dregg_mina_wrap_ft_eval0 not exported by the linked archive (rebuild to enable). \
             There is NO Rust fallback and there must not be one"
                .into(),
        )
    }
}

// ===========================================================================
// MINA — THE PER-CHECKPOINT LOOP (`dregg_mina_checkpoint_advance`)
// ===========================================================================
//
// ⚑ WHY THIS SECTION EXISTS, and it is the THIRD instance of one class in three days. On
// 2026-07-30 `Dregg2.Bridge.MinaCheckpoint` landed with `@[export] dregg_mina_checkpoint_advance`,
// `Dregg2/FFI.lean` rooted it, `build.rs` added it to `REQUIRED_DECISION_EXPORTS`, declared
// `dregg_mina_checkpoint_advance_present` to `--check-cfg` and probed the archive to SET it — and
// there was no `shim.define`, no `_str` bridge in `lean_init.c`, and no `#[cfg(…)]` here. So the
// archive carried the symbol, cargo set the cfg, and **nothing in the process could call it**: a
// gate that cannot be entered cannot go red. `cfg_gate_declaration_audit`'s check #3
// (`EMITTED ⊆ USED`) is what found it, which is the point of that test.
//
// It is the same commit-shape as `2a64b61b4` (`dregg_mina_wrap_challenges`, exported/probed/cfg-set
// with no bridge at all) — the export and the plumbing were authored in one commit that was
// deliberately committed UNBUILT, and the plumbing half was three files short. Both halves land
// together here.
//
// ⚑ WHAT THE GATE IS. A TWO-TIER head the fork-choice pair above cannot express. Mina's Pickles
// proof is recursive, so verifying ONE block's Wrap proof attests the whole chain behind it; a
// client verifies at a CHECKPOINT cadence it chooses and runs a cheap provisional tier in between.
// The split is safe because `provisional_never_ratchets` proves a between-checkpoint step is
// DEFINITIONALLY unable to raise `finalized`, and `runSteps_finalized_monotone` proves the ratchet
// survives ANY interleaving of the two tiers. A longer cadence therefore costs LATENCY, not safety.
//
// ⚑ RUST SUPPLIES NO CHEAP VERDICT, deliberately. The parent link and the density RE-DERIVATION
// (`MinaSlidingWindow.step` from the decoded parent — strictly stronger than the bound check a
// served window gets) happen INSIDE the gate. A bit Rust computed and handed over would be a
// carrier for a decision. The ONE bit that crosses is `wrap_ok`, the Wrap arithmetic, which is
// arithmetic Rust did not do either — it comes from a prover, and an unavailable prover supplies
// `false`, never a skip (`checkpoint_without_the_wrap_verdict_moves_nothing`).

/// The persisted result of one checkpoint-loop step. Callers write ALL FOUR fields back.
///
/// ⚑ Every field is the gate's output, parsed. Nothing here is computed on this side, and there is
/// no constructor that fills one in from anywhere else.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MinaCheckpointRoll {
    /// The PROVISIONAL tip moved. A guess — it decides nothing and it can be walked in a cycle by
    /// an adversarial presentation order (`beats_not_transitive`, contained to this tier).
    pub tip_moved: bool,
    /// The VERIFIED head moved, and therefore the ratchet may have risen. Only a CHECKPOINT call
    /// can ever set this: `provisional_never_ratchets`.
    pub advanced: bool,
    /// The new finalized height. A RATCHET — `runSteps_finalized_monotone` proves this is never
    /// below the `finalized` that went in, under any interleaving of the two tiers, any order, any
    /// length. Persist it as returned; never recompute `blockchain_length - k` on this side.
    pub finalized: u64,
    /// The new provisional run counter — blocks accepted onto the tip since the last checkpoint.
    /// A checkpoint that advances RESETS it to 0 (`an_advancing_checkpoint_reanchors_the_tip`);
    /// once it reaches the cap the cheap tier stops moving the tip at all
    /// (`a_stale_run_refuses_to_move_the_tip`), so a peer withholding checkpoint evidence can
    /// stall the client but cannot walk it arbitrarily far on cheap checks.
    pub run: u64,
}

/// The FOUR protocol states one checkpoint step reads, each with the state hash it is claimed
/// under.
///
/// ⚑ Every hash is a CLAIM, not framing: `MinaForkChoiceGate.decodeSide?` re-derives `state_hash`
/// from the bytes and refuses the whole wire when it disagrees. Grouped into a struct rather than
/// eight positional arguments because transposing a (hash, bytes) pair is exactly the mistake that
/// would otherwise be silent at the call site.
#[derive(Debug, Clone, Copy)]
pub struct MinaCheckpointSides<'a> {
    /// The candidate's PARENT — required, never optional. It is what the density re-derivation
    /// reads; making it optional would produce a client that silently degrades to a bound check
    /// whenever a peer declines to serve one.
    pub parent_state_hash: &'a str,
    /// The parent's raw binprot `Protocol_state.Value.Stable.V2` bytes.
    pub parent_protocol_state: &'a [u8],
    /// The persisted PROVISIONAL tip.
    pub tip_state_hash: &'a str,
    /// The provisional tip's raw bytes.
    pub tip_protocol_state: &'a [u8],
    /// The persisted VERIFIED head — the last checkpoint, the thing carrying the ratchet.
    pub verified_state_hash: &'a str,
    /// The verified head's raw bytes.
    pub verified_protocol_state: &'a [u8],
    /// The block being offered.
    pub candidate_state_hash: &'a str,
    /// The candidate's raw bytes.
    pub candidate_protocol_state: &'a [u8],
}

/// Whether the linked archive exports the verified checkpoint-loop gate
/// (`dregg_mina_checkpoint_advance`, spliced from `Dregg2.Bridge.MinaCheckpoint`). When false the
/// caller must FAIL CLOSED: neither tier moves, the ratchet does not rise, and the client is
/// visibly stalled. There is NO Rust twin and there must not be one — a Rust two-tier head is a
/// re-rendering of `provisional_never_ratchets`, i.e. of the safety argument itself, and the
/// available fallbacks are per-block verification the client cannot afford or a single-tier head
/// whose ratchet moves on cheap checks alone.
pub fn mina_checkpoint_advance_available() -> bool {
    ffi_mina_checkpoint_advance::present() && lean_init_once().is_ok()
}

/// Build the checkpoint-loop wire.
///
/// `checkpoint` selects the tier: `true` runs the expensive one (and is the only tier that can move
/// the ratchet), `false` the cheap per-block one. `wrap_ok` is the Wrap ARITHMETIC verdict and is
/// read ONLY on a checkpoint call — an unavailable prover passes `false` here and NEVER a skip.
/// `finalized` / `run` are read back from persistence unmodified; `run_cap` is the client's own
/// policy for how long a provisional run may get before the cheap tier refuses to extend it.
pub fn mina_checkpoint_advance_wire(
    checkpoint: bool,
    wrap_ok: bool,
    finalized: u64,
    run: u64,
    run_cap: u64,
    sides: &MinaCheckpointSides<'_>,
) -> String {
    format!(
        "md={};wk={};fz={finalized};rn={run};rc={run_cap};ph={};th={};vh={};ch={};\
         p={};t={};v={};c={}",
        if checkpoint { 'c' } else { 'p' },
        u8::from(wrap_ok),
        sides.parent_state_hash,
        sides.tip_state_hash,
        sides.verified_state_hash,
        sides.candidate_state_hash,
        hex_lower(sides.parent_protocol_state),
        hex_lower(sides.tip_protocol_state),
        hex_lower(sides.verified_protocol_state),
        hex_lower(sides.candidate_protocol_state),
    )
}

/// Run the VERIFIED gate `@[export] dregg_mina_checkpoint_advance` over a pre-built wire and return
/// the raw output (`"mv=B;adv=B;fin=N;rn=N"` / `"ERR"`). `Err` when the archive did not export it.
pub fn shadow_mina_checkpoint_advance(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi_mina_checkpoint_advance::call(wire)
}

/// Strict decode of the checkpoint gate's output. Anything that is not exactly
/// `"mv=" B ";adv=" B ";fin=" u64 ";rn=" u64` — including the gate's own `"ERR"` — is an `Err`, and
/// the caller persists NOTHING: it keeps its tip, its verified head, its finalized height and its
/// run counter, all unchanged. There is no arm that returns an advance it did not read and none
/// that returns a `finalized` this side computed.
fn parse_checkpoint_roll(out: &str) -> Result<MinaCheckpointRoll, String> {
    if out == "ERR" {
        return Err(
            "the VERIFIED checkpoint gate REFUSED this step: a malformed wire, an odd-length hex \
             string, a byte string that is not a `Protocol_state.Value`, a side whose bytes do not \
             hash to the state hash presented with them, or carried constants that disagree with \
             the pinned mainnet ones. Nothing moved and nothing is to be persisted"
                .to_string(),
        );
    }
    let v = parse_kv_ordered(out, &["mv", "adv", "fin", "rn"])?;
    let bit = |s: &str, key: &str| -> Result<bool, String> {
        match s {
            "1" => Ok(true),
            "0" => Ok(false),
            _ => Err(format!(
                "the gate returned a non-boolean `{key}` field `{s}`"
            )),
        }
    };
    let num = |s: &str, key: &str| -> Result<u64, String> {
        if !all_decimal(s) {
            return Err(format!(
                "the gate returned a non-decimal `{key}` field `{s}`"
            ));
        }
        s.parse::<u64>()
            .map_err(|e| format!("the gate returned an unrepresentable `{key}` field `{s}`: {e}"))
    };
    Ok(MinaCheckpointRoll {
        tip_moved: bit(&v[0], "mv")?,
        advanced: bit(&v[1], "adv")?,
        finalized: num(&v[2], "fin")?,
        run: num(&v[3], "rn")?,
    })
}

/// ⚑⚑ **THE PER-CHECKPOINT LOOP.** Present ONE candidate — with its parent — to the two-tier head
/// and get back everything the client must persist.
///
/// ⚑ ONE CANDIDATE, ONE CALL, against the head as it stands after the previous call. Not a fold:
/// `MinaChainSelection.beats_not_transitive` proves `select` has genuine 3-cycles at real mainnet
/// constants, so a "best of a set" is a function of presentation order and a hostile peer picks the
/// order. What survives that is the ratchet, and the ratchet is why the cycles are harmless: they
/// are contained to the provisional tier, which decides nothing.
///
/// `Err` on an absent archive and on every refusal alike, because both mean the same thing to the
/// caller — persist nothing, keep what you hold.
pub fn verified_mina_checkpoint_advance(
    checkpoint: bool,
    wrap_ok: bool,
    finalized: u64,
    run: u64,
    run_cap: u64,
    sides: &MinaCheckpointSides<'_>,
) -> Result<MinaCheckpointRoll, String> {
    let wire = mina_checkpoint_advance_wire(checkpoint, wrap_ok, finalized, run, run_cap, sides);
    let out = shadow_mina_checkpoint_advance(&wire)?;
    parse_checkpoint_roll(&out)
}

#[cfg(all(lean_lib_present, dregg_mina_checkpoint_advance_present))]
mod ffi_mina_checkpoint_advance {
    use std::ffi::CString;
    use std::os::raw::c_char;

    extern "C" {
        fn dregg_mina_checkpoint_advance_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
    }

    pub fn present() -> bool {
        true
    }

    pub fn call(wire: &str) -> Result<String, String> {
        let c_in = CString::new(wire).map_err(|e| format!("wire has interior NUL: {e}"))?;
        let mut cap = 256;
        loop {
            let mut buf = vec![0u8; cap];
            let full = unsafe {
                dregg_mina_checkpoint_advance_str(
                    c_in.as_ptr(),
                    buf.as_mut_ptr() as *mut c_char,
                    cap,
                )
            };
            if full == usize::MAX {
                return Err("dregg_mina_checkpoint_advance_str: unusable output buffer".into());
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

#[cfg(not(all(lean_lib_present, dregg_mina_checkpoint_advance_present)))]
mod ffi_mina_checkpoint_advance {
    pub fn present() -> bool {
        false
    }

    pub fn call(_wire: &str) -> Result<String, String> {
        Err(
            "dregg_mina_checkpoint_advance not exported by the linked archive (rebuild to enable). \
             There is NO Rust twin and there must not be one"
                .into(),
        )
    }
}

#[cfg(test)]
mod checkpoint_advance_tests {
    use super::*;

    /// Four distinguishable byte strings, so a wire that transposed two sides would be visible.
    fn sides<'a>(
        parent: &'a [u8],
        tip: &'a [u8],
        verified: &'a [u8],
        candidate: &'a [u8],
    ) -> MinaCheckpointSides<'a> {
        MinaCheckpointSides {
            parent_state_hash: "11",
            parent_protocol_state: parent,
            tip_state_hash: "22",
            tip_protocol_state: tip,
            verified_state_hash: "33",
            verified_protocol_state: verified,
            candidate_state_hash: "44",
            candidate_protocol_state: candidate,
        }
    }

    /// The wire grammar is EXACTLY what `MinaCheckpoint.parseCheckpointWire` splits on: five
    /// leading `key=value` fields then eight more, `;`-separated, in that order. A field out of
    /// position is a refusal in the Lean, not a re-ordered read, so this is a byte-level contract
    /// and not a formatting preference.
    #[test]
    fn wire_grammar_matches_lean_parseCheckpointWire() {
        let s = sides(b"\x01", b"\x02", b"\x03", b"\x04");
        assert_eq!(
            mina_checkpoint_advance_wire(false, false, 7, 3, 20, &s),
            "md=p;wk=0;fz=7;rn=3;rc=20;ph=11;th=22;vh=33;ch=44;p=01;t=02;v=03;c=04"
        );
        // The CHECKPOINT tier and an affirmative Wrap verdict are the only two fields that differ.
        assert_eq!(
            mina_checkpoint_advance_wire(true, true, 7, 3, 20, &s),
            "md=c;wk=1;fz=7;rn=3;rc=20;ph=11;th=22;vh=33;ch=44;p=01;t=02;v=03;c=04"
        );
        // Thirteen fields, exactly — `parseCheckpointWire` matches `m :: w :: z :: n :: r :: rest`
        // and then `rest` against a list of EXACTLY eight.
        assert_eq!(
            mina_checkpoint_advance_wire(false, false, 0, 0, 0, &s)
                .split(';')
                .count(),
            13
        );
    }

    /// ⚑ THE CFG-OFF POLE, asserted by exact message rather than `is_err()`. With
    /// `dregg_mina_checkpoint_advance_present` unset the gate is a REFUSAL that names itself — not
    /// a Rust two-tier head, not a permissive default, and not a silent `Ok`.
    #[cfg(not(all(lean_lib_present, dregg_mina_checkpoint_advance_present)))]
    #[test]
    fn absent_export_refuses_and_names_itself() {
        assert!(
            !mina_checkpoint_advance_available(),
            "the checkpoint gate must not report available when the cfg is off"
        );
        let s = sides(b"\x01", b"\x02", b"\x03", b"\x04");
        let err = verified_mina_checkpoint_advance(true, true, 100, 0, 20, &s)
            .expect_err("an absent export must never yield a roll to persist");
        assert_eq!(
            err,
            "dregg_mina_checkpoint_advance not exported by the linked archive (rebuild to \
             enable). There is NO Rust twin and there must not be one"
        );
        // ⚑ And a CHECKPOINT call with `wrap_ok = true` and a large `finalized` is refused too —
        // the one shape a fail-OPEN fallback would have been tempting for.
        assert_eq!(
            shadow_mina_checkpoint_advance("md=c;wk=1;fz=999;rn=0;rc=20").unwrap_err(),
            "dregg_mina_checkpoint_advance not exported by the linked archive (rebuild to \
             enable). There is NO Rust twin and there must not be one"
        );
    }

    /// ⚑ THE CFG-ON POLE. With the cfg set the module is the `extern "C"` one, the availability
    /// probe is true (given a healthy init), and the gate answers rather than refusing structurally.
    #[cfg(all(lean_lib_present, dregg_mina_checkpoint_advance_present))]
    #[test]
    fn present_export_is_entered_and_refuses_garbage() {
        assert!(
            mina_checkpoint_advance_available(),
            "the cfg is set and the archive is linked — the gate must be enterable"
        );
        // The gate was ENTERED (an absent export would be `Err` here, not `Ok("ERR")`), and its
        // refusal is a refusal rather than a verdict computed from what did parse.
        assert_eq!(
            shadow_mina_checkpoint_advance("garbage").as_deref(),
            Ok("ERR")
        );
        // …and a REFUSAL never becomes something to persist.
        let s = sides(b"\x00", b"\x00", b"\x00", b"\x00");
        assert!(
            verified_mina_checkpoint_advance(true, true, 539_897, 0, 20, &s).is_err(),
            "bytes that are not a protocol state must not yield a roll to persist"
        );
    }

    /// The answer parser is STRICT and ORDERED. A gate that grew a field, dropped one, reordered
    /// two or answered a non-number must not be read as a partially-parsed roll — every one of
    /// these is a refusal, and none of them silently persists a `finalized`.
    #[test]
    fn the_roll_parser_refuses_every_shape_but_the_one() {
        assert_eq!(
            parse_checkpoint_roll("mv=1;adv=1;fin=539897;rn=0"),
            Ok(MinaCheckpointRoll {
                tip_moved: true,
                advanced: true,
                finalized: 539_897,
                run: 0
            })
        );
        assert_eq!(
            parse_checkpoint_roll("mv=0;adv=0;fin=0;rn=7"),
            Ok(MinaCheckpointRoll {
                tip_moved: false,
                advanced: false,
                finalized: 0,
                run: 7
            })
        );
        // The gate's own fail-closed answer.
        assert!(parse_checkpoint_roll("ERR")
            .unwrap_err()
            .contains("REFUSED this step"));
        // Field count.
        assert_eq!(
            parse_checkpoint_roll("mv=1;adv=1;fin=5").unwrap_err(),
            "the gate answered 3 field(s), expected 4 ([\"mv\", \"adv\", \"fin\", \"rn\"])"
        );
        // Field ORDER — `adv` arriving where `mv` belongs is not a roll with the fields swapped.
        assert_eq!(
            parse_checkpoint_roll("adv=1;mv=1;fin=5;rn=0").unwrap_err(),
            "field adv is not the expected `mv`"
        );
        // A bit that is not a bit. `2` is not "truthy".
        assert_eq!(
            parse_checkpoint_roll("mv=2;adv=0;fin=5;rn=0").unwrap_err(),
            "the gate returned a non-boolean `mv` field `2`"
        );
        // A ratchet that is not a number, and one that is signed.
        assert_eq!(
            parse_checkpoint_roll("mv=0;adv=0;fin=-1;rn=0").unwrap_err(),
            "the gate returned a non-decimal `fin` field `-1`"
        );
        assert_eq!(
            parse_checkpoint_roll("mv=0;adv=0;fin=5;rn=x").unwrap_err(),
            "the gate returned a non-decimal `rn` field `x`"
        );
    }
}
