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
}
