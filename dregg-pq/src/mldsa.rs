//! The canonical ML-DSA-65 (FIPS 204) signing primitive: one from-seed
//! derivation, one sign, one fail-closed verify. Domain separation (FIPS 204
//! `ctx`) is supplied by the caller on every call, so the same key material can
//! never produce a signature valid on two surfaces.

use fips204::ml_dsa_65;
use fips204::traits::{KeyGen as _, SerDes as _, Signer as _, Verifier as _};
use std::sync::OnceLock;

use crate::audit::PqSite;

/// A pluggable, Lean-VERIFIED ML-DSA verify backend, installed by an integration layer.
///
/// The extracted core lives in `metatheory/Dregg2/Crypto/Fips204Verify.lean`
/// (`verifyCore` = the `Fips204Spec.MlDsaParams.verifyB` predicate at the deployed ML-DSA-65
/// parameters), `@[export]`ed as `dregg_fips204_verify` and compiled to leanc-native code. It is
/// ★ SCOPE — READ THE LEAN STATEMENTS, NOT THIS PROSE. This core is the SCALAR MODEL, not
/// ML-DSA-65. `Fips204Verify.realParams` is an `n = 1` instance over `ℤ` with `A := LinearMap.id`,
/// `challenge _ := 1` (constant), and `hash μ hb := μ + 8380417 * hb` (linear) — real only in its
/// rounding constants. It is NOT the same object as `MlDsaVerifyReal.verifyCore`, which is the
/// full-dimension byte-level verifier over real 1952-byte keys / 3309-byte signatures.
/// ★ `verifyCore_unfolds_to_def` IS NOT A SPEC-AGREEMENT WARRANT: it is `:= rfl` on `verifyCore`'s
/// own definiens (`verifyCore` is DEFINED as `realParams.verifyB`), i.e. `P = P`. Its own Lean
/// docstring states verbatim: "IT IS NOT EVIDENCE OF SPEC AGREEMENT ... it would hold verbatim for
/// any `realParams` whatsoever, including a broken one." Do not cite it as a proof that the
/// deployed verify is correct. What it records is only that the `@[export]`ed object is a plain
/// alias — nothing was re-implemented between the `def` and the FFI. It discharges
/// `DreggPqRefinement.Fips204Correct` for the verify direction (`extractedApi_fips204`) — no `fips204`
/// crate is trusted for the round-trip. `dregg-lean-ffi::shadow_fips204_verify` runs it natively.
///
/// dregg-pq stays a LIGHT leaf (9 crates depend on it): it takes a function pointer, never a
/// dependency on the Lean archive — the same discipline the storage extraction used (its round-trip
/// lives in `dregg-lean-ffi`, not the `storage` leaf). An integration layer installs the native core
/// via [`install_lean_verify_core`]; [`ml_dsa_verify_core`] then routes the SECURITY-CRITICAL verify
/// through the Lean-verified object rather than a trusted primitive.
type LeanVerifyCore = fn(wire: &str) -> Option<String>;
static LEAN_VERIFY_CORE: OnceLock<LeanVerifyCore> = OnceLock::new();

/// Install the extracted, Lean-verified ML-DSA verify core (e.g.
/// `|w| dregg_lean_ffi::shadow_fips204_verify(w).ok()`). Returns `false` if one is already installed
/// (the install is once-per-process; the verified core is not hot-swappable).
pub fn install_lean_verify_core(core: LeanVerifyCore) -> bool {
    LEAN_VERIFY_CORE.set(core).is_ok()
}

/// Route a deployed-parameter ML-DSA verify statement `"thi μ c̃ z h"` (the wire the extracted Lean
/// `verifyFFI` reads) through the installed Lean-verified verify core. `Some(true)` = accept,
/// `Some(false)` = reject (a forged/tampered statement), `None` = no core installed (caller falls back
/// to the `fips204` primitive). This is the routing seam that sends the security-critical verify
/// through the `Fips204Correct`-discharging Lean object; the full-byte-codec path over real 1952/3309-
/// byte keys/signatures is the named engineering residual (`Fips204Verify.lean`).
pub fn ml_dsa_verify_core(wire: &str) -> Option<bool> {
    let core = LEAN_VERIFY_CORE.get()?;
    match core(wire)?.as_str() {
        "1" => Some(true),
        _ => Some(false),
    }
}

/// A pluggable, Lean-VERIFIED **REAL, FULL-BYTE** ML-DSA verify backend (BRICK 8), installed by an
/// integration layer. Where [`LeanVerifyCore`] carries the `A=id` SCALAR reduction over a 5-integer toy
/// wire, THIS core carries the FULL-DIMENSION ML-DSA-65 verify over the actual `pk ‖ msg ‖ ctx ‖ sig`
/// bytes.
///
/// The extracted core is `Dregg2.Crypto.Fips204Verify.verifyRealFFI` over `MlDsaVerifyReal.verifyCore`
/// (the `n=256` negacyclic ring / NTT / SampleInBall / ExpandA / real 1952/3309-byte codec), `@[export]`ed
/// as `dregg_fips204_verify_real` and compiled to leanc-native code. It is PROVED (`native_decide`) to
/// ACCEPT a genuine `fips204` v0.4.6 crate signature (`verify_accepts_real`) and REJECT a one-byte tamper /
/// wrong message (`verify_rejects_tampered`, `verify_rejects_wrong_msg`). `dregg-lean-ffi::
/// shadow_fips204_verify_real` runs it natively.
///
/// dregg-pq stays a LIGHT leaf (it never depends on the 195 MB Lean archive): it takes a function pointer.
/// An integration layer that CAN link the archive installs the native core via
/// [`install_lean_verify_core_real`]; once installed, [`ml_dsa_verify`] takes its accept/reject verdict
/// from the Lean-verified object over the real bytes — the `fips204` crate is NO LONGER the verify
/// authority. The wire is `"hex(pk) hex(msg) hex(ctx) hex(sig)"`; the reply is `"1"` (accept) / `"0"`
/// (reject / malformed).
type LeanVerifyCoreReal = fn(wire: &str) -> Option<String>;
static LEAN_VERIFY_CORE_REAL: OnceLock<LeanVerifyCoreReal> = OnceLock::new();

/// Install the extracted, Lean-verified REAL, full-byte ML-DSA verify core (e.g.
/// `|w| dregg_lean_ffi::shadow_fips204_verify_real(w).ok()`). Once installed, [`ml_dsa_verify`] routes the
/// SECURITY-CRITICAL accept/reject through it — taking the `fips204` crate OUT of the verify TCB. Returns
/// `false` if one is already installed (once-per-process; the verified core is not hot-swappable).
pub fn install_lean_verify_core_real(core: LeanVerifyCoreReal) -> bool {
    LEAN_VERIFY_CORE_REAL.set(core).is_ok()
}

/// Whether a Lean-verified REAL verify core has been installed (so [`ml_dsa_verify`] is Lean-backed rather
/// than routed to the `fips204` crate). A deployed, verified node installs one at startup.
pub fn lean_verify_core_real_installed() -> bool {
    LEAN_VERIFY_CORE_REAL.get().is_some()
}

/// Outcome of installing the Lean-verified REAL ML-DSA verify core as [`ml_dsa_verify`]'s authority
/// (via [`install_verified_mldsa_verify_core`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MlDsaVerifyCoreInstall {
    /// The real core was installed by THIS call — the `fips204` crate is now out of the verify TCB.
    Installed,
    /// A core was already installed this process (install is once-per-process) — crate still out of TCB.
    AlreadyInstalled,
    /// The linked Lean archive does not export the real verify core; the `fips204`-crate fallback stays
    /// in place (a valid FIPS-204 verify, but NOT the Lean-verified authority).
    ExportAbsent,
}

/// THE ONE install every deployed, archive-linked process calls to make the Lean-verified REAL, full-byte
/// ML-DSA verify core ([`install_lean_verify_core_real`]) the accept/reject AUTHORITY behind
/// [`ml_dsa_verify`] — taking the `fips204` crate OUT of that process's verify TCB.
///
/// dregg-pq stays a LIGHT leaf: the two archive-dependent symbols are INJECTED as `fn` pointers rather than
/// depended on. Every host (node, the SDK-hosted wire silo, starbridge-v2, …) passes the SAME two
/// `dregg-lean-ffi` symbols:
///
/// ```ignore
/// dregg_pq::install_verified_mldsa_verify_core(
///     dregg_lean_ffi::fips204_verify_real_core_available,
///     |w| dregg_lean_ffi::shadow_fips204_verify_real(w).ok(),
/// )
/// ```
///
/// so the gating + install + once-per-process semantics live in ONE tested function (and the CI guard has a
/// single grep target) instead of copy-pasted per process.
///
/// Gated on `export_available()` (the `fips204_verify_real_core_available()` check): install ONLY when the
/// linked archive actually EXPORTS the real core. A stale archive lacking it would make the installed core
/// return `None` on every call and — because [`ml_dsa_verify`] fails CLOSED on a core fault — reject every
/// signature; so when the export is absent we return [`MlDsaVerifyCoreInstall::ExportAbsent`] and keep the
/// `fips204`-crate fallback (a valid FIPS-204 verify) rather than bricking verify. Idempotent and
/// once-per-process.
pub fn install_verified_mldsa_verify_core(
    export_available: fn() -> bool,
    shadow: fn(wire: &str) -> Option<String>,
) -> MlDsaVerifyCoreInstall {
    if !export_available() {
        return MlDsaVerifyCoreInstall::ExportAbsent;
    }
    if install_lean_verify_core_real(shadow) {
        MlDsaVerifyCoreInstall::Installed
    } else {
        MlDsaVerifyCoreInstall::AlreadyInstalled
    }
}

/// Marshal `(pk, msg, ctx, sig)` into the byte wire the Lean real verify core reads:
/// `"hex(pk) hex(msg) hex(ctx) hex(sig)"` (four space-separated lowercase-hex fields; an empty field is the
/// empty token between two spaces).
fn real_verify_wire(pk: &[u8], msg: &[u8], ctx: &[u8], sig: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity((pk.len() + msg.len() + ctx.len() + sig.len()) * 2 + 3);
    for (i, field) in [pk, msg, ctx, sig].into_iter().enumerate() {
        if i != 0 {
            s.push(' ');
        }
        for &b in field {
            s.push(HEX[(b >> 4) as usize] as char);
            s.push(HEX[(b & 0x0f) as usize] as char);
        }
    }
    s
}

/// A pluggable, Lean-VERIFIED ML-DSA SIGN backend, installed by an integration layer (the mirror of
/// [`LeanVerifyCore`] for the signing direction).
///
/// The extracted core is `Dregg2.Crypto.Fips204Verify.signCore` — the DETERMINISTIC
/// Fiat–Shamir-with-aborts signer (`sk → μ → randomness → Option Sig`) at the deployed ML-DSA-65
/// parameters, `@[export]`ed as `dregg_fips204_sign` and compiled to leanc-native code. It is PROVED to
/// ★ SCOPE: like the verify core above, this is the SCALAR `realParams` model (`s1 s2 t0 μ y : ℤ`,
/// `A = id`, constant challenge), NOT full-dimension ML-DSA-65 — for that see
/// `MlDsaSignReal.signCore` over real 4032-byte `sk` / 3309-byte signatures. `signCore_eq_spec` is
/// a DEFINITIONAL unfolding (`simp only [signCore, h, if_true]`): on an accepted iteration the
/// `if`'s true branch IS `realParams.sign`. That is an alias record, not evidence the scalar model
/// is ML-DSA. Together with the extracted `verifyCore` it discharges
/// `DreggPqRefinement.Fips204Correct` FULLY (`signExtractedApi_fips204`) — no `fips204` crate is trusted
/// for the sign→verify round-trip. `dregg-lean-ffi::shadow_fips204_sign` runs it natively.
///
/// Same light-leaf discipline as the verify core: dregg-pq takes a function pointer, never a dependency
/// on the Lean archive. An integration layer installs the native core via [`install_lean_sign_core`];
/// [`ml_dsa_sign_core`] then routes the signing path through the Lean-verified object.
type LeanSignCore = fn(wire: &str) -> Option<String>;
static LEAN_SIGN_CORE: OnceLock<LeanSignCore> = OnceLock::new();

/// Install the extracted, Lean-verified ML-DSA sign core (e.g.
/// `|w| dregg_lean_ffi::shadow_fips204_sign(w).ok()`). Returns `false` if one is already installed
/// (once-per-process; the verified core is not hot-swappable).
pub fn install_lean_sign_core(core: LeanSignCore) -> bool {
    LEAN_SIGN_CORE.set(core).is_ok()
}

/// Whether a Lean-verified sign core has been installed behind [`ml_dsa_sign_core`]. NOTE: the installed
/// object is the SCALAR (n=1) `signCore`, so this being `true` does NOT mean the deployed byte-level signer
/// ([`MlDsaKey::sign`]) is Lean-backed — that path still uses the `fips204` crate (the real full-byte sign
/// core is a named follow-up; see [`install_lean_verify_core_real`] for the verify-side equivalent that IS
/// deployed).
pub fn lean_sign_core_installed() -> bool {
    LEAN_SIGN_CORE.get().is_some()
}

/// Route a deployed-parameter ML-DSA sign request `"s₁ s₂ t₀ μ y"` (the wire the extracted Lean
/// `signFFI` reads — secret `(s₁,s₂,t₀)`, message `μ`, and the sampled randomness/mask `y`) through the
/// installed Lean-verified sign core. The outer `Option` is the install state; the inner `Option` is the
/// rejection-sampling verdict:
///
///   * `None`                 — no core installed (caller falls back to the `fips204` primitive).
///   * `Some(None)`           — the sample was REJECTED (norm/hint gate failed); the caller resamples
///                              `y` and retries (the Dilithium rejection loop) — an honest reject, not a
///                              fake accept.
///   * `Some(Some(sig_wire))` — an ACCEPTED signature `"c̃ z h"` (three ints), exactly what
///                              [`ml_dsa_verify_core`] verifies after the `"thi μ "` prefix.
///
/// This is the routing seam that sends the signing path through the `Fips204Correct`-discharging Lean
/// object; the full-byte-codec path over real keys/signatures is the named engineering residual
/// (`Fips204Verify.lean`).
pub fn ml_dsa_sign_core(wire: &str) -> Option<Option<String>> {
    let core = LEAN_SIGN_CORE.get()?;
    match core(wire)?.as_str() {
        "REJECT" => Some(None),
        sig => Some(Some(sig.to_string())),
    }
}

/// A pluggable, Lean-VERIFIED **REAL, FULL-BYTE** ML-DSA SIGN backend (the brick-8 SIGN analog), installed
/// by an integration layer. Where [`LeanSignCore`] carries the `A=id` SCALAR reduction over a 5-int toy
/// wire, THIS core carries the FULL-DIMENSION ML-DSA-65 signer over the actual `sk ‖ msg ‖ ctx` bytes.
///
/// The extracted core is `Dregg2.Crypto.MlDsaSignReal.signRealFFI` over `signCore` (the `n=256` negacyclic
/// ring / NTT / SampleInBall / ExpandA / MakeHint / rejection loop / real 4032/3309-byte codec), `@[export]`ed
/// as `dregg_fips204_sign_real` and compiled to leanc-native code. It is PROVED (`native_decide`)
/// to reproduce NIST's OWN published expected signature byte-for-byte on the COMPLETE NIST ACVP
/// `ML-DSA-sigGen-FIPS204` group for this parameter set — `MlDsaSigGenAcvp.sign_matches_acvp_group`,
/// all 15 cases of `tgId = 3` (ML-DSA-65, deterministic, external, pure), `tcId` 31-45, messages
/// 1-8192 B and contexts 0-255 B. The anchor is NIST, NOT the `fips204` crate. Its output is also
/// accepted by `MlDsaVerifyReal.verifyCore` across the whole group
/// (`MlDsaSigGenAcvp.sign_verify_agree_acvp_group`).
/// ★ THESE ARE KATs, NOT REFINEMENT THEOREMS: 15 concrete inputs, NO `forall`. The for-all-inputs
/// obligation is `SignCoreSpec` and it is OPEN. Widening from the previous single vector
/// (`sign_matches_acvp_deterministic`, `tcId = 36`, which is the group's SHORTEST message at 1 byte)
/// removes the cherry-picked-vector objection; it does not convert a KAT into a proof.
/// `dregg-lean-ffi::shadow_fips204_sign_real` runs it natively.
///
/// dregg-pq stays a LIGHT leaf (it never depends on the 195 MB Lean archive): it takes a function pointer.
/// An integration layer that CAN link the archive installs the native core via
/// [`install_lean_sign_core_real`]; once installed, [`MlDsaKey::try_sign`] / [`ml_dsa_sign_from_seed`]
/// PRODUCE the signature via the Lean-verified object over the real bytes — the `fips204` crate is NO LONGER
/// the signing authority. The wire is `"hex(sk) hex(msg) hex(ctx)"`; the reply is `hex(sig)` (accepted) or
/// `"ERR"` (malformed wire).
///
/// ⚠ DETERMINISTIC: the Lean `signCore` is the `rnd = 0` deterministic variant, so on the installed path the
/// deployed signer is DETERMINISTIC (the FIPS 204 deterministic signing variant — spec-valid; the crate
/// fallback path is hedged/randomized). Same 32-byte seed + ctx + message ⇒ identical signature bytes.
type LeanSignCoreReal = fn(wire: &str) -> Option<String>;
static LEAN_SIGN_CORE_REAL: OnceLock<LeanSignCoreReal> = OnceLock::new();

/// Install the extracted, Lean-verified REAL, full-byte ML-DSA sign core (e.g.
/// `|w| dregg_lean_ffi::shadow_fips204_sign_real(w).ok()`). Once installed, [`MlDsaKey::try_sign`] PRODUCES
/// the signature through it — taking the `fips204` crate OUT of the sign TCB. Returns `false` if one is
/// already installed (once-per-process; the verified core is not hot-swappable).
pub fn install_lean_sign_core_real(core: LeanSignCoreReal) -> bool {
    LEAN_SIGN_CORE_REAL.set(core).is_ok()
}

/// Whether a Lean-verified REAL sign core has been installed (so [`MlDsaKey::try_sign`] is Lean-backed rather
/// than crate-signed). A deployed, verified node installs one at startup.
pub fn lean_sign_core_real_installed() -> bool {
    LEAN_SIGN_CORE_REAL.get().is_some()
}

/// Outcome of installing the Lean-verified REAL ML-DSA sign core as [`MlDsaKey::try_sign`]'s producer
/// (via [`install_verified_mldsa_sign_core_real`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MlDsaSignCoreRealInstall {
    /// The real core was installed by THIS call — the `fips204` crate is now out of the sign TCB.
    Installed,
    /// A core was already installed this process (install is once-per-process) — crate still out of TCB.
    AlreadyInstalled,
    /// The linked Lean archive does not export the real sign core; the `fips204`-crate fallback stays in
    /// place (a valid FIPS-204 sign, but NOT the Lean-verified producer).
    ExportAbsent,
}

/// THE ONE install every deployed, archive-linked process calls to make the Lean-verified REAL, full-byte
/// ML-DSA sign core ([`install_lean_sign_core_real`]) the PRODUCER behind [`MlDsaKey::try_sign`] /
/// [`ml_dsa_sign_from_seed`] — taking the `fips204` crate OUT of that process's sign TCB.
///
/// dregg-pq stays a LIGHT leaf: the two archive-dependent symbols are INJECTED as `fn` pointers rather than
/// depended on. Every host passes the SAME two `dregg-lean-ffi` symbols:
///
/// ```ignore
/// dregg_pq::install_verified_mldsa_sign_core_real(
///     dregg_lean_ffi::fips204_sign_real_core_available,
///     |w| dregg_lean_ffi::shadow_fips204_sign_real(w).ok(),
/// )
/// ```
///
/// Gated on `export_available()` (the `fips204_sign_real_core_available()` check): install ONLY when the
/// linked archive actually EXPORTS the real core. A stale archive lacking it would make the installed core
/// return `None` on every call and — because [`MlDsaKey::try_sign`] fails CLOSED on a core fault — produce
/// no signature; so when the export is absent we return [`MlDsaSignCoreRealInstall::ExportAbsent`] and keep
/// the `fips204`-crate fallback (a valid FIPS-204 sign) rather than bricking sign. Idempotent and
/// once-per-process.
pub fn install_verified_mldsa_sign_core_real(
    export_available: fn() -> bool,
    shadow: fn(wire: &str) -> Option<String>,
) -> MlDsaSignCoreRealInstall {
    if !export_available() {
        return MlDsaSignCoreRealInstall::ExportAbsent;
    }
    if install_lean_sign_core_real(shadow) {
        MlDsaSignCoreRealInstall::Installed
    } else {
        MlDsaSignCoreRealInstall::AlreadyInstalled
    }
}

/// Marshal `(sk, msg, ctx)` into the byte wire the Lean real sign core reads:
/// `"hex(sk) hex(msg) hex(ctx)"` (three space-separated lowercase-hex fields; an empty field is the empty
/// token between two spaces).
fn real_sign_wire(sk: &[u8], msg: &[u8], ctx: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity((sk.len() + msg.len() + ctx.len()) * 2 + 2);
    for (i, field) in [sk, msg, ctx].into_iter().enumerate() {
        if i != 0 {
            s.push(' ');
        }
        for &b in field {
            s.push(HEX[(b >> 4) as usize] as char);
            s.push(HEX[(b & 0x0f) as usize] as char);
        }
    }
    s
}

/// Decode a lowercase-hex string (the Lean real sign core's `hex(sig)` reply) back to bytes. Returns `None`
/// on an odd length or any non-hex character (so a `"ERR"` reply or a garbled wire fails CLOSED at the
/// caller — no partial/spurious signature).
fn decode_hex(s: &str) -> Option<Vec<u8>> {
    if s.len() % 2 != 0 {
        return None;
    }
    fn nibble(c: u8) -> Option<u8> {
        match c {
            b'0'..=b'9' => Some(c - b'0'),
            b'a'..=b'f' => Some(c - b'a' + 10),
            b'A'..=b'F' => Some(c - b'A' + 10),
            _ => None,
        }
    }
    let bytes = s.as_bytes();
    let mut out = Vec::with_capacity(bytes.len() / 2);
    for pair in bytes.chunks_exact(2) {
        out.push((nibble(pair[0])? << 4) | nibble(pair[1])?);
    }
    Some(out)
}

/// A pluggable, Lean-VERIFIED ML-DSA-65 KEYGEN backend, installed by an integration layer that can link
/// `dregg-lean-ffi`. The extracted core lives in `metatheory/Dregg2/Crypto/MlDsaKeygen.lean`
/// (`mldsaKeygenInternal` = the deterministic FIPS 204 ML-DSA.KeyGen_internal at ML-DSA-65 parameters),
/// `@[export]`ed as `dregg_mldsa_keygen_real` and compiled to leanc-native code. It is KAT-anchored
/// byte-exact vs the NIST ACVP `ML-DSA-keyGen-FIPS204` ML-DSA-65 vectors (single-vector `native_decide`);
/// the byte↔ring KeyGen refinement forall is OPEN. `dregg-lean-ffi::shadow_mldsa_keygen_real` runs it
/// natively. The wire is `"hex(xi)"` (the 32-byte ξ seed); the reply is `"hex(pk) hex(sk)"` or `"ERR"`.
type LeanKeygenCoreReal = fn(wire: &str) -> Option<String>;
static LEAN_KEYGEN_CORE_REAL: OnceLock<LeanKeygenCoreReal> = OnceLock::new();

/// Install the extracted, Lean-verified REAL, full-byte ML-DSA-65 keygen core (e.g.
/// `|w| dregg_lean_ffi::shadow_mldsa_keygen_real(w).ok()`). Once installed, [`MlDsaKey::from_ed25519_seed`]
/// EXPANDS the seed through it — taking the `fips204` crate OUT of the IDENTITY-KEY keygen TCB. Returns
/// `false` if one is already installed (once-per-process; the verified core is not hot-swappable).
pub fn install_lean_keygen_core_real(core: LeanKeygenCoreReal) -> bool {
    LEAN_KEYGEN_CORE_REAL.set(core).is_ok()
}

/// Whether a Lean-verified REAL keygen core has been installed (so [`MlDsaKey::from_ed25519_seed`] is
/// Lean-backed rather than crate-expanded). A deployed, verified node installs one at startup.
pub fn lean_keygen_core_real_installed() -> bool {
    LEAN_KEYGEN_CORE_REAL.get().is_some()
}

/// Outcome of installing the Lean-verified REAL ML-DSA keygen core as [`MlDsaKey::from_ed25519_seed`]'s
/// expander (via [`install_verified_mldsa_keygen_core_real`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MlDsaKeygenCoreRealInstall {
    /// The real core was installed by THIS call — the `fips204` crate is now out of the keygen TCB.
    Installed,
    /// A core was already installed this process (install is once-per-process) — crate still out of TCB.
    AlreadyInstalled,
    /// The linked Lean archive does not export the real keygen core; the `fips204`-crate fallback stays
    /// in place (a valid FIPS-204 keygen, but NOT the Lean-verified expander).
    ExportAbsent,
}

/// THE ONE install every deployed, archive-linked process calls to make the Lean-verified REAL, full-byte
/// ML-DSA-65 keygen core ([`install_lean_keygen_core_real`]) the EXPANDER behind
/// [`MlDsaKey::from_ed25519_seed`] — taking the `fips204` crate OUT of that process's IDENTITY-KEY keygen
/// TCB.
///
/// ```ignore
/// dregg_pq::install_verified_mldsa_keygen_core_real(
///     dregg_lean_ffi::mldsa_keygen_real_core_available,
///     |w| dregg_lean_ffi::shadow_mldsa_keygen_real(w).ok(),
/// )
/// ```
///
/// Gated on `export_available()`: install ONLY when the linked archive actually EXPORTS the real core. A
/// stale archive lacking it would make the installed core return `None` on every call and — because
/// [`MlDsaKey::from_ed25519_seed`] fails CLOSED on the identity key (it will NOT silently fall back to the
/// unaudited crate once a core is installed) — brick identity-key derivation; so when the export is absent
/// we return [`MlDsaKeygenCoreRealInstall::ExportAbsent`] and keep the `fips204`-crate fallback (a valid
/// FIPS-204 keygen). Idempotent and once-per-process.
pub fn install_verified_mldsa_keygen_core_real(
    export_available: fn() -> bool,
    shadow: fn(wire: &str) -> Option<String>,
) -> MlDsaKeygenCoreRealInstall {
    if !export_available() {
        return MlDsaKeygenCoreRealInstall::ExportAbsent;
    }
    if install_lean_keygen_core_real(shadow) {
        MlDsaKeygenCoreRealInstall::Installed
    } else {
        MlDsaKeygenCoreRealInstall::AlreadyInstalled
    }
}

/// Marshal the 32-byte ξ seed into the byte wire the Lean real keygen core reads: `"hex(xi)"` (one
/// lowercase-hex field, 64 chars).
fn real_keygen_wire(seed: &[u8; 32]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(64);
    for &b in seed {
        s.push(HEX[(b >> 4) as usize] as char);
        s.push(HEX[(b & 0x0f) as usize] as char);
    }
    s
}

/// Serialized length of an ML-DSA-65 secret key (FIPS 204 = 4032 bytes).
pub const ML_DSA_SK_LEN: usize = ml_dsa_65::SK_LEN;

/// Serialized length of an ML-DSA-65 public key (FIPS 204 = 1952 bytes).
pub const ML_DSA_PK_LEN: usize = ml_dsa_65::PK_LEN;

/// Serialized length of an ML-DSA-65 signature (FIPS 204).
pub const ML_DSA_SIG_LEN: usize = ml_dsa_65::SIG_LEN;

/// The post-quantum half of a hybrid identity: an ML-DSA-65 signing key plus its
/// serialized public key, derived DETERMINISTICALLY from the SAME 32-byte
/// ed25519 seed the classical identity uses.
#[derive(Clone)]
pub struct MlDsaKey {
    secret: ml_dsa_65::PrivateKey,
    public_bytes: [u8; ml_dsa_65::PK_LEN],
}

impl core::fmt::Debug for MlDsaKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("MlDsaKey(..)")
    }
}

impl MlDsaKey {
    /// Derive the ML-DSA-65 keypair DETERMINISTICALLY from a 32-byte ed25519
    /// seed (`ML-DSA.KeyGen` from `ξ = seed`). Same seed → same PQ key, so the
    /// PQ public key matches across cipherclerk / node / genesis with no
    /// separate ceremony.
    pub fn from_ed25519_seed(seed: &[u8; 32]) -> Self {
        // AUTHORITY: the Lean-verified real ML-DSA-65 keygen core over the ξ seed, when installed
        // (`install_verified_mldsa_keygen_core_real`, done by any process that can link `dregg-lean-ffi`).
        // On this path the `fips204` crate does NOT expand the identity seed — it has left the identity-key
        // keygen TCB. The pk/sk bytes are PRODUCED by the extracted `mldsaKeygenInternal` (KAT-anchored vs
        // the NIST ACVP ML-DSA-65 keyGen vectors); the crate `PrivateKey` is only a container reconstructed
        // from the verified sk bytes so the (separately verified) signer can use it.
        if let Some(core) = LEAN_KEYGEN_CORE_REAL.get() {
            if let Some(key) = Self::from_verified_core(seed, *core) {
                return key;
            }
            // A core is installed but FAULTED (FFI/archive fault, `"ERR"`, wrong-length decode). For the
            // IDENTITY key we fail CLOSED and refuse to silently fall back to the unaudited crate — an
            // uncatchable abort, the same posture `crate::audit` uses for the unaudited fallback.
            crate::audit::abort_verified_core_fault(
                PqSite::MlDsaKeygen,
                "ML-DSA-65 KeyGen (deterministic, from the ed25519 seed)",
                "dregg_mldsa_keygen_real",
            );
        }
        // FALLBACK (no verified core installed): the `fips204` crate seed expansion. A verified core now
        // EXISTS and has an install fn, so this is the same shape as the sign/verify fallbacks — refuses
        // (aborts) unless DREGG_ALLOW_UNAUDITED_PQ=1, and names the install call. See `crate::audit`.
        crate::audit::guard_unaudited_fallback(
            PqSite::MlDsaKeygen,
            "ML-DSA-65 KeyGen (deterministic, from the ed25519 seed)",
            "fips204 0.4",
            "install_verified_mldsa_keygen_core_real",
        );
        let (pk, sk) = ml_dsa_65::KG::keygen_from_seed(seed);
        Self {
            secret: sk,
            public_bytes: pk.into_bytes(),
        }
    }

    /// Expand `seed` through the installed Lean-verified real keygen `core` and rebuild the `MlDsaKey` from
    /// its `"hex(pk) hex(sk)"` reply. `None` on any core fault (a `None`/`"ERR"` reply, a non-hex or
    /// wrong-length field, or a `PrivateKey` that fails to parse) so the caller fails CLOSED.
    fn from_verified_core(seed: &[u8; 32], core: LeanKeygenCoreReal) -> Option<Self> {
        let reply = core(&real_keygen_wire(seed))?;
        let mut fields = reply.split(' ');
        let pk = decode_hex(fields.next()?)?;
        let sk = decode_hex(fields.next()?)?;
        if fields.next().is_some() {
            return None;
        }
        if pk.len() != ml_dsa_65::PK_LEN || sk.len() != ml_dsa_65::SK_LEN {
            return None;
        }
        let mut pk_arr = [0u8; ml_dsa_65::PK_LEN];
        pk_arr.copy_from_slice(&pk);
        let mut sk_arr = [0u8; ml_dsa_65::SK_LEN];
        sk_arr.copy_from_slice(&sk);
        let secret = ml_dsa_65::PrivateKey::try_from_bytes(sk_arr).ok()?;
        Some(Self {
            secret,
            public_bytes: pk_arr,
        })
    }

    /// The serialized ML-DSA-65 public key — the value a verifier ENROLLS and
    /// PINS to this holder's identity.
    pub fn public_bytes(&self) -> Vec<u8> {
        self.public_bytes.to_vec()
    }

    /// Sign `message` under the caller-supplied FIPS 204 `ctx` (hedged from OS
    /// entropy). Panics only on the vanishingly rare internal RNG failure — use
    /// [`MlDsaKey::try_sign`] where a fail-closed (absent-half) result is wanted.
    pub fn sign(&self, ctx: &[u8], message: &[u8]) -> Vec<u8> {
        self.try_sign(ctx, message)
            .expect("ml-dsa sign failed (internal RNG)")
    }

    /// Sign `message` under the caller-supplied FIPS 204 `ctx`. `None` only on
    /// the vanishingly rare internal RNG failure, which then fails CLOSED at
    /// verification (a present-but-absent PQ half rejects the hybrid).
    ///
    /// # The signature bytes come from the Lean-verified core, not the crate
    ///
    /// When a Lean-verified REAL sign core is installed ([`install_lean_sign_core_real`], done by any
    /// process that can link `dregg-lean-ffi`), the 3309-byte signature is PRODUCED by the extracted,
    /// full-dimension `MlDsaSignReal.signCore` (the brick-8 SIGN analog) over the actual `sk ‖ msg ‖ ctx`
    /// bytes — running as leanc-native code, PROVED to reproduce a genuine crate DETERMINISTIC signature
    /// byte-for-byte. On that path the `fips204` crate is NO LONGER trusted to sign: it is not consulted at
    /// all. The signer becomes DETERMINISTIC (`rnd = 0`, the FIPS 204 deterministic variant — spec-valid).
    ///
    /// When NO verified core is installed (a caller that has not wired the Lean archive), this falls back to
    /// the hedged `fips204` crate primitive. `dregg-pq` is a light leaf that cannot itself link the 195 MB
    /// Lean archive, so the routing is an install-time seam; a deployed, verified node installs the real core
    /// at startup and thereby leaves the crate out of the sign TCB.
    pub fn try_sign(&self, ctx: &[u8], message: &[u8]) -> Option<Vec<u8>> {
        // AUTHORITY: the Lean-verified real sign core over the real bytes, when installed. The `fips204`
        // crate is not consulted on this path — it has left the sign TCB.
        if let Some(core) = LEAN_SIGN_CORE_REAL.get() {
            let sk_bytes = self.secret.clone().into_bytes();
            let wire = real_sign_wire(&sk_bytes, message, ctx);
            // A `None` (FFI/archive fault), a `"ERR"` reply, or a wrong-length decode fails CLOSED (`None`),
            // which then rejects at verification — never a partial/spurious signature.
            let sig = decode_hex(core(&wire).as_deref()?)?;
            return (sig.len() == ml_dsa_65::SIG_LEN).then_some(sig);
        }

        // FALLBACK (no verified core installed): the hedged `fips204` crate primitive.
        // Refuses (aborts) unless DREGG_ALLOW_UNAUDITED_PQ=1 — see `crate::audit`.
        crate::audit::guard_unaudited_fallback(
            PqSite::MlDsaSign,
            "ML-DSA-65 sign",
            "fips204 0.4",
            "install_verified_mldsa_sign_core_real",
        );
        self.secret.try_sign(message, ctx).ok().map(|s| s.to_vec())
    }

    /// Sign with the FIPS 204 deterministic variant (`rnd = {0}^32`).
    ///
    /// This is required when the signature bytes themselves are part of a
    /// canonical object hash: a hedged signature is valid but would give the
    /// same logical object a different identity on every signing.  The
    /// installed Lean real core is already deterministic.  The guarded crate
    /// fallback uses `try_sign_with_seed` with the all-zero FIPS randomness,
    /// rather than silently falling back to the hedged [`MlDsaKey::try_sign`].
    pub fn try_sign_deterministic(&self, ctx: &[u8], message: &[u8]) -> Option<Vec<u8>> {
        if let Some(core) = LEAN_SIGN_CORE_REAL.get() {
            let sk_bytes = self.secret.clone().into_bytes();
            let wire = real_sign_wire(&sk_bytes, message, ctx);
            let sig = decode_hex(core(&wire).as_deref()?)?;
            return (sig.len() == ml_dsa_65::SIG_LEN).then_some(sig);
        }

        crate::audit::guard_unaudited_fallback(
            PqSite::MlDsaSign,
            "ML-DSA-65 deterministic sign",
            "fips204 0.4",
            "install_verified_mldsa_sign_core_real",
        );
        self.secret
            .try_sign_with_seed(&[0u8; 32], message, ctx)
            .ok()
            .map(|signature| signature.to_vec())
    }
}

/// The ML-DSA-65 public key of the signer holding `seed`, derived
/// deterministically (`ML-DSA.KeyGen(ξ = seed)`). Convenience for enrollment
/// flows that never keep the signing key.
pub fn ml_dsa_public_from_seed(seed: &[u8; 32]) -> Vec<u8> {
    MlDsaKey::from_ed25519_seed(seed).public_bytes()
}

/// Sign `message` under `ctx` with the ML-DSA-65 key derived from `seed`.
/// `None` only on the vanishingly rare internal RNG failure. Convenience for
/// surfaces that sign straight from a seed without keeping a key struct.
pub fn ml_dsa_sign_from_seed(seed: &[u8; 32], ctx: &[u8], message: &[u8]) -> Option<Vec<u8>> {
    MlDsaKey::from_ed25519_seed(seed).try_sign(ctx, message)
}

/// Why [`ml_dsa_verify`]'s accept/reject REFUSED rather than answering. Distinct from a
/// cryptographic reject on purpose: mirroring twin#1's `ConservationGateUnavailable`,
/// twin#8b's `FinalityGateUnavailable` and twin#3b's `CoordDecisionGateUnavailable`, a
/// VERIFIER's missing or broken archive is not a SIGNER's fault. No signature is invalid in
/// either variant — the verified core could not answer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MlDsaVerifyRefusal {
    /// A Lean-verified REAL verify core IS installed and it produced no usable verdict (a
    /// `None` from the FFI, an `"ERR"`/garbled reply). The signature is REJECTED and the
    /// `fips204` crate is NOT consulted: routing to the crate here would silently re-admit
    /// exactly the authority the install removed. NOT bypassable — an archive that faults is
    /// an integrity failure, not a policy choice.
    VerifiedCoreFaulted,
    /// NO verified core is installed in this process AND the bypass is not declared —
    /// `DREGG_ALLOW_UNAUDITED_PQ` is unset, or `DREGG_REQUIRE_LEAN=1` revoked it. The process
    /// ABORTS rather than let the unaudited `fips204` crate decide accept/reject.
    NoVerifiedCoreAndBypassNotDeclared,
}

impl std::fmt::Display for MlDsaVerifyRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::VerifiedCoreFaulted => write!(
                f,
                "VerifiedCoreFaulted: the Lean-verified ML-DSA-65 verify core \
                 (dregg_fips204_verify_real = MlDsaVerifyReal.verifyCore) IS installed and \
                 produced no usable verdict — the signature is REJECTED and the unaudited \
                 fips204 crate is NOT consulted (this is a BROKEN ARCHIVE, not a verdict about \
                 any signature)"
            ),
            Self::NoVerifiedCoreAndBypassNotDeclared => write!(
                f,
                "NoVerifiedCoreAndBypassNotDeclared: no Lean-verified ML-DSA-65 verify core is \
                 installed in this process and the declared unaudited bypass does not hold \
                 (DREGG_ALLOW_UNAUDITED_PQ unset, or DREGG_REQUIRE_LEAN=1 revoked it) — the \
                 process REFUSES to let the unaudited fips204 crate decide accept/reject"
            ),
        }
    }
}

/// FAIL-CLOSED CLASS (twin#13): whether [`ml_dsa_verify`] may take its ACCEPT/REJECT verdict
/// from the unaudited `fips204` crate. A thin, named alias of the shared
/// `audit::unaudited_pq_bypass_allowed` so this site's bypass has a name of its own in
/// `gate-dataflow.tsv` — the shape `belt_gate_bypass_allowed` / `coord_gate_bypass_allowed`
/// already use.
///
/// ONE DECLARED BYPASS: no verified core is installed in this binary AT ALL (`dregg-pq` is a
/// light leaf — an archive-less build, the wasm/zkVM guest, a host that cannot link the
/// 156 MB archive) **and** the operator accepted the unaudited primitive
/// (`DREGG_ALLOW_UNAUDITED_PQ=1`). `require_lean` (`DREGG_REQUIRE_LEAN=1`) REVOKES it — that
/// variable previously had NO EFFECT ON THIS PATH AT ALL.
///
/// ⚑ ONE BOOLEAN EXPRESSION, AND IT CALLS NOTHING WHOSE BODY HOLDS A REFUSAL TOKEN. See
/// `audit::unaudited_pq_bypass_allowed`'s header: a bare `return false` — or an inlined
/// helper containing a bare `false` — reads to `gate-dataflow.py` as A REFUSAL and blinds the
/// checker to the caller's real refusal arm. MEASURED at the finality site (`1736835f69`).
/// Both booleans are computed by the CALLER (in `audit.rs`, a different file, so the checker
/// cannot inline them) and passed in.
fn mldsa_verify_bypass_allowed(
    verified_core_installed: bool,
    unaudited_accepted_by_operator: bool,
    require_lean: bool,
) -> bool {
    !require_lean && !verified_core_installed && unaudited_accepted_by_operator
}

/// THE FAIL-CLOSED DISPOSITION for the Lean-verified ML-DSA-65 verify core — the
/// ACCEPT/REJECT gate behind ~10 surfaces (token/revocation, lightclient, cell-crypto, wire,
/// turn/authorize, captp, blocklace/pq). Called by [`ml_dsa_verify`] on every verification
/// whose length gate passed. Registered as twin#13 in
/// `scripts/ci-invariants/gate-dataflow.tsv`.
///
/// `Ok(())` ⇒ the caller may answer: either the verified core produced the verdict, or a
/// DECLARED bypass permits the `fips204` crate to. `Err(..)` ⇒ REFUSE, and which refusal it
/// is decides the shape (see [`MlDsaVerifyRefusal`]): a faulted core REJECTS the signature,
/// an undeclared bypass ABORTS the process.
///
/// ## Why the row is on THIS function and not on `ml_dsa_verify`
///
/// MEASURED, not assumed. A `gate-dataflow.tsv` row pointing at `ml_dsa_verify` itself with
/// `acquire = LEAN_VERIFY_CORE_REAL` printed **PASS — "gate-absent path REFUSES immediately
/// (`return false`)"** against the pre-fix code that fell straight through to the crate. The
/// `return false` it found is the MALFORMED-LENGTH `let Ok(..) = .. else` guard further down
/// the same region; strip that one line and the same row goes RED. So registering the site
/// directly would have been DECORATION — a refusal about a wrong-length key standing in for a
/// disposition about a missing verified core. The disposition is its own function so the
/// checker slices the decision and nothing else.
///
/// ## The vacuity short-circuit, and why it is REQUIRED
///
/// A refusal that fires where it means nothing is not a gate. `ml_dsa_verify`'s
/// wrong-length-key / wrong-length-signature check runs BEFORE this disposition is consulted
/// (it is the first statement of the function), and that ordering is load-bearing twice over.
/// A malformed PQ half has NO cryptographic verdict for a missing core to have made — the
/// answer is `false` on every backend — so refusing there would be the same over-refusal the
/// conservation fix hit on a `set_state` with no value delta and twin#8b hit on a
/// heartbeat-only poll. And because the undeclared-bypass refusal is an UNCATCHABLE ABORT, a
/// gate placed ahead of the length check would hand any peer a REMOTE KILL: one truncated
/// signature on a node with no verified core installed would take the process down.
fn mldsa_verify_disposition(
    verified_verdict: Option<bool>,
    verified_core_installed: bool,
    unaudited_accepted_by_operator: bool,
    require_lean: bool,
) -> Result<(), MlDsaVerifyRefusal> {
    let Some(_accept_or_reject) = verified_verdict else {
        if mldsa_verify_bypass_allowed(
            verified_core_installed,
            unaudited_accepted_by_operator,
            require_lean,
        ) {
            return Ok(());
        }
        return Err(if verified_core_installed {
            MlDsaVerifyRefusal::VerifiedCoreFaulted
        } else {
            MlDsaVerifyRefusal::NoVerifiedCoreAndBypassNotDeclared
        });
    };
    Ok(())
}

/// Verify an ML-DSA-65 signature over `message` under the caller-supplied FIPS
/// 204 `ctx`.
///
/// Returns `false` — never a panic — on a wrong-length public key, a
/// wrong-length signature, an undecodable key, or a failed cryptographic check.
/// This is the fail-CLOSED primitive: a present-but-invalid (or malformed) PQ
/// half must make the whole hybrid verification reject.
///
/// # The security-critical bool comes from the Lean-verified core, not the crate
///
/// When a Lean-verified REAL verify core is installed ([`install_lean_verify_core_real`], done by any
/// process that can link `dregg-lean-ffi`), the ACCEPT/REJECT verdict is computed by the extracted,
/// full-dimension `MlDsaVerifyReal.verifyCore` (BRICK 8) over the actual `pk ‖ msg ‖ ctx ‖ sig` bytes —
/// running as leanc-native code, PROVED to accept a genuine crate signature and reject tampers. On that
/// path the `fips204` crate is NO LONGER trusted for verify: it is not consulted at all.
///
/// When NO verified core is installed (a caller that has not wired the Lean archive), this falls back to
/// the `fips204` crate primitive. `dregg-pq` is a light leaf shared by 9 crates and cannot itself link the
/// 195 MB Lean archive, so the routing is an install-time seam rather than a direct call; a deployed,
/// verified node installs the real core at startup and thereby leaves the crate out of the verify TCB.
///
/// # ⚑ THE FALLBACK IS A DECLARED BYPASS, NOT A FALLTHROUGH
///
/// The disposition is the named, registered [`mldsa_verify_disposition`] (twin#13 in
/// `scripts/ci-invariants/gate-dataflow.tsv`), and it is consulted on EVERY verification whose length
/// gate passed. There are exactly three outcomes and each is legible in
/// `audit::pq_provenance()`'s per-site counters:
///
///   * the verified core answered ⇒ its verdict, counted as `verified`;
///   * no core installed AND the DECLARED bypass holds (`DREGG_ALLOW_UNAUDITED_PQ=1`, not revoked by
///     `DREGG_REQUIRE_LEAN=1`) ⇒ the `fips204` crate answers, counted as `unaudited` and warned once
///     for THIS site by name — so "which implementation answered a given verification" is a question
///     with an answer, rather than one boot line nobody reads;
///   * otherwise ⇒ REFUSE. A faulted-but-installed core REJECTS; an undeclared bypass ABORTS.
pub fn ml_dsa_verify(public_bytes: &[u8], ctx: &[u8], message: &[u8], sig_bytes: &[u8]) -> bool {
    // ⚑ THE VACUITY SHORT-CIRCUIT, AND IT MUST STAY AHEAD OF THE GATE. A wrong-length key or
    // signature has NO cryptographic verdict on ANY backend, so there is nothing for a missing
    // verified core to have decided — refusing here would be the over-refusal the conservation fix
    // hit on a value-free `set_state`. It is also a DoS boundary: the undeclared-bypass refusal below
    // is an UNCATCHABLE ABORT, so a gate placed ahead of this check would let any peer kill the
    // process with one truncated signature.
    if public_bytes.len() != ml_dsa_65::PK_LEN || sig_bytes.len() != ml_dsa_65::SIG_LEN {
        return false;
    }

    // AUTHORITY: the Lean-verified real verify core over the real bytes, when installed. The `fips204`
    // crate is not consulted on this path — it has left the verify TCB. `None` distinguishes A CORE
    // THAT COULD NOT ANSWER (FFI/archive fault, `"ERR"`) from a core that answered REJECT — the old
    // `matches!(.., Some("1"))` collapsed both to `false`, which is the right VERDICT but leaves an
    // operator unable to tell a broken archive from a stream of bad signatures.
    let installed_core = LEAN_VERIFY_CORE_REAL.get();
    let verified_verdict = installed_core.and_then(|core| {
        let wire = real_verify_wire(public_bytes, message, ctx, sig_bytes);
        core(&wire).map(|reply| reply == "1")
    });

    if let Err(refusal) = mldsa_verify_disposition(
        verified_verdict,
        installed_core.is_some(),
        crate::audit::unaudited_pq_accepted(),
        crate::audit::require_verified_lean_gate(),
    ) {
        match refusal {
            // The archive is BROKEN, not the signature. Reject (never consult the crate — that would
            // re-admit exactly the authority the install removed) and make the fault countable so a
            // node whose every verify suddenly fails is diagnosable as an archive fault.
            // (`note_verified_core_fault` counts it and explains itself ONCE per site — a broken
            // archive faults on every call, so an unlatched line would be one stderr write per
            // verification.)
            MlDsaVerifyRefusal::VerifiedCoreFaulted => {
                crate::audit::note_verified_core_fault(PqSite::MlDsaVerify);
                return false;
            }
            // No verified core and no declared bypass: the unaudited crate must NOT decide a
            // security accept/reject. Uncatchable abort, naming the install that fixes it.
            MlDsaVerifyRefusal::NoVerifiedCoreAndBypassNotDeclared => {
                crate::audit::refuse_unaudited(
                    "ML-DSA-65 verify",
                    "fips204 0.4",
                    "install_verified_mldsa_verify_core",
                )
            }
        }
    }

    if let Some(accept) = verified_verdict {
        crate::audit::note_verified_answer(PqSite::MlDsaVerify);
        return accept;
    }

    // THE DECLARED BYPASS (no verified core in this process + the operator accepted the unaudited
    // primitive): the `fips204` crate answers, and the provenance says so per-site.
    crate::audit::note_unaudited_answer(
        PqSite::MlDsaVerify,
        "ML-DSA-65 verify",
        "fips204 0.4",
        "install_verified_mldsa_verify_core",
    );
    let Ok(pk_arr) = <[u8; ml_dsa_65::PK_LEN]>::try_from(public_bytes) else {
        return false;
    };
    let Ok(sig) = <[u8; ml_dsa_65::SIG_LEN]>::try_from(sig_bytes) else {
        return false;
    };
    let Ok(vk) = ml_dsa_65::PublicKey::try_from_bytes(pk_arr) else {
        return false;
    };
    vk.verify(message, &sig, ctx)
}

#[cfg(test)]
mod tests {
    use super::*;

    const CTX: &[u8] = b"dregg-pq-unit-test-ctx-v1";

    /// ⚑ POLE A (the DISPOSITION, exhaustively): the Lean-verified ML-DSA-65 verify core cannot
    /// answer, so the ACCEPT/REJECT gate REFUSES rather than handing the verdict to the unaudited
    /// `fips204` crate. twin#13 — the fifth member of the fail-OPEN class, and the first whose
    /// fallback is a real third-party crate rather than a hand-written Rust twin.
    ///
    /// The test asserts THE NEGATIVE the way conservation's, twin#8b's and twin#3b's Pole A do: an
    /// `Ok(())` in a no-bypass quadrant PANICS with a FAIL-OPEN message, because `Ok(())` there means
    /// the site went on to take a SECURITY ACCEPT/REJECT from a primitive nobody audited.
    ///
    /// It also pins the DECLARED bypass, that `DREGG_REQUIRE_LEAN=1` revokes it (that variable
    /// previously had NO EFFECT ON THIS PATH AT ALL), and the bypass predicate's own quadrants —
    /// invariant 6 checks that the region REACHES a refusal past the declared discriminator and does
    /// NOT evaluate the discriminator, so a mutation of `mldsa_verify_bypass_allowed` to a bare `true`
    /// stays GREEN there and must redden HERE.
    #[test]
    fn ml_dsa_verify_fails_closed_when_the_verified_core_cannot_answer() {
        // ── THE HOLE, CLOSED (a). No verified core installed, and the operator did NOT accept the
        //    unaudited primitive ⇒ REFUSE (the site aborts rather than let `fips204` decide).
        match mldsa_verify_disposition(None, false, false, false) {
            Err(MlDsaVerifyRefusal::NoVerifiedCoreAndBypassNotDeclared) => { /* fail-closed */ }
            other => panic!(
                "FAIL-OPEN: no Lean-verified ML-DSA-65 verify core is installed and the operator has \
                 NOT set DREGG_ALLOW_UNAUDITED_PQ=1, yet the disposition returned {other:?} instead of \
                 refusing. Permitting the site here means a SECURITY ACCEPT/REJECT — the verdict behind \
                 token/revocation, the lightclient, cell-crypto, the wire, turn/authorize, captp and \
                 blocklace/pq — is taken from the unaudited `fips204` crate."
            ),
        }

        // ── THE HOLE, CLOSED (b): the core IS installed and FAULTED (a `None`/`\"ERR\"` out of the
        //    FFI). NOT bypassable at all — routing to the crate here would silently re-admit exactly
        //    the authority the install removed. Every combination of the two escapes must still refuse.
        for (accepted, require_lean) in [(false, false), (true, false), (false, true), (true, true)]
        {
            match mldsa_verify_disposition(None, true, accepted, require_lean) {
                Err(MlDsaVerifyRefusal::VerifiedCoreFaulted) => { /* fail-closed */ }
                other => panic!(
                    "FAIL-OPEN: a verified verify core IS installed and produced NO usable verdict, and \
                     the disposition returned {other:?} (accepted={accepted}, \
                     require_lean={require_lean}). A FAULTING archive must REJECT, never fall back to \
                     the unaudited crate — that is the one state with no opt-out."
                ),
            }
        }

        // ── THE CORE ANSWERED: there is no missing gate to dispose of, whichever way it answered.
        //    Both verdicts, so the disposition cannot be a disguised "reject everything".
        for verdict in [true, false] {
            assert!(
                mldsa_verify_disposition(Some(verdict), true, false, false).is_ok(),
                "an ANSWERING verified core must never be refused — {verdict} is the verified \
                 object's own accept/reject, not a missing gate"
            );
        }

        // ── THE DECLARED BYPASS: no core installed in this binary at all (an archive-less build /
        //    the guest / every `dregg-pq` unit-test binary) AND the operator accepted it.
        assert!(
            mldsa_verify_disposition(None, false, true, false).is_ok(),
            "with NO verified core linked and DREGG_ALLOW_UNAUDITED_PQ=1 this is the DECLARED bypass \
             (gate-dataflow.tsv twin#13), not a silent fall-open — a blanket refusal would brick every \
             wasm / zkVM / archive-less build"
        );

        // ── `DREGG_REQUIRE_LEAN=1` REVOKES IT. Before this existed the variable had NO EFFECT on any
        //    PQ path: an operator could demand the verified artifact and still get `fips204`.
        assert!(
            mldsa_verify_disposition(None, false, true, true).is_err(),
            "DREGG_REQUIRE_LEAN=1 must REVOKE the unaudited bypass — two switches with contradictory \
             meanings must not resolve in favour of the permissive one"
        );

        // The bypass predicate's own quadrants, so a future widening is a visible diff and not a quiet
        // boolean flip. Invariant 6 CANNOT see this (it does not evaluate the discriminator) — these
        // lines are the complement that catches a `mldsa_verify_bypass_allowed -> true` mutant.
        assert!(
            mldsa_verify_bypass_allowed(false, true, false),
            "the one declared bypass"
        );
        assert!(
            !mldsa_verify_bypass_allowed(false, false, false),
            "no opt-in ⇒ no bypass (the DEFAULT is the safe one)"
        );
        assert!(
            !mldsa_verify_bypass_allowed(true, true, false),
            "a core IS installed ⇒ never a bypass, whatever the operator set"
        );
        assert!(
            !mldsa_verify_bypass_allowed(false, true, true),
            "DREGG_REQUIRE_LEAN=1 revokes"
        );
    }

    /// ⚑ POLE A AT THE SITE, plus its NON-OVER-FIRE companion: the ONLY thing that changes between
    /// the two halves is whether the installed verified core can answer.
    ///
    /// The armed-and-unanswerable state is not producible from outside — with no core installed the
    /// miss is a DECLARED bypass, and with a real archive `shadow_fips204_verify_real` answers — so it
    /// is driven here by installing a core that returns `None`. `LEAN_VERIFY_CORE_REAL` is a
    /// process-wide `OnceLock`, and `dregg-pq`'s unit tests run concurrently in ONE process, so this
    /// test must NOT install into it (that would silently retarget `sign_then_verify_roundtrips` and
    /// friends). It therefore drives the disposition + the length short-circuit, and the SITE with a
    /// real installed core is `tests/mldsa_lean_verify.rs` (archive-present) and
    /// `tests/unaudited_refusal.rs` (subprocess, archive-absent, both env poles).
    ///
    /// What it DOES pin at the site is the VACUITY SHORT-CIRCUIT, which is load-bearing twice: a
    /// malformed PQ half has no verdict on any backend, and because the undeclared-bypass refusal is
    /// an UNCATCHABLE ABORT, a gate ahead of the length check would hand any peer a remote kill.
    #[test]
    fn ml_dsa_verify_length_gate_short_circuits_ahead_of_the_pq_gate() {
        // A wrong-length key / signature is refused WITHOUT the disposition being consulted at all.
        // If this ever regressed, this very test would ABORT the test process (no core is installed
        // in a `dregg-pq` unit binary), which is the loudest possible failure signal.
        assert!(
            !ml_dsa_verify(&[], CTX, b"msg", &[0u8; ML_DSA_SIG_LEN]),
            "a wrong-length public key rejects on every backend — the length gate, not the PQ gate"
        );
        assert!(
            !ml_dsa_verify(&[0u8; ML_DSA_PK_LEN], CTX, b"msg", &[]),
            "a wrong-length signature rejects on every backend"
        );
        assert!(
            !ml_dsa_verify(&[0u8; 7], CTX, b"msg", &[0u8; 11]),
            "both wrong ⇒ reject, and no gate consulted"
        );

        // And the short-circuit is NOT vacuous: at CORRECT lengths the call does reach a backend.
        // (In this binary that is the declared bypass — the `#[cfg(test)]` override stands in for the
        // operator opt-in — so this line also witnesses that the bypass is live rather than the
        // refusal firing on everything.)
        let key = MlDsaKey::from_ed25519_seed(&[11u8; 32]);
        let msg = b"the length gate must not swallow a well-formed verification";
        let sig = key.sign(CTX, msg);
        assert!(
            ml_dsa_verify(&key.public_bytes(), CTX, msg, &sig),
            "a WELL-FORMED verification must still reach a backend and accept — otherwise the three \
             rejections above are satisfied by a function that rejects everything"
        );
        assert!(
            crate::audit::any_unaudited_pq_answer(),
            "and the PROVENANCE must record that it was the unaudited crate that answered it — a \
             per-site count is the whole point of the legibility half of twin#13"
        );
    }

    #[test]
    fn from_seed_is_deterministic() {
        let seed = [7u8; 32];
        let a = MlDsaKey::from_ed25519_seed(&seed);
        let b = MlDsaKey::from_ed25519_seed(&seed);
        assert_eq!(a.public_bytes(), b.public_bytes());
        assert_eq!(a.public_bytes().len(), ML_DSA_PK_LEN);
        // The free helper agrees with the key-struct derivation.
        assert_eq!(ml_dsa_public_from_seed(&seed), a.public_bytes());
        // A different seed yields a different key.
        let c = MlDsaKey::from_ed25519_seed(&[8u8; 32]);
        assert_ne!(a.public_bytes(), c.public_bytes());
    }

    #[test]
    fn sign_then_verify_roundtrips() {
        let key = MlDsaKey::from_ed25519_seed(&[3u8; 32]);
        let msg = b"the same canonical signing message both halves cover";
        let sig = key.sign(CTX, msg);
        assert!(ml_dsa_verify(&key.public_bytes(), CTX, msg, &sig));
        // The from-seed sign helper produces an equally valid signature.
        let sig2 = ml_dsa_sign_from_seed(&[3u8; 32], CTX, msg).expect("sign");
        assert!(ml_dsa_verify(&key.public_bytes(), CTX, msg, &sig2));
    }

    #[test]
    fn ctx_separates_domains() {
        // A signature minted under one ctx must not verify under another —
        // domain separation is load-bearing and rides the caller's ctx.
        let key = MlDsaKey::from_ed25519_seed(&[5u8; 32]);
        let msg = b"canonical message";
        let sig = key.sign(b"surface-A-v1", msg);
        assert!(ml_dsa_verify(
            &key.public_bytes(),
            b"surface-A-v1",
            msg,
            &sig
        ));
        assert!(!ml_dsa_verify(
            &key.public_bytes(),
            b"surface-B-v1",
            msg,
            &sig
        ));
    }

    #[test]
    fn forged_and_malformed_rejected_fail_closed() {
        let key = MlDsaKey::from_ed25519_seed(&[3u8; 32]);
        let msg = b"canonical message";
        let mut sig = key.sign(CTX, msg);
        // Flip one byte: a present-but-invalid PQ half must fail closed.
        sig[0] ^= 0xff;
        assert!(!ml_dsa_verify(&key.public_bytes(), CTX, msg, &sig));

        // A signature by an attacker's OWN key over the SAME message, verified
        // against the honest holder's enrolled public key, must REJECT.
        let attacker = MlDsaKey::from_ed25519_seed(&[99u8; 32]);
        let forged = attacker.sign(CTX, msg);
        assert!(!ml_dsa_verify(&key.public_bytes(), CTX, msg, &forged));
        // (the forged signature IS valid under the attacker's own key — proving
        //  the rejection is the pin, not a broken signature)
        assert!(ml_dsa_verify(&attacker.public_bytes(), CTX, msg, &forged));

        // Wrong message under a valid signature rejects.
        let good = key.sign(CTX, msg);
        assert!(!ml_dsa_verify(
            &key.public_bytes(),
            CTX,
            b"different message",
            &good
        ));
        // Empty / malformed inputs reject rather than panic.
        assert!(!ml_dsa_verify(&[], CTX, msg, &good));
        assert!(!ml_dsa_verify(&key.public_bytes(), CTX, msg, &[]));
    }

    /// The routing seam sends the security-critical verify through the extracted, Lean-verified core.
    /// Here the installed core stands in for `dregg-lean-ffi::shadow_fips204_verify` (which drives the
    /// leanc-native SCALAR `Fips204Verify.verifyCore` — `realParams.verifyB` at `n = 1` over `ℤ`,
    /// NOT the full-byte `MlDsaVerifyReal.verifyCore`, as the `(thi=3, μ=7, ...)` data below shows;
    /// its round-trip is green in dregg-lean-ffi's
    /// `verified_ml_dsa_verify_runs_in_lean`). It carries the SAME contract the Lean `verifyFFI` proves:
    /// the honest deployed-parameter statement `(thi=3, μ=7, c̃=7, z=45, h=0)` ACCEPTS; a tampered `c̃`
    /// or out-of-range `z` REJECTS. This test exercises that the seam routes `ml_dsa_verify_core`
    /// through the installed verified object and honors its accept/reject verdict.
    #[test]
    fn verify_routes_through_lean_core() {
        // No core installed ⇒ the seam declines and the caller falls back.
        assert_eq!(ml_dsa_verify_core("3 7 7 45 0"), None);
        // Install a core carrying the extracted `verifyCore`'s proven contract (the `#guard` teeth).
        let installed = install_lean_verify_core(|wire| {
            Some(
                match wire {
                    // honest round-trip (realParams.sign 5 1 3 7 40 = (7,45,0)) ⇒ accept
                    "3 7 7 45 0" => "1",
                    // tampered c̃ ⇒ reject; out-of-range z ⇒ reject; malformed ⇒ reject
                    "3 7 8 45 0" | "3 7 7 100000000 0" => "0",
                    _ => "0",
                }
                .to_string(),
            )
        });
        assert!(installed, "first install succeeds");
        assert!(
            !install_lean_verify_core(|_| None),
            "install is once-per-process"
        );
        // The security-critical verdicts route through the installed verified core.
        assert_eq!(
            ml_dsa_verify_core("3 7 7 45 0"),
            Some(true),
            "honest ACCEPTS"
        );
        assert_eq!(
            ml_dsa_verify_core("3 7 8 45 0"),
            Some(false),
            "tampered c̃ REJECTS"
        );
        assert_eq!(
            ml_dsa_verify_core("3 7 7 100000000 0"),
            Some(false),
            "out-of-range z REJECTS"
        );

        // ── THE SIGN → VERIFY ROUND-TRIP through the extracted cores (Unit 3a) ──
        // The sign core is a SEPARATE once-per-process seam (its own OnceLock). It stands in for
        // `dregg-lean-ffi::shadow_fips204_sign` (the leanc-native `signCore`; round-trip green in
        // dregg-lean-ffi's `verified_ml_dsa_sign_verify_roundtrips_in_lean`). It carries the SAME
        // contract the Lean `signFFI` proves: the honest secret `(s₁,s₂,t₀)=(5,1,3)` with mask `y=40`
        // and message `μ=7` SIGNS to `(c̃,z,h) = (7,45,0)`; a mask whose commitment low part fails the
        // `lowGap` gate (`y=261888`) or whose response is out of norm (`y=1000000`) is honestly
        // REJECTED (retry), not faked; a malformed wire fails closed.
        assert_eq!(
            ml_dsa_sign_core("5 1 3 7 40"),
            None,
            "no sign core ⇒ caller falls back"
        );
        let sign_installed = install_lean_sign_core(|wire| {
            Some(
                match wire {
                    "5 1 3 7 40" => "7 45 0",
                    "5 1 3 7 261888" | "5 1 3 7 1000000" => "REJECT",
                    _ => "REJECT",
                }
                .to_string(),
            )
        });
        assert!(sign_installed, "first sign install succeeds");
        assert!(
            !install_lean_sign_core(|_| None),
            "sign install is once-per-process"
        );

        // The honest sign produces the accepted signature wire.
        let sig = ml_dsa_sign_core("5 1 3 7 40")
            .expect("sign core installed")
            .expect("accepted iteration");
        assert_eq!(sig, "7 45 0", "honest sign emits the signature wire");

        // ROUND-TRIP: the accepted signature, prefixed with `thi μ` (derived public key thi = 5+1−3 =
        // 3, message μ = 7), VERIFIES through the SAME extracted verify core installed above.
        assert_eq!(
            ml_dsa_verify_core(&format!("3 7 {sig}")),
            Some(true),
            "the extracted sign output round-trips through the verify core"
        );

        // A REJECTED sample is honestly `Some(None)` — the caller resamples; it is NOT a faked accept.
        assert_eq!(
            ml_dsa_sign_core("5 1 3 7 261888"),
            Some(None),
            "a bad-mask sample (lowGap fails) is honestly rejected (retry)"
        );
        assert_eq!(
            ml_dsa_sign_core("5 1 3 7 1000000"),
            Some(None),
            "an out-of-norm response is honestly rejected (retry)"
        );
        // A malformed sign wire fails closed (reject/retry, never a spurious signature).
        assert_eq!(
            ml_dsa_sign_core("garbage"),
            Some(None),
            "malformed sign wire fails closed"
        );
    }
}
