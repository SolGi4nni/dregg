//! A **hybrid** (classical + post-quantum) session key-exchange, so a recorded
//! session is not *harvest-now-decrypt-later* (HNDL) vulnerable: an adversary
//! who records the handshake today and acquires a quantum computer later still
//! cannot recover the session key.
//!
//! The classical transport seals each frame with X25519 ECDH → HKDF-SHA256 →
//! ChaCha20-Poly1305. That protects against a *classical* adversary but not a
//! future quantum one, because X25519 (a discrete-log problem) falls to Shor's
//! algorithm. This module adds the missing half: a session KEM whose derived
//! key depends on **both** an X25519 secret **and** an ML-KEM-768 (FIPS 203)
//! secret.
//!
//! ## The combiner (the load-bearing correctness point)
//!
//! We follow the published **X-Wing** / TLS **X25519MLKEM768** hybrid-KEM
//! construction: derive one classical secret `ss_x25519` and one post-quantum
//! secret `ss_mlkem`, then feed **both, concatenated, plus the full public
//! transcript** through a single KDF:
//!
//! ```text
//! session_key = HKDF-SHA256(
//!     salt = DOMAIN,
//!     ikm  = ss_x25519 ‖ ss_mlkem,
//!     info = DOMAIN ‖ transcript )
//! ```
//!
//! This is a **concatenation KDF, never XOR**: with XOR an adversary who learns
//! one secret could cancel it and forge agreement on the other; with a
//! collision-resistant KDF over the *concatenation* the output depends jointly
//! and inextricably on both. Consequently breaking X25519 alone (quantum) does
//! not recover the key — `ss_mlkem` still protects it — and breaking ML-KEM
//! alone does not either — `ss_x25519` protects it. That two-sided dependence is
//! exactly what the `hybrid_dependence_*` tests pin.
//!
//! The `transcript` binds the derived key to the exact public handshake material
//! (both X25519 public keys, the ML-KEM encapsulation key, and the ML-KEM
//! ciphertext), so an active attacker cannot substitute ephemeral material
//! without changing the key — the same transcript binding X-Wing performs over
//! `ct_X ‖ pk_X`.
//!
//! ## Shape
//!
//! One round trip. The **responder** publishes a [`HybridOffer`] (its X25519
//! ephemeral public key + its ML-KEM encapsulation key) and keeps the matching
//! [`HybridResponder`] secrets. The **initiator** consumes the offer with
//! [`initiate`], producing a [`HybridInitiatorMessage`] (its X25519 ephemeral
//! public key + the ML-KEM ciphertext) and *its* copy of the session key. The
//! responder feeds that message to [`HybridResponder::finish`] to derive the
//! *same* session key. Confidentiality only: this is a KEM, there is no enroll /
//! pin / signature here (peer authentication rides the existing identity/handoff
//! layer).
//!
//! ## `kem` traits
//!
//! ml-kem 0.2.3 re-exports the `Encapsulate`/`Decapsulate` traits its encaps /
//! decaps are built on via its own `ml_kem::kem` module, so this module imports
//! them from `ml_kem::kem` and never names the pinned pre-release `kem` crate.

use hkdf::Hkdf;
use ml_kem::kem::{Decapsulate, Encapsulate};
use ml_kem::{Ciphertext, Encoded, EncodedSizeUser, KemCore, MlKem768};
use rand_core::RngCore;
use sha2::Sha256;
use std::sync::OnceLock;
use x25519_dalek::{PublicKey, StaticSecret};
use zeroize::Zeroize;

/// A pluggable, Lean-VERIFIED ML-KEM (FIPS 203) encaps/decaps backend, installed by an integration layer
/// — the KEM mirror of the ML-DSA verify/sign cores in [`crate::mldsa`].
///
/// The extracted cores live in `metatheory/Dregg2/Crypto/Fips203Kem.lean` (`encapsCore` = `foEncaps` and
/// `decapsCore` = `foDecaps` at the deployed Kyber parameters — the re-encryption check + implicit
/// reject), `@[export]`ed as `dregg_fips203_encaps` / `dregg_fips203_decaps` and compiled to leanc-native
/// code. They are PROVED to agree with the `MlKemIndCca` spec (`encapsCore_eq_spec` / `decapsCore_eq_spec`)
/// and to discharge `DreggKemRefinement.Fips203Correct` — the encaps→decaps round-trip — with NO `ml-kem`
/// crate hypothesis (`extractedKemApi_fips203`). `dregg-lean-ffi::shadow_fips203_{encaps,decaps}` run them.
///
/// dregg-pq stays a LIGHT leaf: it takes function pointers, never a dependency on the Lean archive — the
/// same discipline as the ML-DSA cores. An integration layer installs the native cores via
/// [`install_lean_encaps_core`] / [`install_lean_decaps_core`]; [`ml_kem_encaps_core`] /
/// [`ml_kem_decaps_core`] then route the deployed-parameter ML-KEM through the Lean-verified objects.
type LeanKemCore = fn(wire: &str) -> Option<String>;
static LEAN_ENCAPS_CORE: OnceLock<LeanKemCore> = OnceLock::new();
static LEAN_DECAPS_CORE: OnceLock<LeanKemCore> = OnceLock::new();

/// Install the extracted, Lean-verified ML-KEM encaps core (e.g.
/// `|w| dregg_lean_ffi::shadow_fips203_encaps(w).ok()`). Returns `false` if one is already installed
/// (once-per-process; the verified core is not hot-swappable).
pub fn install_lean_encaps_core(core: LeanKemCore) -> bool {
    LEAN_ENCAPS_CORE.set(core).is_ok()
}

/// Install the extracted, Lean-verified ML-KEM decaps core (e.g.
/// `|w| dregg_lean_ffi::shadow_fips203_decaps(w).ok()`). Returns `false` if one is already installed
/// (once-per-process; the verified core is not hot-swappable).
pub fn install_lean_decaps_core(core: LeanKemCore) -> bool {
    LEAN_DECAPS_CORE.set(core).is_ok()
}

/// Route a deployed-parameter ML-KEM encaps request `"A t m"` (the wire the extracted Lean `encapsFFI`
/// reads — public key `(A,t)`, message bit `m`) through the installed Lean-verified encaps core.
/// `Some("u v K")` = the ciphertext `(u,v)` + encapsulated secret `K`; `None` = no core installed (caller
/// falls back to the `ml-kem` primitive). This is the routing seam that sends the ML-KEM encaps through
/// the `Fips203Correct`-discharging Lean object; the full-byte-codec path over real 1184/1088-byte
/// keys/ciphertexts is the named engineering residual (`Fips203Kem.lean`).
pub fn ml_kem_encaps_core(wire: &str) -> Option<String> {
    let core = LEAN_ENCAPS_CORE.get()?;
    core(wire)
}

/// Route a deployed-parameter ML-KEM decaps request `"A t s z u v"` (the wire the extracted Lean
/// `decapsFFI` reads — encapsulation key `(A,t)`, secret `s`, implicit-reject seed `z`, ciphertext
/// `(u,v)`) through the installed Lean-verified decaps core. `Some(K)` = the recovered shared secret
/// (`H(m′)` on a matching re-encryption, else the implicit-reject secret `J(z‖c)` — ML-KEM decaps never
/// fails on a well-formed ciphertext); `None` = no core installed (caller falls back). This is the
/// SECURITY-CRITICAL direction routed through the Lean-verified object: a tampered ciphertext
/// implicit-rejects to a DIFFERENT secret, so the parties diverge without leaking.
pub fn ml_kem_decaps_core(wire: &str) -> Option<String> {
    let core = LEAN_DECAPS_CORE.get()?;
    core(wire)
}

/// A pluggable, Lean-VERIFIED **REAL, FULL-BYTE** ML-KEM-768 decaps backend (BRICK K6), installed by an
/// integration layer. Where [`LeanKemCore`] above carries the `A=1,n=1` SCALAR decaps over a 6-integer toy
/// wire, THIS core carries the FULL-DIMENSION ML-KEM-768 decapsulation over the actual `dk ‖ ct` bytes.
///
/// The extracted core is `Dregg2.Crypto.MlKemDecaps.mlkemDecapsRealFFI` over `mlkemDecaps` (the FO pipeline:
/// K-PKE decrypt, `G = SHA3-512` split, full re-encryption, byte-exact `c' = c` implicit-reject over the real
/// n=256 negacyclic ring / NTT / real 2400/1088-byte codec), `@[export]`ed as `dregg_mlkem_decaps_real` and
/// compiled to leanc-native code. It is PROVED (`native_decide`) to RECOVER a genuine `ml-kem` v0.2.3 crate
/// shared secret (`mlkemDecapsRealFFI_recovers_real_secret`) and to implicit-reject a one-byte tamper to a
/// DIFFERENT secret (`mlkemDecapsRealFFI_rejects_tampered`). `dregg-lean-ffi::shadow_mlkem_decaps_real` runs
/// it natively.
///
/// dregg-pq stays a LIGHT leaf (it never depends on the ~195 MB Lean archive): it takes a function pointer.
/// An integration layer that CAN link the archive installs the native core via
/// [`install_lean_kem_decaps_core_real`]; once installed, [`HybridResponder::finish`] takes the ML-KEM shared
/// secret from the Lean-verified object over the real bytes — the `ml-kem` crate is NO LONGER the decaps
/// authority (its `.decapsulate` is not called). The wire is `"hex(dk) hex(ct)"`; the reply is `hex(K)` (the
/// recovered 32-byte secret) / `"ERR"` (malformed → fail closed).
type LeanKemDecapsCoreReal = fn(wire: &str) -> Option<String>;
static LEAN_KEM_DECAPS_CORE_REAL: OnceLock<LeanKemDecapsCoreReal> = OnceLock::new();

/// Install the extracted, Lean-verified REAL, full-byte ML-KEM-768 decaps core (e.g.
/// `|w| dregg_lean_ffi::shadow_mlkem_decaps_real(w).ok()`). Once installed, [`HybridResponder::finish`] routes
/// the SECURITY-CRITICAL ML-KEM decaps through it — taking the `ml-kem` crate OUT of the decaps TCB. Returns
/// `false` if one is already installed (once-per-process; the verified core is not hot-swappable).
pub fn install_lean_kem_decaps_core_real(core: LeanKemDecapsCoreReal) -> bool {
    LEAN_KEM_DECAPS_CORE_REAL.set(core).is_ok()
}

/// Whether a Lean-verified REAL ML-KEM decaps core has been installed (so [`HybridResponder::finish`] takes
/// the ML-KEM shared secret from the Lean-verified object rather than the `ml-kem` crate's `.decapsulate`). A
/// deployed, verified node installs one at startup.
pub fn mlkem_decaps_real_core_installed() -> bool {
    LEAN_KEM_DECAPS_CORE_REAL.get().is_some()
}

/// Outcome of installing the Lean-verified REAL ML-KEM decaps core as [`HybridResponder::finish`]'s authority
/// (via [`install_verified_mlkem_decaps_core`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MlKemDecapsCoreInstall {
    /// The real core was installed by THIS call — the `ml-kem` crate is now out of the decaps TCB.
    Installed,
    /// A core was already installed this process (install is once-per-process) — crate still out of TCB.
    AlreadyInstalled,
    /// The linked Lean archive does not export the real decaps core; the `ml-kem`-crate fallback stays in
    /// place (a valid FIPS-203 decaps, but NOT the Lean-verified authority).
    ExportAbsent,
}

/// A pluggable, Lean-VERIFIED **REAL, FULL-BYTE** ML-KEM-768 ENCAPS backend (BRICK K5 — the ENCAPS mirror of
/// the K6 decaps core above), installed by an integration layer. It carries the full-dimension ML-KEM-768
/// deterministic FO encapsulation over the actual `ek ‖ m` bytes.
///
/// The extracted core is `Dregg2.Crypto.MlKemEncaps.mlkemEncapsRealFFI` over `mlkemEncaps` (the FIPS 203 Alg 16
/// FO encaps: `H(ek)` SHA3-256, `G(m ‖ H(ek))` SHA3-512 split, K-PKE.Encrypt over the real n=256 negacyclic
/// ring / NTT / real 1184/1088-byte codec), `@[export]`ed as `dregg_mlkem_encaps_real` and compiled to
/// leanc-native code. It is PROVED (`native_decide`) BYTE-EXACT vs the `ml-kem` v0.2.3 crate's
/// `EncapsulateDeterministic` (`encaps_matches_crate`) and to round-trip through the verified K4 decaps
/// (`encaps_decaps_roundtrip`). `dregg-lean-ffi::shadow_mlkem_encaps_real` runs it natively.
///
/// dregg-pq stays a LIGHT leaf (it never depends on the ~195 MB Lean archive): it takes a function pointer.
/// An integration layer that CAN link the archive installs the native core via
/// [`install_lean_kem_encaps_core_real`]; once installed, [`initiate`] produces the ML-KEM ciphertext + shared
/// secret from the Lean-verified object over the real bytes — the `ml-kem` crate is NO LONGER the encaps
/// authority (its `.encapsulate` is not called). The initiator supplies its own 32-byte `m` (as the crate does
/// internally). The wire is `"hex(ek) hex(m)"`; the reply is `"hex(ct) hex(K)"` / `"ERR"` (malformed → fail
/// closed).
type LeanKemEncapsCoreReal = fn(wire: &str) -> Option<String>;
static LEAN_KEM_ENCAPS_CORE_REAL: OnceLock<LeanKemEncapsCoreReal> = OnceLock::new();

/// Install the extracted, Lean-verified REAL, full-byte ML-KEM-768 encaps core (e.g.
/// `|w| dregg_lean_ffi::shadow_mlkem_encaps_real(w).ok()`). Once installed, [`initiate`] routes the ML-KEM
/// encaps through it — taking the `ml-kem` crate OUT of the encaps TCB. Returns `false` if one is already
/// installed (once-per-process; the verified core is not hot-swappable).
pub fn install_lean_kem_encaps_core_real(core: LeanKemEncapsCoreReal) -> bool {
    LEAN_KEM_ENCAPS_CORE_REAL.set(core).is_ok()
}

/// Whether a Lean-verified REAL ML-KEM encaps core has been installed (so [`initiate`] produces the ML-KEM
/// ciphertext + shared secret from the Lean-verified object rather than the `ml-kem` crate's `.encapsulate`).
/// A deployed, verified node installs one at startup.
pub fn mlkem_encaps_real_core_installed() -> bool {
    LEAN_KEM_ENCAPS_CORE_REAL.get().is_some()
}

/// Outcome of installing the Lean-verified REAL ML-KEM encaps core as [`initiate`]'s authority (via
/// [`install_verified_mlkem_encaps_core`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MlKemEncapsCoreInstall {
    /// The real core was installed by THIS call — the `ml-kem` crate is now out of the encaps TCB.
    Installed,
    /// A core was already installed this process (install is once-per-process) — crate still out of TCB.
    AlreadyInstalled,
    /// The linked Lean archive does not export the real encaps core; the `ml-kem`-crate fallback stays in
    /// place (a valid FIPS-203 encaps, but NOT the Lean-verified authority).
    ExportAbsent,
}

/// THE ONE install every deployed, archive-linked process calls to make the Lean-verified REAL, full-byte
/// ML-KEM-768 encaps core ([`install_lean_kem_encaps_core_real`]) the ciphertext+secret AUTHORITY behind
/// [`initiate`] — taking the `ml-kem` crate OUT of that process's KEM-encaps TCB.
///
/// dregg-pq stays a LIGHT leaf: the archive-dependent symbols are INJECTED as `fn` pointers rather than
/// depended on. Gated on `export_available()`: install ONLY when the linked archive actually EXPORTS the real
/// core. When the export is absent we return [`MlKemEncapsCoreInstall::ExportAbsent`] and keep the
/// `ml-kem`-crate fallback (a valid FIPS-203 encaps) rather than bricking encaps. Idempotent and
/// once-per-process.
pub fn install_verified_mlkem_encaps_core(
    export_available: fn() -> bool,
    shadow: fn(wire: &str) -> Option<String>,
) -> MlKemEncapsCoreInstall {
    if !export_available() {
        return MlKemEncapsCoreInstall::ExportAbsent;
    }
    if install_lean_kem_encaps_core_real(shadow) {
        MlKemEncapsCoreInstall::Installed
    } else {
        MlKemEncapsCoreInstall::AlreadyInstalled
    }
}

/// THE ONE install every deployed, archive-linked process calls to make the Lean-verified REAL, full-byte
/// ML-KEM-768 decaps core ([`install_lean_kem_decaps_core_real`]) the shared-secret AUTHORITY behind
/// [`HybridResponder::finish`] — taking the `ml-kem` crate OUT of that process's KEM-decaps TCB.
///
/// dregg-pq stays a LIGHT leaf: the archive-dependent symbols are INJECTED as `fn` pointers rather than
/// depended on. Every host passes the SAME two `dregg-lean-ffi` symbols:
///
/// ```ignore
/// dregg_pq::install_verified_mlkem_decaps_core(
///     dregg_lean_ffi::mlkem_decaps_real_core_available,
///     |w| dregg_lean_ffi::shadow_mlkem_decaps_real(w).ok(),
/// )
/// ```
///
/// Gated on `export_available()` (the `mlkem_decaps_real_core_available()` check): install ONLY when the
/// linked archive actually EXPORTS the real core. A stale archive lacking it would make the installed core
/// return `None` on every call and — because [`HybridResponder::finish`] fails CLOSED on a core fault — reject
/// every ciphertext; so when the export is absent we return [`MlKemDecapsCoreInstall::ExportAbsent`] and keep
/// the `ml-kem`-crate fallback (a valid FIPS-203 decaps) rather than bricking decaps. Idempotent and
/// once-per-process.
pub fn install_verified_mlkem_decaps_core(
    export_available: fn() -> bool,
    shadow: fn(wire: &str) -> Option<String>,
) -> MlKemDecapsCoreInstall {
    if !export_available() {
        return MlKemDecapsCoreInstall::ExportAbsent;
    }
    if install_lean_kem_decaps_core_real(shadow) {
        MlKemDecapsCoreInstall::Installed
    } else {
        MlKemDecapsCoreInstall::AlreadyInstalled
    }
}

/// Marshal `(dk, ct)` into the byte wire the Lean real decaps core reads: `"hex(dk) hex(ct)"` (two
/// space-separated lowercase-hex fields).
fn real_decaps_wire(dk: &[u8], ct: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity((dk.len() + ct.len()) * 2 + 1);
    for (i, field) in [dk, ct].into_iter().enumerate() {
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

/// Decode the Lean real decaps core's reply — exactly 64 lowercase-hex chars — into the 32-byte ML-KEM shared
/// secret. `None` on any malformed reply (wrong length, non-hex, or `"ERR"`), which the caller treats as a
/// fail-closed decaps fault.
fn decode_ss_hex(reply: &str) -> Option<[u8; 32]> {
    let bytes = reply.as_bytes();
    if bytes.len() != 64 {
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
    let mut out = [0u8; 32];
    for (i, chunk) in bytes.chunks_exact(2).enumerate() {
        out[i] = (nibble(chunk[0])? << 4) | nibble(chunk[1])?;
    }
    Some(out)
}

/// Marshal `(ek, m)` into the byte wire the Lean real encaps core reads: `"hex(ek) hex(m)"` (two
/// space-separated lowercase-hex fields).
fn real_encaps_wire(ek: &[u8], m: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity((ek.len() + m.len()) * 2 + 1);
    for (i, field) in [ek, m].into_iter().enumerate() {
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

/// Decode the Lean real encaps core's reply — `"hex(ct) hex(K)"` (two space-separated lowercase-hex fields:
/// the 1088-byte ciphertext + 32-byte shared secret) — into `(ct_bytes, ss)`. `None` on any malformed reply
/// (wrong field count, wrong length, non-hex, or `"ERR"`), which the caller treats as a fail-closed encaps
/// fault.
fn decode_ct_ss_hex(reply: &str) -> Option<(Vec<u8>, [u8; 32])> {
    fn nibble(c: u8) -> Option<u8> {
        match c {
            b'0'..=b'9' => Some(c - b'0'),
            b'a'..=b'f' => Some(c - b'a' + 10),
            b'A'..=b'F' => Some(c - b'A' + 10),
            _ => None,
        }
    }
    fn hex_bytes(field: &str) -> Option<Vec<u8>> {
        let b = field.as_bytes();
        if b.is_empty() || b.len() % 2 != 0 {
            return None;
        }
        let mut out = Vec::with_capacity(b.len() / 2);
        for chunk in b.chunks_exact(2) {
            out.push((nibble(chunk[0])? << 4) | nibble(chunk[1])?);
        }
        Some(out)
    }
    let mut fields = reply.split(' ');
    let ct_hex = fields.next()?;
    let k_hex = fields.next()?;
    if fields.next().is_some() {
        return None; // exactly two fields
    }
    let ct = hex_bytes(ct_hex)?;
    let k = hex_bytes(k_hex)?;
    let ss: [u8; 32] = k.try_into().ok()?;
    Some((ct, ss))
}

type Ek = <MlKem768 as KemCore>::EncapsulationKey;
type Dk = <MlKem768 as KemCore>::DecapsulationKey;

/// HKDF domain-separation / version tag for the hybrid combiner. Bump on any
/// change to the transcript layout or combiner. Kept byte-identical to captp's
/// original inline value so the derived key is unchanged across the lift.
const HYBRID_DOMAIN: &[u8] = b"dregg-captp-hybrid-kem-x25519-mlkem768-v1";

/// Errors from the hybrid handshake (all are malformed-wire faults; the KEM
/// itself does not fail on well-formed input).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HybridError {
    /// The ML-KEM encapsulation key in an offer was the wrong length / malformed.
    BadEncapKey,
    /// The ML-KEM ciphertext in an initiator message was the wrong length /
    /// malformed.
    BadCiphertext,
    /// ML-KEM encapsulation failed (RNG fault).
    Encapsulation,
}

impl std::fmt::Display for HybridError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HybridError::BadEncapKey => write!(f, "malformed ML-KEM encapsulation key"),
            HybridError::BadCiphertext => write!(f, "malformed ML-KEM ciphertext"),
            HybridError::Encapsulation => write!(f, "ML-KEM encapsulation failed"),
        }
    }
}

impl std::error::Error for HybridError {}

/// An OS-backed CSPRNG adapter exposing the `rand_core` 0.6 `CryptoRngCore` that
/// `ml-kem` / `x25519-dalek` require, sourced from `getrandom`. Every call reads
/// fresh OS entropy (no reseed state to compromise).
struct OsCsprng;

impl rand_core::RngCore for OsCsprng {
    fn next_u32(&mut self) -> u32 {
        let mut b = [0u8; 4];
        self.fill_bytes(&mut b);
        u32::from_le_bytes(b)
    }
    fn next_u64(&mut self) -> u64 {
        let mut b = [0u8; 8];
        self.fill_bytes(&mut b);
        u64::from_le_bytes(b)
    }
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        getrandom::fill(dest).expect("getrandom failed");
    }
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}

impl rand_core::CryptoRng for OsCsprng {}

/// The responder's public offer: its X25519 ephemeral public key and its
/// ML-KEM-768 encapsulation key. Sent to the initiator to open a hybrid
/// handshake.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HybridOffer {
    /// X25519 ephemeral public key (classical half).
    pub x25519_pk: [u8; 32],
    /// ML-KEM-768 encapsulation key bytes (post-quantum half, 1184 B).
    pub mlkem_ek: Vec<u8>,
}

/// The initiator's reply: its X25519 ephemeral public key and the ML-KEM
/// ciphertext encapsulated to the responder's encapsulation key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HybridInitiatorMessage {
    /// X25519 ephemeral public key (classical half).
    pub x25519_pk: [u8; 32],
    /// ML-KEM-768 ciphertext (post-quantum half, 1088 B).
    pub mlkem_ct: Vec<u8>,
}

/// Responder-side secret state kept between publishing a [`HybridOffer`] and
/// calling [`finish`](HybridResponder::finish). Holds the X25519 secret, the
/// ML-KEM decapsulation key, and a copy of the public offer material needed to
/// reconstruct the transcript.
pub struct HybridResponder {
    x25519_sk: StaticSecret,
    x25519_pk: [u8; 32],
    mlkem_dk: Dk,
    mlkem_ek_bytes: Vec<u8>,
}

/// Build the concatenation-KDF transcript: the exact public handshake bytes, in
/// a fixed order both sides agree on.
fn transcript(offer_x25519: &[u8; 32], ek: &[u8], msg_x25519: &[u8; 32], ct: &[u8]) -> Vec<u8> {
    let mut t = Vec::with_capacity(32 + ek.len() + 32 + ct.len());
    t.extend_from_slice(offer_x25519);
    t.extend_from_slice(ek);
    t.extend_from_slice(msg_x25519);
    t.extend_from_slice(ct);
    t
}

/// The load-bearing combiner: HKDF-SHA256 over `ss_x25519 ‖ ss_mlkem`
/// (concatenation, never XOR) with the transcript as HKDF `info`. See the module
/// docs.
pub fn combine(ss_x25519: &[u8; 32], ss_mlkem: &[u8; 32], transcript: &[u8]) -> [u8; 32] {
    let mut ikm = Vec::with_capacity(64);
    ikm.extend_from_slice(ss_x25519);
    ikm.extend_from_slice(ss_mlkem);

    let hk = Hkdf::<Sha256>::new(Some(HYBRID_DOMAIN), &ikm);
    let mut info = Vec::with_capacity(HYBRID_DOMAIN.len() + transcript.len());
    info.extend_from_slice(HYBRID_DOMAIN);
    info.extend_from_slice(transcript);

    let mut key = [0u8; 32];
    hk.expand(&info, &mut key)
        .expect("HKDF-SHA256 expand of 32 bytes never fails");
    ikm.zeroize();
    key
}

fn shared_to_array(ss: ml_kem::SharedKey<MlKem768>) -> [u8; 32] {
    let mut out = [0u8; 32];
    out.copy_from_slice(ss.as_slice());
    out
}

/// Responder step 1: mint a fresh hybrid offer and keep the matching secret
/// state. The returned [`HybridOffer`] is sent to the initiator; the
/// [`HybridResponder`] is retained for [`finish`](HybridResponder::finish).
pub fn responder_offer() -> (HybridOffer, HybridResponder) {
    let mut rng = OsCsprng;

    // Classical half: fresh X25519 ephemeral keypair.
    let x25519_sk = StaticSecret::random_from_rng(&mut rng);
    let x25519_pk = PublicKey::from(&x25519_sk).to_bytes();

    // Post-quantum half: fresh ML-KEM-768 keypair.
    let (mlkem_dk, mlkem_ek) = MlKem768::generate(&mut rng);
    let mlkem_ek_bytes = mlkem_ek.as_bytes().to_vec();

    let offer = HybridOffer {
        x25519_pk,
        mlkem_ek: mlkem_ek_bytes.clone(),
    };
    let responder = HybridResponder {
        x25519_sk,
        x25519_pk,
        mlkem_dk,
        mlkem_ek_bytes,
    };
    (offer, responder)
}

/// Initiator step: consume a responder's [`HybridOffer`], deriving the session
/// key and the [`HybridInitiatorMessage`] to send back.
///
/// Fails only if the offer's ML-KEM encapsulation key is malformed.
pub fn initiate(offer: &HybridOffer) -> Result<(HybridInitiatorMessage, [u8; 32]), HybridError> {
    let mut rng = OsCsprng;

    // Classical half: our ephemeral X25519 + DH against the offer's pk.
    let x25519_sk = StaticSecret::random_from_rng(&mut rng);
    let x25519_pk = PublicKey::from(&x25519_sk).to_bytes();
    let ss_x25519 = x25519_sk
        .diffie_hellman(&PublicKey::from(offer.x25519_pk))
        .to_bytes();

    // Post-quantum half: encapsulate to the offer's ML-KEM key. Length-gate the encapsulation key first (a
    // wrong-length ek is a malformed-wire fault on BOTH paths); `ek_encoded` is consumed by the crate fallback.
    let ek_encoded =
        Encoded::<Ek>::try_from(offer.mlkem_ek.as_slice()).map_err(|_| HybridError::BadEncapKey)?;
    let (ct_bytes, ss_mlkem) = if let Some(core) = LEAN_KEM_ENCAPS_CORE_REAL.get() {
        // AUTHORITY: the Lean-verified real encaps core over the real bytes. The `ml-kem` crate's
        // `.encapsulate` is NOT consulted on this path — it has left the KEM-encaps TCB. We generate our own
        // 32-byte `m` (fresh OS entropy, exactly as the crate's randomized encaps does internally); the core
        // deterministically produces `(ct, K)` from `(ek, m)`. A `None` (archive fault) or malformed
        // (`"ERR"` / wrong-length / non-hex) reply fails CLOSED as an encapsulation fault.
        let mut m = [0u8; 32];
        rng.fill_bytes(&mut m);
        let wire = real_encaps_wire(&offer.mlkem_ek, &m);
        let reply = core(&wire).ok_or(HybridError::Encapsulation)?;
        m.zeroize();
        decode_ct_ss_hex(&reply).ok_or(HybridError::Encapsulation)?
    } else {
        // FALLBACK (no verified core installed): the `ml-kem` crate primitive.
        let ek = Ek::from_bytes(&ek_encoded);
        let (ct, ss_mlkem) = ek
            .encapsulate(&mut rng)
            .map_err(|_| HybridError::Encapsulation)?;
        (ct.as_slice().to_vec(), shared_to_array(ss_mlkem))
    };

    let t = transcript(&offer.x25519_pk, &offer.mlkem_ek, &x25519_pk, &ct_bytes);
    let session_key = combine(&ss_x25519, &ss_mlkem, &t);

    Ok((
        HybridInitiatorMessage {
            x25519_pk,
            mlkem_ct: ct_bytes,
        },
        session_key,
    ))
}

impl HybridResponder {
    /// Responder step 2: consume the initiator's message and derive the session
    /// key — identical to the initiator's when the handshake is faithful.
    ///
    /// Fails only if the ML-KEM ciphertext is malformed.
    ///
    /// # The ML-KEM shared secret comes from the Lean-verified core, not the crate
    ///
    /// When a Lean-verified REAL decaps core is installed ([`install_lean_kem_decaps_core_real`], done by any
    /// process that can link `dregg-lean-ffi`), the ML-KEM half's shared secret is recovered by the extracted,
    /// full-byte `MlKemDecaps.mlkemDecaps` (BRICK K6) over the actual `dk ‖ ct` bytes — running as leanc-native
    /// code, PROVED to recover a genuine crate secret and implicit-reject tampers to a DIFFERENT secret. On
    /// that path the `ml-kem` crate's `.decapsulate` is NOT called: the crate has left the decaps TCB. The
    /// X25519 + transcript + HKDF combiner around the ML-KEM secret is unchanged.
    ///
    /// When NO verified core is installed (a caller that has not wired the Lean archive), this falls back to
    /// the `ml-kem` crate primitive. `dregg-pq` is a light leaf and cannot itself link the ~195 MB Lean
    /// archive, so the routing is an install-time seam rather than a direct call; a deployed, verified node
    /// installs the real core at startup and thereby leaves the crate out of the KEM-decaps TCB.
    pub fn finish(&self, msg: &HybridInitiatorMessage) -> Result<[u8; 32], HybridError> {
        // Classical half: DH of our secret against the initiator's pk.
        let ss_x25519 = self
            .x25519_sk
            .diffie_hellman(&PublicKey::from(msg.x25519_pk))
            .to_bytes();

        // Post-quantum half: recover the ML-KEM shared secret. Length-gate the ciphertext first (a
        // wrong-length ct is a malformed-wire fault on BOTH paths); `ct` is consumed by the crate fallback.
        let ct = Ciphertext::<MlKem768>::try_from(msg.mlkem_ct.as_slice())
            .map_err(|_| HybridError::BadCiphertext)?;
        let ss_mlkem = if let Some(core) = LEAN_KEM_DECAPS_CORE_REAL.get() {
            // AUTHORITY: the Lean-verified real decaps core over the real bytes. The `ml-kem` crate's
            // `.decapsulate` is NOT consulted on this path — it has left the KEM-decaps TCB. A `None` (archive
            // fault) or malformed (`"ERR"` / non-32-byte) reply fails CLOSED as a bad ciphertext, so the node
            // never proceeds with a wrong secret. A well-formed-but-tampered ct returns the implicit-reject
            // secret (a valid 64-hex-char reply), so the parties diverge — ML-KEM's implicit-reject semantics.
            let dk_bytes = self.mlkem_dk.as_bytes();
            let wire = real_decaps_wire(dk_bytes.as_slice(), &msg.mlkem_ct);
            let reply = core(&wire).ok_or(HybridError::BadCiphertext)?;
            decode_ss_hex(&reply).ok_or(HybridError::BadCiphertext)?
        } else {
            // FALLBACK (no verified core installed): the `ml-kem` crate primitive.
            shared_to_array(
                self.mlkem_dk
                    .decapsulate(&ct)
                    .map_err(|_| HybridError::BadCiphertext)?,
            )
        };

        let t = transcript(
            &self.x25519_pk,
            &self.mlkem_ek_bytes,
            &msg.x25519_pk,
            &msg.mlkem_ct,
        );
        Ok(combine(&ss_x25519, &ss_mlkem, &t))
    }
}

/// **Bare ML-KEM-768 (FIPS 203) key generation** — the post-quantum KEM half exposed on its own, for the
/// X-Wing hybrids that combine it with a SEPARATELY-run X25519 (e.g. the orb TLS 1.3 `X25519MLKEM768`
/// key exchange, whose classical half is its own EverCrypt X25519 and whose combiner is its own concat-KDF).
/// Returns `(ek, dk)` — the 1184-byte encapsulation key and the 2400-byte decapsulation key at their
/// FIPS-203 ML-KEM-768 sizes. The SAME `ml-kem` v0.2.3 primitive [`responder_offer`] mints its post-quantum
/// half from; dregg `MlKemIndCca` grounds its IND-CCA in the MLWE lattice floor.
pub fn ml_kem768_keygen() -> (Vec<u8>, Vec<u8>) {
    let mut rng = OsCsprng;
    let (dk, ek) = MlKem768::generate(&mut rng);
    (ek.as_bytes().to_vec(), dk.as_bytes().to_vec())
}

/// **Bare ML-KEM-768 encapsulation.** Encapsulate to a 1184-byte encapsulation key `ek`, returning the
/// 1088-byte ciphertext and the 32-byte shared secret `(ct, ss)`. `None` on a wrong-length/malformed `ek`
/// (fail-closed). The SAME primitive [`initiate`]s post-quantum half calls; the encaps randomness is fresh
/// OS entropy. The orb TLS X-Wing server side runs this for the ML-KEM half, then concat-KDFs `ss` with its
/// X25519 secret.
pub fn ml_kem768_encaps(ek: &[u8]) -> Option<(Vec<u8>, [u8; 32])> {
    let ek_encoded = Encoded::<Ek>::try_from(ek).ok()?;
    let ek = Ek::from_bytes(&ek_encoded);
    let mut rng = OsCsprng;
    let (ct, ss) = ek.encapsulate(&mut rng).ok()?;
    Some((ct.as_slice().to_vec(), shared_to_array(ss)))
}

/// **Bare ML-KEM-768 decapsulation.** Recover the 32-byte shared secret from a 1088-byte ciphertext `ct`
/// under the 2400-byte decapsulation key `dk`. `None` on a wrong-length/malformed `dk`/`ct` (fail-closed).
/// A well-formed-but-tampered ciphertext does NOT fail: it implicit-rejects to a DIFFERENT (message-
/// independent) secret — ML-KEM FO implicit-reject — so the two parties diverge without leaking, exactly the
/// behavior [`HybridResponder::finish`] relies on. The orb TLS X-Wing client side runs this.
pub fn ml_kem768_decaps(dk: &[u8], ct: &[u8]) -> Option<[u8; 32]> {
    let dk_encoded = Encoded::<Dk>::try_from(dk).ok()?;
    let dk = Dk::from_bytes(&dk_encoded);
    let ct = Ciphertext::<MlKem768>::try_from(ct).ok()?;
    Some(shared_to_array(dk.decapsulate(&ct).ok()?))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// KEM correctness: both parties derive the SAME session key from the hybrid
    /// handshake (X25519 + ML-KEM-768 round trip).
    #[test]
    fn hybrid_roundtrip_same_key() {
        let (offer, responder) = responder_offer();
        // Offer carries both halves at their FIPS-203 / X25519 sizes.
        assert_eq!(offer.x25519_pk.len(), 32);
        assert_eq!(offer.mlkem_ek.len(), 1184); // ML-KEM-768 encapsulation key

        let (msg, initiator_key) = initiate(&offer).expect("initiate");
        assert_eq!(msg.mlkem_ct.len(), 1088); // ML-KEM-768 ciphertext

        let responder_key = responder.finish(&msg).expect("finish");
        assert_eq!(
            initiator_key, responder_key,
            "both sides must agree on the hybrid session key"
        );
    }

    /// HYBRID-DEPENDENCE: the derived session key depends on BOTH secrets.
    /// Zeroing or replacing either secret alone changes the key, and the
    /// transcript binds in too. This pins the concatenation-KDF combiner:
    /// neither half can be cancelled.
    #[test]
    fn hybrid_dependence_on_both_secrets() {
        let ss_x = [0x11u8; 32];
        let ss_m = [0x22u8; 32];
        let t = b"fixed-transcript";

        let key = combine(&ss_x, &ss_m, t);

        assert_ne!(
            key,
            combine(&ss_x, &[0u8; 32], t),
            "zeroing the ML-KEM secret must change the key"
        );
        assert_ne!(
            key,
            combine(&ss_x, &[0x33u8; 32], t),
            "replacing the ML-KEM secret must change the key"
        );
        assert_ne!(
            key,
            combine(&[0u8; 32], &ss_m, t),
            "zeroing the X25519 secret must change the key"
        );
        assert_ne!(
            key,
            combine(&[0x44u8; 32], &ss_m, t),
            "replacing the X25519 secret must change the key"
        );
        assert_ne!(
            key,
            combine(&ss_x, &ss_m, b"other-transcript"),
            "the transcript must bind into the key"
        );
    }

    /// End-to-end: a ciphertext tampered in flight makes the responder derive a
    /// DIFFERENT key than the initiator — the ML-KEM half genuinely participates.
    #[test]
    fn hybrid_tampered_ciphertext_diverges() {
        let (offer, responder) = responder_offer();
        let (mut msg, initiator_key) = initiate(&offer).expect("initiate");

        msg.mlkem_ct[500] ^= 0xff;
        let responder_key = responder.finish(&msg).expect("finish still succeeds");
        assert_ne!(
            initiator_key, responder_key,
            "tampering the PQ ciphertext must break key agreement"
        );
    }

    /// The routing seam sends the ML-KEM encaps/decaps through the extracted, Lean-verified cores. The
    /// installed cores stand in for `dregg-lean-ffi::shadow_fips203_{encaps,decaps}` (which drive the
    /// leanc-native `encapsCore`/`decapsCore`; their round-trip is green in dregg-lean-ffi's
    /// `verified_ml_kem_encaps_decaps_roundtrips_in_lean`). They carry the SAME contract the Lean FFI
    /// proves: the honest deployed data `(A,t,s)=(1,2,1)`, message `m=1` ENCAPS to `"1 1667 3"`; DECAPS of
    /// that ciphertext recovers `"3"` (the round-trip that discharges `Fips203Correct`); a TAMPERED
    /// ciphertext implicit-rejects to a DIFFERENT secret (`"3536"` ≠ `"3"`).
    #[test]
    fn kem_routes_through_lean_core() {
        // No cores installed ⇒ the seams decline and the caller falls back.
        assert_eq!(ml_kem_encaps_core("1 2 1"), None);
        assert_eq!(ml_kem_decaps_core("1 2 1 0 1 1667"), None);

        // Install cores carrying the extracted encaps/decaps cores' proven contract (the `#guard` teeth).
        let enc_installed = install_lean_encaps_core(|wire| {
            Some(
                match wire {
                    "1 2 1" => "1 1667 3",
                    _ => "ERR",
                }
                .to_string(),
            )
        });
        assert!(enc_installed, "first encaps install succeeds");
        assert!(
            !install_lean_encaps_core(|_| None),
            "encaps install is once-per-process"
        );
        let dec_installed = install_lean_decaps_core(|wire| {
            Some(
                match wire {
                    // honest ciphertext ⇒ recovers the encapsulated secret K=3
                    "1 2 1 0 1 1667" => "3",
                    // tampered ciphertext ⇒ implicit reject to a DIFFERENT (message-independent) secret
                    "1 2 1 0 1 1767" => "3536",
                    _ => "ERR",
                }
                .to_string(),
            )
        });
        assert!(dec_installed, "first decaps install succeeds");
        assert!(
            !install_lean_decaps_core(|_| None),
            "decaps install is once-per-process"
        );

        // The honest encaps produces the ciphertext + encapsulated secret wire.
        let enc = ml_kem_encaps_core("1 2 1").expect("encaps core installed");
        assert_eq!(
            enc, "1 1667 3",
            "honest encaps emits the ciphertext + secret"
        );

        // ROUND-TRIP: decaps of the honest ciphertext recovers the encapsulated secret K=3.
        assert_eq!(
            ml_kem_decaps_core("1 2 1 0 1 1667"),
            Some("3".to_string()),
            "the extracted encaps output round-trips through the decaps core"
        );

        // A TAMPERED ciphertext implicit-rejects to a DIFFERENT secret — the parties diverge.
        assert_eq!(
            ml_kem_decaps_core("1 2 1 0 1 1767"),
            Some("3536".to_string()),
            "a tampered ciphertext implicit-rejects to a different secret"
        );
        assert_ne!(
            ml_kem_decaps_core("1 2 1 0 1 1767"),
            ml_kem_decaps_core("1 2 1 0 1 1667"),
            "tampering the ML-KEM ciphertext breaks key agreement"
        );
    }

    /// Malformed post-quantum material is rejected, not silently accepted.
    #[test]
    fn hybrid_rejects_malformed_material() {
        let (mut offer, _responder) = responder_offer();
        offer.mlkem_ek.truncate(10);
        assert_eq!(initiate(&offer).unwrap_err(), HybridError::BadEncapKey);

        let (offer, responder) = responder_offer();
        let (mut msg, _k) = initiate(&offer).unwrap();
        msg.mlkem_ct.truncate(10);
        assert_eq!(
            responder.finish(&msg).unwrap_err(),
            HybridError::BadCiphertext
        );
    }

    /// BRICK K6 marshalling: the `dk ‖ ct` wire the Lean real decaps core reads is `"hex(dk) hex(ct)"`, and
    /// its 64-hex-char reply decodes back to the 32-byte shared secret; a malformed reply (`"ERR"`, wrong
    /// length, non-hex) fails closed to `None`. These are the pure marshallers `finish` uses on the
    /// Lean-routed path; the end-to-end real-core install + recover is the running-binary gate
    /// `node/tests/mlkem_live_decaps.rs` (which links the archive).
    #[test]
    fn real_decaps_wire_and_reply_roundtrip() {
        // Wire is two space-separated lowercase-hex fields.
        assert_eq!(
            real_decaps_wire(&[0x00, 0xff, 0x10], &[0xab, 0x01]),
            "00ff10 ab01"
        );
        assert_eq!(real_decaps_wire(&[], &[]), " ");

        // A 32-byte secret round-trips through hex.
        let ss = [
            0x00u8, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd,
            0xee, 0xff, 0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0xfe, 0xdc, 0xba, 0x98,
            0x76, 0x54, 0x32, 0x10,
        ];
        let hex: String = ss.iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(decode_ss_hex(&hex), Some(ss));

        // Fail-closed replies decode to None (the caller treats these as a bad-ciphertext fault).
        assert_eq!(
            decode_ss_hex("ERR"),
            None,
            "the malformed-wire sentinel fails closed"
        );
        assert_eq!(decode_ss_hex(""), None, "empty reply fails closed");
        assert_eq!(
            decode_ss_hex(&hex[..62]),
            None,
            "short (31-byte) reply fails closed"
        );
        assert_eq!(
            decode_ss_hex(&format!("{}zz", &hex[..62])),
            None,
            "non-hex reply fails closed"
        );
    }

    /// BRICK K5 marshalling: the `ek ‖ m` wire the Lean real encaps core reads is `"hex(ek) hex(m)"`, and its
    /// `"hex(ct) hex(K)"` reply decodes back to `(ct_bytes, ss)`; a malformed reply (`"ERR"`, wrong field
    /// count, odd-length hex, wrong K length, non-hex) fails closed to `None`. These are the pure marshallers
    /// `initiate` uses on the Lean-routed path; the end-to-end real-core install + byte-exact encaps + full
    /// handshake is the running-binary gate `node/tests/mlkem_live_encaps.rs` (which links the archive).
    #[test]
    fn real_encaps_wire_and_reply_roundtrip() {
        // Wire is two space-separated lowercase-hex fields.
        assert_eq!(
            real_encaps_wire(&[0x00, 0xff, 0x10], &[0xab, 0x01]),
            "00ff10 ab01"
        );
        assert_eq!(real_encaps_wire(&[], &[]), " ");

        // A `(ct, K)` reply round-trips: a 3-byte ct + a 32-byte K.
        let ct = vec![0xde, 0xad, 0xbe];
        let ss = [
            0x00u8, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd,
            0xee, 0xff, 0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0xfe, 0xdc, 0xba, 0x98,
            0x76, 0x54, 0x32, 0x10,
        ];
        let ct_hex: String = ct.iter().map(|b| format!("{b:02x}")).collect();
        let ss_hex: String = ss.iter().map(|b| format!("{b:02x}")).collect();
        let reply = format!("{ct_hex} {ss_hex}");
        assert_eq!(decode_ct_ss_hex(&reply), Some((ct.clone(), ss)));

        // Fail-closed replies decode to None.
        assert_eq!(
            decode_ct_ss_hex("ERR"),
            None,
            "the malformed sentinel fails closed"
        );
        assert_eq!(decode_ct_ss_hex(""), None, "empty reply fails closed");
        assert_eq!(
            decode_ct_ss_hex(&ct_hex),
            None,
            "one field (no K) fails closed"
        );
        assert_eq!(
            decode_ct_ss_hex(&format!("{ct_hex} {ss_hex} extra")),
            None,
            "three fields fail closed"
        );
        assert_eq!(
            decode_ct_ss_hex(&format!("{ct_hex} {}", &ss_hex[..62])),
            None,
            "a 31-byte K fails closed (wrong shared-secret length)"
        );
        assert_eq!(
            decode_ct_ss_hex(&format!("{ct_hex} {}zz", &ss_hex[..62])),
            None,
            "non-hex K fails closed"
        );
    }

    /// The shared encaps install seam reports `ExportAbsent` (and does NOT install) when the archive lacks the
    /// real encaps export — the gate that keeps the `ml-kem`-crate fallback rather than bricking encaps. (Kept
    /// export-absent so it never touches the once-per-process `LEAN_KEM_ENCAPS_CORE_REAL` cell that the
    /// running-binary gate installs.)
    #[test]
    fn mlkem_encaps_install_seam_export_absent_keeps_fallback() {
        assert_eq!(
            install_verified_mlkem_encaps_core(|| false, |_| None),
            MlKemEncapsCoreInstall::ExportAbsent,
            "an absent export must NOT install a core (crate fallback stays)"
        );
        assert!(
            !mlkem_encaps_real_core_installed(),
            "no real KEM encaps core is installed by the export-absent path"
        );
    }

    /// The shared install seam reports `ExportAbsent` (and does NOT install) when the archive lacks the real
    /// decaps export — the gate that keeps the `ml-kem`-crate fallback rather than bricking decaps. (Kept
    /// export-absent so it never touches the once-per-process `LEAN_KEM_DECAPS_CORE_REAL` cell that the
    /// running-binary gate installs.)
    #[test]
    fn mlkem_install_seam_export_absent_keeps_fallback() {
        assert_eq!(
            install_verified_mlkem_decaps_core(|| false, |_| None),
            MlKemDecapsCoreInstall::ExportAbsent,
            "an absent export must NOT install a core (crate fallback stays)"
        );
        assert!(
            !mlkem_decaps_real_core_installed(),
            "no real KEM decaps core is installed by the export-absent path"
        );
    }
}
