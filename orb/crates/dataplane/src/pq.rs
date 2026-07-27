//! The post-quantum (ML-DSA-65 / FIPS 204) half of the orb's hybrid JWT verify.
//!
//! `Jwt.lean`'s `Crypto.mlDsaVerify` (`@[extern "drorb_ml_dsa_verify"]`) is the
//! post-quantum verifier the `Jwt.Alg.hybrid` path calls. The C crypto shim
//! (`ffi/crypto_shim.c`, `drorb_ml_dsa_verify`) marshals the four Lean
//! `ByteArray`s to raw `(ptr, len)` and calls [`drorb_pq_ml_dsa_verify`] here,
//! which is `dregg_pq::ml_dsa_verify` — the SAME fail-closed FIPS-204 verify the
//! dregg federation core uses (ed25519 ∧ ML-DSA-65).
//!
//! # Where the soundness lives
//!
//! `dregg_pq::ml_dsa_verify` fails CLOSED on a wrong-length key/signature and,
//! when the Lean-verified core is installed
//! (`dregg_pq::install_verified_mldsa_verify_core`, a deploy-time step that
//! co-links dregg's Lean archive via `dregg-lean-ffi`), routes the accept/reject
//! verdict through dregg's extracted, PROVED `MlDsaVerifyReal.verifyCore` — taking
//! the `fips204` crate out of the verify TCB. Absent that install (this
//! build+prove cut), it uses the `fips204` crate primitive, a valid FIPS-204
//! verify that dregg's `verifyCore` is proven byte-for-byte to agree with. Either
//! way the ML-DSA half's forgery-resistance is dregg's proof — the orb composes,
//! it does not re-derive FIPS-204 (see `Crypto.Assumptions.mlDsaVerify_authentic`).

use std::slice;

/// The C-ABI entry the crypto shim's `drorb_ml_dsa_verify` calls: verify an
/// ML-DSA-65 (FIPS 204) signature over `msg` under domain-separation `ctx`,
/// against the pinned public key `pk`. Returns `1` on a valid signature, `0`
/// otherwise — fail-closed: a wrong-length key/signature, a forged/tampered
/// signature, a wrong `ctx`, or a null pointer all return `0`.
///
/// # Safety
/// Each `(ptr, len)` pair must describe a readable byte range for the duration of
/// the call, or be `(null, 0)`. Lean `ByteArray`s always satisfy this.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn drorb_pq_ml_dsa_verify(
    pk: *const u8,
    pk_len: usize,
    msg: *const u8,
    msg_len: usize,
    sig: *const u8,
    sig_len: usize,
    ctx: *const u8,
    ctx_len: usize,
) -> u8 {
    fn as_slice<'a>(p: *const u8, n: usize) -> &'a [u8] {
        if n == 0 || p.is_null() {
            &[]
        } else {
            // SAFETY: the caller (the Lean `ByteArray` shim) guarantees `(p, n)`
            // is a readable byte range for the duration of the call.
            unsafe { slice::from_raw_parts(p, n) }
        }
    }
    let pk = as_slice(pk, pk_len);
    let msg = as_slice(msg, msg_len);
    let sig = as_slice(sig, sig_len);
    let ctx = as_slice(ctx, ctx_len);
    // dregg_pq::ml_dsa_verify(public_bytes, ctx, message, sig_bytes) -> bool.
    dregg_pq::ml_dsa_verify(pk, ctx, msg, sig) as u8
}

/// The C-ABI entry the crypto shim's `drorb_ml_kem_encaps` calls: ML-KEM-768
/// (FIPS 203) encapsulate to the 1184-byte encapsulation key `ek`. On success
/// writes the 1088-byte ciphertext followed by the 32-byte shared secret (1120
/// bytes total) into `out` and returns `1`; on a wrong-length / malformed `ek`
/// (or a null pointer) writes nothing and returns `0` — fail-closed.
///
/// This is `dregg_pq::ml_kem768_encaps` — the SAME `ml-kem` v0.2.3 ML-KEM-768
/// primitive dregg's proven X-Wing hybrid KEM (`hybrid_kem`) is built on, whose
/// IND-CCA dregg grounds in the MLWE lattice floor. The orb composes; it does not
/// re-derive FIPS 203 (see `Crypto.Xwing.mlKem_ind_cca`).
///
/// # Safety
/// `ek` must describe a readable `ek_len`-byte range (or be null); `out` must be
/// writable for 1120 bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn drorb_pq_ml_kem_encaps(ek: *const u8, ek_len: usize, out: *mut u8) -> u8 {
    if ek.is_null() || out.is_null() {
        return 0;
    }
    // SAFETY: the caller (the Lean `ByteArray` shim) guarantees `(ek, ek_len)` is
    // a readable range and `out` is writable for 1120 bytes.
    let ek = unsafe { slice::from_raw_parts(ek, ek_len) };
    match dregg_pq::ml_kem768_encaps(ek) {
        Some((ct, ss)) if ct.len() == 1088 => {
            unsafe {
                std::ptr::copy_nonoverlapping(ct.as_ptr(), out, 1088);
                std::ptr::copy_nonoverlapping(ss.as_ptr(), out.add(1088), 32);
            }
            1
        }
        _ => 0,
    }
}

/// The C-ABI entry the crypto shim's `drorb_ml_kem_decaps` calls: ML-KEM-768
/// (FIPS 203) decapsulate the 1088-byte ciphertext `ct` under the 2400-byte
/// decapsulation key `dk`. On success writes the 32-byte shared secret into `out`
/// and returns `1`; on a wrong-length / malformed key/ciphertext (or a null
/// pointer) returns `0` — fail-closed. A well-formed-but-TAMPERED ciphertext does
/// not fail: it returns `1` with the DIFFERENT (message-independent) implicit-reject
/// secret (ML-KEM's FO implicit-reject), so the parties diverge without leaking.
///
/// This is `dregg_pq::ml_kem768_decaps` — dregg's proven ML-KEM-768 core.
///
/// # Safety
/// `dk`/`ct` must describe readable ranges (or be null); `out` must be writable
/// for 32 bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn drorb_pq_ml_kem_decaps(
    dk: *const u8,
    dk_len: usize,
    ct: *const u8,
    ct_len: usize,
    out: *mut u8,
) -> u8 {
    if dk.is_null() || ct.is_null() || out.is_null() {
        return 0;
    }
    // SAFETY: the caller guarantees the two `(ptr, len)` ranges are readable and
    // `out` is writable for 32 bytes.
    let dk = unsafe { slice::from_raw_parts(dk, dk_len) };
    let ct = unsafe { slice::from_raw_parts(ct, ct_len) };
    match dregg_pq::ml_kem768_decaps(dk, ct) {
        Some(ss) => {
            unsafe {
                std::ptr::copy_nonoverlapping(ss.as_ptr(), out, 32);
            }
            1
        }
        None => 0,
    }
}

/// Install the Lean-VERIFIED post-quantum cores as this process's accept/reject
/// AUTHORITY, taking the unverified `fips204` / `ml-kem` crates OUT of the
/// deployed verify+KEM TCB.
///
/// MUST be called once at startup, before any request can reach the JWT-hybrid
/// verify or the KEM. `dregg-pq` keeps its crate fallbacks until this runs, so
/// omitting the call is a SILENT downgrade: the binary looks identical and still
/// verifies signatures, but the authority behind the verdict is the unverified
/// crate rather than the proven core. That is why each arm below is ASSERTED
/// rather than logged-and-ignored — an `ExportAbsent` means the linked archive
/// does not carry the export (a stale archive), and serving on would advertise
/// assurance this build does not have.
///
/// Each `export_available` probe reads the ACTUAL linked archive, so a binary
/// spliced without the cores fails loudly here instead of falling back quietly.
pub fn install_verified_cores() {
    use dregg_pq::{
        MlDsaKeygenCoreRealInstall, MlDsaSignCoreRealInstall, MlDsaVerifyCoreInstall,
        MlKemDecapsCoreInstall, MlKemEncapsCoreInstall, MlKemKeygenCoreInstall,
        install_verified_mldsa_keygen_core_real, install_verified_mldsa_sign_core_real,
        install_verified_mldsa_verify_core, install_verified_mlkem_decaps_core,
        install_verified_mlkem_encaps_core, install_verified_mlkem_keygen_core,
    };

    // ML-DSA-65 verify: the proven `MlDsaVerifyReal.verifyCore`.
    let dsa = install_verified_mldsa_verify_core(
        dregg_lean_ffi::fips204_verify_real_core_available,
        |w| dregg_lean_ffi::shadow_fips204_verify_real(w).ok(),
    );
    assert!(
        matches!(
            dsa,
            MlDsaVerifyCoreInstall::Installed | MlDsaVerifyCoreInstall::AlreadyInstalled
        ),
        "verified ML-DSA verify core NOT installed ({dsa:?}) - the fips204 crate would stay the \
         deployed verify authority; refusing to serve a build that overstates its TCB"
    );

    // ML-DSA-65 sign: the proven, full-byte `MlDsaSignReal.signCore`. Installing
    // this is what takes the `fips204` crate out of the deployed SIGN TCB — until
    // it runs, `MlDsaKey::try_sign` answers from the crate primitive, and
    // dregg-pq's audit gate ABORTS the process rather than sign with it.
    //
    // NOTE the behavioural consequence, deliberately accepted: on the installed
    // path the signer is DETERMINISTIC (`rnd = 0`, the FIPS 204 deterministic
    // variant — spec-valid), where the crate fallback is hedged/randomized. Same
    // seed + ctx + message now yields identical signature bytes. That difference
    // is also the cheapest live discriminator for WHICH object signed.
    //
    // ASSERTED, not warn-and-continue: unlike `node` (which logs `ExportAbsent`
    // and keeps the hedged crate fallback so signing does not brick), this binary
    // must never serve while advertising a TCB it does not have — an absent sign
    // core is fatal here exactly as an absent verify or KEM core is.
    let sign = install_verified_mldsa_sign_core_real(
        dregg_lean_ffi::fips204_sign_real_core_available,
        |w| dregg_lean_ffi::shadow_fips204_sign_real(w).ok(),
    );
    assert!(
        matches!(
            sign,
            MlDsaSignCoreRealInstall::Installed | MlDsaSignCoreRealInstall::AlreadyInstalled
        ),
        "verified ML-DSA sign core NOT installed ({sign:?}) - the fips204 crate would stay the \
         deployed sign authority (and dregg-pq's audit gate would abort on first sign); refusing \
         to serve a build that overstates its TCB"
    );

    // ML-KEM-768 encaps: the REAL, full-dimension `mlkemEncaps` core over the
    // byte wire dregg-pq marshals. NOT the `fips203_*` seam - that binds the
    // scalar toy export (wire grammar "A t m", three decimal ints), which is
    // also present in the archive, so its availability probe returns true and
    // the install would report Installed while every real KEM op fails closed.
    let enc =
        install_verified_mlkem_encaps_core(dregg_lean_ffi::mlkem_encaps_real_core_available, |w| {
            dregg_lean_ffi::shadow_mlkem_encaps_real(w).ok()
        });
    assert!(
        matches!(
            enc,
            MlKemEncapsCoreInstall::Installed | MlKemEncapsCoreInstall::AlreadyInstalled
        ),
        "verified ML-KEM encaps core NOT installed ({enc:?}) - the ml-kem crate would stay the \
         deployed encaps authority"
    );

    // ML-KEM-768 decaps: the REAL, full-dimension `mlkemDecaps` FO pipeline.
    let dec =
        install_verified_mlkem_decaps_core(dregg_lean_ffi::mlkem_decaps_real_core_available, |w| {
            dregg_lean_ffi::shadow_mlkem_decaps_real(w).ok()
        });
    assert!(
        matches!(
            dec,
            MlKemDecapsCoreInstall::Installed | MlKemDecapsCoreInstall::AlreadyInstalled
        ),
        "verified ML-KEM decaps core NOT installed ({dec:?}) - the ml-kem crate would stay the \
         deployed decaps authority"
    );

    // ML-KEM-768 keygen: the KAT-anchored deterministic FIPS 203 ML-KEM.KeyGen_internal core over a
    // 64-byte (d || z) seed. Installed ASSERT-FATAL like the other cores: once installed,
    // `dregg_pq::ml_kem768_keygen` mints (ek, dk) via the verified core and the `ml-kem` crate leaves the
    // KEM-keygen TCB. The byte<->ring kpkeKeyGen_refines_ring forall stays OPEN (KAT-anchored, not a
    // refinement proof). An ExportAbsent here means a stale archive without the keygen export.
    let kg =
        install_verified_mlkem_keygen_core(dregg_lean_ffi::mlkem_keygen_real_core_available, |w| {
            dregg_lean_ffi::shadow_mlkem_keygen_real(w).ok()
        });
    assert!(
        matches!(
            kg,
            MlKemKeygenCoreInstall::Installed | MlKemKeygenCoreInstall::AlreadyInstalled
        ),
        "verified ML-KEM keygen core NOT installed ({kg:?}) - the ml-kem crate would stay the \
         deployed keygen authority"
    );

    // ML-DSA-65 IDENTITY keygen: the KAT-anchored deterministic FIPS 204 ML-DSA.KeyGen_internal core over
    // the 32-byte xi seed. Installed ASSERT-FATAL like the other cores: once installed,
    // `dregg_pq::MlDsaKey::from_ed25519_seed` mints the NODE IDENTITY (pk, sk) via the verified Lean core
    // and the `fips204` crate leaves the IDENTITY-KEY keygen TCB (and dregg-pq aborts if it were ever asked
    // to expand the identity seed with the crate). The byte<->ring KeyGen refinement forall stays OPEN
    // (KAT-anchored vs the NIST ACVP ML-DSA-65 keyGen vectors, not a refinement proof). An ExportAbsent here
    // means a stale archive without the keygen export.
    let dkg = install_verified_mldsa_keygen_core_real(
        dregg_lean_ffi::mldsa_keygen_real_core_available,
        |w| dregg_lean_ffi::shadow_mldsa_keygen_real(w).ok(),
    );
    assert!(
        matches!(
            dkg,
            MlDsaKeygenCoreRealInstall::Installed | MlDsaKeygenCoreRealInstall::AlreadyInstalled
        ),
        "verified ML-DSA keygen core NOT installed ({dkg:?}) - the fips204 crate would stay the \
         deployed IDENTITY-KEY keygen authority; refusing to serve a build that overstates its TCB"
    );
}

#[cfg(test)]
mod tests {
    use dregg_pq::MlDsaKey;
    use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};

    /// The FIPS 204 `ctx` domain-separation string this surface pins for the
    /// ML-DSA-65 half (the orb JWT-hybrid surface).
    const CTX: &[u8] = b"drorb-jwt-hybrid-v1";

    /// The orb's hybrid verify predicate, copied from `Jwt.hybridVerify`: BOTH the
    /// classical Ed25519 signature AND the post-quantum ML-DSA-65 signature must
    /// verify over the SAME signing input, under the PINNED keys; either half bad
    /// ⇒ reject (fail-closed). This mirrors the proven `Jwt.jwt_hybrid_sound`
    /// (accepts iff both) and the pinning behind `Jwt.jwt_hybrid_no_downgrade`.
    fn hybrid_verify(
        ed_pk: &VerifyingKey,
        mldsa_pk: &[u8],
        signing_input: &[u8],
        ed_sig: &Signature,
        mldsa_sig: &[u8],
    ) -> bool {
        ed_pk.verify(signing_input, ed_sig).is_ok()
            && dregg_pq::ml_dsa_verify(mldsa_pk, CTX, signing_input, mldsa_sig)
    }

    /// THE ROUTING GATE for deployed-weakness #1: prove the Lean-verified core is
    /// the ACTUAL accept/reject authority behind the deployed verify — not merely
    /// that a verify happens to work (the unverified `fips204` fallback also
    /// returns the right answers, which is exactly why a green build proves
    /// nothing here).
    ///
    /// The chain: install the cores as `main` does -> assert dregg-pq reports the
    /// REAL core installed (so `ml_dsa_verify` takes the core branch, not the
    /// crate branch) -> drive a genuine ML-DSA-65 signature and a tampered one
    /// through the SAME `dregg_pq::ml_dsa_verify` the deployed C-ABI seam calls.
    /// With the core installed, those verdicts come from the extracted Lean
    /// `verifyCore`.
    #[test]
    fn verified_core_is_the_deployed_verify_authority() {
        super::install_verified_cores();

        // The OnceLock is now populated: `ml_dsa_verify` routes through the Lean
        // core. Absent this, every assertion below would still pass on the
        // `fips204` crate - which is the whole point of checking it.
        assert!(
            dregg_pq::lean_verify_core_real_installed(),
            "the REAL Lean verify core must be the installed authority"
        );

        let seed = [7u8; 32];
        let mldsa = MlDsaKey::from_ed25519_seed(&seed);
        let pk = mldsa.public_bytes();
        let msg: &[u8] = b"drorb routing proof: the verified core owns this verdict";
        let sig = mldsa.sign(CTX, msg);

        // Genuine signature -> TRUE, through the Lean-verified core.
        assert!(
            dregg_pq::ml_dsa_verify(&pk, CTX, msg, &sig),
            "a genuine ML-DSA-65 signature must verify through the verified core"
        );

        // Tampered signature -> FALSE, through the Lean-verified core.
        let mut bad = sig.clone();
        bad[0] ^= 0xff;
        assert!(
            !dregg_pq::ml_dsa_verify(&pk, CTX, msg, &bad),
            "a tampered ML-DSA-65 signature must be rejected by the verified core"
        );

        // Wrong message -> FALSE (the signature is valid, but not for this input).
        assert!(
            !dregg_pq::ml_dsa_verify(&pk, CTX, b"a different message", &sig),
            "a signature over a different message must be rejected"
        );
    }

    /// THE ROUTING GATE for the SIGN half: prove the Lean-verified REAL sign core is
    /// the ACTUAL PRODUCER of the deployed signature bytes — not merely that signing
    /// works (the unaudited `fips204` crate fallback also produces perfectly valid
    /// signatures, which is exactly why "it signed and it verified" proves nothing).
    ///
    /// Three independent discriminators, none of which the crate path can satisfy:
    ///
    ///  1. `lean_sign_core_real_installed()` — the OnceLock behind `try_sign` holds a
    ///     core, so `try_sign` takes the core branch and never consults `fips204`.
    ///  2. DETERMINISM — the installed core is the `rnd = 0` FIPS 204 deterministic
    ///     variant; the crate fallback is HEDGED from `OsRng`. Signing the same
    ///     (seed, ctx, msg) twice yields byte-identical signatures here. On the crate
    ///     path those two signatures differ with overwhelming probability, so this
    ///     single assertion separates the two producers behaviourally.
    ///  3. The bytes are a genuine ML-DSA-65 signature: full `SIG_LEN`, VERIFIES under
    ///     the pinned key, and a tampered copy is rejected — so discriminator 2 is not
    ///     being satisfied by some degenerate constant.
    ///
    /// Discriminators 1-3 are checked here; the symbol-level confirmation (a gdb
    /// breakpoint on the Lean export `dregg_fips204_sign_real_str` firing while the
    /// `fips204` crate sign symbol never does) is run against THIS test binary.
    #[test]
    fn verified_sign_core_is_the_deployed_sign_authority() {
        super::install_verified_cores();

        assert!(
            dregg_pq::lean_sign_core_real_installed(),
            "the REAL Lean sign core must be the installed producer behind MlDsaKey::try_sign"
        );

        let seed = [0x5au8; 32];
        let key = MlDsaKey::from_ed25519_seed(&seed);
        let pk = key.public_bytes();
        let msg: &[u8] = b"drorb sign routing proof: the verified core produced these bytes";

        let sig_a = key.try_sign(CTX, msg).expect("verified core signs");
        let sig_b = key.try_sign(CTX, msg).expect("verified core signs again");

        assert_eq!(
            sig_a.len(),
            dregg_pq::ML_DSA_SIG_LEN,
            "a full-size ML-DSA-65 signature"
        );
        assert_eq!(
            sig_a, sig_b,
            "DETERMINISTIC (rnd=0) — the Lean core produced these bytes; the hedged fips204 \
             crate fallback would have produced two DIFFERENT signatures"
        );
        assert!(
            dregg_pq::ml_dsa_verify(&pk, CTX, msg, &sig_a),
            "the verified core's signature is a genuine ML-DSA-65 signature (it verifies)"
        );
        let mut bad = sig_a.clone();
        bad[0] ^= 0xff;
        assert!(
            !dregg_pq::ml_dsa_verify(&pk, CTX, msg, &bad),
            "sanity: a tampered copy is rejected (the accept above is not vacuous)"
        );

        println!(
            "SIGN ROUTING: installed={}  deterministic-repeat=MATCH  len={}  verifies=YES  \
             tampered=REJECT  sig[0..8]={:02x?}",
            dregg_pq::lean_sign_core_real_installed(),
            sig_a.len(),
            &sig_a[..8]
        );
    }

    #[test]
    fn hybrid_jwt_verifies_tamper_and_downgrade_fail_closed() {
        // Install the verified cores FIRST, exactly as `main` does. This test drives
        // real ML-DSA sign / ML-KEM ops, and dregg-pq's audit gate ABORTS any process
        // that answers one from the unaudited crate primitive. Installing is the
        // correct way to satisfy that gate — the opt-out env var would make the test
        // pass by forfeiting the very property it is here to exercise.
        super::install_verified_cores();

        // ONE 32-byte seed drives BOTH halves — dregg's `Id = H(ed25519 ‖ ml_dsa)`.
        let seed = [42u8; 32];
        let ed_sk = SigningKey::from_bytes(&seed);
        let ed_pk = ed_sk.verifying_key();
        let mldsa = MlDsaKey::from_ed25519_seed(&seed);
        let mldsa_pk = mldsa.public_bytes(); // the ENROLLED / PINNED PQ public key

        // The JWT signing input ASCII(BASE64URL(header) '.' BASE64URL(payload)).
        let signing_input: &[u8] = b"eyJhbGciOiJIeWJyaWQiLCJraWQiOiJvcmItMSJ9.eyJzdWIiOiJlbWJlciJ9";

        // Sign BOTH halves over the SAME signing input (ed25519 detached; ML-DSA
        // under the pinned ctx).
        let ed_sig = ed_sk.sign(signing_input);
        let mldsa_sig = mldsa.sign(CTX, signing_input);

        // (1) A genuine ed25519 ∧ ML-DSA-65 hybrid token VERIFIES.
        assert!(
            hybrid_verify(&ed_pk, &mldsa_pk, signing_input, &ed_sig, &mldsa_sig),
            "genuine ed25519 ∧ ML-DSA-65 hybrid token must verify"
        );

        // (2) A tampered ML-DSA-65 half FAILS CLOSED — even though the classical
        //     ed25519 half is still perfectly valid (proving BOTH-verify).
        let mut tampered = mldsa_sig.clone();
        tampered[0] ^= 0xff;
        assert!(
            ed_pk.verify(signing_input, &ed_sig).is_ok(),
            "sanity: the ed25519 half is genuinely valid"
        );
        assert!(
            !dregg_pq::ml_dsa_verify(&mldsa_pk, CTX, signing_input, &tampered),
            "sanity: dregg-pq rejects the tampered ML-DSA-65 signature"
        );
        assert!(
            !hybrid_verify(&ed_pk, &mldsa_pk, signing_input, &ed_sig, &tampered),
            "a tampered ML-DSA-65 half must fail the hybrid (fail-closed)"
        );

        // (3) An ed25519-ONLY token against a HYBRID-pinned identity — the ML-DSA
        //     half is absent — is REJECTED (no downgrade to classical-only).
        let no_pq_half: Vec<u8> = Vec::new();
        assert!(
            !hybrid_verify(&ed_pk, &mldsa_pk, signing_input, &ed_sig, &no_pq_half),
            "an ed25519-only token must not admit against a hybrid-pinned key (no downgrade)"
        );

        // (4) A cross-key ML-DSA forgery (attacker's own key over the same input)
        //     against the honest pinned key is REJECTED — the pin, not luck.
        let attacker = MlDsaKey::from_ed25519_seed(&[99u8; 32]);
        let forged = attacker.sign(CTX, signing_input);
        assert!(
            !hybrid_verify(&ed_pk, &mldsa_pk, signing_input, &ed_sig, &forged),
            "a forged ML-DSA-65 half under an unenrolled key must reject"
        );

        // (5) FIPS-204 ctx domain-separation: the genuine sig under a DIFFERENT
        //     ctx does not verify.
        assert!(
            !dregg_pq::ml_dsa_verify(&mldsa_pk, b"other-surface-v1", signing_input, &mldsa_sig),
            "FIPS-204 ctx domain-separation: a wrong ctx rejects"
        );

        println!(
            "HYBRID JWT TEST: genuine=ACCEPT  tampered-mldsa=REJECT  ed25519-only=REJECT  \
             cross-key-forgery=REJECT  wrong-ctx=REJECT"
        );
    }

    /// Exercise the EXACT C-ABI crossing the Lean `Crypto.mlDsaVerify` opaque binds
    /// to (`drorb_pq_ml_dsa_verify`), so the deployed shim entry — not just the
    /// library call — is under test.
    #[test]
    fn shim_entry_accepts_genuine_rejects_tampered() {
        // Install the verified cores FIRST, exactly as `main` does. This test drives
        // real ML-DSA sign / ML-KEM ops, and dregg-pq's audit gate ABORTS any process
        // that answers one from the unaudited crate primitive. Installing is the
        // correct way to satisfy that gate — the opt-out env var would make the test
        // pass by forfeiting the very property it is here to exercise.
        super::install_verified_cores();

        let seed = [7u8; 32];
        let mldsa = MlDsaKey::from_ed25519_seed(&seed);
        let pk = mldsa.public_bytes();
        let msg: &[u8] = b"canonical signing input";
        let sig = mldsa.sign(CTX, msg);
        unsafe {
            assert_eq!(
                super::drorb_pq_ml_dsa_verify(
                    pk.as_ptr(),
                    pk.len(),
                    msg.as_ptr(),
                    msg.len(),
                    sig.as_ptr(),
                    sig.len(),
                    CTX.as_ptr(),
                    CTX.len(),
                ),
                1,
                "shim entry accepts a genuine ML-DSA-65 signature"
            );
            let mut t = sig.clone();
            t[0] ^= 0xff;
            assert_eq!(
                super::drorb_pq_ml_dsa_verify(
                    pk.as_ptr(),
                    pk.len(),
                    msg.as_ptr(),
                    msg.len(),
                    t.as_ptr(),
                    t.len(),
                    CTX.as_ptr(),
                    CTX.len(),
                ),
                0,
                "shim entry rejects a tampered ML-DSA-65 signature (fail-closed)"
            );
        }
    }

    /// **The X-Wing (X25519 + ML-KEM-768) hybrid TLS KEX, my-hand-reproducible.** Runs a full
    /// round-trip using the REAL dregg wire for the ML-KEM half (the C-ABI `drorb_pq_ml_kem_*` the
    /// Lean `Crypto.mlKemEncaps`/`mlKemDecaps` bind to) + x25519-dalek for the classical half + the
    /// SAME concatenation-KDF combiner as `Crypto.Xwing.xwingCombine` (HKDF-SHA256 over
    /// `ss_x25519 ‖ ss_mlkem`, domain "drorb-tls-hybrid-kem-x25519-mlkem768-v1"). Pins: (1) both
    /// sides derive the SAME secret; (2) a tampered ML-KEM ciphertext makes them DIVERGE (implicit
    /// reject) so the handshake fails; (3) a classical-X25519-only secret CANNOT reproduce the
    /// hybrid secret (no downgrade).
    #[test]
    fn xwing_hybrid_kex_roundtrip_tamper_downgrade() {
        // Install the verified cores FIRST, exactly as `main` does. This test drives
        // real ML-DSA sign / ML-KEM ops, and dregg-pq's audit gate ABORTS any process
        // that answers one from the unaudited crate primitive. Installing is the
        // correct way to satisfy that gate — the opt-out env var would make the test
        // pass by forfeiting the very property it is here to exercise.
        super::install_verified_cores();

        use hkdf::Hkdf;
        use sha2::Sha256;
        use x25519_dalek::{PublicKey, StaticSecret};

        const DOMAIN: &[u8] = b"drorb-tls-hybrid-kem-x25519-mlkem768-v1";
        // The orb's concat-KDF combiner, byte-for-byte (Crypto.Xwing.xwingCombine).
        fn xwing_combine(ss_x: &[u8; 32], ss_m: &[u8; 32], transcript: &[u8]) -> [u8; 32] {
            let mut ikm = Vec::with_capacity(64);
            ikm.extend_from_slice(ss_x);
            ikm.extend_from_slice(ss_m); // CONCATENATION, never XOR
            let hk = Hkdf::<Sha256>::new(Some(DOMAIN), &ikm);
            let mut info = Vec::new();
            info.extend_from_slice(DOMAIN);
            info.extend_from_slice(transcript);
            let mut key = [0u8; 32];
            hk.expand(&info, &mut key).expect("hkdf expand");
            key
        }
        // ML-KEM encaps/decaps through the REAL dregg C-ABI wire (the shim entries).
        fn encaps(ek: &[u8]) -> (Vec<u8>, [u8; 32]) {
            let mut out = [0u8; 1120];
            let ok =
                unsafe { super::drorb_pq_ml_kem_encaps(ek.as_ptr(), ek.len(), out.as_mut_ptr()) };
            assert_eq!(ok, 1, "encaps to a valid ek succeeds");
            let mut ss = [0u8; 32];
            ss.copy_from_slice(&out[1088..1120]);
            (out[0..1088].to_vec(), ss)
        }
        fn decaps(dk: &[u8], ct: &[u8]) -> Option<[u8; 32]> {
            let mut out = [0u8; 32];
            let ok = unsafe {
                super::drorb_pq_ml_kem_decaps(
                    dk.as_ptr(),
                    dk.len(),
                    ct.as_ptr(),
                    ct.len(),
                    out.as_mut_ptr(),
                )
            };
            if ok == 1 { Some(out) } else { None }
        }

        // --- CLIENT (KEM responder): X25519 ephemeral + ML-KEM-768 keypair. ---
        let (ek, dk) = dregg_pq::ml_kem768_keygen();
        assert_eq!(ek.len(), 1184);
        assert_eq!(dk.len(), 2400);
        let client_x_sk = StaticSecret::from([7u8; 32]);
        let client_x_pub = PublicKey::from(&client_x_sk).to_bytes();

        // --- SERVER (KEM initiator = the orb's hybridServerKex): X25519 DH + ML-KEM encaps. ---
        let server_x_sk = StaticSecret::from([9u8; 32]);
        let server_x_pub = PublicKey::from(&server_x_sk).to_bytes();
        let ss_x_server = server_x_sk
            .diffie_hellman(&PublicKey::from(client_x_pub))
            .to_bytes();
        let (ct, ss_m_server) = encaps(&ek);
        assert_eq!(ct.len(), 1088);
        let transcript = [&client_x_pub[..], &ek[..], &server_x_pub[..], &ct[..]].concat();
        let server_dhe = xwing_combine(&ss_x_server, &ss_m_server, &transcript);

        // --- CLIENT finish: X25519 DH against the server share + ML-KEM decaps. ---
        let ss_x_client = client_x_sk
            .diffie_hellman(&PublicKey::from(server_x_pub))
            .to_bytes();
        let ss_m_client = decaps(&dk, &ct).expect("decaps of the honest ciphertext");
        let client_dhe = xwing_combine(&ss_x_client, &ss_m_client, &transcript);

        // (1) ROUND-TRIP: both sides derive the SAME X-Wing shared secret.
        assert_eq!(ss_x_server, ss_x_client, "X25519 DH agrees on both sides");
        assert_eq!(
            ss_m_server, ss_m_client,
            "ML-KEM shared secret round-trips (honest ct)"
        );
        assert_eq!(
            server_dhe, client_dhe,
            "X-Wing hybrid session key matches on both sides"
        );

        // (2) TAMPER the ML-KEM ciphertext: the client implicit-rejects to a DIFFERENT secret,
        //     so the derived session keys DIVERGE -> the handshake Finished check fails.
        let mut ct_bad = ct.clone();
        ct_bad[500] ^= 0xff;
        let transcript_bad = [&client_x_pub[..], &ek[..], &server_x_pub[..], &ct_bad[..]].concat();
        let ss_m_client_bad =
            decaps(&dk, &ct_bad).expect("decaps never fails on a well-formed ct (implicit reject)");
        assert_ne!(
            ss_m_server, ss_m_client_bad,
            "a tampered ML-KEM ct implicit-rejects to a DIFFERENT secret"
        );
        let client_dhe_bad = xwing_combine(&ss_x_client, &ss_m_client_bad, &transcript_bad);
        assert_ne!(
            server_dhe, client_dhe_bad,
            "tampered ML-KEM ct -> hybrid keys diverge -> handshake fails"
        );

        // Malformed ct / dk / ek lengths fail closed.
        assert_eq!(
            decaps(&dk, &ct[..10]),
            None,
            "short ciphertext fails closed"
        );
        assert_eq!(
            decaps(&dk[..10], &ct),
            None,
            "short decaps key fails closed"
        );
        {
            let mut out = [0u8; 1120];
            let ok =
                unsafe { super::drorb_pq_ml_kem_encaps(ek[..10].as_ptr(), 10, out.as_mut_ptr()) };
            assert_eq!(ok, 0, "encaps to a malformed ek fails closed");
        }

        // (3) DOWNGRADE: a classical-X25519-ONLY peer (no ML-KEM half) can NEVER reproduce the
        //     hybrid secret -> substituting X25519-only against a Hybrid-pinned peer FAILS.
        assert_ne!(
            server_dhe, ss_x_server,
            "the hybrid key is NOT the bare X25519 secret (it binds the ML-KEM half)"
        );
        let classical_only = xwing_combine(&ss_x_client, &[0u8; 32], &transcript);
        assert_ne!(
            server_dhe, classical_only,
            "a classical-only (zero ML-KEM) key cannot substitute for the hybrid (no downgrade)"
        );

        println!(
            "XWING HYBRID KEX TEST: roundtrip=MATCH  tampered-mlkem=DIVERGE  \
             malformed=FAIL-CLOSED  downgrade-x25519-only=REJECT"
        );
    }
}
