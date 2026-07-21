//! ─────────────────────────────────────────────────────────────────────────────
//! FROZEN PUBLICATION SNAPSHOT — DO NOT HAND-EDIT — NOT AUTHORITATIVE.
//!
//! This file is a snapshot cut from the drorb dataplane crate for the public
//! dregg repo ("orb + orb-compiler: fresh cut", 2026-07-11, breadstuffs commit
//! 62a3abb6b). The LIVE, AUTHORITATIVE source is:
//!
//!     drorb/crates/dataplane/src/pq.rs
//!
//! Changes belong UPSTREAM in drorb, then flow here via a re-cut. Editing this
//! copy by hand re-introduces exactly the drift this header documents.
//!
//! STATUS (as of 2026-07-20): STALE and CRATE-AUTHORITATIVE.
//!   • This cut LACKS `install_verified_cores()` (the verify / encaps / decaps /
//!     sign verified-core installs + fail-loud assert posture) that drorb's cut
//!     carries. Its `main.rs` never installs the Lean-verified cores.
//!   • Consequence: absent the installs, `dregg_pq` keeps its UNVERIFIED
//!     `fips204` / `ml-kem` crate fallbacks as the deployed PQ authority. Under
//!     dregg-pq's Gate-2 audit refusal, a binary built from this cut would ABORT
//!     on the first PQ op — so it is crate-authoritative, not verified-core.
//!   • It ALSO CANNOT BUILD IN PLACE: the `dregg-pq` path dep resolves to a
//!     nonexistent `breadstuffs/breadstuffs/dregg-pq` (the path is written for
//!     drorb's tree depth, not this cut's), and there is no `dregg-lean-ffi`
//!     dep, so the verified-core installs cannot be linked here even if added.
//!     Demonstrated: `cargo metadata` fails to load the manifest.
//!
//! THE REAL FIX is a SCRIPTED re-cut (drorb -> orb) that rewrites the dep paths
//! for this tree's depth, adds the `dregg-lean-ffi` dep, and carries the current
//! `install_verified_cores()` + `main.rs` install call. Until that re-cut lands,
//! treat drorb as authoritative and do not build/deploy from this cut.
//! ─────────────────────────────────────────────────────────────────────────────
//!
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

    #[test]
    fn hybrid_jwt_verifies_tamper_and_downgrade_fail_closed() {
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
