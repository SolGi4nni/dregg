//! Host witness for the executor PD's REAL elliptic-curve crypto floor — §1
//! ed25519, §3 Pedersen (Ristretto255), §7 ChaCha20-Poly1305 AEAD.
//!
//! Includes the SAME three floor modules the staticlib cross-compiles
//! (`crypto-floor/src/{ed25519,pedersen,aead}.rs`, via `#[path]`) and runs their
//! anti-ghost teeth natively on the host — a runnable proof that the wiring bites
//! on a box with no user-mode qemu-aarch64. The verify/commit/seal paths here are
//! byte-for-byte the paths the seL4 executor PD's crypto floor runs (the modules
//! call the identical in-workspace crates).

// The three floor modules are self-contained (they call ed25519-dalek /
// curve25519-dalek / chacha20poly1305 directly — no dependence on the floor's
// no_std field/galloc), so they compile verbatim in this std crate.
#[path = "../../dregg-pd/executor-pd/crypto-floor/src/ed25519.rs"]
pub mod ed25519;
#[path = "../../dregg-pd/executor-pd/crypto-floor/src/pedersen.rs"]
pub mod pedersen;
#[path = "../../dregg-pd/executor-pd/crypto-floor/src/aead.rs"]
pub mod aead;

// ---- §1 ed25519 strict verify -------------------------------------------------

/// Mirror of `dreggcf_ed25519_selftest`: ACCEPT a genuine sig; REJECT a forged
/// sig / a wrong message / a wrong key. Returns a 4-bit mask (0xF = all bite).
pub fn ed25519_selftest() -> u8 {
    use ed25519_dalek::{Signer, SigningKey};
    let sk = SigningKey::from_bytes(&[7u8; 32]);
    let pk = sk.verifying_key().to_bytes();
    let msg = b"dregg-firmament executor turn v1";
    let sig = sk.sign(msg).to_bytes();

    let mut mask = 0u8;
    let ok = unsafe { ed25519::verify(pk.as_ptr(), msg.as_ptr(), msg.len(), sig.as_ptr()) };
    if ok == 1 {
        mask |= 0x1;
    }
    let mut forged = sig;
    forged[40] ^= 0x01;
    if unsafe { ed25519::verify(pk.as_ptr(), msg.as_ptr(), msg.len(), forged.as_ptr()) } == 0 {
        mask |= 0x2;
    }
    let other = b"dregg-firmament executor turn v2";
    if unsafe { ed25519::verify(pk.as_ptr(), other.as_ptr(), other.len(), sig.as_ptr()) } == 0 {
        mask |= 0x4;
    }
    let pk2 = SigningKey::from_bytes(&[9u8; 32]).verifying_key().to_bytes();
    if unsafe { ed25519::verify(pk2.as_ptr(), msg.as_ptr(), msg.len(), sig.as_ptr()) } == 0 {
        mask |= 0x8;
    }
    mask
}

// ---- §3 Pedersen commitment (Ristretto255) -----------------------------------

/// Mirror of `dreggcf_pedersen_selftest`: opening verifies; wrong value/blinding
/// fail; the homomorphism `commit(a,r1)+commit(b,r2) == commit(a+b,r1+r2)` holds.
/// Returns a 4-bit mask (0xF = all bite).
pub fn pedersen_selftest() -> u8 {
    use curve25519_dalek::ristretto::CompressedRistretto;
    use curve25519_dalek::scalar::Scalar;

    let value: u64 = 1_234_567;
    let mut blinding = [0u8; 32];
    blinding[0] = 0x9A;
    blinding[31] = 0x42;
    let mut commit = [0u8; 32];
    unsafe { pedersen::commit(value, blinding.as_ptr(), commit.as_mut_ptr()) };

    let mut mask = 0u8;
    if unsafe { pedersen::verify_opening(value, blinding.as_ptr(), commit.as_ptr()) } == 1 {
        mask |= 0x1;
    }
    if unsafe { pedersen::verify_opening(value + 1, blinding.as_ptr(), commit.as_ptr()) } == 0 {
        mask |= 0x2;
    }
    let mut other_bl = blinding;
    other_bl[0] ^= 0xFF;
    if unsafe { pedersen::verify_opening(value, other_bl.as_ptr(), commit.as_ptr()) } == 0 {
        mask |= 0x4;
    }
    // homomorphism
    let (a, b): (u64, u64) = (100, 250);
    let mut r1 = [0u8; 32];
    r1[0] = 0x11;
    let mut r2 = [0u8; 32];
    r2[0] = 0x22;
    let mut ca = [0u8; 32];
    let mut cb = [0u8; 32];
    unsafe {
        pedersen::commit(a, r1.as_ptr(), ca.as_mut_ptr());
        pedersen::commit(b, r2.as_ptr(), cb.as_mut_ptr());
    }
    let r_sum = (Scalar::from_bytes_mod_order(r1) + Scalar::from_bytes_mod_order(r2)).to_bytes();
    let mut c_sum = [0u8; 32];
    unsafe { pedersen::commit(a + b, r_sum.as_ptr(), c_sum.as_mut_ptr()) };
    if let (Some(pa), Some(pb), Some(psum)) = (
        CompressedRistretto(ca).decompress(),
        CompressedRistretto(cb).decompress(),
        CompressedRistretto(c_sum).decompress(),
    ) {
        if (pa + pb) == psum {
            mask |= 0x8;
        }
    }
    mask
}

/// THE RECONCILIATION TOOTH: the floor's Pedersen commitment is byte-IDENTICAL to
/// `cell::value_commitment::commit_bytes` — the commitment the executor's
/// conservation check consumes and the circuit binds. We recompute that exact
/// reference here (the SAME generators, scalar, compress) and assert byte
/// equality with the floor's `pedersen::commit`. If these ever diverge, the
/// on-device commitment would bind bytes the host never produces.
pub fn pedersen_matches_cell_commit_bytes() -> bool {
    use curve25519_dalek::ristretto::RistrettoPoint;
    use curve25519_dalek::scalar::Scalar;

    // VERBATIM cell::value_commitment::{hash_to_generator,value_generator,
    // randomness_generator,commit_bytes}.
    fn hash_to_generator(domain: &[u8]) -> RistrettoPoint {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-pedersen generator v1");
        hasher.update(domain);
        let mut xof = hasher.finalize_xof();
        let mut uniform = [0u8; 64];
        xof.fill(&mut uniform);
        RistrettoPoint::from_uniform_bytes(&uniform)
    }
    fn reference_commit_bytes(value: u64, blinding: &[u8; 32]) -> [u8; 32] {
        let v = Scalar::from(value);
        let r = Scalar::from_bytes_mod_order(*blinding);
        let point =
            v * hash_to_generator(b"dregg-value-generator") + r * hash_to_generator(b"dregg-randomness-generator");
        point.compress().to_bytes()
    }

    // a spread of vectors (incl. value 0, large value, and an arbitrary blinding).
    let vectors: [(u64, [u8; 32]); 3] = [
        (0, [0u8; 32]),
        (1_234_567, {
            let mut b = [0u8; 32];
            b[0] = 0x9A;
            b[31] = 0x42;
            b
        }),
        (u64::MAX, [0xABu8; 32]),
    ];
    for (value, blinding) in vectors {
        let reference = reference_commit_bytes(value, &blinding);
        let mut got = [0u8; 32];
        unsafe { pedersen::commit(value, blinding.as_ptr(), got.as_mut_ptr()) };
        if got != reference {
            return false;
        }
    }
    true
}

// ---- §7 ChaCha20-Poly1305 AEAD ------------------------------------------------

/// Mirror of `dreggcf_chacha_selftest`: seal->open round-trips; a tampered
/// ciphertext byte, a wrong key, and a tampered tag byte each fail the tag.
/// Returns a 4-bit mask (0xF = all bite).
pub fn aead_selftest() -> u8 {
    let key = [0x42u8; 32];
    let nonce = [0x07u8; 12];
    let pt = b"note-opening: value=1234567 asset=7 blinding=...";
    let mut boxed = [0u8; 128];
    let n = unsafe {
        aead::seal(key.as_ptr(), nonce.as_ptr(), pt.as_ptr(), pt.len(), boxed.as_mut_ptr(), boxed.len())
    };
    if n < 0 {
        return 0;
    }
    let n = n as usize;
    let mut out = [0u8; 128];
    let mut mask = 0u8;
    let m = unsafe {
        aead::open(key.as_ptr(), nonce.as_ptr(), boxed.as_ptr(), n, out.as_mut_ptr(), out.len())
    };
    if m == pt.len() as isize && out[..pt.len()] == pt[..] {
        mask |= 0x1;
    }
    let mut tampered = boxed;
    tampered[n / 2] ^= 0x01;
    if unsafe { aead::open(key.as_ptr(), nonce.as_ptr(), tampered.as_ptr(), n, out.as_mut_ptr(), out.len()) } < 0 {
        mask |= 0x2;
    }
    let wrong_key = [0x43u8; 32];
    if unsafe { aead::open(wrong_key.as_ptr(), nonce.as_ptr(), boxed.as_ptr(), n, out.as_mut_ptr(), out.len()) } < 0 {
        mask |= 0x4;
    }
    let mut tag_tampered = boxed;
    tag_tampered[n - 1] ^= 0x80;
    if unsafe { aead::open(key.as_ptr(), nonce.as_ptr(), tag_tampered.as_ptr(), n, out.as_mut_ptr(), out.len()) } < 0 {
        mask |= 0x8;
    }
    mask
}

/// THE INTEROP TOOTH: the floor's AEAD opens a box sealed by the SAME crate API
/// the committed-note ECIES uses (`cell::note_encryption::encrypt`'s
/// `ChaCha20Poly1305::new(key).encrypt(nonce, pt)`). We seal with that exact call
/// here and assert the floor's `aead::open` recovers the plaintext — the on-device
/// note-open path against a host-sealed note.
pub fn aead_opens_cell_sealed_box() -> bool {
    use ::aead::{Aead, KeyInit};
    use chacha20poly1305::{ChaCha20Poly1305, Key, Nonce};

    let key = [0x55u8; 32];
    let nonce = [0x21u8; 12];
    let pt = b"value=42 asset=7 blinding=deadbeef";

    // host seal, EXACTLY cell::note_encryption::encrypt's primitive call.
    let cipher = ChaCha20Poly1305::new(Key::from_slice(&key));
    let boxed = cipher
        .encrypt(Nonce::from_slice(&nonce), pt.as_ref())
        .expect("seal");

    // floor open.
    let mut out = [0u8; 128];
    let m = unsafe {
        aead::open(key.as_ptr(), nonce.as_ptr(), boxed.as_ptr(), boxed.len(), out.as_mut_ptr(), out.len())
    };
    m == pt.len() as isize && out[..pt.len()] == pt[..]
}

/// Drive all three primitives + the two interop teeth, printing a human report.
/// Returns `true` iff every tooth bites.
pub fn run_report() -> bool {
    println!("\n== executor-PD REAL elliptic-curve crypto floor — host witness ==");

    let e = ed25519_selftest();
    println!(
        "  §1 ed25519 verify_strict       -> 0x{e:x} (0xF: ACCEPT genuine, REJECT forged/wrong-msg/wrong-key)"
    );

    let p = pedersen_selftest();
    println!(
        "  §3 pedersen (Ristretto255)     -> 0x{p:x} (0xF: open verifies, wrong value/blinding fail, homomorphic)"
    );
    let p_match = pedersen_matches_cell_commit_bytes();
    println!(
        "  §3 == cell::commit_bytes       -> {} (byte-identical to the host/circuit commitment)",
        if p_match { "MATCH" } else { "DIVERGED — UNSOUND!" }
    );

    let a = aead_selftest();
    println!(
        "  §7 chacha20poly1305 AEAD       -> 0x{a:x} (0xF: round-trip, tampered-ct/wrong-key/tampered-tag fail)"
    );
    let a_interop = aead_opens_cell_sealed_box();
    println!(
        "  §7 opens cell-sealed note      -> {} (the on-device note-open path)",
        if a_interop { "OK" } else { "FAILED" }
    );

    let all = e == 0xF && p == 0xF && p_match && a == 0xF && a_interop;
    if all {
        println!("== all elliptic-curve teeth bite — ed25519 + Pedersen + AEAD are REAL ( ◕‿◕ ) ==");
    } else {
        println!("== SOME elliptic-curve teeth FAILED ==");
    }
    all
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ed25519_teeth_all_bite() {
        assert_eq!(ed25519_selftest(), 0xF);
    }

    #[test]
    fn pedersen_teeth_all_bite() {
        assert_eq!(pedersen_selftest(), 0xF);
    }

    #[test]
    fn pedersen_byte_identical_to_cell_commit_bytes() {
        assert!(
            pedersen_matches_cell_commit_bytes(),
            "the floor's Pedersen must equal cell::value_commitment::commit_bytes"
        );
    }

    #[test]
    fn aead_teeth_all_bite() {
        assert_eq!(aead_selftest(), 0xF);
    }

    #[test]
    fn aead_opens_a_cell_sealed_box() {
        assert!(aead_opens_cell_sealed_box());
    }
}
