//! CREDENTIAL COST AT THE ML-DSA BOUNDARY — an explicit measurement, not an inference.
//!
//! `#[ignore]`d, because it is a stopwatch rather than a gate. Run it deliberately:
//!
//! ```text
//! cargo test -p dregg-auth --test pq_cost_probe -- --ignored --nocapture
//! ```
//!
//! The quantity this work moves is the number of ML-DSA-65 KEYGENS per operation:
//!
//! | operation                | keygens before | after |
//! |--------------------------|----------------|-------|
//! | `RootKey::mint`          | 2              | 1     |
//! | `Credential::attenuate`  | 2              | 1     |
//! | `verify_hybrid`, minted  | 1              | 0     |
//! | `verify_hybrid`, decoded | 1              | 1 then 0 |
//!
//! `mint` and `attenuate` keep one because each MINTS A NEW TAIL IDENTITY, whose
//! key genuinely does not exist yet; that key is then installed as the new
//! credential's memo rather than dropped.
//!
//! ## ⚠ WHAT THIS PROBE CAN AND CANNOT TELL YOU
//!
//! `dregg-auth` does not depend on `dregg-lean-ffi`, so this process CANNOT
//! install the Lean-verified cores: it times `dregg-pq`'s `fips204` fallback,
//! which needs `DREGG_ALLOW_UNAUDITED_PQ=1` or the audit gate aborts.
//!
//! **On that build the keygen is ~0.5 ms, not 174–227 ms, so it does NOT dominate
//! and the keygen count is NOT readable off the ratios.** Measured 2026-07-25 on
//! persvati: keygen 0.5, mint 6.5, attenuate 12.3 — the bulk there is
//! `getrandom` for the fresh ed25519 tail key, the hedged signature, and debug
//! codegen. An earlier version of this header claimed the ratio revealed the
//! count; running it refuted that, and the claim is retracted rather than
//! quietly dropped.
//!
//! So: read the COUNTS from the table above (they are structural, and pinned by
//! `Arc::ptr_eq` in `credential::chain::ml_dsa_memo_tests`), and price them with
//! the independently measured deployed keygen — a C driver against
//! `libdregg_lean.a` at 174–227 ms. One removed keygen is one 174–227 ms saving
//! on a build with the verified cores installed. What this probe measures on its
//! own terms is the DIRECTION (memoised paths are cheaper than un-memoised ones,
//! and refusing a stranger is cheaper than verifying anyone) and the fact that
//! nothing here regressed.

use std::time::Instant;

use dregg_auth::credential::{Caveat, Context, Credential, Pred, RootKey};

fn read_caveat() -> Caveat {
    Caveat::FirstParty(Pred::AttrEq {
        key: "tool".into(),
        value: "read".into(),
    })
}

fn ok_ctx() -> Context {
    Context::new().at(10).attr("tool", "read")
}

fn ms<T>(label: &str, reps: usize, mut f: impl FnMut(usize) -> T) {
    let start = Instant::now();
    for i in 0..reps {
        std::hint::black_box(f(i));
    }
    let each = start.elapsed().as_secs_f64() * 1000.0 / reps as f64;
    println!("{label:<44} {each:9.1} ms");
}

#[test]
#[ignore = "a stopwatch, not a gate — run with --ignored"]
fn credential_pq_cost() {
    // Warm: the first ML-DSA call in a process pays module init and first-touch
    // paging that no later call pays.
    let _ = dregg_pq::ml_dsa_public_from_seed(&[0x01; 32]);

    ms("ML-DSA-65 keygen (the unit)", 3, |i| {
        dregg_pq::ml_dsa_public_from_seed(&[0x10 + i as u8; 32])
    });

    ms("RootKey::mint (1 keygen: the new tail)", 3, |i| {
        RootKey::from_seed([0x20 + i as u8; 32]).mint([read_caveat()])
    });

    // A root that mints repeatedly pays for its OWN key once, ever.
    let root = RootKey::from_seed([0x30; 32]);
    let _ = root.public_hybrid();
    ms("  …same root, 2nd mint onward", 3, |_| {
        root.mint([read_caveat()])
    });

    ms("Credential::attenuate (1 keygen: the new tail)", 3, |_| {
        root.mint([read_caveat()]).attenuate([read_caveat()])
    });

    let enrolled = root.public_hybrid();
    let minted = root.mint([read_caveat()]).attenuate([read_caveat()]);
    ms("verify_hybrid, credential minted here", 3, |_| {
        minted.verify_hybrid(&enrolled, &ok_ctx())
    });

    let wire = minted.encode();
    ms("verify_hybrid, fresh decode each time", 3, |_| {
        Credential::decode(&wire)
            .expect("decode")
            .verify_hybrid(&enrolled, &ok_ctx())
    });

    let decoded = Credential::decode(&wire).expect("decode");
    let _ = decoded.verify_hybrid(&enrolled, &ok_ctx());
    ms("  …same decoded credential, 2nd verify on", 3, |_| {
        decoded.verify_hybrid(&enrolled, &ok_ctx())
    });

    // What a stranger costs a verifier: the whole point of the gate reorder.
    let stranger = RootKey::from_seed([0x40; 32]);
    let forged = stranger.mint([read_caveat()]).attenuate([read_caveat()]);
    ms("REFUSING a stranger's chain (attacker cost)", 3, |_| {
        forged.verify_hybrid(&enrolled, &ok_ctx())
    });
}
