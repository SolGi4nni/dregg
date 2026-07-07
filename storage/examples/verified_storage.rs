//! `verified_storage` — a runnable, end-to-end demo of dregg's **formally-verified
//! decentralized storage**, tied at every step to the Lean theorem that proves it sound.
//!
//! Run it:  `cargo run -p dregg-storage --example verified_storage`
//!
//! Unlike Filecoin / Arweave / Storj ("trust the incentives"), every step below is
//! machine-checked in Lean (`metatheory/Dregg2/Storage/`), `#assert_axioms`-clean, and the
//! ONLY cryptographic assumption is that Poseidon2 is collision-resistant.

use dregg_storage::bucket_commitment::{BucketContent, Object, content_root, open, verify_opening};
use dregg_storage::erasure::ErasureEncoder;

fn rule(title: &str) {
    println!(
        "\n\x1b[1;36m── {title} {}\x1b[0m",
        "─".repeat(60usize.saturating_sub(title.len()))
    );
}
fn proof(theorem: &str) {
    println!("     \x1b[2m↳ proven: Dregg2/Storage/{theorem}\x1b[0m");
}

fn main() {
    println!("\x1b[1;35m╔══════════════════════════════════════════════════════════════╗");
    println!("║   dregg · FORMALLY-VERIFIED DECENTRALIZED STORAGE (live demo) ║");
    println!("╚══════════════════════════════════════════════════════════════╝\x1b[0m");

    // The blob a user wants stored, decentralized + verifiable.
    let blob = b"the quick brown fox settles a half-open escrow and files a receipt".to_vec();
    println!(
        "\n\x1b[1mblob:\x1b[0m {:?}  ({} bytes)",
        String::from_utf8_lossy(&blob),
        blob.len()
    );

    // ── 1. COMMIT — one Poseidon2 content root binds the blob. ─────────────
    rule("1. COMMIT");
    let mut bucket = BucketContent::new();
    bucket.insert("fox.txt".into(), Object::new("text/plain", blob.clone()));
    let root = content_root(&bucket);
    println!("     content root: \x1b[33m{root}\x1b[0m");
    println!("     a single felt binds the whole object set — no ghost object hides under it.");
    proof("BucketCommitment.lean :: contentRoot_injective");

    // ── 2. ERASURE-CODE — spread across providers, any k-of-n reconstruct. ──
    rule("2. ERASURE-CODE (Reed-Solomon)");
    let enc = ErasureEncoder::new(32, 3); // 32-byte shards, 3x expansion
    let shards = enc.encode(&blob);
    let n_total = shards.len();
    let n_data = shards.iter().filter(|s| !s.is_parity).count();
    println!(
        "     encoded into \x1b[1m{n_total}\x1b[0m shards ({n_data} data + {} parity)",
        n_total - n_data
    );
    println!(
        "     any \x1b[1m{n_data}\x1b[0m of the {n_total} suffice — true k-of-n, spread across providers."
    );
    proof("Erasure.lean :: rs_decode_correct  (k-of-n reconstruction)");

    // ── 3. PROVIDERS GO DARK — lose everything but k shards. ───────────────
    rule("3. PROVIDER CHURN");
    let survivors: Vec<_> = shards.iter().rev().take(n_data).cloned().collect();
    println!(
        "     \x1b[31m{} providers went dark\x1b[0m — only {} shards left (and mostly parity!).",
        n_total - survivors.len(),
        survivors.len()
    );

    // ── 4. RECONSTRUCT — from whatever survived. ───────────────────────────
    rule("4. RECONSTRUCT");
    let recovered = enc
        .reconstruct(&survivors, blob.len())
        .expect("k-of-n reconstruction");
    assert_eq!(recovered, blob, "reconstruction must equal the original");
    println!(
        "     recovered \x1b[32m{} bytes — byte-identical to the original ✓\x1b[0m",
        recovered.len()
    );
    println!(
        "     the decoder CANNOT be tricked into a wrong blob (distinct messages can't share k shards)."
    );
    proof("Erasure.lean :: rs_decode_correct + no_wrong_reconstruction");

    // ── 5. TRUSTLESS READ — verify a served object against the root, no trust. ──
    rule("5. TRUSTLESS READ");
    let opening = open(&bucket, "fox.txt").expect("open the committed object");
    let ok = verify_opening(&opening);
    println!(
        "     an untrusted gateway served the object; the client re-witnessed it against the root: \x1b[32m{ok}\x1b[0m"
    );
    println!("     no trust in the provider — the bytes bind to the committed root or they don't.");
    proof("BucketCommitment.lean :: read_sound  (·= Retrievability.por_sound)");

    // ── 6. FORGERY — a provider swaps in different bytes under the genuine root. ──
    rule("6. FORGERY REFUSED");
    let mut forged = opening.clone();
    forged.object = Object::new(
        "text/plain",
        b"the quick brown fox drains the escrow to me".to_vec(),
    );
    let forged_ok = verify_opening(&forged);
    println!(
        "     a malicious provider served \x1b[31mDIFFERENT bytes\x1b[0m under the genuine root..."
    );
    println!(
        "     verify: \x1b[1;{}\x1b[0m  {}",
        if forged_ok {
            "31mACCEPTED (BUG!)"
        } else {
            "32mREFUSED 🛡"
        },
        if forged_ok {
            ""
        } else {
            "— the forged bytes don't reproduce the committed leaf."
        }
    );
    assert!(!forged_ok, "a forged object must be refused");
    proof("Retrievability.lean :: por_refuses_substitution");

    // ── the point. ─────────────────────────────────────────────────────────
    println!("\n\x1b[1;35m╔══════════════════════════════════════════════════════════════╗\x1b[0m");
    println!("\x1b[1m  Every step above is a THEOREM, not a test.\x1b[0m");
    println!("  6 machine-checked Lean constructions in metatheory/Dregg2/Storage/,");
    println!("  #assert_axioms-clean — sole assumption: Poseidon2 collision-resistance.");
    println!(
        "  commitment · erasure · fountain · proof-of-retrievability · availability · market."
    );
    println!("\x1b[1;35m╚══════════════════════════════════════════════════════════════╝\x1b[0m");
}
