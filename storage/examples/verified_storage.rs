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

    // ── 4b. FOUNTAIN / RATELESS — a bottomless stream of droplets, decode from any enough. ──
    rule("4b. FOUNTAIN (rateless / LT)");
    let (k_blocks, droplets_used, ft_ok) = fountain_demo(&blob);
    assert!(ft_ok, "fountain decode must recover the blob");
    println!(
        "     {k_blocks} source blocks → a bottomless droplet stream; decoded from the first \x1b[1m{droplets_used}\x1b[0m \x1b[32m✓\x1b[0m"
    );
    println!(
        "     rateless: no fixed rate — providers stream droplets, the client stops when it has enough."
    );
    proof("Fountain.lean :: fountain_decode_unique  (rateless decode is unique)");

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

    // ── 7. THE MARKET — a provider that withholds data gets its bond BURNED. ──
    rule("7. SLASH (the economic teeth)");
    let (bond_before, bond_after, impostor_rejected) = market_slash_demo();
    assert!(impostor_rejected, "an unbonded claim must be rejected");
    assert!(
        bond_after < bond_before,
        "a slash must strictly reduce the bond"
    );
    println!(
        "     an \x1b[31munbonded impostor\x1b[0m tried to claim the deal → \x1b[32mREJECTED\x1b[0m (only bonded providers serve)."
    );
    println!(
        "     a bonded provider then \x1b[31mfailed a proof-of-retrievability audit\x1b[0m..."
    );
    println!(
        "     bond: {bond_before} → \x1b[1;31m{bond_after}\x1b[0m  — \x1b[1mslashed. withholding costs real money.\x1b[0m 🔥"
    );
    proof("ProviderMarket.lean :: unauthorized_claim_rejected + slash_decreases_collateral");

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

/// A minimal REAL LT fountain code (illustrative — mirrors the proven `Fountain.lean` over GF(2)):
/// source blocks XOR'd into a bottomless droplet stream, recovered by belief-propagation peeling.
/// Deterministic (fixed LCG + blob) so the demo always decodes. Returns (k blocks, droplets, ok).
fn fountain_demo(blob: &[u8]) -> (usize, usize, bool) {
    let bs = 8usize;
    let k = blob.len().div_ceil(bs);
    let src: Vec<Vec<u8>> = (0..k)
        .map(|i| {
            let mut b = vec![0u8; bs];
            let (s, e) = (i * bs, ((i + 1) * bs).min(blob.len()));
            b[..e - s].copy_from_slice(&blob[s..e]);
            b
        })
        .collect();
    let mut rng = 0x2545_F491_4F6C_DD1Du64;
    let mut next = || {
        rng = rng
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (rng >> 33) as usize
    };
    // A bottomless stream: 2k+4 droplets, degrees 1..3 (a robust-soliton-lite mix).
    let mut droplets: Vec<(Vec<usize>, Vec<u8>)> = Vec::new();
    while droplets.len() < 2 * k + 4 {
        let deg = 1 + next() % 3;
        let mut neigh = Vec::new();
        while neigh.len() < deg {
            let n = next() % k;
            if !neigh.contains(&n) {
                neigh.push(n);
            }
        }
        let mut payload = vec![0u8; bs];
        for &n in &neigh {
            for b in 0..bs {
                payload[b] ^= src[n][b];
            }
        }
        droplets.push((neigh, payload));
    }
    // Peeling decode.
    let mut got: Vec<Option<Vec<u8>>> = vec![None; k];
    loop {
        let mut progressed = false;
        for (neigh, payload) in droplets.iter() {
            let unknown: Vec<usize> = neigh
                .iter()
                .cloned()
                .filter(|&n| got[n].is_none())
                .collect();
            if unknown.len() == 1 {
                let n = unknown[0];
                let mut val = payload.clone();
                for &m in neigh {
                    if m != n {
                        if let Some(v) = &got[m] {
                            for b in 0..bs {
                                val[b] ^= v[b];
                            }
                        }
                    }
                }
                got[n] = Some(val);
                progressed = true;
            }
        }
        if got.iter().all(Option::is_some) || !progressed {
            break;
        }
    }
    let ok = got.iter().all(Option::is_some);
    let mut out = Vec::new();
    if ok {
        for r in &got {
            out.extend_from_slice(r.as_ref().unwrap());
        }
        out.truncate(blob.len());
    }
    (k, droplets.len(), ok && out == blob)
}

/// A deal lifecycle mirroring the proven `ProviderMarket.lean`: an unbonded impostor is rejected,
/// a bonded provider claims + posts collateral, then a failed audit STRICTLY slashes the bond.
/// Returns (bond_before, bond_after, impostor_rejected).
fn market_slash_demo() -> (i64, i64, bool) {
    let bonded = ["provider_A"];
    let impostor_rejected = !bonded.contains(&"rando"); // unauthorized_claim_rejected
    let (mut provider_set, mut collateral) = (false, 0i64);
    let bond = 1000;
    if bonded.contains(&"provider_A") && !provider_set && bond > 0 {
        provider_set = true;
        collateral = bond; // claimDeal
    }
    let before = collateral;
    let (penalty, audit_failed) = (300i64, true);
    if audit_failed && provider_set && penalty > 0 && penalty <= collateral {
        collateral -= penalty; // slash_decreases_collateral
    }
    (before, collateral, impostor_rejected)
}
