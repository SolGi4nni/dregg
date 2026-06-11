//! # Differential: Lean `Authority.CaveatChain` (FIRST-PARTY chain)  ⟺  the REAL macaroon engine.
//!
//! This is the Rust side of the differential for the FIRST-PARTY half of
//! `metatheory/Dregg2/Authority/CaveatChain.lean` — the faithful executable Lean model of the macaroon
//! as a real HMAC-authenticated append-only caveat chain (`Macaroon::{new, add_first_party, verify}`,
//! `macaroon.rs:118-262`). Its companion `macaroon/src/discharge_diff.rs` pins the THIRD-PARTY
//! (`MacaroonDischarge`) flow; this file pins the first-party fold + integrity teeth that
//! `CaveatChain` proves but no differential previously connected to the running code (a
//! "proven-but-dark mirror" gap the Silver-coverage sweep is closing).
//!
//! The Lean proves, relative to the named `MacKernel.unforgeable` (HMAC EUF-CMA) portal:
//!
//!  * `seedTag`/`foldTag`/`replayTag` — `T₀ = mac(root, nonce)`, `Tᵢ = mac(Tᵢ₋₁, encode(Cᵢ))`, and
//!    `verify` recomputes the tail from the root and compares (`verify_iff_wellTagged`).
//!  * `honest_chain_verifies` — a `seed` then any number of `append`s always `verify`s.
//!  * `append_narrows` — append-only attenuation can only restrict (the narrowing algebra).
//!  * `removal_breaks_tail` / `forgery_requires_mac_query` / `chain_unforgeable` — dropping, tampering,
//!    or forging a caveat is rejected (unless a MAC collision, which `unforgeable` forbids).
//!
//! This differential drives the GENUINE `Macaroon` engine — the same `crypto::hmac_sha256` chain the
//! SDK and federation authenticate bearer tokens with — and asserts:
//!
//!  1. **Replay agreement** — the Lean `replayTag` (`seedTag` + `foldTag` over the caveat encodings)
//!     re-run here against the REAL `crypto::hmac_sha256` chain equals the real `Macaroon.tail`
//!     byte-for-byte, after every `add_first_party`.
//!  2. **Honest-verify agreement** — a `Macaroon::new` + `add_first_party`* chain `verify`s on the real
//!     engine (`honest_chain_verifies`).
//!  3. **Integrity-tooth agreement** — the real `Macaroon::verify` REJECTS a removed caveat
//!     (`removal_breaks_tail`), a tampered caveat (`forgery_requires_mac_query`), and a wrong root key
//!     (`chain_unforgeable` premise) — exactly the negative theorems' decisions.

#![cfg(test)]

use crate::caveat::{CaveatSet, WireCaveat};
use crate::crypto;
use crate::macaroon::Macaroon;

/// Build a first-party `WireCaveat` (type 0 — a non-3p, non-bind first-party caveat) with a
/// `key=value` body. `WireCaveat::encode()` is the `encode(Cᵢ)` the Lean `Link.encoded` stands for.
fn kv_wire(key: &str, value: &str) -> WireCaveat {
    let mut body = key.as_bytes().to_vec();
    body.push(b'=');
    body.extend_from_slice(value.as_bytes());
    WireCaveat::new(0, body)
}

/// Append a first-party caveat to the macaroon via the real `add_first_party_wire`
/// (`macaroon.rs:158`) — the same HMAC-chain advance as `add_first_party`.
fn append_kv(mac: &mut Macaroon, key: &str, value: &str) {
    mac.add_first_party_wire(kv_wire(key, value));
}

// ───────────────────────────── Lean-mirror: replayTag = seedTag + foldTag ─────────────────────────────

/// Lean `Authority.CaveatChain.seedTag root nonce = mac root nonce` (`macaroon.rs:121`).
fn lean_seed_tag(root: &[u8; 32], nonce_bytes: &[u8]) -> [u8; 32] {
    crypto::hmac_sha256(root, nonce_bytes)
}

/// Lean `Authority.CaveatChain.foldTag t0 links` — the left fold `Tᵢ = mac(Tᵢ₋₁, encode(Cᵢ))`
/// (`macaroon.rs:215-254`). `encodings` are the `WireCaveat::encode()` bytes (`Link.encoded`).
fn lean_fold_tag(t0: [u8; 32], encodings: &[Vec<u8>]) -> [u8; 32] {
    let mut t = t0;
    for enc in encodings {
        t = crypto::hmac_sha256(&t, enc);
    }
    t
}

/// Lean `replayTag c = foldTag (seedTag root nonce) links` — recompute the tail from the ROOT
/// (`macaroon.rs:213-254`); does NOT consult the stored tail.
fn lean_replay_tag(root: &[u8; 32], nonce_bytes: &[u8], encodings: &[Vec<u8>]) -> [u8; 32] {
    lean_fold_tag(lean_seed_tag(root, nonce_bytes), encodings)
}

/// The encoded bytes of each first-party caveat in a macaroon = `WireCaveat::encode()` (`Link.encoded`).
fn wire_encodings(mac: &Macaroon) -> Vec<Vec<u8>> {
    mac.caveats.iter().map(|w| w.encode()).collect()
}

// ═══════════════════════ Differential 1: replay agreement (Lean replayTag == real tail) ═══════════════════════

#[test]
fn diff_replay_tag_matches_real_tail() {
    let root_key = crypto::random_key();
    let mut mac = Macaroon::new(
        &root_key,
        b"kid-replay".to_vec(),
        "https://dregg.dev".into(),
    );

    // After Macaroon::new, the tail is exactly seedTag(root, nonce) (empty fold).
    let nonce_bytes = mac.nonce.encode();
    assert_eq!(
        lean_replay_tag(&root_key, &nonce_bytes, &[]),
        mac.tail,
        "T₀ = seedTag(root, nonce) must equal the real new-macaroon tail"
    );

    // After each add_first_party, the real tail must equal the Lean replayTag over the encodings.
    let caveats = [("app", "demo"), ("action", "read"), ("exp", "block-150")];
    for (k, v) in &caveats {
        append_kv(&mut mac, k, v);
        let encs = wire_encodings(&mac);
        assert_eq!(
            lean_replay_tag(&root_key, &nonce_bytes, &encs),
            mac.tail,
            "Tᵢ = foldTag over encodings must equal the real tail after each append"
        );
    }
}

// ═══════════════════════ Differential 2: honest_chain_verifies (append-only chain verifies) ═══════════════════════

#[test]
fn diff_honest_chain_verifies() {
    let root_key = crypto::random_key();
    let mut mac = Macaroon::new(
        &root_key,
        b"kid-honest".to_vec(),
        "https://dregg.dev".into(),
    );
    append_kv(&mut mac, "app", "demo");
    append_kv(&mut mac, "action", "read");

    // Lean `honest_chain_verifies`: seed then appends always verify on the real engine.
    let collected = mac
        .verify(&root_key, &[])
        .expect("honest first-party chain must verify");
    assert_eq!(
        collected.len(),
        2,
        "verify collects all first-party caveats for clearing"
    );

    // And the Lean verify (replayTag == stored tail) AGREES with the real accept.
    let nonce_bytes = mac.nonce.encode();
    let lean_verifies = lean_replay_tag(&root_key, &nonce_bytes, &wire_encodings(&mac)) == mac.tail;
    assert!(
        lean_verifies,
        "Lean Chain.verify agrees the honest chain is well-tagged"
    );
}

// ═══════════════════════ Differential 3: integrity teeth (removal / tamper / wrong-key REJECTED) ═══════════════════════

#[test]
fn diff_removal_breaks_tail() {
    // Lean `removal_breaks_tail`: dropping the last caveat without re-signing fails verify.
    let root_key = crypto::random_key();
    let mut mac = Macaroon::new(&root_key, b"kid-rm".to_vec(), "https://dregg.dev".into());
    append_kv(&mut mac, "app", "demo");
    append_kv(&mut mac, "action", "read");

    let mut stripped = mac.clone();
    stripped.caveats = CaveatSet::new();
    stripped.caveats.push(mac.caveats.as_slice()[0].clone()); // drop the 2nd caveat, keep mac.tail

    // Real engine rejects; Lean replayTag over the stripped links ≠ the (unchanged) stored tail.
    assert!(
        stripped.verify(&root_key, &[]).is_err(),
        "real: removed caveat rejected"
    );
    let nonce_bytes = stripped.nonce.encode();
    assert_ne!(
        lean_replay_tag(&root_key, &nonce_bytes, &wire_encodings(&stripped)),
        stripped.tail,
        "Lean: stripped chain's replayTag diverges from the stored tail (removal_breaks_tail)"
    );
}

#[test]
fn diff_tampered_caveat_rejected() {
    // Lean `forgery_requires_mac_query`: tampering a caveat's encoded bytes fails verify.
    let root_key = crypto::random_key();
    let mut mac = Macaroon::new(
        &root_key,
        b"kid-tamper".to_vec(),
        "https://dregg.dev".into(),
    );
    append_kv(&mut mac, "app", "demo");

    let mut tampered = mac.clone();
    if let Some(c) = tampered.caveats.as_slice().first() {
        let mut modified: WireCaveat = c.clone();
        modified.body = vec![0xff, 0xfe, 0xfd];
        tampered.caveats = CaveatSet::new();
        tampered.caveats.push(modified);
    }

    assert!(
        tampered.verify(&root_key, &[]).is_err(),
        "real: tampered caveat rejected"
    );
    let nonce_bytes = tampered.nonce.encode();
    assert_ne!(
        lean_replay_tag(&root_key, &nonce_bytes, &wire_encodings(&tampered)),
        tampered.tail,
        "Lean: tampered chain's replayTag diverges from the stored tail"
    );
}

#[test]
fn diff_wrong_root_key_rejected() {
    // Lean `chain_unforgeable` premise: a verifier without the root key cannot accept the chain.
    let root_key = crypto::random_key();
    let wrong_key = crypto::random_key();
    let mut mac = Macaroon::new(&root_key, b"kid-wrong".to_vec(), "https://dregg.dev".into());
    append_kv(&mut mac, "app", "demo");

    assert!(
        mac.verify(&wrong_key, &[]).is_err(),
        "real: wrong root key rejected"
    );
    // Lean: replaying from the WRONG seed yields a different tail.
    let nonce_bytes = mac.nonce.encode();
    assert_ne!(
        lean_replay_tag(&wrong_key, &nonce_bytes, &wire_encodings(&mac)),
        mac.tail,
        "Lean: replay from the wrong root key diverges from the genuine tail"
    );
    assert_eq!(
        lean_replay_tag(&root_key, &nonce_bytes, &wire_encodings(&mac)),
        mac.tail,
        "Lean: replay from the GENUINE root key matches (the positive control)"
    );
}
