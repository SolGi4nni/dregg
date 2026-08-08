//! THE VERIFIED-ORDER BUDGET — how far does the verified Lean τ-order FFI actually reach,
//! and do the two orders the node swaps between agree?
//!
//! ## The claim under test
//!
//! `node/src/blocklace_sync.rs` says the node "finalizes over the VERIFIED ordering": the
//! authoritative finalized order is `BlocklaceFinality.tauOrder`, reached through
//! `finality_gate::VerifiedFinality::compute_order` → `dregg_lean_ffi::verified_tau_order` →
//! the `@[export] dregg_tau_order`. That claim is **conditional on a per-poll wall-clock
//! budget** (`verified_order_ffi_timeout()`, default **2500 ms**). When the budget is missed
//! the poll does NOT use the verified order — it either runs the un-verified Rust
//! `ordering::tau` twin (`DREGG_ALLOW_UNVERIFIED_CONSENSUS=1`, which is what
//! `scripts/federation-local.sh:86` sets) or finalizes NOTHING (a Lean-linked PoA node, which
//! `scripts/poa-devnet.sh` pins to `=0`).
//!
//! So "we finalize over the verified ordering" is really "we finalize over the verified
//! ordering **on polls where a 2500 ms budget is met**". This test measures where that budget
//! is met, and pins the two facts an operator has to be able to rely on.
//!
//! ## What is measured, and why it is measured this way
//!
//! Both sides run the REAL node code — `VerifiedFinality::compute_order` and
//! `blocklace_sync::build_ordering_blocklace` + `dregg_blocklace::ordering::tau`, the exact
//! pair `poll_finalized_blocks` runs each poll. Nothing here re-implements either; a mirror
//! would silently test itself (and the topological-insertion fix in
//! `build_ordering_blocklace` is exactly the part a mirror gets wrong).
//!
//! The lace is the shape a live federation produces: an `n`-validator committee, round-
//! synchronous, every round citing ALL of the previous round. That is the DAG
//! `scripts/federation-local.sh` builds, and the shape whose growth drove the observed
//! over-budget warnings at `lace_size` 773–981.
//!
//! ## ⚠ Wall-clock is machine- and LOAD-dependent
//!
//! Absolute milliseconds price the box, not the code. The `#[ignore]`d
//! [`verified_order_cost_curve`] is a MEASUREMENT INSTRUMENT, not a gate — run it explicitly
//! on a quiet box and read the printed table. The GATE in this file is
//! [`the_two_orders_the_node_swaps_between_agree_exactly`], which asserts a machine-independent
//! property: the verified Lean order and the Rust `ordering::tau` order the node substitutes
//! for it are the SAME SEQUENCE, not merely the same set.
//!
//! ## The set/sequence distinction is the point
//!
//! `poll_finalized_blocks`'s own differential (`blocklace_sync.rs`, the `coord` closure)
//! compares `Vec<(seq, creator)>` **after `sort_unstable()`** — it compares the finalized
//! SET. The fallback substitutes one ORDER for another. A differential that sorts before
//! comparing cannot, even in principle, see the property the substitution needs. This test
//! asserts the SEQUENCE.

use std::time::{Duration, Instant};

use dregg_blocklace::finality::{Block, BlockId, Blocklace, Payload};
use dregg_blocklace::signer::HybridBlockSigner;
use dregg_node::blocklace_sync::build_ordering_blocklace;
use dregg_node::finality_gate::VerifiedFinality;
use ed25519_dalek::SigningKey;

/// The default per-poll budget `blocklace_sync::verified_order_ffi_timeout()` enforces. Kept
/// here as a plain constant so the printed table can say "over/under" without importing a
/// private fn; if the default in `blocklace_sync.rs` changes, this comment is the only thing
/// that goes stale (the measurement itself does not depend on it).
const DEFAULT_PER_POLL_BUDGET: Duration = Duration::from_millis(2500);

/// Put THIS process in the same disposition as the deployed binary: verified PQ cores installed
/// before the first ML-DSA operation.
///
/// `HybridBlockSigner::new` derives an ML-DSA-65 key from the ed25519 seed, and `dregg_pq`'s audit
/// gate `process::abort()`s rather than answer that from the unaudited `fips204` crate. The five
/// callers of `install_verified_pq_cores` are all BINARY entry points, and `node/src/lib.rs`'s
/// `pq_test_bootstrap` initializer is `#[cfg(test)]` — so it covers the lib-test binary and NOT an
/// integration test in `node/tests/`, which is its own process. Without this call the first
/// `committee()` aborts the whole test binary with SIGABRT.
///
/// ⚠ The other way to make that abort go away is `DREGG_ALLOW_UNAUDITED_PQ=1`, which routes keygen
/// onto the unaudited crate — the exact substitution the gate exists to prevent, and a reason to
/// distrust every verdict obtained that way. This test asserts a property OF THE VERIFIED
/// consensus ordering; obtaining it on unaudited crypto would be self-defeating. Idempotent,
/// export-gated, once-per-process.
fn install_pq_cores_for_this_test_process() {
    dregg_node::install_verified_pq_cores();
}

/// An `n`-validator round-synchronous committee, built once (ML-DSA key derivation is per
/// signer, not per block — `Block::new` would re-derive on every call and dominate setup).
fn committee(n: usize) -> Vec<HybridBlockSigner> {
    install_pq_cores_for_this_test_process();
    (0..n)
        .map(|i| HybridBlockSigner::new(SigningKey::from_bytes(&[(i as u8) + 1; 32])))
        .collect()
}

/// Build a round-synchronous, fully cross-linked lace of `rounds` rounds over `signers`:
/// round 0 is the genesis cohort, and every later round's blocks cite ALL of the previous
/// round's. Total blocks = `signers.len() * rounds`. This is the live federation shape.
fn build_lace(signers: &[HybridBlockSigner], rounds: u64) -> (Blocklace, Vec<[u8; 32]>) {
    let participants: Vec<[u8; 32]> = signers.iter().map(|s| s.creator()).collect();
    let mut lace = Blocklace::new(
        SigningKey::from_bytes(&[1u8; 32]),
        // quorum threshold: the usual supermajority shape; irrelevant to `tau`/`tauOrder`,
        // which take the participant set explicitly.
        (signers.len() * 2) / 3 + 1,
    );

    let mut prev: Vec<BlockId> = Vec::new();
    for round in 0..rounds {
        let mut this_round = Vec::with_capacity(signers.len());
        for (i, s) in signers.iter().enumerate() {
            let b = Block::new_signed_by(
                s,
                round,
                // Turn payloads are CONSENSUS-ACTIONABLE — the same class the live producer
                // emits, so nothing here is dismissed as DAG plumbing.
                Payload::Turn(vec![(round as u8).wrapping_mul(7).wrapping_add(i as u8)]),
                prev.clone(),
            );
            this_round.push(b.id());
            lace.receive_block(b).expect("round insert");
        }
        prev = this_round;
    }
    (lace, participants)
}

/// The node's REAL Rust order for a lace: exactly what `poll_finalized_blocks` computes into
/// `rust_order` — `build_ordering_blocklace` (topological insert) then `ordering::tau`, then
/// map the ordering ids back to finality `BlockId`s.
fn node_rust_order(lace: &Blocklace, participants: &[[u8; 32]]) -> Vec<BlockId> {
    let (ordering_lace, id_map) = build_ordering_blocklace(lace);
    dregg_blocklace::ordering::tau(&ordering_lace, participants)
        .into_iter()
        .filter_map(|oid| id_map.get(&oid).copied())
        .collect()
}

/// `(creator, seq)` coordinates IN ORDER — the content-identical coordinate the two id schemes
/// (blake3 `BlockId` vs interned Lean `Nat`) share. NOT sorted: the sequence is the point.
fn coords_in_order(lace: &Blocklace, ids: &[BlockId]) -> Vec<([u8; 32], u64)> {
    ids.iter()
        .filter_map(|id| lace.get(id).map(|b| (b.creator, b.seq)))
        .collect()
}

/// ── THE GATE ────────────────────────────────────────────────────────────────────────────────
///
/// The verified Lean `dregg_tau_order` and the Rust `ordering::tau` the node SUBSTITUTES for it
/// on an over-budget poll must produce the **same sequence** of `(creator, seq)` coordinates.
///
/// This is the property the timeout fallback silently assumes. `blocklace_sync.rs` states it
/// ("the edge-faithful Rust `tau` order … == `tauOrder` after the topological build fix") and
/// then substitutes on that basis, but the differential guarding the claim SORTS before
/// comparing — so it checks the finalized SET and is blind to a pure reordering. If the two
/// ever disagree in ORDER, an over-budget poll changes the executed order of turns while every
/// existing check stays green. That is the finding this test exists to make impossible to miss.
///
/// Self-skips when the archive lacks the raw-order export (a stale/marshal-only build), unless
/// `DREGG_TEST_REQUIRE_LEAN=1`, under which the absent export PANICS — the same posture
/// `finality_gate.rs`'s gate tests take.
#[test]
fn the_two_orders_the_node_swaps_between_agree_exactly() {
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::tau_order_available(),
        "the Lean raw tau-order export (tau_order_available()==false)",
    ) {
        return;
    }

    // Committee sizes and depths kept small enough to run inside a normal `cargo test` — the
    // ORDER-AGREEMENT property is not a function of scale, and the cost curve lives in the
    // #[ignore]d measurement below. n=4 is the observed federation; n=3 and n=5 bracket it
    // (n=3 is unanimity/zero-slack, n=5 has real supermajority slack).
    for n in [3usize, 4, 5] {
        let signers = committee(n);
        for rounds in [3u64, 6, 9] {
            let (lace, participants) = build_lace(&signers, rounds);
            let lean = VerifiedFinality::compute_order(&lace, &participants)
                .expect("raw-order gate ran (archive present + wire non-ERR)");
            let rust = node_rust_order(&lace, &participants);

            let lean_seq = coords_in_order(&lace, &lean);
            let rust_seq = coords_in_order(&lace, &rust);

            // ANTI-VACUITY: a comparison of two empty orders proves nothing, and an
            // un-super-ratified lace finalizes nothing. Require the verified rule to have
            // actually finalized something before reading the agreement as evidence.
            assert!(
                !lean_seq.is_empty(),
                "n={n} rounds={rounds}: the verified rule finalized NOTHING — the agreement \
                 assertion below would be vacuous. Increase the depth so a leader super-ratifies."
            );

            assert_eq!(
                lean_seq,
                rust_seq,
                "n={n} rounds={rounds} (lace={} blocks): the verified Lean `dregg_tau_order` \
                 and the Rust `ordering::tau` produced DIFFERENT SEQUENCES. The node SUBSTITUTES \
                 the Rust order for the verified one on any poll that misses the \
                 `DREGG_FINALITY_ORDER_TIMEOUT_MS` budget, so this is a live order divergence, \
                 not a lab curiosity. lean_len={} rust_len={}",
                lace.iter().count(),
                lean_seq.len(),
                rust_seq.len(),
            );

            // And the weaker property the NODE's own differential checks — pinned separately so
            // a future change that keeps the sets equal while breaking the order fails on the
            // assertion above and NOT on this one, making the distinction legible in the output.
            let mut lean_set = lean_seq.clone();
            let mut rust_set = rust_seq.clone();
            lean_set.sort_unstable();
            rust_set.sort_unstable();
            assert_eq!(
                lean_set, rust_set,
                "n={n} rounds={rounds}: finalized SETS differ (the node's own differential would \
                 have caught this one)"
            );
        }
    }
}

/// ── THE MEASUREMENT INSTRUMENT (not a gate) ─────────────────────────────────────────────────
///
/// Print the verified-Lean τ-order FFI cost against lace size, alongside the Rust `ordering::tau`
/// cost on the same lace, and mark where the per-poll budget is crossed.
///
/// `#[ignore]` because it asserts nothing about wall-clock (which prices the box and its load,
/// not the code) and because the large sizes take minutes. Run it explicitly, ON A QUIET BOX,
/// and read the table:
///
/// ```text
/// cargo test -p dregg-node --test verified_order_budget -- --ignored --nocapture
/// ```
///
/// Knobs: `ORDER_BUDGET_N` (committee size, default 4), `ORDER_BUDGET_ROUNDS`
/// (comma-separated round counts), `ORDER_BUDGET_CEILING_MS` (stop growing once one FFI call
/// exceeds this, default 120000).
///
/// The order-agreement assertion runs at EVERY size here too — so the agreement evidence is not
/// confined to the small laces the gate above can afford.
#[test]
#[ignore = "measurement instrument: wall-clock, minutes long, run explicitly on a quiet box"]
fn verified_order_cost_curve() {
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::tau_order_available(),
        "the Lean raw tau-order export (tau_order_available()==false)",
    ) {
        return;
    }

    let n: usize = std::env::var("ORDER_BUDGET_N")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(4);
    let rounds_list: Vec<u64> = std::env::var("ORDER_BUDGET_ROUNDS")
        .ok()
        .map(|v| v.split(',').filter_map(|p| p.trim().parse().ok()).collect())
        .unwrap_or_else(|| vec![5, 10, 20, 40, 60, 80, 120, 160, 240]);
    let ceiling = Duration::from_millis(
        std::env::var("ORDER_BUDGET_CEILING_MS")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(120_000),
    );

    let signers = committee(n);

    eprintln!(
        "# verified tau-order FFI cost curve  (committee n={n}, round-synchronous, fully cross-linked)"
    );
    eprintln!(
        "# per-poll budget = {} ms (blocklace_sync::verified_order_ffi_timeout default)",
        DEFAULT_PER_POLL_BUDGET.as_millis()
    );
    eprintln!("#");
    eprintln!("#   blocks   lean_ms   rust_ms   lean/rust   vs_budget   growth_exp   finalized");

    let mut prev: Option<(f64, f64)> = None; // (blocks, lean_ms)
    for rounds in rounds_list {
        let (lace, participants) = build_lace(&signers, rounds);
        let blocks = lace.iter().count();

        let t0 = Instant::now();
        let lean = VerifiedFinality::compute_order(&lace, &participants)
            .expect("raw-order gate ran (archive present + wire non-ERR)");
        let lean_ms = t0.elapsed().as_secs_f64() * 1000.0;

        let t1 = Instant::now();
        let rust = node_rust_order(&lace, &participants);
        let rust_ms = t1.elapsed().as_secs_f64() * 1000.0;

        // The agreement property, re-asserted at every measured size.
        let lean_seq = coords_in_order(&lace, &lean);
        let rust_seq = coords_in_order(&lace, &rust);
        assert_eq!(
            lean_seq,
            rust_seq,
            "blocks={blocks}: verified Lean order and Rust `ordering::tau` order DIVERGED IN \
             SEQUENCE at scale (lean_len={} rust_len={})",
            lean_seq.len(),
            rust_seq.len()
        );

        // Local growth exponent between consecutive points: log(t2/t1) / log(n2/n1). A pure
        // O(n^k) shows k here; it is the only load-robust number in the table (a steady load
        // factor cancels in the ratio).
        let exp = match prev {
            Some((pb, pt)) if pt > 0.0 && pb > 0.0 && blocks as f64 > pb => {
                format!(
                    "{:>10.2}",
                    (lean_ms / pt).ln() / ((blocks as f64) / pb).ln()
                )
            }
            _ => format!("{:>10}", "-"),
        };
        let verdict = if lean_ms > DEFAULT_PER_POLL_BUDGET.as_millis() as f64 {
            "OVER"
        } else {
            "under"
        };
        eprintln!(
            "  {blocks:>8}  {lean_ms:>8.1}  {rust_ms:>8.2}  {:>9.1}x  {verdict:>9}  {exp}  {:>9}",
            if rust_ms > 0.0 {
                lean_ms / rust_ms
            } else {
                0.0
            },
            lean_seq.len(),
        );
        prev = Some((blocks as f64, lean_ms));

        if t0.elapsed() > ceiling {
            eprintln!(
                "# stopping: a single FFI call exceeded the {} ms measurement ceiling",
                ceiling.as_millis()
            );
            break;
        }
    }
}
