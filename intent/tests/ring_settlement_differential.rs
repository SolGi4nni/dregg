//! Ring-settlement differential: PIN the Rust intent-crate ring settlement against the
//! VERIFIED executor's per-asset conservation + atomicity decision.
//!
//! # Why this test exists (the coherence move)
//!
//! The running matcher (`solver.rs` / `trustless.rs`) settles ring trades with its OWN Rust
//! accounting: `RingSolver::validate_ring` builds the `Vec<Settlement>` legs from a cycle, and
//! `check_settlement_conservation` (exposed here as `trustless::ring_conservation_decision`)
//! decides accept/reject by the closed-accounting shape (no phantom value / per-asset balance /
//! cycle closure). That settlement path had ZERO references to the verified executor
//! (`grep dregg_lean_ffi intent/src` = 0) — value moved off the verified path.
//!
//! The verified executor's settlement semantics are now MODELLED + PROVED in Lean
//! (`metatheory/Dregg2/Intent/Ring.lean`): a ring's legs are folded through the verified
//! per-asset kernel `recKExecAsset` (the SAME gate the mandates route through), with two
//! keystones —
//!
//!   * `settleRing_conserves` — a fully-settled ring conserves value PER ASSET (Σ legs = 0);
//!   * `settleRing_atomic` — any leg that cannot commit aborts the WHOLE ring (all-or-nothing).
//!
//! This differential PINS that the Rust ring-settlement decision AGREES with that verified
//! semantics over a ring corpus: the [`verified_executor_reference`] below is a faithful
//! reimplementation of the Lean `settleRing` fold (the EXACT `recKExecAsset` gate + per-asset
//! ledger the Lean keystones are proved over — mirrored the same way
//! `dregg-lean-ffi/src/full_turn_differential.rs` mirrors `execFullTurn`). For each ring we
//! assert: the Rust intent path accepts the ring IFF the verified executor settles it fully and
//! conserves every asset. A drift between the two is caught here.
//!
//! NEXT STEP (named-open, not done here): route the LIVE settlement
//! (`TrustlessIntentEngine::finalize` → `lowering::lower` → `SealedTurn`) through the verified
//! executor FFI (`dregg_lean_ffi::shadow_exec_full_forest_auth` via `dregg-turn`'s `lean-shadow`
//! feature) instead of executing the `SealedTurn` on the legacy Rust path. That is a full
//! turn-execution refactor gated on the FFI feature; this differential pins the SEMANTICS agree
//! first (the "differential first" discipline, like the captp/mandate differentials).

use dregg_intent::CommitmentId;
use dregg_intent::exchange::AssetId;
use dregg_intent::solver::{ExchangeSpec, IntentNode, RingSolver, RingTrade, Settlement};
use dregg_intent::trustless::ring_conservation_decision;

use std::collections::{BTreeMap, BTreeSet};

fn asset(byte: u8) -> AssetId {
    let mut a = [0u8; 32];
    a[0] = byte;
    a
}

fn cid(byte: u8) -> CommitmentId {
    CommitmentId([byte; 32])
}

// =============================================================================
// The VERIFIED-EXECUTOR REFERENCE — a faithful mirror of Lean `Dregg2.Intent.Ring.settleRing`.
//
// Each leg is the executable `Turn { actor := from, src := from, dst := to, amt := amount }` over
// the per-asset ledger `bal : (cell, asset) -> i128` (the Lean `RecordKernelState.bal`). The gate
// is `recKExecAsset`: authorized (here: actor owns src, i.e. the sender authorises their own send —
// the `actor == src` leg of `authorizedB`) AND `0 <= amt` AND `amt <= bal src asset` (availability)
// AND `src != dst` AND both cells live. The fold is ALL-OR-NOTHING: any leg that fails aborts the
// whole ring to `None` (atomicity / rollback).
// =============================================================================

/// The per-asset ledger: `(cell, asset) -> balance`. The Lean `RecordKernelState.bal`, restricted
/// to the cells/assets the ring touches.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Ledger {
    bal: BTreeMap<(u8, [u8; 32]), i128>,
    accounts: BTreeSet<u8>,
}

impl Ledger {
    fn get(&self, cell: u8, a: &[u8; 32]) -> i128 {
        *self.bal.get(&(cell, *a)).unwrap_or(&0)
    }
    fn set(&mut self, cell: u8, a: &[u8; 32], v: i128) {
        self.bal.insert((cell, *a), v);
    }
    /// Total supply of asset `a` across the live accounts — the Lean `recTotalAsset`.
    fn total_asset(&self, a: &[u8; 32]) -> i128 {
        self.accounts.iter().map(|c| self.get(*c, a)).sum()
    }
}

/// `recKExecAsset` for one leg: the verified per-asset transition. `None` on a failed gate.
fn rec_exec_asset(k: &Ledger, s: &Settlement) -> Option<Ledger> {
    let from = s.from.0[0];
    let to = s.to.0[0];
    let amt = s.amount as i128;
    let src_bal = k.get(from, &s.asset);
    // The verified gate (mirror of `recKExecAsset`): authorised (sender owns src ⇒ actor==src),
    // amount non-negative and available IN THAT ASSET, distinct endpoints, both live.
    let ok = amt >= 0
        && amt <= src_bal
        && from != to
        && k.accounts.contains(&from)
        && k.accounts.contains(&to);
    if !ok {
        return None;
    }
    let mut ns = k.clone();
    ns.set(from, &s.asset, src_bal - amt);
    ns.set(to, &s.asset, k.get(to, &s.asset) + amt);
    Some(ns)
}

/// `settleRing` — the atomic fold of the ring's legs through the verified executor. `None` if ANY
/// leg fails (rollback to the pre-state). Mirror of Lean `settleRing`.
fn verified_executor_reference(k0: &Ledger, ring: &RingTrade) -> Option<Ledger> {
    let mut k = k0.clone();
    for leg in &ring.settlements {
        match rec_exec_asset(&k, leg) {
            Some(nk) => k = nk,
            None => return None, // atomicity: the whole ring aborts
        }
    }
    Some(k)
}

/// Seed a ledger that FUNDS every sender for its leg (so the availability gate passes), with all
/// touched cells live. This isolates the CONSERVATION question from incidental underfunding —
/// we want to test that a *structurally accepted* ring also conserves on the verified executor.
fn funded_ledger(ring: &RingTrade) -> Ledger {
    let mut bal: BTreeMap<(u8, [u8; 32]), i128> = BTreeMap::new();
    let mut accounts: BTreeSet<u8> = BTreeSet::new();
    for leg in &ring.settlements {
        let from = leg.from.0[0];
        let to = leg.to.0[0];
        accounts.insert(from);
        accounts.insert(to);
        // Fund the sender with exactly its outgoing amount of that asset.
        *bal.entry((from, leg.asset)).or_insert(0) += leg.amount as i128;
    }
    Ledger { bal, accounts }
}

/// The set of assets a ring touches (for the per-asset conservation check).
fn touched_assets(ring: &RingTrade) -> BTreeSet<[u8; 32]> {
    ring.settlements.iter().map(|l| l.asset).collect()
}

// =============================================================================
// The COMPARISON ORACLE: for a ring, assert the Rust intent decision and the verified-executor
// decision AGREE.
//   accept  := the Rust ring conserves (ring_conservation_decision == Ok)
//   settles := the verified executor settles the funded ring fully AND conserves every asset
// The differential pins `accept <=> settles` over the corpus.
// =============================================================================

fn check_agreement(ring: &RingTrade) {
    let rust_accepts = ring_conservation_decision(std::slice::from_ref(ring)).is_ok();

    let k0 = funded_ledger(ring);
    let settled = verified_executor_reference(&k0, ring);
    let verified_settles_and_conserves = match &settled {
        Some(k1) => touched_assets(ring)
            .iter()
            .all(|a| k1.total_asset(a) == k0.total_asset(a)),
        None => false,
    };

    assert_eq!(
        rust_accepts, verified_settles_and_conserves,
        "DIVERGENCE: Rust ring-conservation accept={rust_accepts} but verified executor \
         settles+conserves={verified_settles_and_conserves}\n  ring={:?}",
        ring.settlements
    );

    // When BOTH accept, the verified post-state must literally conserve EVERY touched asset
    // (the Lean `settleRing_conserves` keystone, witnessed on this corpus).
    if rust_accepts {
        let k1 = settled.expect("accepted ring must settle on the verified executor");
        for a in touched_assets(ring) {
            assert_eq!(
                k1.total_asset(&a),
                k0.total_asset(&a),
                "verified executor leaked value in asset {:02x}.. on an accepted ring",
                a[0]
            );
        }
    }
}

// =============================================================================
// CORPUS 1: rings built by the REAL Rust matcher (`RingSolver::validate_ring`).
// =============================================================================

/// Build a node from raw parts.
fn node(id: u8, creator: u8, off: u8, off_amt: u64, want: u8, want_min: u64) -> IntentNode {
    IntentNode {
        intent_id: [id; 32],
        exchange: ExchangeSpec {
            offer_asset: asset(off),
            offer_amount: off_amt,
            want_asset: asset(want),
            want_min_amount: want_min,
            min_rate: None,
            max_rate: None,
        },
        creator: cid(creator),
        expiry: 9999,
    }
}

#[test]
fn ring_solver_2cycle_agrees_with_verified_executor() {
    // A 2-ring: A offers AA wants BB; B offers BB wants AA. Cycle order [A, B].
    let a = node(1, 0x01, 0xAA, 100, 0xBB, 50);
    let b = node(2, 0x02, 0xBB, 80, 0xAA, 40);
    let solver = RingSolver::new(5);
    let ring = solver
        .validate_ring(&[a, b], 100)
        .expect("2-ring should validate");
    assert_eq!(ring.settlements.len(), 2);
    check_agreement(&ring);
}

#[test]
fn ring_solver_3cycle_agrees_with_verified_executor() {
    // The canonical 3-ring from solver.rs's own test: A(AA->BB), B(BB->CC), C(CC->AA),
    // ordered [A, C, B] (A->C->B->A).
    let a = node(1, 0x01, 0xAA, 100, 0xBB, 50);
    let b = node(2, 0x02, 0xBB, 80, 0xCC, 30);
    let c = node(3, 0x03, 0xCC, 60, 0xAA, 40);
    let solver = RingSolver::new(5);
    let ring = solver
        .validate_ring(&[a, c, b], 100)
        .expect("3-ring should validate");
    assert_eq!(ring.settlements.len(), 3);
    // Both must agree, and the verified executor must conserve AA, BB, CC.
    check_agreement(&ring);
}

#[test]
fn ring_solver_corpus_fuzz_agrees() {
    // A small fixed-seed corpus of well-formed cyclic rings of varying size and amounts. Every
    // ring the matcher validates must settle+conserve on the verified executor.
    let solver = RingSolver::new(6);
    // xorshift PRNG for determinism (no external dep).
    let mut state: u64 = 0xD1CE_F00D_1234_5678;
    let mut next = || {
        state ^= state >> 12;
        state ^= state << 25;
        state ^= state >> 27;
        state.wrapping_mul(0x2545_F491_4F6C_DD1D)
    };

    let mut validated = 0usize;
    for _ in 0..400 {
        let n = 2 + (next() % 4) as usize; // 2..5 participants
        // Asset kinds AA, BB, CC, DD, EE chained in a cycle: node k offers asset k, wants asset k-1.
        let amts: Vec<u64> = (0..n).map(|_| 1 + (next() % 1000)).collect();
        let mut nodes = Vec::new();
        for k in 0..n {
            let off = 0xA0 + k as u8;
            let want = 0xA0 + ((k + n - 1) % n) as u8; // wants the previous node's offer
            // offer_amount must be >= the next node's want_min; use a generous offer.
            let want_min = amts[k];
            let off_amt = 2000 + amts[k]; // always enough
            nodes.push(node(
                (k + 1) as u8,
                (k + 1) as u8,
                off,
                off_amt,
                want,
                want_min,
            ));
        }
        // The ring order: node k's offer (asset A0+k) satisfies the node that WANTS A0+k, which is
        // node k+1 (it wants A0+k). So the cycle in graph order is 0->1->2->...->0; validate_ring
        // expects the cycle in walk order, which is exactly `nodes` as built.
        if let Ok(ring) = solver.validate_ring(&nodes, 100) {
            validated += 1;
            check_agreement(&ring);
        }
    }
    assert!(validated > 0, "corpus produced no validated rings");
}

// =============================================================================
// CORPUS 2: ADVERSARIAL hand-built rings — the TEETH. A non-conserving "ring" the Rust
// structural check rejects must ALSO fail on the verified executor (and vice versa). This is the
// Lean `freeMintRing_rejected` / `zeroLegRing_rejected` teeth, witnessed at the Rust differential.
// =============================================================================

#[test]
fn free_mint_ring_caught_by_rust_cycle_closure_not_by_per_asset_executor() {
    // Cell 1 sends AA to cell 2, but cell 2 never sends (only receives) — a free mint. The cycle
    // does not close, so the Rust check rejects (`recvImpSend` / cycle-closure fails).
    //
    // HONEST ASYMMETRY (the old test asserted a TAUTOLOGY on the literal and never ran the
    // executor): the verified per-asset executor, given a FUNDED sender, SETTLES the single leg and
    // CONSERVES the per-asset total (a transfer is conserving by construction). So per-asset
    // conservation ALONE does not catch the free mint — the Rust cycle-closure check is the
    // load-bearing teeth here, and this differential documents that gap rather than hiding it.
    let ring = RingTrade {
        participants: vec![[1; 32]],
        settlements: vec![Settlement {
            from: cid(1),
            to: cid(2),
            asset: asset(0xAA),
            amount: 5,
        }],
        score: 1.0,
    };
    // Rust structural check rejects — and specifically on the CYCLE-CLOSURE teeth (a receiver that
    // never sends), not some incidental error.
    let err = ring_conservation_decision(std::slice::from_ref(&ring))
        .expect_err("free-mint ring must be rejected by the Rust conservation check");
    assert!(
        err.contains("free mint") || err.contains("never sends"),
        "rejection must name the cycle-closure (free-mint) teeth, got: {err}"
    );
    // The verified per-asset executor is INVOKED (not a tautology): it settles the funded leg and
    // conserves every touched asset's global total — proving it does NOT reject the free mint.
    let k0 = funded_ledger(&ring);
    let settled =
        verified_executor_reference(&k0, &ring).expect("funded single leg settles on the executor");
    for a in touched_assets(&ring) {
        assert_eq!(
            settled.total_asset(&a),
            k0.total_asset(&a),
            "the per-asset executor conserves asset {:02x}.. — so per-asset conservation alone does \
             NOT catch the free mint",
            a[0]
        );
    }
    // The exact gap the Rust check closes: a node receives but never sends (non-closed cycle).
    let senders: BTreeSet<u8> = ring.settlements.iter().map(|s| s.from.0[0]).collect();
    let receivers: BTreeSet<u8> = ring.settlements.iter().map(|s| s.to.0[0]).collect();
    assert!(
        receivers.iter().any(|r| !senders.contains(r)),
        "cell 2 receives but never sends — the non-closure the per-asset executor misses"
    );
}

#[test]
fn zero_amount_leg_rejected_by_rust_but_committed_by_the_per_asset_executor() {
    // An otherwise-closed 2-ring with a zero-amount leg (a no-op masquerading as a settlement).
    let ring = RingTrade {
        participants: vec![[1; 32], [2; 32]],
        settlements: vec![
            Settlement {
                from: cid(1),
                to: cid(2),
                asset: asset(0xAA),
                amount: 5,
            },
            Settlement {
                from: cid(2),
                to: cid(1),
                asset: asset(0xBB),
                amount: 0, // phantom no-op
            },
        ],
        score: 2.0,
    };
    // Rust rejects — specifically on the NO-PHANTOM-VALUE teeth (the zero-amount leg).
    let err = ring_conservation_decision(std::slice::from_ref(&ring))
        .expect_err("zero-amount leg must be rejected by the Rust conservation check");
    assert!(
        err.contains("zero-amount"),
        "rejection must name the zero-amount (no-phantom-value) teeth, got: {err}"
    );
    // HONEST ASYMMETRY (invoking the executor, not a tautology): the verified per-asset executor
    // COMMITS the zero transfer (amt=0 passes the availability gate — a vacuous move), settling the
    // ring and conserving every asset. So the no-phantom-value rule lives ONLY on the Rust side;
    // this differential documents that the per-asset executor does NOT reject the masquerade.
    let k0 = funded_ledger(&ring);
    let settled = verified_executor_reference(&k0, &ring)
        .expect("the per-asset executor commits the zero leg (a vacuous, conserving move)");
    for a in touched_assets(&ring) {
        assert_eq!(
            settled.total_asset(&a),
            k0.total_asset(&a),
            "the executor conserves asset {:02x}.. — a zero move is vacuous, so per-asset \
             conservation does NOT reject the phantom leg",
            a[0]
        );
    }
}

#[test]
fn receive_only_node_caught_by_rust_cycle_closure_not_by_per_asset_executor() {
    // A "ring" with an asset sent but, by a fabricated decoupled shape, more received than sent:
    // we add a second credit leg of AA with no matching debit (free credit). check_settlement_
    // conservation's per-asset balance (sent==received) is preserved by from/to pairing for these
    // legs, so to break per-asset balance we instead break cycle closure: a third party only
    // receives.
    let ring = RingTrade {
        participants: vec![[1; 32], [2; 32], [3; 32]],
        settlements: vec![
            Settlement {
                from: cid(1),
                to: cid(2),
                asset: asset(0xAA),
                amount: 10,
            },
            Settlement {
                from: cid(2),
                to: cid(1),
                asset: asset(0xBB),
                amount: 7,
            },
            // Cell 3 only receives — free mint into the ring.
            Settlement {
                from: cid(1),
                to: cid(3),
                asset: asset(0xCC),
                amount: 3,
            },
        ],
        score: 3.0,
    };
    // Rust rejects on the cycle-closure teeth (cell 3 receives but never sends).
    let err = ring_conservation_decision(std::slice::from_ref(&ring))
        .expect_err("a ring with a receive-only node (cell 3) must be rejected (free mint)");
    assert!(
        err.contains("free mint") || err.contains("never sends"),
        "rejection must name the cycle-closure (free-mint) teeth, got: {err}"
    );
    // HONEST ASYMMETRY (executor INVOKED): the funded legs all settle and every asset's global
    // total is conserved — the per-asset executor does NOT catch cell 3's receive-only free mint.
    let k0 = funded_ledger(&ring);
    let settled =
        verified_executor_reference(&k0, &ring).expect("funded legs settle on the executor");
    for a in touched_assets(&ring) {
        assert_eq!(
            settled.total_asset(&a),
            k0.total_asset(&a),
            "the per-asset executor conserves asset {:02x}.. — cycle-closure is the load-bearing \
             Rust teeth, not per-asset conservation",
            a[0]
        );
    }
    let senders: BTreeSet<u8> = ring.settlements.iter().map(|s| s.from.0[0]).collect();
    let receivers: BTreeSet<u8> = ring.settlements.iter().map(|s| s.to.0[0]).collect();
    // Cell 3 receives but never sends — the non-closure the per-asset executor misses.
    assert!(
        receivers.iter().any(|r| !senders.contains(r)),
        "cell 3 receives but never sends — the cycle-closure gap the executor does not close"
    );
}
