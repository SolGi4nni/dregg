//! Synthetic committed turns — the demonstration substrate (postgres-free).
//!
//! The real Tier-B writer (M2) tails the node's commit log and projects each
//! `dregg_cell::Cell` post-image into a [`MirrorBatch`](crate::mirror::MirrorBatch)
//! (see `docs/PG-DREGG.md` §9.1: "the mirror is a projection of an artifact that
//! already exists"). That writer needs `node/` + `dregg-cell` and is queued
//! behind the rotation lane.
//!
//! This module stands in for it with *synthetic* but **structurally faithful**
//! batches: a hand-built sequence of committed turns (a genesis funding, a
//! transfer, a capability grant, an organ op) whose rows have exactly the shape
//! the node's projection produces, and whose `prev_root`/`ledger_root` form a
//! real hash chain the [`RootChain`](crate::mirror::RootChain) tooth accepts.
//!
//! It is the SINGLE source of demo data, shared by:
//!
//!   * `examples/end_to_end.rs` (the `cargo run --example` artifact), and
//!   * the `#[pg_test]`s in [`crate`] (run against real pg18),
//!
//! so the postgres-free demo and the through-SQL demo cannot drift.
//!
//! Nothing here is circuit-backed or node-linked: the roots are BLAKE3 hashes of
//! the batch contents (a stand-in for the kernel's `ledger_root`), chained
//! exactly as the real roots chain. That is enough to exercise the mirror's
//! whole write path (`check_ordinals` → `RootChain::extend`) and to populate the
//! Tier-B tables for the RLS-narrowing query.

use crate::mirror::{CapRow, CellRow, Domain, MemCell, MirrorBatch, TurnRow};

/// The genesis ledger root the chain is pinned to (the all-zero root; a real
/// deployment pins the kernel's genesis commitment here).
pub const GENESIS_ROOT: [u8; 32] = [0u8; 32];

/// Three demo cell ids. They double as the RLS *resources*: a cap token gates
/// `read` on `encode(cell_id,'hex')`, so attenuating a token to a cell-id
/// prefix narrows exactly which `dregg.cells` rows a reader sees.
pub const TREASURY: [u8; 32] = cell_id(0xc0);
pub const ALICE: [u8; 32] = cell_id(0xa1);
pub const BOB: [u8; 32] = cell_id(0xb0);

/// A readable, prefix-stable cell id: first byte is the tag, the rest fixed.
/// The leading byte makes the hex string start `c0…`, `a1…`, `b0…`, so a token
/// attenuated to the prefix `"a1"` admits ALICE and nothing else.
const fn cell_id(tag: u8) -> [u8; 32] {
    let mut id = [0x11u8; 32];
    id[0] = tag;
    id
}

/// A tiny BLAKE3-free content root: the FNV-1a-ish fold of the batch's defining
/// fields. NOT cryptographic — a deterministic stand-in for the kernel's
/// `ledger_root` so the chain links without pulling a hash crate. (The real
/// `ledger_root` is the kernel commitment; the mirror only needs *some* stable
/// per-state value that the next turn's `prev_root` must equal.)
fn fold_root(prev: [u8; 32], ordinal: u64, cells: &[CellRow]) -> [u8; 32] {
    let mut acc: u64 = 0xcbf29ce484222325 ^ ordinal.wrapping_mul(0x100000001b3);
    for b in prev {
        acc = (acc ^ b as u64).wrapping_mul(0x100000001b3);
    }
    for c in cells {
        for b in c.cell_id {
            acc = (acc ^ b as u64).wrapping_mul(0x100000001b3);
        }
        acc = (acc ^ c.balance as u64).wrapping_mul(0x100000001b3);
        acc = (acc ^ c.nonce).wrapping_mul(0x100000001b3);
    }
    let mut out = [0u8; 32];
    for (i, chunk) in out.chunks_mut(8).enumerate() {
        let v = acc.wrapping_add((i as u64).wrapping_mul(0x9e3779b97f4a7c15));
        chunk.copy_from_slice(&v.to_le_bytes());
    }
    out
}

fn cell(id: [u8; 32], balance: i64, nonce: u64, ordinal: u64) -> CellRow {
    CellRow {
        cell_id: id,
        mode: "Hosted".into(),
        balance,
        nonce,
        fields: vec![],
        fields_json: Some(format!("{{\"balance\":{balance},\"nonce\":{nonce}}}")),
        heap: None,
        program: None,
        verification_key: None,
        permissions_json: Some("{\"transfer\":\"owner\"}".into()),
        delegate: None,
        lifecycle: "Active".into(),
        last_ordinal: ordinal,
        cell_root: id, // a stand-in commitment; the real one is recStateCommit
    }
}

/// A memory-domain projection of a register write, so `dregg.memory` (the
/// universal table) is populated alongside the typed `dregg.cells` view — both
/// halves of the docs §9.4 / §5 model are exercised.
fn balance_reg(id: [u8; 32], balance: i64, ordinal: u64) -> MemCell {
    MemCell {
        domain: Domain::Registers,
        collection: id.to_vec(),
        key: b"balance".to_vec(),
        value: Some(balance.to_le_bytes().to_vec()),
        last_ordinal: ordinal,
    }
}

fn turn_row(ordinal: u64, prev: [u8; 32], post: [u8; 32], creator: [u8; 32]) -> TurnRow {
    TurnRow {
        ordinal,
        height: ordinal,
        block_id: {
            let mut b = [0x22u8; 32];
            b[0] = ordinal as u8;
            b
        },
        block_executed_up_to: ordinal,
        turn_hash: {
            let mut b = [0x33u8; 32];
            b[0] = ordinal as u8;
            b
        },
        creator,
        receipt_hash: {
            let mut b = [0x44u8; 32];
            b[0] = ordinal as u8;
            b
        },
        ledger_root: post,
        prev_root: prev,
    }
}

/// One synthetic turn, carrying the post-image of the cells it touched. The
/// helper computes the post root from `prev` + the touched cells so the chain
/// links by construction.
fn make_batch(
    ordinal: u64,
    prev: [u8; 32],
    creator: [u8; 32],
    cells: Vec<CellRow>,
    caps: Vec<CapRow>,
) -> MirrorBatch {
    let post = fold_root(prev, ordinal, &cells);
    let memory: Vec<MemCell> = cells
        .iter()
        .map(|c| balance_reg(c.cell_id, c.balance, ordinal))
        .collect();
    MirrorBatch {
        turn: turn_row(ordinal, prev, post, creator),
        cells,
        caps,
        memory,
    }
}

/// The synthetic ledger story, as a chain of committed turns:
///
/// | ord | turn          | effect                                            |
/// |-----|---------------|---------------------------------------------------|
/// | 0   | genesis       | TREASURY funded to 1_000_000                       |
/// | 1   | transfer      | TREASURY → ALICE 400, TREASURY → BOB 100          |
/// | 2   | grant         | ALICE grants BOB a capability (slot 0)            |
/// | 3   | organ op      | ALICE seals a field (a channel/organ-style op)    |
///
/// Conservation holds across the transfer (the three post-balances sum to the
/// genesis total). The returned batches chain: batch *n+1*'s `prev_root` is
/// batch *n*'s `ledger_root`, with batch 0 pinned to [`GENESIS_ROOT`].
pub fn ledger_story() -> Vec<MirrorBatch> {
    let mut out = Vec::new();

    // ord 0 — genesis: TREASURY funded.
    let b0 = make_batch(
        0,
        GENESIS_ROOT,
        TREASURY,
        vec![cell(TREASURY, 1_000_000, 0, 0)],
        vec![],
    );
    let r0 = b0.turn.ledger_root;
    out.push(b0);

    // ord 1 — transfer: TREASURY pays ALICE 400 and BOB 100 (conservation: the
    // three post-balances sum to 1_000_000).
    let b1 = make_batch(
        1,
        r0,
        TREASURY,
        vec![
            cell(TREASURY, 999_500, 1, 1),
            cell(ALICE, 400, 0, 1),
            cell(BOB, 100, 0, 1),
        ],
        vec![],
    );
    let r1 = b1.turn.ledger_root;
    out.push(b1);

    // ord 2 — grant: ALICE installs a capability to BOB at slot 0. The cap row
    // (the delegation edge) lands in dregg.capabilities / the cap_edges view.
    let grant_cap = CapRow {
        holder: ALICE,
        slot: 0,
        target: BOB,
        permissions_json: "{\"transfer\":\"delegated\"}".into(),
        breadstuff: None,
        expires_at: Some(10_000),
        allowed_effects_json: Some("[\"transfer\"]".into()),
        stored_epoch: Some(0),
        last_ordinal: 2,
    };
    let b2 = make_batch(2, r1, ALICE, vec![cell(ALICE, 400, 1, 2)], vec![grant_cap]);
    let r2 = b2.turn.ledger_root;
    out.push(b2);

    // ord 3 — organ op: ALICE seals a field slot (an organ/channel-style state
    // mutation that bumps the nonce and rewrites a register). This exercises a
    // non-transfer effect in the mirror.
    let b3 = make_batch(3, r2, ALICE, vec![cell(ALICE, 400, 2, 3)], vec![]);
    out.push(b3);

    out
}

/// A TAMPERED batch: the same ordinal-2 turn but with a substituted `prev_root`
/// (as if an attacker reordered / forged it). The [`RootChain`](crate::mirror::RootChain)
/// tooth must REFUSE it — that is the anti-substitution demonstration.
pub fn tampered_batch_at_2() -> MirrorBatch {
    let mut b = make_batch(
        2,
        [0x99u8; 32],
        ALICE,
        vec![cell(ALICE, 999_999, 1, 2)],
        vec![],
    );
    // also flip the ordinal-stamp on a row to show check_ordinals (uncomment to
    // exercise the Malformed path); here we keep the RootMismatch path clean.
    b.turn.prev_root = [0x99u8; 32];
    b
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mirror::{ChainRefusal, RootChain};

    #[test]
    fn the_story_chains_and_conserves() {
        let story = ledger_story();
        assert_eq!(story.len(), 4);

        // It chains through the RootChain tooth from a pinned genesis.
        let mut chain = RootChain::resume(GENESIS_ROOT, 0);
        for b in &story {
            chain.extend(b).expect("the synthetic story must chain");
        }
        assert_eq!(chain.next_ordinal(), 4);

        // Conservation across the transfer turn (ord 1): the three post-balances
        // sum to the genesis total.
        let transfer = &story[1];
        let total: i64 = transfer.cells.iter().map(|c| c.balance).sum();
        assert_eq!(total, 1_000_000, "transfer must conserve value");

        // The grant turn carries the delegation edge.
        assert_eq!(story[2].caps.len(), 1);
        assert_eq!(story[2].caps[0].holder, ALICE);
        assert_eq!(story[2].caps[0].target, BOB);
    }

    #[test]
    fn the_tampered_batch_is_refused() {
        let story = ledger_story();
        let mut chain = RootChain::resume(GENESIS_ROOT, 0);
        chain.extend(&story[0]).unwrap();
        chain.extend(&story[1]).unwrap();
        // Now a tampered ordinal-2 batch (substituted prev_root) is REFUSED, and
        // the chain head does not move.
        let head_before = chain.head();
        let err = chain.extend(&tampered_batch_at_2()).unwrap_err();
        assert!(matches!(err, ChainRefusal::RootMismatch { .. }));
        assert_eq!(
            chain.head(),
            head_before,
            "a tampered batch cannot move the head"
        );
    }

    #[test]
    fn cell_ids_are_prefix_distinct_for_rls() {
        // The RLS-narrowing story relies on the hex cell ids being prefix-
        // distinct: a token attenuated to prefix "a1" must admit ALICE only.
        let hx = |id: [u8; 32]| -> String { id.iter().map(|b| format!("{b:02x}")).collect() };
        assert!(hx(ALICE).starts_with("a1"));
        assert!(hx(BOB).starts_with("b0"));
        assert!(hx(TREASURY).starts_with("c0"));
    }
}
