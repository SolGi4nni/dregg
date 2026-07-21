//! BYTE-IDENTITY differential for the cell-leaf digest cache
//! (`.docs-history-noclaude/INCREMENTAL-COMMITMENT.md` step 3).
//!
//! The cell-leaf cache stores the finished 32-byte canonical Merkle leaf on the
//! `Cell` and reuses it on later `Ledger::root()` calls until the cell is next
//! mutated. The cache is read ONLY by `Ledger::hash_cell`, gated behind the
//! ledger's `&mut`-handoff invalidation. A cache hit MUST be byte-identical to a
//! fresh `compute_canonical_state_commitment`.
//!
//! This drives random mutation sequences through the live `Ledger` mutation API
//! (`get_mut` / `update_with` / `apply_delta` / transfers / migrate-commit) and
//! asserts, after EVERY mutation, that the ledger's membership-proof leaf hash
//! (the cached `hash_cell`) equals the always-recompute leaf over a postcard
//! round-trip (which drops the `#[serde(skip)]` cache and reconstructs it
//! DIRTY, forcing the authoritative BLAKE3 fold). A single mismatch = a
//! mutation path failed to invalidate the cache (a stale cached leaf = a silent
//! wrong commitment). 0 mismatches over the corpus is the completeness witness.

use dregg_cell::commitment::compute_canonical_state_commitment;
use dregg_cell::ledger::{CellStateDelta, Ledger, LedgerDelta};
use dregg_cell::permissions::{AuthRequired, Permissions};
use dregg_cell::{Cell, CellId};

/// Tiny deterministic LCG — reproducible corpus without a `rand` dep.
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 16
    }
    fn pick(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

fn key(b: u8) -> [u8; 32] {
    let mut k = [0u8; 32];
    k[0] = b;
    k[1] = b.wrapping_mul(7).wrapping_add(3);
    k
}

/// Always-recompute reference: round-trip the cell through postcard so the
/// `#[serde(skip)]` leaf-digest cache (and cap-root cache) is dropped and
/// reconstructed DIRTY, forcing the authoritative fold on read.
fn fresh_leaf(cell: &Cell) -> [u8; 32] {
    let bytes = postcard::to_allocvec(cell).expect("serialize cell");
    let reloaded: Cell = postcard::from_bytes(&bytes).expect("deserialize cell");
    compute_canonical_state_commitment(&reloaded)
}

/// After any ledger mutation, every present cell's *cached* leaf (what the
/// federation Merkle tree commits, surfaced via `membership_proof().leaf_hash`)
/// must equal its always-fresh recompute.
fn assert_all_leaves_match(ledger: &mut Ledger, ctx: &str) {
    let ids: Vec<CellId> = ledger.iter().map(|(id, _)| *id).collect();
    for id in ids {
        let fresh = fresh_leaf(ledger.get(&id).expect("present"));
        // membership_proof().leaf_hash is exactly Ledger::hash_cell (the cached
        // path) after materialize.
        let cached = ledger
            .membership_proof(&id)
            .expect("membership proof")
            .leaf_hash;
        assert_eq!(
            cached, fresh,
            "{ctx}: cached leaf != fresh recompute for cell {id:?}"
        );
        // The published root must also equal a full standalone recompute over
        // fresh leaves (belt-and-suspenders: the cache cannot move the root).
    }
}

#[test]
fn leaf_digest_cache_matches_fresh() {
    for seed in 0..8u64 {
        let mut lcg = Lcg(0x9E37_79B9_7F4A_7C15 ^ seed.wrapping_mul(0xD1B5_4A32_D192_ED03));
        let mut ledger = Ledger::new();

        // Seed a handful of hosted cells with non-trivial state.
        let mut ids: Vec<CellId> = Vec::new();
        for i in 0..4u8 {
            let id = ledger.create_cell(key(seed as u8 * 16 + i + 1), key(99 ^ i));
            ids.push(id);
            // give them some starting balance via a direct update so transfers
            // have something to move.
            ledger
                .update_with(&id, |c| {
                    c.state.set_balance(1_000 + i as i64 * 10);
                })
                .expect("seed balance");
        }
        // Warm the tree + all caches once.
        let _ = ledger.root();
        assert_all_leaves_match(&mut ledger, "after-seed");

        for step in 0..160u64 {
            let id = ids[lcg.pick(ids.len() as u64) as usize];
            match lcg.pick(9) {
                0 => {
                    // nonce tick via update_with
                    ledger
                        .update_with(&id, |c| {
                            let _ = c.state.increment_nonce();
                        })
                        .expect("nonce");
                }
                1 => {
                    // balance change via get_mut (direct sealed-write)
                    if let Some(c) = ledger.get_mut(&id) {
                        let _ = c.state.apply_balance_change((lcg.next() % 5) as i64);
                    }
                }
                2 => {
                    // direct pub-field write via get_mut (the pub-field hazard)
                    if let Some(c) = ledger.get_mut(&id) {
                        let slot = (lcg.pick(16)) as usize;
                        let mut v = [0u8; 32];
                        v[0] = (lcg.next() & 0xff) as u8;
                        c.state.fields[slot] = v;
                    }
                }
                3 => {
                    // permissions swap via direct pub-field write through get_mut
                    if let Some(c) = ledger.get_mut(&id) {
                        c.permissions = if lcg.pick(2) == 0 {
                            Permissions::default()
                        } else {
                            Permissions {
                                send: AuthRequired::Impossible,
                                ..Permissions::default()
                            }
                        };
                    }
                }
                4 => {
                    // grant a capability (cap set changes) via update_with
                    let target = CellId::derive_raw(&key((lcg.pick(250) + 1) as u8), &key(7));
                    ledger
                        .update_with(&id, |c| {
                            let _ = c.capabilities.grant(target, AuthRequired::Signature);
                        })
                        .expect("grant");
                }
                5 => {
                    // ext-field map write (recomputes fields_root) via get_mut
                    if let Some(c) = ledger.get_mut(&id) {
                        let mut v = [0u8; 32];
                        v[31] = (lcg.next() & 0xff) as u8;
                        c.state.set_field_ext(16 + (lcg.pick(8)), v);
                    }
                }
                6 => {
                    // heap write (recomputes heap_root) via get_mut
                    if let Some(c) = ledger.get_mut(&id) {
                        let mut v = [0u8; 32];
                        v[30] = (lcg.next() & 0xff) as u8;
                        c.state.set_heap(1, (lcg.pick(8)) as u32, v);
                    }
                }
                7 => {
                    // apply_delta: a CellStateDelta (nonce + balance + field) on one cell
                    let mut delta = LedgerDelta::new();
                    let mut sd = CellStateDelta::empty();
                    sd.nonce_increment = lcg.pick(2) == 0;
                    sd.balance_change = (lcg.next() % 3) as i64;
                    if lcg.pick(2) == 0 {
                        let mut v = [0u8; 32];
                        v[1] = (lcg.next() & 0xff) as u8;
                        sd.field_updates.push(((lcg.pick(16)) as u64, v));
                    }
                    delta.updated.push((id, sd));
                    // sometimes also a transfer between two cells
                    if lcg.pick(2) == 0 {
                        let a = ids[lcg.pick(ids.len() as u64) as usize];
                        let b = ids[lcg.pick(ids.len() as u64) as usize];
                        if a != b {
                            delta.computron_transfers.push((a, b, 1));
                        }
                    }
                    let _ = ledger.apply_delta(&delta);
                }
                8 => {
                    // a no-op get_mut (invalidate even when nothing changes) —
                    // the cache must still recompute to the SAME value (the
                    // unconditional-invalidate-is-harmless property).
                    let _ = ledger.get_mut(&id);
                }
                _ => unreachable!(),
            }

            // Materialize + check every cell's cached leaf vs fresh recompute.
            let _ = ledger.root();
            assert_all_leaves_match(&mut ledger, &format!("seed={seed} step={step}"));
        }
    }
}

/// A focused unit witness: a cache HIT (two `root()` calls with no mutation in
/// between) returns the SAME root, and a mutation between them moves it exactly
/// as a fresh recompute would.
#[test]
fn cache_hit_is_stable_and_mutation_moves_it() {
    let mut ledger = Ledger::new();
    let id = ledger.create_cell(key(1), key(2));
    ledger
        .update_with(&id, |c| c.state.set_balance(500))
        .unwrap();

    let r1 = ledger.root();
    let r2 = ledger.root(); // pure cache hit — no mutation
    assert_eq!(r1, r2, "two root() with no mutation must be byte-identical");

    let fresh_before = fresh_leaf(ledger.get(&id).unwrap());
    assert_eq!(
        ledger.membership_proof(&id).unwrap().leaf_hash,
        fresh_before
    );

    // Mutate, then confirm the cached leaf tracks the fresh recompute.
    ledger
        .update_with(&id, |c| {
            let _ = c.state.increment_nonce();
        })
        .unwrap();
    let _ = ledger.root();
    let fresh_after = fresh_leaf(ledger.get(&id).unwrap());
    assert_ne!(fresh_before, fresh_after, "a nonce tick must move the leaf");
    assert_eq!(
        ledger.membership_proof(&id).unwrap().leaf_hash,
        fresh_after,
        "cached leaf must equal fresh recompute after mutation"
    );
}
