//! **THE ONE-FELT HEAP ADDRESS: a colliding pair's removal was invisible to the
//! signed anchor, and is now REFUSED.**
//!
//! `CellState::heap_map` is a `BTreeMap<(u32, u32), FieldElement>` — a 2^64 producer
//! key space. The committed leaf address is ONE felt,
//! `heap_addr(BabyBear::new(coll), BabyBear::new(key)) = hash_many([coll, key])`
//! (`circuit/src/heap_root.rs`), so the producer key → address map is not injective.
//! Until 2026-07-28 all four heap-tree builders answered a repeated address with a
//! silent `leaves.dedup_by_key(|l| l.addr.as_u32())`: one leaf was dropped, the
//! other committed, and NOTHING returned an error.
//!
//! The consequence is [`removal_of_a_merged_entry_was_invisible_to_the_anchor`]: with
//! two colliding entries present, REMOVING the merged-away one leaves the 8-felt root
//! — a component of the consensus anchor the executor signs — byte-identical. The
//! entry lives in `heap_map` and is absent from the commitment, so the root both
//! presents and denies it.
//!
//! ⚠ `as_u32()` is NOT a truncation and widening the dedup key is a NO-OP. `BabyBear`
//! is a canonical `u32` in `[0, p-1]` with `p = 2013265921 < 2^32`
//! (`circuit/src/field.rs`), so `as_u32()` already IS the whole felt. The address is
//! narrow because it is ONE ~31-bit felt, not because the dedup key was truncated.
//! The fix is therefore a REFUSAL, not a wider dedup.
//!
//! Two collision channels, both exercised below:
//!   * **A — mod-p aliasing, cost ZERO.** `BabyBear::new` reduces mod `BABYBEAR_P`,
//!     so `key` and `key + BABYBEAR_P` are distinct map keys at one address. No
//!     search. ⚑ The Lean model does not cover this: `Substrate/Heap.lean`'s
//!     `AddrPair = Fin babyBearP × Fin babyBearP` is the IN-RANGE pair and
//!     `truncAddr_inj` ("the truncation loses nothing") is stated for exactly those.
//!     The deployed `u32` domain is strictly wider than the modelled one.
//!   * **B — the birthday bound on a ~31-bit address**, for the in-range pairs the
//!     Lean model DOES cover. Measured below.

use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::heap_root::{
    CanonicalHeapTree, CanonicalHeapTree8, HEAP_TREE_DEPTH, HeapLeaf,
    compute_canonical_heap_root_8, compute_canonical_heap_root_8_entries, compute_heap_root,
    heap_addr,
};

/// A `(coll, key)` pair as the producer holds it — raw `u32`s, exactly the
/// `CellState::heap_map` key type.
type Pair = (u32, u32);

fn addr_of(p: Pair) -> BabyBear {
    heap_addr(BabyBear::new(p.0), BabyBear::new(p.1))
}

fn entries(ps: &[(Pair, u32)]) -> Vec<((BabyBear, BabyBear), BabyBear)> {
    ps.iter()
        .map(|((c, k), v)| ((BabyBear::new(*c), BabyBear::new(*k)), BabyBear::new(*v)))
        .collect()
}

/// **THE PRE-FIX BUILDER, VERBATIM** — the body every heap-tree builder had before
/// 2026-07-28: sentinel, sort, and the silent `dedup_by_key` that this campaign
/// deleted. Kept here as an in-test ORACLE (the same discipline `heap_root.rs`'s own
/// `dense_build` oracle uses) so the wound is demonstrated PERMANENTLY and in-value,
/// rather than resting on a git-history claim that decays.
///
/// Folds the 1-felt tree by hand — enough to show the ROOT does not move, which is
/// the whole content of the wound.
fn legacy_dedup_root(mut leaves: Vec<HeapLeaf>) -> BabyBear {
    use dregg_circuit::poseidon2::{hash_fact, hash_many};
    const DEPTH: usize = HEAP_TREE_DEPTH;
    // The MIN sentinel `{MIN, 0, MAX}`, as the builders prepend it.
    leaves.push(HeapLeaf {
        addr: BabyBear::ZERO,
        value: BabyBear::ZERO,
        next_addr: BabyBear(2013265920),
    });
    leaves.sort_by_key(|l| l.addr.as_u32());
    // ⚠ THE DELETED LINE. This is the wound.
    leaves.dedup_by_key(|l| l.addr.as_u32());
    // Relink the IMT chain (each leaf → successor's addr, last → SENTINEL_MAX).
    let n = leaves.len();
    for i in 0..n {
        leaves[i].next_addr = if i + 1 < n {
            leaves[i + 1].addr
        } else {
            BabyBear(2013265920)
        };
    }
    // Dense fold to the canonical depth.
    let mut level: Vec<BabyBear> = leaves.iter().map(|l| hash_many(&l.preimage())).collect();
    level.resize(1usize << DEPTH, BabyBear::ZERO);
    for _ in 0..DEPTH {
        level = level.chunks(2).map(|c| hash_fact(c[0], &[c[1]])).collect();
    }
    level[0]
}

// ===========================================================================
// THE COLLISION CHANNELS
// ===========================================================================

/// CHANNEL A: two distinct `(u32, u32)` map keys, ONE address, ZERO search.
#[test]
fn channel_a_mod_p_aliasing_costs_nothing() {
    let a: Pair = (1, 7);
    let b: Pair = (1, 7 + BABYBEAR_P); // 2013265928 — an ordinary u32

    assert_ne!(a, b, "distinct `BTreeMap<(u32,u32),_>` keys");
    assert_eq!(
        addr_of(a),
        addr_of(b),
        "mod-p aliasing must collapse two distinct u32 keys onto one address"
    );
    eprintln!(
        "CHANNEL A: {a:?} and {b:?} both address {} — no search performed",
        addr_of(a).as_u32()
    );
}

/// CHANNEL B: the birthday bound on a ~31-bit address, over the IN-RANGE pairs the
/// Lean model covers. Reports the work actually done.
#[test]
fn channel_b_birthday_collision_on_in_range_pairs() {
    use std::collections::HashMap;
    let mut seen: HashMap<u32, Pair> = HashMap::new();
    let mut tried = 0u64;
    let mut found = None;
    'outer: for coll in 0u32..64 {
        for key in 0u32..2_000_000 {
            tried += 1;
            match seen.insert(addr_of((coll, key)).as_u32(), (coll, key)) {
                Some(prev) if prev != (coll, key) => {
                    found = Some((prev, (coll, key)));
                    break 'outer;
                }
                _ => {}
            }
        }
    }
    let (p, q) = found.expect("a ~31-bit address space must collide inside this budget");
    eprintln!(
        "CHANNEL B: {tried} folds found IN-RANGE pairs {p:?} and {q:?} at address {}",
        addr_of(p).as_u32()
    );
    assert_ne!(p, q, "the colliding pairs are genuinely distinct");
    assert!(
        p.0 < BABYBEAR_P && p.1 < BABYBEAR_P && q.0 < BABYBEAR_P && q.1 < BABYBEAR_P,
        "both pairs are IN-RANGE, so this channel survives any u32 range check"
    );
    assert_eq!(addr_of(p), addr_of(q), "one address");
    assert!(
        tried < 1_000_000,
        "the birthday price must be measured, not assumed: {tried} folds"
    );
}

// ===========================================================================
// POLE 1 — THE WOUND, DRIVEN, AND ITS CLOSURE
// ===========================================================================

/// **THE DRIVEN COLLISION.** Against the PRE-FIX builder the anchor does not move
/// when the merged-away entry is removed; against the DEPLOYED builder the same
/// input is refused outright.
#[test]
fn removal_of_a_merged_entry_was_invisible_to_the_anchor() {
    let a: Pair = (1, 7);
    let b: Pair = (1, 7 + BABYBEAR_P);
    assert_eq!(addr_of(a), addr_of(b), "the fixture must actually collide");

    let both = vec![
        HeapLeaf::entry(addr_of(a), BabyBear::new(11)),
        HeapLeaf::entry(addr_of(b), BabyBear::new(22)),
    ];
    let only_a = vec![HeapLeaf::entry(addr_of(a), BabyBear::new(11))];

    // ── PRE-FIX: the removal is invisible. ──
    let legacy_both = legacy_dedup_root(both.clone());
    let legacy_after_removing_b = legacy_dedup_root(only_a.clone());
    eprintln!(
        "PRE-FIX  root{{A,B}} = {}   root{{A}} = {}",
        legacy_both.as_u32(),
        legacy_after_removing_b.as_u32()
    );
    assert_eq!(
        legacy_both, legacy_after_removing_b,
        "THE WOUND: under the deleted `dedup_by_key`, removing the merged-away entry \
         B left the committed root byte-identical — the removal was invisible to the \
         signed anchor. If this assertion ever fails the oracle has drifted from the \
         code it transcribes and the demonstration is worthless."
    );

    // ── POST-FIX: the same input is REFUSED, at every builder. ──
    for (name, refused) in [
        (
            "compute_canonical_heap_root_8",
            std::panic::catch_unwind(|| compute_canonical_heap_root_8(both.clone())).is_err(),
        ),
        (
            "CanonicalHeapTree::new",
            std::panic::catch_unwind(|| CanonicalHeapTree::new(both.clone(), HEAP_TREE_DEPTH))
                .is_err(),
        ),
        (
            "CanonicalHeapTree8::new",
            std::panic::catch_unwind(|| CanonicalHeapTree8::new(both.clone(), HEAP_TREE_DEPTH))
                .is_err(),
        ),
        (
            "compute_canonical_heap_root_8_entries",
            std::panic::catch_unwind(|| {
                compute_canonical_heap_root_8_entries(&entries(&[(a, 11), (b, 22)]))
            })
            .is_err(),
        ),
    ] {
        assert!(
            refused,
            "{name} must REFUSE two leaves at one address, not silently merge them"
        );
        eprintln!("POST-FIX: {name} refused the colliding pair");
    }
}

/// The CHANNEL B (in-range, birthday) pair is refused too — the guard is not
/// keyed on the mod-p channel, it is keyed on the address.
#[test]
fn the_in_range_birthday_pair_is_refused_as_well() {
    use std::collections::HashMap;
    let mut seen: HashMap<u32, Pair> = HashMap::new();
    let mut found = None;
    'outer: for coll in 0u32..64 {
        for key in 0u32..2_000_000 {
            match seen.insert(addr_of((coll, key)).as_u32(), (coll, key)) {
                Some(prev) if prev != (coll, key) => {
                    found = Some((prev, (coll, key)));
                    break 'outer;
                }
                _ => {}
            }
        }
    }
    let (p, q) = found.expect("collision");
    let leaves = vec![
        HeapLeaf::entry(addr_of(p), BabyBear::new(1)),
        HeapLeaf::entry(addr_of(q), BabyBear::new(2)),
    ];
    // Pre-fix, this pair merged exactly like the mod-p one.
    assert_eq!(
        legacy_dedup_root(leaves.clone()),
        legacy_dedup_root(vec![HeapLeaf::entry(addr_of(p), BabyBear::new(1))]),
        "the in-range birthday pair merged under the deleted dedup too"
    );
    assert!(
        std::panic::catch_unwind(|| compute_canonical_heap_root_8(leaves)).is_err(),
        "the in-range birthday pair must be refused"
    );
}

// ===========================================================================
// POLE 2 — HONEST TRAFFIC STILL WORKS
// ===========================================================================

/// Non-colliding traffic commits, and — the property the wound destroyed — a
/// removal MOVES the anchor.
#[test]
fn honest_traffic_commits_and_its_removal_moves_the_anchor() {
    let full: Vec<(Pair, u32)> = vec![
        ((1, 1), 10),
        ((1, 2), 20),
        ((2, 1), 30),
        ((7, 99), 40),
        ((0, 0), 50),
    ];
    // Every address distinct — honest traffic.
    let mut addrs: Vec<u32> = full.iter().map(|(p, _)| addr_of(*p).as_u32()).collect();
    addrs.sort_unstable();
    let before_dedup = addrs.len();
    addrs.dedup();
    assert_eq!(
        before_dedup,
        addrs.len(),
        "the honest fixture must not collide"
    );

    let root_full = compute_canonical_heap_root_8_entries(&entries(&full));

    // Removing ANY one entry must move the anchor.
    for drop_idx in 0..full.len() {
        let mut reduced = full.clone();
        let dropped = reduced.remove(drop_idx);
        let root_reduced = compute_canonical_heap_root_8_entries(&entries(&reduced));
        assert_ne!(
            root_full, root_reduced,
            "removing {dropped:?} must move the committed root"
        );
    }

    // ⚑ NO RE-EMIT. For every input the pre-fix builder accepted with distinct
    // addresses, `dedup_by_key` was a no-op, so the committed value is UNCHANGED by
    // this fix. Asserted against the verbatim pre-fix oracle rather than argued:
    // nothing must be re-emitted, re-genesised, or VK-rotated.
    let honest_leaves: Vec<HeapLeaf> = full
        .iter()
        .map(|(p, v)| HeapLeaf::entry(addr_of(*p), BabyBear::new(*v)))
        .collect();
    assert_eq!(
        legacy_dedup_root(honest_leaves.clone()),
        compute_heap_root(honest_leaves.clone()),
        "the committed root for honest (distinct-address) traffic must be BYTE-IDENTICAL \
         to the pre-fix builder — this fix refuses inputs, it does not move values"
    );

    // And the ordinary builders accept the whole set at both widths.
    let leaves: Vec<HeapLeaf> = full
        .iter()
        .map(|(p, v)| HeapLeaf::entry(addr_of(*p), BabyBear::new(*v)))
        .collect();
    let t1 = CanonicalHeapTree::new(leaves.clone(), HEAP_TREE_DEPTH);
    let t8 = CanonicalHeapTree8::new(leaves.clone(), HEAP_TREE_DEPTH);
    assert_eq!(
        t1.num_entries(),
        full.len(),
        "every honest entry is committed — none merged away"
    );
    assert_eq!(t8.root8(), compute_canonical_heap_root_8(leaves));
    // A membership opening exists for every honest key.
    for (p, _) in &full {
        assert!(
            t1.position_of(addr_of(*p)).is_some(),
            "honest key {p:?} must be openable"
        );
    }
}

/// The empty heap and a single-entry heap — the degenerate ends — still build.
#[test]
fn degenerate_heaps_still_build() {
    let empty = compute_canonical_heap_root_8(Vec::new());
    let one =
        compute_canonical_heap_root_8(vec![HeapLeaf::entry(addr_of((3, 4)), BabyBear::new(42))]);
    assert_ne!(empty, one, "one entry is not the empty heap");
}

// ===========================================================================
// ⚑ THE SEVERE HALF — THE SAME TREE, ADDRESSED BY AN ATTACKER-CHOSEN FOLD
// ===========================================================================

/// ⚑ The heap's `(coll, key)` addresses are NOT attacker-chosen (every production
/// collection is a `const` and every key is a `const` or `const + loop index`), so
/// for the heap this wound is an ACCIDENT, not a forgery primitive.
///
/// The note-commitment / shielded-note / nullifier / revoked accumulators are the
/// SAME `CanonicalHeapTree8` and shared the SAME deleted `dedup_by_key`, but their
/// leaf ADDRESS is `fold_bytes32_to_bb(commitment)` — a 256→31-bit Horner fold of a
/// value the counterparty derives from secrets it chooses. There the colliding pair
/// IS grindable offline, which is what separates the two halves of this finding by
/// orders of magnitude.
///
/// This test measures that price rather than asserting it, and shows the deleted
/// dedup made an accumulator INSERT a no-op on the committed root.
#[test]
fn accumulator_fold_collision_is_cheap_and_was_a_silent_no_op() {
    use dregg_circuit::effect_vm::fold_bytes32_to_bb;
    use std::collections::HashMap;

    // Grind BLAKE3 IMAGES, because a real nullifier / note commitment is a hash
    // output rather than a freely-chosen string: the attacker varies note secrets
    // offline and keeps the pair whose committed addresses coincide. (Varying a
    // single 4-byte limb below `p` would be injective and never collide — the fold
    // is linear, so the search has to move the hash image, not one limb.)
    let mut seen: HashMap<u32, [u8; 32]> = HashMap::new();
    let mut tried = 0u64;
    let mut pair = None;
    for i in 0u64..5_000_000 {
        tried += 1;
        let b: [u8; 32] = *blake3::hash(&i.to_le_bytes()).as_bytes();
        if let Some(prev) = seen.insert(fold_bytes32_to_bb(&b).as_u32(), b) {
            if prev != b {
                pair = Some((prev, b));
                break;
            }
        }
    }
    let (n1, n2) = pair.expect("a ~31-bit fold must collide inside this budget");
    assert_ne!(n1, n2, "two DISTINCT 32-byte accumulator entries");
    assert_eq!(
        fold_bytes32_to_bb(&n1),
        fold_bytes32_to_bb(&n2),
        "one committed address"
    );
    eprintln!(
        "ACCUMULATOR: {tried} folds found two distinct 32-byte entries at address {} \
         (offline, no chain interaction)",
        fold_bytes32_to_bb(&n1).as_u32()
    );

    // PRE-FIX: inserting the SECOND one did not move the committed root.
    let leaf = |b: &[u8; 32]| HeapLeaf::entry(fold_bytes32_to_bb(b), BabyBear::new(1));
    assert_eq!(
        legacy_dedup_root(vec![leaf(&n1)]),
        legacy_dedup_root(vec![leaf(&n1), leaf(&n2)]),
        "THE WOUND, at the accumulator: under the deleted dedup, adding a second \
         distinct entry whose fold collides left the committed accumulator root \
         byte-identical — the insert was a no-op on the commitment"
    );

    // POST-FIX: refused, loudly.
    assert!(
        std::panic::catch_unwind(|| compute_canonical_heap_root_8(vec![leaf(&n1), leaf(&n2)]))
            .is_err(),
        "the accumulator must refuse two entries at one committed address"
    );
}

/// ⚑ THE SENTINEL LEG, closed by the same guard. The MIN sentinel is PUSHED LAST and
/// `sort_by_key` is stable, so under the deleted dedup a real leaf at `addr == 0`
/// sorted first and the GENESIS SENTINEL was the leaf silently dropped. The tree then
/// had no `{MIN, 0, MAX}` node at all, and every non-membership opening that straddles
/// the low bracket rests on it.
#[test]
fn a_real_leaf_at_the_min_sentinel_no_longer_evicts_the_sentinel() {
    let at_min = vec![HeapLeaf::entry(BabyBear::ZERO, BabyBear::new(9))];

    /// The same dense fold as the oracle but with NO sentinel prepended at all —
    /// what the tree looks like once the genesis sentinel has been evicted.
    fn root_without_any_sentinel(leaves: &[HeapLeaf]) -> BabyBear {
        use dregg_circuit::poseidon2::{hash_fact, hash_many};
        let mut level: Vec<BabyBear> = leaves
            .iter()
            .map(|l| hash_many(&[l.addr, l.value, BabyBear(2013265920)]))
            .collect();
        level.resize(1usize << HEAP_TREE_DEPTH, BabyBear::ZERO);
        for _ in 0..HEAP_TREE_DEPTH {
            level = level.chunks(2).map(|c| hash_fact(c[0], &[c[1]])).collect();
        }
        level[0]
    }

    // PRE-FIX: the committed tree is BYTE-IDENTICAL to one with no genesis sentinel
    // at all — i.e. the dedup dropped the sentinel, not the real leaf (the real leaf
    // is pushed first and `sort_by_key` is stable, so it wins the tie).
    assert_eq!(
        legacy_dedup_root(at_min.clone()),
        root_without_any_sentinel(&at_min),
        "THE SENTINEL LEG: under the deleted dedup a real leaf at address 0 EVICTED \
         the genesis MIN sentinel — the committed root is that of a sentinel-less tree"
    );
    // ...and that is NOT what an honest single-entry heap commits.
    let honest = vec![HeapLeaf::entry(addr_of((3, 4)), BabyBear::new(9))];
    assert_ne!(
        legacy_dedup_root(honest.clone()),
        root_without_any_sentinel(&honest),
        "non-vacuity: for a NON-colliding leaf the sentinel is present, so the two \
         folds differ — the assertion above is detecting eviction, not an identity"
    );

    // POST-FIX: refused.
    assert!(
        std::panic::catch_unwind(|| compute_canonical_heap_root_8(at_min)).is_err(),
        "a live leaf AT SENTINEL_MIN must be refused, not silently allowed to evict \
         the genesis sentinel"
    );
}
