//! # The grain `/var` one-felt leaf: OLD ADMITS, NEW REJECTS — with a real collision.
//!
//! ## The wound, at the site the census named and did not close
//!
//! Until 2026-08-03 a grain's `/var` committed one [`HeapLeaf`] per entry:
//!
//! ```text
//!   addr  = hash_bytes(b"grain/var/addr:v1\0"  ‖ key)        -- ONE felt
//!   value = hash_bytes(b"grain/var/value:v1\0" ‖ value)      -- ONE felt
//!   root  = felt_to_bytes32(compute_heap_root(leaves))       -- ONE felt, lane 0
//! ```
//!
//! and [`sandstorm_bridge::cell::verify_inclusion`] recomputed that leaf from the served
//! `{key, value}` and folded a 1-felt `hash_fact` path to the root. The value felt was the
//! **only** binding of an arbitrary-length `/var` blob, so with `log2 p = 30.906891` a
//! hostile hosting server could serve a *different card* under the owner's honestly-signed
//! root by finding one collision — `2^15.4534` ≈ 44,900 Poseidon2 evaluations, milliseconds.
//!
//! That is not the NUL-append `O(1)` preimage ambiguity closed in
//! `var_nul_append_inclusion_forgery.rs`; it is the 31-bit codomain that file's
//! `the_one_felt_leaf_is_still_the_open_one` pinned as the OPEN one and said to delete when
//! the leaf widened. This file is that deletion, and it exhibits the collision rather than
//! asserting the bound.
//!
//! ## What this file establishes
//!
//! * [`old_admitted_a_searched_card_swap`] — the RETIRED construction, reproduced here
//!   byte-for-byte and driven end to end: a real collision found by deterministic search
//!   over genuinely well-formed grain settings cards, and the retired verifier ACCEPTING
//!   the wrong card at the honest key under the honest root. The forgery, exhibited.
//! * [`new_rejects_the_same_card_swap`] — the deployed eight-lane commitment REFUSES the
//!   same pair at the real [`verify_inclusion`], while the honest card still verifies.
//! * [`completeness_every_honest_entry_still_opens`] — the widening is not a DoS: every
//!   honest entry across many lengths still proves and verifies, and the root stays
//!   insert-order-free.
//! * [`the_bound_is_derived_not_remembered`] — the two figures, computed from `p` at run
//!   time, and the COLLISION one named as the governing figure.
//!
//! ⚠ The bound that governs here is the **collision** one. A hostile host chooses BOTH
//! sides — the card it commits and the card it later serves — so it never faces the second
//! preimage. Retired: `2^15.4534`. Deployed: `2^123.6276`.

use std::collections::HashMap;
use std::time::Instant;

use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::{
    compute_heap_root, CanonicalHeapTree, HeapLeaf, HEAP_TREE_DEPTH, SENTINEL_MAX,
};
use dregg_circuit::poseidon2::{hash_bytes, hash_fact};
use sandstorm_bridge::cell::{var_leaf_digest8, verify_inclusion, Umem, VAR_LANES};

// ===========================================================================
// THE RETIRED CONSTRUCTION, reproduced. A negative witness must keep exhibiting
// the defect it names after the implementation is gone (the same discipline
// `var_nul_append_inclusion_forgery.rs::retired_packed_limbs` follows).
// ===========================================================================

const RETIRED_ADDR_DOMAIN: &[u8] = b"grain/var/addr:v1\0";
const RETIRED_VALUE_DOMAIN: &[u8] = b"grain/var/value:v1\0";

fn tagged(domain: &[u8], rest: &[u8]) -> Vec<u8> {
    let mut buf = Vec::with_capacity(domain.len() + rest.len());
    buf.extend_from_slice(domain);
    buf.extend_from_slice(rest);
    buf
}

/// The retired `sandstorm_bridge::cell::var_addr`.
fn retired_var_addr(key: &str) -> BabyBear {
    hash_bytes(&tagged(RETIRED_ADDR_DOMAIN, key.as_bytes()))
}

/// The retired `sandstorm_bridge::cell::var_value_felt` — the ONE felt that was the whole
/// binding of an arbitrary-length `/var` blob.
fn retired_var_value_felt(value: &[u8]) -> BabyBear {
    hash_bytes(&tagged(RETIRED_VALUE_DOMAIN, value))
}

/// The retired `sandstorm_bridge::cell::felt_to_bytes32` (lane 0, rest zero).
fn retired_felt_to_bytes32(felt: BabyBear) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[0..4].copy_from_slice(&felt.as_u32().to_le_bytes());
    out
}

/// The retired one-leaf-per-entry leaf set.
fn retired_leaves(entries: &[(String, Vec<u8>)]) -> Vec<HeapLeaf> {
    entries
        .iter()
        .map(|(k, v)| HeapLeaf::entry(retired_var_addr(k), retired_var_value_felt(v)))
        .collect()
}

/// The retired `Umem::commit_root_bytes`.
fn retired_root_bytes(entries: &[(String, Vec<u8>)]) -> [u8; 32] {
    retired_felt_to_bytes32(compute_heap_root(retired_leaves(entries)))
}

/// The retired `InclusionProof`.
struct RetiredProof {
    next_addr: BabyBear,
    siblings: Vec<BabyBear>,
    directions: Vec<u8>,
}

/// The retired `Umem::prove`.
fn retired_prove(entries: &[(String, Vec<u8>)], key: &str) -> Option<RetiredProof> {
    let tree = CanonicalHeapTree::new(retired_leaves(entries), HEAP_TREE_DEPTH);
    let pos = tree.position_of(retired_var_addr(key))?;
    let (siblings, directions) = tree.prove_membership(pos)?;
    Some(RetiredProof {
        next_addr: tree.sorted_leaves()[pos].next_addr,
        siblings,
        directions,
    })
}

/// The retired `verify_inclusion` — the 1-felt `hash_fact` fold to a lane-0 root.
fn retired_verify_inclusion(
    root: &[u8; 32],
    key: &str,
    value: &[u8],
    proof: &RetiredProof,
) -> bool {
    if proof.siblings.len() != proof.directions.len() {
        return false;
    }
    let mut leaf = HeapLeaf::entry(retired_var_addr(key), retired_var_value_felt(value));
    leaf.next_addr = proof.next_addr;
    if leaf.addr.as_u32() >= leaf.next_addr.as_u32() {
        return false;
    }
    let mut acc = leaf.digest();
    for (sib, &dir) in proof.siblings.iter().zip(proof.directions.iter()) {
        acc = if dir == 0 {
            hash_fact(acc, &[*sib])
        } else {
            hash_fact(*sib, &[acc])
        };
    }
    retired_felt_to_bytes32(acc) == *root
}

// ===========================================================================
// THE SEARCH — genuinely well-formed grain settings cards.
// ===========================================================================

/// A plausible `/var` settings card a real grain would store at `settings.json`: the only
/// varying part is a visit counter an app legitimately increments. Both members of the
/// colliding pair are cards the grain could honestly have written; neither is a blob of
/// tuned bytes.
fn settings_card(visits: u64) -> Vec<u8> {
    format!("{{\"theme\":\"dark\",\"tz\":\"UTC\",\"visits\":{visits}}}").into_bytes()
}

/// Deterministic search for two distinct well-formed cards sharing the retired value felt.
/// Returns `(a, b, evaluations)` — the search is a plain scan from `visits = 0`, so it is
/// reproducible and its cost is the reported count, not a seed's luck.
fn search_retired_value_collision() -> (u64, u64, u64) {
    let mut seen: HashMap<u32, u64> = HashMap::new();
    let mut evaluations: u64 = 0;
    for visits in 0u64.. {
        evaluations += 1;
        let felt = retired_var_value_felt(&settings_card(visits)).as_u32();
        if let Some(&prior) = seen.get(&felt) {
            return (prior, visits, evaluations);
        }
        seen.insert(felt, visits);
    }
    unreachable!("the pigeonhole guarantees a collision within p+1 evaluations")
}

/// A second `/var` entry so the exhibit runs over a heap with real bracketing neighbours,
/// not a degenerate single-leaf tree.
const OTHER_KEY: &str = "card/index.html";
const OTHER_VALUE: &[u8] = b"<!doctype html><title>grain</title><p>hello";
const CARD_KEY: &str = "settings.json";

#[test]
fn old_admitted_a_searched_card_swap() {
    let started = Instant::now();
    let (a, b, evaluations) = search_retired_value_collision();
    let elapsed = started.elapsed();
    let card_a = settings_card(a);
    let card_b = settings_card(b);

    // The pair is REAL: two distinct, well-formed cards on one retired value felt.
    assert_ne!(card_a, card_b, "the two cards genuinely differ");
    assert_eq!(
        retired_var_value_felt(&card_a),
        retired_var_value_felt(&card_b),
        "the retired one-felt value binding conflates them"
    );
    println!(
        "collision on the retired /var value felt: visits={a} vs visits={b} \
         ({evaluations} evaluations, {elapsed:?})\n  A = {}\n  B = {}",
        String::from_utf8_lossy(&card_a),
        String::from_utf8_lossy(&card_b),
    );

    // ⚑ THE FORGERY, DRIVEN END TO END AT THE RETIRED VERIFIER. The grain honestly commits
    // card A; the owner signs that root. The hostile host serves card B with the honest
    // proof, and the retired verifier ACCEPTS it.
    let honest: Vec<(String, Vec<u8>)> = vec![
        (CARD_KEY.to_string(), card_a.clone()),
        (OTHER_KEY.to_string(), OTHER_VALUE.to_vec()),
    ];
    let root = retired_root_bytes(&honest);
    let proof = retired_prove(&honest, CARD_KEY).expect("the key is present");

    // ANTI-VACUITY: the honest card verifies, or "admitted" would mean nothing.
    assert!(
        retired_verify_inclusion(&root, CARD_KEY, &card_a, &proof),
        "ANTI-VACUITY: the honest card must verify at the retired verifier"
    );
    // Baseline: an ARBITRARY wrong card is refused — the retired verifier was not simply
    // broken, it was 31-bit bound. This is what makes the acceptance below a COLLISION
    // result and not a trivially-accepting verifier.
    assert!(
        !retired_verify_inclusion(&root, CARD_KEY, &settings_card(a + 1), &proof),
        "the retired verifier must refuse an unsearched wrong card"
    );

    assert!(
        retired_verify_inclusion(&root, CARD_KEY, &card_b, &proof),
        "OLD-ADMITS: the retired /var verifier accepted a DIFFERENT settings card at the \
         honest key under the honest owner-signed root"
    );

    // The retired ROOT is unmoved too: swapping the whole committed card leaves the
    // published `data_root` byte-identical, so the ledger anchor cannot see the swap either.
    let swapped: Vec<(String, Vec<u8>)> = vec![
        (CARD_KEY.to_string(), card_b.clone()),
        (OTHER_KEY.to_string(), OTHER_VALUE.to_vec()),
    ];
    assert_eq!(
        retired_root_bytes(&swapped),
        root,
        "the retired /var root does not move when the committed card is replaced"
    );
}

#[test]
fn new_rejects_the_same_card_swap() {
    let (a, b, _) = search_retired_value_collision();
    let card_a = settings_card(a);
    let card_b = settings_card(b);

    // The deployed wide leaf digest SEPARATES the pair the retired felt conflated — in
    // every lane, not just one (a widening that separated them in one lane would be one
    // lane of binding wearing eight lanes' clothes).
    let d_a = var_leaf_digest8(CARD_KEY, &card_a);
    let d_b = var_leaf_digest8(CARD_KEY, &card_b);
    for lane in 0..d_a.len() {
        assert_ne!(
            d_a[lane], d_b[lane],
            "lane {lane} did not separate the pair"
        );
    }

    let mut var = Umem::new();
    var.put(CARD_KEY, card_a.clone());
    var.put(OTHER_KEY, OTHER_VALUE.to_vec());
    let root = var.commit();
    let proof = var.prove(CARD_KEY).expect("the key is present");

    // COMPLETENESS: the honest card still verifies at the deployed verifier.
    assert!(
        verify_inclusion(&root, CARD_KEY, &card_a, &proof),
        "the honest card must still verify — a refusal that refused honest witnesses is a DoS"
    );

    // ⚑ NEW-REJECTS: the card the retired construction admitted is REFUSED.
    assert!(
        !verify_inclusion(&root, CARD_KEY, &card_b, &proof),
        "NEW-REJECTS: the searched card swap must not open at the deployed eight-lane leaf"
    );

    // And the deployed ROOT moves when the committed card is replaced — the ledger anchor
    // now sees the swap the retired one could not.
    let mut swapped = Umem::new();
    swapped.put(CARD_KEY, card_b.clone());
    swapped.put(OTHER_KEY, OTHER_VALUE.to_vec());
    assert_ne!(
        swapped.commit(),
        root,
        "the deployed /var root must move when the committed card is replaced"
    );

    // The swap is refused against the swapped root too (the proof is for the other tree).
    let swapped_proof = swapped.prove(CARD_KEY).expect("present");
    assert!(verify_inclusion(
        &swapped.commit(),
        CARD_KEY,
        &card_b,
        &swapped_proof
    ));
    assert!(!verify_inclusion(
        &swapped.commit(),
        CARD_KEY,
        &card_a,
        &swapped_proof
    ));
}

#[test]
fn completeness_every_honest_entry_still_opens() {
    // A realistic `/var`: many keys, many value lengths, covering every residue mod 4 (the
    // packer stride) and mod 8 (the lane count).
    let mut var = Umem::new();
    let mut expected: Vec<(String, Vec<u8>)> = Vec::new();
    for n in 0..40usize {
        let key = format!("k{n:03}");
        let value: Vec<u8> = (0..n)
            .map(|i| (i as u8).wrapping_mul(53).wrapping_add(7))
            .collect();
        var.put(key.clone(), value.clone());
        expected.push((key, value));
    }
    let root = var.commit();

    for (key, value) in &expected {
        let proof = var
            .prove(key)
            .unwrap_or_else(|| panic!("{key} must be provable"));
        assert!(
            verify_inclusion(&root, key, value, &proof),
            "honest entry {key} (len {}) failed to verify — the widening is a DoS",
            value.len()
        );
        // Every lane opening is a full-depth path (no lane is silently empty).
        for lane in &proof.lanes {
            assert_eq!(lane.siblings.len(), HEAP_TREE_DEPTH);
            assert_ne!(lane.next_addr, BabyBear::ZERO);
        }
    }

    // The commitment is still order-free (the property the sorted tree exists for).
    let mut reversed = Umem::new();
    for (key, value) in expected.iter().rev() {
        reversed.put(key.clone(), value.clone());
    }
    assert_eq!(
        reversed.commit(),
        root,
        "the root must stay insert-order-free"
    );

    // An empty value is still a legitimate entry and still distinct from absence and from
    // a NUL (the property `var_nul_append_inclusion_forgery.rs` closed, preserved here).
    let mut e = Umem::new();
    e.put("empty", Vec::new());
    e.put("full", b"x".to_vec());
    let er = e.commit();
    let ep = e.prove("empty").expect("present");
    assert!(verify_inclusion(&er, "empty", b"", &ep));
    assert!(!verify_inclusion(&er, "empty", b"\0", &ep));

    // At least one lane of some entry carries the terminal pointer, so the SENTINEL_MAX
    // branch of the well-linked check is genuinely exercised by this corpus.
    let terminal = expected.iter().any(|(k, _)| {
        var.prove(k)
            .is_some_and(|p| p.lanes.iter().any(|l| l.next_addr == SENTINEL_MAX))
    });
    assert!(
        terminal,
        "no lane carried the terminal pointer — the edge case is untested"
    );
}

/// ⚑ **DERIVED, not remembered.** Both figures are computed from `p` here, and the
/// COLLISION one is named as the governing figure: a hostile host chooses both the card it
/// commits and the card it serves, so it never faces the second preimage.
#[test]
fn the_bound_is_derived_not_remembered() {
    let bits_per_lane = f64::from(2_013_265_921u32).log2();
    assert!((bits_per_lane - 30.906_891).abs() < 1e-5);

    // Retired: ONE lane.
    let retired_collision = bits_per_lane / 2.0;
    let retired_second_preimage = bits_per_lane;
    assert!((retired_collision - 15.453_445).abs() < 1e-5);
    assert!((retired_second_preimage - 30.906_891).abs() < 1e-5);

    // Deployed: EIGHT lanes — the count is read from the code, not typed in.
    let lanes = VAR_LANES as f64;
    assert_eq!(lanes, 8.0);
    let deployed_collision = lanes * bits_per_lane / 2.0;
    let deployed_second_preimage = lanes * bits_per_lane;
    assert!(
        (deployed_collision - 123.627_564).abs() < 1e-4,
        "deployed COLLISION bound is 2^{deployed_collision}"
    );
    assert!(
        (deployed_second_preimage - 247.255_128).abs() < 1e-4,
        "deployed second-preimage bound is 2^{deployed_second_preimage}"
    );

    // The governing figure clears this tree's ~124-bit bar; the retired one did not.
    assert!(deployed_collision > 123.0);
    assert!(retired_collision < 16.0);
}
