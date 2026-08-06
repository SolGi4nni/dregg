//! # The trustless bucket read could be PANICKED by an untrusted opening, at `2^15.4534`
//!
//! `dregg_storage::bucket_commitment::verify_opening` is the trustless read: a stranger
//! re-witnesses served bytes against a committed root with no trust in the server. Its input,
//! `ObjectOpening`, derives `Deserialize` — the whole point is that it arrives over a wire from
//! somebody you do not trust.
//!
//! Leg (2) re-folds `op.leaves` through `fold_leaves`, which addresses each object's eight wide
//! limbs at `(coll, i)` with `coll = dregg_circuit::poseidon2::hash_bytes(key)` — ONE BabyBear,
//! `log2 p = 30.906891` bits — and hands the entries to `compute_heap_root_entries` →
//! `CanonicalHeapTree::new` → `assert_addr_unique`, which **panics** on two leaves sharing an
//! address (`circuit/src/heap_root.rs:552`, `:297-313`).
//!
//! So two DISTINCT object keys whose `hash_bytes` images coincide give eight duplicated addresses
//! and abort the verifier.
//!
//! ## The class this is NOT
//!
//! This is **not** a forgery, and the `(B)` note at the call site is right that it cannot become
//! one: `object_leaf(key, object)` binds the key a second time through an injective 3-bytes-per-
//! felt packing inside an 8-felt digest, and leg (1) recomputes it from the served bytes. A
//! colliding `coll` moves no object's leaf. Saying "collision ⇒ forgery" here would be inventing
//! a wound; the gain is availability, and it is real.
//!
//! ## The bound, derived — COLLISION, not second preimage
//!
//! The attacker mints BOTH keys of the pair (they are strings they choose), so this is a birthday
//! event over the image, not a targeted search against a key someone else published:
//!
//! ```text
//!   log2 p = log2 2013265921 = 30.906891
//!   collision ≈ 2^(30.906891 / 2) = 2^15.4534 ≈ 44,900 evaluations
//! ```
//!
//! The second-preimage figure for the same felt is `2^30.91`; quoting it would be the flattering
//! half of the pair and it is not what this costs.

use std::collections::HashMap;

use dregg_circuit::poseidon2::hash_bytes;
use dregg_storage::bucket_commitment::{
    BucketContent, Object, ObjectOpening, content_root, object_leaf, open, verify_opening,
};

/// Deterministic birthday search for two DISTINCT object keys sharing a `hash_bytes` image.
/// Returns `(a, b, evaluations)`.
fn find_colliding_keys() -> (String, String, u64) {
    // Cached: two tests consume the same pair and the search is this file's whole cost.
    static FOUND: std::sync::OnceLock<(String, String, u64)> = std::sync::OnceLock::new();
    FOUND.get_or_init(search_colliding_keys).clone()
}

fn search_colliding_keys() -> (String, String, u64) {
    let mut seen: HashMap<u32, String> = HashMap::new();
    let mut evaluations = 0u64;
    for i in 0u64.. {
        let key = format!("/objects/{i}");
        evaluations += 1;
        let image = hash_bytes(key.as_bytes()).as_u32();
        if let Some(prev) = seen.get(&image) {
            return (prev.clone(), key, evaluations);
        }
        seen.insert(image, key);
    }
    unreachable!("the field is finite; a collision exists by pigeonhole")
}

#[test]
fn two_object_keys_collide_on_the_one_felt_collection_by_deterministic_search() {
    let started = std::time::Instant::now();
    let (a, b, evaluations) = find_colliding_keys();
    let elapsed = started.elapsed();
    eprintln!(
        "bucket `coll` collision: {evaluations} evaluations in {elapsed:?} \
         (derived birthday bound 2^(30.906891/2) = 2^15.4534 ≈ 44,900; expected draws \
         sqrt(pi*p/2) ≈ 56,235 — ONE trial, so this count is a draw, not a check of the bound)"
    );
    assert_ne!(a, b, "the pair must be two DISTINCT keys");
    assert_eq!(
        hash_bytes(a.as_bytes()),
        hash_bytes(b.as_bytes()),
        "...sharing the one-felt collection image"
    );
    // ANTI-VACUITY: the companion that makes this (B) rather than (A) genuinely separates them.
    let o = Object::new("text/plain", b"x".to_vec());
    assert_ne!(
        object_leaf(&a, &o),
        object_leaf(&b, &o),
        "the 8-felt object leaf binds the key injectively — that is what makes the collision an \
         availability event and not a forgery, and if this ever passes the classification flips"
    );
}

#[test]
fn old_admits_the_hostile_opening_and_new_rejects_it() {
    let (a, b, _) = find_colliding_keys();

    // A well-formed, honest bucket and its genuine opening.
    let mut content = BucketContent::new();
    content.insert(a.clone(), Object::new("text/plain", b"alpha".to_vec()));
    let honest = open(&content, &a).expect("the key is present");
    assert!(
        verify_opening(&honest),
        "COMPLETENESS: a genuine opening still verifies"
    );

    // The hostile opening: the same served object, with a SECOND listed leaf whose key collides
    // with the first on `coll`. Every field is well-typed; nothing here is malformed.
    let hostile = ObjectOpening {
        key: honest.key.clone(),
        object: honest.object.clone(),
        bucket_root: honest.bucket_root.clone(),
        leaves: vec![
            (a.clone(), object_leaf(&a, &content[&a])),
            (
                b.clone(),
                object_leaf(&b, &Object::new("text/plain", b"beta".to_vec())),
            ),
        ],
    };

    // ⚑ OLD ADMITS — the retired body went straight to `fold_leaves(op.leaves)`, which reaches
    // `assert_addr_unique` and ABORTS. Reproduced here through `content_root`, the public entry to
    // that same fold, since that is exactly what leg (2) did before the refusal was added.
    // (The hook is muted so the expected abort does not read as a test failure in the log.)
    let previous_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let retired = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        content_root_of_listed(&hostile)
    }));
    let verdict =
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| verify_opening(&hostile)));
    std::panic::set_hook(previous_hook);

    assert!(
        retired.is_err(),
        "⚑ OLD ADMITS: the retired leg (2) must panic on the ambiguous list — if it does not, the \
         refusal below is guarding nothing and this exhibit is vacuous"
    );

    // ⚑ NEW REJECTS — and it REJECTS, it does not abort: the caller gets `false`.
    let verdict = verdict.expect("⚑ NEW REJECTS: the verifier must return, not unwind");
    assert!(
        !verdict,
        "an opening with an ambiguous leaf list is not a valid opening"
    );
}

/// Re-fold a listed leaf set the way leg (2) did before the refusal — through the public
/// `content_root`, which reaches the same `fold_leaves`/`assert_addr_unique` path.
fn content_root_of_listed(op: &ObjectOpening) -> String {
    let mut content = BucketContent::new();
    for (i, (key, _)) in op.leaves.iter().enumerate() {
        content.insert(key.clone(), Object::new("text/plain", vec![i as u8]));
    }
    content_root(&content)
}

#[test]
fn completeness_an_ordinary_multi_object_bucket_still_opens() {
    let mut content = BucketContent::new();
    for i in 0..8u8 {
        content.insert(
            format!("/asset/{i}"),
            Object::new("application/octet-stream", vec![i; 16]),
        );
    }
    let root = content_root(&content);
    for key in content.keys().cloned().collect::<Vec<_>>() {
        let opening = open(&content, &key).expect("present");
        assert_eq!(opening.bucket_root, root, "the opening names the real root");
        assert!(
            verify_opening(&opening),
            "COMPLETENESS: every honest object still opens after the refusal — key {key}"
        );
    }
}
