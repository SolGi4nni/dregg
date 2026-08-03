//! # The grain `/var` NUL-append forgery: OLD ADMITS, NEW REFUSES.
//!
//! ## The wound, at the site the brief named
//!
//! A grain's `/var` is committed as a `CanonicalHeapTree` whose leaves are
//! `HeapLeaf::entry(var_addr(key), var_value_felt(value))` (`sandstorm-bridge/src/cell.rs:84`),
//! and both of those felts were `dregg_circuit::poseidon2::hash_bytes` over a domain tag
//! concatenated with an arbitrary-length string. Until 2026-08-01 `hash_bytes` was
//! `hash_many(from_bytes_packed(data))`, whose packer ZERO-FILLED the final partial 4-byte chunk
//! while the sponge tag counted FELTS. So appending NUL bytes to a `/var` value — up to the next
//! multiple of four — moved neither the leaf value nor the root, and
//!
//! > **a hosting server could serve `value ‖ "\0"` and the visitor's inclusion proof still
//! > verified.**
//!
//! Same for the KEY: two `/var` keys differing only by trailing NULs shared one heap ADDRESS,
//! i.e. literally one leaf.
//!
//! ## What this file establishes
//!
//! * [`old_admitted_the_nul_append_at_the_var_leaf`] — the retired packing, spelled out here and
//!   applied to the REAL domain-tagged buffers, conflates `value` with `value ‖ "\0"` and
//!   `key` with `key ‖ "\0"`. That is the forgery, exhibited rather than asserted.
//! * [`new_refuses_the_nul_appended_card`] — under the deployed encoder the padded card is
//!   REFUSED by `verify_inclusion` against the honest root, and the padded key is a different
//!   address. The refusal is checked at the real verifier, not at the hash.
//! * [`completeness_the_honest_card_still_verifies`] — every honest `/var` entry still proves and
//!   verifies, and the root is still order-free. A refusal that also refused honest witnesses
//!   would be a DoS, not a fix.
//!
//! ## ⚠ What was NOT closed here — and is now closed NEXT DOOR
//!
//! This file closes the `O(1)` APPEND, which no widening would have closed. It did not touch
//! the 31-bit CODOMAIN, which no preimage repair reaches: `var_value_felt` squeezed ONE felt,
//! so a *searched* collision on a `/var` value cost `2^15.4534` ≈ 44,900 evaluations.
//!
//! **That one closed on 2026-08-03** — `tests/var_leaf_wide_old_admits_new_rejects.rs` exhibits
//! the collision (two well-formed settings cards, deterministic search) and drives the retired
//! verifier into ACCEPTING the wrong card, then shows the deployed eight-lane leaf refusing it.
//! One `/var` entry is now eight lane leaves under an 8-felt `CanonicalHeapTree8` root:
//! collision `2^123.6276`.
//!
//! [`the_residual_is_now_the_address_not_the_leaf`] carries what is genuinely still open, so
//! the green here is not misread as "`/var` inclusion is sound".

use sandstorm_bridge::cell::{verify_inclusion, Umem};

/// **THE RETIRED PACKING**, spelled out — byte-for-byte the deleted
/// `dregg_circuit::field::BabyBear::from_bytes_packed`: 4-byte little-endian strides, missing
/// bytes read as zero. Reproduced here (rather than called) because a negative witness must keep
/// exhibiting the defect it names after the implementation is gone.
///
/// The felt VALUES are irrelevant to the exhibit — what mattered is that the packed limb sequence
/// and its length were identical, so `hash_many` (which tags `state[4]` with the limb count)
/// returned the same felt. So this returns the `u32` limbs before reduction, and equality of these
/// lists IS equality of the old `hash_bytes` preimage.
fn retired_packed_limbs(bytes: &[u8]) -> Vec<u32> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let mut val: u32 = 0;
        for j in 0..4 {
            if i + j < bytes.len() {
                val |= u32::from(bytes[i + j]) << (j * 8);
            }
        }
        out.push(val);
        i += 4;
    }
    out
}

/// The two domain tags the deployed code prepends (`sandstorm-bridge/src/cell.rs:52,56`).
const VAR_ADDR_DOMAIN: &[u8] = b"grain/var/addr:v1\0";
const VAR_VALUE_DOMAIN: &[u8] = b"grain/var/value:v1\0";

fn tagged(domain: &[u8], rest: &[u8]) -> Vec<u8> {
    let mut buf = Vec::with_capacity(domain.len() + rest.len());
    buf.extend_from_slice(domain);
    buf.extend_from_slice(rest);
    buf
}

/// The value the exhibit uses. `VAR_VALUE_DOMAIN` is 19 bytes, so a 2-byte value gives a 21-byte
/// buffer = 6 packed limbs with one live byte in the last — and 1..=3 trailing NULs keep both the
/// limb values and the limb count fixed. That is the whole mechanism.
const HONEST_VALUE: &[u8] = b"hi";
const HONEST_KEY: &str = "cfg";

#[test]
fn old_admitted_the_nul_append_at_the_var_leaf() {
    // The VALUE leg: the served card body, padded.
    let honest = tagged(VAR_VALUE_DOMAIN, HONEST_VALUE);
    assert_eq!(honest.len(), 21, "19-byte tag + 2-byte value");
    for pad in 1..=3usize {
        let mut padded_value = HONEST_VALUE.to_vec();
        padded_value.extend(std::iter::repeat_n(0u8, pad));
        let forged = tagged(VAR_VALUE_DOMAIN, &padded_value);
        assert_ne!(honest, forged, "the buffers genuinely differ");
        assert_eq!(
            retired_packed_limbs(&honest),
            retired_packed_limbs(&forged),
            "the retired packing conflated the value with value ‖ {pad} NULs"
        );
        assert_eq!(
            retired_packed_limbs(&honest).len(),
            retired_packed_limbs(&forged).len(),
            "…and the FELT COUNT agreed too, so hash_many's domain tag did not separate them"
        );
    }

    // The KEY leg: two distinct `/var` keys on one heap ADDRESS, i.e. literally one leaf.
    let honest_key = tagged(VAR_ADDR_DOMAIN, HONEST_KEY.as_bytes());
    assert_eq!(honest_key.len(), 21);
    let forged_key = tagged(VAR_ADDR_DOMAIN, b"cfg\0");
    assert_ne!(honest_key, forged_key);
    assert_eq!(
        retired_packed_limbs(&honest_key),
        retired_packed_limbs(&forged_key),
        "the retired packing put two distinct /var keys on ONE heap address"
    );
}

#[test]
fn new_refuses_the_nul_appended_card() {
    let mut umem = Umem::new();
    umem.put(HONEST_KEY, HONEST_VALUE.to_vec());
    umem.put("other", b"payload".to_vec());
    let root = umem.commit();
    let proof = umem.prove(HONEST_KEY).expect("the key is present");

    // Baseline: the honest card verifies. (If this were false the refusals below would be vacuous.)
    assert!(
        verify_inclusion(&root, HONEST_KEY, HONEST_VALUE, &proof),
        "ANTI-VACUITY: the honest card must verify, or 'refused' means nothing"
    );

    // ⚑ THE FORGERY, REFUSED. The server serves `value ‖ NULs` with the honest proof.
    for pad in 1..=8usize {
        let mut padded = HONEST_VALUE.to_vec();
        padded.extend(std::iter::repeat_n(0u8, pad));
        assert!(
            !verify_inclusion(&root, HONEST_KEY, &padded, &proof),
            "serving value ‖ {pad} NULs still verified — the append forgery is OPEN"
        );
    }

    // ...and truncation, the other side of the same ambiguity.
    assert!(!verify_inclusion(&root, HONEST_KEY, b"h", &proof));
    assert!(!verify_inclusion(&root, HONEST_KEY, b"", &proof));

    // The KEY leg: a NUL-appended key is a DIFFERENT leaf, so the honest proof cannot open it.
    assert!(!verify_inclusion(&root, "cfg\0", HONEST_VALUE, &proof));

    // And two keys differing only by trailing NULs are now two distinct entries, not one.
    let mut two = Umem::new();
    two.put("cfg", b"a".to_vec());
    two.put("cfg\0", b"b".to_vec());
    assert_eq!(two.len(), 2);
    let root2 = two.commit();
    let p_a = two.prove("cfg").expect("present");
    let p_b = two.prove("cfg\0").expect("present");
    assert!(verify_inclusion(&root2, "cfg", b"a", &p_a));
    assert!(verify_inclusion(&root2, "cfg\0", b"b", &p_b));
    // Crossed openings are refused — the two leaves are genuinely separate.
    assert!(!verify_inclusion(&root2, "cfg", b"b", &p_a));
    assert!(!verify_inclusion(&root2, "cfg\0", b"a", &p_b));
}

#[test]
fn completeness_the_honest_card_still_verifies() {
    // A realistic `/var`: many keys, many value lengths, including every residue mod 4 and mod 2
    // (the lengths where the old padding bit and where the new final lane is half-empty).
    let mut umem = Umem::new();
    let mut expected: Vec<(String, Vec<u8>)> = Vec::new();
    for n in 0..40usize {
        let key = format!("k{n:03}");
        let value: Vec<u8> = (0..n)
            .map(|i| (i as u8).wrapping_mul(53).wrapping_add(7))
            .collect();
        umem.put(key.clone(), value.clone());
        expected.push((key, value));
    }
    let root = umem.commit();

    for (key, value) in &expected {
        let proof = umem
            .prove(key)
            .unwrap_or_else(|| panic!("{key} must be provable"));
        assert!(
            verify_inclusion(&root, key, value, &proof),
            "honest entry {key} (len {}) failed to verify — the fix is a DoS",
            value.len()
        );
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

    // An empty value is still a legitimate entry and still distinct from absence.
    let mut e = Umem::new();
    e.put("empty", Vec::new());
    e.put("full", b"x".to_vec());
    let er = e.commit();
    let ep = e.prove("empty").expect("present");
    assert!(verify_inclusion(&er, "empty", b"", &ep));
    assert!(!verify_inclusion(&er, "empty", b"\0", &ep));
}

/// ⚠ **NOT A GUARD — A LEDGER.** The `/var` LEAF is now eight lanes (`2^123.6276` collision,
/// `var_leaf_wide_old_admits_new_rejects.rs`), so the residual this file used to carry is closed.
/// What remains is one size down and a different KIND of failure, and it is written here so a
/// reader who sees this crate green reads the right thing.
///
/// `var_coll` — the ADDRESS base an entry's eight lane leaves hang off — is still ONE felt. Two
/// `/var` keys colliding on it (`2^15.4534`, ~44,900 evaluations) share all eight lane addresses.
/// That is **not a forgery**: the key is bound again at full width inside the leaf VALUES by
/// `var_leaf_digest8`, which `verify_inclusion` recomputes from the claimed key, so neither key
/// can open the other's card. It is an AVAILABILITY event — `heap_root::assert_addr_unique`
/// PANICS, refusing to commit an ambiguous root, which is fail-closed.
///
/// The eight-fold leaf count moves that bound: an accidental collision becomes likely near
/// `2^15.4534 / 8 ≈ 5,793` entries rather than `≈ 46,341`, and the depth-16 tree now holds `8191`
/// entries rather than `65535`. Closing it needs an address space wider than one felt, which is
/// `HeapLeaf`'s shape and therefore the deployed IMT gate's — the same Lean/emit item named at
/// `exec_lean::nullifier::addr_of`. Delete this when `HeapLeaf::addr` widens.
#[test]
fn the_residual_is_now_the_address_not_the_leaf() {
    let bits = f64::from(2_013_265_921u32).log2();
    assert!((bits - 30.906_891).abs() < 1e-5);

    // The address residual: one felt, birthday over the LANE count.
    let lanes = sandstorm_bridge::cell::VAR_LANES as f64;
    assert_eq!(lanes, 8.0);
    let addr_collision = bits / 2.0;
    assert!((addr_collision - 15.453_445).abs() < 1e-5);
    let safe_entries = 2f64.powf(addr_collision) / lanes;
    assert!(
        (5_600.0..6_000.0).contains(&safe_entries),
        "an accidental /var address collision becomes likely near {safe_entries} entries"
    );

    // The leaf residual is GONE: the deployed leaf is eight lanes, over the bar.
    let leaf_collision = lanes * bits / 2.0;
    assert!(
        leaf_collision > 123.0,
        "the /var LEAF binds at 2^{leaf_collision} — closed 2026-08-03"
    );
}
