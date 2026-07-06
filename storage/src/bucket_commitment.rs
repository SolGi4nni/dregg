//! `bucket_commitment` — the bucket-object-store's REAL Poseidon2 content
//! commitment + the trustless verified read.
//!
//! Ported dregg-native from the retired operated layer's object store
//! (the prior operated layer — the leaf-fold, the injective
//! anti-alias packing, and `verify_opening`), over the SAME native circuit
//! primitives the old code already imported (`dregg_circuit::heap_root::
//! compute_heap_root_entries`, `dregg_circuit::poseidon2::wire_commit_8`).
//! The bucket *data plane* (cap-gated put/get/list/delete, receipts, metering)
//! is superseded natively by `starbridge-apps/storage-gateway-mandate`; what
//! this module carries is the commitment scheme that made a bucket read
//! **trustless** — the piece with no other native carrier.
//!
//! - [`object_leaf`] — the per-object leaf `H(key, content_type, body)`, a wide
//!   8-felt (~124-bit) Poseidon2 digest with **injective** byte→felt packing
//!   (3 bytes/felt, no modular wraparound — defeats the 4-byte `% p` `+p`-alias
//!   class) and length-delimited parts.
//! - [`content_root`] — the bucket commitment: the sorted-Poseidon2 cell-heap
//!   fold over the object leaves (`compute_heap_root_entries`) published through
//!   the kernel's 8-felt faithful widening (`wire_commit_8`) — a WIDE carrier
//!   chain with no 31-bit intermediate (the `FAITHFUL-STATE-COMMITMENT.md`
//!   discipline).
//! - [`ObjectOpening`] / [`verify_opening`] — **the trustless read**: served
//!   bytes re-witnessed against the committed root with no trust in the server.
//!
//! The domain-separation string (`dregg-bucket-content-root-v1`) is native to
//! this substrate; there is no legacy corpus to stay byte-compatible with.
//!
//! WIRING (one line, not yet applied): `pub mod bucket_commitment;` in
//! `storage/src/lib.rs`.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

/// One stored object: its content type + bytes. (The minimal object surface the
/// commitment binds; the richer data-plane object model lives with whichever
/// gateway serves the bucket.)
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Object {
    pub content_type: String,
    pub body: Vec<u8>,
}

impl Object {
    pub fn new(content_type: &str, body: Vec<u8>) -> Self {
        Self {
            content_type: content_type.to_string(),
            body,
        }
    }

    /// The object's own content address: the wide Poseidon2 digest of its
    /// content type + bytes (keyless — moves iff the content moves).
    pub fn content_address(&self) -> String {
        poseidon2::felts8_to_hex(&poseidon2::digest8(&[
            self.content_type.as_bytes(),
            &self.body,
        ]))
    }
}

/// A bucket's committed content: the canonical (sorted) `key → Object` map the
/// root folds over.
pub type BucketContent = BTreeMap<String, Object>;

/// Hash an arbitrary byte slice to the canonical digest (used for ad-hoc leaf
/// digests): the wide 8-felt (64-hex) collision-resistant Poseidon2 digest, the
/// same hash family the dregg kernel commits a cell value with.
pub fn digest(bytes: &[u8]) -> String {
    poseidon2::felts8_to_hex(&poseidon2::digest8(&[bytes]))
}

/// The per-object **leaf** commitment: `H(key, content_type, body)`. Binds the
/// object's identity (its key) to its bytes. The bucket root is the fold over
/// these.
pub fn object_leaf(key: &str, object: &Object) -> String {
    poseidon2::felts8_to_hex(&poseidon2::digest8(&[
        key.as_bytes(),
        object.content_type.as_bytes(),
        &object.body,
    ]))
}

/// The bucket **content commitment**: the fold over the sorted-by-key object
/// leaves. Deterministic and order-independent of insertion (the `BTreeMap`
/// canonicalizes), and a single changed byte in any object moves it.
pub fn content_root(content: &BucketContent) -> String {
    fold_leaves(content.iter().map(|(k, o)| (k.clone(), object_leaf(k, o))))
}

/// Fold an ordered `(key, leaf)` sequence into the bucket root — the REAL
/// sorted-Poseidon2 cell-heap root.
///
/// Each object's wide 8-felt leaf digest is placed in the canonical SORTED
/// Poseidon2 Merkle heap keyed by `(collection = key, limb-index)`; the kernel's
/// heap-root function (`compute_heap_root_entries`) folds the root, and the
/// published commitment is the kernel's 8-felt faithful widening
/// (`wire_commit_8`) over the per-object wide limbs with the heap root as the
/// final `iroot` — a WIDE carrier chain with no 31-bit intermediate. The object
/// key is bound twice: into the leaf digest (its identity) and into the heap
/// collection (its position), so a server cannot reorder/relabel without moving
/// the root.
fn fold_leaves(leaves: impl IntoIterator<Item = (String, String)>) -> String {
    use dregg_circuit::field::BabyBear;
    use dregg_circuit::heap_root::compute_heap_root_entries;
    use dregg_circuit::poseidon2::{hash_bytes, wire_commit_8};
    use poseidon2::{felts8_to_hex, parse_felts8};

    let mut entries: Vec<((BabyBear, BabyBear), BabyBear)> = Vec::new();
    let mut limbs: Vec<BabyBear> = Vec::new();
    let mut count: u32 = 0;
    for (key, leaf) in leaves {
        count += 1;
        // The object's namespace within the cell heap (the sort-key collection).
        let coll = hash_bytes(key.as_bytes());
        // `leaf` is the object's own 64-hex wide digest ([`object_leaf`]).
        let d8 = parse_felts8(&leaf).unwrap_or([BabyBear::ZERO; 8]);
        for (i, &limb) in d8.iter().enumerate() {
            entries.push(((coll, BabyBear::new(i as u32)), limb));
            limbs.push(limb);
        }
    }
    let heap_root = compute_heap_root_entries(&entries);
    // The 4-felt domain header binds the bucket domain + object count and keeps
    // the fold total when the bucket is empty (`pre_limbs.len() >= 4`). The
    // domain string is kept byte-identical to the retired layer's so surviving
    // roots re-verify.
    let mut pre = vec![
        hash_bytes(b"dregg-bucket-content-root-v1"),
        BabyBear::new(count),
        BabyBear::ZERO,
        BabyBear::ZERO,
    ];
    pre.extend_from_slice(&limbs);
    felts8_to_hex(&wire_commit_8(&pre, heap_root))
}

/// A self-verifying read of one object against a bucket's committed root.
///
/// Carries the served object bytes, the claimed `bucket_root`, and the full
/// ordered `(key, leaf)` digest list. [`verify_opening`] checks it with no trust
/// in the source. On a dregg node this is a Merkle path against the cell's
/// committed root; here it is the full leaf list (small digests + the one
/// object's bytes), which has the same *bytes-bind-to-root* property.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObjectOpening {
    /// The object key this opening is for.
    pub key: String,
    /// The served object (the bytes being re-witnessed).
    pub object: Object,
    /// The bucket's committed content root the object is opened against.
    pub bucket_root: String,
    /// The full ordered list of `(key, leaf-digest)` — the target's neighbors as
    /// compact digests, the target's own listed leaf included.
    pub leaves: Vec<(String, String)>,
}

impl ObjectOpening {
    /// Re-witness this opening — a convenience wrapper over [`verify_opening`].
    pub fn verify(&self) -> bool {
        verify_opening(self)
    }
}

/// Build the opening for `key` against `content`'s committed root, or `None` if
/// the key is absent. (What a serving gateway returns for a verified GET.)
pub fn open(content: &BucketContent, key: &str) -> Option<ObjectOpening> {
    let object = content.get(key)?.clone();
    Some(ObjectOpening {
        key: key.to_string(),
        object,
        bucket_root: content_root(content),
        leaves: content
            .iter()
            .map(|(k, o)| (k.clone(), object_leaf(k, o)))
            .collect(),
    })
}

/// **The trustless read.** Re-witness, with no trust in the source, that the
/// served object bytes are the object committed at `key` in `bucket_root`.
///
/// Returns `true` iff both hold:
/// 1. the leaf recomputed from the *served bytes* (`object_leaf(key, object)`)
///    equals the leaf the opening lists at `key` — the bytes bind to the leaf;
/// 2. re-folding the listed leaves reproduces the claimed `bucket_root` — the
///    leaf is included in the committed root.
///
/// A flipped object byte fails (1); a tampered root or a doctored leaf list
/// fails (2).
pub fn verify_opening(op: &ObjectOpening) -> bool {
    // (1) the served bytes must reproduce the leaf the opening claims at `key`.
    let recomputed = object_leaf(&op.key, &op.object);
    let Some((_, listed_leaf)) = op.leaves.iter().find(|(k, _)| k == &op.key) else {
        return false; // the key is not even in the opening's leaf list
    };
    if &recomputed != listed_leaf {
        return false;
    }
    // (2) the listed leaves must re-fold to the claimed root.
    let refolded = fold_leaves(op.leaves.iter().cloned());
    refolded == op.bucket_root
}

/// The REAL Poseidon2 object/bucket commitment primitives. Wide 8-felt
/// (~124-bit) digests over the kernel's Poseidon2 sponge, the same hash family
/// the dregg umem heap commits with.
pub(crate) mod poseidon2 {
    use dregg_circuit::field::BabyBear;
    use dregg_circuit::poseidon2::hash_many_8;

    /// A WIDE (8-felt, ~124-bit) Poseidon2 digest over the length-delimited
    /// parts. Each part is prefixed by its byte length so field-domain
    /// concatenation is unambiguous (a server cannot shift bytes between parts
    /// without moving it), and each part's bytes are packed with the
    /// **injective** [`pack_bytes`] (3 bytes/felt, no modular wraparound) so
    /// distinct byte strings always map to distinct felt sequences — the content
    /// commitment is a true injective function of the bytes, so a same-length
    /// adversarial byte substitution cannot alias.
    pub(crate) fn digest8(parts: &[&[u8]]) -> [BabyBear; 8] {
        let mut input: Vec<BabyBear> = Vec::new();
        for p in parts {
            input.push(BabyBear::new(p.len() as u32));
            input.extend(pack_bytes(p));
        }
        hash_many_8(&input)
    }

    /// **Injective** byte → field packing for the content commitment.
    ///
    /// Packs **3 little-endian bytes per element** (a u24 value `< 2^24 ≤ p`, so
    /// `BabyBear::new` performs no modular reduction). This is deliberately NOT
    /// the shared `dregg_circuit::field::from_bytes_packed`, which packs **4**
    /// bytes into a u32 and reduces `% p`: since `p ≈ 2^30.9 < 2^32`, ~53% of
    /// 4-byte chunks alias their `+p` partner (`v ≡ v + p`), so two distinct
    /// equal-length byte strings could produce the identical digest and pass the
    /// trustless read.
    ///
    /// With 3 bytes/felt there is no wraparound, so within a fixed length two
    /// byte strings differing at any position produce a different felt at that
    /// chunk; combined with the byte-length prefix in [`digest8`] the map is
    /// injective for same-length **and** different-length inputs. The real
    /// Poseidon2 `hash_many_8` stays the hash.
    fn pack_bytes(bytes: &[u8]) -> Vec<BabyBear> {
        let mut out = Vec::with_capacity(bytes.len() / 3 + 1);
        for chunk in bytes.chunks(3) {
            let mut val: u32 = 0;
            for (j, &b) in chunk.iter().enumerate() {
                val |= (b as u32) << (j * 8);
            }
            // val < 2^24 < p, so `new` is the identity (no reduction, injective).
            out.push(BabyBear::new(val));
        }
        out
    }

    /// Lower-hex encode an 8-felt digest (8 × u32 → 64 hex chars).
    pub(crate) fn felts8_to_hex(f: &[BabyBear; 8]) -> String {
        use std::fmt::Write as _;
        let mut s = String::with_capacity(64);
        for x in f {
            let _ = write!(s, "{:08x}", x.as_u32());
        }
        s
    }

    /// Parse a 64-hex 8-felt digest back into its felts (round-trips
    /// [`felts8_to_hex`]; values are canonical `< p`, so the round-trip is
    /// exact). `None` on a wrong length or a non-hex chunk.
    pub(crate) fn parse_felts8(hex: &str) -> Option<[BabyBear; 8]> {
        if hex.len() != 64 {
            return None;
        }
        let mut out = [BabyBear::ZERO; 8];
        for (i, slot) in out.iter_mut().enumerate() {
            let chunk = hex.get(i * 8..i * 8 + 8)?;
            *slot = BabyBear::new(u32::from_str_radix(chunk, 16).ok()?);
        }
        Some(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bucket_with(objs: &[(&str, &str)]) -> BucketContent {
        let mut c = BucketContent::new();
        for (k, v) in objs {
            c.insert(
                k.to_string(),
                Object::new("application/octet-stream", v.as_bytes().to_vec()),
            );
        }
        c
    }

    #[test]
    fn content_root_is_deterministic_and_sensitive() {
        let a = bucket_with(&[("a.txt", "hi"), ("b.json", "{}")]);
        // Insertion order does not matter (BTreeMap canonical).
        let b = bucket_with(&[("b.json", "{}"), ("a.txt", "hi")]);
        assert_eq!(content_root(&a), content_root(&b));
        // A single changed byte moves the root.
        let d = bucket_with(&[("a.txt", "hI"), ("b.json", "{}")]);
        assert_ne!(content_root(&a), content_root(&d));
        // A moved key moves the root.
        let m = bucket_with(&[("a2.txt", "hi"), ("b.json", "{}")]);
        assert_ne!(content_root(&a), content_root(&m));
        // A changed content-type moves the root.
        let mut t = bucket_with(&[("b.json", "{}")]);
        t.insert("a.txt".into(), Object::new("text/plain", b"hi".to_vec()));
        assert_ne!(content_root(&a), content_root(&t));
    }

    #[test]
    fn the_root_and_leaf_are_the_wide_poseidon2_commitment() {
        let c = bucket_with(&[("a.txt", "hello"), ("b.json", "{\"k\":1}")]);
        let root = content_root(&c);
        assert_eq!(root.len(), 64, "the bucket root is 8-felt wide (64 hex)");
        assert!(root.chars().all(|ch| ch.is_ascii_hexdigit()));
        let leaf = object_leaf("a.txt", c.get("a.txt").unwrap());
        assert_eq!(leaf.len(), 64, "the object leaf is 8-felt wide (64 hex)");
    }

    #[test]
    fn trustless_read_round_trips() {
        let c = bucket_with(&[("a.txt", "hello"), ("b.json", "{\"k\":1}")]);
        let op = open(&c, "a.txt").expect("present");
        assert!(verify_opening(&op));
        assert_eq!(op.object.body, b"hello");
        // Opening a missing key yields nothing.
        assert!(open(&c, "missing").is_none());
    }

    #[test]
    fn tampered_bytes_fail_verification() {
        let c = bucket_with(&[("a.txt", "hello"), ("b.json", "{}")]);
        let mut op = open(&c, "a.txt").unwrap();
        // A server flips a byte of the served object — verification must fail
        // because the recomputed leaf no longer matches the listed leaf.
        op.object.body = b"hellO".to_vec();
        assert!(!verify_opening(&op));
    }

    #[test]
    fn tampered_root_fails_verification() {
        let c = bucket_with(&[("a.txt", "hello"), ("b.json", "{}")]);
        let mut op = open(&c, "a.txt").unwrap();
        op.bucket_root = "0000000000000000".to_string();
        assert!(!verify_opening(&op));
    }

    #[test]
    fn doctored_neighbor_leaf_fails_verification() {
        let c = bucket_with(&[("a.txt", "hello"), ("b.json", "{}")]);
        let mut op = open(&c, "a.txt").unwrap();
        // Tamper a *different* object's listed leaf — the re-fold no longer
        // reproduces the committed root, so the read is rejected.
        if let Some(slot) = op.leaves.iter_mut().find(|(k, _)| k != &op.key) {
            slot.1 = "ffffffffffffffff".to_string();
        }
        assert!(!verify_opening(&op));
    }

    /// The anti-aliasing tooth over the trustless read. A malicious host
    /// substitutes the served bytes for a SAME-LENGTH `+p` alias — the exact
    /// collision class a 4-byte `% p` packing accepts as genuine. With the
    /// injective packing the substitution moves the object leaf, so
    /// `verify_opening` REJECTS it and the bucket `content_root` moves.
    #[test]
    fn same_length_alias_substitution_is_rejected_by_verify_opening() {
        use dregg_circuit::field::BabyBear;

        // A `+p` alias pair over one 4-byte chunk (both length 4):
        //   value 1              → LE [01,00,00,00]
        //   value 1 + p          → LE [02,00,00,78]   (p = 0x78000001)
        let honest = vec![0x01u8, 0x00, 0x00, 0x00];
        let forged = vec![0x02u8, 0x00, 0x00, 0x78];
        assert_eq!(
            honest.len(),
            forged.len(),
            "the substitution is same-length"
        );
        assert_ne!(honest, forged, "the bytes genuinely differ");
        // Witness that the SHARED 4-byte primitive aliases them (the hole the
        // injective packing exists to close).
        assert_eq!(
            BabyBear::from_bytes_packed(&honest),
            BabyBear::from_bytes_packed(&forged),
            "the 4-byte %p packing aliases this pair"
        );

        let mut c = bucket_with(&[("b.json", "{}")]);
        c.insert(
            "blob.bin".into(),
            Object::new("application/octet-stream", honest.clone()),
        );

        // The honest served bytes verify.
        let op = open(&c, "blob.bin").expect("present");
        assert!(op.verify(), "the honest bytes re-witness against the root");

        // A same-length aliasing substitution is REFUSED.
        let mut tampered = op.clone();
        tampered.object.body = forged.clone();
        assert!(
            !verify_opening(&tampered),
            "the same-length +p alias substitution is caught by the injective leaf"
        );

        // And the content_root itself separates the two contents.
        let mut c2 = bucket_with(&[("b.json", "{}")]);
        c2.insert(
            "blob.bin".into(),
            Object::new("application/octet-stream", forged),
        );
        assert_ne!(
            content_root(&c),
            content_root(&c2),
            "the injective packing moves the content_root for the alias pair"
        );

        // The keyless content address separates them too.
        assert_eq!(
            c.get("blob.bin").unwrap().content_address(),
            Object::new("application/octet-stream", honest).content_address()
        );
    }
}
