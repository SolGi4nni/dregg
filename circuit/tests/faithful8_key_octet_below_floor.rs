//! **The KEY_COMMIT octet is below the faithful-commitment law's own floor, and the burn-down
//! list is now a gate instead of a convention.**
//!
//! `Faithful8::from_canonical_key` used to be listed beside the tree roots and the wire-commit
//! chain as a *faithful* constructor, with a doc reading "8+8+8+6 = 30 bits per limb, 240 bits
//! total, faithful". This file is the arithmetic that demoted it, measured rather than asserted:
//!
//! * `the_deployed_pack_never_reads_sixteen_source_bits` MEASURES the read-set of the deployed
//!   packer (`dregg_cell::commitment::canonical_to_babybear_pi`) in BOTH directions — sixteen
//!   named bits that provably do not move the octet, and 240 that provably do. The number 240
//!   comes out of the code, not out of a comment.
//! * `key_octet_collision_is_below_the_law_floor` puts that measurement against the floor derived
//!   from `BABYBEAR_P`. ⚠ SAY WHICH BOUND: the law's "~124-bit" is `8 · log₂ p / 2 = 123.63`, a
//!   BIRTHDAY COLLISION bound over a full 8-lane image. The key octet's IMAGE is `2^240`; its
//!   birthday COLLISION is `2^120`; `120 < 123.63`.
//! * `an_ed25519_key_and_its_negation_pack_to_one_octet` is the EXHIBIT, and it removes the
//!   escape the old doc offered ("only a colliding *meaningful* value costs anything, ~2^120").
//!   The source of this octet is `Cell::public_key`, an Ed25519 public key. RFC 8032 §5.1.2 puts
//!   the x-sign in bit 7 of byte 31 — one of the sixteen unread bits. So the ACTUAL collision
//!   cost among *valid public keys* is `0`, not `2^120`.
//! * `the_burn_down_list_names_every_hatch_call_site` turns the law's "adding a `_DANGER` site
//!   without listing it here is a review-time violation" into something that can go red.
//!
//! Nothing here changes what any encoder computes. The demotion is type- and doc-level: the
//! constructor's body is now the `_DANGER` hatch, so the octet is on the list where it belongs.
//! The fix that raises the number is a NINTH key lane (`2^278` image, `2^139` birthday) and it is
//! a descriptor re-emit + VK rotation + `CANONICAL_STATE_SCHEMA_EPOCH` 15 → 16 — a different lane.

use std::path::{Path, PathBuf};

use curve25519_dalek::constants::ED25519_BASEPOINT_POINT;
use curve25519_dalek::scalar::Scalar;
use dregg_cell::commitment::canonical_to_babybear_pi;
use dregg_circuit::Faithful8;
use dregg_circuit::faithful8::KEY_COMMIT_30BIT_RESIDUAL;
use dregg_circuit::field::{BABYBEAR_P, BabyBear};

/// The sixteen source bits the `8+8+8+6` pack throws away: bits 6 and 7 of every fourth byte.
/// Written from the SHAPE (`hi & 0x3F` on `canonical[4i+3]`), and then CHECKED against the
/// deployed packer in both directions below — this array is the hypothesis, not the measurement.
const CLAIMED_UNREAD: [(usize, u8); 16] = [
    (3, 6),
    (3, 7),
    (7, 6),
    (7, 7),
    (11, 6),
    (11, 7),
    (15, 6),
    (15, 7),
    (19, 6),
    (19, 7),
    (23, 6),
    (23, 7),
    (27, 6),
    (27, 7),
    (31, 6),
    (31, 7),
];

fn octet(b: &[u8; 32]) -> [u32; 8] {
    canonical_to_babybear_pi(b)
}

fn faithful(b: &[u8; 32]) -> Faithful8 {
    Faithful8::from_canonical_key(octet(b).map(BabyBear::new))
}

/// A base vector with every bit of every byte exercised across the 32 positions, so a flip test
/// is never masked by a byte that happened to already be 0 or 0xFF.
fn base_vector() -> [u8; 32] {
    let mut b = [0u8; 32];
    for (i, byte) in b.iter_mut().enumerate() {
        *byte = (i as u8).wrapping_mul(37).wrapping_add(0x5a);
    }
    b
}

#[test]
fn the_deployed_pack_never_reads_sixteen_source_bits() {
    let base = base_vector();
    let reference = octet(&base);

    let mut unread = Vec::new();
    let mut read = Vec::new();
    for byte in 0..32usize {
        for bit in 0..8u8 {
            let mut flipped = base;
            flipped[byte] ^= 1 << bit;
            if octet(&flipped) == reference {
                unread.push((byte, bit));
            } else {
                read.push((byte, bit));
            }
        }
    }

    // MEASURED, not transcribed: the read-set has exactly 240 members and the unread-set exactly
    // 16, and the unread-set is precisely the one the `hi & 0x3F` shape predicts.
    assert_eq!(
        unread.len(),
        16,
        "expected 16 unread source bits, measured {}: {unread:?}",
        unread.len()
    );
    assert_eq!(read.len(), 240, "expected 240 read source bits");
    assert_eq!(
        unread.as_slice(),
        CLAIMED_UNREAD.as_slice(),
        "the unread set is not the sign/high-bit pair of every fourth byte"
    );

    // The consequence, stated as the fiber size rather than as an adjective: every octet this
    // packer emits has at least 2^16 distinct 32-byte preimages, so a SECOND PREIMAGE is one
    // bit-flip and costs no search whatsoever.
    for &(byte, bit) in &CLAIMED_UNREAD {
        let mut sibling = base;
        sibling[byte] ^= 1 << bit;
        assert_ne!(
            sibling, base,
            "the sibling must be a different 32-byte value"
        );
        assert_eq!(
            faithful(&sibling).limbs(),
            faithful(&base).limbs(),
            "the wall must not distinguish two keys differing only at byte {byte} bit {bit}"
        );
    }
}

#[test]
fn key_octet_collision_is_below_the_law_floor() {
    // Source A: the field's own prime, defined structurally in `circuit/src/field.rs` as
    // (1<<31) - (1<<27) + 1 — not a literal transcribed here.
    let log2_p = f64::from(BABYBEAR_P).log2();

    // THE FLOOR the law quotes as "~124-bit" is a BIRTHDAY COLLISION bound over a full 8-lane
    // image: 8 lanes x log2 p bits of image, halved.
    let floor_image_bits = 8.0 * log2_p;
    let floor_collision_bits = floor_image_bits / 2.0;
    assert!(
        (floor_image_bits - 247.255).abs() < 1e-2,
        "8-lane image is 247.26 bits, got {floor_image_bits}"
    );
    assert!(
        (floor_collision_bits - 123.6276).abs() < 1e-3,
        "the law's ~124-bit floor is 123.63 bits of COLLISION, got {floor_collision_bits}"
    );

    // Source B: the key octet's image, derived from the MEASURED read-set (256 source bits minus
    // the 16 the previous test proves are never read), not from the doc's "240".
    let base = base_vector();
    let reference = octet(&base);
    let mut unread = 0u32;
    for byte in 0..32usize {
        for bit in 0..8u8 {
            let mut flipped = base;
            flipped[byte] ^= 1 << bit;
            if octet(&flipped) == reference {
                unread += 1;
            }
        }
    }
    let key_image_bits = f64::from(256 - unread);
    let key_collision_bits = key_image_bits / 2.0;
    assert_eq!(key_image_bits, 240.0, "measured key-octet image bits");
    assert_eq!(key_collision_bits, 120.0);

    // THE CLAIM OF THIS LANE, in one line. 240 bits of IMAGE is not "at floor"; it is 3.63 bits
    // of COLLISION below a floor that is itself only a birthday bound.
    assert!(
        key_collision_bits < floor_collision_bits,
        "if this ever passes, the key octet reached the floor and the demotion can be reverted"
    );
    let deficit = floor_collision_bits - key_collision_bits;
    assert!(
        (deficit - 3.6276).abs() < 1e-3,
        "the deficit is 3.63 bits of collision strength, got {deficit}"
    );

    // The ninth lane is what raises it, and it clears the floor with room: 9 x log2 p / 2.
    let nine_lane_collision = 9.0 * log2_p / 2.0;
    assert!(nine_lane_collision > floor_collision_bits);
    assert!((nine_lane_collision - 139.081).abs() < 1e-2);
}

#[test]
fn an_ed25519_key_and_its_negation_pack_to_one_octet() {
    // A real curve point, and its negation. RFC 8032 5.1.2: the encoding is y little-endian with
    // the x-sign in the most significant bit of the final octet. Negation flips exactly that bit.
    let a = ED25519_BASEPOINT_POINT * Scalar::from(0x5eed_1234_9abc_def0u64);
    let minus_a = -a;

    let key_a: [u8; 32] = a.compress().to_bytes();
    let key_minus_a: [u8; 32] = minus_a.compress().to_bytes();

    // They are DIFFERENT public keys — and different in exactly one bit, the discarded sign bit.
    assert_ne!(key_a, key_minus_a);
    let mut diff_bits = Vec::new();
    for byte in 0..32usize {
        let x = key_a[byte] ^ key_minus_a[byte];
        for bit in 0..8u8 {
            if x & (1 << bit) != 0 {
                diff_bits.push((byte, bit));
            }
        }
    }
    assert_eq!(
        diff_bits,
        vec![(31usize, 7u8)],
        "the two encodings must differ in exactly the x-sign bit"
    );
    assert!(CLAIMED_UNREAD.contains(&(31, 7)), "and that bit is unread");

    // Both are valid, decompressible Edwards points of the same order — not malformed strings.
    assert!(
        curve25519_dalek::edwards::CompressedEdwardsY(key_a)
            .decompress()
            .is_some()
    );
    assert!(
        curve25519_dalek::edwards::CompressedEdwardsY(key_minus_a)
            .decompress()
            .is_some()
    );

    // THE EXHIBIT. The deployed packer, and then the type wall, collapse them onto one octet.
    assert_eq!(
        octet(&key_a),
        octet(&key_minus_a),
        "A and -A must pack identically for this exhibit to bite"
    );
    assert_eq!(faithful(&key_a).limbs(), faithful(&key_minus_a).limbs());

    // So "a colliding MEANINGFUL value costs ~2^120" is false for this key type: the cost is 0.
    // The octet the rotated pre-limbs commit at B_PUBKEY_OCTET does not distinguish the cell
    // owned by A from the cell owned by -A.
}

// ---------------------------------------------------------------------------------------------
// THE BURN-DOWN LIST, AS A GATE
// ---------------------------------------------------------------------------------------------

/// The needles are assembled with `concat!` so this file does not itself contain the literals it
/// searches for — the walk below covers every `*.rs` in the workspace, including this one, and a
/// path exclusion would be a place to hide a call site.
const HATCH_CALL: &str = concat!("from_lossy_", "31bit_DANGER(");
/// `from_canonical_key(` is a burn-down name too, because the two deployed producers reach the
/// hatch THROUGH it. Matching the open paren keeps `from_canonical_keys(` (a different function,
/// `turn::pending::ReactiveNullifierSet`) out of the set.
const KEY_CALL: &str = concat!("from_canonical", "_key(");

const LIST_BEGIN: &str = "<!-- BURN-DOWN-LIST-BEGIN -->";
const LIST_END: &str = "<!-- BURN-DOWN-LIST-END -->";

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("circuit/ has a parent")
        .to_path_buf()
}

fn collect_rs(dir: &Path, out: &mut Vec<PathBuf>) {
    let skip = ["target", ".git", "node_modules", ".lake", "lake-packages"];
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if path.is_dir() {
            if !skip.contains(&name.as_ref()) {
                collect_rs(&path, out);
            }
        } else if name.ends_with(".rs") {
            out.push(path);
        }
    }
}

/// A call site is a non-comment line mentioning a burn-down name in call position. The `fn from_`
/// filter drops the two DEFINITIONS in `circuit/src/faithful8.rs`; the call inside
/// `from_canonical_key`'s body is NOT filtered, and `faithful8.rs` is on the list because of it.
///
/// ⚠ **`tests/` directories are scoped out, and the law is what scopes them.** "Non-commitment
/// uses of the fold are out of scope and sound: … and tests." A test that CALLS the residual is
/// exercising it, not admitting it into a commitment. The exclusion is by directory rather than
/// by heuristic so it cannot be argued with — and it is safe in the one direction that matters,
/// because production code does not live in a `tests/` directory, while a `#[cfg(test)] mod` in a
/// `src/` file IS still scanned. First run of this gate went red on a sibling lane's
/// `commit/tests/key_octet_f2_twins_and_the_hole.rs`, which is how the scope question surfaced.
fn burn_down_call_sites() -> Vec<String> {
    let root = repo_root();
    let mut files = Vec::new();
    collect_rs(&root, &mut files);
    files.sort();

    let mut hits = Vec::new();
    for file in files {
        if file.components().any(|c| c.as_os_str() == "tests") {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(&file) else {
            continue;
        };
        let mut hit = false;
        for line in text.lines() {
            let t = line.trim_start();
            if t.starts_with("//") || t.contains("fn from_") {
                continue;
            }
            if t.contains(HATCH_CALL) || t.contains(KEY_CALL) {
                hit = true;
                break;
            }
        }
        if hit {
            let rel = file
                .strip_prefix(&root)
                .expect("under the repo root")
                .to_string_lossy()
                .replace('\\', "/");
            hits.push(rel);
        }
    }
    hits.sort();
    hits
}

fn law_doc() -> String {
    std::fs::read_to_string(repo_root().join("docs/FAITHFUL-COMMITMENT-LAW.md"))
        .expect("the law doc is readable")
}

fn listed_paths(doc: &str) -> Vec<String> {
    let begin = doc.find(LIST_BEGIN).expect(
        "the law doc must carry a machine-readable burn-down section — the marker is missing",
    );
    let end = doc
        .find(LIST_END)
        .expect("the burn-down section must be closed");
    assert!(begin < end, "burn-down markers are out of order");
    let mut out = Vec::new();
    for line in doc[begin..end].lines() {
        let t = line.trim_start();
        let Some(rest) = t.strip_prefix("- `") else {
            continue;
        };
        let Some(path) = rest.split('`').next() else {
            continue;
        };
        out.push(path.to_string());
    }
    out.sort();
    out
}

#[test]
fn the_burn_down_list_names_every_hatch_call_site() {
    let measured = burn_down_call_sites();
    let listed = listed_paths(&law_doc());

    // The list is NOT empty. It was recorded as "EMPTY (v13 DONE)" while the key octet rode in
    // through the front door; an empty list is a claim, and this is the instrument for it.
    assert!(
        !measured.is_empty(),
        "no burn-down call sites found at all — the walk is broken, not the tree"
    );

    let unlisted: Vec<_> = measured.iter().filter(|p| !listed.contains(p)).collect();
    assert!(
        unlisted.is_empty(),
        "burn-down call sites missing from docs/FAITHFUL-COMMITMENT-LAW.md: {unlisted:?}\n\
         Adding a degraded-octet admission without listing it is a review-time violation, and \
         this is the test that makes it a red one."
    );

    let stale: Vec<_> = listed.iter().filter(|p| !measured.contains(p)).collect();
    assert!(
        stale.is_empty(),
        "the law doc lists burn-down sites that no longer have a call: {stale:?}\n\
         A closed residual must leave the list, or the list stops meaning anything."
    );
}

#[test]
fn the_law_doc_quotes_the_bound_it_means() {
    let doc = law_doc();
    // The house error this document names is quoting an IMAGE size where a COLLISION bound is
    // meant. All three of the key octet's numbers must appear, so a reader cannot pick up the
    // flattering one by accident.
    for needle in ["2^240", "2^120", "123.63"] {
        assert!(
            doc.contains(needle),
            "the law doc must state {needle} for the key octet"
        );
    }
    // And the residual's reason string must name its closure epoch, so the grep is readable
    // without opening the doc.
    assert!(KEY_COMMIT_30BIT_RESIDUAL.contains("ninth key lane"));
    assert!(KEY_COMMIT_30BIT_RESIDUAL.contains("2^240"));
    assert!(KEY_COMMIT_30BIT_RESIDUAL.contains("collision 0"));
}
