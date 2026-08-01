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
//! * `the_burn_down_list_names_every_hatch_admission` turns the law's "adding a `_DANGER` site
//!   without listing it here is a review-time violation" into something that can go red. ⚑ It is
//!   keyed on the `(file, reason-constant)` ADMISSION, not on the file path — see the section
//!   header below for the wound that keying cost.
//!
//! Nothing here changes what any encoder computes. The demotion is type- and doc-level: the
//! constructor's body is now the `_DANGER` hatch, so the octet is on the list where it belongs.
//!
//! The fix that raises the number is a NINTH key lane, and ⚠ **SAY WHICH BOUND** for the fix as
//! well as for the wound. This header used to price it at "`2^278` image, `2^139` birthday". Those
//! are the CAPACITY of nine BabyBear lanes (`9 · log₂ p` and its birthday bound) — the size of the
//! codomain, not of any encoding's image — and `2^278.16 > 2^256` is the tell, since a map out of
//! 32 bytes has at most `2^256` images. The encoding actually recommended is the base-`2^29` NONET
//! (`Dregg2.Circuit.KeyLanes9.keyToLanes9`): image EXACTLY `2^256` and INJECTIVE
//! (`keyToLanes9_injective`, from a total decoder plus a machine-checked left inverse), so **the
//! encoding step loses nothing, there is no encoding collision to bound, and the binding reduces to
//! the sponge that absorbs the lanes.** `the_nonet_separates_the_pair_the_octet_merges` exhibits
//! that on the very pair this file shows the deployed octet merging. The landing is a descriptor
//! re-emit + VK rotation + `CANONICAL_STATE_SCHEMA_EPOCH` 15 → 16 — a different lane.

use std::collections::{BTreeMap, BTreeSet};
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

    // ⚠ SAY WHICH BOUND FOR THE FIX TOO. Nine BabyBear lanes have a CAPACITY of 9 x log2 p =
    // 278.16 bits with a 139.08-bit birthday bound. This file, `faithful8.rs` and the law doc all
    // used to quote that pair as the ninth key lane's IMAGE and COLLISION. It is neither: it is the
    // size of the CODOMAIN. The tell is one comparison —
    let nine_lane_capacity_image = 9.0 * log2_p;
    let nine_lane_capacity_collision = nine_lane_capacity_image / 2.0;
    assert!((nine_lane_capacity_image - 278.163).abs() < 1e-2);
    assert!((nine_lane_capacity_collision - 139.081).abs() < 1e-2);
    assert!(
        nine_lane_capacity_image > 256.0,
        "THE TELL: 2^{nine_lane_capacity_image} exceeds the 2^256 source, so it cannot be the image \
         of any encoding of 32 bytes — it is what nine lanes can HOLD"
    );
    assert!(nine_lane_capacity_collision > floor_collision_bits);

    // THE ENCODING ACTUALLY RECOMMENDED is the base-2^29 nonet (`Dregg2.Circuit.KeyLanes9`'s
    // `keyToLanes9`, injective in Lean by a total decoder and a machine-checked left inverse). Its
    // arithmetic, recomputed from BABYBEAR_P rather than quoted: the radix sits below p so no lane
    // reduces, and eight lanes of 29 bits leave a top lane of 24 — 2^256 on the nose.
    const NONET_RADIX_BITS: u32 = 29;
    assert!(
        f64::from(1u32 << NONET_RADIX_BITS) < f64::from(BABYBEAR_P),
        "the nonet radix must sit below p, else a lane reduces and injectivity dies"
    );
    let top_lane_bits = 256 - 8 * NONET_RADIX_BITS;
    assert_eq!(top_lane_bits, 24, "the top lane's width");
    assert!(
        top_lane_bits > 0 && top_lane_bits <= NONET_RADIX_BITS,
        "nine lanes at this radix must cover 256 bits with the top lane no wider than the radix"
    );
    // And eight cannot, whatever the lanes carry — the same pigeonhole as `floor_image_bits`.
    assert!(
        floor_image_bits < 256.0,
        "if eight lanes ever held 2^256 the ninth would be unnecessary"
    );

    // ⚑ THE HONEST SENTENCE: image EXACTLY 2^256, INJECTIVE, so the encoding step loses nothing and
    // the binding reduces to the sponge. NOT "2^139.08 of collision" — no encoding collision
    // exists at all. `the_nonet_separates_the_pair_the_octet_merges` is the exhibit.
    let nonet_image_bits = f64::from(8 * NONET_RADIX_BITS + top_lane_bits);
    assert_eq!(nonet_image_bits, 256.0);
}

/// The `A` / `−A` pair that the deployed octet merges gets DISTINCT base-`2^29` nonets, and the
/// nonet round-trips. This is what "injective, so the encoding step loses nothing" means on the
/// exact object the previous test exhibits as free.
///
/// ⚠ **SUBSTRATE, said out loud: this is ARITHMETIC IN A TEST, not an encoder.** The ninth-lane
/// encoder is Lean-authored (`Dregg2.Circuit.KeyLanes9.keyToLanes9`, with `keyToLanes9_injective`
/// and `keyLanes9ToBytes_keyToLanes9`) and is NOT deployed anywhere. No Rust file in this tree may
/// author it; these ten lines read bits out of a byte array to exhibit a difference.
#[test]
fn the_nonet_separates_the_pair_the_octet_merges() {
    /// Bits `[29i, 29i+29)` of the 32 bytes read as a little-endian 256-bit integer.
    fn lane(b: &[u8; 32], i: usize) -> u32 {
        let mut v = 0u32;
        for k in 0..29usize {
            let bit = 29 * i + k;
            if bit >= 256 {
                break;
            }
            if (b[bit / 8] >> (bit % 8)) & 1 == 1 {
                v |= 1 << k;
            }
        }
        v
    }
    fn nonet(b: &[u8; 32]) -> [u32; 9] {
        std::array::from_fn(|i| lane(b, i))
    }
    fn unnonet(lanes: [u32; 9]) -> [u8; 32] {
        let mut out = [0u8; 32];
        for (i, l) in lanes.iter().enumerate() {
            for k in 0..29usize {
                let bit = 29 * i + k;
                if bit >= 256 {
                    break;
                }
                if (l >> k) & 1 == 1 {
                    out[bit / 8] |= 1 << (bit % 8);
                }
            }
        }
        out
    }

    let a = ED25519_BASEPOINT_POINT * Scalar::from(0x5eed_1234_9abc_def0u64);
    let key_a: [u8; 32] = a.compress().to_bytes();
    let key_minus_a: [u8; 32] = (-a).compress().to_bytes();

    // The premise, re-measured here so this test does not depend on another one having run.
    assert_eq!(
        octet(&key_a),
        octet(&key_minus_a),
        "the deployed 8-lane pack must merge them"
    );

    let na = nonet(&key_a);
    let nma = nonet(&key_minus_a);
    assert_ne!(
        na, nma,
        "the base-2^29 nonet must SEPARATE the pair the deployed octet merges"
    );

    // Every lane is a legal BabyBear value with no reduction, and the top lane is the narrow one.
    for (i, l) in na.iter().chain(nma.iter()).enumerate() {
        assert!(*l < 1 << 29, "lane {i} must be below the radix");
        assert!(
            u64::from(*l) < u64::from(BABYBEAR_P),
            "lane {i} must not reduce"
        );
    }
    assert!(
        na[8] < 1 << 24 && nma[8] < 1 << 24,
        "the top lane carries 24 bits"
    );

    // The left inverse, on these two and on a full-range vector: what makes it INJECTIVE rather
    // than merely wide.
    assert_eq!(unnonet(na), key_a);
    assert_eq!(unnonet(nma), key_minus_a);
    let dense = base_vector();
    assert_eq!(unnonet(nonet(&dense)), dense);
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
// THE BURN-DOWN LIST, AS A GATE — KEYED ON THE ADMISSION, NOT ON THE FILE
// ---------------------------------------------------------------------------------------------
//
// ⚑ **The wound this rewrite closes, measured 2026-08-01.** The first version of this gate pushed
// a FILE PATH once per file (`hit = true; break;` on the first match). It caught a new file with a
// hatch call — and it was BLIND exactly where the next degraded octet gets added, because the three
// listed files are the two deployed producers and the wall itself. A second, DISTINCT residual
// declared inside `circuit/src/faithful8.rs` and admitted through a new router passed 5/5. A gate
// whose stated purpose is "a documented wound is not a detected one" could not see the wound it
// guards.
//
// The key is now the pair `(file, reason-constant)`. `(file, line)` would have been the obvious
// alternative and it is worse: it goes red on every reflow, so it would be relaxed within a week.
// The reason constant survives a reformat and names the thing being admitted.

/// The needles are assembled with `concat!` so this file does not itself contain the literals it
/// searches for — the walk below covers every `*.rs` in the workspace, including this one, and a
/// path exclusion would be a place to hide a call site.
const HATCH: &str = concat!("from_lossy_", "31bit_DANGER");

/// The hatch's own source file. Two things are read out of it and NEITHER is transcribed here: the
/// set of ROUTERS (constructors whose body calls the hatch, so that calling one is an admission
/// even though the call site never names the hatch), and the `&str` REASON CONSTANTS with their
/// values. `from_canonical_key` is a router because its body is
/// `Self::from_lossy_31bit_DANGER(KEY_COMMIT_30BIT_RESIDUAL, limbs)` — measured, so a second
/// constructor that does the same becomes a router the moment it is written.
const HATCH_SRC: &str = "circuit/src/faithful8.rs";

const LIST_BEGIN: &str = "<!-- BURN-DOWN-LIST-BEGIN -->";
const LIST_END: &str = "<!-- BURN-DOWN-LIST-END -->";

/// One admission: the file that makes it, and the reason constant it is made under.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct Admission {
    file: String,
    reason: String,
}

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

fn hatch_source() -> String {
    std::fs::read_to_string(repo_root().join(HATCH_SRC))
        .expect("the hatch's own source is readable")
}

/// The first argument of the call whose `(` sits at byte `open`, as written. Depth- and
/// string-aware, and it spans lines, so a rustfmt-wrapped call still yields its reason.
fn first_arg(text: &str, open: usize) -> String {
    let mut depth = 0i32;
    let mut in_str = false;
    let mut escaped = false;
    let mut out = String::new();
    for c in text[open + 1..].chars() {
        if in_str {
            out.push(c);
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                in_str = false;
            }
            continue;
        }
        match c {
            '"' => {
                in_str = true;
                out.push(c);
            }
            '(' | '[' | '{' => {
                depth += 1;
                out.push(c);
            }
            ')' | ']' | '}' => {
                if depth == 0 {
                    break;
                }
                depth -= 1;
                out.push(c);
            }
            ',' if depth == 0 => break,
            _ => out.push(c),
        }
    }
    out.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// The declared name of the `fn` a line opens, if it opens one (`fn f(`, `pub fn f(`,
/// `pub(crate) const fn f(` all qualify).
fn declared_fn(line: &str) -> Option<String> {
    let at = line.find("fn ")?;
    let rest = &line[at + 3..];
    let end = rest.find('(')?;
    let name = rest[..end].trim();
    if name.is_empty() || !name.chars().all(|c| c.is_alphanumeric() || c == '_') {
        return None;
    }
    Some(name.to_string())
}

/// Is the needle occurrence at `at` a DEFINITION rather than a call? Precise where the old
/// `contains("fn from_")` filter was a heuristic: the text immediately before the name is `fn`.
fn is_definition(line: &str, at: usize) -> bool {
    line[..at].trim_end().ends_with("fn")
}

/// Occurrences of `name(` on a non-comment line, as `(byte-offset-of-the-paren)`.
fn call_parens(text: &str, line: &str, line_start: usize, name: &str) -> Vec<usize> {
    let needle = format!("{name}(");
    let mut out = Vec::new();
    let mut from = 0usize;
    while let Some(rel) = line[from..].find(&needle) {
        let at = from + rel;
        from = at + needle.len();
        if !is_definition(line, at) {
            out.push(line_start + at + name.len());
        }
    }
    let _ = text;
    out
}

/// The ROUTERS: constructors in the hatch's own file whose body calls the hatch, mapped to the
/// reason they pass. DERIVED, not transcribed — `from_canonical_key` is here because its body
/// reads `Self::from_lossy_31bit_DANGER(KEY_COMMIT_30BIT_RESIDUAL, limbs)`, and a second such
/// constructor becomes a router the moment somebody writes one.
fn routers(src: &str) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    let mut current: Option<String> = None;
    let mut offset = 0usize;
    for line in src.split_inclusive('\n') {
        let start = offset;
        offset += line.len();
        let t = line.trim_start();
        if t.starts_with("//") {
            continue;
        }
        if let Some(name) = declared_fn(line) {
            current = Some(name);
        }
        for paren in call_parens(src, line, start, HATCH) {
            let Some(owner) = current.clone() else {
                continue;
            };
            if owner == HATCH {
                continue;
            }
            out.insert(owner, first_arg(src, paren));
        }
    }
    out
}

/// A minimal Rust `&str` literal reader — `\\`, `\"`, `\n`, `\t`, `\r`, and the LINE CONTINUATION
/// (`\` before a newline swallows the newline and the next line's indent), which is how
/// `KEY_COMMIT_30BIT_RESIDUAL` is written. `None` on anything it does not understand, and an
/// unresolvable reason FAILS the gate rather than being quietly skipped.
fn read_str_literal(text: &str) -> Option<String> {
    let mut chars = text.chars();
    if chars.next()? != '"' {
        return None;
    }
    let mut out = String::new();
    while let Some(c) = chars.next() {
        match c {
            '"' => return Some(out),
            '\\' => match chars.next()? {
                '\\' => out.push('\\'),
                '"' => out.push('"'),
                'n' => out.push('\n'),
                't' => out.push('\t'),
                'r' => out.push('\r'),
                '\n' => {
                    let mut peek = chars.clone();
                    while let Some(w) = peek.next() {
                        if w.is_whitespace() {
                            chars = peek.clone();
                        } else {
                            break;
                        }
                    }
                }
                _ => return None,
            },
            _ => out.push(c),
        }
    }
    None
}

/// The `&str` reason constants declared beside the hatch, by name, with their values — PARSED from
/// the source rather than linked, so a residual whose constant is not `pub` (or that this test
/// never imported) is still resolvable and still gated.
fn reason_constants(src: &str) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    let mut rest = src;
    while let Some(at) = rest.find("const ") {
        let after = &rest[at + "const ".len()..];
        rest = after;
        let Some(colon) = after.find(':') else {
            continue;
        };
        let name = after[..colon].trim();
        if name.is_empty()
            || !name
                .chars()
                .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_')
        {
            continue;
        }
        let Some(tail) = after[colon + 1..].trim_start().strip_prefix("&str") else {
            continue;
        };
        let Some(tail) = tail.trim_start().strip_prefix('=') else {
            continue;
        };
        let Some(value) = read_str_literal(tail.trim_start()) else {
            continue;
        };
        out.insert(name.to_string(), value);
    }
    out
}

/// Every admission in the tree, as `(file, reason)` pairs. A call to the hatch contributes the
/// reason it passes; a call to a ROUTER contributes the reason that router's body passes.
///
/// ⚠ **`tests/` directories are scoped out, and the law is what scopes them.** "Non-commitment
/// uses of the fold are out of scope and sound: … and tests." A test that CALLS the residual is
/// exercising it, not admitting it into a commitment. The exclusion is by directory rather than
/// by heuristic so it cannot be argued with — and it is safe in the one direction that matters,
/// because production code does not live in a `tests/` directory, while a `#[cfg(test)] mod` in a
/// `src/` file IS still scanned. First run of this gate went red on a sibling lane's
/// `commit/tests/key_octet_f2_twins_and_the_hole.rs`, which is how the scope question surfaced.
fn burn_down_admissions(routers: &BTreeMap<String, String>) -> BTreeSet<Admission> {
    let root = repo_root();
    let mut files = Vec::new();
    collect_rs(&root, &mut files);
    files.sort();

    let mut out = BTreeSet::new();
    for file in files {
        if file.components().any(|c| c.as_os_str() == "tests") {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(&file) else {
            continue;
        };
        let rel = file
            .strip_prefix(&root)
            .expect("under the repo root")
            .to_string_lossy()
            .replace('\\', "/");

        let mut offset = 0usize;
        for line in text.split_inclusive('\n') {
            let start = offset;
            offset += line.len();
            if line.trim_start().starts_with("//") {
                continue;
            }
            for paren in call_parens(&text, line, start, HATCH) {
                out.insert(Admission {
                    file: rel.clone(),
                    reason: first_arg(&text, paren),
                });
            }
            for (router, reason) in routers {
                if call_parens(&text, line, start, router).is_empty() {
                    continue;
                }
                out.insert(Admission {
                    file: rel.clone(),
                    reason: reason.clone(),
                });
            }
        }
    }
    out
}

fn law_doc() -> String {
    std::fs::read_to_string(repo_root().join("docs/FAITHFUL-COMMITMENT-LAW.md"))
        .expect("the law doc is readable")
}

fn burn_down_section(doc: &str) -> String {
    let begin = doc.find(LIST_BEGIN).expect(
        "the law doc must carry a machine-readable burn-down section — the marker is missing",
    );
    let end = doc
        .find(LIST_END)
        .expect("the burn-down section must be closed");
    assert!(begin < end, "burn-down markers are out of order");
    doc[begin..end].to_string()
}

/// The listed admissions: an entry reads ``- `<path>` — `<REASON_CONST>` — prose``, and the first
/// two code spans on the line are the key. Continuation lines carry no `- ` and are ignored.
fn listed_admissions(section: &str) -> BTreeSet<Admission> {
    let mut out = BTreeSet::new();
    for line in section.lines() {
        let t = line.trim_start();
        if !t.starts_with("- `") {
            continue;
        }
        let spans: Vec<&str> = t.split('`').skip(1).step_by(2).collect();
        assert!(
            spans.len() >= 2,
            "a burn-down entry must read: - `<path>` — `<REASON_CONST>` — why. Got: {t}"
        );
        assert!(
            spans[1]
                .chars()
                .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_'),
            "the SECOND code span of a burn-down entry is the reason constant, not prose. Got \
             `{}` on: {t}",
            spans[1]
        );
        out.insert(Admission {
            file: spans[0].to_string(),
            reason: spans[1].to_string(),
        });
    }
    out
}

#[test]
fn the_burn_down_list_names_every_hatch_admission() {
    let src = hatch_source();
    let routers = routers(&src);

    // ANTI-VACUITY on the DERIVATION, before anything is compared. If the router scan came back
    // empty, both deployed producers would silently vanish from the measured set — a green gate
    // over an unwatched tree, which is the failure this whole file exists to make impossible.
    assert!(
        !routers.is_empty(),
        "no hatch router derived from {HATCH_SRC} — the scan is broken, not the tree"
    );
    let key_router = concat!("from_canonical", "_key");
    assert!(
        routers.contains_key(key_router),
        "the deployed key-octet router is not among the derived routers {:?} — the two producers \
         reach the hatch THROUGH it, so losing it blinds the walk",
        routers.keys().collect::<Vec<_>>()
    );

    let measured = burn_down_admissions(&routers);

    // The list is NOT empty. It was recorded as "EMPTY (v13 DONE)" while the key octet rode in
    // through the front door; an empty list is a claim, and this is the instrument for it.
    assert!(
        !measured.is_empty(),
        "no burn-down admissions found at all — the walk is broken, not the tree"
    );

    let doc = law_doc();
    let section = burn_down_section(&doc);
    let listed = listed_admissions(&section);

    let unlisted: Vec<_> = measured.difference(&listed).collect();
    assert!(
        unlisted.is_empty(),
        "burn-down admissions missing from docs/FAITHFUL-COMMITMENT-LAW.md: {unlisted:#?}\n\
         The key is (file, reason), so a SECOND residual inside a file already on the list is a \
         new entry and must be written down. Adding a degraded-octet admission without listing it \
         is a review-time violation, and this is the test that makes it a red one."
    );

    let stale: Vec<_> = listed.difference(&measured).collect();
    assert!(
        stale.is_empty(),
        "the law doc lists burn-down admissions that no longer exist: {stale:#?}\n\
         A closed residual must leave the list, or the list stops meaning anything."
    );

    // ⚑ AND THE REASON ITSELF MUST BE IN THE DOC, VERBATIM. Keying on the constant NAME is only
    // half of it: the name is a label, and the doc has to carry what it labels. This is generic
    // over the residuals, which is what the previous version was not — it asserted three
    // hand-picked needles, so a second residual's reason went unchecked entirely.
    let consts = reason_constants(&src);
    for admission in &measured {
        let value = consts.get(&admission.reason).unwrap_or_else(|| {
            panic!(
                "the reason `{}` admitted in {} is not a `&str` constant declared beside the hatch \
                 in {HATCH_SRC}. Declare it there: the burn-down grep and the law doc need one \
                 source, and an inline literal gives them two.",
                admission.reason, admission.file
            )
        });
        assert!(
            value.trim().len() > 20,
            "the reason `{}` is too thin to be a residual's justification: {value:?}",
            admission.reason
        );
        assert!(
            section.contains(value.as_str()),
            "the burn-down section of docs/FAITHFUL-COMMITMENT-LAW.md does not quote the reason \
             `{}` VERBATIM. The doc and the constant must not drift.\n  wanted: {value}",
            admission.reason
        );
    }
}

#[test]
fn the_law_doc_quotes_the_bound_it_means() {
    let doc = law_doc();

    // The house error this document names is quoting an IMAGE size where a COLLISION bound is
    // meant. All three of the key octet's numbers must appear, so a reader cannot pick up the
    // flattering one by accident. ⚑ The needles are DERIVED from `BABYBEAR_P` and from this file's
    // own measurement of the deployed packer, not transcribed — a pin against a transcription is
    // decoration.
    let log2_p = f64::from(BABYBEAR_P).log2();
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
    let image_bits = 256 - unread;
    for needle in [
        format!("2^{image_bits}"),            // the IMAGE, 2^240
        format!("2^{}", image_bits / 2),      // the BIRTHDAY COLLISION, 2^120
        format!("{:.2}", 8.0 * log2_p / 2.0), // the FLOOR, 123.63
    ] {
        assert!(
            doc.contains(&needle),
            "the law doc must state {needle} for the key octet"
        );
    }

    // ⚠ AND IT MUST NOT QUOTE THE FLATTERING NUMBER OF THE FIX. `2^278.16` / `2^139.08` are the
    // CAPACITY of nine BabyBear lanes; they were written into this document, into `faithful8.rs`
    // and into this file's own header as the ninth key lane's IMAGE and COLLISION — inside the
    // section that forbids exactly that substitution.
    //
    // ⚑ A NEGATIVE textual check is the wrong instrument here and the first draft of this test
    // used one: `!doc.contains("2^278.16 image")` passed only because markdown puts a backtick
    // between the two words, so it could not have gone red for the regression it named — and it
    // would also fight the corrective prose, which has to QUOTE the wrong sentence to record it.
    // The gate is instead POSITIVE and ANCHORED: the paragraph that prices the ninth key lane must
    // carry what the encoding actually is.
    assert!(
        9.0 * log2_p > 256.0,
        "the tell, restated from BABYBEAR_P: nine lanes hold more than the 2^256 source, so \
         2^{:.2} is a CAPACITY and cannot be any encoding's image",
        9.0 * log2_p
    );

    const ANCHOR: &str = "What closes it: a NINTH key lane";
    let at = doc
        .find(ANCHOR)
        .expect("the law doc must price the ninth key lane under a findable heading");
    let window: String = doc[at..].chars().take(1000).collect();
    for needle in [
        "2^256",                 // the nonet's image, exactly
        "INJECTIVE",             // what it is, and the reason there is no collision term
        "keyToLanes9_injective", // the Lean theorem, nameable
        "CAPACITY",              // and the 2^278.16 pair labelled for what it is
    ] {
        assert!(
            window.contains(needle),
            "the law doc's ninth-key-lane paragraph must say {needle}. The honest sentence is: \
             image exactly 2^256, INJECTIVE, so the encoding step loses nothing and the binding \
             reduces to the sponge — NOT a 2^{:.2} image with a 2^{:.2} birthday bound, which is \
             the nine-lane CAPACITY.\n--- paragraph as found ---\n{window}",
            9.0 * log2_p,
            9.0 * log2_p / 2.0
        );
    }

    // The same correction, at the constructor that carries the residual — the site a reader hits
    // first is the doc comment, not this document.
    let src = hatch_source();
    for needle in ["keyToLanes9_injective", "image exactly `2^256`", "CAPACITY"] {
        assert!(
            src.contains(needle),
            "{HATCH_SRC} must say {needle} where it prices the ninth key lane"
        );
    }

    // And the residual's reason string must name its closure epoch, so the grep is readable
    // without opening the doc. (The doc-side of this is generic in the burn-down test above.)
    assert!(KEY_COMMIT_30BIT_RESIDUAL.contains("ninth key lane"));
    assert!(KEY_COMMIT_30BIT_RESIDUAL.contains(&format!("image 2^{image_bits}")));
    assert!(KEY_COMMIT_30BIT_RESIDUAL.contains("collision 0"));
}
