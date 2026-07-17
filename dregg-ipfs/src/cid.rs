//! `cid` — the **CID alignment**: a dregg blake3 content commitment IS an IPFS
//! CIDv1.
//!
//! The single fact this module turns into code: **IPFS CIDs carry a blake3
//! multihash**. A dregg content commitment that is a 32-byte blake3 digest
//! (`dregg-merge`'s `Delta::id`, or a blake3 commitment over a raw blob) is, byte
//! for byte, the digest an IPFS CIDv1 wraps. So a dregg object/site/delta does not
//! get a *separate* IPFS address — its dregg content address, re-encoded, **is**
//! its IPFS address.
//!
//! ```text
//!   dregg blake3 commitment            IPFS CIDv1 (raw codec, blake3 multihash)
//!   ───────────────────────            ────────────────────────────────────────
//!   d = blake3(bytes)   (32 B)   ⇄     0x01 0x55 0x1e 0x20 ‖ d
//!                                       │    │    │    └ digest length = 32
//!                                       │    │    └ multihash code: blake3 = 0x1e
//!                                       │    └ multicodec: raw = 0x55
//!                                       └ CID version = 1
//!                                       (multibase base32-lower, prefix `b`)
//! ```
//!
//! ## Identical vs chunked (the honest boundary)
//!
//! For a **single raw blob** the CID's embedded digest is exactly `blake3(blob)` —
//! the CID *equals* the dregg content commitment, and a fetcher recomputes
//! `blake3(fetched)` and compares ([`crate::fetch_verified`]). This is the clean
//! case the bridge targets: pin the whole blob as one raw block.
//!
//! IPFS only diverges from the flat digest when it **chunks** a large file into a
//! UnixFS/DAG — then the root CID is a dag-pb hash *over the chunk links*, not
//! `blake3(file)`. The bridge handles that by committing the **DAG root CID**
//! itself in the cell (the cell commits whatever CID was pinned), and verifying the
//! fetched bytes by re-pinning/re-CIDing through the same chunker, rather than by a
//! flat re-hash. The default path keeps blobs whole (one raw block) so the clean
//! identity holds; see `docs/IPFS-INTEGRATION-PLAN.md`.

use std::fmt;

use serde::{Deserialize, Serialize};

/// The `raw` multicodec (`0x55`) — an opaque byte blob, no IPLD framing. The
/// default codec the bridge pins under, so the CID's digest is a flat
/// `blake3(blob)`.
pub const CODEC_RAW: u64 = 0x55;
/// The `dag-pb` multicodec (`0x70`) — UnixFS / a chunked file DAG root. The codec a
/// CID carries when IPFS chunked a large file.
pub const CODEC_DAG_PB: u64 = 0x70;
/// The `dag-cbor` multicodec (`0x71`) — a structured IPLD node. A natural codec for
/// committing a `dregg-merge` delta as a typed IPLD object.
pub const CODEC_DAG_CBOR: u64 = 0x71;

/// The blake3 multihash code (`0x1e`) — the alignment hinge: a blake3 digest is a
/// first-class IPFS multihash, so a dregg blake3 commitment needs no re-hashing to
/// become a CID.
pub const MH_BLAKE3: u64 = 0x1e;

/// The sha2-256 multihash code (`0x12`) — the multihash a legacy **CIDv0** (`Qm…`)
/// carries. dregg never *mints* sha2 CIDs (the alignment is blake3), but the bridge
/// parses CIDv0 so it can interoperate with content published by a stock `ipfs add`
/// (which defaults to sha2-256 / CIDv0).
pub const MH_SHA2_256: u64 = 0x12;

/// The blake3 digest width the bridge uses (the dregg content-commitment width:
/// `dregg-merge` ids, the kernel receipt hash, MMR leaves are all 32 bytes).
pub const BLAKE3_LEN: usize = 32;

/// A parsed **content identifier** — a CIDv1: a `(codec, multihash)` pair the
/// bridge reads and writes. Equality is structural (version+codec+hash+digest), so
/// two `Cid`s compare equal iff they encode to the same bytes.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Cid {
    /// The CID version. The bridge produces and expects `1`.
    pub version: u64,
    /// The multicodec of the addressed content ([`CODEC_RAW`] / [`CODEC_DAG_PB`] / …).
    pub codec: u64,
    /// The multihash function code ([`MH_BLAKE3`]).
    pub hash_code: u64,
    /// The raw digest bytes (for blake3, 32 of them).
    pub digest: Vec<u8>,
}

impl Cid {
    /// Wrap an already-computed blake3 `digest` as a CIDv1 under `codec`. This is
    /// the **alignment constructor**: hand it a dregg blake3 content commitment and
    /// it returns that commitment's CID with no re-hashing.
    pub fn from_blake3_digest(codec: u64, digest: [u8; BLAKE3_LEN]) -> Cid {
        Cid {
            version: 1,
            codec,
            hash_code: MH_BLAKE3,
            digest: digest.to_vec(),
        }
    }

    /// The CIDv1 of `bytes` pinned as a single **raw** block: `blake3(bytes)` under
    /// the `raw` codec. For a whole-blob pin this CID *equals* the dregg content
    /// commitment of `bytes`, so a fetcher re-hashes and compares.
    pub fn raw_blake3(bytes: &[u8]) -> Cid {
        Cid::from_blake3_digest(CODEC_RAW, *blake3::hash(bytes).as_bytes())
    }

    /// Whether this is a whole-blob raw CID over a 32-byte blake3 digest — the case
    /// in which [`crate::fetch_verified`] can re-witness fetched bytes by a flat
    /// `blake3` recompute.
    pub fn is_raw_blake3(&self) -> bool {
        self.version == 1
            && self.codec == CODEC_RAW
            && self.hash_code == MH_BLAKE3
            && self.digest.len() == BLAKE3_LEN
    }

    /// Whether this CID is a **dag-pb** node (UnixFS: a chunked-file DAG root, or a
    /// directory). Such a CID cannot be checked by a flat re-hash of the *content* —
    /// its digest is over the DAG node's serialized links/metadata, not the file
    /// bytes — so it is read by the verified DAG walk ([`crate::unixfs::fetch_cat`])
    /// rather than [`crate::fetch_verified`].
    pub fn is_dag_pb(&self) -> bool {
        self.version == 1 && self.codec == CODEC_DAG_PB
    }

    /// Whether the CID's digest is a blake3 multihash the bridge can re-witness a
    /// *block's own bytes* against (the block-level content-address check that holds
    /// for every block in a blake3 DAG, raw leaf or dag-pb node alike).
    pub fn is_blake3(&self) -> bool {
        self.hash_code == MH_BLAKE3 && self.digest.len() == BLAKE3_LEN
    }

    /// The digest as a fixed 32-byte array, if this is a blake3 CID.
    pub fn blake3_digest(&self) -> Option<[u8; BLAKE3_LEN]> {
        if self.hash_code != MH_BLAKE3 || self.digest.len() != BLAKE3_LEN {
            return None;
        }
        let mut out = [0u8; BLAKE3_LEN];
        out.copy_from_slice(&self.digest);
        Some(out)
    }

    /// The canonical binary CIDv1: `varint(version) ‖ varint(codec) ‖ multihash`,
    /// where `multihash = varint(hash_code) ‖ varint(len) ‖ digest`.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(8 + self.digest.len());
        put_varint(&mut out, self.version);
        put_varint(&mut out, self.codec);
        put_varint(&mut out, self.hash_code);
        put_varint(&mut out, self.digest.len() as u64);
        out.extend_from_slice(&self.digest);
        out
    }

    /// Parse a binary CIDv1 (the inverse of [`to_bytes`](Cid::to_bytes)).
    pub fn from_bytes(bytes: &[u8]) -> Result<Cid, CidError> {
        let mut p = 0usize;
        let version = take_varint(bytes, &mut p)?;
        if version != 1 {
            return Err(CidError::UnsupportedVersion(version));
        }
        let codec = take_varint(bytes, &mut p)?;
        let hash_code = take_varint(bytes, &mut p)?;
        let len = take_varint(bytes, &mut p)? as usize;
        if bytes.len() - p != len {
            return Err(CidError::DigestLength {
                declared: len,
                actual: bytes.len() - p,
            });
        }
        Ok(Cid {
            version,
            codec,
            hash_code,
            digest: bytes[p..].to_vec(),
        })
    }

    /// The canonical string CID.
    ///
    /// - **CIDv1** (`version == 1`, the form the bridge mints): multibase base32-lower
    ///   (prefix `b`) of the binary CIDv1 — what `ipfs add --cid-version=1` prints and
    ///   a gateway URL carries.
    /// - **CIDv0** (`version == 0`, a parsed legacy `Qm…`): base58btc of the bare
    ///   sha2-256 multihash, with no multibase prefix — the historical form.
    pub fn to_string_cid(&self) -> String {
        if self.version == 0 {
            // CIDv0 is base58btc of the raw multihash (no version/codec framing).
            let mut mh = Vec::with_capacity(2 + self.digest.len());
            put_varint(&mut mh, self.hash_code);
            put_varint(&mut mh, self.digest.len() as u64);
            mh.extend_from_slice(&self.digest);
            return base58btc_encode(&mh);
        }
        let mut s = String::from("b");
        s.push_str(&base32_lower_encode(&self.to_bytes()));
        s
    }

    /// Parse a string CID.
    ///
    /// - A base32-lower multibase (`b…`) is decoded as a binary **CIDv1** — the form
    ///   the bridge emits.
    /// - A bare base58btc string beginning `Q` is decoded as a legacy **CIDv0** (a
    ///   sha2-256 dag-pb node), for interop with content a stock `ipfs add` published.
    ///
    /// Other multibases (base16, base64, …) are out of scope for this bridge.
    pub fn parse(s: &str) -> Result<Cid, CidError> {
        let s = s.trim();
        let mut chars = s.chars();
        match chars.next() {
            Some('b') => {
                let raw = base32_lower_decode(chars.as_str())?;
                Cid::from_bytes(&raw)
            }
            // A bare `Qm…` is a CIDv0 (base58btc of a sha2-256 multihash).
            Some('Q') => Cid::parse_cidv0(s),
            Some(other) => Err(CidError::UnsupportedMultibase(other)),
            None => Err(CidError::Empty),
        }
    }

    /// Parse a legacy CIDv0 string (`Qm…`): base58btc of a `sha2-256` multihash
    /// (`0x12 0x20 ‖ 32-byte digest`), implicitly `dag-pb`-codec, version 0.
    fn parse_cidv0(s: &str) -> Result<Cid, CidError> {
        let mh = base58btc_decode(s)?;
        let mut p = 0usize;
        let hash_code = take_varint(&mh, &mut p)?;
        let len = take_varint(&mh, &mut p)? as usize;
        if hash_code != MH_SHA2_256 || len != 32 || mh.len() - p != len {
            return Err(CidError::BadCidV0);
        }
        Ok(Cid {
            version: 0,
            codec: CODEC_DAG_PB,
            hash_code,
            digest: mh[p..].to_vec(),
        })
    }
}

impl fmt::Display for Cid {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_string_cid())
    }
}

/// Why a CID could not be parsed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CidError {
    /// An empty CID string.
    Empty,
    /// A multibase prefix other than base32-lower (`b`).
    UnsupportedMultibase(char),
    /// A CID version other than 1.
    UnsupportedVersion(u64),
    /// A character outside the base32-lower alphabet.
    BadBase32(char),
    /// The base32 string's trailing padding bits were non-zero (or a spurious extra
    /// symbol) — a non-canonical encoding. Distinct strings that decode to the same
    /// bytes are refused so CID parsing is injective.
    NonCanonicalBase32,
    /// A character outside the base58btc alphabet.
    BadBase58(char),
    /// A `Qm…` string that is not a well-formed CIDv0 (sha2-256 / 32-byte multihash).
    BadCidV0,
    /// A varint ran past the end of the buffer.
    TruncatedVarint,
    /// A varint encoded more than 64 bits.
    VarintOverflow,
    /// The declared digest length disagrees with the remaining bytes.
    DigestLength { declared: usize, actual: usize },
}

impl fmt::Display for CidError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CidError::Empty => write!(f, "empty CID"),
            CidError::UnsupportedMultibase(c) => write!(f, "unsupported multibase prefix `{c}`"),
            CidError::UnsupportedVersion(v) => write!(f, "unsupported CID version {v}"),
            CidError::BadBase32(c) => write!(f, "invalid base32 character `{c}`"),
            CidError::NonCanonicalBase32 => {
                write!(f, "non-canonical base32 (nonzero padding bits)")
            }
            CidError::BadBase58(c) => write!(f, "invalid base58btc character `{c}`"),
            CidError::BadCidV0 => write!(f, "malformed CIDv0 (expected a sha2-256 multihash)"),
            CidError::TruncatedVarint => write!(f, "truncated varint"),
            CidError::VarintOverflow => write!(f, "varint exceeds 64 bits"),
            CidError::DigestLength { declared, actual } => {
                write!(
                    f,
                    "digest length mismatch: declared {declared}, got {actual}"
                )
            }
        }
    }
}

impl std::error::Error for CidError {}

// -- unsigned LEB128 varint (the multiformats varint) -------------------------
// (pub(crate): the CAR v1 framing in `crate::car` uses the same multiformats varint.)

pub(crate) fn put_varint(out: &mut Vec<u8>, mut v: u64) {
    loop {
        let mut byte = (v & 0x7f) as u8;
        v >>= 7;
        if v != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        if v == 0 {
            break;
        }
    }
}

pub(crate) fn take_varint(bytes: &[u8], pos: &mut usize) -> Result<u64, CidError> {
    let mut result: u64 = 0;
    let mut shift = 0u32;
    loop {
        let b = *bytes.get(*pos).ok_or(CidError::TruncatedVarint)?;
        *pos += 1;
        if shift >= 64 || (shift == 63 && (b & 0x7f) > 1) {
            return Err(CidError::VarintOverflow);
        }
        result |= ((b & 0x7f) as u64) << shift;
        if b & 0x80 == 0 {
            return Ok(result);
        }
        shift += 7;
    }
}

// -- base32 (RFC4648 lower, no padding) — multibase `b` -----------------------

const B32_ALPHABET: &[u8; 32] = b"abcdefghijklmnopqrstuvwxyz234567";

fn base32_lower_encode(data: &[u8]) -> String {
    let mut out = String::with_capacity(data.len().div_ceil(5) * 8);
    let mut buffer: u32 = 0;
    let mut bits: u32 = 0;
    for &byte in data {
        buffer = (buffer << 8) | byte as u32;
        bits += 8;
        while bits >= 5 {
            bits -= 5;
            let idx = ((buffer >> bits) & 0x1f) as usize;
            out.push(B32_ALPHABET[idx] as char);
        }
    }
    if bits > 0 {
        // Pad the final partial group with zero bits (no `=` padding in multibase).
        let idx = ((buffer << (5 - bits)) & 0x1f) as usize;
        out.push(B32_ALPHABET[idx] as char);
    }
    out
}

fn base32_lower_decode(s: &str) -> Result<Vec<u8>, CidError> {
    let mut out = Vec::with_capacity(s.len() * 5 / 8);
    let mut buffer: u32 = 0;
    let mut bits: u32 = 0;
    for c in s.chars() {
        let val = match c {
            'a'..='z' => c as u32 - 'a' as u32,
            '2'..='7' => c as u32 - '2' as u32 + 26,
            _ => return Err(CidError::BadBase32(c)),
        };
        buffer = (buffer << 5) | val;
        bits += 5;
        if bits >= 8 {
            bits -= 8;
            out.push((buffer >> bits) as u8);
        }
    }
    // Canonical, no-pad multibase base32: at most 4 leftover bits (a partial final
    // symbol group), and those bits MUST be zero. A full leftover symbol (`bits >= 5`)
    // is a spurious trailing char, and nonzero padding bits mean two distinct strings
    // would decode to the same bytes — both make CID parsing non-injective, so refuse.
    if bits >= 5 {
        return Err(CidError::NonCanonicalBase32);
    }
    if bits > 0 && (buffer & ((1u32 << bits) - 1)) != 0 {
        return Err(CidError::NonCanonicalBase32);
    }
    Ok(out)
}

// -- base58btc (the Bitcoin alphabet) — CIDv0 (`Qm…`) --------------------------

const B58_ALPHABET: &[u8; 58] = b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";

fn base58btc_encode(data: &[u8]) -> String {
    // Count leading zero bytes → leading '1's.
    let zeros = data.iter().take_while(|&&b| b == 0).count();
    // Base-256 → base-58 by repeated division (big-endian digit buffer).
    let mut digits: Vec<u8> = Vec::with_capacity(data.len() * 2);
    for &byte in data {
        let mut carry = byte as u32;
        for d in digits.iter_mut() {
            carry += (*d as u32) << 8;
            *d = (carry % 58) as u8;
            carry /= 58;
        }
        while carry > 0 {
            digits.push((carry % 58) as u8);
            carry /= 58;
        }
    }
    let mut out = String::with_capacity(zeros + digits.len());
    for _ in 0..zeros {
        out.push('1');
    }
    for &d in digits.iter().rev() {
        out.push(B58_ALPHABET[d as usize] as char);
    }
    out
}

fn base58btc_decode(s: &str) -> Result<Vec<u8>, CidError> {
    let zeros = s.chars().take_while(|&c| c == '1').count();
    let mut bytes: Vec<u8> = Vec::with_capacity(s.len());
    for c in s.chars() {
        let val = B58_ALPHABET
            .iter()
            .position(|&a| a as char == c)
            .ok_or(CidError::BadBase58(c))? as u32;
        let mut carry = val;
        for b in bytes.iter_mut() {
            carry += (*b as u32) * 58;
            *b = (carry & 0xff) as u8;
            carry >>= 8;
        }
        while carry > 0 {
            bytes.push((carry & 0xff) as u8);
            carry >>= 8;
        }
    }
    let mut out = vec![0u8; zeros];
    out.extend(bytes.iter().rev());
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn varint_round_trips() {
        for v in [
            0u64,
            1,
            0x1e,
            0x55,
            0x70,
            0x71,
            127,
            128,
            255,
            256,
            0x3fff,
            1 << 35,
            u64::MAX,
        ] {
            let mut buf = Vec::new();
            put_varint(&mut buf, v);
            let mut p = 0;
            assert_eq!(take_varint(&buf, &mut p).unwrap(), v);
            assert_eq!(p, buf.len());
        }
    }

    #[test]
    fn base32_known_vector() {
        // The first bytes of every CIDv1 raw CID are [0x01, 0x55, ...]; base32-lower
        // of [0x01, 0x55] is "afkq", so a raw CIDv1 string begins "bafk…" — the
        // ubiquitous IPFS raw-block prefix. This pins the alphabet + bit-packing.
        assert_eq!(base32_lower_encode(&[0x01, 0x55]), "afkq");
        assert_eq!(base32_lower_decode("afkq").unwrap(), vec![0x01, 0x55]);
    }

    #[test]
    fn raw_blake3_cid_embeds_the_blake3_digest() {
        let bytes = b"hello from a dregg cell";
        let cid = Cid::raw_blake3(bytes);
        // The CID's structural fields are the alignment claim.
        assert_eq!(cid.version, 1);
        assert_eq!(cid.codec, CODEC_RAW);
        assert_eq!(cid.hash_code, MH_BLAKE3);
        assert_eq!(cid.digest.len(), BLAKE3_LEN);
        assert!(cid.is_raw_blake3());
        // The embedded digest IS blake3(bytes) — the content commitment, unchanged.
        assert_eq!(
            cid.blake3_digest().unwrap(),
            *blake3::hash(bytes).as_bytes()
        );
        // And it begins with the canonical raw-block multibase prefix.
        assert!(cid.to_string_cid().starts_with("bafk"), "{}", cid);
    }

    #[test]
    fn cid_string_round_trips() {
        let cid = Cid::raw_blake3(b"round trip me");
        let s = cid.to_string_cid();
        assert_eq!(Cid::parse(&s).unwrap(), cid);
        // Binary round-trip too.
        assert_eq!(Cid::from_bytes(&cid.to_bytes()).unwrap(), cid);
    }

    #[test]
    fn from_blake3_digest_is_the_alignment_identity() {
        // A dregg blake3 commitment (e.g. a `dregg-merge` Delta::id) re-encodes to a
        // CID with NO re-hashing, and back to the exact same digest.
        let commitment = *blake3::hash(b"a dregg-merge delta").as_bytes();
        let cid = Cid::from_blake3_digest(CODEC_DAG_CBOR, commitment);
        assert_eq!(cid.blake3_digest().unwrap(), commitment);
        assert_eq!(cid.codec, CODEC_DAG_CBOR);
        assert_eq!(Cid::parse(&cid.to_string_cid()).unwrap(), cid);
    }

    #[test]
    fn parse_rejects_garbage() {
        assert_eq!(Cid::parse(""), Err(CidError::Empty));
        assert!(matches!(
            Cid::parse("zABC"),
            Err(CidError::UnsupportedMultibase('z'))
        ));
        assert!(matches!(Cid::parse("b1810"), Err(CidError::BadBase32('1'))));
    }

    #[test]
    fn base32_decode_is_canonical_strict() {
        // `blake3` raw CID base32 is canonical: 36 binary bytes → 58 symbols with 2
        // padding bits that MUST be zero. A CID string with a *different* final symbol
        // (nonzero padding bits) must NOT decode to the same digest — else two strings
        // alias one CID and parsing is not injective.
        let cid = Cid::raw_blake3(b"injectivity matters");
        let s = cid.to_string_cid();
        // Bump the final symbol to one whose low bits are set: the canonical last
        // symbol encodes the 2 real payload bits + 3 zero pad bits. Any symbol that
        // shares the top 2 bits but sets a low bit is a non-canonical alias.
        let last = s.chars().last().unwrap();
        let idx = B32_ALPHABET
            .iter()
            .position(|&a| a as char == last)
            .unwrap();
        // Flip the lowest pad bit (bit 0) — still same decoded bytes under a lax
        // decoder, but a strict decoder rejects it.
        let aliased_idx = idx ^ 0b1;
        if aliased_idx != idx {
            let mut chars: Vec<char> = s.chars().collect();
            *chars.last_mut().unwrap() = B32_ALPHABET[aliased_idx] as char;
            let aliased: String = chars.into_iter().collect();
            assert!(
                matches!(Cid::parse(&aliased), Err(CidError::NonCanonicalBase32)),
                "a non-canonical trailing symbol must be refused, not aliased"
            );
        }
        // A spurious extra symbol (a whole leftover 5-bit group — 15 bits cannot be a
        // whole number of bytes) is refused too.
        assert!(matches!(
            base32_lower_decode("aaa"),
            Err(CidError::NonCanonicalBase32)
        ));
        // `aa` (10 bits → one zero byte + 2 zero pad bits) IS canonical.
        assert_eq!(base32_lower_decode("aa").unwrap(), vec![0u8]);
    }

    #[test]
    fn base58_round_trips_and_handles_leading_zeros() {
        for v in [
            vec![],
            vec![0u8],
            vec![0, 0, 1, 2, 3],
            vec![0x12, 0x20, 0xde, 0xad, 0xbe, 0xef],
            (0u8..40).collect::<Vec<_>>(),
        ] {
            let enc = base58btc_encode(&v);
            assert_eq!(base58btc_decode(&enc).unwrap(), v, "b58 round-trip {v:?}");
        }
    }

    #[test]
    fn cidv0_parses_for_interop() {
        // Build a real sha2-256 multihash (0x12 0x20 ‖ 32 bytes) and its base58btc
        // CIDv0 string with our own encoder, then parse it back — proving the CIDv0
        // decode path (version 0, implicit dag-pb, sha2-256) round-trips.
        let digest = [0x42u8; 32];
        let mut mh = vec![MH_SHA2_256 as u8, 32];
        mh.extend_from_slice(&digest);
        let s = base58btc_encode(&mh);
        assert!(s.starts_with("Qm"), "a sha2-256 CIDv0 begins `Qm`, got {s}");

        let cid = Cid::parse(&s).unwrap();
        assert_eq!(cid.version, 0);
        assert_eq!(cid.codec, CODEC_DAG_PB);
        assert_eq!(cid.hash_code, MH_SHA2_256);
        assert_eq!(cid.digest, digest);
        // Re-renders back to the exact same CIDv0 string.
        assert_eq!(cid.to_string_cid(), s);
        // A CIDv0 is not a flat-verifiable raw blake3 blob.
        assert!(!cid.is_raw_blake3());

        // A `Qm…`-shaped string whose multihash is the wrong length is refused as a
        // malformed CIDv0 (34-byte buffer keeps the `Q` leading char, so it routes to
        // the CIDv0 parser rather than the multibase branch).
        let mut bad = vec![MH_SHA2_256 as u8, 30];
        bad.extend_from_slice(&[0u8; 32]); // declares len 30 but carries 32
        let bad_s = base58btc_encode(&bad);
        assert!(Cid::parse(&bad_s).is_err());
    }
}
