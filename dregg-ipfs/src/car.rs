//! `car` — **CAR v1** export/import: a root CID + its block closure as one byte
//! stream, verify-don't-trust on the way back in.
//!
//! A [CAR v1] (Content Addressable aRchive) is the interchange format the IPFS
//! ecosystem moves DAGs around in (`ipfs dag export/import`, pinning-service uploads,
//! Filecoin deals). The format is deliberately simple:
//!
//! ```text
//!   varint(header_len) ‖ header            header = dag-cbor {version: 1, roots: [CID]}
//!   varint(frame_len)  ‖ CID ‖ block       … repeated, one frame per block
//! ```
//!
//! Everything is length-delimited by the multiformats varint (the same one CIDs use).
//!
//! ## Honest encoding scope
//!
//! The header's dag-cbor is **hand-encoded for the fixed shape** `{version: 1,
//! roots: [<one CID>]}` — canonical deterministic CBOR (map keys sorted `roots` <
//! `version` by the length-first rule, tag 42 + identity-multibase byte string for
//! the CID, exactly what go-car writes for a single-root CAR) — rather than pulling a
//! CBOR dependency into this deliberately dependency-light crate. The decoder reads
//! only that shape (either key order, ≥1 roots); a CAR whose header uses richer CBOR
//! is refused, not misread. CARv2 (it wraps a v1 payload in an index envelope) is out
//! of scope.
//!
//! ## The import teeth
//!
//! [`import_car`] refuses — never partially ingests — a CAR that fails ANY of:
//!
//! - **block re-witness**: every frame's block bytes must blake3-hash to its CID's
//!   digest ([`CarError::BlockDigestMismatch`]); a non-blake3 CID cannot be
//!   re-witnessed and is refused ([`CarError::NotBlake3`]) rather than trusted;
//! - **root presence**: every header root must be among the CAR's blocks
//!   ([`CarError::RootNotPresent`]);
//! - **closure**: every link every `dag-pb` block makes must resolve to a block in
//!   the CAR ([`CarError::IncompleteDag`]) — a CAR is a *closure*, and a frame whose
//!   CID was bit-flipped (block still self-consistent under the flipped CID) breaks
//!   the closure and is caught here;
//! - **framing**: truncated/overrunning varints, a malformed CID, trailing bytes.
//!
//! Since `import_car` returns the whole verified block set or an error, a tampered
//! CAR is a named refusal with nothing ingested.
//!
//! [CAR v1]: https://ipld.io/specs/transport/car/carv1/

use std::collections::HashMap;
use std::fmt;

use crate::cid::{Cid, put_varint, take_varint};
use crate::client::{IpfsClient, IpfsError};
use crate::unixfs::{Block, dag_pb_links};

/// Why a CAR stream could not be exported or imported. Every arm is a named refusal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CarError {
    /// The stream ended inside a varint, frame, or header.
    Truncated(String),
    /// The header is not the fixed dag-cbor shape `{version: 1, roots: [CID…]}`.
    BadHeader(String),
    /// The header declares a CAR version other than 1.
    UnsupportedVersion(u64),
    /// A frame's CID could not be parsed (only CIDv1 appears in dregg CARs).
    BadCid(String),
    /// A CID whose multihash is not 32-byte blake3 — this bridge cannot re-witness
    /// the block against it, so it is refused rather than trusted.
    NotBlake3(String),
    /// **The tamper tooth**: a frame's block bytes do not hash to its CID's digest.
    BlockDigestMismatch { cid: String, got: String },
    /// A header root is not among the CAR's blocks.
    RootNotPresent(String),
    /// A `dag-pb` block links a CID that is not in the CAR — the block closure is
    /// broken (also what a bit-flip inside a frame's CID bytes decays into).
    IncompleteDag { parent: String, missing: String },
    /// A `dag-pb` block's links could not be parsed.
    BadDagNode(String),
    /// Bytes remain after the last well-formed frame.
    TrailingBytes(usize),
}

impl fmt::Display for CarError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CarError::Truncated(w) => write!(f, "truncated CAR stream: {w}"),
            CarError::BadHeader(e) => write!(f, "malformed CAR header: {e}"),
            CarError::UnsupportedVersion(v) => write!(f, "unsupported CAR version {v}"),
            CarError::BadCid(e) => write!(f, "malformed CID in CAR frame: {e}"),
            CarError::NotBlake3(c) => {
                write!(
                    f,
                    "CID {c} is not blake3 — its block cannot be re-witnessed"
                )
            }
            CarError::BlockDigestMismatch { cid, got } => {
                write!(f, "CAR block hashes to {got}, not its declared CID {cid}")
            }
            CarError::RootNotPresent(c) => {
                write!(f, "CAR header root {c} is not among the CAR's blocks")
            }
            CarError::IncompleteDag { parent, missing } => write!(
                f,
                "dag-pb block {parent} links {missing}, which is not in the CAR"
            ),
            CarError::BadDagNode(e) => write!(f, "unparseable dag-pb block in CAR: {e}"),
            CarError::TrailingBytes(n) => write!(f, "{n} trailing bytes after the last frame"),
        }
    }
}

impl std::error::Error for CarError {}

/// A verified, fully-parsed CAR v1: the header roots + every block, each already
/// re-witnessed against its CID and closure-checked ([`import_car`]).
#[derive(Clone, Debug)]
pub struct CarContents {
    /// The header's root CIDs (each guaranteed present among [`blocks`](Self::blocks)).
    pub roots: Vec<Cid>,
    /// Every block, in frame order (duplicate frames deduplicated, first kept).
    pub blocks: Vec<Block>,
}

// ── export ─────────────────────────────────────────────────────────────────────

/// Serialize `root` + `blocks` (its block closure) as a CAR v1 byte stream.
///
/// The same teeth as import run on the way OUT — a caller cannot export an archive
/// this module would refuse to read back: every block is re-witnessed against its CID
/// ([`CarError::BlockDigestMismatch`] / [`CarError::NotBlake3`]), the root must be
/// among the blocks, and the dag-pb closure must be complete. Duplicate blocks (same
/// CID) are written once, first occurrence order kept.
pub fn export_car(root: &Cid, blocks: &[Block]) -> Result<Vec<u8>, CarError> {
    let deduped = verify_block_set(std::slice::from_ref(root), blocks)?;

    let mut out = Vec::new();
    let header = encode_header(root);
    put_varint(&mut out, header.len() as u64);
    out.extend_from_slice(&header);
    for block in &deduped {
        let cid_bytes = block.cid.to_bytes();
        put_varint(&mut out, (cid_bytes.len() + block.bytes.len()) as u64);
        out.extend_from_slice(&cid_bytes);
        out.extend_from_slice(&block.bytes);
    }
    Ok(out)
}

// ── import ─────────────────────────────────────────────────────────────────────

/// Read a CAR v1 stream back, **re-witnessing every block against its CID** and
/// checking root presence + dag-pb closure before returning anything (the module
/// header lists every refusal). A tampered CAR is a named [`CarError`], never a
/// partial ingest.
pub fn import_car(bytes: &[u8]) -> Result<CarContents, CarError> {
    let mut p = 0usize;

    // Header envelope: varint(len) ‖ dag-cbor header.
    let header_len = take_varint(bytes, &mut p)
        .map_err(|e| CarError::Truncated(format!("header length varint: {e}")))?
        as usize;
    let header_end = p
        .checked_add(header_len)
        .filter(|&e| e <= bytes.len())
        .ok_or_else(|| CarError::Truncated("header overruns the stream".into()))?;
    let roots = decode_header(&bytes[p..header_end])?;
    p = header_end;

    // Frames: varint(len) ‖ CID ‖ block, to the end of the stream.
    let mut blocks: Vec<Block> = Vec::new();
    while p < bytes.len() {
        let frame_len = take_varint(bytes, &mut p)
            .map_err(|e| CarError::Truncated(format!("frame length varint: {e}")))?
            as usize;
        let frame_end = p
            .checked_add(frame_len)
            .filter(|&e| e <= bytes.len())
            .ok_or_else(|| CarError::Truncated("frame overruns the stream".into()))?;
        let frame = &bytes[p..frame_end];
        let mut fp = 0usize;
        let cid = parse_cid_prefix(frame, &mut fp)?;
        blocks.push(Block {
            cid,
            bytes: frame[fp..].to_vec(),
        });
        p = frame_end;
    }
    if p != bytes.len() {
        return Err(CarError::TrailingBytes(bytes.len() - p));
    }

    let blocks = verify_block_set(&roots, &blocks)?;
    Ok(CarContents { roots, blocks })
}

/// [`import_car`] + ingest: fully verify the CAR, then store every block on `client`
/// and pin the roots. Because verification completes BEFORE the first `put_block`, a
/// tampered CAR leaves the client untouched. Returns the roots.
pub fn import_car_into<C: IpfsClient>(client: &C, bytes: &[u8]) -> Result<Vec<Cid>, IpfsError> {
    let car = import_car(bytes).map_err(|e| IpfsError::BadResponse(format!("CAR import: {e}")))?;
    for block in &car.blocks {
        client.put_block(&block.cid, &block.bytes)?;
    }
    for root in &car.roots {
        client.pin(root)?;
    }
    Ok(car.roots)
}

// ── the shared verifier: re-witness + root presence + closure ──────────────────

/// The checks shared by export and import: every block blake3-re-witnessed against
/// its CID, every root present, every dag-pb link resolving inside the set.
/// Returns the deduplicated blocks (first occurrence order).
fn verify_block_set(roots: &[Cid], blocks: &[Block]) -> Result<Vec<Block>, CarError> {
    let mut present: HashMap<Vec<u8>, ()> = HashMap::new();
    let mut deduped: Vec<Block> = Vec::new();
    for block in blocks {
        if !block.cid.is_blake3() {
            return Err(CarError::NotBlake3(block.cid.to_string_cid()));
        }
        let got = *blake3::hash(&block.bytes).as_bytes();
        if got.as_slice() != block.cid.digest.as_slice() {
            return Err(CarError::BlockDigestMismatch {
                cid: block.cid.to_string_cid(),
                got: Cid::from_blake3_digest(block.cid.codec, got).to_string_cid(),
            });
        }
        if present.insert(block.cid.to_bytes(), ()).is_none() {
            deduped.push(block.clone());
        }
    }
    for root in roots {
        if !present.contains_key(&root.to_bytes()) {
            return Err(CarError::RootNotPresent(root.to_string_cid()));
        }
    }
    // Closure: every dag-pb block's links resolve within the set. (Raw blocks link
    // nothing.) This is also what catches a bit-flip inside a frame's CID bytes: the
    // block still self-hashes under the flipped CID, but its parent's link now
    // dangles.
    for block in &deduped {
        if block.cid.is_dag_pb() {
            let links =
                dag_pb_links(&block.bytes).map_err(|e| CarError::BadDagNode(e.to_string()))?;
            for link in links {
                if !present.contains_key(&link.to_bytes()) {
                    return Err(CarError::IncompleteDag {
                        parent: block.cid.to_string_cid(),
                        missing: link.to_string_cid(),
                    });
                }
            }
        }
    }
    Ok(deduped)
}

// ── the fixed-shape dag-cbor header ─────────────────────────────────────────────

/// Encode the CAR v1 header for one root: canonical deterministic dag-cbor of
/// `{version: 1, roots: [root]}`. Keys sort `roots` < `version` (length-first). The
/// CID is tag 42 over a byte string carrying the identity-multibase prefix `0x00`
/// then the binary CIDv1 — the dag-cbor CID convention.
fn encode_header(root: &Cid) -> Vec<u8> {
    let mut out = Vec::new();
    out.push(0xa2); // map(2)
    // "roots": [ tag42( 0x00 ‖ cid ) ]
    cbor_text(&mut out, "roots");
    out.push(0x81); // array(1)
    out.extend_from_slice(&[0xd8, 0x2a]); // tag(42)
    let cid_bytes = root.to_bytes();
    let mut payload = Vec::with_capacity(1 + cid_bytes.len());
    payload.push(0x00); // identity multibase prefix
    payload.extend_from_slice(&cid_bytes);
    cbor_bytes(&mut out, &payload);
    // "version": 1
    cbor_text(&mut out, "version");
    cbor_uint(&mut out, 1);
    out
}

/// Decode the fixed-shape header: a 2-entry map with text keys `version` (must be 1)
/// and `roots` (an array of tag-42 CIDs), in either key order. Anything else is a
/// [`CarError::BadHeader`] — the decoder reads exactly the shape the encoder writes.
fn decode_header(bytes: &[u8]) -> Result<Vec<Cid>, CarError> {
    let mut p = 0usize;
    let first = *bytes
        .get(p)
        .ok_or_else(|| CarError::Truncated("empty header".into()))?;
    if first != 0xa2 {
        return Err(CarError::BadHeader(format!(
            "expected a 2-entry map (0xa2), got 0x{first:02x}"
        )));
    }
    p += 1;

    let mut version: Option<u64> = None;
    let mut roots: Option<Vec<Cid>> = None;
    for _ in 0..2 {
        let key = cbor_read_text(bytes, &mut p)?;
        match key.as_str() {
            "version" => {
                if version.replace(cbor_read_uint(bytes, &mut p)?).is_some() {
                    return Err(CarError::BadHeader("duplicate `version` key".into()));
                }
            }
            "roots" => {
                if roots.replace(cbor_read_roots(bytes, &mut p)?).is_some() {
                    return Err(CarError::BadHeader("duplicate `roots` key".into()));
                }
            }
            other => {
                return Err(CarError::BadHeader(format!("unexpected key `{other}`")));
            }
        }
    }
    if p != bytes.len() {
        return Err(CarError::BadHeader(format!(
            "{} trailing header bytes",
            bytes.len() - p
        )));
    }
    let version = version.ok_or_else(|| CarError::BadHeader("no `version` key".into()))?;
    if version != 1 {
        return Err(CarError::UnsupportedVersion(version));
    }
    let roots = roots.ok_or_else(|| CarError::BadHeader("no `roots` key".into()))?;
    if roots.is_empty() {
        return Err(CarError::BadHeader("empty `roots` array".into()));
    }
    Ok(roots)
}

// ── minimal CBOR primitives (exactly what the fixed header shape needs) ─────────

/// Write a CBOR unsigned int (major 0).
fn cbor_uint(out: &mut Vec<u8>, v: u64) {
    cbor_head(out, 0, v);
}

/// Write a CBOR text string (major 3).
fn cbor_text(out: &mut Vec<u8>, s: &str) {
    cbor_head(out, 3, s.len() as u64);
    out.extend_from_slice(s.as_bytes());
}

/// Write a CBOR byte string (major 2).
fn cbor_bytes(out: &mut Vec<u8>, b: &[u8]) {
    cbor_head(out, 2, b.len() as u64);
    out.extend_from_slice(b);
}

/// Write a CBOR head: 3-bit major type + the shortest-form argument (canonical).
fn cbor_head(out: &mut Vec<u8>, major: u8, v: u64) {
    let m = major << 5;
    if v < 24 {
        out.push(m | v as u8);
    } else if v <= u8::MAX as u64 {
        out.push(m | 24);
        out.push(v as u8);
    } else if v <= u16::MAX as u64 {
        out.push(m | 25);
        out.extend_from_slice(&(v as u16).to_be_bytes());
    } else if v <= u32::MAX as u64 {
        out.push(m | 26);
        out.extend_from_slice(&(v as u32).to_be_bytes());
    } else {
        out.push(m | 27);
        out.extend_from_slice(&v.to_be_bytes());
    }
}

/// Read a CBOR head, returning `(major, argument)`.
fn cbor_read_head(bytes: &[u8], p: &mut usize) -> Result<(u8, u64), CarError> {
    let b = *bytes
        .get(*p)
        .ok_or_else(|| CarError::Truncated("CBOR head".into()))?;
    *p += 1;
    let major = b >> 5;
    let info = b & 0x1f;
    let arg = match info {
        0..=23 => info as u64,
        24..=27 => {
            let n = 1usize << (info - 24);
            let end = p
                .checked_add(n)
                .filter(|&e| e <= bytes.len())
                .ok_or_else(|| CarError::Truncated("CBOR argument".into()))?;
            let mut v = 0u64;
            for &byte in &bytes[*p..end] {
                v = (v << 8) | byte as u64;
            }
            *p = end;
            v
        }
        other => {
            return Err(CarError::BadHeader(format!(
                "unsupported CBOR additional-info {other}"
            )));
        }
    };
    Ok((major, arg))
}

fn cbor_read_uint(bytes: &[u8], p: &mut usize) -> Result<u64, CarError> {
    let (major, arg) = cbor_read_head(bytes, p)?;
    if major != 0 {
        return Err(CarError::BadHeader(format!(
            "expected an unsigned int, got CBOR major {major}"
        )));
    }
    Ok(arg)
}

fn cbor_read_text(bytes: &[u8], p: &mut usize) -> Result<String, CarError> {
    let (major, len) = cbor_read_head(bytes, p)?;
    if major != 3 {
        return Err(CarError::BadHeader(format!(
            "expected a text key, got CBOR major {major}"
        )));
    }
    let end = p
        .checked_add(len as usize)
        .filter(|&e| e <= bytes.len())
        .ok_or_else(|| CarError::Truncated("CBOR text".into()))?;
    let s = std::str::from_utf8(&bytes[*p..end])
        .map_err(|_| CarError::BadHeader("non-utf8 text key".into()))?
        .to_string();
    *p = end;
    Ok(s)
}

/// Read the `roots` value: an array of tag-42 byte strings, each `0x00 ‖ CIDv1`.
fn cbor_read_roots(bytes: &[u8], p: &mut usize) -> Result<Vec<Cid>, CarError> {
    let (major, count) = cbor_read_head(bytes, p)?;
    if major != 4 {
        return Err(CarError::BadHeader(format!(
            "expected a roots array, got CBOR major {major}"
        )));
    }
    // Declared-count sanity: never pre-allocate off an adversarial header.
    if count > 1024 {
        return Err(CarError::BadHeader(format!("{count} declared roots")));
    }
    let mut roots = Vec::new();
    for _ in 0..count {
        let (tag_major, tag) = cbor_read_head(bytes, p)?;
        if tag_major != 6 || tag != 42 {
            return Err(CarError::BadHeader(format!(
                "expected CID tag 42, got major {tag_major} arg {tag}"
            )));
        }
        let (bs_major, len) = cbor_read_head(bytes, p)?;
        if bs_major != 2 {
            return Err(CarError::BadHeader(format!(
                "expected a CID byte string, got CBOR major {bs_major}"
            )));
        }
        let end = p
            .checked_add(len as usize)
            .filter(|&e| e <= bytes.len())
            .ok_or_else(|| CarError::Truncated("CID byte string".into()))?;
        let raw = &bytes[*p..end];
        *p = end;
        let cid_bytes = raw
            .strip_prefix(&[0x00])
            .ok_or_else(|| CarError::BadHeader("CID missing identity prefix 0x00".into()))?;
        let cid = Cid::from_bytes(cid_bytes).map_err(|e| CarError::BadCid(e.to_string()))?;
        roots.push(cid);
    }
    Ok(roots)
}

/// Parse a binary CIDv1 as a *prefix* of `frame` (advancing `p` past exactly the CID
/// bytes) — a CAR frame is `CID ‖ block` with no inner delimiter, so the CID's own
/// self-delimiting structure is the split. Only CIDv1 appears in dregg CARs (a legacy
/// CIDv0 frame — a bare sha2 multihash — is refused, and could not be blake3
/// re-witnessed anyway).
fn parse_cid_prefix(frame: &[u8], p: &mut usize) -> Result<Cid, CarError> {
    let version =
        take_varint(frame, p).map_err(|e| CarError::BadCid(format!("version varint: {e}")))?;
    if version != 1 {
        return Err(CarError::BadCid(format!(
            "unsupported CID version {version} in a CAR frame"
        )));
    }
    let codec =
        take_varint(frame, p).map_err(|e| CarError::BadCid(format!("codec varint: {e}")))?;
    let hash_code =
        take_varint(frame, p).map_err(|e| CarError::BadCid(format!("multihash varint: {e}")))?;
    let len = take_varint(frame, p)
        .map_err(|e| CarError::BadCid(format!("digest length varint: {e}")))?
        as usize;
    let end = p
        .checked_add(len)
        .filter(|&e| e <= frame.len())
        .ok_or_else(|| CarError::Truncated("CID digest overruns the frame".into()))?;
    let digest = frame[*p..end].to_vec();
    *p = end;
    Ok(Cid {
        version,
        codec,
        hash_code,
        digest,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::client::MockIpfs;
    use crate::unixfs::{build_dir_dag_with, fetch_dir};

    /// A small but structurally rich block set: a directory holding a multi-block
    /// file, so the CAR carries raw leaves, dag-pb file interiors, and a dag-pb dir.
    fn sample_dag() -> (Cid, Vec<Block>) {
        let big: Vec<u8> = (0..300u32).map(|i| (i * 11 % 251) as u8).collect();
        let entries: [(&str, &[u8]); 2] = [("readme.txt", b"hello car"), ("data.bin", &big)];
        let dag = build_dir_dag_with(&entries, 64, 3).unwrap();
        (dag.root, dag.blocks)
    }

    #[test]
    fn export_import_round_trips_byte_identical_blocks() {
        let (root, blocks) = sample_dag();
        let car = export_car(&root, &blocks).unwrap();
        let contents = import_car(&car).unwrap();
        assert_eq!(contents.roots, vec![root.clone()]);
        assert_eq!(contents.blocks.len(), blocks.len());
        for (a, b) in contents.blocks.iter().zip(blocks.iter()) {
            assert_eq!(a.cid, b.cid);
            assert_eq!(a.bytes, b.bytes, "byte-identical block round-trip");
        }
        // And a re-export of the import is byte-identical to the original CAR.
        assert_eq!(export_car(&root, &contents.blocks).unwrap(), car);
    }

    #[test]
    fn import_into_a_client_serves_the_verified_dag() {
        let (root, blocks) = sample_dag();
        let car = export_car(&root, &blocks).unwrap();
        let node = MockIpfs::new();
        let roots = import_car_into(&node, &car).unwrap();
        assert_eq!(roots, vec![root.clone()]);
        assert!(node.is_pinned(&root));
        let entries = fetch_dir(&node, &root).unwrap();
        assert_eq!(entries[1].0, "readme.txt");
        assert_eq!(entries[1].1, b"hello car");
    }

    #[test]
    fn every_single_flipped_byte_is_a_named_refusal() {
        // Exhaustive single-byte tamper: flip each byte of the CAR (header, frame
        // lengths, CID bytes, block bytes) and require import refuses EVERY variant.
        // Framing, header shape, per-block re-witness, root presence, and closure
        // together leave no byte that can change without a named error.
        let (root, blocks) = sample_dag();
        let car = export_car(&root, &blocks).unwrap();
        for i in 0..car.len() {
            let mut evil = car.clone();
            evil[i] ^= 0x01;
            let res = import_car(&evil);
            assert!(
                res.is_err(),
                "flipping byte {i} (0x{:02x}) was ACCEPTED: {:?}",
                car[i],
                res.map(|c| c.blocks.len())
            );
        }
    }

    #[test]
    fn a_truncated_car_is_refused() {
        let (root, blocks) = sample_dag();
        let car = export_car(&root, &blocks).unwrap();
        for keep in [1usize, 10, car.len() / 2, car.len() - 1] {
            assert!(import_car(&car[..keep]).is_err(), "kept {keep} bytes");
        }
        // Trailing garbage after the last frame is refused too (decays into a
        // truncated/garbage extra frame — named, not ignored).
        let mut padded = car.clone();
        padded.push(0x00);
        assert!(import_car(&padded).is_err());
    }

    #[test]
    fn a_header_root_missing_from_the_blocks_is_refused() {
        let (_, blocks) = sample_dag();
        // Export under a root that is NOT in the block set: refused at export…
        let foreign = Cid::raw_blake3(b"not in this car");
        assert_eq!(
            export_car(&foreign, &blocks).unwrap_err(),
            CarError::RootNotPresent(foreign.to_string_cid())
        );
        // …and a hand-spliced CAR whose header names that root is refused at import.
        // (Splice: encode header for the foreign root + honest frames from a real CAR.)
        let (root, _) = sample_dag();
        let honest = export_car(&root, &blocks).unwrap();
        let mut p = 0usize;
        let hlen = take_varint(&honest, &mut p).unwrap() as usize;
        let frames = &honest[p + hlen..];
        let mut spliced = Vec::new();
        let new_header = encode_header(&foreign);
        put_varint(&mut spliced, new_header.len() as u64);
        spliced.extend_from_slice(&new_header);
        spliced.extend_from_slice(frames);
        assert_eq!(
            import_car(&spliced).unwrap_err(),
            CarError::RootNotPresent(foreign.to_string_cid())
        );
    }

    #[test]
    fn a_dropped_block_breaks_the_closure() {
        let (root, blocks) = sample_dag();
        // Drop one LEAF block (not the root): root is present, every remaining block
        // self-verifies — only the closure check catches the hole.
        let dropped = blocks[0].cid.clone();
        let partial: Vec<Block> = blocks[1..].to_vec();
        match export_car(&root, &partial).unwrap_err() {
            CarError::IncompleteDag { missing, .. } => {
                assert_eq!(missing, dropped.to_string_cid());
            }
            other => panic!("expected IncompleteDag, got {other:?}"),
        }
    }

    #[test]
    fn a_wrong_version_header_is_refused() {
        let (root, blocks) = sample_dag();
        let car = export_car(&root, &blocks).unwrap();
        // The canonical header ends "version" ‖ 0x01; flip the version to 2.
        let mut p = 0usize;
        let hlen = take_varint(&car, &mut p).unwrap() as usize;
        let mut evil = car.clone();
        // Last byte of the header is the version uint (canonical key order).
        evil[p + hlen - 1] = 0x02;
        assert_eq!(
            import_car(&evil).unwrap_err(),
            CarError::UnsupportedVersion(2)
        );
    }

    #[test]
    fn header_round_trips_and_reads_either_key_order() {
        let root = Cid::raw_blake3(b"a root");
        let header = encode_header(&root);
        assert_eq!(decode_header(&header).unwrap(), vec![root.clone()]);
        // Hand-build the version-first key order (go-car historically wrote struct
        // order); the decoder accepts it.
        let mut alt = vec![0xa2];
        cbor_text(&mut alt, "version");
        cbor_uint(&mut alt, 1);
        cbor_text(&mut alt, "roots");
        alt.push(0x81);
        alt.extend_from_slice(&[0xd8, 0x2a]);
        let mut payload = vec![0x00];
        payload.extend_from_slice(&root.to_bytes());
        cbor_bytes(&mut alt, &payload);
        assert_eq!(decode_header(&alt).unwrap(), vec![root]);
    }

    #[test]
    fn import_into_refuses_before_ingesting_anything() {
        let (root, blocks) = sample_dag();
        let car = export_car(&root, &blocks).unwrap();
        // Corrupt the LAST block's bytes: verification must fail with NOTHING stored.
        let mut evil = car.clone();
        let last = evil.len() - 1;
        evil[last] ^= 0xff;
        let node = MockIpfs::new();
        assert!(import_car_into(&node, &evil).is_err());
        assert_eq!(node.block_count(), 0, "a refused CAR ingests nothing");
    }
}
