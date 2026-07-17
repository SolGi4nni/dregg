//! `unixfs` — **chunked content**: a real UnixFS/dag-pb file DAG builder, a
//! **directory** builder over named file entries, and the verified DAG-walk reads.
//!
//! The single-block bridge ([`crate::pin_blob`] / [`crate::fetch_verified`]) is exact
//! but only reaches content that fits in one IPFS block. Larger content is what IPFS
//! *chunks*: raw leaf blocks under a `dag-pb` UnixFS-file root whose CID is a hash over
//! the **link structure**, not the file bytes — so a flat re-hash cannot check it, and
//! the old bridge simply refused it ([`crate::client::IpfsError::NotVerifiableByFlatHash`]).
//! This module closes that hole with two halves that both stay verify-don't-trust:
//!
//! - [`build_file_dag`] / [`pin_file`] — split content into ≤[`DEFAULT_CHUNK_SIZE`]
//!   raw leaves and fold them into a **balanced** UnixFS-file DAG (each parent a
//!   `dag-pb` node linking ≤[`DEFAULT_MAX_LINKS`] children). Every block is
//!   blake3-addressed, so the leaves reuse the exact single-block CID
//!   ([`crate::cid::Cid::raw_blake3`]) and the root is a `dag-pb` blake3 CID.
//! - [`fetch_cat`] — the **verified DAG walk**: fetch the root block, re-hash it
//!   against the root CID, parse its links, and recurse — re-witnessing *every* block
//!   (leaf and interior) against its own CID before using it, then concatenating the
//!   leaves in order. A lying node that flips any byte moves that block's hash and is
//!   refused. The reassembled length is checked against the UnixFS `filesize`.
//! - [`build_dir_dag`] / [`pin_dir`] / [`fetch_dir`] — **directories**: one `dag-pb`
//!   node (`UnixFS Type=Directory`) whose links carry entry **names** over per-entry
//!   file DAGs, and the verified inverse that re-witnesses the directory node + every
//!   file block and returns the named entries. Single-level (a flat dir of files —
//!   no nesting, no HAMT sharding); a nested directory is a named refusal, and a
//!   directory node that would exceed one block ([`DEFAULT_CHUNK_SIZE`]) is refused
//!   at build time rather than silently sharded.
//!
//! Because [`fetch_cat`] follows links generically (a link to a `dag-pb` child is
//! walked recursively), it reads a multi-level DAG produced by a stock `ipfs add
//! --hash=blake3` too, not only the single-level shape this builder writes. **Honest
//! boundary:** the block-level content-addressing is exact and enforced; *byte-exact
//! parity* with go-ipfs's default chunker boundaries + balanced-layout Tsizes (so this
//! builder's root CID equals a live `ipfs add`'s) is reviewed-go — this builder emits a
//! valid, self-consistent, fully verifiable blake3 UnixFS DAG that [`fetch_cat`]
//! round-trips.

use crate::cid::{CODEC_DAG_PB, CODEC_RAW, Cid};
use crate::client::{IpfsClient, IpfsError};

/// The default leaf chunk size — 256 KiB, the go-ipfs default fixed-size chunker.
pub const DEFAULT_CHUNK_SIZE: usize = 256 * 1024;

/// The default maximum links per `dag-pb` node — the go-ipfs balanced-DAG default
/// (`ipfs.DefaultLinksPerBlock`).
pub const DEFAULT_MAX_LINKS: usize = 174;

/// One content-addressed block of a built DAG: its CID and its exact bytes. Pin these
/// (leaves first) to make the DAG retrievable; the [`root`](FileDag::root) is the CID
/// to commit + fetch.
#[derive(Clone, Debug)]
pub struct Block {
    /// The block's CID (raw leaf, or `dag-pb` interior/root node).
    pub cid: Cid,
    /// The block's exact bytes (a raw leaf's content, or a serialized `PBNode`).
    pub bytes: Vec<u8>,
}

/// A built UnixFS file DAG: the root CID to commit, plus every block to pin.
#[derive(Clone, Debug)]
pub struct FileDag {
    /// The DAG root CID (a raw-leaf CID for content ≤ one chunk, else a `dag-pb` root).
    pub root: Cid,
    /// All blocks (leaves + interior nodes + root), safe to pin in order (children
    /// before parents).
    pub blocks: Vec<Block>,
}

/// Build a UnixFS file DAG over `content` with the default chunk size + fan-out.
pub fn build_file_dag(content: &[u8]) -> FileDag {
    build_file_dag_with(content, DEFAULT_CHUNK_SIZE, DEFAULT_MAX_LINKS)
}

/// Build a UnixFS file DAG with explicit `chunk_size` + `max_links`.
///
/// Content that fits in one chunk becomes a single **raw** leaf (root == that leaf CID
/// == `raw(blake3(content))`, identical to the single-block bridge). Larger content is
/// chunked into raw leaves and folded into a balanced `dag-pb` tree.
pub fn build_file_dag_with(content: &[u8], chunk_size: usize, max_links: usize) -> FileDag {
    assert!(chunk_size > 0 && max_links >= 2, "degenerate DAG params");

    // A single chunk is a bare raw leaf — no dag-pb wrapper (matches raw-leaves add).
    if content.len() <= chunk_size {
        let cid = Cid::raw_blake3(content);
        return FileDag {
            root: cid.clone(),
            blocks: vec![Block {
                cid,
                bytes: content.to_vec(),
            }],
        };
    }

    let mut blocks: Vec<Block> = Vec::new();

    // Level 0: the raw leaves.
    let mut level: Vec<Node> = content
        .chunks(chunk_size)
        .map(|chunk| {
            let cid = Cid::raw_blake3(chunk);
            blocks.push(Block {
                cid: cid.clone(),
                bytes: chunk.to_vec(),
            });
            Node {
                cid,
                filesize: chunk.len() as u64,
                dag_size: chunk.len() as u64,
            }
        })
        .collect();

    // Fold up into balanced dag-pb parents until a single root remains.
    while level.len() > 1 {
        let mut next: Vec<Node> = Vec::with_capacity(level.len().div_ceil(max_links));
        for group in level.chunks(max_links) {
            let (node, bytes) = build_parent(group);
            blocks.push(Block {
                cid: node.cid.clone(),
                bytes,
            });
            next.push(node);
        }
        level = next;
    }

    FileDag {
        root: level.into_iter().next().expect("nonempty").cid,
        blocks,
    }
}

/// Build a UnixFS file DAG over `content` and pin every block to `client`, returning
/// the root CID (to commit in the cell). Children are pinned before parents so the DAG
/// is complete before the root becomes referenceable.
pub fn pin_file<C: IpfsClient>(client: &C, content: &[u8]) -> Result<Cid, IpfsError> {
    let dag = build_file_dag(content);
    for block in &dag.blocks {
        client.put_block(&block.cid, &block.bytes)?;
    }
    Ok(dag.root)
}

/// **The verified DAG-walk read.** Fetch and reassemble the content addressed by
/// `root` from `client`, re-witnessing *every* block against its own CID — no trust in
/// the serving node. Handles a bare raw blob, a single-level DAG, or a multi-level DAG.
///
/// Refuses: a block whose bytes do not hash to its CID
/// ([`IpfsError::CidMismatch`]); a non-blake3 / non-UnixFS CID
/// ([`IpfsError::NotVerifiableByFlatHash`]); a DAG deeper than 64 levels
/// ([`IpfsError::DagTooDeep`], guarding against a cyclic/adversarial DAG); a
/// reassembled length disagreeing with the UnixFS `filesize`.
pub fn fetch_cat<C: IpfsClient>(client: &C, root: &Cid) -> Result<Vec<u8>, IpfsError> {
    let mut out = Vec::new();
    walk(client, root, 0, &mut out)?;
    Ok(out)
}

const MAX_DEPTH: usize = 64;

fn walk<C: IpfsClient>(
    client: &C,
    cid: &Cid,
    depth: usize,
    out: &mut Vec<u8>,
) -> Result<(), IpfsError> {
    if depth > MAX_DEPTH {
        return Err(IpfsError::DagTooDeep {
            max_depth: MAX_DEPTH,
        });
    }
    let block = client.get(cid)?;
    // Every block in a blake3 DAG is re-witnessed against its own CID: the tamper
    // tooth that makes the whole walk trustless.
    if !cid.is_blake3() {
        return Err(IpfsError::NotVerifiableByFlatHash(cid.to_string_cid()));
    }
    let recomputed = *blake3::hash(&block).as_bytes();
    if recomputed.as_slice() != cid.digest.as_slice() {
        return Err(IpfsError::CidMismatch {
            requested: cid.to_string_cid(),
            got: Cid::from_blake3_digest(cid.codec, recomputed).to_string_cid(),
        });
    }

    match cid.codec {
        CODEC_RAW => {
            // A raw leaf: its bytes are file content.
            out.extend_from_slice(&block);
            Ok(())
        }
        CODEC_DAG_PB => {
            let node = parse_pb_node(&block)?;
            // A directory node cannot be `cat`ed into file bytes — that is
            // `fetch_dir`'s job. Refuse rather than concatenating entries silently.
            if node.data_type == Some(UNIXFS_TYPE_DIRECTORY) {
                return Err(IpfsError::InvalidDirectory(format!(
                    "{} is a UnixFS directory, not a file (use fetch_dir)",
                    cid.to_string_cid()
                )));
            }
            let start = out.len();
            for link in &node.links {
                let child = Cid::from_bytes(&link.hash)
                    .map_err(|e| IpfsError::BadDagNode(format!("bad link CID: {e}")))?;
                walk(client, &child, depth + 1, out)?;
            }
            // If the node carried a UnixFS filesize, the reassembled span must match —
            // a truncated/padded DAG is refused even if every block self-verifies.
            if let Some(filesize) = node.filesize {
                let got = (out.len() - start) as u64;
                if got != filesize {
                    return Err(IpfsError::BadDagNode(format!(
                        "unixfs filesize {filesize} != reassembled {got}"
                    )));
                }
            }
            Ok(())
        }
        other => Err(IpfsError::NotVerifiableByFlatHash(format!(
            "codec 0x{other:x} is not a UnixFS file DAG"
        ))),
    }
}

// -- directories: a dag-pb dir node over named file entries --------------------

/// A built UnixFS **directory** DAG: the directory root CID, every block to pin
/// (entry file blocks + the directory node), and the per-entry file roots.
#[derive(Clone, Debug)]
pub struct DirDag {
    /// The directory root CID (always a `dag-pb` node, `UnixFS Type=Directory`).
    pub root: Cid,
    /// All blocks (entry file DAGs' blocks, then the directory node last), safe to pin
    /// in order (children before the directory node).
    pub blocks: Vec<Block>,
    /// The `(name, file-root CID)` of each entry, in the directory's canonical
    /// (name-sorted) order.
    pub entries: Vec<(String, Cid)>,
}

/// Build a UnixFS **directory** over named file `entries` with the default chunk
/// size + fan-out. See [`build_dir_dag_with`].
pub fn build_dir_dag(entries: &[(&str, &[u8])]) -> Result<DirDag, IpfsError> {
    build_dir_dag_with(entries, DEFAULT_CHUNK_SIZE, DEFAULT_MAX_LINKS)
}

/// Build a UnixFS directory: each entry's content becomes a file DAG
/// ([`build_file_dag_with`]) and one `dag-pb` node (`UnixFS Type=Directory`) links
/// them by **name**. Links are canonically **sorted by name** (the go-ipfs directory
/// order), so the same entry set always roots at the same CID regardless of the
/// caller's ordering.
///
/// Refusals ([`IpfsError::InvalidDirectory`]): an empty entry name, a name containing
/// `/` or NUL (this is a single-level directory — no path smuggling), a duplicate
/// name; and a directory node that would exceed one block ([`DEFAULT_CHUNK_SIZE`]) —
/// this builder does not HAMT-shard, it refuses honestly.
pub fn build_dir_dag_with(
    entries: &[(&str, &[u8])],
    chunk_size: usize,
    max_links: usize,
) -> Result<DirDag, IpfsError> {
    // Validate names before hashing anything.
    let mut seen = std::collections::HashSet::new();
    for (name, _) in entries {
        if name.is_empty() {
            return Err(IpfsError::InvalidDirectory("empty entry name".into()));
        }
        if name.contains('/') || name.contains('\0') {
            return Err(IpfsError::InvalidDirectory(format!(
                "entry name `{name}` contains a path separator or NUL"
            )));
        }
        if !seen.insert(*name) {
            return Err(IpfsError::InvalidDirectory(format!(
                "duplicate entry name `{name}`"
            )));
        }
    }

    // Canonical order: sort entries by name so the dir CID is order-independent.
    let mut sorted: Vec<&(&str, &[u8])> = entries.iter().collect();
    sorted.sort_by_key(|(name, _)| *name);

    let mut blocks: Vec<Block> = Vec::new();
    let mut dir_entries: Vec<(String, Cid)> = Vec::new();
    let mut node = Vec::new();
    for (name, content) in sorted {
        let file = build_file_dag_with(content, chunk_size, max_links);
        // Tsize = the cumulative serialized size of the entry's whole file DAG.
        let tsize: u64 = file.blocks.iter().map(|b| b.bytes.len() as u64).sum();
        let link = encode_pb_link_named(&file.root.to_bytes(), name, tsize);
        pb_field_bytes(&mut node, 2, &link);
        dir_entries.push((name.to_string(), file.root.clone()));
        blocks.extend(file.blocks);
    }
    // Data (field 1): UnixFS Type=Directory, nothing else.
    let mut unixfs_data = Vec::new();
    pb_field_varint(&mut unixfs_data, 1, UNIXFS_TYPE_DIRECTORY);
    pb_field_bytes(&mut node, 1, &unixfs_data);

    // A directory node must fit in one block — this builder does not HAMT-shard.
    if node.len() > DEFAULT_CHUNK_SIZE {
        return Err(IpfsError::InvalidDirectory(format!(
            "directory node is {} bytes, over the {DEFAULT_CHUNK_SIZE}-byte single-block \
             limit (HAMT sharding is out of scope)",
            node.len()
        )));
    }

    let root = Cid::from_blake3_digest(CODEC_DAG_PB, *blake3::hash(&node).as_bytes());
    blocks.push(Block {
        cid: root.clone(),
        bytes: node,
    });
    Ok(DirDag {
        root,
        blocks,
        entries: dir_entries,
    })
}

/// Build a UnixFS directory over named `entries` and pin every block to `client`,
/// returning the directory root CID. Children are pinned before the directory node.
pub fn pin_dir<C: IpfsClient>(client: &C, entries: &[(&str, &[u8])]) -> Result<Cid, IpfsError> {
    let dag = build_dir_dag(entries)?;
    for block in &dag.blocks {
        client.put_block(&block.cid, &block.bytes)?;
    }
    Ok(dag.root)
}

/// **The verified directory read.** Fetch the directory node addressed by `root`,
/// re-witness it against its CID, and read every named entry through the verified
/// file walk ([`fetch_cat`]) — every block (directory node, interior nodes, leaves)
/// is re-hashed against its own CID before use. Returns the `(name, content)` pairs
/// in the directory's stored (canonical) order.
///
/// Refuses: a tampered block ([`IpfsError::CidMismatch`]); a non-directory node read
/// as a directory, an unnamed / empty-named / duplicate-named link, or a nested
/// directory entry ([`IpfsError::InvalidDirectory`] — single-level scope, matching
/// [`build_dir_dag`]); plus everything the file walk refuses.
pub fn fetch_dir<C: IpfsClient>(
    client: &C,
    root: &Cid,
) -> Result<Vec<(String, Vec<u8>)>, IpfsError> {
    if !root.is_blake3() {
        return Err(IpfsError::NotVerifiableByFlatHash(root.to_string_cid()));
    }
    if !root.is_dag_pb() {
        return Err(IpfsError::InvalidDirectory(format!(
            "{} is not a dag-pb node (a directory root always is)",
            root.to_string_cid()
        )));
    }
    let block = client.get(root)?;
    // Re-witness the directory node itself before trusting any of its links.
    let recomputed = *blake3::hash(&block).as_bytes();
    if recomputed.as_slice() != root.digest.as_slice() {
        return Err(IpfsError::CidMismatch {
            requested: root.to_string_cid(),
            got: Cid::from_blake3_digest(root.codec, recomputed).to_string_cid(),
        });
    }
    let node = parse_pb_node(&block)?;
    if node.data_type != Some(UNIXFS_TYPE_DIRECTORY) {
        return Err(IpfsError::InvalidDirectory(format!(
            "{} is not a UnixFS directory node (use fetch_cat for a file)",
            root.to_string_cid()
        )));
    }
    let mut out = Vec::with_capacity(node.links.len());
    let mut seen = std::collections::HashSet::new();
    for link in &node.links {
        let name = link.name.clone().unwrap_or_default();
        if name.is_empty() {
            return Err(IpfsError::InvalidDirectory(
                "directory link has no name".into(),
            ));
        }
        if !seen.insert(name.clone()) {
            return Err(IpfsError::InvalidDirectory(format!(
                "duplicate entry name `{name}`"
            )));
        }
        let child = Cid::from_bytes(&link.hash)
            .map_err(|e| IpfsError::BadDagNode(format!("bad link CID: {e}")))?;
        // The verified file walk re-witnesses every block of the entry; a nested
        // directory entry is refused inside it (single-level scope).
        let content = fetch_cat(client, &child)?;
        out.push((name, content));
    }
    Ok(out)
}

// -- the balanced-tree parent builder -----------------------------------------

/// A DAG node summary used while folding levels: its CID, the UnixFS filesize of the
/// subtree it roots, and its cumulative serialized DAG size (for a link's `Tsize`).
struct Node {
    cid: Cid,
    filesize: u64,
    dag_size: u64,
}

/// Build one `dag-pb` UnixFS-file parent over `children`; returns the node summary and
/// the serialized block bytes.
fn build_parent(children: &[Node]) -> (Node, Vec<u8>) {
    let filesize: u64 = children.iter().map(|c| c.filesize).sum();
    let blocksizes: Vec<u64> = children.iter().map(|c| c.filesize).collect();
    let unixfs_data = encode_unixfs_file(filesize, &blocksizes);

    // Canonical dag-pb: Links (field 2) precede Data (field 1).
    let mut node = Vec::new();
    for c in children {
        // Tsize = the cumulative serialized size of the linked subtree.
        let link = encode_pb_link(&c.cid.to_bytes(), c.dag_size);
        pb_field_bytes(&mut node, 2, &link);
    }
    pb_field_bytes(&mut node, 1, &unixfs_data);

    let cid = Cid::from_blake3_digest(CODEC_DAG_PB, *blake3::hash(&node).as_bytes());
    let dag_size = node.len() as u64 + children.iter().map(|c| c.dag_size).sum::<u64>();
    (
        Node {
            cid,
            filesize,
            dag_size,
        },
        node,
    )
}

// -- minimal protobuf (dag-pb + UnixFS) ---------------------------------------

/// UnixFS `DataType::File` (= 2).
const UNIXFS_TYPE_FILE: u64 = 2;

/// UnixFS `DataType::Directory` (= 1).
const UNIXFS_TYPE_DIRECTORY: u64 = 1;

/// Encode the UnixFS `Data` message for a file node: `Type=File`, `filesize`, and the
/// per-child `blocksizes`. (No inline `Data` — the bytes live in the raw leaves.)
fn encode_unixfs_file(filesize: u64, blocksizes: &[u64]) -> Vec<u8> {
    let mut out = Vec::new();
    pb_field_varint(&mut out, 1, UNIXFS_TYPE_FILE); // Type
    pb_field_varint(&mut out, 3, filesize); // filesize
    for &bs in blocksizes {
        pb_field_varint(&mut out, 4, bs); // repeated blocksizes
    }
    out
}

/// Encode a dag-pb `PBLink`: `Hash` (field 1, the child CID bytes) + `Tsize` (field 3).
/// `Name` (field 2) is omitted (empty) for a file DAG.
fn encode_pb_link(hash: &[u8], tsize: u64) -> Vec<u8> {
    let mut out = Vec::new();
    pb_field_bytes(&mut out, 1, hash); // Hash
    pb_field_varint(&mut out, 3, tsize); // Tsize
    out
}

/// Encode a **named** dag-pb `PBLink` (a directory entry): `Hash` (field 1) + `Name`
/// (field 2) + `Tsize` (field 3).
fn encode_pb_link_named(hash: &[u8], name: &str, tsize: u64) -> Vec<u8> {
    let mut out = Vec::new();
    pb_field_bytes(&mut out, 1, hash); // Hash
    pb_field_bytes(&mut out, 2, name.as_bytes()); // Name
    pb_field_varint(&mut out, 3, tsize); // Tsize
    out
}

/// A parsed dag-pb `PBLink`: the child CID bytes + the entry name, if any (a file
/// DAG's links are unnamed; a directory's carry the entry name).
struct PbLink {
    hash: Vec<u8>,
    name: Option<String>,
}

/// A parsed dag-pb node: the ordered child links, the UnixFS `Type` (file /
/// directory), and the UnixFS `filesize` if the `Data` field carried one.
struct PbNode {
    links: Vec<PbLink>,
    data_type: Option<u64>,
    filesize: Option<u64>,
}

/// Parse a dag-pb `PBNode`: collect every `Links` (field 2) entry, and read the
/// UnixFS `Type` + `filesize` from the `Data` (field 1) message.
fn parse_pb_node(bytes: &[u8]) -> Result<PbNode, IpfsError> {
    let mut links = Vec::new();
    let mut data_type = None;
    let mut filesize = None;
    let mut p = 0usize;
    while p < bytes.len() {
        let (field, wire, val) = pb_read_field(bytes, &mut p)?;
        match (field, wire) {
            // Links (field 2): a length-delimited PBLink submessage.
            (2, 2) => {
                let link = as_bytes(val)?;
                links.push(parse_pb_link(link)?);
            }
            // Data (field 1): the UnixFS Data message.
            (1, 2) => {
                let (ty, fs) = parse_unixfs_data(as_bytes(val)?)?;
                data_type = ty;
                filesize = fs;
            }
            _ => {}
        }
    }
    Ok(PbNode {
        links,
        data_type,
        filesize,
    })
}

/// Parse a `PBLink`: `Hash` (field 1, required) + `Name` (field 2, optional).
fn parse_pb_link(bytes: &[u8]) -> Result<PbLink, IpfsError> {
    let mut p = 0usize;
    let mut hash = None;
    let mut name = None;
    while p < bytes.len() {
        let (field, wire, val) = pb_read_field(bytes, &mut p)?;
        match (field, wire) {
            (1, 2) => hash = Some(as_bytes(val)?.to_vec()),
            (2, 2) => {
                let raw = as_bytes(val)?;
                name = Some(
                    std::str::from_utf8(raw)
                        .map_err(|_| IpfsError::BadDagNode("non-utf8 link name".into()))?
                        .to_string(),
                );
            }
            _ => {}
        }
    }
    Ok(PbLink {
        hash: hash.ok_or_else(|| IpfsError::BadDagNode("PBLink had no Hash".into()))?,
        name,
    })
}

/// Read the UnixFS `Type` (field 1) and `filesize` (field 3) from a `Data` message.
fn parse_unixfs_data(bytes: &[u8]) -> Result<(Option<u64>, Option<u64>), IpfsError> {
    let mut p = 0usize;
    let mut data_type = None;
    let mut filesize = None;
    while p < bytes.len() {
        let (field, wire, val) = pb_read_field(bytes, &mut p)?;
        if let PbVal::Varint(v) = val {
            match (field, wire) {
                (1, 0) => data_type = Some(v),
                (3, 0) => filesize = Some(v),
                _ => {}
            }
        }
    }
    Ok((data_type, filesize))
}

/// The dag-pb child link CIDs of a serialized node — used by [`crate::car`] to check
/// a CAR's block closure (every link a dag-pb block makes must resolve inside the CAR).
pub(crate) fn dag_pb_links(bytes: &[u8]) -> Result<Vec<Cid>, IpfsError> {
    parse_pb_node(bytes)?
        .links
        .iter()
        .map(|l| {
            Cid::from_bytes(&l.hash)
                .map_err(|e| IpfsError::BadDagNode(format!("bad link CID: {e}")))
        })
        .collect()
}

// -- protobuf wire primitives -------------------------------------------------

enum PbVal<'a> {
    Varint(u64),
    Bytes(&'a [u8]),
}

fn as_bytes(v: PbVal<'_>) -> Result<&[u8], IpfsError> {
    match v {
        PbVal::Bytes(b) => Ok(b),
        PbVal::Varint(_) => Err(IpfsError::BadDagNode("expected length-delimited".into())),
    }
}

/// Read one protobuf field `(field_number, wire_type, value)`. Supports wire types 0
/// (varint) and 2 (length-delimited); others are a malformed-node error.
fn pb_read_field<'a>(bytes: &'a [u8], p: &mut usize) -> Result<(u64, u64, PbVal<'a>), IpfsError> {
    let key = pb_read_varint(bytes, p)?;
    let field = key >> 3;
    let wire = key & 0x7;
    match wire {
        0 => {
            let v = pb_read_varint(bytes, p)?;
            Ok((field, wire, PbVal::Varint(v)))
        }
        2 => {
            let len = pb_read_varint(bytes, p)? as usize;
            let end = p
                .checked_add(len)
                .filter(|&e| e <= bytes.len())
                .ok_or_else(|| IpfsError::BadDagNode("length-delimited overrun".into()))?;
            let slice = &bytes[*p..end];
            *p = end;
            Ok((field, wire, PbVal::Bytes(slice)))
        }
        other => Err(IpfsError::BadDagNode(format!(
            "unsupported wire type {other}"
        ))),
    }
}

fn pb_read_varint(bytes: &[u8], p: &mut usize) -> Result<u64, IpfsError> {
    let mut result: u64 = 0;
    let mut shift = 0u32;
    loop {
        let b = *bytes
            .get(*p)
            .ok_or_else(|| IpfsError::BadDagNode("truncated varint".into()))?;
        *p += 1;
        if shift >= 64 {
            return Err(IpfsError::BadDagNode("varint overflow".into()));
        }
        result |= ((b & 0x7f) as u64) << shift;
        if b & 0x80 == 0 {
            return Ok(result);
        }
        shift += 7;
    }
}

fn pb_write_varint(out: &mut Vec<u8>, mut v: u64) {
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

/// Write a varint field: `key = (field << 3) | 0` then the value.
fn pb_field_varint(out: &mut Vec<u8>, field: u64, v: u64) {
    pb_write_varint(out, field << 3);
    pb_write_varint(out, v);
}

/// Write a length-delimited field: `key = (field << 3) | 2`, length, then bytes.
fn pb_field_bytes(out: &mut Vec<u8>, field: u64, data: &[u8]) {
    pb_write_varint(out, (field << 3) | 2);
    pb_write_varint(out, data.len() as u64);
    out.extend_from_slice(data);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::client::MockIpfs;

    #[test]
    fn single_chunk_is_a_bare_raw_leaf() {
        // Content within one chunk builds no dag-pb wrapper: the root IS the raw-blake3
        // single-block CID, identical to the bridge's whole-blob pin.
        let content = b"small enough to be one block";
        let dag = build_file_dag_with(content, 256, DEFAULT_MAX_LINKS);
        assert_eq!(dag.root, Cid::raw_blake3(content));
        assert_eq!(dag.blocks.len(), 1);
        assert!(dag.root.is_raw_blake3());
    }

    #[test]
    fn chunked_file_round_trips_through_the_verified_walk() {
        let node = MockIpfs::new();
        // ~5 chunks of 64 bytes each: forces a dag-pb root over raw leaves.
        let content: Vec<u8> = (0..300u32).map(|i| (i * 7 % 251) as u8).collect();
        let root = {
            let dag = build_file_dag_with(&content, 64, DEFAULT_MAX_LINKS);
            assert!(
                dag.root.is_dag_pb(),
                "multi-chunk content roots at a dag-pb node"
            );
            for b in &dag.blocks {
                node.put_block(&b.cid, &b.bytes).unwrap();
            }
            dag.root
        };
        // The verified walk reassembles the exact bytes.
        assert_eq!(fetch_cat(&node, &root).unwrap(), content);
    }

    #[test]
    fn multi_level_dag_round_trips() {
        let node = MockIpfs::new();
        // 20 leaves with max_links=3 → a 3-level balanced tree.
        let content: Vec<u8> = (0..20u32 * 8).map(|i| i as u8).collect();
        let dag = build_file_dag_with(&content, 8, 3);
        assert!(dag.root.is_dag_pb());
        assert!(
            dag.blocks.len() > 21,
            "interior nodes exist: {}",
            dag.blocks.len()
        );
        for b in &dag.blocks {
            node.put_block(&b.cid, &b.bytes).unwrap();
        }
        assert_eq!(fetch_cat(&node, &dag.root).unwrap(), content);
    }

    #[test]
    fn pin_file_then_fetch_cat() {
        let node = MockIpfs::new();
        let content: Vec<u8> = (0..1000u32).map(|i| (i % 256) as u8).collect();
        let root = pin_file(&node, &content).unwrap();
        assert_eq!(fetch_cat(&node, &root).unwrap(), content);
    }

    #[test]
    fn a_tampered_leaf_is_refused_by_the_walk() {
        let node = MockIpfs::new();
        let content: Vec<u8> = (0..300u32).map(|i| i as u8).collect();
        let dag = build_file_dag_with(&content, 64, DEFAULT_MAX_LINKS);
        for b in &dag.blocks {
            node.put_block(&b.cid, &b.bytes).unwrap();
        }
        // Tamper a raw leaf (the first block is a leaf).
        let leaf = &dag.blocks[0];
        node.tamper(&leaf.cid, b"this is not the committed chunk!");
        let err = fetch_cat(&node, &dag.root).unwrap_err();
        assert!(matches!(err, IpfsError::CidMismatch { .. }), "got {err:?}");
    }

    #[test]
    fn a_missing_block_is_not_found() {
        let node = MockIpfs::new();
        let content: Vec<u8> = (0..300u32).map(|i| i as u8).collect();
        let dag = build_file_dag_with(&content, 64, DEFAULT_MAX_LINKS);
        // Pin everything EXCEPT one leaf.
        for b in dag.blocks.iter().skip(1) {
            node.put_block(&b.cid, &b.bytes).unwrap();
        }
        // Now forget one leaf so it is unavailable during the walk.
        node.forget(&dag.blocks[0].cid);
        assert!(matches!(
            fetch_cat(&node, &dag.root),
            Err(IpfsError::NotFound(_))
        ));
    }

    #[test]
    fn dir_round_trips_including_a_multi_block_file() {
        let node = MockIpfs::new();
        // One small file + one file large enough to chunk into a multi-block DAG.
        let big: Vec<u8> = (0..500u32).map(|i| (i * 13 % 251) as u8).collect();
        let entries: [(&str, &[u8]); 3] = [
            ("manifest.txt", b"hello manifest"),
            ("universe.bin", &big),
            ("a.txt", b"first by name"),
        ];
        let dag = build_dir_dag_with(&entries, 64, 3).unwrap();
        assert!(dag.root.is_dag_pb());
        // Canonical order is name-sorted regardless of the caller's order.
        let names: Vec<&str> = dag.entries.iter().map(|(n, _)| n.as_str()).collect();
        assert_eq!(names, ["a.txt", "manifest.txt", "universe.bin"]);
        // The big entry really is a multi-block file DAG (its root is dag-pb).
        assert!(dag.entries[2].1.is_dag_pb());
        for b in &dag.blocks {
            node.put_block(&b.cid, &b.bytes).unwrap();
        }
        let fetched = fetch_dir(&node, &dag.root).unwrap();
        assert_eq!(fetched.len(), 3);
        assert_eq!(fetched[0], ("a.txt".to_string(), b"first by name".to_vec()));
        assert_eq!(
            fetched[1],
            ("manifest.txt".to_string(), b"hello manifest".to_vec())
        );
        assert_eq!(fetched[2], ("universe.bin".to_string(), big));
    }

    #[test]
    fn dir_cid_is_order_independent() {
        let a: [(&str, &[u8]); 2] = [("x", b"one"), ("y", b"two")];
        let b: [(&str, &[u8]); 2] = [("y", b"two"), ("x", b"one")];
        assert_eq!(
            build_dir_dag(&a).unwrap().root,
            build_dir_dag(&b).unwrap().root
        );
    }

    #[test]
    fn a_tampered_dir_block_is_refused() {
        let node = MockIpfs::new();
        let big: Vec<u8> = (0..500u32).map(|i| i as u8).collect();
        let entries: [(&str, &[u8]); 2] = [("small", b"tiny"), ("big", &big)];
        let dag = build_dir_dag_with(&entries, 64, 3).unwrap();
        for b in &dag.blocks {
            node.put_block(&b.cid, &b.bytes).unwrap();
        }
        // Tamper the DIRECTORY node itself (the last block).
        let dir_block = dag.blocks.last().unwrap();
        node.tamper(&dir_block.cid, b"not the directory you committed");
        assert!(matches!(
            fetch_dir(&node, &dag.root).unwrap_err(),
            IpfsError::CidMismatch { .. }
        ));
        // Restore, then tamper a LEAF of an entry's file DAG instead.
        node.put_block(&dir_block.cid, &dir_block.bytes).unwrap();
        node.tamper(&dag.blocks[0].cid, b"evil leaf");
        assert!(matches!(
            fetch_dir(&node, &dag.root).unwrap_err(),
            IpfsError::CidMismatch { .. }
        ));
    }

    #[test]
    fn a_missing_dir_block_is_not_found() {
        let node = MockIpfs::new();
        let big: Vec<u8> = (0..500u32).map(|i| i as u8).collect();
        let entries: [(&str, &[u8]); 2] = [("small", b"tiny"), ("big", &big)];
        let dag = build_dir_dag_with(&entries, 64, 3).unwrap();
        for b in dag.blocks.iter().skip(1) {
            node.put_block(&b.cid, &b.bytes).unwrap();
        }
        node.forget(&dag.blocks[0].cid);
        assert!(matches!(
            fetch_dir(&node, &dag.root),
            Err(IpfsError::NotFound(_))
        ));
    }

    #[test]
    fn dir_build_refuses_bad_names() {
        let dup: [(&str, &[u8]); 2] = [("same", b"a"), ("same", b"b")];
        assert!(matches!(
            build_dir_dag(&dup),
            Err(IpfsError::InvalidDirectory(_))
        ));
        let empty: [(&str, &[u8]); 1] = [("", b"a")];
        assert!(matches!(
            build_dir_dag(&empty),
            Err(IpfsError::InvalidDirectory(_))
        ));
        let pathy: [(&str, &[u8]); 1] = [("a/b", b"a")];
        assert!(matches!(
            build_dir_dag(&pathy),
            Err(IpfsError::InvalidDirectory(_))
        ));
    }

    #[test]
    fn fetch_cat_refuses_a_directory_and_fetch_dir_refuses_a_file() {
        let node = MockIpfs::new();
        let entries: [(&str, &[u8]); 1] = [("f", b"content")];
        let dir_root = pin_dir(&node, &entries).unwrap();
        // cat on a directory is a named refusal, not a silent concatenation.
        assert!(matches!(
            fetch_cat(&node, &dir_root).unwrap_err(),
            IpfsError::InvalidDirectory(_)
        ));
        // fetch_dir on a (chunked) FILE root is a named refusal too.
        let content: Vec<u8> = (0..300u32).map(|i| i as u8).collect();
        let file = build_file_dag_with(&content, 64, DEFAULT_MAX_LINKS);
        for b in &file.blocks {
            node.put_block(&b.cid, &b.bytes).unwrap();
        }
        assert!(matches!(
            fetch_dir(&node, &file.root).unwrap_err(),
            IpfsError::InvalidDirectory(_)
        ));
        // And fetch_dir on a raw leaf is refused as not-a-dag-pb-node.
        let raw = node.put_raw(b"just a blob").unwrap();
        assert!(matches!(
            fetch_dir(&node, &raw).unwrap_err(),
            IpfsError::InvalidDirectory(_)
        ));
    }

    #[test]
    fn nested_directory_entries_are_refused_on_fetch() {
        // Hand-build a directory whose entry links to ANOTHER directory: the verified
        // read refuses it (single-level scope) rather than cat-ing it.
        let node = MockIpfs::new();
        let inner: [(&str, &[u8]); 1] = [("leaf", b"inner content")];
        let inner_dag = build_dir_dag(&inner).unwrap();
        for b in &inner_dag.blocks {
            node.put_block(&b.cid, &b.bytes).unwrap();
        }
        // Outer dir node linking the inner DIRECTORY by name.
        let mut outer = Vec::new();
        let link = encode_pb_link_named(&inner_dag.root.to_bytes(), "nested", 1);
        pb_field_bytes(&mut outer, 2, &link);
        let mut data = Vec::new();
        pb_field_varint(&mut data, 1, UNIXFS_TYPE_DIRECTORY);
        pb_field_bytes(&mut outer, 1, &data);
        let outer_cid = Cid::from_blake3_digest(CODEC_DAG_PB, *blake3::hash(&outer).as_bytes());
        node.put_block(&outer_cid, &outer).unwrap();
        assert!(matches!(
            fetch_dir(&node, &outer_cid).unwrap_err(),
            IpfsError::InvalidDirectory(_)
        ));
    }

    #[test]
    fn pb_varint_round_trips() {
        for v in [0u64, 1, 127, 128, 300, 262144, u64::MAX] {
            let mut buf = Vec::new();
            pb_write_varint(&mut buf, v);
            let mut p = 0;
            assert_eq!(pb_read_varint(&buf, &mut p).unwrap(), v);
            assert_eq!(p, buf.len());
        }
    }
}
