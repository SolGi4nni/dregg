//! `ipfs` — the **PUBLISH/FETCH join**: a published universe travels over IPFS,
//! verify-don't-trust end to end.
//!
//! ## The two-address relationship (read this first)
//!
//! A universe on IPFS has **two addresses with two jobs**, and they are never
//! conflated:
//!
//! - **[`UniverseId`] — the authorship commitment.** A domain-tagged blake3 over the
//!   universe's *semantics* (name, label, source, deploy identity, provenance, win,
//!   parent, author key). It is what the [`Registry`](crate::Registry) keys by, what
//!   an author signs, what a derivation edge names. It is *not* a hash of any byte
//!   serialization.
//! - **the CID — the transport address.** `blake3` over the canonical *payload
//!   bytes* this module encodes ([the wire format](#the-canonical-wire-format)),
//!   wrapped as a CIDv1 by `dregg-ipfs`. It is what an IPFS node routes, pins, and
//!   serves by.
//!
//! The bridge between them is **re-derivation, never trust**: [`fetch_universe`]
//! re-witnesses the fetched *bytes* against the CID (every block, via dregg-ipfs's
//! verified walk), then reconstructs the universe through the REAL publish
//! validation ([`UniversePlan`] — parse, compile, deploy, attestation-signature
//! verify) and **re-derives the [`UniverseId`] from the content itself**. A caller
//! holding an expected id (say, from a registry entry or a derivation edge) passes
//! it in and a mismatch is a named refusal. So a lying node can serve neither
//! tampered bytes (CID re-witness refuses) nor a *different* validly-addressed
//! universe under a swapped CID (the re-derived id refuses). The CID locates; the
//! UniverseId identifies.
//!
//! ## The canonical wire format
//!
//! The payload is a deliberately minimal, versioned, deterministic binary encoding
//! (magic `ugc-dregg/universe-wire/v1`, length-prefixed fields) carrying exactly the
//! inputs the public publish constructors need — for a procgen universe that is the
//! 32-byte committed seed (the scene REGENERATES from it byte-for-byte on decode,
//! through procgen's verified draw stream), for an authored one the source + win.
//! Decoding *is* publishing: the same parse/compile/deploy/attest gates run, so a
//! payload that decodes at all is a real, deployable, correctly-attributed universe.
//! A [`ProofAnchor`](crate::ProofAnchor) is **not** carried — it is board-side
//! configuration distributed like a verification key, not world content (it does not
//! enter the [`UniverseId`] either).
//!
//! ## Pieces
//!
//! - [`publish_universe`] — pin the canonical payload (one raw block when it fits,
//!   else a UnixFS file DAG) and return both addresses. Refuses to pin a payload
//!   that does not re-derive the universe's own id (the round-trip is checked
//!   *before* anything leaves the process).
//! - [`fetch_universe`] — the verified inverse described above.
//! - [`bundle_universe_car`] / [`import_universe_car`] — the whole universe as one
//!   offline artifact: a UnixFS **directory** (`universe.bin` + a human-legible
//!   `manifest.txt` naming the id + author) exported as a **CAR v1** stream; the
//!   import re-witnesses every block, re-derives the id, and cross-checks the
//!   manifest's claim against the re-derived truth.

use std::fmt;

use dregg_ipfs::car::{CarError, export_car, import_car};
use dregg_ipfs::cid::Cid;
use dregg_ipfs::client::{IpfsClient, IpfsError};
use dregg_ipfs::unixfs::{Block, build_dir_dag, fetch_cat, fetch_dir, pin_file};
use procgen_dregg::CommittedSeed;

use crate::{
    AuthorSignature, Provenance, PublishError, Universe, UniverseId, UniversePlan, WinCondition,
};

/// The wire-format magic + version. Bump the suffix on any encoding change — an
/// unknown magic is a named refusal, never a guess.
const WIRE_MAGIC: &[u8] = b"ugc-dregg/universe-wire/v1\n";

/// The directory entry name of the canonical payload inside a universe CAR.
pub const CAR_PAYLOAD_NAME: &str = "universe.bin";
/// The directory entry name of the human-legible manifest inside a universe CAR.
pub const CAR_MANIFEST_NAME: &str = "manifest.txt";

/// Why a universe could not cross the IPFS join. Every arm is a refusal with a name.
#[derive(Debug)]
pub enum UgcIpfsError {
    /// The IPFS transport / verified-walk layer refused (not-found, CID mismatch on
    /// a tampered block, …).
    Ipfs(IpfsError),
    /// The CAR codec refused (tampered frame, missing root, broken closure, …).
    Car(CarError),
    /// The payload bytes are not the canonical wire format (bad magic, truncated
    /// field, trailing bytes, …).
    Decode(String),
    /// The payload decoded structurally but did not *re-publish*: the scene failed
    /// parse/compile/deploy, or the carried attestation signature did not verify
    /// over the reconstructed content commitment.
    Publish(PublishError),
    /// **The identity tooth**: the [`UniverseId`] re-derived from the content is not
    /// the expected one. On fetch/import: the transport served a different universe
    /// than the caller asked for. On publish/bundle: the encoding failed to
    /// round-trip the universe's own identity (refused before pinning anything).
    IdMismatch {
        expected: UniverseId,
        got: UniverseId,
    },
    /// The CAR's directory is not the expected bundle shape (missing entry, more
    /// than one root, …).
    BundleShape(String),
    /// The bundle's manifest claims an id/author-key that disagrees with the truth
    /// re-derived from `universe.bin` — a doctored label over honest content.
    ManifestMismatch(String),
}

impl fmt::Display for UgcIpfsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UgcIpfsError::Ipfs(e) => write!(f, "ipfs: {e}"),
            UgcIpfsError::Car(e) => write!(f, "car: {e}"),
            UgcIpfsError::Decode(e) => write!(f, "universe wire decode: {e}"),
            UgcIpfsError::Publish(e) => write!(f, "fetched universe did not re-publish: {e}"),
            UgcIpfsError::IdMismatch { expected, got } => write!(
                f,
                "universe id re-derived from content is {got}, expected {expected}"
            ),
            UgcIpfsError::BundleShape(e) => write!(f, "universe CAR bundle shape: {e}"),
            UgcIpfsError::ManifestMismatch(e) => write!(f, "manifest disagrees with content: {e}"),
        }
    }
}

impl std::error::Error for UgcIpfsError {}

impl From<IpfsError> for UgcIpfsError {
    fn from(e: IpfsError) -> UgcIpfsError {
        UgcIpfsError::Ipfs(e)
    }
}
impl From<CarError> for UgcIpfsError {
    fn from(e: CarError) -> UgcIpfsError {
        UgcIpfsError::Car(e)
    }
}
impl From<PublishError> for UgcIpfsError {
    fn from(e: PublishError) -> UgcIpfsError {
        UgcIpfsError::Publish(e)
    }
}

/// The receipt of [`publish_universe`]: **both addresses** of the published universe
/// (see the module header for their distinct jobs).
#[derive(Clone, Debug)]
pub struct PublishedUniverse {
    /// The authorship commitment — the registry key, unchanged by transport.
    pub universe_id: UniverseId,
    /// The transport address the payload was pinned under: a raw blake3 CID when the
    /// payload fits one block (the common case — the CID *is* `blake3(payload)`),
    /// else the dag-pb root of a UnixFS file DAG over the payload.
    pub payload_cid: Cid,
    /// The canonical payload length in bytes.
    pub payload_len: usize,
}

// ═══════════════════════════════════════════════════════════════════════════════
// publish / fetch
// ═══════════════════════════════════════════════════════════════════════════════

/// **PUBLISH a universe to IPFS**: encode the canonical payload, prove to ourselves
/// it re-derives the universe's own [`UniverseId`] (a payload that would come back
/// as a different universe is refused *before* a byte is pinned), then pin it —
/// one raw block when it fits, else a UnixFS file DAG — returning both addresses.
pub fn publish_universe<C: IpfsClient>(
    client: &C,
    universe: &Universe,
) -> Result<PublishedUniverse, UgcIpfsError> {
    let payload = wire_encode(universe);
    verify_rederives(universe, &payload)?;
    // `pin_file` handles both sizes: content within one chunk pins as a single raw
    // block whose CID IS blake3(payload); larger content becomes a verified file DAG.
    let payload_cid = pin_file(client, &payload)?;
    Ok(PublishedUniverse {
        universe_id: universe.id(),
        payload_cid,
        payload_len: payload.len(),
    })
}

/// **FETCH a universe from IPFS, verify-don't-trust**:
///
/// 1. fetch the payload through the verified walk (`fetch_cat` — every block
///    re-witnessed against its own CID; a tampered byte is a refusal);
/// 2. reconstruct the universe through the REAL publish validation (parse, compile,
///    deploy, attestation verify) — decoding *is* publishing;
/// 3. **re-derive the [`UniverseId`] from the content** and, when the caller knows
///    which universe this is supposed to be, refuse a mismatch
///    ([`UgcIpfsError::IdMismatch`]).
///
/// Pass `expected` whenever you hold an id from a registry entry / derivation edge /
/// manifest — it closes the substitution hole a bare CID leaves open (a node serving
/// a *different*, validly-addressed universe). With `expected = None` the returned
/// universe is still internally sound (its id is re-derived, its attestation
/// verified); the caller just hasn't bound it to a prior commitment.
pub fn fetch_universe<C: IpfsClient>(
    client: &C,
    cid: &Cid,
    expected: Option<&UniverseId>,
) -> Result<Universe, UgcIpfsError> {
    let payload = fetch_cat(client, cid)?;
    let universe = wire_decode(&payload)?;
    if let Some(want) = expected {
        if universe.id() != *want {
            return Err(UgcIpfsError::IdMismatch {
                expected: *want,
                got: universe.id(),
            });
        }
    }
    Ok(universe)
}

// ═══════════════════════════════════════════════════════════════════════════════
// the CAR bundle — a universe as one offline, self-verifying artifact
// ═══════════════════════════════════════════════════════════════════════════════

/// A built universe CAR bundle: the CAR v1 byte stream, its directory root CID, and
/// the universe's authorship commitment.
#[derive(Clone, Debug)]
pub struct UniverseCarBundle {
    /// The CAR v1 stream (header root = [`root`](Self::root), then the block closure).
    pub car: Vec<u8>,
    /// The UnixFS directory root: `{ manifest.txt, universe.bin }`.
    pub root: Cid,
    /// The authorship commitment of the bundled universe.
    pub universe_id: UniverseId,
}

/// **BUNDLE a universe as a CAR**: the canonical payload plus a small human-legible
/// manifest (naming the [`UniverseId`] + author) as a UnixFS directory, exported as
/// a CAR v1 stream — one file that any IPFS tool can import (`ipfs dag import`) and
/// that [`import_universe_car`] reads back fully re-verified. The same
/// refuse-before-emitting round-trip check as [`publish_universe`] runs first.
pub fn bundle_universe_car(universe: &Universe) -> Result<UniverseCarBundle, UgcIpfsError> {
    let payload = wire_encode(universe);
    verify_rederives(universe, &payload)?;
    let manifest = manifest_text(universe);
    let entries: [(&str, &[u8]); 2] = [
        (CAR_MANIFEST_NAME, manifest.as_bytes()),
        (CAR_PAYLOAD_NAME, &payload),
    ];
    let dir = build_dir_dag(&entries)?;
    let car = export_car(&dir.root, &dir.blocks)?;
    Ok(UniverseCarBundle {
        car,
        root: dir.root,
        universe_id: universe.id(),
    })
}

/// **IMPORT a universe CAR, re-verifying everything**:
///
/// 1. the CAR codec re-witnesses every block against its CID and checks root
///    presence + closure (a flipped byte anywhere is a named refusal, nothing
///    partially ingested);
/// 2. the directory must be the bundle shape (`universe.bin` + `manifest.txt`);
/// 3. `universe.bin` reconstructs through the real publish validation and the
///    [`UniverseId`] is **re-derived from content**;
/// 4. the manifest's *claims* (id, author key) are checked against that re-derived
///    truth — a doctored manifest over honest content is refused;
/// 5. `expected`, when given, is checked exactly as in [`fetch_universe`].
pub fn import_universe_car(
    car: &[u8],
    expected: Option<&UniverseId>,
) -> Result<Universe, UgcIpfsError> {
    let contents = import_car(car)?;
    if contents.roots.len() != 1 {
        return Err(UgcIpfsError::BundleShape(format!(
            "expected exactly one root, got {}",
            contents.roots.len()
        )));
    }
    let root = contents.roots[0].clone();
    // Serve the verified block set to the verified directory walk (read-only, no
    // network) — the walk re-witnesses each block a second time as it reads.
    let store = CarStore(&contents.blocks);
    let entries = fetch_dir(&store, &root)?;

    let payload = entry(&entries, CAR_PAYLOAD_NAME)?;
    let manifest = entry(&entries, CAR_MANIFEST_NAME)?;

    let universe = wire_decode(payload)?;
    check_manifest(manifest, &universe)?;
    if let Some(want) = expected {
        if universe.id() != *want {
            return Err(UgcIpfsError::IdMismatch {
                expected: *want,
                got: universe.id(),
            });
        }
    }
    Ok(universe)
}

/// A read-only [`IpfsClient`] over a verified CAR's block set, so the verified
/// directory/file walks can read an imported bundle with no network and no store.
struct CarStore<'a>(&'a [Block]);

impl IpfsClient for CarStore<'_> {
    fn put_raw(&self, _bytes: &[u8]) -> Result<Cid, IpfsError> {
        Err(IpfsError::Unsupported("CarStore is read-only".into()))
    }
    fn get(&self, cid: &Cid) -> Result<Vec<u8>, IpfsError> {
        self.0
            .iter()
            .find(|b| &b.cid == cid)
            .map(|b| b.bytes.clone())
            .ok_or_else(|| IpfsError::NotFound(cid.to_string_cid()))
    }
    fn pin(&self, _cid: &Cid) -> Result<(), IpfsError> {
        Err(IpfsError::Unsupported("CarStore is read-only".into()))
    }
}

fn entry<'a>(entries: &'a [(String, Vec<u8>)], name: &str) -> Result<&'a Vec<u8>, UgcIpfsError> {
    entries
        .iter()
        .find(|(n, _)| n == name)
        .map(|(_, bytes)| bytes)
        .ok_or_else(|| UgcIpfsError::BundleShape(format!("no `{name}` entry in the bundle")))
}

// ═══════════════════════════════════════════════════════════════════════════════
// the canonical wire format
// ═══════════════════════════════════════════════════════════════════════════════

/// Encode the canonical payload: the exact inputs the public publish constructors
/// need (see the module header). Deterministic: the same universe always encodes to
/// the same bytes, so its payload CID is stable.
fn wire_encode(u: &Universe) -> Vec<u8> {
    let mut out = Vec::from(WIRE_MAGIC);
    match u.provenance() {
        Provenance::Authored => {
            out.push(0); // kind: authored
            put_str(&mut out, u.name());
            put_str(&mut out, u.author());
            put_str(&mut out, u.source());
            let vars = &u.win().vars;
            out.extend_from_slice(&(vars.len() as u64).to_le_bytes());
            for (k, v) in vars {
                put_str(&mut out, k);
                out.extend_from_slice(&v.to_le_bytes());
            }
        }
        Provenance::Procgen { committed_seed } => {
            out.push(1); // kind: procgen — name/source/win/deploy all REGENERATE
            put_str(&mut out, u.author());
            out.extend_from_slice(committed_seed);
        }
    }
    match u.parent() {
        None => out.push(0),
        Some(p) => {
            out.push(1);
            out.extend_from_slice(p.as_bytes());
        }
    }
    match (u.author_id(), u.attestation()) {
        (Some(key), Some(sig)) => {
            out.push(1);
            out.extend_from_slice(key.as_bytes());
            out.extend_from_slice(sig.as_bytes());
        }
        _ => out.push(0),
    }
    out
}

/// Decode a canonical payload by **re-publishing it**: reconstruct through
/// [`UniversePlan`] (parse, compile, deploy; for procgen, regenerate the scene from
/// the committed seed through the verified draw stream) and re-verify any carried
/// attestation. The returned universe's id is therefore *derived from this content*,
/// never read from the payload — the payload does not even carry an id field.
fn wire_decode(bytes: &[u8]) -> Result<Universe, UgcIpfsError> {
    let rest = bytes
        .strip_prefix(WIRE_MAGIC)
        .ok_or_else(|| UgcIpfsError::Decode("missing or unknown wire magic/version".into()))?;
    let mut p = 0usize;

    enum Kind {
        Authored {
            name: String,
            label: String,
            source: String,
            win: WinCondition,
        },
        Procgen {
            label: String,
            seed: [u8; 32],
        },
    }

    let kind = match take_u8(rest, &mut p)? {
        0 => {
            let name = take_str(rest, &mut p)?;
            let label = take_str(rest, &mut p)?;
            let source = take_str(rest, &mut p)?;
            let count = take_u64(rest, &mut p)?;
            if count > 4096 {
                return Err(UgcIpfsError::Decode(format!("{count} win vars declared")));
            }
            let mut vars = Vec::new();
            for _ in 0..count {
                let k = take_str(rest, &mut p)?;
                let v = take_u64(rest, &mut p)?;
                vars.push((k, v));
            }
            Kind::Authored {
                name,
                label,
                source,
                win: WinCondition { vars },
            }
        }
        1 => {
            let label = take_str(rest, &mut p)?;
            let seed = take_arr::<32>(rest, &mut p)?;
            Kind::Procgen { label, seed }
        }
        other => {
            return Err(UgcIpfsError::Decode(format!(
                "unknown universe kind {other}"
            )));
        }
    };

    let parent = match take_u8(rest, &mut p)? {
        0 => None,
        1 => Some(UniverseId::from_bytes(take_arr::<32>(rest, &mut p)?)),
        other => return Err(UgcIpfsError::Decode(format!("bad parent flag {other}"))),
    };

    let author = match take_u8(rest, &mut p)? {
        0 => None,
        1 => {
            let key = take_arr::<32>(rest, &mut p)?;
            let sig = take_arr::<64>(rest, &mut p)?;
            Some((key, sig))
        }
        other => return Err(UgcIpfsError::Decode(format!("bad author flag {other}"))),
    };

    if p != rest.len() {
        return Err(UgcIpfsError::Decode(format!(
            "{} trailing bytes",
            rest.len() - p
        )));
    }

    // Re-PUBLISH: the same validation gates every publish runs.
    let plan = match kind {
        Kind::Authored {
            name,
            label,
            source,
            win,
        } => UniversePlan::authored(&name, &label, &source, win, parent)?,
        Kind::Procgen { label, seed } => {
            UniversePlan::procgen(&label, CommittedSeed::from_bytes(seed), parent)?
        }
    };
    let universe = match author {
        None => plan.anonymous(),
        Some((key, sig)) => plan.attest(key, AuthorSignature::from_bytes(sig))?,
    };
    Ok(universe)
}

/// The refuse-before-emitting round-trip check: the canonical payload must decode
/// back to a universe with the SAME re-derived id. Guards publish/bundle against any
/// drift between the wire format and the publish constructors (e.g. a constructor
/// default the encoding does not carry) — such a payload would come back as a
/// *different* universe, so it never leaves the process.
fn verify_rederives(universe: &Universe, payload: &[u8]) -> Result<(), UgcIpfsError> {
    let back = wire_decode(payload)?;
    if back.id() != universe.id() {
        return Err(UgcIpfsError::IdMismatch {
            expected: universe.id(),
            got: back.id(),
        });
    }
    Ok(())
}

// ── the manifest (human-legible; every claim checked against re-derived truth) ──

fn hex32(bytes: &[u8; 32]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// The bundle manifest: line-oriented, fixed layout. The id/author-key lines are
/// CLAIMS for human eyes and IPFS tooling — [`check_manifest`] verifies them against
/// the truth re-derived from `universe.bin`, so a doctored manifest cannot relabel
/// honest content.
fn manifest_text(u: &Universe) -> String {
    let mut s = String::new();
    s.push_str("ugc-dregg universe manifest v1\n");
    s.push_str(&format!("universe_id = {}\n", hex32(u.id().as_bytes())));
    s.push_str(&format!("author = {}\n", u.author()));
    if let Some(key) = u.author_id() {
        s.push_str(&format!("author_key = {}\n", key.hex()));
    }
    s
}

/// Check the manifest's claims against the re-derived universe. Layout-strict on the
/// lines that carry commitments (line 1 magic, line 2 `universe_id = …`) so a crafted
/// author label cannot inject a second id line that shadows the real one.
fn check_manifest(manifest: &[u8], universe: &Universe) -> Result<(), UgcIpfsError> {
    let text = std::str::from_utf8(manifest)
        .map_err(|_| UgcIpfsError::ManifestMismatch("manifest is not utf-8".into()))?;
    let mut lines = text.lines();
    if lines.next() != Some("ugc-dregg universe manifest v1") {
        return Err(UgcIpfsError::ManifestMismatch(
            "unknown manifest magic".into(),
        ));
    }
    let want_id = format!("universe_id = {}", hex32(universe.id().as_bytes()));
    let got_id = lines.next().unwrap_or_default();
    if got_id != want_id {
        return Err(UgcIpfsError::ManifestMismatch(format!(
            "manifest claims `{got_id}`, content re-derives `{want_id}`"
        )));
    }
    // If the content is signed, the manifest must name the SAME key (and vice versa:
    // a manifest naming a key over anonymous content is refused).
    let claimed_key = text
        .lines()
        .find_map(|l| l.strip_prefix("author_key = "))
        .map(str::to_string);
    let real_key = universe.author_id().map(|k| k.hex());
    if claimed_key != real_key {
        return Err(UgcIpfsError::ManifestMismatch(format!(
            "manifest author_key {claimed_key:?} != content's {real_key:?}"
        )));
    }
    Ok(())
}

// ── length-prefixed primitives ─────────────────────────────────────────────────

fn put_str(out: &mut Vec<u8>, s: &str) {
    out.extend_from_slice(&(s.len() as u64).to_le_bytes());
    out.extend_from_slice(s.as_bytes());
}

fn take_u8(bytes: &[u8], p: &mut usize) -> Result<u8, UgcIpfsError> {
    let b = *bytes
        .get(*p)
        .ok_or_else(|| UgcIpfsError::Decode("truncated byte".into()))?;
    *p += 1;
    Ok(b)
}

fn take_u64(bytes: &[u8], p: &mut usize) -> Result<u64, UgcIpfsError> {
    let arr = take_arr::<8>(bytes, p)?;
    Ok(u64::from_le_bytes(arr))
}

fn take_arr<const N: usize>(bytes: &[u8], p: &mut usize) -> Result<[u8; N], UgcIpfsError> {
    let end = p
        .checked_add(N)
        .filter(|&e| e <= bytes.len())
        .ok_or_else(|| UgcIpfsError::Decode(format!("truncated {N}-byte field")))?;
    let mut out = [0u8; N];
    out.copy_from_slice(&bytes[*p..end]);
    *p = end;
    Ok(out)
}

fn take_str(bytes: &[u8], p: &mut usize) -> Result<String, UgcIpfsError> {
    let len = take_u64(bytes, p)? as usize;
    let end = p
        .checked_add(len)
        .filter(|&e| e <= bytes.len())
        .ok_or_else(|| UgcIpfsError::Decode("string overruns the payload".into()))?;
    let s = std::str::from_utf8(&bytes[*p..end])
        .map_err(|_| UgcIpfsError::Decode("non-utf8 string field".into()))?
        .to_string();
    *p = end;
    Ok(s)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::WinCondition;
    use dregg_ipfs::client::MockIpfs;
    use ed25519_dalek::{Signer, SigningKey};

    const SCENE: &str = "---\nid: test-hoard\ntitle: The Test Hoard\nweight: 1\n---\n\n\
        === entry\n\nA test chamber.\n\n\
        * [Seize the hoard]\n  ~ gold += 500\n  -> END\n\n\
        * [Leave empty-handed]\n  -> END\n";

    fn authored() -> Universe {
        Universe::authored(
            "The Test Hoard",
            "ember",
            SCENE,
            WinCondition::ended_with(&[("gold", 500)]),
        )
        .unwrap()
    }

    fn signed() -> Universe {
        let sk = SigningKey::from_bytes(&[7u8; 32]);
        let plan =
            UniversePlan::authored("Signed Hoard", "ember", SCENE, WinCondition::ended(), None)
                .unwrap();
        let sig = sk.sign(&plan.signing_commitment());
        plan.attest(
            sk.verifying_key().to_bytes(),
            AuthorSignature::from_bytes(sig.to_bytes()),
        )
        .unwrap()
    }

    fn procgen() -> Universe {
        Universe::daily("dreggbot", &[42u8; 32]).unwrap()
    }

    #[test]
    fn publish_then_fetch_re_derives_the_same_universe() {
        let node = MockIpfs::new();
        for u in [authored(), signed(), procgen()] {
            let receipt = publish_universe(&node, &u).unwrap();
            assert_eq!(receipt.universe_id, u.id());
            let back = fetch_universe(&node, &receipt.payload_cid, Some(&u.id())).unwrap();
            // The id is RE-DERIVED from fetched content (the payload carries no id
            // field at all) and equals the published one.
            assert_eq!(back.id(), u.id());
            assert_eq!(back.name(), u.name());
            assert_eq!(back.source(), u.source());
            assert_eq!(back.author_id(), u.author_id());
            assert_eq!(back.provenance(), u.provenance());
            // A procgen universe still regenerates from its committed seed.
            if matches!(u.provenance(), Provenance::Procgen { .. }) {
                assert!(back.regenerates_from_seed());
            }
        }
    }

    #[test]
    fn the_payload_cid_is_deterministic() {
        let node = MockIpfs::new();
        let a = publish_universe(&node, &authored()).unwrap();
        let b = publish_universe(&node, &authored()).unwrap();
        assert_eq!(a.payload_cid, b.payload_cid);
    }

    #[test]
    fn tampered_payload_bytes_are_refused_at_the_cid() {
        let node = MockIpfs::new();
        let u = authored();
        let receipt = publish_universe(&node, &u).unwrap();
        node.tamper(&receipt.payload_cid, b"not the universe you committed");
        let err = fetch_universe(&node, &receipt.payload_cid, Some(&u.id()))
            .err()
            .expect("a tampered payload must be refused");
        match err {
            UgcIpfsError::Ipfs(IpfsError::CidMismatch { .. }) => {}
            other => panic!("expected a CID-mismatch refusal, got {other:?}"),
        }
    }

    #[test]
    fn an_expected_id_mismatch_is_refused() {
        let node = MockIpfs::new();
        let a = authored();
        let b = procgen();
        let receipt_a = publish_universe(&node, &a).unwrap();
        // Ask for A's CID but expect B's id: a valid, honestly-addressed payload
        // that is simply NOT the universe the caller committed to. Refused.
        let err = fetch_universe(&node, &receipt_a.payload_cid, Some(&b.id()))
            .err()
            .expect("an expected-id mismatch must be refused");
        match err {
            UgcIpfsError::IdMismatch { expected, got } => {
                assert_eq!(expected, b.id());
                assert_eq!(got, a.id());
            }
            other => panic!("expected IdMismatch, got {other:?}"),
        }
        // Without an expectation the fetch succeeds and reports what it truly is.
        let back = fetch_universe(&node, &receipt_a.payload_cid, None).unwrap();
        assert_eq!(back.id(), a.id());
    }

    #[test]
    fn a_forged_attestation_cannot_cross_the_join() {
        // Take a signed universe's payload and swap the author key for another key
        // (leaving the signature): the decode re-runs the REAL attestation verify
        // and refuses — authorship cannot be reassigned in transit.
        let u = signed();
        let payload = wire_encode(&u);
        let mut forged = payload.clone();
        let key_off = payload.len() - 96; // author flag(1) + key(32) + sig(64) tail
        assert_eq!(forged[key_off - 1], 1, "author flag precedes the key");
        forged[key_off] ^= 0x01;
        let err = wire_decode(&forged)
            .err()
            .expect("a forged author key must be refused");
        match err {
            UgcIpfsError::Publish(PublishError::AuthorSignature)
            | UgcIpfsError::Publish(PublishError::AuthorKey(_)) => {}
            other => panic!("expected an attestation refusal, got {other:?}"),
        }
    }

    #[test]
    fn garbage_and_truncated_payloads_are_named_refusals() {
        assert!(matches!(
            wire_decode(b"not a universe payload"),
            Err(UgcIpfsError::Decode(_))
        ));
        let payload = wire_encode(&authored());
        for keep in [WIRE_MAGIC.len(), payload.len() / 2, payload.len() - 1] {
            assert!(wire_decode(&payload[..keep]).is_err(), "kept {keep}");
        }
        // Trailing bytes are refused too (the encoding is canonical, not a prefix).
        let mut padded = payload.clone();
        padded.push(0);
        assert!(matches!(wire_decode(&padded), Err(UgcIpfsError::Decode(_))));
    }

    #[test]
    fn car_bundle_round_trips_end_to_end() {
        for u in [authored(), signed(), procgen()] {
            let bundle = bundle_universe_car(&u).unwrap();
            assert_eq!(bundle.universe_id, u.id());
            let back = import_universe_car(&bundle.car, Some(&u.id())).unwrap();
            assert_eq!(back.id(), u.id());
            assert_eq!(back.source(), u.source());
            assert_eq!(back.author_id(), u.author_id());
        }
    }

    #[test]
    fn a_flipped_byte_anywhere_in_the_car_bundle_is_refused() {
        let bundle = bundle_universe_car(&authored()).unwrap();
        let id = bundle.universe_id;
        for i in 0..bundle.car.len() {
            let mut evil = bundle.car.clone();
            evil[i] ^= 0x01;
            assert!(
                import_universe_car(&evil, Some(&id)).is_err(),
                "flipping CAR byte {i} was accepted"
            );
        }
    }

    #[test]
    fn a_doctored_manifest_over_honest_content_is_refused() {
        // Rebuild the bundle dir with a manifest claiming a DIFFERENT id: every
        // block still self-verifies (the CAR is honest about its bytes), but the
        // manifest's claim disagrees with the id re-derived from universe.bin.
        let u = authored();
        let payload = wire_encode(&u);
        let mut lying = manifest_text(&u);
        lying = lying.replace(&hex32(u.id().as_bytes()), &hex32(&[0xabu8; 32]));
        let entries: [(&str, &[u8]); 2] = [
            (CAR_MANIFEST_NAME, lying.as_bytes()),
            (CAR_PAYLOAD_NAME, &payload),
        ];
        let dir = build_dir_dag(&entries).unwrap();
        let car = export_car(&dir.root, &dir.blocks).unwrap();
        assert!(matches!(
            import_universe_car(&car, None).err(),
            Some(UgcIpfsError::ManifestMismatch(_))
        ));
    }

    #[test]
    fn a_bundle_missing_the_payload_is_a_shape_refusal() {
        let u = authored();
        let manifest = manifest_text(&u);
        let entries: [(&str, &[u8]); 1] = [(CAR_MANIFEST_NAME, manifest.as_bytes())];
        let dir = build_dir_dag(&entries).unwrap();
        let car = export_car(&dir.root, &dir.blocks).unwrap();
        assert!(matches!(
            import_universe_car(&car, None).err(),
            Some(UgcIpfsError::BundleShape(_))
        ));
    }

    #[test]
    fn import_expected_id_mismatch_is_refused() {
        let bundle = bundle_universe_car(&authored()).unwrap();
        let other = procgen().id();
        assert!(matches!(
            import_universe_car(&bundle.car, Some(&other)).err(),
            Some(UgcIpfsError::IdMismatch { .. })
        ));
    }

    #[test]
    fn a_fetched_universe_still_verifies_completions() {
        // The join composes with the flywheel: a universe fetched from IPFS drives
        // the SAME no-cheat verifier as a locally-published one.
        let node = MockIpfs::new();
        let u = authored();
        let receipt = publish_universe(&node, &u).unwrap();
        let fetched = fetch_universe(&node, &receipt.payload_cid, Some(&u.id())).unwrap();
        let play = crate::record_playthrough(&fetched, &[0]).unwrap();
        let turns = crate::verify_completion(
            &fetched,
            &crate::Completion {
                universe: fetched.id(),
                player: "player-1".into(),
                play,
                claimed_turns: 1,
            },
        )
        .unwrap();
        assert_eq!(turns, 1);
    }
}
