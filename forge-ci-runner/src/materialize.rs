//! THE MATERIALIZATION ADAPTER — the bridge that closes the `input_root` seam.
//!
//! The forge gate ([`dregg_doc::check::RequiredCheck::ci_run`]) accepts a
//! [`dregg_doc::CiVerdict`] only when `verdict.input_root ==
//! pr.input_root() == dregg_doc::substrate_commit(pr.merged_graph())`. The
//! confined runner ([`crate::run_check_confined`]) computes its verdict's
//! `input_root` from the WORKING TREE it ran on ([`crate::input_root_of_dir`]).
//! For the two to agree, the working tree the command ran against must be the
//! materialization of the PR's merged code, and the runner's projection of that
//! tree must fold back to the SAME root the forge binds.
//!
//! ## What a PR's code is (single document, not a file tree)
//!
//! In dregg-doc today a pull request is over ONE base/head [`History`] of ONE
//! [`DocGraph`] ([`dregg_doc::PullRequest::merged_graph`] returns a single
//! `DocGraph`). So "the PR's code" is one document: the fold of a patch history.
//! There is no path→doc repository tree yet (that is the named onward seam — see
//! the crate report).
//!
//! ## Why the canonical unit is the HISTORY, not the bare graph
//!
//! [`substrate_commit`] binds each atom's PROVENANCE (`author ‖ patch-id`), not
//! just its content ([`dregg_doc::substrate`]). Provenance is not reconstructible
//! from a rendered-text dump, and dregg-doc exposes no public constructor that
//! stamps an arbitrary provenance onto an atom (the graph mutators are
//! `pub(crate)`; a patch's id is content-derived from its `(author, ops)`, never
//! settable). The ONLY faithful, public reconstruction path is therefore to
//! REPLAY the patch history: replaying the identical `(author, ops)` patches
//! re-derives every patch-id — hence every atom's provenance — bit-for-bit
//! ([`History::replay`] is deterministic). This is exactly why dregg-doc's own
//! reopen path ([`dregg_doc::DocHeapCell`]) reconstructs a document FROM its
//! committed patch-history rather than from a graph snapshot.
//!
//! So the materialization writes the patch history as a canonical sidecar and the
//! runner's [`crate::input_root_of_dir`] reconstructs from THAT — making the
//! round-trip exact and provenance-faithful.
//!
//! ## The reconciliation (how the two projections are made to agree)
//!
//! [`materialize`] writes two things under the work dir:
//! - `document.txt` — the merged document's RENDERED content (what the CI command
//!   actually reads / builds / tests); and
//! - `.dregg-ci/merged.history` — the CANONICAL serialization of the patch
//!   history whose fold is that document (the code-state root source).
//!
//! [`crate::input_root_of_dir`] is taught to recognise the sidecar: when
//! `.dregg-ci/merged.history` is present it DESERIALIZES the history, REPLAYS it
//! to a [`DocGraph`], and returns [`substrate_commit`] of THAT graph — the very
//! same value [`canonical_input_root`] and the forge's `pr.input_root()` compute.
//! When the sidecar is absent it falls back to the file-tree→(path,hash)
//! projection (unchanged), so a raw tree still hashes deterministically.
//!
//! The round-trip that closes the seam:
//! ```text
//!   input_root_of_dir(materialize(h)) = substrate_commit(replay(decode(encode(h))))
//!                                      = substrate_commit(replay(h))   [codec round-trips]
//!                                      = canonical_input_root(h)
//!                                      = substrate_commit(pr.merged_graph())  [merged == replay(h)]
//!                                      = pr.input_root()
//! ```
//! so a verdict the runner produces over the materialized tree carries the exact
//! `input_root` a real PR's L1 gate binds.

use std::io;
use std::path::{Path, PathBuf};

use dregg_doc::{content, substrate_commit, Author, History, Op, Patch};

/// The sidecar directory the materialization writes under a work dir.
pub const SIDECAR_DIR: &str = ".dregg-ci";
/// The canonical patch-history file inside [`SIDECAR_DIR`] — the code-state root
/// source [`crate::input_root_of_dir`] reads.
pub const HISTORY_FILE: &str = "merged.history";
/// The rendered-content file the CI command runs against.
pub const DOCUMENT_FILE: &str = "document.txt";

/// Domain/version tag heading the serialized patch-history payload. Mirrors
/// dregg-doc's own `dregg-doc/history/v1` op grammar (so the format is the
/// document language's, not an ad-hoc one), carried in a file this crate owns.
const HISTORY_DOMAIN: &[u8] = b"forge-ci-runner/merged-history/v1";

/// The path of the history sidecar under a work dir.
pub fn history_sidecar_path(work_dir: &Path) -> PathBuf {
    work_dir.join(SIDECAR_DIR).join(HISTORY_FILE)
}

/// The path of the rendered document under a work dir.
pub fn document_path(work_dir: &Path) -> PathBuf {
    work_dir.join(DOCUMENT_FILE)
}

/// **THE PR'S CANONICAL CODE-STATE ROOT** — [`substrate_commit`] of the history's
/// fold. Equals `pr.input_root()` for the PR whose merged code is this history's
/// replay, and equals [`crate::input_root_of_dir`] of [`materialize`]'s output.
pub fn canonical_input_root(history: &History) -> [u8; 32] {
    substrate_commit(&history.replay())
}

/// **MATERIALIZE** a PR's merged code (as its patch [`History`]) into `work_dir`:
/// write the rendered content to `document.txt` (what the CI command runs on) and
/// the canonical patch-history to `.dregg-ci/merged.history` (the code-state root
/// source). After this, `input_root_of_dir(work_dir) == canonical_input_root(history)`.
pub fn materialize(history: &History, work_dir: &Path) -> io::Result<()> {
    std::fs::create_dir_all(work_dir)?;

    // The rendered document — the folded, human-readable content the command acts
    // on. (`to_marked_string` renders clean runs verbatim and any residual
    // conflict region between markers; a landable PR is clean.)
    let graph = history.replay();
    let rendered = content(&graph).to_marked_string();
    std::fs::write(document_path(work_dir), rendered.as_bytes())?;

    // The canonical patch history — the root source. Written last so a present
    // sidecar always implies a fully-written document beside it.
    let sidecar = history_sidecar_path(work_dir);
    if let Some(parent) = sidecar.parent() {
        std::fs::create_dir_all(parent)?;
    }
    std::fs::write(sidecar, encode_history(history))?;
    Ok(())
}

/// Read a materialized patch-history from `work_dir`, if the sidecar is present.
/// `Ok(None)` when there is no sidecar (a raw tree — the caller falls back to the
/// file projection); an [`io::ErrorKind::InvalidData`] when the sidecar is
/// present but malformed (a tampered/truncated payload is refused, never silently
/// treated as an empty history).
pub fn read_materialized_history(work_dir: &Path) -> io::Result<Option<History>> {
    let sidecar = history_sidecar_path(work_dir);
    match std::fs::read(&sidecar) {
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(e) => Err(e),
        Ok(bytes) => decode_history(&bytes)
            .map(Some)
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "malformed merged.history")),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The patch-history codec — a canonical, length-prefixed, domain-tagged byte
// serialization over the PUBLIC `Op` grammar. Canonical (order IS the data), so
// the same history always encodes to the same bytes; the decoder is strict
// (wrong tag / unknown op / truncation / bad UTF-8 / trailing garbage → refuse).
// Faithful because it reconstructs the exact `Patch::by(author, ops)` — whose
// content-derived id, hence every atom's provenance, re-derives bit-for-bit.
// ─────────────────────────────────────────────────────────────────────────────

fn enc_run(out: &mut Vec<u8>, b: &[u8]) {
    out.extend_from_slice(&(b.len() as u64).to_le_bytes());
    out.extend_from_slice(b);
}

fn enc_op(out: &mut Vec<u8>, op: &Op) {
    match op {
        Op::Add { id, content, after } => {
            out.push(0);
            out.extend_from_slice(&id.0.to_le_bytes());
            enc_run(out, content.as_bytes());
            out.extend_from_slice(&after.0.to_le_bytes());
        }
        Op::Delete { id } => {
            out.push(1);
            out.extend_from_slice(&id.0.to_le_bytes());
        }
        Op::Connect { from, to } => {
            out.push(2);
            out.extend_from_slice(&from.0.to_le_bytes());
            out.extend_from_slice(&to.0.to_le_bytes());
        }
        Op::SetField {
            name,
            value,
            superseding,
        } => {
            out.push(3);
            enc_run(out, name.as_bytes());
            enc_run(out, value.as_bytes());
            out.push(u8::from(*superseding));
        }
        Op::Resurrect { id } => {
            out.push(4);
            out.extend_from_slice(&id.0.to_le_bytes());
        }
        Op::Disconnect { from, to } => {
            out.push(5);
            out.extend_from_slice(&from.0.to_le_bytes());
            out.extend_from_slice(&to.0.to_le_bytes());
        }
        Op::RetractField { name } => {
            out.push(6);
            enc_run(out, name.as_bytes());
        }
    }
}

/// The canonical byte serialization of a history: domain tag, patch count, then
/// each patch `(author, op-count, ops)` in chain order.
pub fn encode_history(h: &History) -> Vec<u8> {
    let mut out = Vec::new();
    enc_run(&mut out, HISTORY_DOMAIN);
    out.extend_from_slice(&(h.len() as u64).to_le_bytes());
    for p in h.patches() {
        out.extend_from_slice(&p.author.0.to_le_bytes());
        out.extend_from_slice(&(p.ops.len() as u64).to_le_bytes());
        for op in &p.ops {
            enc_op(&mut out, op);
        }
    }
    out
}

/// A strict little-endian cursor over untrusted bytes: every read is bounds-
/// checked; any shortfall is `None`.
struct Dec<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Dec<'a> {
    fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        let end = self.at.checked_add(n)?;
        if end > self.bytes.len() {
            return None;
        }
        let s = &self.bytes[self.at..end];
        self.at = end;
        Some(s)
    }
    fn u8(&mut self) -> Option<u8> {
        Some(self.take(1)?[0])
    }
    fn u64(&mut self) -> Option<u64> {
        Some(u64::from_le_bytes(self.take(8)?.try_into().ok()?))
    }
    fn u128(&mut self) -> Option<u128> {
        Some(u128::from_le_bytes(self.take(16)?.try_into().ok()?))
    }
    fn atom_id(&mut self) -> Option<dregg_doc::AtomId> {
        Some(dregg_doc::AtomId(self.u128()?))
    }
    fn run(&mut self) -> Option<&'a [u8]> {
        let n = self.u64()? as usize;
        self.take(n)
    }
    fn string(&mut self) -> Option<String> {
        String::from_utf8(self.run()?.to_vec()).ok()
    }
}

/// Decode a history from its canonical bytes — the strict inverse of
/// [`encode_history`]. `None` on a wrong domain tag, an unknown op tag,
/// truncation, invalid UTF-8, or trailing garbage.
pub fn decode_history(bytes: &[u8]) -> Option<History> {
    let mut d = Dec { bytes, at: 0 };
    if d.run()? != HISTORY_DOMAIN {
        return None;
    }
    let n_patches = d.u64()? as usize;
    let mut h = History::new();
    for _ in 0..n_patches {
        let author = Author(d.u64()?);
        let n_ops = d.u64()? as usize;
        let mut ops = Vec::with_capacity(n_ops);
        for _ in 0..n_ops {
            ops.push(match d.u8()? {
                0 => Op::Add {
                    id: d.atom_id()?,
                    content: d.string()?,
                    after: d.atom_id()?,
                },
                1 => Op::Delete { id: d.atom_id()? },
                2 => Op::Connect {
                    from: d.atom_id()?,
                    to: d.atom_id()?,
                },
                3 => Op::SetField {
                    name: d.string()?,
                    value: d.string()?,
                    superseding: d.u8()? != 0,
                },
                4 => Op::Resurrect { id: d.atom_id()? },
                5 => Op::Disconnect {
                    from: d.atom_id()?,
                    to: d.atom_id()?,
                },
                6 => Op::RetractField { name: d.string()? },
                _ => return None,
            });
        }
        h.commit(Patch::by(author, ops));
    }
    if d.at != bytes.len() {
        return None; // trailing garbage → malformed
    }
    Some(h)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::input_root_of_dir;
    use dregg_doc::{substrate_commit, AtomId, History, Patch, PullRequest};

    /// A small two-atom document history ("two\nthree\n"), mirroring how
    /// dregg-doc's own PR tests build a clean history.
    fn sample_history() -> History {
        let mut h = History::new();
        let (a, op_a) = Patch::add(1, "two\n", AtomId::ROOT);
        h.commit(Patch::by(dregg_doc::Author(2), [op_a]));
        let (_b, op_b) = Patch::add(2, "three\n", a);
        h.commit(Patch::by(dregg_doc::Author(2), [op_b]));
        h
    }

    /// A DIFFERENT history (appends "four\n" not "three\n").
    fn other_history() -> History {
        let mut h = History::new();
        let (a, op_a) = Patch::add(1, "two\n", AtomId::ROOT);
        h.commit(Patch::by(dregg_doc::Author(2), [op_a]));
        let (_b, op_b) = Patch::add(4, "four\n", a);
        h.commit(Patch::by(dregg_doc::Author(2), [op_b]));
        h
    }

    fn tempdir(tag: &str) -> PathBuf {
        use std::sync::atomic::{AtomicU64, Ordering};
        static N: AtomicU64 = AtomicU64::new(0);
        let p = std::env::temp_dir().join(format!(
            "{tag}-{}-{}",
            std::process::id(),
            N.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&p).unwrap();
        p
    }

    // ── POLE (i): THE ROUND-TRIP. materialize(h) then input_root_of_dir folds
    //    back to the exact value the forge PR gate binds.
    #[test]
    fn round_trip_input_root_equals_substrate_commit_and_pr_input_root() {
        let h = sample_history();
        let dir = tempdir("fcr-mat-rt");
        materialize(&h, &dir).unwrap();

        let from_tree = input_root_of_dir(&dir).unwrap();

        // Both sides of the seam compute the same root...
        assert_eq!(
            from_tree,
            canonical_input_root(&h),
            "input_root_of_dir(materialize(h)) == canonical_input_root(h)"
        );
        assert_eq!(
            from_tree,
            substrate_commit(&h.replay()),
            "== substrate_commit(the merged graph)"
        );

        // ...and it is EXACTLY what a real PR's L1 gate would bind. For a clean PR
        // over an empty base, merged_graph == head.replay(), so pr.input_root()
        // == substrate_commit(h.replay()).
        let pr = PullRequest::open(History::new(), h.clone());
        assert_eq!(pr.input_root(), substrate_commit(&h.replay()));
        assert_eq!(
            from_tree,
            pr.input_root(),
            "the materialized tree folds to the PR's input_root — the gate binds it"
        );

        // The rendered document is on disk for the CI command to run against.
        let doc = std::fs::read_to_string(document_path(&dir)).unwrap();
        assert_eq!(doc, "two\nthree\n");

        let _ = std::fs::remove_dir_all(dir);
    }

    // ── POLE (iii): NO COLLISION. A different graph materializes to a different
    //    root (the projection is non-degenerate).
    #[test]
    fn distinct_histories_materialize_to_distinct_roots() {
        let (da, db) = (tempdir("fcr-mat-a"), tempdir("fcr-mat-b"));
        materialize(&sample_history(), &da).unwrap();
        materialize(&other_history(), &db).unwrap();

        let ra = input_root_of_dir(&da).unwrap();
        let rb = input_root_of_dir(&db).unwrap();
        assert_ne!(ra, rb, "distinct merged code → distinct input_root");
        assert_ne!(
            ra,
            substrate_commit(&History::new().replay()),
            "a populated document is not the empty-document root"
        );

        for d in [da, db] {
            let _ = std::fs::remove_dir_all(d);
        }
    }

    // The codec round-trips ANY history bit-for-bit (provenance fidelity rests on
    // this), and the strict decoder refuses tampering.
    #[test]
    fn codec_round_trips_and_rejects_tampering() {
        let h = sample_history();
        let bytes = encode_history(&h);
        let back = decode_history(&bytes).expect("clean decode");
        assert_eq!(back, h, "history codec is exact");
        assert_eq!(
            substrate_commit(&back.replay()),
            substrate_commit(&h.replay())
        );

        assert!(
            decode_history(&bytes[..bytes.len() - 1]).is_none(),
            "truncation refused"
        );
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert!(
            decode_history(&trailing).is_none(),
            "trailing garbage refused"
        );
        assert!(
            decode_history(b"not-a-history").is_none(),
            "wrong domain refused"
        );
    }
}
