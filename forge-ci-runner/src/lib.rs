//! forge-ci-runner — "CHECK, DON'T TRUST" CI for the dregg-native forge.
//!
//! The forge gate [`dregg_doc::check::CheckRequirement::CiRun`] is satisfied by a
//! committed, executor-signed [`dregg_doc::CiVerdict`] bound inside a signed turn.
//! But the SIGNER is the CI host: it can sign a *well-formed* verdict for the
//! real code while having lied about what the command actually did. This crate is
//! the pair that closes that:
//!
//! - **L2 [`run_check_confined`]** — the CONFINED RUNNER. It runs the check
//!   command inside a macOS-Seatbelt confinement (firmament
//!   [`ProcessKernel::spawn_pd_confined_exec`](dregg_firmament::process_kernel::ProcessKernel::spawn_pd_confined_exec)),
//!   digests the confined process's stdout, reaps its exit code, and commits a
//!   [`CiVerdict`] as the GENESIS turn of a fresh CI-run cell via
//!   [`dregg_doc::run_ci_verdict`] — so the signed `turn_hash` equals the
//!   fresh-genesis re-derivation [`dregg_doc::planned_ci_run_hash`] the forge
//!   check runs (the L1 in-turn binding).
//!
//! - **L3 [`reexecute_and_verify`]** — the RE-EXECUTOR (the audit that replaces
//!   the circular one). Given a verdict + the same inputs, it re-runs the SAME
//!   command in a FRESH confinement and compares `{exit_code, output_digest,
//!   confinement_id}`. [`AuditVerdict::Honest`] iff every field matches;
//!   [`AuditVerdict::HostLied`] (naming the divergent field) otherwise. A host
//!   that signed `exit_code=0` over a command that actually failed, or a bogus
//!   `output_digest`, is CONVICTED here — detection is real, not circular.
//!
//! ## The determinism constraint (operational, load-bearing)
//!
//! `output_digest` matching across the L2 run and the L3 re-run REQUIRES the
//! check command to be DETERMINISTIC in the confined inputs. The confinement
//! HELPS by fixing the inputs (a fresh work dir seeded from `input_dir`, an
//! `execve` door to exactly one image, no ambient network) — but the command
//! ITSELF must not embed nondeterminism (wall-clock, RNG, absolute-temp-path
//! echoes, unsorted directory walks, network fetches). A flaky/nondeterministic
//! check is a FALSE-CONVICTION hazard: L3 would report [`AuditVerdict::HostLied`]
//! on an honest host whose output merely varied run-to-run. Use a check that
//! prints a stable digest of its inputs; if a build is inherently nondeterministic,
//! digest a normalized artifact, not the raw bytes. (This is why the runner
//! substitutes the per-run work dir through the [`WORK_TOKEN`] placeholder rather
//! than letting the absolute path leak into argv — the same tokenized argv drives
//! both runs, so the path itself never perturbs the output.)
//!
//! ## `input_root` and the materialization seam
//!
//! [`CiVerdict::input_root`] must equal the PR's `substrate_commit(merged_graph)`
//! ([`dregg_doc::PullRequest::input_root`]) for the forge gate to accept it.
//! [`input_root_of_dir`] computes that value with the REAL
//! [`dregg_doc::substrate_commit`] over a [`DocGraph`](dregg_doc::DocGraph)
//! projection of the working tree (one atom per file, keyed by relative path +
//! content digest, in sorted order). It equals a PR's `input_root` exactly when
//! the working tree the command ran against is the materialization of that PR's
//! `merged_graph`. THE ADAPTER SEAM is that doc-graph → working-tree
//! materialization (project a PR's merged `DocGraph` to files, run the command,
//! and this crate's projection folds it back to the identical root). Here the
//! projection is file-tree → `DocGraph`; the forge's `merged_graph` → file-tree
//! materializer is the inverse the real forge supplies. See the crate report.

#![cfg_attr(docsrs, feature(doc_cfg))]

// The confined-run core needs the firmament heavy-body jail, which is
// macOS-Seatbelt (`spawn_pd_confined_exec` is `cfg(process-pd-sandbox, unix)`;
// the SBPL backend is macOS). Gate the executing surface accordingly; the pure
// projection/id helpers below stay platform-independent.
#[cfg(target_os = "macos")]
mod confined;
#[cfg(target_os = "macos")]
pub use confined::{
    reexecute_and_verify, run_check_confined, AuditVerdict, CiRunReceipt, RunError,
};

use dregg_doc::{substrate_commit, AtomId, Author, DocGraph, Patch};

/// The placeholder the runner substitutes with the per-run confined WORK dir in
/// every `argv` element (so the same tokenized argv drives both the L2 run and
/// the L3 re-run — the ephemeral absolute path never leaks into the command and
/// never perturbs `output_digest`).
pub const WORK_TOKEN: &str = "{WORK}";

/// Domain tag for [`confinement_id`] — separates a confinement profile's identity
/// digest from any other bytes.
pub(crate) const CONFINEMENT_DOMAIN: &[u8] = b"forge-ci-runner/confinement/v1";

/// THE CONFINEMENT PROFILE IDENTITY — a stable digest of the sandbox SHAPE + the
/// command it runs, independent of the ephemeral per-run work-dir path.
///
/// It commits: the fixed profile shape (system-reads on, the homebrew prefix, one
/// writable work dir named by the [`WORK_TOKEN`] placeholder — NOT the ephemeral
/// path), the `execve` image, and the tokenized argv. Because the work dir is
/// tokenized, two runs of the same `(image, argv, brew)` in different temp dirs
/// digest to the SAME id — so L3 rebuilds `verdict.confinement_id` from the honest
/// inputs and any mismatch means the verdict was for a different sandbox/command.
pub fn confinement_id(command_image: &str, argv: &[String], homebrew_prefix: &str) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(CONFINEMENT_DOMAIN);
    h.update(b"\0system_reads=1");
    h.update(b"\0brew=");
    h.update(homebrew_prefix.as_bytes());
    h.update(b"\0write=");
    h.update(WORK_TOKEN.as_bytes()); // one writable work dir, tokenized (path-agnostic)
    h.update(b"\0exec=");
    h.update(command_image.as_bytes());
    for a in argv {
        h.update(b"\0arg=");
        h.update(a.as_bytes());
    }
    *h.finalize().as_bytes()
}

/// Project a working tree at `dir` into a [`DocGraph`] and take its REAL substrate
/// commitment ([`dregg_doc::substrate_commit`], the sorted-Poseidon2 heap root) —
/// the [`CiVerdict::input_root`](dregg_doc::CiVerdict::input_root) the forge gate
/// binds to.
///
/// The projection is deterministic: files are collected recursively, sorted by
/// relative path, and each becomes one atom whose content is
/// `"<relpath>\0<blake3-hex of file bytes>"` (chained in sorted order). Distinct
/// trees project to distinct graphs, hence distinct roots. See the crate/module
/// docs for the materialization seam that makes this equal a real PR's
/// `input_root`.
pub fn input_root_of_dir(dir: &std::path::Path) -> std::io::Result<[u8; 32]> {
    Ok(substrate_commit(&doc_graph_of_dir(dir)?))
}

/// The [`DocGraph`] projection of the working tree at `dir` (see
/// [`input_root_of_dir`]).
pub fn doc_graph_of_dir(dir: &std::path::Path) -> std::io::Result<DocGraph> {
    let mut files: Vec<(String, [u8; 32])> = Vec::new();
    collect_files(dir, dir, &mut files)?;
    files.sort_by(|a, b| a.0.cmp(&b.0));

    let mut g = DocGraph::new();
    let mut prev = AtomId::ROOT;
    for (i, (relpath, digest)) in files.iter().enumerate() {
        let content = format!("{relpath}\0{}", hex32(digest));
        let (id, op) = Patch::add(i as u64, &content, prev);
        g = Patch::by(Author(0), [op]).apply_to(&g);
        prev = id;
    }
    Ok(g)
}

/// Recursively collect `(relative-path, blake3-of-content)` for every file under
/// `root`, relative to `base`. Directories are descended in a deterministic order
/// (the final list is sorted by the caller); symlinks are followed as files by
/// `read`.
fn collect_files(
    base: &std::path::Path,
    dir: &std::path::Path,
    out: &mut Vec<(String, [u8; 32])>,
) -> std::io::Result<()> {
    let mut entries: Vec<_> = std::fs::read_dir(dir)?.collect::<Result<_, _>>()?;
    entries.sort_by_key(|e| e.file_name());
    for entry in entries {
        let path = entry.path();
        let ft = entry.file_type()?;
        if ft.is_dir() {
            collect_files(base, &path, out)?;
        } else {
            let bytes = std::fs::read(&path)?;
            let rel = path
                .strip_prefix(base)
                .unwrap_or(&path)
                .to_string_lossy()
                .into_owned();
            out.push((rel, *blake3::hash(&bytes).as_bytes()));
        }
    }
    Ok(())
}

/// Lowercase-hex a 32-byte digest.
fn hex32(b: &[u8; 32]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(64);
    for &x in b {
        s.push(HEX[(x >> 4) as usize] as char);
        s.push(HEX[(x & 0x0f) as usize] as char);
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn input_root_is_deterministic_and_content_sensitive() {
        let a = tempdir("fcr-ir-a");
        let b = tempdir("fcr-ir-b");
        let c = tempdir("fcr-ir-c");
        std::fs::write(a.join("f.txt"), b"hello\n").unwrap();
        std::fs::write(b.join("f.txt"), b"hello\n").unwrap(); // same content
        std::fs::write(c.join("f.txt"), b"HELLO\n").unwrap(); // different content

        let ra = input_root_of_dir(&a).unwrap();
        let rb = input_root_of_dir(&b).unwrap();
        let rc = input_root_of_dir(&c).unwrap();
        assert_eq!(ra, rb, "identical trees → identical input_root");
        assert_ne!(ra, rc, "distinct content → distinct input_root");

        for d in [a, b, c] {
            let _ = std::fs::remove_dir_all(d);
        }
    }

    #[test]
    fn confinement_id_is_path_agnostic_and_command_sensitive() {
        // Same image+argv → same id regardless of temp dir (the WORK token is
        // what the profile commits, not the ephemeral path).
        let id1 = confinement_id("/bin/cat", &["{WORK}/f.txt".into()], "/opt/homebrew");
        let id2 = confinement_id("/bin/cat", &["{WORK}/f.txt".into()], "/opt/homebrew");
        assert_eq!(id1, id2);
        // A different command → a different id.
        let id3 = confinement_id("/bin/echo", &["{WORK}/f.txt".into()], "/opt/homebrew");
        assert_ne!(id1, id3);
    }

    fn tempdir(tag: &str) -> std::path::PathBuf {
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
}
