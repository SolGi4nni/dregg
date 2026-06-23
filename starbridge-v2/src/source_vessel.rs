//! `SourceVessel` — deos as a SELF-DESCRIBING VESSEL.
//!
//! An agent put INTO deos (a Claude logged into the embedded Hermes, or the
//! cockpit itself) can already crawl the RUNTIME — the cells, the caps, the
//! receipts — through the reflective object model. But to understand *what it
//! is*, it needs the SOURCE: the Rust, the Lean (`metatheory/`, esp.
//! `CONSTRUCTIVE-KNOWLEDGE.md` / `DREGG-CALCULUS.md`), the docs that DEFINE the
//! system it is trapped within.
//!
//! This module is the READ surface over a bundled copy of the dregg source. The
//! carrier is a compressed tarball (`dregg-src.tar.zst`, assembled by
//! `scripts/pack-dregg-src.sh` — the source that DEFINES the system, no build
//! artifacts) shipped inside the AppImage at `usr/share/dregg-src/`. A
//! [`SourceVessel`] locates that carrier at runtime, indexes it, and answers
//! reads BY PATH.
//!
//! # Why this is a cap-bounded READ (the ocap shape)
//!
//! A [`SourceVessel`] is a **read capability over the source root, and nothing
//! more**:
//!
//!   * It exposes ONLY [`read`](SourceVessel::read) / [`list`](SourceVessel::list)
//!     / [`contains`](SourceVessel::contains). There is no write/mutate method —
//!     reading the source grants NO write-authority over the live system. An
//!     agent holding a `SourceVessel` can learn what it inhabits; it cannot use
//!     that to change it. The bound is in the TYPE, not a runtime check to forget.
//!   * Every read is CONFINED to the vessel root: a path is normalized and a
//!     `..` escape (or an absolute path reaching outside the source prefix) is
//!     refused. The vessel's authority is exactly "the bundled source, read-only".
//!
//! This is the smallest real thing that lets code inside deos read a source file
//! by path. The richer mount (the source as read-only cells through the SAME
//! [`FirmamentFs`](../../deos-zed/src/fs/firmament.rs) the editor + self-hosting
//! use) builds ON TOP of this reader — see [`seed_into_firmament`] (firmament
//! feature), which seeds the source files as cells WITHOUT granting an edit cap,
//! so they appear in the namespace but a save is refused in-band (read-only).
//!
//! See `docs/deos/SELF-DESCRIBING-VESSEL.md`.

use std::collections::BTreeMap;
use std::io::Read as _;
use std::path::{Component, Path, PathBuf};

use anyhow::{anyhow, bail, Context as _, Result};

/// The top-level prefix the packer lays inside the tarball (`dregg-src/<path>`).
/// We strip it so a vessel read uses the natural repo-relative path
/// (`metatheory/CONSTRUCTIVE-KNOWLEDGE.md`), not the carrier's internal prefix.
const ARCHIVE_PREFIX: &str = "dregg-src/";

/// The bundled carrier's filename (under the AppImage's `usr/share/dregg-src/`).
const ARCHIVE_NAME: &str = "dregg-src.tar.zst";

/// The env override naming the carrier directly — for a dev run, a test, or a
/// non-AppImage layout. Takes precedence over the executable-relative search.
pub const ARCHIVE_ENV: &str = "DREGG_SRC_ARCHIVE";

/// A read-only, in-deos view of the dregg source — the self-describing vessel.
///
/// Holds the decoded source as an in-memory path→bytes index (the carrier is a
/// ~15 MB tarball decompressing to ~77 MB of text; indexing it once is cheap and
/// makes every read a map lookup). The map IS the cap: there is no handle to
/// anything outside it.
pub struct SourceVessel {
    /// repo-relative path → file bytes. The prefix is already stripped.
    entries: BTreeMap<PathBuf, Vec<u8>>,
    /// Where the carrier was found (for provenance / the status line).
    origin: String,
}

impl std::fmt::Debug for SourceVessel {
    /// Concise: the file count + total bytes + origin, NOT the multi-MB entry
    /// bodies (so a `Debug` print / `unwrap_err` message stays small).
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SourceVessel")
            .field("files", &self.entries.len())
            .field("total_bytes", &self.total_bytes())
            .field("origin", &self.origin)
            .finish()
    }
}

impl SourceVessel {
    /// Open the vessel from a `dregg-src.tar.zst` carrier on disk, decoding it
    /// into the in-memory index. The whole bundled source becomes readable by
    /// path through the returned cap.
    pub fn open(archive: &Path) -> Result<Self> {
        let file = std::fs::File::open(archive)
            .with_context(|| format!("opening source carrier {}", archive.display()))?;
        let mut vessel = Self::from_reader(file)
            .with_context(|| format!("decoding source carrier {}", archive.display()))?;
        vessel.origin = archive.display().to_string();
        Ok(vessel)
    }

    /// Open the vessel by FINDING the carrier at runtime, in order:
    ///   1. `$DREGG_SRC_ARCHIVE` if set (a dev/test/explicit override).
    ///   2. Next to the executable, the AppImage layout: `<exe_dir>/../share/
    ///      dregg-src/dregg-src.tar.zst` (AppDir/usr/bin → AppDir/usr/share), and
    ///      a couple of sibling fallbacks (`<exe_dir>/dregg-src.tar.zst`,
    ///      `<exe_dir>/share/dregg-src/...`).
    ///
    /// Returns the first that exists. `Err` (with the searched paths) if none is
    /// present — the honest "this build did not ship the source" signal, never a
    /// silent empty vessel.
    pub fn discover() -> Result<Self> {
        let mut tried: Vec<PathBuf> = Vec::new();

        if let Ok(p) = std::env::var(ARCHIVE_ENV) {
            let path = PathBuf::from(&p);
            if path.is_file() {
                return Self::open(&path);
            }
            tried.push(path);
        }

        for cand in Self::executable_relative_candidates() {
            if cand.is_file() {
                return Self::open(&cand);
            }
            tried.push(cand);
        }

        bail!(
            "no dregg source carrier ({ARCHIVE_NAME}) found — this build did not ship \
             the self-describing source vessel. Searched: {tried:?}. Set \
             ${ARCHIVE_ENV} to a carrier, or run scripts/pack-dregg-src.sh and \
             place it under usr/share/dregg-src/."
        )
    }

    /// The executable-relative carrier locations to probe (AppImage + siblings).
    fn executable_relative_candidates() -> Vec<PathBuf> {
        let mut out = Vec::new();
        if let Ok(exe) = std::env::current_exe() {
            if let Some(dir) = exe.parent() {
                // AppImage: AppDir/usr/bin/starbridge-v2 → AppDir/usr/share/dregg-src/
                out.push(dir.join("../share/dregg-src").join(ARCHIVE_NAME));
                // sibling share dir
                out.push(dir.join("share/dregg-src").join(ARCHIVE_NAME));
                // right next to the binary
                out.push(dir.join(ARCHIVE_NAME));
            }
        }
        out
    }

    /// Decode a vessel directly from a carrier byte stream (a `dregg-src.tar.zst`
    /// reader). Used by [`open`](Self::open) and by tests that feed an in-memory
    /// carrier. The entries are indexed with the `dregg-src/` prefix stripped.
    pub fn from_reader<R: std::io::Read>(reader: R) -> Result<Self> {
        let decoder = zstd::stream::read::Decoder::new(reader)
            .context("initializing zstd decoder for the source carrier")?;
        let mut archive = tar::Archive::new(decoder);
        let mut entries = BTreeMap::new();
        for entry in archive.entries().context("reading tar entries")? {
            let mut entry = entry.context("reading a tar entry")?;
            let header = entry.header();
            if !header.entry_type().is_file() {
                continue;
            }
            let raw = entry.path().context("decoding a tar entry path")?.into_owned();
            // Strip the `dregg-src/` carrier prefix → the natural repo path.
            let rel = match raw.strip_prefix(ARCHIVE_PREFIX) {
                Ok(p) => p.to_path_buf(),
                Err(_) => raw,
            };
            let mut bytes = Vec::with_capacity(header.size().unwrap_or(0) as usize);
            entry.read_to_end(&mut bytes).context("reading a tar entry body")?;
            entries.insert(rel, bytes);
        }
        if entries.is_empty() {
            bail!("source carrier decoded to ZERO files — the vessel would be empty");
        }
        Ok(SourceVessel { entries, origin: "<reader>".to_string() })
    }

    /// Normalize a requested path INTO the vessel root, refusing any escape. A
    /// leading `/` is stripped (the vessel root is the repo root); `.` is dropped;
    /// a `..` that would climb above the root is REFUSED (the cap confinement).
    /// Returns the canonical repo-relative key used in the index.
    fn confine(path: &Path) -> Result<PathBuf> {
        let mut out = PathBuf::new();
        for comp in path.components() {
            match comp {
                Component::Prefix(_) | Component::RootDir => { /* anchor to root */ }
                Component::CurDir => {}
                Component::ParentDir => {
                    if !out.pop() {
                        bail!(
                            "path {} escapes the source vessel root (a `..` above the \
                             bundled source is refused — the vessel is a confined read cap)",
                            path.display()
                        );
                    }
                }
                Component::Normal(seg) => out.push(seg),
            }
        }
        Ok(out)
    }

    /// **Read a source file BY PATH** — the cap-bounded read. `path` is repo-
    /// relative (e.g. `metatheory/CONSTRUCTIVE-KNOWLEDGE.md` or
    /// `dregg-lean-ffi/src/lib.rs`); a leading `/` is fine (anchored to the root).
    /// Returns the file's real content as UTF-8. A path outside the vessel is
    /// refused; an absent path errors. NO write counterpart exists.
    pub fn read(&self, path: impl AsRef<Path>) -> Result<String> {
        let bytes = self.read_bytes(path)?;
        String::from_utf8(bytes).context("source file is not valid UTF-8")
    }

    /// Read a source file's raw bytes by path (the byte-exact cap read).
    pub fn read_bytes(&self, path: impl AsRef<Path>) -> Result<Vec<u8>> {
        let key = Self::confine(path.as_ref())?;
        self.entries
            .get(&key)
            .cloned()
            .ok_or_else(|| anyhow!("no source file at {} in the vessel", key.display()))
    }

    /// Whether the vessel carries a file at `path` (cap-confined).
    pub fn contains(&self, path: impl AsRef<Path>) -> bool {
        match Self::confine(path.as_ref()) {
            Ok(key) => self.entries.contains_key(&key),
            Err(_) => false,
        }
    }

    /// List every source path the vessel carries (repo-relative, sorted). The
    /// agent's table of contents over what it can read.
    pub fn list(&self) -> Vec<PathBuf> {
        self.entries.keys().cloned().collect()
    }

    /// List the source paths under `dir` (a repo-relative directory prefix). With
    /// an empty path this is the whole vessel.
    pub fn list_under(&self, dir: impl AsRef<Path>) -> Result<Vec<PathBuf>> {
        let prefix = Self::confine(dir.as_ref())?;
        Ok(self
            .entries
            .keys()
            .filter(|p| prefix.as_os_str().is_empty() || p.starts_with(&prefix))
            .cloned()
            .collect())
    }

    /// The number of source files in the vessel.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the vessel is empty (never, post-construction — `from_reader`
    /// refuses an empty carrier; kept for the clippy `len`-without-`is_empty` lint).
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Where the carrier was found — provenance for the status line / a log line
    /// ("reading my own source from <origin>").
    pub fn origin(&self) -> &str {
        &self.origin
    }

    /// The total uncompressed source bytes the vessel holds (the size of the
    /// system's definition the agent can read).
    pub fn total_bytes(&self) -> usize {
        self.entries.values().map(|b| b.len()).sum()
    }
}

/// **Seed the bundled source into a [`FirmamentFs`] as READ-ONLY cells** — the
/// "source appears as cells/files through the SAME FirmamentFs the editor uses"
/// path. Each source file becomes a file cell in the namespace under
/// `mount_root` (e.g. `/dregg-src`), seeded with its content as genesis state —
/// but, crucially, this uses [`FirmamentFs::seed_file`], and the vessel grants NO
/// EDIT CAP beyond what seeding implies; the caller treats the mount as read-only
/// (a save would be refused in-band by the cross-cell cap gate were the cap
/// withheld — see `firmament.rs`'s `save_without_the_edit_cap_is_refused_in_band`).
///
/// Returns the number of source cells seeded. The host can then [`Fs::load`] any
/// source path and get its real content from a SOVEREIGN CELL — the source is now
/// part of the same reflective image the cockpit inspects.
///
/// `limit` caps how many files are seeded (the full 3.6k-file source would mint
/// 3.6k cells; a caller usually seeds a focused subtree — pass `None` for all).
#[cfg(feature = "firmament")]
pub fn seed_into_firmament(
    vessel: &SourceVessel,
    fs: &deos_zed::fs::firmament::FirmamentFs,
    mount_root: &Path,
    subtree: Option<&Path>,
    limit: Option<usize>,
) -> Result<usize> {
    let paths = match subtree {
        Some(s) => vessel.list_under(s)?,
        None => vessel.list(),
    };
    let mut seeded = 0usize;
    for rel in paths {
        if let Some(max) = limit {
            if seeded >= max {
                break;
            }
        }
        let content = match vessel.read(&rel) {
            Ok(c) => c,
            Err(_) => continue, // skip non-UTF-8 (there are none in the source set)
        };
        let mount = mount_root.join(&rel);
        fs.seed_file(mount, &content)
            .with_context(|| format!("seeding source cell for {}", rel.display()))?;
        seeded += 1;
    }
    Ok(seeded)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write as _;

    /// Build an in-memory `dregg-src.tar.zst` carrier from `(path, content)`
    /// pairs, exactly as `scripts/pack-dregg-src.sh` does (the `dregg-src/`
    /// prefix included). Returns the carrier bytes.
    fn make_carrier(files: &[(&str, &str)]) -> Vec<u8> {
        let mut tar_buf = Vec::new();
        {
            let mut builder = tar::Builder::new(&mut tar_buf);
            for (path, content) in files {
                let bytes = content.as_bytes();
                let mut header = tar::Header::new_gnu();
                header.set_size(bytes.len() as u64);
                header.set_mode(0o644);
                header.set_cksum();
                let full = format!("{ARCHIVE_PREFIX}{path}");
                builder.append_data(&mut header, full, bytes).unwrap();
            }
            builder.finish().unwrap();
        }
        let mut packed = Vec::new();
        let mut enc = zstd::stream::write::Encoder::new(&mut packed, 3).unwrap();
        enc.write_all(&tar_buf).unwrap();
        enc.finish().unwrap();
        packed
    }

    #[test]
    fn vessel_reads_a_source_file_by_path_from_within() {
        // The vessel carries a real-shaped source file; the agent reads it back
        // BY PATH and gets the exact content — deos describing itself.
        let ck = "# dregg, as a metatheory of constructive knowledge\n\nauthority = PRODUCTION.\n";
        let lib = "//! dregg-lean-ffi — the verified Lean bridge.\npub fn lean_available() -> bool { true }\n";
        let carrier = make_carrier(&[
            ("metatheory/CONSTRUCTIVE-KNOWLEDGE.md", ck),
            ("dregg-lean-ffi/src/lib.rs", lib),
        ]);

        let vessel = SourceVessel::from_reader(&carrier[..]).unwrap();
        assert_eq!(vessel.len(), 2);

        // THE PROOF: a source file is readable from within by path.
        assert_eq!(
            vessel.read("metatheory/CONSTRUCTIVE-KNOWLEDGE.md").unwrap(),
            ck,
            "the agent reads the metatheory source it inhabits"
        );
        assert_eq!(vessel.read("dregg-lean-ffi/src/lib.rs").unwrap(), lib);
        // A leading slash is anchored to the root (the same file).
        assert_eq!(vessel.read("/dregg-lean-ffi/src/lib.rs").unwrap(), lib);
        assert!(vessel.contains("metatheory/CONSTRUCTIVE-KNOWLEDGE.md"));
        assert!(!vessel.contains("does/not/exist.rs"));
    }

    #[test]
    fn vessel_is_a_confined_read_cap_no_escape() {
        let carrier = make_carrier(&[("a/b.rs", "x")]);
        let vessel = SourceVessel::from_reader(&carrier[..]).unwrap();
        // A `..` climbing above the root is refused (the cap confinement).
        let err = vessel.read("../../etc/passwd").unwrap_err();
        assert!(
            err.to_string().contains("escapes the source vessel root"),
            "a `..` escape must be refused: {err}"
        );
        // An absolute path reaching outside is anchored to the root, not the FS:
        // `/a/b.rs` reads the bundled file, not a host `/a/b.rs`.
        assert_eq!(vessel.read("/a/b.rs").unwrap(), "x");
    }

    #[test]
    fn vessel_lists_its_contents_and_subtrees() {
        let carrier = make_carrier(&[
            ("metatheory/A.lean", "a"),
            ("metatheory/B.lean", "b"),
            ("cell/src/lib.rs", "c"),
        ]);
        let vessel = SourceVessel::from_reader(&carrier[..]).unwrap();
        assert_eq!(vessel.list().len(), 3);
        let meta = vessel.list_under("metatheory").unwrap();
        assert_eq!(meta.len(), 2, "two files under metatheory/");
        assert!(meta.iter().all(|p| p.starts_with("metatheory")));
        assert_eq!(vessel.total_bytes(), 3);
    }

    #[test]
    fn empty_carrier_is_refused() {
        let carrier = make_carrier(&[]);
        let err = SourceVessel::from_reader(&carrier[..]).unwrap_err();
        assert!(err.to_string().contains("ZERO files"));
    }
}
