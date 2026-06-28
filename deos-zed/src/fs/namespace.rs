//! `DirNamespace` — the firmament path → cell namespace, backed by `rbg`'s
//! capability-secure [`DirectoryCell`](dregg_rbg::DirectoryCell) (the Robigalia
//! VFS heritage) rather than a flat `BTreeMap<PathBuf, CellId>`.
//!
//! # Why this, and not a flat map
//!
//! The first-slice namespace was a single flat `BTreeMap<PathBuf, CellId>` — it
//! worked, but it threw away everything a *directory* is. A `DirectoryCell` is a
//! real capability:
//!
//! * **Recursive scoping.** A path is resolved component-by-component through a
//!   chain of `DirectoryCell`s; a directory contains directories. The root
//!   directory cell IS the editor's mount point — the editor can only see and
//!   edit what that cap reaches.
//! * **Capability-scoped listing.** `read_dir` is `DirectoryCell::list(caller)`:
//!   holding the directory cap (membership) *is* the authority to enumerate it. A
//!   non-member is refused — listing is no longer ambient.
//! * **`dregg://` sturdy refs.** Every entry carries a
//!   [`SturdyRef`](dregg_rbg::SturdyRef) = `(federation, cell, swiss)`. So a path
//!   does not resolve to a bare local `CellId` — it resolves to a *portable,
//!   cross-federation capability URI* a remote node could enliven. This is the
//!   distribution foundation: a file is reachable by any holder of its sturdy
//!   ref, not just this process.
//! * **Versioned CAS = decentralized coordination.** `swap(name, expected_ver,
//!   …)` is an atomic compare-and-swap; a stale writer gets `VersionConflict`.
//!   Two editors racing to bind the same name coordinate through the version,
//!   exactly as two nodes would.
//!
//! The file *content* still lives in a file cell on the verified spine (a save is
//! still a receipted turn over that cell — see [`super::firmament`]). This module
//! owns only the *name → cell* mapping: the directory tree whose leaves point at
//! those file cells.

use std::collections::HashSet;
use std::path::{Component, Path, PathBuf};

use anyhow::{anyhow, bail, Result};
use dregg_rbg::{DirectoryCell, DirectoryEntry, DirectoryError, EntryKind, MemberId, SturdyRef};
use dregg_types::{CellId, FederationId};

/// The federation the headless / per-editor [`OwnedSpine`](super::firmament) path
/// scopes its directories to. A host (e.g. starbridge-v2's `World`) mounts in its
/// OWN federation via [`DirNamespace::new`]; this is the self-contained default.
pub const DEOS_ZED_FEDERATION: FederationId = FederationId([0xF0; 32]);

/// Map a [`DirectoryError`] into an `anyhow::Error` (it is `Display`/`Error`, but
/// `anyhow` cannot auto-convert a non-`'static`-bounded foreign error uniformly
/// here, so we render it).
fn de(e: DirectoryError) -> anyhow::Error {
    anyhow!("directory: {e}")
}

/// A path → cell namespace as a tree of capability-secure `DirectoryCell`s.
///
/// Holds the directory cells (the root + every sub-directory) keyed by cell id,
/// plus the editor's [`MemberId`] — the single authority that lists/gets/swaps
/// (the cap that reaches the mounted tree). File *content* lives elsewhere (on
/// the verified spine); a leaf entry's [`SturdyRef`] points at the file cell.
pub struct DirNamespace {
    /// Every directory cell in the tree, keyed by its own cell id. The root is
    /// `root`; sub-directories are reached by walking entries of kind
    /// [`EntryKind::SubDirectory`].
    dirs: std::collections::BTreeMap<CellId, DirectoryCell>,
    /// The root directory cell id — the editor's mount point.
    root: CellId,
    /// The federation these directories (and their sturdy refs) are scoped to.
    federation: FederationId,
    /// The editor's member id — the caller for every directory op. It is a member
    /// of every directory created here, so its cap reaches the whole tree.
    editor: MemberId,
    /// Monotonic counter for minting fresh sub-directory cell ids.
    next_dir: u32,
}

impl DirNamespace {
    /// A fresh namespace: an empty root directory cell in `federation`, with
    /// `editor` as its sole (founding) member. Seed files with
    /// [`DirNamespace::bind`].
    pub fn new(federation: FederationId, editor: MemberId) -> Self {
        let root = Self::dir_id(0);
        let members: HashSet<MemberId> = std::iter::once(editor).collect();
        let root_cell = DirectoryCell::new(root, federation, members, 0);
        let mut dirs = std::collections::BTreeMap::new();
        dirs.insert(root, root_cell);
        DirNamespace {
            dirs,
            root,
            federation,
            editor,
            next_dir: 1,
        }
    }

    /// The federation these directories are scoped to.
    pub fn federation(&self) -> FederationId {
        self.federation
    }

    /// The root directory cell id (the editor's mount point / cap root).
    pub fn root(&self) -> CellId {
        self.root
    }

    // --- id minting ---------------------------------------------------------

    /// A directory cell id, domain-tagged `0xD?` so it can never collide with a
    /// file cell (`0xF1` at byte 4) or the editor cell (`0xED` at byte 0).
    fn dir_id(counter: u32) -> CellId {
        let mut b = [0u8; 32];
        b[0..4].copy_from_slice(&counter.to_le_bytes());
        b[4] = 0xD0; // domain tag: directory
        CellId(b)
    }

    fn fresh_dir_id(&mut self) -> CellId {
        let id = Self::dir_id(self.next_dir);
        self.next_dir += 1;
        id
    }

    /// The sturdy-ref swiss number for a file leaf. Deterministically derived from
    /// the file cell id (in-process the swiss is not a secret; a host wiring real
    /// cross-federation enlivening replaces this with the cell's true swiss).
    fn file_swiss(file: CellId) -> [u8; 32] {
        file.0
    }

    // --- path decomposition -------------------------------------------------

    /// Split a path into its `Normal` components, rejecting `..` (no escaping the
    /// mount) and ignoring the leading `/` and any `.`.
    fn components(path: &Path) -> Result<Vec<String>> {
        let mut out = Vec::new();
        for c in path.components() {
            match c {
                Component::RootDir | Component::Prefix(_) | Component::CurDir => {}
                Component::ParentDir => bail!("'..' is not allowed in a firmament path"),
                Component::Normal(s) => out.push(
                    s.to_str()
                        .ok_or_else(|| anyhow!("non-UTF-8 path component"))?
                        .to_string(),
                ),
            }
        }
        Ok(out)
    }

    // --- resolution ---------------------------------------------------------

    /// Resolve a path to its directory cell id (the dir AT `path`). The root path
    /// (`/`) resolves to the root cell. Each component must be a sub-directory.
    fn resolve_dir(&self, comps: &[String]) -> Result<CellId> {
        let mut cur = self.root;
        for name in comps {
            let dir = self
                .dirs
                .get(&cur)
                .ok_or_else(|| anyhow!("directory cell {:02x?}… vanished", &cur.0[..2]))?;
            let entry = dir.get(self.editor, name).map_err(de)?;
            if entry.kind != EntryKind::SubDirectory {
                bail!("'{name}' is a file, not a directory");
            }
            cur = entry.sturdy_ref.cell_id;
        }
        Ok(cur)
    }

    /// Resolve a path to the file cell id its leaf entry points at.
    pub fn resolve_file(&self, path: &Path) -> Result<CellId> {
        let comps = Self::components(path)?;
        let (name, dirs) = comps
            .split_last()
            .ok_or_else(|| anyhow!("the root path is a directory, not a file"))?;
        let dir_id = self.resolve_dir(dirs)?;
        let dir = self
            .dirs
            .get(&dir_id)
            .ok_or_else(|| anyhow!("directory cell vanished"))?;
        let entry = dir.get(self.editor, name).map_err(de)?;
        if entry.kind == EntryKind::SubDirectory {
            bail!("'{}' is a directory, not a file", path.display());
        }
        Ok(entry.sturdy_ref.cell_id)
    }

    /// `true` if `path` resolves to a directory in the tree (root included).
    pub fn is_dir(&self, path: &Path) -> bool {
        match Self::components(path) {
            Ok(comps) => self.resolve_dir(&comps).is_ok(),
            Err(_) => false,
        }
    }

    /// The [`SturdyRef`] (the `dregg://` capability URI: federation + cell +
    /// swiss) a file path resolves to — the portable, cross-federation handle to
    /// the file. A remote holder of this ref can enliven the same file.
    pub fn sturdy_ref(&self, path: &Path) -> Result<SturdyRef> {
        let comps = Self::components(path)?;
        let (name, dirs) = comps
            .split_last()
            .ok_or_else(|| anyhow!("the root path has no sturdy ref"))?;
        let dir_id = self.resolve_dir(dirs)?;
        let dir = self
            .dirs
            .get(&dir_id)
            .ok_or_else(|| anyhow!("dir vanished"))?;
        let entry = dir.get(self.editor, name).map_err(de)?;
        Ok(entry.sturdy_ref.clone())
    }

    // --- mutation -----------------------------------------------------------

    /// Ensure a sub-directory `name` exists under `parent`, creating it (and
    /// registering it in `parent`) if absent. Returns the sub-directory cell id.
    /// Errors if `name` already exists as a *file*.
    fn ensure_subdir(&mut self, parent: CellId, name: &str) -> Result<CellId> {
        // Probe (immutable) first.
        let existing = {
            let dir = self
                .dirs
                .get(&parent)
                .ok_or_else(|| anyhow!("parent directory vanished"))?;
            match dir.get(self.editor, name) {
                Ok(entry) => Some(entry.clone()),
                Err(DirectoryError::NotFound { .. }) => None,
                Err(e) => return Err(de(e)),
            }
        };
        if let Some(entry) = existing {
            if entry.kind != EntryKind::SubDirectory {
                bail!("'{name}' already exists as a file, not a directory");
            }
            return Ok(entry.sturdy_ref.cell_id);
        }
        // Create the sub-directory cell and register it in the parent.
        let sub_id = self.fresh_dir_id();
        let members: HashSet<MemberId> = std::iter::once(self.editor).collect();
        let sub = DirectoryCell::new(sub_id, self.federation, members, 0);
        self.dirs.insert(sub_id, sub);
        let sref = SturdyRef {
            federation_id: self.federation,
            cell_id: sub_id,
            swiss: sub_id.0,
        };
        let parent_dir = self
            .dirs
            .get_mut(&parent)
            .ok_or_else(|| anyhow!("parent directory vanished"))?;
        parent_dir
            .register_subdirectory(self.editor, name, sref, None, 0)
            .map_err(de)?;
        Ok(sub_id)
    }

    /// Bind `path` to the file cell `file`, creating intermediate directories as
    /// needed. The leaf entry is an [`EntryKind::Capability`] whose sturdy ref
    /// points at `file`. This is an atomic insert (CAS at version 0): binding a
    /// name that already exists is a [`DirectoryError::VersionConflict`], surfaced
    /// as an error — the decentralized-coordination tooth (a second writer racing
    /// the same name loses the CAS).
    pub fn bind(&mut self, path: &Path, file: CellId) -> Result<()> {
        let comps = Self::components(path)?;
        let (name, dirs) = comps
            .split_last()
            .ok_or_else(|| anyhow!("cannot bind the root path to a file"))?;
        let mut cur = self.root;
        for d in dirs {
            cur = self.ensure_subdir(cur, d)?;
        }
        let entry = DirectoryEntry {
            sturdy_ref: SturdyRef {
                federation_id: self.federation,
                cell_id: file,
                swiss: Self::file_swiss(file),
            },
            version: 0,
            kind: EntryKind::Capability,
            description: None,
            tags: vec!["file".to_string()],
            registered_at: 0,
            expires_at: None,
        };
        let dir = self
            .dirs
            .get_mut(&cur)
            .ok_or_else(|| anyhow!("directory vanished"))?;
        dir.swap(self.editor, name, 0, Some(entry)).map_err(de)?;
        Ok(())
    }

    // --- listing ------------------------------------------------------------

    /// The immediate children of the directory at `path`: `(name, is_dir)` pairs,
    /// in name order. This is `DirectoryCell::list(editor)` — capability-scoped
    /// (a non-member caller would be refused; here the editor always holds the
    /// cap). Errors if `path` is not a directory.
    pub fn list_children(&self, path: &Path) -> Result<Vec<(String, bool)>> {
        let comps = Self::components(path)?;
        let dir_id = self.resolve_dir(&comps)?;
        let dir = self
            .dirs
            .get(&dir_id)
            .ok_or_else(|| anyhow!("directory vanished"))?;
        let listing = dir.list(self.editor).map_err(de)?;
        Ok(listing
            .entries
            .into_iter()
            .map(|(name, entry)| (name, entry.kind == EntryKind::SubDirectory))
            .collect())
    }

    /// Every file in the tree as `(absolute path, file cell id)` pairs. A
    /// depth-first walk over the directory cells. Used to backfill the disk
    /// mirror.
    pub fn all_files(&self) -> Result<Vec<(PathBuf, CellId)>> {
        let mut out = Vec::new();
        self.collect(self.root, &PathBuf::from("/"), &mut out)?;
        Ok(out)
    }

    fn collect(
        &self,
        dir_id: CellId,
        prefix: &Path,
        out: &mut Vec<(PathBuf, CellId)>,
    ) -> Result<()> {
        let dir = self
            .dirs
            .get(&dir_id)
            .ok_or_else(|| anyhow!("directory vanished"))?;
        let listing = dir.list(self.editor).map_err(de)?;
        for (name, entry) in listing.entries {
            let p = prefix.join(&name);
            if entry.kind == EntryKind::SubDirectory {
                self.collect(entry.sturdy_ref.cell_id, &p, out)?;
            } else {
                out.push((p, entry.sturdy_ref.cell_id));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ns() -> DirNamespace {
        DirNamespace::new(DEOS_ZED_FEDERATION, MemberId([0xED; 32]))
    }

    fn file(seed: u8) -> CellId {
        let mut b = [0u8; 32];
        b[0] = seed;
        b[4] = 0xF1;
        CellId(b)
    }

    #[test]
    fn binds_and_resolves_through_a_directory_chain() {
        let mut ns = ns();
        let f = file(1);
        ns.bind(Path::new("/proj/src/main.rs"), f).unwrap();
        assert_eq!(ns.resolve_file(Path::new("/proj/src/main.rs")).unwrap(), f);
        // The intermediate directories are REAL DirectoryCells, recursively scoped.
        assert!(ns.is_dir(Path::new("/proj")));
        assert!(ns.is_dir(Path::new("/proj/src")));
        assert!(ns.is_dir(Path::new("/"))); // the mount root
        assert!(!ns.is_dir(Path::new("/proj/src/main.rs")));
    }

    #[test]
    fn list_children_is_capability_scoped_listing() {
        let mut ns = ns();
        ns.bind(Path::new("/proj/a.rs"), file(1)).unwrap();
        ns.bind(Path::new("/proj/b.rs"), file(2)).unwrap();
        ns.bind(Path::new("/proj/sub/c.rs"), file(3)).unwrap();
        let mut kids = ns.list_children(Path::new("/proj")).unwrap();
        kids.sort();
        assert_eq!(
            kids,
            vec![
                ("a.rs".to_string(), false),
                ("b.rs".to_string(), false),
                ("sub".to_string(), true),
            ]
        );
    }

    #[test]
    fn a_path_resolves_to_a_portable_cross_federation_sturdy_ref() {
        // The distribution payoff: a file path resolves NOT to a bare local cell
        // id but to a dregg:// sturdy ref (federation + cell + swiss) — the
        // portable capability a remote node enlivens. The leaf ref's cell is the
        // file cell; its federation is the mount's federation.
        let mut ns = ns();
        let f = file(7);
        ns.bind(Path::new("/proj/x.rs"), f).unwrap();
        let sref = ns.sturdy_ref(Path::new("/proj/x.rs")).unwrap();
        assert_eq!(sref.cell_id, f, "the ref points at the file cell");
        assert_eq!(
            sref.federation_id, DEOS_ZED_FEDERATION,
            "scoped to the mount"
        );
        assert_eq!(sref.swiss, f.0, "the bearer secret is derived in-process");
    }

    #[test]
    fn rebinding_a_name_loses_the_cas_decentralized_coordination() {
        // Versioned CAS is the coordination tooth: a second writer binding an
        // already-bound name loses (VersionConflict surfaced as an error), exactly
        // as two racing nodes would coordinate through the version.
        let mut ns = ns();
        ns.bind(Path::new("/proj/x.rs"), file(1)).unwrap();
        let err = ns.bind(Path::new("/proj/x.rs"), file(2)).unwrap_err();
        assert!(
            err.to_string().contains("conflict"),
            "a CAS race on the same name is refused: {err}"
        );
        // The original binding is intact.
        assert_eq!(ns.resolve_file(Path::new("/proj/x.rs")).unwrap(), file(1));
    }

    #[test]
    fn a_file_in_the_path_is_not_a_directory() {
        let mut ns = ns();
        ns.bind(Path::new("/proj/x.rs"), file(1)).unwrap();
        // Trying to bind UNDER a file path must fail (x.rs is a file, not a dir).
        let err = ns
            .bind(Path::new("/proj/x.rs/inner.rs"), file(2))
            .unwrap_err();
        assert!(err.to_string().contains("file"), "got: {err}");
    }

    #[test]
    fn parent_dir_escape_is_rejected() {
        let mut ns = ns();
        let err = ns
            .bind(Path::new("/proj/../escape.rs"), file(1))
            .unwrap_err();
        assert!(err.to_string().contains(".."), "got: {err}");
    }

    #[test]
    fn all_files_walks_the_whole_tree() {
        let mut ns = ns();
        ns.bind(Path::new("/a.rs"), file(1)).unwrap();
        ns.bind(Path::new("/proj/b.rs"), file(2)).unwrap();
        ns.bind(Path::new("/proj/sub/c.rs"), file(3)).unwrap();
        let mut all = ns.all_files().unwrap();
        all.sort();
        assert_eq!(
            all,
            vec![
                (PathBuf::from("/a.rs"), file(1)),
                (PathBuf::from("/proj/b.rs"), file(2)),
                (PathBuf::from("/proj/sub/c.rs"), file(3)),
            ]
        );
    }
}
