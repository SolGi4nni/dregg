//! `FirmamentFs` — the firmament-backed [`Fs`](super::Fs) impl: a file IS a cell,
//! a SAVE IS a receipted dregg turn.
//!
//! This is the deos-integration payoff: an editor whose every file operation is a
//! capability-checked, receipted operation over sovereign cells — NOT raw
//! `std::fs`. Because the editor only ever speaks the [`Fs`](super::Fs) trait,
//! turning the editor "firmament-backed" is exactly this one impl. No editor or
//! file-tree code changes.
//!
//! # The mapping (path → cell, save → receipted turn)
//!
//! | `Fs` method     | firmament realization                                              |
//! |-----------------|--------------------------------------------------------------------|
//! | `load(path)`    | resolve `path` → the file-cell via the path namespace; read the    |
//! |                 | cell's content substance (the committed `fields_map`, decoded). A   |
//! |                 | read is authority-checked but does not mutate state — no turn.      |
//! | `save(path, c)` | a dregg TURN: a cap-gated `SetField` write over the file-cell's     |
//! |                 | content, driven through the REAL `TurnExecutor`, leaving a verifiable|
//! |                 | RECEIPT. "Save" becomes an attestable event, not an opaque syscall. |
//! | `read_dir(p)`   | list the namespace's entries under `p` (the directory cell).        |
//! | `metadata(p)`   | resolve the path → file-cell or directory; report kind + length.    |
//!
//! # Why this used to be a stub
//!
//! Wiring it needs a live executor handle + a mounted root namespace. The
//! constructor took those as opaque `()` placeholders. They are now real: this
//! module owns an in-process [`Ledger`] + [`TurnExecutor`] (the SAME verified
//! spine starbridge-v2's `World` wraps), seeds an editor (author) cell + a root
//! directory cell, and resolves paths to file cells under it. The host (a deos
//! image) can hand a `FirmamentFs` to `EditorPane::new` and the editor edits
//! cells, with receipted saves, instead of disk — and nothing in the editor or
//! file tree changes.

#[cfg(not(feature = "firmament"))]
mod stub {
    use std::path::Path;

    use anyhow::{bail, Result};

    use crate::fs::{DirEntry, Fs, Metadata};

    /// The firmament-backed filesystem (STUB build — the `firmament` feature is
    /// off). Satisfies the [`Fs`](crate::fs::Fs) trait so it is a drop-in
    /// replacement for `RealFs` the moment the feature is enabled, but every
    /// method returns a clear "not built with `firmament`" error. Build with
    /// `--features firmament` for the live cell-backed impl.
    pub struct FirmamentFs {
        _private: (),
    }

    impl FirmamentFs {
        /// Build a firmament fs. In the stub build this constructs successfully
        /// but every operation errors — enable the `firmament` feature for the
        /// real cell-backed impl.
        pub fn new() -> Self {
            FirmamentFs { _private: () }
        }

        fn not_built<T>(what: &str) -> Result<T> {
            bail!(
                "FirmamentFs::{what} needs the `firmament` feature: rebuild deos-zed \
                 with `--features firmament` for the live cell-backed impl (a file is a \
                 cell, a save is a receipted turn). See src/fs/firmament.rs."
            )
        }
    }

    impl Default for FirmamentFs {
        fn default() -> Self {
            Self::new()
        }
    }

    impl Fs for FirmamentFs {
        fn load(&self, _path: &Path) -> Result<String> {
            Self::not_built("load")
        }
        fn save(&self, _path: &Path, _content: &str) -> Result<()> {
            Self::not_built("save")
        }
        fn read_dir(&self, _path: &Path) -> Result<Vec<DirEntry>> {
            Self::not_built("read_dir")
        }
        fn metadata(&self, _path: &Path) -> Result<Metadata> {
            Self::not_built("metadata")
        }
        fn backend_label(&self) -> &'static str {
            "FirmamentFs (build with --features firmament) — STUB"
        }
    }
}

#[cfg(not(feature = "firmament"))]
pub use stub::FirmamentFs;

#[cfg(feature = "firmament")]
mod live {
    use std::collections::BTreeMap;
    use std::path::{Path, PathBuf};
    use std::sync::Mutex;

    use anyhow::{anyhow, bail, Context as _, Result};

    use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions, STATE_SLOTS};
    use dregg_turn::{
        ActionBuilder, ComputronCosts, Effect, TurnBuilder, TurnExecutor, TurnReceipt, TurnResult,
    };

    use crate::fs::{DirEntry, Fs, Metadata};

    // --- content <-> field-element encoding -----------------------------------
    //
    // A file's content is a UTF-8 String — many bytes. The cell's committed
    // `fields_map` stores `u64 -> FieldElement` ([u8; 32]) entries, written by
    // the executor's `set_field_ext` arm for any key >= STATE_SLOTS (the same
    // overflow map dregg-doc's ExecutorDrivenDoc lays its projection into). We
    // lay the content into that map:
    //   * key LEN_KEY        = the byte length, little-endian in the first 8 bytes.
    //   * keys CHUNK_BASE+i  = the i-th 32-byte chunk of the content bytes.
    // so the file cell's `fields_root` (which the canonical state commitment
    // absorbs) commits to exactly this content. load() decodes it back; a light
    // client trusts the SAME root the executor moved on save.

    /// The committed-map key holding the content byte length. Lifted past the 16
    /// fixed register slots so it lands in `fields_map` (not the fixed `fields[]`).
    const LEN_KEY: u64 = STATE_SLOTS as u64;
    /// The first committed-map key holding a content chunk. Subsequent chunks are
    /// `CHUNK_BASE + i`.
    const CHUNK_BASE: u64 = STATE_SLOTS as u64 + 1;
    /// Bytes per field element.
    const CHUNK: usize = 32;

    /// The number of chunk fields a content of `len` bytes occupies.
    fn chunk_count(len: usize) -> usize {
        len.div_ceil(CHUNK)
    }

    /// Decode a file cell's committed `fields_map` back into the content String.
    fn decode_content(cell: &Cell) -> Result<String> {
        let len_felt = cell
            .state
            .get_field_ext(LEN_KEY)
            .ok_or_else(|| anyhow!("file cell holds no content (no length field)"))?;
        let len = u64::from_le_bytes(len_felt[0..8].try_into().unwrap()) as usize;
        let mut bytes = Vec::with_capacity(len);
        for i in 0..chunk_count(len) {
            let felt = cell
                .state
                .get_field_ext(CHUNK_BASE + i as u64)
                .ok_or_else(|| anyhow!("file cell is missing content chunk {i}"))?;
            bytes.extend_from_slice(&felt);
        }
        bytes.truncate(len);
        String::from_utf8(bytes).context("file cell content is not valid UTF-8")
    }

    /// Build the `SetField` effects that write `content` into the file cell,
    /// REPLACING whatever is there. Returns the writes (length + chunks) plus the
    /// zeroing writes for any stale chunks the cell still holds beyond the new
    /// content (so a shrink genuinely vacates the old tail — the commitment binds
    /// only the live content).
    fn content_write_effects(cell: &Cell, file: CellId, content: &str) -> Vec<Effect> {
        let bytes = content.as_bytes();
        let new_chunks = chunk_count(bytes.len());

        let mut effects = Vec::with_capacity(new_chunks + 1);

        // Length.
        let mut len_felt = [0u8; 32];
        len_felt[0..8].copy_from_slice(&(bytes.len() as u64).to_le_bytes());
        effects.push(Effect::SetField {
            cell: file,
            index: LEN_KEY as usize,
            value: len_felt,
        });

        // Chunks.
        for i in 0..new_chunks {
            let start = i * CHUNK;
            let end = (start + CHUNK).min(bytes.len());
            let mut felt = [0u8; 32];
            felt[..end - start].copy_from_slice(&bytes[start..end]);
            effects.push(Effect::SetField {
                cell: file,
                index: (CHUNK_BASE + i as u64) as usize,
                value: felt,
            });
        }

        // Vacate stale tail chunks (the cell had more chunks than the new content).
        let old_len = cell
            .state
            .get_field_ext(LEN_KEY)
            .map(|f| u64::from_le_bytes(f[0..8].try_into().unwrap()) as usize)
            .unwrap_or(0);
        let old_chunks = chunk_count(old_len);
        for i in new_chunks..old_chunks {
            effects.push(Effect::SetField {
                cell: file,
                index: (CHUNK_BASE + i as u64) as usize,
                value: [0u8; 32],
            });
        }

        effects
    }

    // --- cell construction ----------------------------------------------------

    /// Open permissions (the cap gate carries authority, not a signature) — the
    /// same shape dregg-doc's executor-drive seam uses for its region/editor
    /// cells, so a cross-cell `SetField` is gated by the c-list cap.
    fn open_permissions() -> Permissions {
        Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        }
    }

    /// A file cell: open `set_state` so the per-file authority is the editor's
    /// c-list cap (the cross-cell gate), not a signature. Domain-tagged pk so a
    /// file cell can never collide with the editor cell.
    fn make_file_cell(seed: u32) -> Cell {
        let mut pk = [0u8; 32];
        pk[0..4].copy_from_slice(&seed.to_le_bytes());
        pk[4] = 0xF1; // domain tag: file
        let mut cell = Cell::with_balance(pk, [0u8; 32], 0);
        cell.permissions = open_permissions();
        cell
    }

    /// The editor (author) cell — the turn's agent. Holds the caps to the file
    /// cells it may edit; that cap (or its absence) is the real save gate.
    fn make_editor_cell() -> Cell {
        let mut pk = [0u8; 32];
        pk[0] = 0xED; // domain tag: editor
        let mut cell = Cell::with_balance(pk, [0u8; 32], 1_000_000);
        cell.permissions = open_permissions();
        cell
    }

    // --- the namespace --------------------------------------------------------

    /// A path → file-cell entry in the in-memory namespace (the first-slice
    /// directory: a flat path map, the simpler alternative the seam doc names to
    /// `rbg`'s richer `DirectoryCell`). Each entry is a leaf file cell whose
    /// content substance is the editable text.
    struct Entry {
        cell: CellId,
    }

    /// The mutable inner state, behind one `Mutex` so `FirmamentFs` is `Send +
    /// Sync` (the [`Fs`](crate::fs::Fs) trait bound) while exposing `&self`
    /// methods that mutate the ledger on save.
    struct Inner {
        /// The REAL embedded verified spine: the executor + the ledger it mutates.
        executor: TurnExecutor,
        ledger: Ledger,
        /// The author cell — the agent of every save turn; holds the file caps.
        editor: CellId,
        /// The editor's nonce (the executor advances it per commit; the next turn
        /// carries it).
        nonce: u64,
        /// The editor's receipt-chain head (chained per save).
        chain_head: Option<[u8; 32]>,
        /// path → file cell.
        entries: BTreeMap<PathBuf, Entry>,
        /// A monotonic seed for new file cells.
        next_seed: u32,
        /// Every save's receipt, in commit order — the provenance log (the same
        /// shape `World::receipts`): a save is now an attestable, navigable event.
        receipts: Vec<TurnReceipt>,
    }

    /// The firmament-backed filesystem: file = cell, save = receipted turn.
    ///
    /// Owns an in-process [`Ledger`] + [`TurnExecutor`] — the SAME verified spine
    /// starbridge-v2's `World` wraps. Construct empty with [`FirmamentFs::new`],
    /// then seed files with [`FirmamentFs::seed_file`]; or a host hands one
    /// pre-mounted. Every [`Fs::save`](crate::fs::Fs::save) runs a cap-gated
    /// `SetField` turn through the executor and records the genuine
    /// [`TurnReceipt`].
    pub struct FirmamentFs {
        inner: Mutex<Inner>,
    }

    impl FirmamentFs {
        /// A fresh firmament fs with an empty ledger seeded with the editor
        /// (author) cell. No files yet — seed them with
        /// [`FirmamentFs::seed_file`].
        pub fn new() -> Self {
            let mut ledger = Ledger::new();
            let editor_cell = make_editor_cell();
            let editor = editor_cell.id();
            ledger.insert_cell(editor_cell).expect("editor insert");
            FirmamentFs {
                inner: Mutex::new(Inner {
                    executor: TurnExecutor::new(ComputronCosts::zero()),
                    ledger,
                    editor,
                    nonce: 0,
                    chain_head: None,
                    entries: BTreeMap::new(),
                    next_seed: 1,
                    receipts: Vec::new(),
                }),
            }
        }

        /// The editor (author) cell id — the agent of every save turn.
        pub fn editor_id(&self) -> CellId {
            self.inner.lock().unwrap().editor
        }

        /// How many save-turn receipts have been recorded (the on-ledger save
        /// count). Each is a genuine finalized `TurnReceipt`.
        pub fn receipt_count(&self) -> usize {
            self.inner.lock().unwrap().receipts.len()
        }

        /// The most recent save's receipt (the proof-carrying token that the last
        /// save happened under the editor's authority), if any save has run.
        pub fn last_receipt(&self) -> Option<TurnReceipt> {
            self.inner.lock().unwrap().receipts.last().cloned()
        }

        /// The file cell backing `path`, if it exists in the namespace.
        pub fn cell_for(&self, path: &Path) -> Option<CellId> {
            self.inner.lock().unwrap().entries.get(path).map(|e| e.cell)
        }

        /// The total balance across all cells in the in-tab ledger — the
        /// conservation observable (Σ balance). A content `SetField` save touches
        /// the file cell's committed `fields_map`, not any balance substance, so a
        /// genuine save leaves this INVARIANT: the editor's edit conserves value.
        /// A test asserts `total_balance` before == after a save (Σδ=0).
        pub fn total_balance(&self) -> i128 {
            self.inner
                .lock()
                .unwrap()
                .ledger
                .iter()
                .map(|(_, c)| c.state.balance() as i128)
                .sum()
        }

        /// **Seed a file into the namespace** with initial `content`, as GENESIS
        /// (the directory-owner installing a file, like a node seeds a genesis
        /// cell): mint a file cell holding the content projection, grant the
        /// editor the file's edit cap, and register the path. Returns the file's
        /// [`CellId`]. This is the read-side fixture a test/host uses to put a
        /// file on the ledger so a later [`Fs::load`](crate::fs::Fs::load) reads
        /// it from the cell, not disk.
        pub fn seed_file(&self, path: impl Into<PathBuf>, content: &str) -> Result<CellId> {
            let path = path.into();
            let mut inner = self.inner.lock().unwrap();

            let seed = inner.next_seed;
            inner.next_seed += 1;

            // Mint the file cell, write the content into its committed map as
            // genesis state (the same projection a save would land — so the
            // commitment matches from genesis), and grant the editor its cap.
            let mut file_cell = make_file_cell(seed);
            let file = file_cell.id();
            for e in content_write_effects(&file_cell, file, content) {
                if let Effect::SetField { index, value, .. } = e {
                    file_cell.state.set_field_ext(index as u64, value);
                }
            }
            inner
                .ledger
                .insert_cell(file_cell)
                .map_err(|e| anyhow!("file cell insert: {e:?}"))?;

            // Grant the editor the per-file edit cap (so a later save commits).
            let editor = inner.editor;
            inner
                .ledger
                .get_mut(&editor)
                .ok_or_else(|| anyhow!("editor cell missing"))?
                .capabilities
                .grant(file, AuthRequired::None)
                .ok_or_else(|| anyhow!("editor c-list full"))?;

            inner.entries.insert(path, Entry { cell: file });
            Ok(file)
        }
    }

    impl Default for FirmamentFs {
        fn default() -> Self {
            Self::new()
        }
    }

    impl Inner {
        /// Run a save as a real cap-gated turn through the executor. Returns the
        /// genuine receipt on commit, or an error carrying the executor's
        /// in-band refusal reason (the anti-ghost tooth: a refused save is an
        /// `Err`, never a silent partial write).
        fn save_turn(&mut self, file: CellId, content: &str) -> Result<TurnReceipt> {
            let effects = {
                let cell = self
                    .ledger
                    .get(&file)
                    .ok_or_else(|| anyhow!("file cell vanished from ledger"))?;
                content_write_effects(cell, file, content)
            };

            // Build the turn: agent = editor, one action targeting the file cell
            // with the content SetField effects. The file's open `set_state`
            // passes turn-level auth; the per-file CAP gate (cross-cell
            // `check_cross_cell_permission`) is the real enforcement — an editor
            // without the file's cap is refused in-band.
            let mut action = ActionBuilder::new_unchecked_for_tests(file, "save", self.editor);
            for e in &effects {
                action = action.effect(e.clone());
            }
            let action = action.build();

            let mut builder = TurnBuilder::new(self.editor, self.nonce);
            builder.add_action(action);
            let mut turn = builder.fee(0).build();
            turn.previous_receipt_hash = self.chain_head;

            match self.executor.execute(&turn, &mut self.ledger) {
                TurnResult::Committed { receipt, .. } => {
                    // The executor advanced the editor's nonce + receipt-chain
                    // head; mirror them so the next save chains.
                    self.nonce = self
                        .ledger
                        .get(&self.editor)
                        .map(|c| c.state.nonce())
                        .unwrap_or(self.nonce + 1);
                    self.chain_head = Some(receipt.receipt_hash());
                    self.receipts.push(receipt.clone());
                    Ok(receipt)
                }
                TurnResult::Rejected { reason, .. } => {
                    Err(anyhow!("save turn refused by the executor: {reason:?}"))
                }
                TurnResult::Expired => bail!("save turn expired"),
                TurnResult::Pending => bail!("save turn pending"),
            }
        }
    }

    impl Fs for FirmamentFs {
        fn load(&self, path: &Path) -> Result<String> {
            let inner = self.inner.lock().unwrap();
            let entry = inner
                .entries
                .get(path)
                .ok_or_else(|| anyhow!("no cell mounted at {}", path.display()))?;
            let cell = inner
                .ledger
                .get(&entry.cell)
                .ok_or_else(|| anyhow!("file cell missing from ledger"))?;
            decode_content(cell)
        }

        fn save(&self, path: &Path, content: &str) -> Result<()> {
            let mut inner = self.inner.lock().unwrap();
            // Resolve the path → file cell; if the path is new, mint a file cell
            // for it on the fly (a "save as" into the namespace) and grant the
            // editor its cap so this very save commits.
            let file = match inner.entries.get(path) {
                Some(e) => e.cell,
                None => {
                    let seed = inner.next_seed;
                    inner.next_seed += 1;
                    let file_cell = make_file_cell(seed);
                    let file = file_cell.id();
                    inner
                        .ledger
                        .insert_cell(file_cell)
                        .map_err(|e| anyhow!("file cell insert: {e:?}"))?;
                    let editor = inner.editor;
                    inner
                        .ledger
                        .get_mut(&editor)
                        .ok_or_else(|| anyhow!("editor cell missing"))?
                        .capabilities
                        .grant(file, AuthRequired::None)
                        .ok_or_else(|| anyhow!("editor c-list full"))?;
                    inner.entries.insert(path.to_path_buf(), Entry { cell: file });
                    file
                }
            };
            // THE SAVE IS A TURN. The receipt is the cap-gated witness that this
            // exact edit happened under this exact authority — recorded in the
            // provenance log; a light client can confirm the file holds this
            // content without trusting the editor.
            inner.save_turn(file, content)?;
            Ok(())
        }

        fn read_dir(&self, path: &Path) -> Result<Vec<DirEntry>> {
            let inner = self.inner.lock().unwrap();
            // List the immediate children of `path` in the namespace. The flat
            // map holds full paths; a child is an entry whose parent is `path`.
            let mut out = Vec::new();
            let mut seen_dirs = std::collections::BTreeSet::new();
            for p in inner.entries.keys() {
                let Ok(rest) = p.strip_prefix(path) else {
                    continue;
                };
                let mut comps = rest.components();
                let Some(first) = comps.next() else { continue };
                let child = path.join(first.as_os_str());
                if comps.next().is_some() {
                    // `child` is an intermediate directory (more path remains).
                    if seen_dirs.insert(child.clone()) {
                        out.push(DirEntry { path: child, is_dir: true });
                    }
                } else {
                    // `child` is a leaf file.
                    out.push(DirEntry { path: child, is_dir: false });
                }
            }
            Ok(out)
        }

        fn metadata(&self, path: &Path) -> Result<Metadata> {
            let inner = self.inner.lock().unwrap();
            if let Some(entry) = inner.entries.get(path) {
                let cell = inner
                    .ledger
                    .get(&entry.cell)
                    .ok_or_else(|| anyhow!("file cell missing from ledger"))?;
                let len = decode_content(cell).map(|s| s.len()).unwrap_or(0) as u64;
                return Ok(Metadata { is_dir: false, is_symlink: false, len });
            }
            // A directory iff some entry lives under it.
            let is_dir = inner.entries.keys().any(|p| p.starts_with(path) && p != path);
            if is_dir {
                Ok(Metadata { is_dir: true, is_symlink: false, len: 0 })
            } else {
                bail!("no cell mounted at {}", path.display())
            }
        }

        fn backend_label(&self) -> &'static str {
            "FirmamentFs (cell=file, save=receipted turn)"
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::fs::Fs;

        #[test]
        fn save_is_a_receipted_turn_and_content_round_trips_through_the_ledger() {
            let fs = FirmamentFs::new();
            let path = PathBuf::from("/proj/src/main.rs");
            let original = "fn main() {\n    println!(\"before\");\n}\n";
            let edited = "fn main() {\n    println!(\"AFTER — a receipted turn\");\n}\n";

            // Seed the file as a cell (the read-side fixture).
            let file = fs.seed_file(&path, original).unwrap();

            // load() reads the content FROM THE CELL (not disk).
            assert_eq!(fs.load(&path).unwrap(), original, "seed round-trips from the cell");
            assert_eq!(fs.receipt_count(), 0, "a seed is genesis, not a turn — no receipt yet");

            // save() runs a real cap-gated turn → a genuine receipt.
            fs.save(&path, edited).unwrap();
            assert_eq!(fs.receipt_count(), 1, "the save produced ONE receipt");
            let receipt = fs.last_receipt().expect("a receipt was recorded");
            assert_eq!(receipt.agent, fs.editor_id(), "the editor is the turn's agent");
            assert_ne!(
                receipt.pre_state_hash, receipt.post_state_hash,
                "the save moved the ledger state (the edit landed on-ledger)"
            );
            assert!(receipt.action_count >= 1);

            // re-load() reads the edited content BACK FROM THE LEDGER (the cell's
            // committed map the turn wrote) — never disk.
            assert_eq!(
                fs.load(&path).unwrap(),
                edited,
                "the edited content round-trips through the ledger, not disk"
            );

            // The file cell is the one the namespace resolves the path to.
            assert_eq!(fs.cell_for(&path), Some(file));
        }

        #[test]
        fn save_without_the_edit_cap_is_refused_in_band() {
            // The cross-cell cap gate is the real save authority: a file cell the
            // editor holds NO cap for cannot be saved (the executor refuses it
            // in-band — the anti-ghost tooth).
            let fs = FirmamentFs::new();
            let path = PathBuf::from("/locked.txt");
            // Mint a file cell directly in the ledger WITHOUT granting the editor
            // its cap, then register the path pointing at it.
            {
                let mut inner = fs.inner.lock().unwrap();
                let seed = inner.next_seed;
                inner.next_seed += 1;
                let mut cell = make_file_cell(seed);
                let file = cell.id();
                for e in content_write_effects(&cell, file, "secret") {
                    if let Effect::SetField { index, value, .. } = e {
                        cell.state.set_field_ext(index as u64, value);
                    }
                }
                inner.ledger.insert_cell(cell).unwrap();
                inner.entries.insert(path.clone(), Entry { cell: file });
                // NB: no capabilities.grant — the editor lacks the file's cap.
            }

            // The read still works (a read is authority-checked at the namespace,
            // not via a turn).
            assert_eq!(fs.load(&path).unwrap(), "secret");

            // The save is REFUSED by the executor's cap gate, in-band.
            let err = fs.save(&path, "tampered").unwrap_err();
            assert!(
                err.to_string().contains("refused"),
                "save without the edit cap must be refused: {err}"
            );
            // The content is UNTOUCHED — the executor rolled the ledger back.
            assert_eq!(fs.load(&path).unwrap(), "secret", "a refused save leaves the cell untouched");
            assert_eq!(fs.receipt_count(), 0, "no receipt for a refused save");
        }

        #[test]
        fn read_dir_lists_namespace_children() {
            let fs = FirmamentFs::new();
            fs.seed_file("/proj/a.rs", "a").unwrap();
            fs.seed_file("/proj/b.rs", "b").unwrap();
            fs.seed_file("/proj/sub/c.rs", "c").unwrap();

            let mut entries = fs.read_dir(Path::new("/proj")).unwrap();
            entries.sort_by(|x, y| x.path.cmp(&y.path));
            let names: Vec<_> = entries.iter().map(|e| (e.file_name(), e.is_dir)).collect();
            assert_eq!(
                names,
                vec![
                    ("a.rs".to_string(), false),
                    ("b.rs".to_string(), false),
                    ("sub".to_string(), true),
                ]
            );

            let md = fs.metadata(Path::new("/proj/a.rs")).unwrap();
            assert!(!md.is_dir && md.len == 1);
            let dmd = fs.metadata(Path::new("/proj/sub")).unwrap();
            assert!(dmd.is_dir);
        }

        #[test]
        fn shrinking_a_file_vacates_stale_tail_chunks() {
            // A save that shrinks the content must vacate the old tail so the
            // commitment binds only the live content (a re-load can't resurrect
            // bytes the editor deleted).
            let fs = FirmamentFs::new();
            let path = PathBuf::from("/big.txt");
            let big = "x".repeat(200); // 7 chunks
            let small = "y".repeat(10); // 1 chunk
            fs.seed_file(&path, &big).unwrap();
            fs.save(&path, &small).unwrap();
            assert_eq!(fs.load(&path).unwrap(), small);
        }
    }
}

#[cfg(feature = "firmament")]
pub use live::FirmamentFs;
