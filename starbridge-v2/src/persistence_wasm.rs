//! WASM stub for native World persistence.
//!
//! On `wasm32-unknown-unknown` there is no `dregg-persist` (it pulls `redb`, a
//! native-only embedded store). A browser image is always EPHEMERAL: `World`'s
//! `persist: Option<WorldPersist>` field is permanently `None`, so the durable
//! paths in `world.rs` are dead — but they must still TYPECHECK against this
//! stub surface. [`WorldPersist`] is therefore an UNINHABITED enum: no value can
//! exist, so every `if let Some(p) = self.persist.as_ref()` arm is dead code,
//! and its method bodies are unreachable (`match *self {}`).
//!
//! [`canonical_ledger_root`] is the genuine pure convergence root (cell-postcard
//! leaves under a derived-key blake3 tree) — it depends only on `dregg_cell` +
//! `postcard` + `blake3`, all wasm32-safe, so the browser image's root matches
//! the native/node root byte-for-byte.

/// The durable store error — a stub on wasm (no store exists). Carried only so
/// `world.rs`'s fail-closed `dual_write` error formatting typechecks.
#[derive(Debug)]
pub enum StoreError {}

impl std::fmt::Display for StoreError {
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {}
    }
}

impl std::error::Error for StoreError {}

/// Why opening a durable image failed — unreachable on wasm (no `World::open`).
#[derive(Debug)]
pub enum OpenError {
    Store(StoreError),
    Divergent { got: [u8; 32], expected: [u8; 32] },
}

impl std::fmt::Display for OpenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OpenError::Store(e) => write!(f, "durable store error: {e}"),
            OpenError::Divergent { got, expected } => {
                write!(f, "recovery convergence FAILED: {got:?} != {expected:?}")
            }
        }
    }
}

impl std::error::Error for OpenError {}

/// The fully-recovered image content — never constructed on wasm.
pub struct RecoveredImage {
    pub ledger: dregg_cell::Ledger,
    pub genesis_cells: Vec<dregg_cell::Cell>,
    pub committed: Vec<dregg_turn::turn::Turn>,
    pub cursor: u64,
}

/// The durable backing — UNINHABITED on wasm (the browser image is ephemeral, so
/// `World::persist` is permanently `None`). Its methods exist only so the dead
/// `Some(p)` arms in `world.rs` typecheck; their bodies are unreachable.
pub enum WorldPersist {}

impl WorldPersist {
    pub fn record_genesis(&self, _cell: &dregg_cell::Cell) -> Result<(), StoreError> {
        match *self {}
    }

    pub fn checkpoint(&self, _ledger: &dregg_cell::Ledger, _height: u64) {
        match *self {}
    }

    pub fn dual_write(
        &mut self,
        _height: u64,
        _ledger: &dregg_cell::Ledger,
        _touched: &[dregg_cell::CellId],
        _receipt: &dregg_turn::turn::TurnReceipt,
        _turn: &dregg_turn::turn::Turn,
    ) -> Result<(), StoreError> {
        match *self {}
    }
}

/// The durable convergence root — the genuine pure implementation (the same
/// construction as `dregg_persist::canonical_ledger_root`: domain
/// `"dregg-ledger-root-v2"`, sort-by-id, length-prefix, whole-cell postcard
/// leaves), copied here because `dregg-persist` is not in the wasm graph. Depends
/// only on wasm-safe crates (`dregg_cell` + `postcard` + `blake3`).
pub fn canonical_ledger_root(ledger: &dregg_cell::Ledger) -> [u8; 32] {
    let mut entries: Vec<([u8; 32], [u8; 32])> = ledger
        .iter()
        .map(|(id, cell)| {
            let bytes = postcard::to_stdvec(cell).unwrap_or_default();
            (*id.as_bytes(), *blake3::hash(&bytes).as_bytes())
        })
        .collect();
    entries.sort_by_key(|a| a.0);
    let mut hasher = blake3::Hasher::new_derive_key("dregg-ledger-root-v2");
    hasher.update(&(entries.len() as u64).to_le_bytes());
    for (id, h) in &entries {
        hasher.update(id);
        hasher.update(h);
    }
    *hasher.finalize().as_bytes()
}
