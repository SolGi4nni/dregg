//! The sqlite-backed [`GalleryStore`] — the durable backing of the `/gallery`
//! universe registry, over the bot's async sqlx [`Database`].
//!
//! `commands::gallery` OWNS the [`GalleryStore`] trait, the `StoredUniverse` /
//! `StoredCompletion` shapes, and the boot replay-and-re-verify (`load_registry`).
//! This module supplies the ONE thing the main loop owes it: a durable impl. It is
//! the exact shape of [`crate::pay::SqliteCreditStore`] — the [`GalleryStore`] trait
//! is SYNC (interior mutability, `&self`), but the bot's `Database` is async sqlx, so
//! each method drives its async query to completion with [`tokio::task::block_in_place`]
//! on the current multi-thread runtime (no nested-runtime panic, no deadlock), falling
//! back to a stored [`tokio::runtime::Handle`] when somehow called from outside a runtime.
//!
//! The persist methods are `INSERT OR IGNORE` on the PK in the `Database` layer, so
//! this store honours the trait's idempotency contract without any extra work here.

use crate::commands::gallery::{GalleryStore, StoredCompletion, StoredUniverse};
use crate::db::{Database, UgcCompletionRow, UgcUniverseRow};

/// A [`GalleryStore`] persisted in the bot's sqlite database. Published universes live
/// in `ugc_universes`, accepted completions in `ugc_completions`; both survive restart
/// and are re-verified by replay on boot.
pub struct SqliteGalleryStore {
    db: Database,
    handle: tokio::runtime::Handle,
}

impl SqliteGalleryStore {
    /// Wrap a `Database`. `handle` is the runtime to fall back to when a store method is
    /// somehow called from OUTSIDE any runtime; inside a runtime worker the current handle
    /// is used.
    pub fn new(db: Database, handle: tokio::runtime::Handle) -> Self {
        SqliteGalleryStore { db, handle }
    }

    /// Drive an async DB future to completion synchronously — the sync↔async bridge the
    /// sync [`GalleryStore`] trait forces (identical to `pay::SqliteCreditStore::block`).
    fn block<F: std::future::Future>(&self, fut: F) -> F::Output {
        match tokio::runtime::Handle::try_current() {
            Ok(current) => tokio::task::block_in_place(move || current.block_on(fut)),
            Err(_) => self.handle.block_on(fut),
        }
    }
}

impl GalleryStore for SqliteGalleryStore {
    fn persist_universe(&self, u: &StoredUniverse) -> Result<(), String> {
        let row = UgcUniverseRow {
            id_hex: u.id_hex.clone(),
            kind: u.kind.clone(),
            name: u.name.clone(),
            author: u.author.clone(),
            source: u.source.clone(),
            epoch_hex: u.epoch_hex.clone(),
            win_json: u.win_json.clone(),
            parent_id_hex: u.parent_id_hex.clone(),
            author_key_hex: u.author_key_hex.clone(),
            author_sig_hex: u.author_sig_hex.clone(),
        };
        self.block(self.db.persist_ugc_universe(&row))
            .map_err(|e| e.to_string())
    }

    fn persist_completion(&self, c: &StoredCompletion) -> Result<(), String> {
        let row = UgcCompletionRow {
            key_hex: c.key_hex.clone(),
            universe_id_hex: c.universe_id_hex.clone(),
            player: c.player.clone(),
            moves_json: c.moves_json.clone(),
            claimed_turns: c.claimed_turns,
        };
        self.block(self.db.persist_ugc_completion(&row))
            .map_err(|e| e.to_string())
    }

    fn list_universes(&self) -> Result<Vec<StoredUniverse>, String> {
        let rows = self
            .block(self.db.list_ugc_universes())
            .map_err(|e| e.to_string())?;
        Ok(rows
            .into_iter()
            .map(|r| StoredUniverse {
                id_hex: r.id_hex,
                kind: r.kind,
                name: r.name,
                author: r.author,
                source: r.source,
                epoch_hex: r.epoch_hex,
                win_json: r.win_json,
                parent_id_hex: r.parent_id_hex,
                author_key_hex: r.author_key_hex,
                author_sig_hex: r.author_sig_hex,
            })
            .collect())
    }

    fn list_completions(&self) -> Result<Vec<StoredCompletion>, String> {
        let rows = self
            .block(self.db.list_ugc_completions())
            .map_err(|e| e.to_string())?;
        Ok(rows
            .into_iter()
            .map(|r| StoredCompletion {
                key_hex: r.key_hex,
                universe_id_hex: r.universe_id_hex,
                player: r.player,
                moves_json: r.moves_json,
                claimed_turns: r.claimed_turns,
            })
            .collect())
    }
}
