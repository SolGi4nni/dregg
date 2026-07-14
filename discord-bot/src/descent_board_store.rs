//! The sqlite-backed [`SqliteDescentBoardStore`] — the durable backing of the `/descent`
//! no-cheat leaderboard board, over the bot's async sqlx [`Database`].
//!
//! `commands::descent` OWNS the [`DescentBoardStore`] trait, the `StoredDescentUniverse` /
//! `StoredDescentCompletion` shapes, and the boot replay-and-re-verify ([`load_board`]). This
//! module supplies the ONE thing the main loop owes it: a durable impl. It is the exact shape of
//! [`crate::gallery_store::SqliteGalleryStore`] — the [`DescentBoardStore`] trait is SYNC (`&self`),
//! but the bot's `Database` is async sqlx, so each method drives its async query to completion with
//! [`tokio::task::block_in_place`] on the current multi-thread runtime, falling back to a stored
//! [`tokio::runtime::Handle`] when called from OUTSIDE a runtime worker — which is the norm here,
//! since the live board is owned by a dedicated *non-tokio* `descent-store` `std::thread`.
//!
//! The persist methods are `INSERT OR IGNORE` on the PK in the `Database` layer, so this store
//! honours the trait's idempotency contract without any extra work here. On boot,
//! [`load_board`](crate::commands::descent::load_board) regenerates each day-world from its stored
//! seed and REPLAYS every completion through the real no-cheat gate: a tampered row (a losing move
//! line, a lied turn count, or a mismatched seed) cannot resurrect a cheat onto the board.
//!
//! [`load_board`]: crate::commands::descent::load_board

use crate::commands::descent::{DescentBoardStore, StoredDescentCompletion, StoredDescentUniverse};
use crate::db::{Database, DescentCompletionRow, DescentUniverseRow};

/// A [`DescentBoardStore`] persisted in the bot's sqlite database. Day-universes live in
/// `descent_universes` (their committed beacon seed), accepted board completions in
/// `descent_completions`; both survive restart and are re-verified by replay on boot.
pub struct SqliteDescentBoardStore {
    db: Database,
    handle: tokio::runtime::Handle,
}

impl SqliteDescentBoardStore {
    /// Wrap a `Database`. `handle` is the runtime to drive the async queries on when the store is
    /// called from OUTSIDE a runtime worker (the live board's dedicated `std::thread`); inside a
    /// runtime worker the current handle is used.
    pub fn new(db: Database, handle: tokio::runtime::Handle) -> Self {
        SqliteDescentBoardStore { db, handle }
    }

    /// Drive an async DB future to completion synchronously — the sync↔async bridge the sync
    /// [`DescentBoardStore`] trait forces (identical to `gallery_store::SqliteGalleryStore::block`).
    fn block<F: std::future::Future>(&self, fut: F) -> F::Output {
        match tokio::runtime::Handle::try_current() {
            Ok(current) => tokio::task::block_in_place(move || current.block_on(fut)),
            Err(_) => self.handle.block_on(fut),
        }
    }
}

impl DescentBoardStore for SqliteDescentBoardStore {
    fn persist_universe(&self, u: &StoredDescentUniverse) -> Result<(), String> {
        let row = DescentUniverseRow {
            id_hex: u.id_hex.clone(),
            author: u.author.clone(),
            seed_hex: u.seed_hex.clone(),
        };
        self.block(self.db.persist_descent_universe(&row))
            .map_err(|e| e.to_string())
    }

    fn persist_completion(&self, c: &StoredDescentCompletion) -> Result<(), String> {
        let row = DescentCompletionRow {
            key_hex: c.key_hex.clone(),
            universe_id_hex: c.universe_id_hex.clone(),
            player: c.player.clone(),
            moves_json: c.moves_json.clone(),
            claimed_turns: c.claimed_turns,
        };
        self.block(self.db.persist_descent_completion(&row))
            .map_err(|e| e.to_string())
    }

    fn list_universes(&self) -> Result<Vec<StoredDescentUniverse>, String> {
        let rows = self
            .block(self.db.list_descent_universes())
            .map_err(|e| e.to_string())?;
        Ok(rows
            .into_iter()
            .map(|r| StoredDescentUniverse {
                id_hex: r.id_hex,
                author: r.author,
                seed_hex: r.seed_hex,
            })
            .collect())
    }

    fn list_completions(&self) -> Result<Vec<StoredDescentCompletion>, String> {
        let rows = self
            .block(self.db.list_descent_completions())
            .map_err(|e| e.to_string())?;
        Ok(rows
            .into_iter()
            .map(|r| StoredDescentCompletion {
                key_hex: r.key_hex,
                universe_id_hex: r.universe_id_hex,
                player: r.player,
                moves_json: r.moves_json,
                claimed_turns: r.claimed_turns,
            })
            .collect())
    }
}
