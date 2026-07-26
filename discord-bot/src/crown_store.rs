//! The sqlite-backed [`SqliteCrownStore`] — the durable backing of 👑 the crown's ranked
//! proof-carrying board, over the bot's async sqlx [`Database`].
//!
//! `commands::crown` OWNS the [`CrownStore`] trait, the [`StoredCrownFold`] shape and the boot
//! re-submit-and-re-verify (`restore_folds`). This module supplies the ONE thing the main loop
//! owes it: a durable impl. It is the exact shape of [`crate::descent_board_store`] — the trait
//! is SYNC (`&self`), but the bot's `Database` is async sqlx, so each method drives its async
//! query to completion with [`tokio::task::block_in_place`] on the current multi-thread runtime,
//! falling back to a stored [`tokio::runtime::Handle`] when called from OUTSIDE a runtime worker
//! — which is the norm here, since the crown board is owned by a dedicated *non-tokio*
//! `crown-board` `std::thread`.
//!
//! `persist_crown_fold` is `INSERT OR IGNORE` on the `token` PK in the `Database` layer, so this
//! store honours the trait's idempotency contract without any extra work here.
//!
//! ## The encoding, and why it is not a serde blob
//!
//! A [`StoredCrownFold`] is the proof envelope plus the board anchor it was accepted against.
//! The envelope is raw bytes (a sqlite `BLOB`). The anchor is a VK fingerprint (32 bytes, hex)
//! and two 8-limb BabyBear vectors, stored as comma-joined canonical decimals. That is
//! deliberately a dumb, readable encoding: an operator can look at a `crown_folds` row and see
//! exactly which trust root a crown was ranked under. It carries no authority of its own — every
//! stored field is re-checked by the light client on the way back in, so a corrupt column costs a
//! refused restore, never a forged crown.

use crate::commands::crown::{CrownStore, StoredCrownFold};
use crate::db::{CrownFoldRow, CrownFoldWrite, Database};

/// A [`CrownStore`] persisted in the bot's sqlite database (`crown_folds`). Accepted crown folds
/// survive restart and are re-verified through the board's own O(1) accept path on boot.
pub struct SqliteCrownStore {
    db: Database,
    handle: tokio::runtime::Handle,
}

impl SqliteCrownStore {
    /// Wrap a `Database`. `handle` is the runtime to drive the async queries on when the store is
    /// called from OUTSIDE a runtime worker (the crown board's dedicated `std::thread`); inside a
    /// runtime worker the current handle is used.
    pub fn new(db: Database, handle: tokio::runtime::Handle) -> Self {
        SqliteCrownStore { db, handle }
    }

    fn block<F: std::future::Future>(&self, fut: F) -> F::Output {
        match tokio::runtime::Handle::try_current() {
            Ok(current) => tokio::task::block_in_place(move || current.block_on(fut)),
            Err(_) => self.handle.block_on(fut),
        }
    }
}

/// Join canonical field limbs into the stored decimal list.
fn join_limbs(limbs: &[u32]) -> String {
    limbs
        .iter()
        .map(|v| v.to_string())
        .collect::<Vec<_>>()
        .join(",")
}

/// Parse the stored decimal list back into exactly `N` limbs. A wrong arity or a non-numeric
/// entry is `None` — the row is then skipped rather than restored under a truncated anchor.
fn split_limbs<const N: usize>(text: &str) -> Option<[u32; N]> {
    let parsed: Vec<u32> = text
        .split(',')
        .map(|v| v.trim().parse::<u32>())
        .collect::<Result<_, _>>()
        .ok()?;
    parsed.try_into().ok()
}

fn parse_vk(hex_text: &str) -> Option<[u8; 32]> {
    let bytes = hex::decode(hex_text).ok()?;
    bytes.try_into().ok()
}

impl CrownStore for SqliteCrownStore {
    fn persist_fold(&self, fold: &StoredCrownFold) -> Result<(), String> {
        let row = CrownFoldRow {
            token: fold.token,
            game: fold.game.clone(),
            channel_id: fold.channel.to_string(),
            player: fold.player.clone(),
            turns: i64::try_from(fold.turns).unwrap_or(i64::MAX),
            vk_hex: hex::encode(fold.vk),
            genesis_root_hex: join_limbs(&fold.genesis_root),
            win_root_hex: join_limbs(&fold.win_root),
            proof: fold.proof.clone(),
            created_at: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_secs() as i64)
                .unwrap_or_default(),
        };
        match self
            .block(self.db.persist_crown_fold(&row))
            .map_err(|e| e.to_string())?
        {
            CrownFoldWrite::Stored | CrownFoldWrite::AlreadyIdentical => Ok(()),
            // ⚑ The row was DROPPED because a different fold already holds this token. Reporting
            // `Ok` here is what made `commands::crown`'s "RANKED but did not persist" warning
            // unreachable: the crown is on the board in memory and will vanish at the next
            // restart, and nothing said so.
            CrownFoldWrite::TokenTaken => Err(format!(
                "token {} is already held by a DIFFERENT crown fold — this fold was not persisted \
                 (its token counter fell behind a row that did not re-verify at boot)",
                fold.token
            )),
        }
    }

    fn list_folds(&self) -> Result<Vec<StoredCrownFold>, String> {
        let rows = self
            .block(self.db.list_crown_folds())
            .map_err(|e| e.to_string())?;
        let mut out = Vec::with_capacity(rows.len());
        for row in rows {
            // A row this build cannot decode is DROPPED, not half-restored: a fold whose anchor
            // is unreadable has no trust root to verify its proof against, and restoring it under
            // a guessed one would be the exact forgery the board refuses.
            let (Some(vk), Some(genesis_root), Some(win_root)) = (
                parse_vk(&row.vk_hex),
                split_limbs(&row.genesis_root_hex),
                split_limbs(&row.win_root_hex),
            ) else {
                tracing::warn!(
                    "crown fold #{} has an undecodable anchor and was not restored",
                    row.token
                );
                continue;
            };
            let Ok(channel) = row.channel_id.parse::<u64>() else {
                tracing::warn!(
                    "crown fold #{} has an undecodable channel id and was not restored",
                    row.token
                );
                continue;
            };
            out.push(StoredCrownFold {
                token: row.token,
                game: row.game,
                channel,
                player: row.player,
                turns: usize::try_from(row.turns).unwrap_or(0),
                vk,
                genesis_root,
                win_root,
                proof: row.proof,
            });
        }
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The round-trip the crown's restart survival rests on: a persisted fold comes back with
    /// its token, anchor, envelope and attested turn count byte-identical — including the two
    /// 8-limb BabyBear anchors, which are what the light client binds a submission against.
    #[tokio::test(flavor = "multi_thread")]
    async fn a_ranked_fold_round_trips_through_sqlite() {
        let db = Database::connect("sqlite::memory:").await.unwrap();
        let store = SqliteCrownStore::new(db, tokio::runtime::Handle::current());
        let fold = StoredCrownFold {
            token: 7,
            game: "automatafl".into(),
            channel: 12_345,
            player: "ab".repeat(32),
            turns: 3,
            vk: [0x5A; 32],
            genesis_root: [1, 2, 3, 4, 5, 6, 7, 8],
            win_root: [9, 10, 11, 12, 13, 14, 15, 16],
            proof: vec![0xDE, 0xAD, 0xBE, 0xEF],
        };
        store.persist_fold(&fold).unwrap();
        // Idempotent by token — a re-persist of the same fold is a no-op, not a duplicate row.
        store.persist_fold(&fold).unwrap();

        let back = store.list_folds().unwrap();
        assert_eq!(back, vec![fold], "the fold round-trips exactly");
    }

    /// ⚑ **A TOKEN COLLISION IS REPORTED, not swallowed.**
    ///
    /// `INSERT OR IGNORE` made "the row landed" and "the row was DROPPED because a different
    /// fold already owns this token" the same `Ok(())`. So `commands::crown::persist_fold`'s
    /// "RANKED but did not persist — its public Re-verify button will not survive a restart"
    /// warning could never fire, and the crown vanished at the next boot with nobody told.
    ///
    /// Both halves are asserted: the genuine re-persist is still idempotent (`Ok`), and the
    /// collision is an `Err` whose text names the token.
    #[tokio::test(flavor = "multi_thread")]
    async fn a_token_collision_is_reported_while_a_genuine_repersist_stays_idempotent() {
        let db = Database::connect("sqlite::memory:").await.unwrap();
        let store = SqliteCrownStore::new(db, tokio::runtime::Handle::current());
        let fold = StoredCrownFold {
            token: 9,
            game: "tug".into(),
            channel: 1,
            player: "aa".repeat(32),
            turns: 2,
            vk: [0x01; 32],
            genesis_root: [1, 2, 3, 4, 5, 6, 7, 8],
            win_root: [9, 10, 11, 12, 13, 14, 15, 16],
            proof: vec![0x01, 0x02],
        };
        store.persist_fold(&fold).expect("the first write lands");
        store
            .persist_fold(&fold)
            .expect("re-persisting the SAME fold is idempotent, not an error");

        // A DIFFERENT fold minted the same token — what a `next_token` that fell behind does.
        let collided = StoredCrownFold {
            player: "bb".repeat(32),
            proof: vec![0xFF, 0xFE],
            ..fold.clone()
        };
        let refused = store
            .persist_fold(&collided)
            .expect_err("a token collision must be REPORTED, not silently dropped");
        assert!(
            refused.contains("token 9") && refused.contains("not persisted"),
            "the refusal must name the token and say the fold did not persist: {refused}"
        );

        // And the store still holds exactly the FIRST fold — the collision changed nothing.
        assert_eq!(store.list_folds().unwrap(), vec![fold]);
    }

    /// A row whose anchor cannot be decoded is DROPPED, not restored under a guessed trust
    /// root. (The proof would fail the light client anyway; this is the earlier, louder tooth.)
    #[tokio::test(flavor = "multi_thread")]
    async fn an_undecodable_anchor_row_is_dropped() {
        let db = Database::connect("sqlite::memory:").await.unwrap();
        db.persist_crown_fold(&CrownFoldRow {
            token: 1,
            game: "tug".into(),
            channel_id: "1".into(),
            player: "p".into(),
            turns: 1,
            vk_hex: "not-hex".into(),
            genesis_root_hex: "1,2,3".into(), // wrong arity, too
            win_root_hex: "1,2,3,4,5,6,7,8".into(),
            proof: vec![1],
            created_at: 0,
        })
        .await
        .unwrap();
        let store = SqliteCrownStore::new(db, tokio::runtime::Handle::current());
        assert!(
            store.list_folds().unwrap().is_empty(),
            "an undecodable anchor never becomes a restored crown"
        );
    }
}
