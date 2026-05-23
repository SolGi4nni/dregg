//! Database layer (SQLite via sqlx).

use sqlx::{Pool, Sqlite, SqlitePool};

/// Database handle wrapping a SQLite connection pool.
#[derive(Clone)]
pub struct Database {
    pool: Pool<Sqlite>,
}

impl Database {
    /// Connect to the database and run migrations.
    pub async fn connect(url: &str) -> Result<Self, sqlx::Error> {
        let pool = SqlitePool::connect(url).await?;
        Ok(Self { pool })
    }

    /// Check if a user has a wallet.
    pub async fn user_exists(&self, _user_id: &str) -> Result<bool, sqlx::Error> {
        // Placeholder — will be implemented with full schema.
        Ok(true)
    }

    /// Get last processed block height for activity feed.
    pub async fn get_last_block_height(&self) -> Result<u64, sqlx::Error> {
        let row: Option<(i64,)> =
            sqlx::query_as("SELECT value FROM kv WHERE key = 'last_block_height'")
                .fetch_optional(&self.pool)
                .await?;
        Ok(row.map(|(v,)| v as u64).unwrap_or(0))
    }

    /// Set last processed block height.
    pub async fn set_last_block_height(&self, height: u64) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT OR REPLACE INTO kv (key, value) VALUES ('last_block_height', ?)",
        )
        .bind(height as i64)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    /// Get all configured feed channels.
    pub async fn get_all_feed_channels(&self) -> Result<Vec<(String, String)>, sqlx::Error> {
        let rows: Vec<(String, String)> =
            sqlx::query_as("SELECT guild_id, channel_id FROM feed_channels")
                .fetch_all(&self.pool)
                .await?;
        Ok(rows)
    }

    /// Get users watching a specific cell.
    pub async fn get_watchers_for_cell(&self, cell_id: &str) -> Result<Vec<String>, sqlx::Error> {
        let rows: Vec<(String,)> =
            sqlx::query_as("SELECT user_id FROM watchers WHERE cell_id = ?")
                .bind(cell_id)
                .fetch_all(&self.pool)
                .await?;
        Ok(rows.into_iter().map(|(id,)| id).collect())
    }
}
