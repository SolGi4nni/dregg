//! Database layer (SQLite via sqlx).

use serde::Serialize;
use sqlx::{Pool, Row, Sqlite, SqlitePool};

/// How a Discord user identity is bound to a dregg cell.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IdentityMode {
    /// The bot deterministically derives and can sign for this cell.
    Hosted,
    /// The user has requested an external link but has not completed ownership proof.
    ExternalPending,
    /// The user proved control of the external cell.
    ExternalVerified,
}

impl IdentityMode {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Hosted => "hosted",
            Self::ExternalPending => "external_pending",
            Self::ExternalVerified => "external_verified",
        }
    }

    fn from_db(value: &str) -> Self {
        match value {
            "external_pending" => Self::ExternalPending,
            "external_verified" => Self::ExternalVerified,
            _ => Self::Hosted,
        }
    }
}

/// User identity record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UserIdentity {
    pub cell_id: String,
    pub mode: IdentityMode,
    pub link_challenge: Option<String>,
}

/// Materialized Starbridge app activity recorded by the Discord host.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct StarbridgeActivity {
    pub id: i64,
    pub app: String,
    pub action: String,
    pub actor_discord_id: String,
    pub guild_id: Option<String>,
    pub subject: Option<String>,
    pub status: String,
    pub details_json: String,
    pub timestamp: i64,
}

/// Discord namespace path backed by a devnet programmable queue.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct StarbridgeQueue {
    pub namespace_path: String,
    pub guild_id: String,
    pub name: String,
    pub queue_id: String,
    pub created_by: String,
    pub acl_role: Option<String>,
    pub rate_limit: Option<i64>,
    pub min_deposit: Option<i64>,
    pub created_at: i64,
}

/// Discord user subscription to a Starbridge queue.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct StarbridgeQueueSubscription {
    pub namespace_path: String,
    pub discord_id: String,
    pub subscribed_at: i64,
}

/// Durable Discord-mediated CapTP handoff state.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CaptpHandoffRecord {
    pub token_id: String,
    pub cell_id: String,
    pub sturdy_uri: String,
    pub from_discord_id: String,
    pub to_discord_id: String,
    pub recipient_cell_id: String,
    pub status: String,
    pub issued_at: i64,
    pub redeemed_at: Option<i64>,
    pub revoked_at: Option<i64>,
    pub token_json: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CaptpExportRecord {
    pub cell_id: String,
    pub sturdy_uri: String,
    pub shared_with: Option<String>,
    pub exported_at: i64,
    pub revoked: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CaptpHeldRecord {
    pub cell_id: String,
    pub sturdy_uri: String,
    pub label: Option<String>,
    pub shared_by: Option<String>,
    pub acquired_at: i64,
    pub live: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CaptpLocalHandoffRecord {
    pub token_id: String,
    pub cell_id: String,
    pub sturdy_uri: String,
    pub recipient_cell_id: String,
    pub local_signature: String,
    pub status: String,
    pub created_at: i64,
    pub redeemed_at: Option<i64>,
}

/// Credential material held locally for a hosted Discord identity.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct HeldCredential {
    pub credential_id: String,
    pub discord_id: String,
    pub holder_cell_id: String,
    pub issuer_cell_id: String,
    pub schema: String,
    pub issued_at: i64,
    pub turn_hash: Option<String>,
    pub encoded_credential: String,
    pub attributes_json: String,
    pub created_at: i64,
}

/// Locally recorded presentation request/placeholder state.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CredentialPresentation {
    pub request_id: String,
    pub verifier_discord_id: String,
    pub subject_discord_id: String,
    pub subject_cell_id: String,
    pub predicate: String,
    pub status: String,
    pub credential_id: Option<String>,
    pub presentation_json: String,
    pub created_at: i64,
}

/// A user's semi-private DreggNet Cloud channel — the surface from which they
/// drive their own confined Hermes. Visibility is gated to the owner + admin;
/// the admin (ember) monitors all of them via the admin portal.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct UserChannel {
    pub channel_id: String,
    pub discord_id: String,
    pub guild_id: String,
    pub cell_id: String,
    pub status: String,
    pub created_at: i64,
}

/// One cap-gated Hermes verdict in a user's channel (the per-channel agent
/// ledger). `allowed` is the gateway verdict; `receipt` is the committed turn
/// hash when admitted; `reason` names the refused leg when not.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct HermesActivity {
    pub id: i64,
    pub discord_id: String,
    pub channel_id: String,
    pub prompt: String,
    pub tool: String,
    pub kind: String,
    pub allowed: bool,
    pub receipt: Option<String>,
    pub remaining: Option<i64>,
    pub reason: Option<String>,
    pub created_at: i64,
}

/// A user's BYO-LLM-key record as stored at rest. The key is ENCRYPTED — only
/// the AEAD `nonce_b64` + `ciphertext_b64` are persisted; the plaintext never is
/// (see `crate::key_vault`). Carries the user's provider + default model and the
/// metering policy (token budget + rate). Does not derive `Debug` to keep the
/// sealed material out of accidental logs.
#[derive(Clone, PartialEq, Eq)]
pub struct LlmKeyRecord {
    pub provider: String,
    pub model: String,
    pub nonce_b64: String,
    pub ciphertext_b64: String,
    pub token_budget: i64,
    pub rate_limit: i64,
}

/// Database handle wrapping a SQLite connection pool.
#[derive(Clone)]
pub struct Database {
    pool: Pool<Sqlite>,
}

impl Database {
    /// Connect to the database and run migrations.
    pub async fn connect(url: &str) -> Result<Self, sqlx::Error> {
        let pool = SqlitePool::connect(url).await?;

        // Run schema initialization.
        sqlx::query(
            "CREATE TABLE IF NOT EXISTS kv (
                key TEXT PRIMARY KEY,
                value TEXT NOT NULL
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS feed_channels (
                guild_id TEXT PRIMARY KEY,
                channel_id TEXT NOT NULL
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS watchers (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id TEXT NOT NULL,
                cell_id TEXT NOT NULL,
                UNIQUE(user_id, cell_id)
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS users (
                discord_id TEXT PRIMARY KEY,
                cell_id TEXT NOT NULL,
                identity_mode TEXT NOT NULL DEFAULT 'hosted',
                link_challenge TEXT
            )",
        )
        .execute(&pool)
        .await?;

        ensure_column(
            &pool,
            "users",
            "identity_mode",
            "TEXT NOT NULL DEFAULT 'hosted'",
        )
        .await?;
        ensure_column(&pool, "users", "link_challenge", "TEXT").await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS transactions (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                from_user TEXT NOT NULL,
                to_user TEXT NOT NULL,
                amount INTEGER NOT NULL,
                tx_hash TEXT NOT NULL,
                timestamp INTEGER NOT NULL
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS starbridge_activity (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                app TEXT NOT NULL,
                action TEXT NOT NULL,
                actor_discord_id TEXT NOT NULL,
                guild_id TEXT,
                subject TEXT,
                status TEXT NOT NULL,
                details_json TEXT NOT NULL,
                timestamp INTEGER NOT NULL
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE INDEX IF NOT EXISTS idx_starbridge_activity_recent
             ON starbridge_activity (timestamp DESC, id DESC)",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE INDEX IF NOT EXISTS idx_starbridge_activity_app_recent
             ON starbridge_activity (app, timestamp DESC, id DESC)",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS starbridge_queues (
                namespace_path TEXT PRIMARY KEY,
                guild_id TEXT NOT NULL,
                name TEXT NOT NULL,
                queue_id TEXT NOT NULL,
                created_by TEXT NOT NULL,
                acl_role TEXT,
                rate_limit INTEGER,
                min_deposit INTEGER,
                created_at INTEGER NOT NULL
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE INDEX IF NOT EXISTS idx_starbridge_queues_guild
             ON starbridge_queues (guild_id, name)",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS starbridge_queue_subscriptions (
                namespace_path TEXT NOT NULL,
                discord_id TEXT NOT NULL,
                subscribed_at INTEGER NOT NULL,
                PRIMARY KEY (namespace_path, discord_id)
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS captp_handoffs (
                token_id TEXT PRIMARY KEY,
                cell_id TEXT NOT NULL,
                sturdy_uri TEXT NOT NULL,
                from_discord_id TEXT NOT NULL,
                to_discord_id TEXT NOT NULL,
                recipient_cell_id TEXT NOT NULL,
                status TEXT NOT NULL,
                issued_at INTEGER NOT NULL,
                redeemed_at INTEGER,
                revoked_at INTEGER,
                token_json TEXT NOT NULL
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE INDEX IF NOT EXISTS idx_captp_handoffs_recipient_status
             ON captp_handoffs (to_discord_id, status, issued_at DESC)",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS identity_held_credentials (
                credential_id TEXT PRIMARY KEY,
                discord_id TEXT NOT NULL,
                holder_cell_id TEXT NOT NULL,
                issuer_cell_id TEXT NOT NULL,
                schema TEXT NOT NULL,
                issued_at INTEGER NOT NULL,
                turn_hash TEXT,
                encoded_credential TEXT NOT NULL,
                attributes_json TEXT NOT NULL,
                created_at INTEGER NOT NULL
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE INDEX IF NOT EXISTS idx_identity_held_credentials_holder
             ON identity_held_credentials (discord_id, holder_cell_id, issued_at DESC)",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS identity_presentations (
                request_id TEXT PRIMARY KEY,
                verifier_discord_id TEXT NOT NULL,
                subject_discord_id TEXT NOT NULL,
                subject_cell_id TEXT NOT NULL,
                predicate TEXT NOT NULL,
                status TEXT NOT NULL,
                credential_id TEXT,
                presentation_json TEXT NOT NULL,
                created_at INTEGER NOT NULL
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE INDEX IF NOT EXISTS idx_identity_presentations_subject
             ON identity_presentations (subject_discord_id, created_at DESC)",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS captp_exports (
                cell_id TEXT PRIMARY KEY,
                sturdy_uri TEXT NOT NULL,
                shared_with TEXT,
                exported_at INTEGER NOT NULL,
                revoked INTEGER NOT NULL DEFAULT 0
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS captp_held_refs (
                cell_id TEXT PRIMARY KEY,
                sturdy_uri TEXT NOT NULL,
                label TEXT,
                shared_by TEXT,
                acquired_at INTEGER NOT NULL,
                live INTEGER NOT NULL DEFAULT 1
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS captp_local_handoffs (
                token_id TEXT PRIMARY KEY,
                cell_id TEXT NOT NULL,
                sturdy_uri TEXT NOT NULL,
                recipient_cell_id TEXT NOT NULL,
                local_signature TEXT NOT NULL,
                status TEXT NOT NULL,
                created_at INTEGER NOT NULL,
                redeemed_at INTEGER
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE INDEX IF NOT EXISTS idx_captp_local_handoffs_cell_status
             ON captp_local_handoffs (cell_id, status, created_at DESC)",
        )
        .execute(&pool)
        .await?;

        // ─── DreggNet Cloud: semi-private per-user channels ──────────────────
        // A user's own (semi-)private Discord channel, gated to them + admin,
        // bound to THEIR dregg cell. The channel is the surface from which the
        // user drives their own confined Hermes. `channel_id` is the Discord
        // snowflake (the unique key); `cell_id` is the user's custodial cell.
        sqlx::query(
            "CREATE TABLE IF NOT EXISTS user_channels (
                channel_id TEXT PRIMARY KEY,
                discord_id TEXT NOT NULL,
                guild_id TEXT NOT NULL,
                cell_id TEXT NOT NULL,
                status TEXT NOT NULL DEFAULT 'active',
                created_at INTEGER NOT NULL
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE INDEX IF NOT EXISTS idx_user_channels_discord
             ON user_channels (discord_id, created_at DESC)",
        )
        .execute(&pool)
        .await?;

        // ─── DreggNet Cloud: per-channel Hermes activity ─────────────────────
        // Every message that drives a user's Hermes leaves a record of the
        // cap-gated verdict: the tool/kind, whether the gateway admitted it, the
        // receipt hash (proof the metered turn committed on the verified
        // executor), the remaining rate budget, and — on refusal — the leg that
        // bit. This is the per-channel agent ledger the admin portal monitors.
        sqlx::query(
            "CREATE TABLE IF NOT EXISTS hermes_activity (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                discord_id TEXT NOT NULL,
                channel_id TEXT NOT NULL,
                prompt TEXT NOT NULL,
                tool TEXT NOT NULL,
                kind TEXT NOT NULL,
                allowed INTEGER NOT NULL,
                receipt TEXT,
                remaining INTEGER,
                reason TEXT,
                created_at INTEGER NOT NULL
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE INDEX IF NOT EXISTS idx_hermes_activity_recent
             ON hermes_activity (created_at DESC)",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE INDEX IF NOT EXISTS idx_hermes_activity_user
             ON hermes_activity (discord_id, created_at DESC)",
        )
        .execute(&pool)
        .await?;

        // ─── BYO-LLM-keys: per-user ported-in provider key, ENCRYPTED AT REST ─
        // The plaintext key NEVER lands here: only the AEAD nonce + ciphertext
        // (sealed under a key derived from the bot secret ‖ the user's id; see
        // `crate::key_vault`). The row also carries the user's chosen provider +
        // default model and the metering policy (token budget + rate). Revoke is
        // a DELETE of this row.
        sqlx::query(
            "CREATE TABLE IF NOT EXISTS user_llm_keys (
                discord_id TEXT PRIMARY KEY,
                provider TEXT NOT NULL,
                model TEXT NOT NULL DEFAULT '',
                nonce_b64 TEXT NOT NULL,
                ciphertext_b64 TEXT NOT NULL,
                token_budget INTEGER NOT NULL,
                rate_limit INTEGER NOT NULL,
                created_at INTEGER NOT NULL,
                updated_at INTEGER NOT NULL
            )",
        )
        .execute(&pool)
        .await?;

        // The community DUNGEON LIBRARY — authored `.dungeon` worlds, stored as SOURCE (never a
        // cached binary shape; every load re-parses fail-closed). Provenance is an AUTHOR LABEL:
        // the author's Discord id + their derived cipherclerk Ed25519 public key hex. This is NOT
        // a signed attestation — it records who published, it does not cryptographically prove the
        // source was signed by that key (see `commands::fiction`). See migrations/003_dungeon_worlds.sql.
        sqlx::query(
            "CREATE TABLE IF NOT EXISTS dungeon_worlds (
                name TEXT PRIMARY KEY,
                display_name TEXT NOT NULL,
                source TEXT NOT NULL,
                author_discord_id TEXT NOT NULL,
                author_pubkey TEXT NOT NULL,
                validates_clean INTEGER NOT NULL,
                room_count INTEGER NOT NULL,
                created_at INTEGER NOT NULL
            )",
        )
        .execute(&pool)
        .await?;

        // ─── $DREGG payment credits (dregg-pay CreditStore backing) ──────────
        // Per-user run-credit balance, the idempotency ledger of credited payment
        // references, and the user→deposit-index map. Credits survive restart. See
        // migrations/004_dregg_pay.sql.
        sqlx::query(
            "CREATE TABLE IF NOT EXISTS pay_credits (
                user    TEXT PRIMARY KEY,
                credits INTEGER NOT NULL DEFAULT 0
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS pay_processed (
                reference TEXT PRIMARY KEY
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS pay_deposit_index (
                user            TEXT PRIMARY KEY,
                deposit_index   INTEGER NOT NULL,
                deposit_address TEXT NOT NULL,
                assigned_at     INTEGER NOT NULL
            )",
        )
        .execute(&pool)
        .await?;

        // ─── The two-balance TREASURY (dregg-pay TreasuryStore backing) ──────
        // Detected game revenue lands here: a USDC payment fuels `usdc` (the FUEL
        // tank, burned per real-AI run and fail-closed on empty), a $DREGG payment
        // grows `dregg` (the illiquid PILE). One durable row so the treasury's
        // dual-asset accounting survives a process restart, exactly like the credit
        // ledger. See `pay::SqliteTreasuryStore`.
        sqlx::query(
            "CREATE TABLE IF NOT EXISTS pay_treasury (
                id    INTEGER PRIMARY KEY CHECK (id = 0),
                usdc  INTEGER NOT NULL DEFAULT 0,
                dregg INTEGER NOT NULL DEFAULT 0
            )",
        )
        .execute(&pool)
        .await?;
        sqlx::query("INSERT OR IGNORE INTO pay_treasury (id, usdc, dregg) VALUES (0, 0, 0)")
            .execute(&pool)
            .await?;

        // ─── UGC gallery (commands::gallery GalleryStore backing) ────────────
        // The durable backing of the `/gallery` universe registry: published
        // universes (their reproducible PUBLIC source — never a cached world)
        // and accepted completions (the player + move sequence — never a trusted
        // receipt blob). Both are re-verified by REPLAY on boot (see
        // `commands::gallery::load_registry`), so a tampered row cannot resurrect
        // a cheat. See migrations/005_ugc_gallery.sql.
        sqlx::query(
            "CREATE TABLE IF NOT EXISTS ugc_universes (
                id_hex         TEXT PRIMARY KEY,
                kind           TEXT NOT NULL,
                name           TEXT NOT NULL,
                author         TEXT NOT NULL,
                source         TEXT NOT NULL,
                epoch_hex      TEXT,
                win_json       TEXT NOT NULL,
                parent_id_hex  TEXT,
                author_key_hex TEXT,
                author_sig_hex TEXT
            )",
        )
        .execute(&pool)
        .await?;

        // Additive columns for a pre-existing DB (verified author identity + remix
        // lineage; see migrations/007_ugc_author_lineage.sql). `ADD COLUMN` errors if the
        // column already exists, so each is best-effort — ignore the duplicate-column error.
        for add in [
            "ALTER TABLE ugc_universes ADD COLUMN parent_id_hex TEXT",
            "ALTER TABLE ugc_universes ADD COLUMN author_key_hex TEXT",
            "ALTER TABLE ugc_universes ADD COLUMN author_sig_hex TEXT",
        ] {
            let _ = sqlx::query(add).execute(&pool).await;
        }

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS ugc_completions (
                key_hex         TEXT PRIMARY KEY,
                universe_id_hex TEXT NOT NULL,
                player          TEXT NOT NULL,
                moves_json      TEXT NOT NULL,
                claimed_turns   INTEGER NOT NULL
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE INDEX IF NOT EXISTS idx_ugc_completions_universe
             ON ugc_completions (universe_id_hex)",
        )
        .execute(&pool)
        .await?;

        // ─── Persistent leveling characters (character::CharacterStore backing) ──
        // A player's leveling character (xp/level/class/abilities) keyed by their stable
        // dregg identity hex, so it survives a process restart. XP + level-ups flow through
        // the REAL gated character turn (this only persists the resulting sheet); a tampered
        // row fails safe to a fresh L1 in `SqliteCharacterStore::load`. See
        // migrations/006_characters.sql.
        sqlx::query(
            "CREATE TABLE IF NOT EXISTS characters (
                identity_hex   TEXT PRIMARY KEY,
                xp             INTEGER NOT NULL DEFAULT 0,
                level          INTEGER NOT NULL DEFAULT 0,
                class          INTEGER NOT NULL DEFAULT 0,
                abilities_used INTEGER NOT NULL DEFAULT 0,
                dead           INTEGER NOT NULL DEFAULT 0,
                echoes         INTEGER NOT NULL DEFAULT 0,
                boon           INTEGER NOT NULL DEFAULT 0,
                updated_at     INTEGER NOT NULL DEFAULT 0
            )",
        )
        .execute(&pool)
        .await?;

        // Additive columns for a pre-existing DB. The HARDCORE death flag (a `/descent` permadeath
        // character's `WriteOnce`-final death must carry across restart), then the META-CURRENCY:
        // `echoes` (the roguelite-retention accrual, granted only on a real death) and `boon` (the
        // persistent `WriteOnce` unlock a next run starts holding). All three MUST survive restart or
        // a returning player's meta-progression silently resets. `ADD COLUMN` errors if the column
        // already exists, so each is best-effort — ignore the duplicate-column error. See
        // migrations/008_character_meta_currency.sql.
        for add in [
            "ALTER TABLE characters ADD COLUMN dead INTEGER NOT NULL DEFAULT 0",
            "ALTER TABLE characters ADD COLUMN echoes INTEGER NOT NULL DEFAULT 0",
            "ALTER TABLE characters ADD COLUMN boon INTEGER NOT NULL DEFAULT 0",
        ] {
            let _ = sqlx::query(add).execute(&pool).await;
        }

        // ─── The /descent no-cheat leaderboard board (commands::descent DescentBoardStore) ──
        // The durable backing of today's Descent board. Like the UGC gallery it stores ONLY the
        // reproducible PUBLIC input: a day-universe's committed beacon SEED (never a cached world)
        // and a winning run's MOVE SEQUENCE + player + claimed turns (never a trusted receipt blob).
        // On boot `commands::descent::load_board` regenerates each day-world from its seed and
        // REPLAYS every completion through the real no-cheat gate — so a tampered row (a losing
        // move line, a lied turn count, or a mismatched seed) cannot resurrect a cheat onto the
        // board. See migrations/009_descent_board.sql.
        sqlx::query(
            "CREATE TABLE IF NOT EXISTS descent_universes (
                id_hex   TEXT PRIMARY KEY,
                author   TEXT NOT NULL,
                seed_hex TEXT NOT NULL
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS descent_completions (
                key_hex         TEXT PRIMARY KEY,
                universe_id_hex TEXT NOT NULL,
                player          TEXT NOT NULL,
                moves_json      TEXT NOT NULL,
                claimed_turns   INTEGER NOT NULL
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE INDEX IF NOT EXISTS idx_descent_completions_universe
             ON descent_completions (universe_id_hex)",
        )
        .execute(&pool)
        .await?;

        // ─── The per-identity RPG world sessions (commands::rpg_world SessionResumeStore) ──
        // The durable backing of each player's PERSISTENT `/play` RPG world (trade / craft /
        // inventory / guild / companion / tavern / party / cheevos). Like the descent board it
        // stores ONLY the reproducible PUBLIC input: a session's open (its seed) and its ordered
        // LANDED advances — never a trusted state blob. On the player's first touch after boot
        // the host REPLAYS these logs through the real executor (a tampered row is refused on
        // re-drive and the session fails closed rather than reopening to a forged state).
        sqlx::query(
            "CREATE TABLE IF NOT EXISTS rpg_sessions (
                player     TEXT NOT NULL,
                key        TEXT NOT NULL,
                session_id TEXT NOT NULL,
                seed       TEXT NOT NULL,
                PRIMARY KEY (player, key, session_id)
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS rpg_session_moves (
                player     TEXT NOT NULL,
                key        TEXT NOT NULL,
                session_id TEXT NOT NULL,
                idx        INTEGER NOT NULL,
                label      TEXT NOT NULL,
                turn       TEXT NOT NULL,
                arg        INTEGER NOT NULL,
                enabled    INTEGER NOT NULL,
                has_text   INTEGER NOT NULL,
                text       TEXT NOT NULL,
                actor      TEXT NOT NULL,
                trust      TEXT NOT NULL,
                PRIMARY KEY (player, key, session_id, idx)
            )",
        )
        .execute(&pool)
        .await?;

        Ok(Self { pool })
    }

    // ─── $DREGG payment credits (dregg-pay CreditStore backing) ─────────────

    /// A user's persisted run-credit balance (0 if none). The read half of
    /// `dregg_pay::CreditStore::balance`.
    pub async fn pay_credit_balance(&self, user: &str) -> Result<u64, sqlx::Error> {
        let row: Option<(i64,)> = sqlx::query_as("SELECT credits FROM pay_credits WHERE user = ?")
            .bind(user)
            .fetch_optional(&self.pool)
            .await?;
        Ok(row.map(|(c,)| c.max(0) as u64).unwrap_or(0))
    }

    /// Set a user's run-credit balance (the write half of
    /// `dregg_pay::CreditStore::set_balance`). Upsert by user.
    pub async fn pay_set_credit_balance(
        &self,
        user: &str,
        credits: u64,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT INTO pay_credits (user, credits) VALUES (?, ?)
             ON CONFLICT(user) DO UPDATE SET credits = excluded.credits",
        )
        .bind(user)
        .bind(credits as i64)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    /// Whether a payment reference has already been credited (idempotency key).
    pub async fn pay_is_processed(&self, reference: &str) -> Result<bool, sqlx::Error> {
        let row: Option<(String,)> =
            sqlx::query_as("SELECT reference FROM pay_processed WHERE reference = ?")
                .bind(reference)
                .fetch_optional(&self.pool)
                .await?;
        Ok(row.is_some())
    }

    /// Record a payment reference as credited (idempotency key). `INSERT OR IGNORE`
    /// so marking the same reference twice is harmless.
    pub async fn pay_mark_processed(&self, reference: &str) -> Result<(), sqlx::Error> {
        sqlx::query("INSERT OR IGNORE INTO pay_processed (reference) VALUES (?)")
            .bind(reference)
            .execute(&self.pool)
            .await?;
        Ok(())
    }

    // ─── The two-balance treasury (dregg-pay TreasuryStore backing) ─────────

    /// The treasury's persisted USDC balance (the FUEL tank), atomic USDC units.
    /// The read half of `dregg_pay::TreasuryStore::usdc_balance`.
    pub async fn pay_treasury_usdc(&self) -> Result<u64, sqlx::Error> {
        let row: Option<(i64,)> = sqlx::query_as("SELECT usdc FROM pay_treasury WHERE id = 0")
            .fetch_optional(&self.pool)
            .await?;
        Ok(row.map(|(v,)| v.max(0) as u64).unwrap_or(0))
    }

    /// The treasury's persisted `$DREGG` balance (the PILE), atomic `$DREGG` units.
    /// The read half of `dregg_pay::TreasuryStore::dregg_balance`.
    pub async fn pay_treasury_dregg(&self) -> Result<u64, sqlx::Error> {
        let row: Option<(i64,)> = sqlx::query_as("SELECT dregg FROM pay_treasury WHERE id = 0")
            .fetch_optional(&self.pool)
            .await?;
        Ok(row.map(|(v,)| v.max(0) as u64).unwrap_or(0))
    }

    /// Set the treasury's USDC balance (the write half of
    /// `dregg_pay::TreasuryStore::set_usdc_balance`). Upsert of the single row.
    pub async fn pay_treasury_set_usdc(&self, v: u64) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT INTO pay_treasury (id, usdc, dregg) VALUES (0, ?, 0)
             ON CONFLICT(id) DO UPDATE SET usdc = excluded.usdc",
        )
        .bind(v as i64)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    /// Set the treasury's `$DREGG` balance (the write half of
    /// `dregg_pay::TreasuryStore::set_dregg_balance`). Upsert of the single row.
    pub async fn pay_treasury_set_dregg(&self, v: u64) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT INTO pay_treasury (id, usdc, dregg) VALUES (0, 0, ?)
             ON CONFLICT(id) DO UPDATE SET dregg = excluded.dregg",
        )
        .bind(v as i64)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    // ─── Persistent leveling characters (character::CharacterStore backing) ──────

    /// Load a player's persisted character slots
    /// `(xp, level, class, abilities_used, dead, echoes, boon)` by their dregg identity hex, or
    /// `None` if no row exists (a new player). The `dead` slot is the HARDCORE death flag (`1` once
    /// perished); `echoes` / `boon` are the META-CURRENCY (the accrued roguelite currency + the
    /// claimed `WriteOnce` unlock) — all three carry across restart. The well-formedness / fail-safe
    /// check lives in `crate::character_store::SqliteCharacterStore::load`.
    pub async fn character_load(
        &self,
        identity_hex: &str,
    ) -> Result<Option<(u64, u64, u64, u64, u64, u64, u64)>, sqlx::Error> {
        let row: Option<(i64, i64, i64, i64, i64, i64, i64)> = sqlx::query_as(
            "SELECT xp, level, class, abilities_used, dead, echoes, boon
             FROM characters WHERE identity_hex = ?",
        )
        .bind(identity_hex)
        .fetch_optional(&self.pool)
        .await?;
        Ok(
            row.map(|(xp, level, class, abilities, dead, echoes, boon)| {
                (
                    xp.max(0) as u64,
                    level.max(0) as u64,
                    class.max(0) as u64,
                    abilities.max(0) as u64,
                    dead.max(0) as u64,
                    echoes.max(0) as u64,
                    boon.max(0) as u64,
                )
            }),
        )
    }

    /// Persist a player's character sheet by their dregg identity hex (upsert), including the
    /// HARDCORE `dead` flag and the META-CURRENCY (`echoes` / `boon`). The carried state a later
    /// [`character_load`](Self::character_load) returns.
    #[allow(clippy::too_many_arguments)]
    pub async fn character_save(
        &self,
        identity_hex: &str,
        xp: u64,
        level: u64,
        class: u64,
        abilities_used: u64,
        dead: u64,
        echoes: u64,
        boon: u64,
        updated_at: i64,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT INTO characters
                (identity_hex, xp, level, class, abilities_used, dead, echoes, boon, updated_at)
             VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
             ON CONFLICT(identity_hex) DO UPDATE SET
                 xp = excluded.xp,
                 level = excluded.level,
                 class = excluded.class,
                 abilities_used = excluded.abilities_used,
                 dead = excluded.dead,
                 echoes = excluded.echoes,
                 boon = excluded.boon,
                 updated_at = excluded.updated_at",
        )
        .bind(identity_hex)
        .bind(xp as i64)
        .bind(level as i64)
        .bind(class as i64)
        .bind(abilities_used as i64)
        .bind(dead as i64)
        .bind(echoes as i64)
        .bind(boon as i64)
        .bind(updated_at)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    /// The persisted deposit index for a user, if one was explicitly assigned.
    pub async fn pay_get_deposit_index(
        &self,
        user: &str,
    ) -> Result<Option<(u32, String)>, sqlx::Error> {
        let row: Option<(i64, String)> = sqlx::query_as(
            "SELECT deposit_index, deposit_address FROM pay_deposit_index WHERE user = ?",
        )
        .bind(user)
        .fetch_optional(&self.pool)
        .await?;
        Ok(row.map(|(i, a)| (i as u32, a)))
    }

    /// Persist a user→deposit-index assignment (idempotent; first assignment wins so a
    /// user's deposit address is stable). `deposit_address` is the base58 address cache.
    pub async fn pay_assign_deposit_index(
        &self,
        user: &str,
        deposit_index: u32,
        deposit_address: &str,
        assigned_at: i64,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT OR IGNORE INTO pay_deposit_index
                (user, deposit_index, deposit_address, assigned_at)
             VALUES (?, ?, ?, ?)",
        )
        .bind(user)
        .bind(deposit_index as i64)
        .bind(deposit_address)
        .bind(assigned_at)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    // ─── UGC gallery (commands::gallery GalleryStore backing) ───────────────

    /// Persist a published universe's reproducible public source (idempotent by
    /// `id_hex` — `INSERT OR IGNORE`, matching the store trait's idempotency contract).
    pub async fn persist_ugc_universe(&self, row: &UgcUniverseRow) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT OR IGNORE INTO ugc_universes
                (id_hex, kind, name, author, source, epoch_hex, win_json,
                 parent_id_hex, author_key_hex, author_sig_hex)
             VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
        )
        .bind(&row.id_hex)
        .bind(&row.kind)
        .bind(&row.name)
        .bind(&row.author)
        .bind(&row.source)
        .bind(&row.epoch_hex)
        .bind(&row.win_json)
        .bind(&row.parent_id_hex)
        .bind(&row.author_key_hex)
        .bind(&row.author_sig_hex)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    /// Persist an accepted completion (idempotent by `key_hex` — `INSERT OR IGNORE`).
    pub async fn persist_ugc_completion(&self, row: &UgcCompletionRow) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT OR IGNORE INTO ugc_completions
                (key_hex, universe_id_hex, player, moves_json, claimed_turns)
             VALUES (?, ?, ?, ?, ?)",
        )
        .bind(&row.key_hex)
        .bind(&row.universe_id_hex)
        .bind(&row.player)
        .bind(&row.moves_json)
        .bind(row.claimed_turns)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    /// Every persisted universe (the boot-replay source).
    pub async fn list_ugc_universes(&self) -> Result<Vec<UgcUniverseRow>, sqlx::Error> {
        let rows = sqlx::query(
            "SELECT id_hex, kind, name, author, source, epoch_hex, win_json,
                    parent_id_hex, author_key_hex, author_sig_hex
             FROM ugc_universes",
        )
        .fetch_all(&self.pool)
        .await?;
        Ok(rows
            .iter()
            .map(|row| UgcUniverseRow {
                id_hex: row.get("id_hex"),
                kind: row.get("kind"),
                name: row.get("name"),
                author: row.get("author"),
                source: row.get("source"),
                epoch_hex: row.get("epoch_hex"),
                win_json: row.get("win_json"),
                parent_id_hex: row.get("parent_id_hex"),
                author_key_hex: row.get("author_key_hex"),
                author_sig_hex: row.get("author_sig_hex"),
            })
            .collect())
    }

    /// Every persisted completion (re-verified by replay on boot).
    pub async fn list_ugc_completions(&self) -> Result<Vec<UgcCompletionRow>, sqlx::Error> {
        let rows = sqlx::query(
            "SELECT key_hex, universe_id_hex, player, moves_json, claimed_turns
             FROM ugc_completions",
        )
        .fetch_all(&self.pool)
        .await?;
        Ok(rows
            .iter()
            .map(|row| UgcCompletionRow {
                key_hex: row.get("key_hex"),
                universe_id_hex: row.get("universe_id_hex"),
                player: row.get("player"),
                moves_json: row.get("moves_json"),
                claimed_turns: row.get("claimed_turns"),
            })
            .collect())
    }

    // ─── The /descent no-cheat leaderboard (commands::descent DescentBoardStore) ────

    /// Persist a day-universe's reproducible descriptor (its committed beacon seed + author),
    /// idempotent by content address (`INSERT OR IGNORE` — matching the store's idempotency
    /// contract). The world is regenerated byte-for-byte from the seed on boot.
    pub async fn persist_descent_universe(
        &self,
        row: &DescentUniverseRow,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT OR IGNORE INTO descent_universes (id_hex, author, seed_hex)
             VALUES (?, ?, ?)",
        )
        .bind(&row.id_hex)
        .bind(&row.author)
        .bind(&row.seed_hex)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    /// Persist an accepted board completion (player + move sequence + claimed turns), idempotent by
    /// `key_hex` (`INSERT OR IGNORE`). Re-verified by replay on boot.
    pub async fn persist_descent_completion(
        &self,
        row: &DescentCompletionRow,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT OR IGNORE INTO descent_completions
                (key_hex, universe_id_hex, player, moves_json, claimed_turns)
             VALUES (?, ?, ?, ?, ?)",
        )
        .bind(&row.key_hex)
        .bind(&row.universe_id_hex)
        .bind(&row.player)
        .bind(&row.moves_json)
        .bind(row.claimed_turns)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    /// Every persisted day-universe (the boot-replay source).
    pub async fn list_descent_universes(&self) -> Result<Vec<DescentUniverseRow>, sqlx::Error> {
        let rows = sqlx::query("SELECT id_hex, author, seed_hex FROM descent_universes")
            .fetch_all(&self.pool)
            .await?;
        Ok(rows
            .iter()
            .map(|row| DescentUniverseRow {
                id_hex: row.get("id_hex"),
                author: row.get("author"),
                seed_hex: row.get("seed_hex"),
            })
            .collect())
    }

    /// Every persisted board completion (re-verified by replay on boot).
    pub async fn list_descent_completions(&self) -> Result<Vec<DescentCompletionRow>, sqlx::Error> {
        let rows = sqlx::query(
            "SELECT key_hex, universe_id_hex, player, moves_json, claimed_turns
             FROM descent_completions",
        )
        .fetch_all(&self.pool)
        .await?;
        Ok(rows
            .iter()
            .map(|row| DescentCompletionRow {
                key_hex: row.get("key_hex"),
                universe_id_hex: row.get("universe_id_hex"),
                player: row.get("player"),
                moves_json: row.get("moves_json"),
                claimed_turns: row.get("claimed_turns"),
            })
            .collect())
    }

    // ─── The per-identity RPG world sessions (commands::rpg_world SessionResumeStore) ────

    /// Record a player's RPG session OPEN — its replay seed (`"-"` for the offering default).
    /// Idempotent by PK (`INSERT OR IGNORE`), so a re-open keeps the recorded advances.
    pub async fn rpg_session_open(
        &self,
        player: &str,
        key: &str,
        session_id: &str,
        seed: &str,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT OR IGNORE INTO rpg_sessions (player, key, session_id, seed)
             VALUES (?, ?, ?, ?)",
        )
        .bind(player)
        .bind(key)
        .bind(session_id)
        .bind(seed)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    /// Append one LANDED advance to a player's RPG session log. `idx` is assigned as the current
    /// move count (the writer is a single dedicated host thread per process, so the append is
    /// sequential; the PK still refuses a duplicate index if it ever were not).
    pub async fn rpg_session_record_move(
        &self,
        player: &str,
        key: &str,
        session_id: &str,
        m: &RpgMoveRow,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT OR IGNORE INTO rpg_session_moves
                (player, key, session_id, idx, label, turn, arg, enabled, has_text, text, actor, trust)
             VALUES (?, ?, ?,
                (SELECT COUNT(*) FROM rpg_session_moves
                 WHERE player = ? AND key = ? AND session_id = ?),
                ?, ?, ?, ?, ?, ?, ?, ?)",
        )
        .bind(player)
        .bind(key)
        .bind(session_id)
        .bind(player)
        .bind(key)
        .bind(session_id)
        .bind(&m.label)
        .bind(&m.turn)
        .bind(m.arg)
        .bind(m.enabled)
        .bind(m.has_text)
        .bind(&m.text)
        .bind(&m.actor)
        .bind(&m.trust)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    /// Drop a player's RPG session log (open + moves) — it will not be resumed on the next boot.
    pub async fn rpg_session_forget(
        &self,
        player: &str,
        key: &str,
        session_id: &str,
    ) -> Result<(), sqlx::Error> {
        sqlx::query("DELETE FROM rpg_sessions WHERE player = ? AND key = ? AND session_id = ?")
            .bind(player)
            .bind(key)
            .bind(session_id)
            .execute(&self.pool)
            .await?;
        sqlx::query(
            "DELETE FROM rpg_session_moves WHERE player = ? AND key = ? AND session_id = ?",
        )
        .bind(player)
        .bind(key)
        .bind(session_id)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    /// A player's recorded RPG session opens (key + session id + seed), for boot replay.
    pub async fn rpg_sessions_of(&self, player: &str) -> Result<Vec<RpgSessionRow>, sqlx::Error> {
        let rows = sqlx::query("SELECT key, session_id, seed FROM rpg_sessions WHERE player = ?")
            .bind(player)
            .fetch_all(&self.pool)
            .await?;
        Ok(rows
            .iter()
            .map(|row| RpgSessionRow {
                key: row.get("key"),
                session_id: row.get("session_id"),
                seed: row.get("seed"),
            })
            .collect())
    }

    /// One RPG session's recorded open, if any.
    pub async fn rpg_session_of(
        &self,
        player: &str,
        key: &str,
        session_id: &str,
    ) -> Result<Option<RpgSessionRow>, sqlx::Error> {
        let row = sqlx::query(
            "SELECT key, session_id, seed FROM rpg_sessions
             WHERE player = ? AND key = ? AND session_id = ?",
        )
        .bind(player)
        .bind(key)
        .bind(session_id)
        .fetch_optional(&self.pool)
        .await?;
        Ok(row.map(|row| RpgSessionRow {
            key: row.get("key"),
            session_id: row.get("session_id"),
            seed: row.get("seed"),
        }))
    }

    /// One RPG session's ordered landed advances.
    pub async fn rpg_session_moves(
        &self,
        player: &str,
        key: &str,
        session_id: &str,
    ) -> Result<Vec<RpgMoveRow>, sqlx::Error> {
        let rows = sqlx::query(
            "SELECT label, turn, arg, enabled, has_text, text, actor, trust
             FROM rpg_session_moves
             WHERE player = ? AND key = ? AND session_id = ?
             ORDER BY idx ASC",
        )
        .bind(player)
        .bind(key)
        .bind(session_id)
        .fetch_all(&self.pool)
        .await?;
        Ok(rows
            .iter()
            .map(|row| RpgMoveRow {
                label: row.get("label"),
                turn: row.get("turn"),
                arg: row.get("arg"),
                enabled: row.get("enabled"),
                has_text: row.get("has_text"),
                text: row.get("text"),
                actor: row.get("actor"),
                trust: row.get("trust"),
            })
            .collect())
    }

    // ─── Dungeon world library ──────────────────────────────────────────────

    /// Publish (insert or replace) an authored dungeon world into the community library. The
    /// SOURCE is stored verbatim; callers re-parse it on load (never a cached binary shape).
    /// `author_pubkey` is the publisher's derived cipherclerk public key hex — an author LABEL,
    /// not a signature over the source.
    pub async fn publish_dungeon_world(&self, rec: &DungeonWorldRecord) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT OR REPLACE INTO dungeon_worlds
                (name, display_name, source, author_discord_id, author_pubkey, validates_clean, room_count, created_at)
             VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
        )
        .bind(&rec.name)
        .bind(&rec.display_name)
        .bind(&rec.source)
        .bind(&rec.author_discord_id)
        .bind(&rec.author_pubkey)
        .bind(rec.validates_clean as i64)
        .bind(rec.room_count)
        .bind(rec.created_at)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    /// List every published world (newest first), for `/dungeon library`.
    pub async fn list_dungeon_worlds(&self) -> Result<Vec<DungeonWorldRecord>, sqlx::Error> {
        let rows = sqlx::query(
            "SELECT name, display_name, source, author_discord_id, author_pubkey, validates_clean, room_count, created_at
             FROM dungeon_worlds ORDER BY created_at DESC",
        )
        .fetch_all(&self.pool)
        .await?;
        Ok(rows.iter().map(row_to_world).collect())
    }

    /// Fetch one published world by its library name (for `/dungeon start <name>`). The caller
    /// re-parses `.source` fail-closed.
    pub async fn get_dungeon_world(
        &self,
        name: &str,
    ) -> Result<Option<DungeonWorldRecord>, sqlx::Error> {
        let row = sqlx::query(
            "SELECT name, display_name, source, author_discord_id, author_pubkey, validates_clean, room_count, created_at
             FROM dungeon_worlds WHERE name = ?",
        )
        .bind(name)
        .fetch_optional(&self.pool)
        .await?;
        Ok(row.as_ref().map(row_to_world))
    }

    // ─── User / cclerk methods ──────────────────────────────────────────────

    /// Check if a user has a cclerk.
    pub async fn user_exists(&self, user_id: &str) -> Result<bool, sqlx::Error> {
        let row: Option<(String,)> =
            sqlx::query_as("SELECT cell_id FROM users WHERE discord_id = ?")
                .bind(user_id)
                .fetch_optional(&self.pool)
                .await?;
        Ok(row.is_some())
    }

    /// Get a user's cell_id.
    pub async fn get_cell_id(&self, discord_id: &str) -> Result<Option<String>, sqlx::Error> {
        Ok(self
            .get_user_identity(discord_id)
            .await?
            .map(|identity| identity.cell_id))
    }

    /// Get a user's full identity record.
    pub async fn get_user_identity(
        &self,
        discord_id: &str,
    ) -> Result<Option<UserIdentity>, sqlx::Error> {
        let row = sqlx::query(
            "SELECT cell_id, identity_mode, link_challenge FROM users WHERE discord_id = ?",
        )
        .bind(discord_id)
        .fetch_optional(&self.pool)
        .await?;

        Ok(row.map(|row| UserIdentity {
            cell_id: row.get("cell_id"),
            mode: IdentityMode::from_db(row.get::<String, _>("identity_mode").as_str()),
            link_challenge: row.get("link_challenge"),
        }))
    }

    /// Return all known user identities for read surfaces and dashboards.
    pub async fn list_user_identities(&self) -> Result<Vec<UserIdentity>, sqlx::Error> {
        let rows =
            sqlx::query("SELECT cell_id, identity_mode, link_challenge FROM users ORDER BY rowid")
                .fetch_all(&self.pool)
                .await?;

        Ok(rows
            .into_iter()
            .map(|row| UserIdentity {
                cell_id: row.get("cell_id"),
                mode: IdentityMode::from_db(row.get::<String, _>("identity_mode").as_str()),
                link_challenge: row.get("link_challenge"),
            })
            .collect())
    }

    /// Admin monitoring listing: `(discord_id, cell_id, identity_mode)` for every
    /// known user — the internal user↔cell mapping the admin portal surfaces.
    pub async fn list_users_admin(&self) -> Result<Vec<(String, String, String)>, sqlx::Error> {
        let rows =
            sqlx::query("SELECT discord_id, cell_id, identity_mode FROM users ORDER BY rowid")
                .fetch_all(&self.pool)
                .await?;
        Ok(rows
            .into_iter()
            .map(|row| {
                (
                    row.get::<String, _>("discord_id"),
                    row.get::<String, _>("cell_id"),
                    row.get::<String, _>("identity_mode"),
                )
            })
            .collect())
    }

    // ─── Activity feed methods ──────────────────────────────────────────────

    /// Get last processed block height for activity feed.
    pub async fn get_last_block_height(&self) -> Result<u64, sqlx::Error> {
        let row: Option<(String,)> =
            sqlx::query_as("SELECT value FROM kv WHERE key = 'last_block_height'")
                .fetch_optional(&self.pool)
                .await?;
        Ok(row.and_then(|(v,)| v.parse::<u64>().ok()).unwrap_or(0))
    }

    /// Set last processed block height.
    pub async fn set_last_block_height(&self, height: u64) -> Result<(), sqlx::Error> {
        sqlx::query("INSERT OR REPLACE INTO kv (key, value) VALUES ('last_block_height', ?)")
            .bind(height.to_string())
            .execute(&self.pool)
            .await?;
        Ok(())
    }

    /// Set the activity feed channel for a guild.
    pub async fn set_feed_channel(
        &self,
        guild_id: &str,
        channel_id: &str,
    ) -> Result<(), sqlx::Error> {
        sqlx::query("INSERT OR REPLACE INTO feed_channels (guild_id, channel_id) VALUES (?, ?)")
            .bind(guild_id)
            .bind(channel_id)
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

    // ─── Watch subscription methods ─────────────────────────────────────────

    /// Add a watch subscription.
    pub async fn add_watch(&self, discord_id: &str, cell_id: &str) -> Result<bool, sqlx::Error> {
        let result = sqlx::query("INSERT OR IGNORE INTO watchers (user_id, cell_id) VALUES (?, ?)")
            .bind(discord_id)
            .bind(cell_id)
            .execute(&self.pool)
            .await?;
        Ok(result.rows_affected() > 0)
    }

    /// Remove a watch subscription.
    pub async fn remove_watch(&self, discord_id: &str, cell_id: &str) -> Result<bool, sqlx::Error> {
        let result = sqlx::query("DELETE FROM watchers WHERE user_id = ? AND cell_id = ?")
            .bind(discord_id)
            .bind(cell_id)
            .execute(&self.pool)
            .await?;
        Ok(result.rows_affected() > 0)
    }

    /// Get users watching a specific cell.
    pub async fn get_watchers_for_cell(&self, cell_id: &str) -> Result<Vec<String>, sqlx::Error> {
        let rows: Vec<(String,)> = sqlx::query_as("SELECT user_id FROM watchers WHERE cell_id = ?")
            .bind(cell_id)
            .fetch_all(&self.pool)
            .await?;
        Ok(rows.into_iter().map(|(id,)| id).collect())
    }

    // ─── Cipherclerk / user registration ────────────────────────────────────────────

    /// Register a user's cell_id.
    pub async fn register_user(&self, discord_id: &str, cell_id: &str) -> Result<(), sqlx::Error> {
        self.register_user_with_mode(discord_id, cell_id, IdentityMode::Hosted, None)
            .await
    }

    /// Register a user's cell_id with explicit identity mode metadata.
    pub async fn register_user_with_mode(
        &self,
        discord_id: &str,
        cell_id: &str,
        mode: IdentityMode,
        link_challenge: Option<&str>,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT OR REPLACE INTO users (discord_id, cell_id, identity_mode, link_challenge) VALUES (?, ?, ?, ?)",
        )
            .bind(discord_id)
            .bind(cell_id)
            .bind(mode.as_str())
            .bind(link_challenge)
            .execute(&self.pool)
            .await?;
        Ok(())
    }

    /// Start an external identity link. This does not mark the identity usable
    /// until a later proof verifier promotes it to `external_verified`.
    pub async fn create_pending_external_link(
        &self,
        discord_id: &str,
        cell_id: &str,
        challenge: &str,
    ) -> Result<(), sqlx::Error> {
        self.register_user_with_mode(
            discord_id,
            cell_id,
            IdentityMode::ExternalPending,
            Some(challenge),
        )
        .await
    }

    /// Unlink a user's cell_id (remove from users table).
    pub async fn unlink_user(&self, discord_id: &str) -> Result<(), sqlx::Error> {
        sqlx::query("DELETE FROM users WHERE discord_id = ?")
            .bind(discord_id)
            .execute(&self.pool)
            .await?;
        Ok(())
    }

    // ─── Identity holder store ───────────────────────────────────────────

    pub async fn store_held_credential(
        &self,
        discord_id: &str,
        holder_cell_id: &str,
        issuer_cell_id: &str,
        credential_id: &str,
        schema: &str,
        issued_at: i64,
        turn_hash: Option<&str>,
        encoded_credential: &str,
        attributes_json: &str,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT OR REPLACE INTO identity_held_credentials
             (credential_id, discord_id, holder_cell_id, issuer_cell_id, schema, issued_at, turn_hash, encoded_credential, attributes_json, created_at)
             VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
        )
        .bind(credential_id)
        .bind(discord_id)
        .bind(holder_cell_id)
        .bind(issuer_cell_id)
        .bind(schema)
        .bind(issued_at)
        .bind(turn_hash)
        .bind(encoded_credential)
        .bind(attributes_json)
        .bind(chrono_now())
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    pub async fn list_held_credentials(
        &self,
        discord_id: &str,
        holder_cell_id: &str,
        limit: u32,
    ) -> Result<Vec<HeldCredential>, sqlx::Error> {
        let rows = sqlx::query(
            "SELECT credential_id, discord_id, holder_cell_id, issuer_cell_id, schema, issued_at, turn_hash, encoded_credential, attributes_json, created_at
             FROM identity_held_credentials
             WHERE discord_id = ? AND holder_cell_id = ?
             ORDER BY issued_at DESC, created_at DESC
             LIMIT ?",
        )
        .bind(discord_id)
        .bind(holder_cell_id)
        .bind(limit)
        .fetch_all(&self.pool)
        .await?;
        Ok(rows.into_iter().map(held_credential_from_row).collect())
    }

    pub async fn find_held_credential_for_predicate(
        &self,
        discord_id: &str,
        holder_cell_id: &str,
        predicate: &str,
    ) -> Result<Option<HeldCredential>, sqlx::Error> {
        let schema_hint = predicate
            .split(|c: char| !c.is_ascii_alphanumeric() && c != '_' && c != '-')
            .find(|part| !part.is_empty());
        let row = if let Some(hint) = schema_hint {
            sqlx::query(
                "SELECT credential_id, discord_id, holder_cell_id, issuer_cell_id, schema, issued_at, turn_hash, encoded_credential, attributes_json, created_at
                 FROM identity_held_credentials
                 WHERE discord_id = ? AND holder_cell_id = ?
                   AND (schema = ? OR attributes_json LIKE ?)
                 ORDER BY issued_at DESC, created_at DESC
                 LIMIT 1",
            )
            .bind(discord_id)
            .bind(holder_cell_id)
            .bind(hint)
            .bind(format!("%\"{hint}\"%"))
            .fetch_optional(&self.pool)
            .await?
        } else {
            None
        };

        if row.is_some() {
            return Ok(row.map(held_credential_from_row));
        }

        let row = sqlx::query(
            "SELECT credential_id, discord_id, holder_cell_id, issuer_cell_id, schema, issued_at, turn_hash, encoded_credential, attributes_json, created_at
             FROM identity_held_credentials
             WHERE discord_id = ? AND holder_cell_id = ?
             ORDER BY issued_at DESC, created_at DESC
             LIMIT 1",
        )
        .bind(discord_id)
        .bind(holder_cell_id)
        .fetch_optional(&self.pool)
        .await?;
        Ok(row.map(held_credential_from_row))
    }

    pub async fn create_identity_presentation(
        &self,
        verifier_discord_id: &str,
        subject_discord_id: &str,
        subject_cell_id: &str,
        predicate: &str,
        status: &str,
        credential_id: Option<&str>,
        presentation_json: &str,
    ) -> Result<CredentialPresentation, sqlx::Error> {
        let request_id = format!(
            "discord-proof-{}-{}",
            chrono_now(),
            short_local_hash(&format!(
                "{verifier_discord_id}:{subject_discord_id}:{predicate}"
            ))
        );
        let created_at = chrono_now();
        sqlx::query(
            "INSERT INTO identity_presentations
             (request_id, verifier_discord_id, subject_discord_id, subject_cell_id, predicate, status, credential_id, presentation_json, created_at)
             VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
        )
        .bind(&request_id)
        .bind(verifier_discord_id)
        .bind(subject_discord_id)
        .bind(subject_cell_id)
        .bind(predicate)
        .bind(status)
        .bind(credential_id)
        .bind(presentation_json)
        .bind(created_at)
        .execute(&self.pool)
        .await?;

        Ok(CredentialPresentation {
            request_id,
            verifier_discord_id: verifier_discord_id.to_string(),
            subject_discord_id: subject_discord_id.to_string(),
            subject_cell_id: subject_cell_id.to_string(),
            predicate: predicate.to_string(),
            status: status.to_string(),
            credential_id: credential_id.map(str::to_string),
            presentation_json: presentation_json.to_string(),
            created_at,
        })
    }

    // ─── Faucet rate limiting ───────────────────────────────────────────────────

    /// Get the timestamp of the user's last faucet claim. Returns None if never claimed.
    pub async fn get_last_faucet_claim(
        &self,
        discord_id: &str,
    ) -> Result<Option<i64>, sqlx::Error> {
        let row: Option<(String,)> = sqlx::query_as("SELECT value FROM kv WHERE key = ?")
            .bind(format!("faucet:{discord_id}"))
            .fetch_optional(&self.pool)
            .await?;
        Ok(row.and_then(|(v,)| v.parse::<i64>().ok()))
    }

    /// Record a faucet claim timestamp.
    pub async fn set_faucet_claim(
        &self,
        discord_id: &str,
        timestamp: i64,
    ) -> Result<(), sqlx::Error> {
        sqlx::query("INSERT OR REPLACE INTO kv (key, value) VALUES (?, ?)")
            .bind(format!("faucet:{discord_id}"))
            .bind(timestamp.to_string())
            .execute(&self.pool)
            .await?;
        Ok(())
    }

    // ─── Transaction history ────────────────────────────────────────────────────

    /// Record a transaction in the local ledger.
    pub async fn record_transaction(
        &self,
        from_discord_id: &str,
        to_discord_id: &str,
        amount: u64,
        tx_hash: &str,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT INTO transactions (from_user, to_user, amount, tx_hash, timestamp) VALUES (?, ?, ?, ?, ?)",
        )
        .bind(from_discord_id)
        .bind(to_discord_id)
        .bind(amount as i64)
        .bind(tx_hash)
        .bind(chrono_now())
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    /// Get recent transactions for a user (as sender or receiver).
    pub async fn get_user_transactions(
        &self,
        discord_id: &str,
        limit: u32,
    ) -> Result<Vec<TransactionRecord>, sqlx::Error> {
        let rows: Vec<TransactionRecord> = sqlx::query_as(
            "SELECT from_user, to_user, amount, tx_hash, timestamp FROM transactions WHERE from_user = ? OR to_user = ? ORDER BY timestamp DESC LIMIT ?",
        )
        .bind(discord_id)
        .bind(discord_id)
        .bind(limit)
        .fetch_all(&self.pool)
        .await?;
        Ok(rows)
    }

    /// Get recent transactions across all users.
    pub async fn get_recent_transactions(
        &self,
        limit: u32,
    ) -> Result<Vec<TransactionRecord>, sqlx::Error> {
        let rows: Vec<TransactionRecord> = sqlx::query_as(
            "SELECT from_user, to_user, amount, tx_hash, timestamp FROM transactions ORDER BY timestamp DESC LIMIT ?",
        )
        .bind(limit)
        .fetch_all(&self.pool)
        .await?;
        Ok(rows)
    }

    /// Get top holders (by number of faucet claims — proxy for balance in local ledger).
    pub async fn get_leaderboard(&self, limit: u32) -> Result<Vec<(String, i64)>, sqlx::Error> {
        let rows: Vec<(String, i64)> = sqlx::query_as(
            "SELECT to_user, SUM(amount) as total FROM transactions GROUP BY to_user ORDER BY total DESC LIMIT ?",
        )
        .bind(limit)
        .fetch_all(&self.pool)
        .await?;
        Ok(rows)
    }

    // ─── Starbridge app materialized activity ──────────────────────────────

    pub async fn record_starbridge_activity(
        &self,
        app: &str,
        action: &str,
        actor_discord_id: &str,
        guild_id: Option<&str>,
        subject: Option<&str>,
        status: &str,
        details: serde_json::Value,
    ) -> Result<i64, sqlx::Error> {
        let details_json = details.to_string();
        let result = sqlx::query(
            "INSERT INTO starbridge_activity
             (app, action, actor_discord_id, guild_id, subject, status, details_json, timestamp)
             VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
        )
        .bind(app)
        .bind(action)
        .bind(actor_discord_id)
        .bind(guild_id)
        .bind(subject)
        .bind(status)
        .bind(details_json)
        .bind(chrono_now())
        .execute(&self.pool)
        .await?;

        Ok(result.last_insert_rowid())
    }

    pub async fn get_recent_starbridge_activity(
        &self,
        limit: u32,
    ) -> Result<Vec<StarbridgeActivity>, sqlx::Error> {
        let rows = sqlx::query(
            "SELECT id, app, action, actor_discord_id, guild_id, subject, status, details_json, timestamp
             FROM starbridge_activity
             ORDER BY timestamp DESC, id DESC
             LIMIT ?",
        )
        .bind(limit)
        .fetch_all(&self.pool)
        .await?;

        Ok(rows.into_iter().map(activity_from_row).collect())
    }

    pub async fn get_recent_starbridge_activity_for_app(
        &self,
        app: &str,
        limit: u32,
    ) -> Result<Vec<StarbridgeActivity>, sqlx::Error> {
        let rows = sqlx::query(
            "SELECT id, app, action, actor_discord_id, guild_id, subject, status, details_json, timestamp
             FROM starbridge_activity
             WHERE app = ?
             ORDER BY timestamp DESC, id DESC
             LIMIT ?",
        )
        .bind(app)
        .bind(limit)
        .fetch_all(&self.pool)
        .await?;

        Ok(rows.into_iter().map(activity_from_row).collect())
    }

    // ─── Starbridge programmable queue host state ─────────────────────────

    pub async fn upsert_starbridge_queue(
        &self,
        namespace_path: &str,
        guild_id: &str,
        name: &str,
        queue_id: &str,
        created_by: &str,
        acl_role: Option<&str>,
        rate_limit: Option<i64>,
        min_deposit: Option<i64>,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT OR REPLACE INTO starbridge_queues
             (namespace_path, guild_id, name, queue_id, created_by, acl_role, rate_limit, min_deposit, created_at)
             VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
        )
        .bind(namespace_path)
        .bind(guild_id)
        .bind(name)
        .bind(queue_id)
        .bind(created_by)
        .bind(acl_role)
        .bind(rate_limit)
        .bind(min_deposit)
        .bind(chrono_now())
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    pub async fn get_starbridge_queue(
        &self,
        namespace_path: &str,
    ) -> Result<Option<StarbridgeQueue>, sqlx::Error> {
        let row = sqlx::query(
            "SELECT namespace_path, guild_id, name, queue_id, created_by, acl_role, rate_limit, min_deposit, created_at
             FROM starbridge_queues
             WHERE namespace_path = ?",
        )
        .bind(namespace_path)
        .fetch_optional(&self.pool)
        .await?;

        Ok(row.map(queue_from_row))
    }

    pub async fn list_starbridge_queues(&self) -> Result<Vec<StarbridgeQueue>, sqlx::Error> {
        let rows = sqlx::query(
            "SELECT namespace_path, guild_id, name, queue_id, created_by, acl_role, rate_limit, min_deposit, created_at
             FROM starbridge_queues
             ORDER BY guild_id, name",
        )
        .fetch_all(&self.pool)
        .await?;

        Ok(rows.into_iter().map(queue_from_row).collect())
    }

    pub async fn subscribe_starbridge_queue(
        &self,
        namespace_path: &str,
        discord_id: &str,
    ) -> Result<bool, sqlx::Error> {
        let result = sqlx::query(
            "INSERT OR IGNORE INTO starbridge_queue_subscriptions
             (namespace_path, discord_id, subscribed_at)
             VALUES (?, ?, ?)",
        )
        .bind(namespace_path)
        .bind(discord_id)
        .bind(chrono_now())
        .execute(&self.pool)
        .await?;
        Ok(result.rows_affected() > 0)
    }

    pub async fn list_starbridge_queue_subscriptions(
        &self,
    ) -> Result<Vec<StarbridgeQueueSubscription>, sqlx::Error> {
        let rows = sqlx::query(
            "SELECT namespace_path, discord_id, subscribed_at
             FROM starbridge_queue_subscriptions
             ORDER BY namespace_path, subscribed_at DESC, discord_id",
        )
        .fetch_all(&self.pool)
        .await?;

        Ok(rows
            .into_iter()
            .map(|row| StarbridgeQueueSubscription {
                namespace_path: row.get("namespace_path"),
                discord_id: row.get("discord_id"),
                subscribed_at: row.get("subscribed_at"),
            })
            .collect())
    }

    pub async fn count_starbridge_queue_subscribers(
        &self,
        namespace_path: &str,
    ) -> Result<i64, sqlx::Error> {
        let row: (i64,) = sqlx::query_as(
            "SELECT COUNT(*) FROM starbridge_queue_subscriptions WHERE namespace_path = ?",
        )
        .bind(namespace_path)
        .fetch_one(&self.pool)
        .await?;
        Ok(row.0)
    }

    /// The subscribers of ONE queue path — the DM fan-out list a publish delivers to
    /// (`commands::subscription_dispatch`).
    pub async fn list_starbridge_queue_subscribers(
        &self,
        namespace_path: &str,
    ) -> Result<Vec<String>, sqlx::Error> {
        let rows = sqlx::query(
            "SELECT discord_id FROM starbridge_queue_subscriptions
             WHERE namespace_path = ?
             ORDER BY subscribed_at DESC, discord_id",
        )
        .bind(namespace_path)
        .fetch_all(&self.pool)
        .await?;
        Ok(rows.into_iter().map(|row| row.get("discord_id")).collect())
    }

    /// One activity row by id — the durable backing of a public governance proposal card's
    /// vote buttons (`commands::governance_card`).
    pub async fn get_starbridge_activity(
        &self,
        id: i64,
    ) -> Result<Option<StarbridgeActivity>, sqlx::Error> {
        let row = sqlx::query(
            "SELECT id, app, action, actor_discord_id, guild_id, subject, status, details_json, timestamp
             FROM starbridge_activity
             WHERE id = ?",
        )
        .bind(id)
        .fetch_optional(&self.pool)
        .await?;
        Ok(row.map(activity_from_row))
    }

    // ─── CapTP durable handoffs ───────────────────────────────────────────

    pub async fn create_captp_handoff(
        &self,
        token_id: &str,
        cell_id: &str,
        sturdy_uri: &str,
        from_discord_id: &str,
        to_discord_id: &str,
        recipient_cell_id: &str,
        token_json: &str,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT OR REPLACE INTO captp_handoffs
             (token_id, cell_id, sturdy_uri, from_discord_id, to_discord_id, recipient_cell_id, status, issued_at, redeemed_at, revoked_at, token_json)
             VALUES (?, ?, ?, ?, ?, ?, 'pending', ?, NULL, NULL, ?)",
        )
        .bind(token_id)
        .bind(cell_id)
        .bind(sturdy_uri)
        .bind(from_discord_id)
        .bind(to_discord_id)
        .bind(recipient_cell_id)
        .bind(chrono_now())
        .bind(token_json)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    pub async fn get_captp_handoff(
        &self,
        token_id: &str,
    ) -> Result<Option<CaptpHandoffRecord>, sqlx::Error> {
        let row = sqlx::query(
            "SELECT token_id, cell_id, sturdy_uri, from_discord_id, to_discord_id, recipient_cell_id, status, issued_at, redeemed_at, revoked_at, token_json
             FROM captp_handoffs
             WHERE token_id = ?",
        )
        .bind(token_id)
        .fetch_optional(&self.pool)
        .await?;

        Ok(row.map(captp_handoff_from_row))
    }

    pub async fn redeem_captp_handoff(
        &self,
        token_id: &str,
        to_discord_id: &str,
    ) -> Result<bool, sqlx::Error> {
        let result = sqlx::query(
            "UPDATE captp_handoffs
             SET status = 'redeemed', redeemed_at = ?
             WHERE token_id = ? AND to_discord_id = ? AND status = 'pending'",
        )
        .bind(chrono_now())
        .bind(token_id)
        .bind(to_discord_id)
        .execute(&self.pool)
        .await?;
        Ok(result.rows_affected() > 0)
    }

    pub async fn revoke_captp_handoffs_for_cell(
        &self,
        cell_id: &str,
        from_discord_id: &str,
    ) -> Result<u64, sqlx::Error> {
        let result = sqlx::query(
            "UPDATE captp_handoffs
             SET status = 'revoked', revoked_at = ?
             WHERE cell_id = ? AND from_discord_id = ? AND status = 'pending'",
        )
        .bind(chrono_now())
        .bind(cell_id)
        .bind(from_discord_id)
        .execute(&self.pool)
        .await?;
        Ok(result.rows_affected())
    }

    pub async fn upsert_captp_export(&self, record: &CaptpExportRecord) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT INTO captp_exports (cell_id, sturdy_uri, shared_with, exported_at, revoked)
             VALUES (?, ?, ?, ?, ?)
             ON CONFLICT(cell_id) DO UPDATE SET
                sturdy_uri = excluded.sturdy_uri,
                shared_with = excluded.shared_with,
                exported_at = excluded.exported_at,
                revoked = excluded.revoked",
        )
        .bind(&record.cell_id)
        .bind(&record.sturdy_uri)
        .bind(&record.shared_with)
        .bind(record.exported_at)
        .bind(record.revoked)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    pub async fn get_captp_export(
        &self,
        cell_id: &str,
    ) -> Result<Option<CaptpExportRecord>, sqlx::Error> {
        let row = sqlx::query(
            "SELECT cell_id, sturdy_uri, shared_with, exported_at, revoked
             FROM captp_exports WHERE cell_id = ?",
        )
        .bind(cell_id)
        .fetch_optional(&self.pool)
        .await?;
        Ok(row.map(captp_export_from_row))
    }

    pub async fn list_captp_exports(&self) -> Result<Vec<CaptpExportRecord>, sqlx::Error> {
        let rows = sqlx::query(
            "SELECT cell_id, sturdy_uri, shared_with, exported_at, revoked
             FROM captp_exports ORDER BY exported_at DESC, cell_id",
        )
        .fetch_all(&self.pool)
        .await?;
        Ok(rows.into_iter().map(captp_export_from_row).collect())
    }

    pub async fn revoke_captp_export(&self, cell_id: &str) -> Result<bool, sqlx::Error> {
        let result = sqlx::query("UPDATE captp_exports SET revoked = 1 WHERE cell_id = ?")
            .bind(cell_id)
            .execute(&self.pool)
            .await?;
        Ok(result.rows_affected() > 0)
    }

    pub async fn upsert_captp_held_ref(&self, record: &CaptpHeldRecord) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT INTO captp_held_refs (cell_id, sturdy_uri, label, shared_by, acquired_at, live)
             VALUES (?, ?, ?, ?, ?, ?)
             ON CONFLICT(cell_id) DO UPDATE SET
                sturdy_uri = excluded.sturdy_uri,
                label = excluded.label,
                shared_by = excluded.shared_by,
                acquired_at = excluded.acquired_at,
                live = excluded.live",
        )
        .bind(&record.cell_id)
        .bind(&record.sturdy_uri)
        .bind(&record.label)
        .bind(&record.shared_by)
        .bind(record.acquired_at)
        .bind(record.live)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    pub async fn list_captp_held_refs(&self) -> Result<Vec<CaptpHeldRecord>, sqlx::Error> {
        let rows = sqlx::query(
            "SELECT cell_id, sturdy_uri, label, shared_by, acquired_at, live
             FROM captp_held_refs ORDER BY acquired_at DESC, cell_id",
        )
        .fetch_all(&self.pool)
        .await?;
        Ok(rows.into_iter().map(captp_held_from_row).collect())
    }

    pub async fn delete_captp_held_ref(&self, cell_id: &str) -> Result<(), sqlx::Error> {
        sqlx::query("DELETE FROM captp_held_refs WHERE cell_id = ?")
            .bind(cell_id)
            .execute(&self.pool)
            .await?;
        Ok(())
    }

    pub async fn upsert_captp_local_handoff(
        &self,
        record: &CaptpLocalHandoffRecord,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT INTO captp_local_handoffs
             (token_id, cell_id, sturdy_uri, recipient_cell_id, local_signature, status, created_at, redeemed_at)
             VALUES (?, ?, ?, ?, ?, ?, ?, ?)
             ON CONFLICT(token_id) DO UPDATE SET
                cell_id = excluded.cell_id,
                sturdy_uri = excluded.sturdy_uri,
                recipient_cell_id = excluded.recipient_cell_id,
                local_signature = excluded.local_signature,
                status = excluded.status,
                created_at = excluded.created_at,
                redeemed_at = excluded.redeemed_at",
        )
        .bind(&record.token_id)
        .bind(&record.cell_id)
        .bind(&record.sturdy_uri)
        .bind(&record.recipient_cell_id)
        .bind(&record.local_signature)
        .bind(&record.status)
        .bind(record.created_at)
        .bind(record.redeemed_at)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    pub async fn get_captp_local_handoff(
        &self,
        token_id: &str,
    ) -> Result<Option<CaptpLocalHandoffRecord>, sqlx::Error> {
        let row = sqlx::query(
            "SELECT token_id, cell_id, sturdy_uri, recipient_cell_id, local_signature, status, created_at, redeemed_at
             FROM captp_local_handoffs WHERE token_id = ?",
        )
        .bind(token_id)
        .fetch_optional(&self.pool)
        .await?;
        Ok(row.map(captp_local_handoff_from_row))
    }

    pub async fn list_captp_local_handoffs(
        &self,
    ) -> Result<Vec<CaptpLocalHandoffRecord>, sqlx::Error> {
        let rows = sqlx::query(
            "SELECT token_id, cell_id, sturdy_uri, recipient_cell_id, local_signature, status, created_at, redeemed_at
             FROM captp_local_handoffs ORDER BY created_at DESC, token_id",
        )
        .fetch_all(&self.pool)
        .await?;
        Ok(rows.into_iter().map(captp_local_handoff_from_row).collect())
    }

    pub async fn revoke_pending_captp_local_handoffs_for_cell(
        &self,
        cell_id: &str,
        revoked_at: i64,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            "UPDATE captp_local_handoffs
             SET status = 'revoked', redeemed_at = COALESCE(redeemed_at, ?)
             WHERE cell_id = ? AND status = 'pending'",
        )
        .bind(revoked_at)
        .bind(cell_id)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    // ─── DreggNet Cloud: semi-private per-user channels ─────────────────────

    /// Record a freshly created (or re-claimed) per-user channel. Upsert by
    /// `channel_id` so re-running the claim flow is idempotent.
    pub async fn upsert_user_channel(
        &self,
        channel_id: &str,
        discord_id: &str,
        guild_id: &str,
        cell_id: &str,
        created_at: i64,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT INTO user_channels (channel_id, discord_id, guild_id, cell_id, status, created_at)
             VALUES (?, ?, ?, ?, 'active', ?)
             ON CONFLICT(channel_id) DO UPDATE SET
                discord_id = excluded.discord_id,
                guild_id = excluded.guild_id,
                cell_id = excluded.cell_id,
                status = 'active'",
        )
        .bind(channel_id)
        .bind(discord_id)
        .bind(guild_id)
        .bind(cell_id)
        .bind(created_at)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    /// Look up the channel record for a Discord channel id (the routing key the
    /// message handler uses to decide whether a channel drives a user's Hermes).
    pub async fn get_user_channel(
        &self,
        channel_id: &str,
    ) -> Result<Option<UserChannel>, sqlx::Error> {
        let row = sqlx::query(
            "SELECT channel_id, discord_id, guild_id, cell_id, status, created_at
             FROM user_channels WHERE channel_id = ?",
        )
        .bind(channel_id)
        .fetch_optional(&self.pool)
        .await?;
        Ok(row.map(user_channel_from_row))
    }

    /// The existing channel a user already owns in a guild, if any (so the claim
    /// flow can return the existing one instead of creating a duplicate).
    pub async fn get_user_channel_for_user(
        &self,
        discord_id: &str,
        guild_id: &str,
    ) -> Result<Option<UserChannel>, sqlx::Error> {
        let row = sqlx::query(
            "SELECT channel_id, discord_id, guild_id, cell_id, status, created_at
             FROM user_channels WHERE discord_id = ? AND guild_id = ? AND status = 'active'
             ORDER BY created_at DESC LIMIT 1",
        )
        .bind(discord_id)
        .bind(guild_id)
        .fetch_optional(&self.pool)
        .await?;
        Ok(row.map(user_channel_from_row))
    }

    /// Every recorded channel (admin portal monitoring view).
    pub async fn list_user_channels(&self) -> Result<Vec<UserChannel>, sqlx::Error> {
        let rows = sqlx::query(
            "SELECT channel_id, discord_id, guild_id, cell_id, status, created_at
             FROM user_channels ORDER BY created_at DESC",
        )
        .fetch_all(&self.pool)
        .await?;
        Ok(rows.into_iter().map(user_channel_from_row).collect())
    }

    // ─── DreggNet Cloud: per-channel Hermes activity ────────────────────────

    /// Append a Hermes verdict to the per-channel agent ledger.
    #[allow(clippy::too_many_arguments)]
    pub async fn record_hermes_activity(
        &self,
        discord_id: &str,
        channel_id: &str,
        prompt: &str,
        tool: &str,
        kind: &str,
        allowed: bool,
        receipt: Option<&str>,
        remaining: Option<i64>,
        reason: Option<&str>,
        created_at: i64,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT INTO hermes_activity
                (discord_id, channel_id, prompt, tool, kind, allowed, receipt, remaining, reason, created_at)
             VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
        )
        .bind(discord_id)
        .bind(channel_id)
        .bind(prompt)
        .bind(tool)
        .bind(kind)
        .bind(allowed as i64)
        .bind(receipt)
        .bind(remaining)
        .bind(reason)
        .bind(created_at)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    /// Recent Hermes activity across all channels (admin portal).
    pub async fn list_recent_hermes_activity(
        &self,
        limit: u32,
    ) -> Result<Vec<HermesActivity>, sqlx::Error> {
        let rows = sqlx::query(
            "SELECT id, discord_id, channel_id, prompt, tool, kind, allowed, receipt, remaining, reason, created_at
             FROM hermes_activity ORDER BY created_at DESC, id DESC LIMIT ?",
        )
        .bind(limit)
        .fetch_all(&self.pool)
        .await?;
        Ok(rows.into_iter().map(hermes_activity_from_row).collect())
    }

    // ─── BYO-LLM-keys (encrypted at rest) ───────────────────────────────────

    /// Set (or replace) a user's encrypted provider key + policy. The caller
    /// passes the ALREADY-SEALED `nonce_b64`/`ciphertext_b64` — the plaintext
    /// never reaches this layer. Upsert: re-running rotates the stored key.
    #[allow(clippy::too_many_arguments)]
    pub async fn set_llm_key(
        &self,
        discord_id: &str,
        provider: &str,
        model: &str,
        nonce_b64: &str,
        ciphertext_b64: &str,
        token_budget: i64,
        rate_limit: i64,
        now: i64,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT INTO user_llm_keys
                (discord_id, provider, model, nonce_b64, ciphertext_b64, token_budget, rate_limit, created_at, updated_at)
             VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
             ON CONFLICT(discord_id) DO UPDATE SET
                provider = excluded.provider,
                model = excluded.model,
                nonce_b64 = excluded.nonce_b64,
                ciphertext_b64 = excluded.ciphertext_b64,
                token_budget = excluded.token_budget,
                rate_limit = excluded.rate_limit,
                updated_at = excluded.updated_at",
        )
        .bind(discord_id)
        .bind(provider)
        .bind(model)
        .bind(nonce_b64)
        .bind(ciphertext_b64)
        .bind(token_budget)
        .bind(rate_limit)
        .bind(now)
        .bind(now)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    /// Fetch a user's encrypted key record, if they have ported one in.
    pub async fn get_llm_key(&self, discord_id: &str) -> Result<Option<LlmKeyRecord>, sqlx::Error> {
        let row = sqlx::query(
            "SELECT provider, model, nonce_b64, ciphertext_b64, token_budget, rate_limit
             FROM user_llm_keys WHERE discord_id = ?",
        )
        .bind(discord_id)
        .fetch_optional(&self.pool)
        .await?;
        Ok(row.map(|row| LlmKeyRecord {
            provider: row.get("provider"),
            model: row.get("model"),
            nonce_b64: row.get("nonce_b64"),
            ciphertext_b64: row.get("ciphertext_b64"),
            token_budget: row.get("token_budget"),
            rate_limit: row.get("rate_limit"),
        }))
    }

    /// Revoke (delete) a user's stored key. Returns `true` if a row was removed.
    /// After this nothing is recoverable — the sealed ciphertext is gone.
    pub async fn revoke_llm_key(&self, discord_id: &str) -> Result<bool, sqlx::Error> {
        let res = sqlx::query("DELETE FROM user_llm_keys WHERE discord_id = ?")
            .bind(discord_id)
            .execute(&self.pool)
            .await?;
        Ok(res.rows_affected() > 0)
    }

    /// Ensure extra tables exist (called from connect).
    pub async fn ensure_extra_tables(&self) -> Result<(), sqlx::Error> {
        sqlx::query(
            "CREATE TABLE IF NOT EXISTS transactions (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                from_user TEXT NOT NULL,
                to_user TEXT NOT NULL,
                amount INTEGER NOT NULL,
                tx_hash TEXT NOT NULL,
                timestamp INTEGER NOT NULL
            )",
        )
        .execute(&self.pool)
        .await?;
        Ok(())
    }
}

fn user_channel_from_row(row: sqlx::sqlite::SqliteRow) -> UserChannel {
    UserChannel {
        channel_id: row.get("channel_id"),
        discord_id: row.get("discord_id"),
        guild_id: row.get("guild_id"),
        cell_id: row.get("cell_id"),
        status: row.get("status"),
        created_at: row.get("created_at"),
    }
}

fn hermes_activity_from_row(row: sqlx::sqlite::SqliteRow) -> HermesActivity {
    let allowed: i64 = row.get("allowed");
    HermesActivity {
        id: row.get("id"),
        discord_id: row.get("discord_id"),
        channel_id: row.get("channel_id"),
        prompt: row.get("prompt"),
        tool: row.get("tool"),
        kind: row.get("kind"),
        allowed: allowed != 0,
        receipt: row.get("receipt"),
        remaining: row.get("remaining"),
        reason: row.get("reason"),
        created_at: row.get("created_at"),
    }
}

fn queue_from_row(row: sqlx::sqlite::SqliteRow) -> StarbridgeQueue {
    StarbridgeQueue {
        namespace_path: row.get("namespace_path"),
        guild_id: row.get("guild_id"),
        name: row.get("name"),
        queue_id: row.get("queue_id"),
        created_by: row.get("created_by"),
        acl_role: row.get("acl_role"),
        rate_limit: row.get("rate_limit"),
        min_deposit: row.get("min_deposit"),
        created_at: row.get("created_at"),
    }
}

fn activity_from_row(row: sqlx::sqlite::SqliteRow) -> StarbridgeActivity {
    StarbridgeActivity {
        id: row.get("id"),
        app: row.get("app"),
        action: row.get("action"),
        actor_discord_id: row.get("actor_discord_id"),
        guild_id: row.get("guild_id"),
        subject: row.get("subject"),
        status: row.get("status"),
        details_json: row.get("details_json"),
        timestamp: row.get("timestamp"),
    }
}

fn captp_handoff_from_row(row: sqlx::sqlite::SqliteRow) -> CaptpHandoffRecord {
    CaptpHandoffRecord {
        token_id: row.get("token_id"),
        cell_id: row.get("cell_id"),
        sturdy_uri: row.get("sturdy_uri"),
        from_discord_id: row.get("from_discord_id"),
        to_discord_id: row.get("to_discord_id"),
        recipient_cell_id: row.get("recipient_cell_id"),
        status: row.get("status"),
        issued_at: row.get("issued_at"),
        redeemed_at: row.get("redeemed_at"),
        revoked_at: row.get("revoked_at"),
        token_json: row.get("token_json"),
    }
}

fn captp_export_from_row(row: sqlx::sqlite::SqliteRow) -> CaptpExportRecord {
    CaptpExportRecord {
        cell_id: row.get("cell_id"),
        sturdy_uri: row.get("sturdy_uri"),
        shared_with: row.get("shared_with"),
        exported_at: row.get("exported_at"),
        revoked: row.get::<i64, _>("revoked") != 0,
    }
}

fn captp_held_from_row(row: sqlx::sqlite::SqliteRow) -> CaptpHeldRecord {
    CaptpHeldRecord {
        cell_id: row.get("cell_id"),
        sturdy_uri: row.get("sturdy_uri"),
        label: row.get("label"),
        shared_by: row.get("shared_by"),
        acquired_at: row.get("acquired_at"),
        live: row.get::<i64, _>("live") != 0,
    }
}

fn captp_local_handoff_from_row(row: sqlx::sqlite::SqliteRow) -> CaptpLocalHandoffRecord {
    CaptpLocalHandoffRecord {
        token_id: row.get("token_id"),
        cell_id: row.get("cell_id"),
        sturdy_uri: row.get("sturdy_uri"),
        recipient_cell_id: row.get("recipient_cell_id"),
        local_signature: row.get("local_signature"),
        status: row.get("status"),
        created_at: row.get("created_at"),
        redeemed_at: row.get("redeemed_at"),
    }
}

fn held_credential_from_row(row: sqlx::sqlite::SqliteRow) -> HeldCredential {
    HeldCredential {
        credential_id: row.get("credential_id"),
        discord_id: row.get("discord_id"),
        holder_cell_id: row.get("holder_cell_id"),
        issuer_cell_id: row.get("issuer_cell_id"),
        schema: row.get("schema"),
        issued_at: row.get("issued_at"),
        turn_hash: row.get("turn_hash"),
        encoded_credential: row.get("encoded_credential"),
        attributes_json: row.get("attributes_json"),
        created_at: row.get("created_at"),
    }
}

/// A recorded transaction.
#[derive(Debug, Clone, sqlx::FromRow)]
pub struct TransactionRecord {
    pub from_user: String,
    pub to_user: String,
    pub amount: i64,
    pub tx_hash: String,
    pub timestamp: i64,
}

fn chrono_now() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs() as i64
}

fn short_local_hash(input: &str) -> String {
    let hash = blake3::hash(input.as_bytes()).to_hex().to_string();
    hash[..12.min(hash.len())].to_string()
}

/// A persisted UGC-gallery universe row — the plain DB shape of a published
/// universe's reproducible public source. `commands::gallery`'s `SqliteGalleryStore`
/// translates this to/from its `StoredUniverse` (kept out of the DB layer so `db`
/// stays free of the gallery command types).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UgcUniverseRow {
    pub id_hex: String,
    pub kind: String,
    pub name: String,
    pub author: String,
    pub source: String,
    pub epoch_hex: Option<String>,
    pub win_json: String,
    /// Remix/fork parent content address (hex), or `None` for a root. Re-verified on boot.
    pub parent_id_hex: Option<String>,
    /// Verified author ed25519 public key (hex), or `None` for an anonymous universe.
    pub author_key_hex: Option<String>,
    /// The author's attestation signature (hex) over the universe content commitment.
    pub author_sig_hex: Option<String>,
}

/// A persisted UGC-gallery completion row — the plain DB shape of an accepted
/// completion (player + move sequence + claimed turns). Re-verified by replay on boot.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UgcCompletionRow {
    pub key_hex: String,
    pub universe_id_hex: String,
    pub player: String,
    pub moves_json: String,
    pub claimed_turns: i64,
}

/// A persisted /descent day-universe row — the plain DB shape of a day-world's reproducible
/// descriptor (its committed beacon seed + author). `commands::descent`'s `SqliteDescentBoardStore`
/// translates this to/from its `StoredDescentUniverse` (kept out of the DB layer so `db` stays free
/// of the descent command types). The world is regenerated byte-for-byte from `seed_hex` on boot.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DescentUniverseRow {
    /// The day-universe content address (hex) at publish time — the row PK + tamper check.
    pub id_hex: String,
    /// The board author label the day's world is published under.
    pub author: String,
    /// Hex of the 32-byte committed beacon seed the day's world regenerates from.
    pub seed_hex: String,
}

/// A persisted /descent board completion row — the plain DB shape of an accepted winning run
/// (player + move sequence + claimed turns). Re-verified by replay on boot.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DescentCompletionRow {
    pub key_hex: String,
    pub universe_id_hex: String,
    pub player: String,
    pub moves_json: String,
    pub claimed_turns: i64,
}

/// A persisted RPG session open row — the plain DB shape of one `/play` world session's replay
/// root (its seed, `"-"` for the offering default). `rpg_store::SqliteRpgResumeStore` translates
/// this to/from `dreggnet_offerings::resume::SessionMoveLog` (kept out of the DB layer so `db`
/// stays free of the offerings types).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RpgSessionRow {
    pub key: String,
    pub session_id: String,
    pub seed: String,
}

/// A persisted RPG session landed-advance row — one committed turn's reproducible public input
/// (the typed action + the attributed actor + its attribution trust tag `s`/`a`). The columns
/// mirror `dreggnet_offerings::resume`'s wire fields exactly.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RpgMoveRow {
    pub label: String,
    pub turn: String,
    pub arg: i64,
    pub enabled: i64,
    pub has_text: i64,
    pub text: String,
    pub actor: String,
    pub trust: String,
}

/// One published dungeon world in the community library. The `source` is authoritative (loaders
/// re-parse it); `author_pubkey` is the publisher's derived cipherclerk public-key hex — an author
/// LABEL recording who published, NOT a signature over the source.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DungeonWorldRecord {
    /// The library name (unique key), e.g. `"clockwork-orchard"`.
    pub name: String,
    /// The world's display name (from its `name:` header).
    pub display_name: String,
    /// The verbatim `.dungeon` source — re-parsed on load, never a cached binary.
    pub source: String,
    /// The publisher's Discord id.
    pub author_discord_id: String,
    /// The publisher's derived cipherclerk Ed25519 public key (hex) — an author label.
    pub author_pubkey: String,
    /// Whether the world passed `validate` with no blocking errors at publish time.
    pub validates_clean: bool,
    /// The number of rooms in the world.
    pub room_count: i64,
    /// Unix seconds when it was published.
    pub created_at: i64,
}

/// Decode a `dungeon_worlds` row into a [`DungeonWorldRecord`].
fn row_to_world(row: &sqlx::sqlite::SqliteRow) -> DungeonWorldRecord {
    DungeonWorldRecord {
        name: row.get("name"),
        display_name: row.get("display_name"),
        source: row.get("source"),
        author_discord_id: row.get("author_discord_id"),
        author_pubkey: row.get("author_pubkey"),
        validates_clean: row.get::<i64, _>("validates_clean") != 0,
        room_count: row.get("room_count"),
        created_at: row.get("created_at"),
    }
}

async fn ensure_column(
    pool: &Pool<Sqlite>,
    table: &str,
    column: &str,
    definition: &str,
) -> Result<(), sqlx::Error> {
    let pragma = format!("PRAGMA table_info({table})");
    let rows = sqlx::query(&pragma).fetch_all(pool).await?;
    let exists = rows
        .iter()
        .any(|row| row.get::<String, _>("name") == column);

    if !exists {
        let alter = format!("ALTER TABLE {table} ADD COLUMN {column} {definition}");
        sqlx::query(&alter).execute(pool).await?;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{Database, IdentityMode};

    #[tokio::test]
    async fn hosted_identity_records_mode() {
        let db = Database::connect("sqlite::memory:").await.unwrap();
        db.register_user("42", "abc").await.unwrap();

        let identity = db.get_user_identity("42").await.unwrap().unwrap();
        assert_eq!(identity.cell_id, "abc");
        assert_eq!(identity.mode, IdentityMode::Hosted);
        assert_eq!(identity.link_challenge, None);
    }

    #[tokio::test]
    async fn pending_external_link_is_not_hosted() {
        let db = Database::connect("sqlite::memory:").await.unwrap();
        db.create_pending_external_link("42", "def", "challenge")
            .await
            .unwrap();

        let identity = db.get_user_identity("42").await.unwrap().unwrap();
        assert_eq!(identity.cell_id, "def");
        assert_eq!(identity.mode, IdentityMode::ExternalPending);
        assert_eq!(identity.link_challenge.as_deref(), Some("challenge"));
    }

    #[tokio::test]
    async fn starbridge_activity_roundtrips() {
        let db = Database::connect("sqlite::memory:").await.unwrap();
        db.record_starbridge_activity(
            "nameservice",
            "register",
            "42",
            Some("7"),
            Some("alice"),
            "submitted",
            serde_json::json!({"name":"alice"}),
        )
        .await
        .unwrap();

        let rows = db.get_recent_starbridge_activity(10).await.unwrap();
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].app, "nameservice");
        assert_eq!(rows[0].action, "register");
        assert_eq!(rows[0].guild_id.as_deref(), Some("7"));
        assert_eq!(rows[0].subject.as_deref(), Some("alice"));
    }

    #[tokio::test]
    async fn identity_holder_store_roundtrips() {
        let db = Database::connect("sqlite::memory:").await.unwrap();
        db.store_held_credential(
            "42",
            "holder",
            "issuer",
            "cred1",
            "kyc-v1",
            123,
            Some("turn"),
            "{\"encoded\":\"credential\"}",
            "{\"age\":21}",
        )
        .await
        .unwrap();

        let rows = db.list_held_credentials("42", "holder", 10).await.unwrap();
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].credential_id, "cred1");
        assert_eq!(rows[0].schema, "kyc-v1");

        let matched = db
            .find_held_credential_for_predicate("42", "holder", "age>=18")
            .await
            .unwrap()
            .unwrap();
        assert_eq!(matched.credential_id, "cred1");

        let presentation = db
            .create_identity_presentation(
                "7",
                "42",
                "holder",
                "age>=18",
                "presentation_unavailable",
                Some("cred1"),
                "{\"status\":\"presentation_unavailable\"}",
            )
            .await
            .unwrap();
        assert_eq!(presentation.credential_id.as_deref(), Some("cred1"));
    }

    #[tokio::test]
    async fn user_channel_roundtrips_and_routes_by_channel() {
        let db = Database::connect("sqlite::memory:").await.unwrap();
        db.upsert_user_channel("chan-1", "user-99", "guild-1", "cell-abc", 100)
            .await
            .unwrap();

        // Routing key: look up by the Discord channel id.
        let by_chan = db.get_user_channel("chan-1").await.unwrap().unwrap();
        assert_eq!(by_chan.discord_id, "user-99");
        assert_eq!(by_chan.cell_id, "cell-abc");
        assert_eq!(by_chan.status, "active");

        // Idempotent re-claim: a user already owns one in the guild.
        let existing = db
            .get_user_channel_for_user("user-99", "guild-1")
            .await
            .unwrap();
        assert!(existing.is_some());

        assert!(db.get_user_channel("nope").await.unwrap().is_none());
        assert_eq!(db.list_user_channels().await.unwrap().len(), 1);
    }

    #[tokio::test]
    async fn hermes_activity_records_both_verdicts() {
        let db = Database::connect("sqlite::memory:").await.unwrap();
        db.record_hermes_activity(
            "user-1",
            "chan-1",
            "read README",
            "read_file",
            "Read",
            true,
            Some("deadbeef"),
            Some(199),
            None,
            10,
        )
        .await
        .unwrap();
        db.record_hermes_activity(
            "user-1",
            "chan-1",
            "run rm",
            "terminal",
            "Execute",
            false,
            None,
            None,
            Some("rate exhausted: 1 of 1 calls used this mandate window"),
            11,
        )
        .await
        .unwrap();

        let recent = db.list_recent_hermes_activity(10).await.unwrap();
        assert_eq!(recent.len(), 2);
        // Most recent first.
        assert!(!recent[0].allowed);
        assert!(
            recent[0]
                .reason
                .as_deref()
                .unwrap()
                .contains("rate exhausted")
        );
        assert!(recent[1].allowed);
        assert_eq!(recent[1].receipt.as_deref(), Some("deadbeef"));
    }
}
