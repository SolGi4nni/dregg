//! The sqlite-backed [`SqliteRpgResumeStore`] — the durable backing of dreggnet-offerings'
//! [`SessionResumeStore`] seam, **scoped to one player identity**, so a player's `/play` RPG
//! world (trade / craft / inventory / guild / companion / tavern / party / cheevos) survives a
//! process restart instead of being a throwaway demo world.
//!
//! `dreggnet_offerings::resume` OWNS the [`SessionResumeStore`] trait + the [`SessionMoveLog`]
//! value; `InMemoryResumeStore` / `FileResumeStore` are the core impls its tests drive. This
//! module supplies the ONE thing the bot owes it: the durable sqlite impl the trait's own doc
//! names as "the discord-bot's follow-up". It is the exact shape of
//! [`crate::character_store::SqliteCharacterStore`] / [`crate::descent_board_store::SqliteDescentBoardStore`]
//! — the trait is SYNC (`&self`), the bot's `Database` is async sqlx, so each method drives its
//! async query to completion with [`tokio::task::block_in_place`] on the current multi-thread
//! runtime, falling back to a stored [`tokio::runtime::Handle`] when called from OUTSIDE a
//! runtime worker — which is the norm here, since each player's `OfferingHost` is owned by the
//! dedicated *non-tokio* `rpg-worlds` `std::thread` (`commands::rpg_world`).
//!
//! ## What persists, and the tooth
//!
//! ONLY the reproducible public input: each session's open (its seed) and its ordered LANDED
//! advances — never a serialized state blob. The host reopens a session by REPLAYING the log
//! through the real executor ([`dreggnet_offerings::OfferingHost::resume`]); a tampered row (a
//! forged / ineligible / reordered advance) is refused on re-drive and the session fails closed.
//!
//! ## Honest scope
//!
//! The signed-counter floors ([`SessionResumeStore::record_signed_counters`]) keep the trait
//! defaults (unsupported → the host retains floors in memory, fail-closed). The bot's RPG press
//! path advances with **asserted** attribution (the presser's derived identity, custodially held
//! by the bot) and never calls `advance_signed`, so there are no floors to persist yet; wiring
//! `dreggnet_offerings::signed` through Discord is the named next step (backlog #25).

use dreggnet_offerings::resume::{SessionMoveLog, SessionResumeStore};
use dreggnet_offerings::signed::Attribution;
use dreggnet_offerings::{Action, DreggIdentity, SessionConfig, SessionId};

use crate::db::{Database, RpgMoveRow, RpgSessionRow};

/// A [`SessionResumeStore`] persisted in the bot's sqlite database, **scoped to one player's
/// derived dregg identity** (the `player` column): every `(key, id)` this store reads or writes
/// is namespaced under that identity, so two players' worlds can never bleed into each other.
/// Cheaply `Clone` (the `Database` is a pool handle).
#[derive(Clone)]
pub struct SqliteRpgResumeStore {
    db: Database,
    handle: tokio::runtime::Handle,
    /// The owning player's derived dregg identity hex — the scope of every row.
    player: String,
}

impl SqliteRpgResumeStore {
    /// Wrap a `Database`, scoped to `player` (the derived dregg identity hex). `handle` is the
    /// runtime to drive the async queries on when called from OUTSIDE a runtime worker (the
    /// dedicated `rpg-worlds` thread); inside a runtime worker the current handle is used.
    pub fn new(db: Database, handle: tokio::runtime::Handle, player: String) -> Self {
        SqliteRpgResumeStore { db, handle, player }
    }

    /// Drive an async DB future to completion synchronously — the sync↔async bridge the sync
    /// trait forces (identical to `descent_board_store::SqliteDescentBoardStore::block`).
    fn block<F: std::future::Future>(&self, fut: F) -> F::Output {
        match tokio::runtime::Handle::try_current() {
            Ok(current) => tokio::task::block_in_place(move || current.block_on(fut)),
            Err(_) => self.handle.block_on(fut),
        }
    }

    /// Assemble one session's persisted rows back into a [`SessionMoveLog`]. `None` if the open
    /// row is absent or its seed field is malformed (a damaged row is treated as absent rather
    /// than resumed to a wrong state — the same posture as the core `FileResumeStore` decoder).
    fn assemble(&self, key: &str, id: &SessionId) -> Option<SessionMoveLog> {
        let row = self
            .block(self.db.rpg_session_of(&self.player, key, &id.0))
            .ok()
            .flatten()?;
        let seed = match row.seed.as_str() {
            "-" => None,
            n => Some(n.parse::<u64>().ok()?),
        };
        let cfg = SessionConfig { seed };
        let mut log = SessionMoveLog::new(key, id.clone(), cfg);
        let moves = self
            .block(self.db.rpg_session_moves(&self.player, key, &id.0))
            .ok()?;
        for m in moves {
            let actor = DreggIdentity(m.actor.clone());
            let attribution = match m.trust.as_str() {
                // A signed move's actor IS its verified pubkey hex (the core codec's contract).
                "s" => Attribution::Signed {
                    pubkey_hex: m.actor.clone(),
                },
                "a" => Attribution::from(actor.clone()),
                // An unknown trust tag is a corrupt row — the whole log is treated as absent,
                // never mis-labeled.
                _ => return None,
            };
            let mut action = Action::new(m.label, m.turn, m.arg, m.enabled != 0);
            if m.has_text != 0 {
                action = action.with_text(m.text);
            }
            log.record_attributed(action, actor, attribution);
        }
        Some(log)
    }
}

impl SessionResumeStore for SqliteRpgResumeStore {
    fn record_open(&self, key: &str, id: &SessionId, cfg: &SessionConfig) {
        let seed = cfg
            .seed
            .map(|s| s.to_string())
            .unwrap_or_else(|| "-".into());
        let _ = self.block(self.db.rpg_session_open(&self.player, key, &id.0, &seed));
    }

    fn record_landed(&self, key: &str, id: &SessionId, action: &Action, actor: &DreggIdentity) {
        self.record_landed_attributed(key, id, action, actor, &Attribution::from(actor.clone()));
    }

    fn record_landed_attributed(
        &self,
        key: &str,
        id: &SessionId,
        action: &Action,
        actor: &DreggIdentity,
        attribution: &Attribution,
    ) {
        // A landed move on a session we never saw opened still establishes the open row (default
        // cfg); in practice `record_open` always precedes it (the host opens before it advances).
        let _ = self.block(self.db.rpg_session_open(&self.player, key, &id.0, "-"));
        let row = RpgMoveRow {
            label: action.label.clone(),
            turn: action.turn.clone(),
            arg: action.arg,
            enabled: action.enabled as i64,
            has_text: action.text.is_some() as i64,
            text: action.text.clone().unwrap_or_default(),
            actor: actor.0.clone(),
            trust: match attribution {
                Attribution::Signed { .. } => "s".to_string(),
                Attribution::Asserted { .. } => "a".to_string(),
            },
        };
        let _ = self.block(
            self.db
                .rpg_session_record_move(&self.player, key, &id.0, &row),
        );
    }

    fn forget(&self, key: &str, id: &SessionId) {
        let _ = self.block(self.db.rpg_session_forget(&self.player, key, &id.0));
    }

    fn load(&self, key: &str, id: &SessionId) -> Option<SessionMoveLog> {
        self.assemble(key, id)
    }

    fn all(&self) -> Vec<SessionMoveLog> {
        let rows: Vec<RpgSessionRow> = self
            .block(self.db.rpg_sessions_of(&self.player))
            .unwrap_or_default();
        rows.iter()
            .filter_map(|r| self.assemble(&r.key, &SessionId::new(r.session_id.clone())))
            .collect()
    }
}
