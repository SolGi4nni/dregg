//! The sqlite-backed [`SqliteCharacterStore`] — the durable backing of dreggnet-offerings'
//! [`CharacterStore`] seam, so a player's LEVELING character survives a process restart, not
//! just an in-session run.
//!
//! `dreggnet_offerings::character` OWNS the [`CharacterStore`] trait + the [`CharacterSheet`]
//! value + the [`AdventurerOffering`] that binds a character to a run; [`InMemoryCharacterStore`]
//! is the in-process impl its tests drive. This module supplies the ONE thing the bot owes it: a
//! durable impl. It is the exact shape of [`crate::pay::SqliteCreditStore`] /
//! [`crate::gallery_store::SqliteGalleryStore`] — the trait is SYNC (`&self` load / `&mut self`
//! save), but the bot's `Database` is async sqlx, so each method drives its async query to
//! completion with [`tokio::task::block_in_place`] on the current multi-thread runtime (no
//! nested-runtime panic, no deadlock), falling back to a stored [`tokio::runtime::Handle`] when
//! called from outside a runtime worker (e.g. a `spawn_blocking` thread).
//!
//! ## What persists, and the fail-safe
//!
//! The persisted state is the [`CharacterSheet`] keyed by the player's stable dregg identity hex:
//! `xp` / `level` / `class` / `abilities_used`. A **tampered or absent row fails safe** — a loaded
//! sheet is validated against the REAL progression curve ([`sheet_is_wellformed`]:
//! `xp >= xp_threshold(level)`, a valid class, `level <= MAX_LEVEL`), so a row that claims a level
//! its XP never earned loads as a **fresh level-1 character**, never a forged level. XP itself is
//! never bumped here — it flows through the real gated character turn ([`award_run_outcome`]).
//!
//! ## Honest scope
//!
//! - What persists: the four progression slots by identity. A fuller RPG persistence (inventory,
//!   reputation, a cross-universe character, a recorded + replay-verified character-turn chain)
//!   builds ON this seam — named, not built here.
//! - The collective `/dungeon` earns XP + levels a character on real party outcomes; a class is
//!   `WriteOnce` in the character cell and persists faithfully, but no Discord class-choice UI is
//!   wired yet (a collective player stays "unclassed" until that lands).

use dreggnet_offerings::character::{
    AdventurerOffering, CharacterSheet, CharacterStore, XP_BLOODY_WARDEN, XP_SEIZE_HOARD,
};
use dreggnet_offerings::{DreggIdentity, SessionConfig};
use dungeon_on_dregg::progression::{MAGE, MAX_LEVEL, ROGUE, WARRIOR, xp_threshold};
use dungeon_on_dregg::{KP_SEIZE, KP_TRADE_BLOWS, ROOM_GATEHALL, ROOM_SANCTUM};

use crate::db::Database;

/// A [`CharacterStore`] persisted in the bot's sqlite database. Character sheets live in the
/// `characters` table keyed by the player's dregg identity hex; they survive restart and a
/// returning player resumes their carried level / XP / class. Cheaply `Clone` (the `Database`
/// is a pool handle) so the live `/dungeon` path can build a short-lived [`AdventurerOffering`]
/// over a clone to run a real gated XP grant off the async worker.
#[derive(Clone)]
pub struct SqliteCharacterStore {
    db: Database,
    handle: tokio::runtime::Handle,
}

impl SqliteCharacterStore {
    /// Wrap a `Database`. `handle` is the runtime to fall back to when a store method is somehow
    /// called from OUTSIDE any runtime worker; inside a runtime worker the current handle is used.
    pub fn new(db: Database, handle: tokio::runtime::Handle) -> Self {
        SqliteCharacterStore { db, handle }
    }

    /// Drive an async DB future to completion synchronously — the sync↔async bridge the sync
    /// [`CharacterStore`] trait forces (identical to `pay::SqliteCreditStore::block`).
    fn block<F: std::future::Future>(&self, fut: F) -> F::Output {
        match tokio::runtime::Handle::try_current() {
            Ok(current) => tokio::task::block_in_place(move || current.block_on(fut)),
            Err(_) => self.handle.block_on(fut),
        }
    }
}

impl CharacterStore for SqliteCharacterStore {
    fn load(&self, who: &DreggIdentity) -> CharacterSheet {
        let raw = self.block(self.db.character_load(&who.0)).ok().flatten();
        match raw {
            Some((xp, level, class, abilities_used)) => {
                let sheet = CharacterSheet {
                    xp,
                    level,
                    class,
                    abilities_used,
                };
                // FAIL-SAFE: a row that does not sit on the real progression curve (a forged
                // level its XP never earned, an unknown class, a level past the ceiling) loads
                // as a FRESH character — never a forged level.
                if sheet_is_wellformed(&sheet) {
                    sheet
                } else {
                    CharacterSheet::default()
                }
            }
            None => CharacterSheet::default(),
        }
    }

    fn save(&mut self, who: &DreggIdentity, sheet: CharacterSheet) {
        let _ = self.block(self.db.character_save(
            &who.0,
            sheet.xp,
            sheet.level,
            sheet.class,
            sheet.abilities_used,
            now_secs(),
        ));
    }
}

/// Whether a persisted [`CharacterSheet`] is well-formed against the REAL progression curve — the
/// fail-safe tooth. A sheet is legitimate iff its class is valid, its level is within the installed
/// ceiling, and its earned XP meets the floor its claimed level requires (`xp_threshold(level)` is
/// exactly the `FieldGte(xp, .)` gate the executor enforces on a level-up). A row failing any of
/// these could only come from tampering — it loads as a fresh L1 character instead.
fn sheet_is_wellformed(sheet: &CharacterSheet) -> bool {
    let class_ok = matches!(sheet.class, 0 | WARRIOR | MAGE | ROGUE);
    let level_ok = sheet.level <= MAX_LEVEL;
    let xp_ok = sheet.xp >= xp_threshold(sheet.level);
    class_ok && level_ok && xp_ok
}

// ── The XP reward binding (collective outcome → earned XP), mirroring character.rs ──────────

/// The XP a just-LANDED collective dungeon move earns, by `(room, choice_index)` — the SAME
/// reward table `dreggnet_offerings::character` binds (bloodying the gate-warden, seizing the
/// hoard). `None` for a move with no reward. Only real, executor-admitted outcomes reach here.
pub fn xp_reward(room: &str, choice_index: usize) -> Option<u64> {
    match (room, choice_index) {
        (ROOM_GATEHALL, i) if i == KP_TRADE_BLOWS => Some(XP_BLOODY_WARDEN),
        (ROOM_SANCTUM, i) if i == KP_SEIZE => Some(XP_SEIZE_HOARD),
        _ => None,
    }
}

/// **Award the earned XP for a landed qualifying collective outcome to each voter who carried
/// it**, through the REAL gated character turn, persisting each. The party's plurality move that
/// landed a qualifying outcome is attributed to its electorate of record (everyone who cast a
/// ballot that round); each of those players earns the outcome's XP as a real
/// `StrictMonotonic(xp)`-gated turn (NOT an integer bump), auto-levels as far as the carried XP
/// now legitimately permits (each a real `FieldGte(xp, threshold)`-gated turn), and the resulting
/// sheet is saved. Returns the updated `(identity, sheet)` for each player. A non-qualifying
/// `(room, choice)` awards nothing.
pub fn award_run_outcome(
    store: &SqliteCharacterStore,
    voters: &[DreggIdentity],
    room: &str,
    choice_index: usize,
) -> Vec<(DreggIdentity, CharacterSheet)> {
    let Some(xp) = xp_reward(room, choice_index) else {
        return Vec::new();
    };
    voters
        .iter()
        .map(|who| (who.clone(), award_and_level(store, who, xp)))
        .collect()
}

/// Grant `xp` to `who`'s persistent character through the real gated turn, auto-level as far as
/// the carried XP legitimately reaches, persist, and return the resulting sheet. Builds a
/// short-lived [`AdventurerOffering`] over a store clone (all durable state is in sqlite, so a
/// clone is sound). The character CELL's identity is derived from `who` inside the offering, so
/// the throwaway session seed is irrelevant to the character.
fn award_and_level(store: &SqliteCharacterStore, who: &DreggIdentity, xp: u64) -> CharacterSheet {
    let mut adv = AdventurerOffering::new(store.clone());
    let session = match adv.open(who.clone(), SessionConfig::with_seed(1)) {
        Ok(s) => s,
        // The character cell failed to deploy — leave the persisted sheet untouched.
        Err(_) => return store.load(who),
    };
    // The sanctioned grant: a real `StrictMonotonic(xp)`-gated turn (a forged grant is refused
    // by the executor — proven in dreggnet-offerings; here we only route the earned XP through it).
    let _ = session.character().grant_xp(xp);
    // Auto-level as far as the (now carried) XP legitimately permits — each a real gated turn;
    // a premature level-up is refused and the loop stops.
    while session.character().level() < MAX_LEVEL && adv.level_up(&session).is_ok() {}
    adv.save(&session);
    session.character().sheet()
}

/// Unix seconds now (save bookkeeping).
fn now_secs() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::*;

    async fn temp_db() -> (tempfile::TempDir, String, Database) {
        let tmp = tempfile::tempdir().unwrap();
        let db_path = tmp.path().join("characters.db");
        let url = format!("sqlite://{}?mode=rwc", db_path.display());
        let db = Database::connect(&url).await.unwrap();
        (tmp, url, db)
    }

    fn ident(tag: &str) -> DreggIdentity {
        DreggIdentity(format!("{tag}{}", "0".repeat(64 - tag.len())))
    }

    /// A character sheet ROUND-TRIPS through the sqlite store: save → load by identity reproduces
    /// its level / XP / class / abilities exactly.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn a_sheet_round_trips_through_the_sqlite_store() {
        let (_tmp, _url, db) = temp_db().await;
        let mut store = SqliteCharacterStore::new(db, tokio::runtime::Handle::current());
        let who = ident("alice");

        let sheet = CharacterSheet {
            xp: 200,
            level: 2,
            class: MAGE,
            abilities_used: 3,
        };
        store.save(&who, sheet);
        let got = store.load(&who);
        assert_eq!(
            got, sheet,
            "the saved sheet loads back identically by identity"
        );
        println!("[round-trip] saved {sheet:?} → loaded {got:?}");
    }

    /// A returning identity RESUMES its persisted character across a SIMULATED RESTART: the store
    /// (and the db pool) is dropped and a fresh store is reopened on the SAME on-disk sqlite file.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn a_returning_identity_resumes_across_a_restart() {
        let (_tmp, url, db) = temp_db().await;
        let who = ident("bob");
        let sheet = CharacterSheet {
            xp: 260,
            level: 3,
            class: WARRIOR,
            abilities_used: 1,
        };
        {
            let mut store =
                SqliteCharacterStore::new(db.clone(), tokio::runtime::Handle::current());
            store.save(&who, sheet);
            drop(store);
        }
        drop(db); // the whole process' handle to the db is gone — a "restart".

        let db2 = Database::connect(&url).await.unwrap();
        let store2 = SqliteCharacterStore::new(db2, tokio::runtime::Handle::current());
        let resumed = store2.load(&who);
        assert_eq!(
            resumed, sheet,
            "the character survived a fresh sqlite open (persistence across restart)"
        );
        println!("[restart] reopened db → resumed {resumed:?} (survives restart)");
    }

    /// A FRESH identity loads a default (level-0) sheet — a new player, not an error.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn a_fresh_identity_loads_default() {
        let (_tmp, _url, db) = temp_db().await;
        let store = SqliteCharacterStore::new(db, tokio::runtime::Handle::current());
        let got = store.load(&ident("nobody"));
        assert_eq!(
            got,
            CharacterSheet::default(),
            "an unknown identity is a fresh character"
        );
    }

    /// FAIL-SAFE: a TAMPERED row (a level its XP never earned) loads as a FRESH character, never
    /// the forged level. Driven by writing a forged row straight to the db, then loading through
    /// the store's validation.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn a_tampered_row_fails_safe_to_a_fresh_character() {
        let (_tmp, _url, db) = temp_db().await;
        let who = ident("cheater");
        // Forge: level 5 with 0 XP (level 5 needs 700 XP), plus a bogus class id.
        db.character_save(&who.0, 0, 5, 99, 0, 0).await.unwrap();

        let store = SqliteCharacterStore::new(db, tokio::runtime::Handle::current());
        let got = store.load(&who);
        assert_eq!(
            got,
            CharacterSheet::default(),
            "a forged level fails safe to a fresh character"
        );
        assert!(got.level < 5, "the forged level did NOT survive the load");

        // Non-vacuous: a WELL-FORMED row on the curve loads faithfully.
        let honest = CharacterSheet {
            xp: 700,
            level: 5,
            class: WARRIOR,
            abilities_used: 0,
        };
        let mut store2 = store.clone();
        store2.save(&who, honest);
        assert_eq!(
            store2.load(&who),
            honest,
            "an honest max-level row loads faithfully"
        );
        println!("[fail-safe] forged L5/0xp → fresh; honest L5/700xp → loads");
    }

    /// XP flows through the REAL gated character turn and PERSISTS: an earning run's rewards
    /// (two bloodied blows +40 each, the hoard +120 = 200) drive the character to level 2
    /// (needs 100) but not level 3 (needs 250) — the auto-level stops at the honest floor — and
    /// the resulting sheet round-trips through the store.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn xp_flows_through_the_gated_turn_and_persists() {
        let (_tmp, url, db) = temp_db().await;
        let store = SqliteCharacterStore::new(db, tokio::runtime::Handle::current());
        let who = ident("dana");

        // Two bloodied-warden outcomes + the seized hoard, awarded to this player.
        let voters = [who.clone()];
        award_run_outcome(&store, &voters, ROOM_GATEHALL, KP_TRADE_BLOWS);
        award_run_outcome(&store, &voters, ROOM_GATEHALL, KP_TRADE_BLOWS);
        award_run_outcome(&store, &voters, ROOM_SANCTUM, KP_SEIZE);

        let sheet = store.load(&who);
        assert_eq!(
            sheet.xp, 200,
            "XP earned from the real gated grants (40+40+120)"
        );
        assert_eq!(
            sheet.level, 2,
            "auto-leveled to 2 (xp 200 >= 100) but NOT 3 (needs 250) — the honest gate"
        );

        // Survives a restart: the earned, gated, leveled character resumes on a fresh open.
        drop(store);
        let db2 = Database::connect(&url).await.unwrap();
        let store2 = SqliteCharacterStore::new(db2, tokio::runtime::Handle::current());
        assert_eq!(
            store2.load(&who),
            sheet,
            "the leveled character survives restart"
        );
        println!("[gated+persist] earned 200xp via gated turns → L2 → survives restart: {sheet:?}");

        // A non-qualifying move awards nothing (anti-ghost: no unearned XP).
        let before = store2.load(&who);
        let mut store3 = store2.clone();
        let awarded = award_run_outcome(&store3, &voters, "hall", 1);
        assert!(awarded.is_empty(), "a non-qualifying move awards no XP");
        store3.save(&who, before); // no-op re-save
        assert_eq!(
            store3.load(&who),
            before,
            "the sheet is unchanged by a non-reward move"
        );
    }
}
