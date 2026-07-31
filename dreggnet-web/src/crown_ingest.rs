//! # `crown_ingest` — **A RESULT EARNED ON ONE SURFACE, VERIFIED AGAIN ON THIS ONE.**
//!
//! A finished match of a portfolio game folds to ONE succinct proof (a **crown fold**). Discord
//! already does that end-to-end: [`discord-bot`'s `commands::crown`] enqueues the real recursive
//! fold, submits the resulting `WholeChainProof` to an in-process
//! [`dreggnet_game_board::GameBoard`], and persists the envelope plus the board CONFIG it was
//! accepted under (`vk` / `genesis_root` / `win_root`). The web had **no crown board at all** — so
//! a crown won in a Discord channel was invisible here, and vice versa.
//!
//! This module is the **receiving half**: a bearer-gated ingest door plus the board it feeds.
//!
//! ```text
//!   DISCORD (AWS edge, no inbound ports)          WEB (hbox, public via Tailscale Funnel)
//!   ─────────────────────────────────────         ─────────────────────────────────────────
//!   /crown → the real recursive fold              POST /crown/ingest   (Bearer, fail-closed)
//!   GameBoard::submit_bytes  ─ O(1) ─▶ ranked            │
//!   persist_fold(envelope + vk/genesis/win)              ▼
//!            │                                    probe-then-pin the anchor,
//!            └── reqwest POST over public HTTPS ─▶ GameBoard::submit_bytes  ─ O(1) ─▶ ranked
//!                                                        │
//!                                                 GET /crown          (the board, re-verified
//!                                                 GET /crown/results.json   on every read)
//! ```
//!
//! ## ⚑ A RESULT IS **RE-CHECKED HERE**, NEVER ADMITTED ON THE SENDER'S SAY-SO
//!
//! Nothing in the wire is believed *except the anchor, when no operator pinned one* — see the
//! next section, which is the one that decides what a row on this board is worth. The only
//! load-bearing field is `proof_b64` — the
//! `WholeChainProof` envelope — and it goes through
//! [`GameBoard::submit_bytes`](dreggnet_game_board::GameBoard::submit_bytes), which is *the same
//! O(1) accept path a live submission takes*: `dregg_lightclient::verify_history_bytes` under the
//! pinned VK, then the genesis binding, then the WIN binding, then the claimed-turn binding
//! (`ugc_dregg::verify_proof_completion`). A tampered envelope, a lied turn count, a proof for a
//! different game or a different universe is **REFUSED and nothing is stored**. The bearer token
//! answers "may this caller write here at all" — it never substitutes for the proof, and a caller
//! holding it still cannot get a bad fold ranked.
//!
//! Everything else on the wire (`origin`, `player`, `ruleset`) is a **LABEL**: it decides how the
//! row is displayed and grouped, and it is never an input to any verification. Say that out loud
//! rather than let a reader infer it from where the fields are used.
//!
//! ## ⚑ THE ANCHOR IS THE TRUST ROOT — AND UNTIL AN OPERATOR PINS ONE, A SUBMITTER MINTS IT
//!
//! The board's whole trust root is the [`ProofAnchor`] (`vk` + `genesis_root` + `win_root`). Read
//! it off the submitted proof and the genesis/WIN checks become self-comparisons — the submitter
//! picks their own win.
//!
//! **MEASURED 2026-07-30, and this module said the opposite until then.** The seam that was
//! supposed to supply a submission-independent anchor (`canonical_anchor`) returned `None`
//! unconditionally, so every deployment fell through to `row.anchor()`: the FIRST accepted fold's
//! own wire, frozen forever by the write-once `ensure_open`. Meanwhile the ingest handler answered
//! `"verified": true` with *"nothing was taken on the sender's word"*. The sender's word was the
//! anchor.
//!
//! What holds now:
//!
//! 1. **An operator may pin the anchor**, via
//!    [`dreggnet_game_board::operator_anchor`] — one environment variable per game, read from a
//!    place no submitter can write, and read by `discord-bot`'s board too so the two agree. A
//!    malformed spec REFUSES the admission rather than falling back to the bootstrap.
//! 2. **Absent that, the board still bootstraps** — the first row that survives a throwaway-board
//!    probe pins it — but the resulting
//!    [`AnchorProvenance::BootstrappedFromSubmission`](dreggnet_game_board::AnchorProvenance)
//!    rides on **every verdict this board prints**: the ingest response, `results.json`, and the
//!    board page, which says in its own chrome that it is RANKING SELF-REPORTED CLAIMS.
//! 3. **The word "verified" is written in exactly one place** — the ingest response's
//!    operator-anchored arm — and the key is ABSENT otherwise, so a consumer testing
//!    `verified === true` gets `undefined` for a self-anchored board rather than a softer string.
//!    What always happened is reported as `accepted`.
//! 4. The probe-before-pin still stands: a corrupt or hostile first row cannot freeze the board on
//!    an anchor nothing verifies against and refuse every honest crown behind it.
//!
//! ⚑ **The consequence, stated plainly because it bounds what this board can hold:** since the
//! anchor pins a *specific* genesis and a *specific* WIN root, only folds attesting **those** roots
//! rank. Two different matches of the same game generally attest different roots, so the second is
//! refused with `GenesisMismatch` / `WinNotProven`. That is not a property this module invented —
//! it is `ugc-dregg`'s accept rule and the Discord board lives under it too. A board that ranks
//! many distinct matches needs a per-match universe (an anchor per match) or a win predicate that
//! is a *property* of the final root rather than the root itself; both are game-board work, not
//! ingest work, and neither is done here.
//!
//! ## The ruleset string
//!
//! Every stored row carries a free-form `ruleset` label — which rules the result was earned under.
//! Nothing consumes it yet. It exists because a rules overhaul of The Descent is imminent
//! (`docs/reference/DESCENT-DECISION-SPACE-2026-07-26.md` changes `CAP`) and the archive repo
//! captures rulesets by content hash: a result stored today without one can never be told apart
//! from a result earned under the new rules. One string, no versioning machinery. Unstated is
//! rendered as `unstated`, never as a guess.
//!
//! ## Freshness
//!
//! A crown fold is **finished**. It is not live state and this page never pretends otherwise: each
//! row states when it was admitted here, and the board is re-verified (O(1) per row, the stored
//! envelope against the pinned anchor) **on every read**, so the verdict shown is this request's,
//! not a cached flag.
//!
//! ## What is NOT here (named, not hidden)
//!
//! * **The sender.** The bot's POST is documented on [`IngestFold`] down to the insertion point and
//!   the runtime gotcha; it is not wired, so today this door is armed and nothing knocks. That is a
//!   deliberate split: the receiving half is the half that must be careful, and it is testable
//!   alone.
//! * **The Descent's reverse direction.** Discord→web *already works* for The Descent
//!   (`discord-bot`'s `share_terminal_run` POSTs to `/descent/submit`, which re-verifies by
//!   REPLAY). Web→Discord needs the bot to PULL a machine-readable board; `GET /crown/results.json` is that
//!   shape for the crown lane, and the Descent lane would need an all-rows read on
//!   [`DescentState`](crate::DescentState) (it exposes only `runs_for_labels` today).
//! * **Per-origin tokens.** ONE shared secret authorizes the door, so `origin` is the authenticated
//!   sender's claim about *itself*. A second sender sharing the token could label its rows with the
//!   first one's origin. It could not forge a result — the proof still has to verify — so this is a
//!   provenance-label weakness, not a ranking one.

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};
use std::time::{SystemTime, UNIX_EPOCH};

use axum::Router;
use axum::extract::{DefaultBodyLimit, State};
use axum::http::{HeaderMap, StatusCode};
use axum::response::{Html, IntoResponse, Json, Response};
use axum::routing::{get, post};
use base64::Engine;
use base64::engine::general_purpose::STANDARD as BASE64;
use rusqlite::Connection;
use serde::{Deserialize, Serialize};
use subtle::ConstantTimeEq;
use zeroize::Zeroizing;

use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::{RecursionVk, SEG_ANCHOR_WIDTH};
use dreggnet_game_board::{AnchorProvenance, Game, GameBoard, ProofAnchor, UniverseId};
use webauth_core::identity_resolve::RootResolver;

use crate::{document, esc};

/// The env var an operator sets to the bearer token that authorizes `POST /crown/ingest`.
/// **UNSET ⇒ the ingest route is fail-closed** (every POST refused with `403`): an open ingest
/// door lets anyone mint a row under anyone's label, and while the *proof* would still have to
/// verify, the board's provenance column would not be worth reading. The board's READ surface
/// (`GET /crown`, `GET /crown/results.json`) is always mounted — a board nobody can read is not a
/// board.
pub const CROWN_INGEST_TOKEN_ENV: &str = "CROWN_INGEST_TOKEN";

/// The durable store's location — the SAME `DATABASE_URL` the Descent board uses, so one
/// deployment variable covers both. Unset ⇒ in-RAM (a restart forgets every admitted crown; they
/// are re-POSTable, and the sender's own store still holds them).
///
/// ⚑ It is the same FILE as the Descent board's, opened through a SECOND `rusqlite::Connection`.
/// The tables are disjoint (`crown_folds` vs `descent_*`) and both boards are single-writer and
/// low-traffic, so this is fine — but it is a second writer on one sqlite file, and if the deploy
/// ever gets busy that is where `SQLITE_BUSY` would first appear. Named rather than discovered.
pub const CROWN_DATABASE_URL_ENV: &str = "DATABASE_URL";

/// The request-body ceiling for `POST /crown/ingest`. A `WholeChainProof` envelope is the whole
/// match compressed to one succinct object, so it is small by design — but the recursion's
/// envelope size is a prover-side constant this module does not own, and a bound that refuses an
/// honest proof would be a silent outage. 32 MiB is far above anything the deployed fold emits and
/// far below anything that threatens the process.
const MAX_INGEST_BODY_BYTES: usize = 32 * 1024 * 1024;

/// The origins this board will label a row with. An unrecognised origin is stored as `other`
/// rather than reflected back into the page: the field is attacker-adjacent (an authenticated
/// sender writes it) and it is rendered, so it is normalized at the door instead of escaped
/// everywhere downstream.
const KNOWN_ORIGINS: [&str; 4] = ["discord", "telegram", "wechat", "web"];

// ═══════════════════════════════════════════════════════════════════════════════
// The wire.
// ═══════════════════════════════════════════════════════════════════════════════

/// **The JSON body of `POST /crown/ingest`** — one finished crown fold as it crosses the network.
///
/// ## What each field is for, and which ones are believed
///
/// | field | believed? | why |
/// |---|---|---|
/// | `proof_b64` | **verified** | the `WholeChainProof` envelope; the light client decides |
/// | `turns` | **verified** | bound against the attested turn count (`ResultMismatch` otherwise) |
/// | `vk` / `genesis_root` / `win_root` | **config** | the anchor; pinned once, probed before pinning, ignored thereafter |
/// | `game` | routing | which board; an unknown slug is refused |
/// | `player` | label | the attribution key the entry ranks under — see the module's attribution note |
/// | `origin` | label | which surface earned it; the sender's claim about itself |
/// | `ruleset` | label | which rules it was earned under; `""` ⇒ `unstated` |
///
/// ## The sender (NOT wired — this is the paste-in)
///
/// `discord-bot/src/commands/crown.rs::persist_fold` is the exact hook: it runs on the crown board
/// thread immediately after `board.submit_bytes` accepted the proof, and it already holds every
/// field this wire needs (`rec.game.slug()`, `rec.player`, `proof.turns()`, `proof.vk.0`,
/// `proof.attested.genesis_root.map(|f| f.0)`, `proof.attested.final_root.map(|f| f.0)`,
/// `proof.proof_bytes`).
///
/// ⚑ **The gotcha that will bite whoever wires it:** that function runs on a dedicated
/// non-tokio `std::thread` (`crown-board`), so `reqwest`'s async client has no runtime in scope
/// and `reqwest::blocking` is not in the bot's feature set
/// (`reqwest = { default-features = false, features = ["json", "rustls-tls"] }`). Either capture a
/// `tokio::runtime::Handle` at boot and `handle.spawn(...)` the POST, or add the `blocking`
/// feature. Do not call `Handle::current()` on the board thread — it panics.
///
/// The POST itself is the shape `share_terminal_run` already uses for the Descent lane: a 10s
/// `reqwest::Client`, `Authorization: Bearer $CROWN_INGEST_TOKEN`, and a failure that is LOGGED and
/// dropped — a crown that did not cross is still ranked on Discord, and a missing row is better
/// than a lying one.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct IngestFold {
    /// The board [`Game`]'s slug — `multiway-tug` or `automatafl`. An unknown slug is refused by
    /// name; this surface never invents a board for a game it does not host.
    pub game: String,
    /// Which surface earned the result (`discord` / `telegram` / `wechat` / `web`; anything else is
    /// stored as `other`). A LABEL and a namespace component, never a verification input.
    #[serde(default)]
    pub origin: String,
    /// The attribution key the entry ranks under — the sending surface's custodial identity hex
    /// (Discord's is `BLAKE3(bot_secret ‖ discord_user_id)`-derived, the full pubkey hex
    /// `identity_of` submits under). Stored VERBATIM: it is what the proof-carrying entry was
    /// ranked with, so rewriting it would make the board's own entry disagree with its display.
    pub player: String,
    /// **Which ruleset this result was earned under.** Free-form, one string, no versioning
    /// machinery. `""` renders as `unstated`.
    #[serde(default)]
    pub ruleset: String,
    /// The claimed turn count — BOUND against the proof's attested `num_turns`. A lie is
    /// `ResultMismatch` and the row is refused.
    pub turns: usize,
    /// The pinned anchor's root-circuit VK fingerprint, 64 lowercase hex.
    pub vk: String,
    /// The pinned anchor's genesis state anchor, as canonical `BabyBear` limbs.
    pub genesis_root: [u32; SEG_ANCHOR_WIDTH],
    /// The pinned anchor's WIN state anchor, as canonical `BabyBear` limbs.
    pub win_root: [u32; SEG_ANCHOR_WIDTH],
    /// The succinct whole-history proof envelope (`WholeChainProof::to_bytes()`), base64
    /// (standard alphabet, padded). **This is the only field that carries weight.**
    pub proof_b64: String,
}

// ═══════════════════════════════════════════════════════════════════════════════
// The stored row.
// ═══════════════════════════════════════════════════════════════════════════════

/// **One admitted crown fold as it is persisted** — the proof envelope plus the board CONFIG it was
/// accepted under, and nothing else. NOT the board state, and emphatically not the moves (there
/// are none: a proof-backed entry stores the envelope and the attested publics).
///
/// On boot every row is RE-SUBMITTED through the same O(1) accept path, so a restored row is one
/// THIS process verified itself, this run. A tampered proof, a lied turn count or a swapped anchor
/// is refused at exactly the same tooth and simply does not come back.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StoredFold {
    /// The content-derived row id (`cf-…`) — see [`fold_id`]. Namespaced by `origin`, so a Discord
    /// result and a web result can never collide even on byte-identical proofs.
    pub id: String,
    /// The game's slug (`multiway-tug` / `automatafl`).
    pub game: String,
    /// The surface that earned it (normalized; see `KNOWN_ORIGINS`).
    pub origin: String,
    /// The attribution key the entry ranks under.
    pub player: String,
    /// Which rules this result was earned under (`""` = unstated).
    pub ruleset: String,
    /// The attested turn count claimed at submit (re-checked against the proof on every restore).
    pub turns: usize,
    /// The pinned anchor's root-circuit VK fingerprint.
    pub vk: [u8; 32],
    /// The pinned anchor's genesis state anchor, as canonical `BabyBear` limbs.
    pub genesis_root: [u32; SEG_ANCHOR_WIDTH],
    /// The pinned anchor's WIN state anchor, as canonical `BabyBear` limbs.
    pub win_root: [u32; SEG_ANCHOR_WIDTH],
    /// The succinct whole-history proof envelope.
    pub proof: Vec<u8>,
    /// When THIS board first admitted the fold (unix seconds). Preserved across a restart: the
    /// result was earned then, not at boot. The page's only freshness claim is this number.
    pub admitted_at: u64,
}

impl StoredFold {
    /// Rebuild the [`ProofAnchor`] this fold claims to have been accepted against.
    ///
    /// `BabyBear::new` reduces, so a hand-edited row cannot smuggle a non-canonical limb past the
    /// anchor comparison. (It would still fail the light client; this keeps the stored
    /// representation from being the place a malleability question arises.)
    fn anchor(&self) -> ProofAnchor {
        ProofAnchor::new(
            RecursionVk(self.vk),
            self.genesis_root.map(BabyBear::new),
            self.win_root.map(BabyBear::new),
        )
    }
}

/// **The content-derived row id.** `blake3` over `origin ‖ game ‖ player ‖ proof`, with an explicit
/// separator so two different field splits cannot hash alike, rendered `cf-<24 hex>`.
///
/// Two properties this buys, both load-bearing:
/// * **an id namespace** — `origin` is inside the hash, so the same envelope arriving from Discord
///   and from the web are two distinct rows rather than a silent overwrite of one by the other;
/// * **idempotence** — a sender that retries a POST (its first attempt timed out after the row
///   landed) re-derives the same id, and the door answers with the existing row instead of ranking
///   the fold twice. `ugc_dregg::Registry::rank_entry` pushes unconditionally, so without this a
///   retry would put one human on the board twice.
pub fn fold_id(origin: &str, game: &str, player: &str, proof: &[u8]) -> String {
    let mut h = blake3::Hasher::new();
    h.update(b"dregg:crown-ingest:v1\x00");
    h.update(origin.as_bytes());
    h.update(b"\x00");
    h.update(game.as_bytes());
    h.update(b"\x00");
    h.update(player.as_bytes());
    h.update(b"\x00");
    h.update(proof);
    let hex = h.finalize().to_hex();
    format!("cf-{}", &hex.as_str()[..24])
}

// ═══════════════════════════════════════════════════════════════════════════════
// The durable store.
// ═══════════════════════════════════════════════════════════════════════════════

/// The crown board's durable seam — **sync** (`&self`), matching
/// [`DescentRunStore`](crate::descent_store::DescentRunStore). Persist MUST be idempotent by `id`,
/// so a double write / a double boot never duplicates a row.
pub trait CrownFoldStore: Send + Sync {
    /// Persist an admitted fold (idempotent by `id`).
    fn persist(&self, fold: &StoredFold) -> Result<(), String>;
    /// Every persisted fold, oldest `admitted_at` first — the anchor-pinning order, so the board
    /// comes up pinned to the same anchor it was pinned to before the restart.
    fn list(&self) -> Result<Vec<StoredFold>, String>;
}

/// A thread-safe in-memory [`CrownFoldStore`] — the fallback when no `DATABASE_URL` is set, and
/// the store the tests drive. Idempotent by `id`, matching the sqlite impl's `INSERT OR IGNORE`.
#[derive(Default)]
pub struct InMemoryCrownFoldStore {
    rows: Mutex<Vec<StoredFold>>,
}

impl InMemoryCrownFoldStore {
    /// A fresh empty store.
    pub fn new() -> InMemoryCrownFoldStore {
        InMemoryCrownFoldStore::default()
    }
}

impl CrownFoldStore for InMemoryCrownFoldStore {
    fn persist(&self, fold: &StoredFold) -> Result<(), String> {
        let mut g = self.rows.lock().map_err(|_| "store poisoned".to_string())?;
        if !g.iter().any(|r| r.id == fold.id) {
            g.push(fold.clone());
        }
        Ok(())
    }
    fn list(&self) -> Result<Vec<StoredFold>, String> {
        let mut rows = self
            .rows
            .lock()
            .map_err(|_| "store poisoned".to_string())?
            .clone();
        rows.sort_by(|a, b| a.admitted_at.cmp(&b.admitted_at).then(a.id.cmp(&b.id)));
        Ok(rows)
    }
}

/// `CREATE TABLE IF NOT EXISTS`, so an existing database is used as-is and a fresh one is
/// initialized. The anchor limbs are stored as JSON arrays of `u32` (readable in a DB browser, and
/// re-reduced through `BabyBear::new` on the way back in).
const MIGRATION: &str = "
CREATE TABLE IF NOT EXISTS crown_folds (
    id           TEXT PRIMARY KEY,
    game         TEXT NOT NULL,
    origin       TEXT NOT NULL,
    player       TEXT NOT NULL,
    ruleset      TEXT NOT NULL,
    turns        INTEGER NOT NULL,
    vk_hex       TEXT NOT NULL,
    genesis_json TEXT NOT NULL,
    win_json     TEXT NOT NULL,
    proof        BLOB NOT NULL,
    admitted_at  INTEGER NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_crown_folds_game ON crown_folds (game);
";

/// A [`CrownFoldStore`] persisted in a sqlite database (rusqlite — for the same one-`links`-package
/// reason [`crate::descent_store`] documents at length: `dreggnet-web` is a root-workspace member
/// and the workspace already links `sqlite3` exactly once).
pub struct SqliteCrownFoldStore {
    conn: Mutex<Connection>,
}

impl SqliteCrownFoldStore {
    /// Open (or create) the store at `url` and run the migration. Accepts a bare path, a
    /// `sqlite:PATH` / `sqlite://PATH` url (an optional `?query` is ignored), or `:memory:` /
    /// empty. Identical parsing to [`crate::descent_store::SqliteDescentRunStore::open`], because
    /// it is the SAME `DATABASE_URL`.
    pub fn open(url: &str) -> Result<SqliteCrownFoldStore, String> {
        let path = url
            .strip_prefix("sqlite://")
            .or_else(|| url.strip_prefix("sqlite:"))
            .unwrap_or(url);
        let path = path.split('?').next().unwrap_or(path);
        let conn = if path.is_empty() || path == ":memory:" {
            Connection::open_in_memory()
        } else {
            Connection::open(path)
        }
        .map_err(|e| e.to_string())?;
        conn.execute_batch(MIGRATION).map_err(|e| e.to_string())?;
        Ok(SqliteCrownFoldStore {
            conn: Mutex::new(conn),
        })
    }
}

impl CrownFoldStore for SqliteCrownFoldStore {
    fn persist(&self, fold: &StoredFold) -> Result<(), String> {
        let conn = self.conn.lock().map_err(|_| "store poisoned".to_string())?;
        let genesis_json = serde_json::to_string(&fold.genesis_root).map_err(|e| e.to_string())?;
        let win_json = serde_json::to_string(&fold.win_root).map_err(|e| e.to_string())?;
        conn.execute(
            "INSERT OR IGNORE INTO crown_folds
                (id, game, origin, player, ruleset, turns, vk_hex, genesis_json, win_json,
                 proof, admitted_at)
             VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11)",
            rusqlite::params![
                &fold.id,
                &fold.game,
                &fold.origin,
                &fold.player,
                &fold.ruleset,
                fold.turns as i64,
                &hex_of(&fold.vk),
                &genesis_json,
                &win_json,
                &fold.proof,
                fold.admitted_at as i64,
            ],
        )
        .map_err(|e| e.to_string())?;
        Ok(())
    }

    fn list(&self) -> Result<Vec<StoredFold>, String> {
        let conn = self.conn.lock().map_err(|_| "store poisoned".to_string())?;
        let mut stmt = conn
            .prepare(
                "SELECT id, game, origin, player, ruleset, turns, vk_hex, genesis_json, win_json,
                        proof, admitted_at
                 FROM crown_folds ORDER BY admitted_at ASC, id ASC",
            )
            .map_err(|e| e.to_string())?;
        let rows = stmt
            .query_map([], |row| {
                Ok((
                    row.get::<_, String>(0)?,
                    row.get::<_, String>(1)?,
                    row.get::<_, String>(2)?,
                    row.get::<_, String>(3)?,
                    row.get::<_, String>(4)?,
                    row.get::<_, i64>(5)?,
                    row.get::<_, String>(6)?,
                    row.get::<_, String>(7)?,
                    row.get::<_, String>(8)?,
                    row.get::<_, Vec<u8>>(9)?,
                    row.get::<_, i64>(10)?,
                ))
            })
            .map_err(|e| e.to_string())?;
        let mut out = Vec::new();
        for row in rows {
            let (id, game, origin, player, ruleset, turns, vk_hex, genesis, win, proof, at) =
                row.map_err(|e| e.to_string())?;
            // A malformed row is DROPPED, never coerced: it would fail the light client anyway,
            // and a silently-zeroed anchor limb is the kind of thing that turns a refusal into a
            // confusing one.
            let (Some(vk), Ok(genesis_root), Ok(win_root)) = (
                decode_hex32(&vk_hex),
                serde_json::from_str::<[u32; SEG_ANCHOR_WIDTH]>(&genesis),
                serde_json::from_str::<[u32; SEG_ANCHOR_WIDTH]>(&win),
            ) else {
                tracing::warn!(%id, "a persisted crown fold row is malformed and was dropped");
                continue;
            };
            out.push(StoredFold {
                id,
                game,
                origin,
                player,
                ruleset,
                turns: turns.max(0) as usize,
                vk,
                genesis_root,
                win_root,
                proof,
                admitted_at: at.max(0) as u64,
            });
        }
        Ok(out)
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// The board.
// ═══════════════════════════════════════════════════════════════════════════════

/// The game's **operator-configured board anchor** — the submission-independent trust root, read
/// from an environment variable no submitter can write, so the board verifies every surface's proof
/// against a genesis / WIN it did NOT choose.
///
/// This is `dreggnet_game_board::operator_anchor` verbatim; `discord-bot`'s crown board calls the
/// SAME function on the SAME variable, deliberately — the two boards must agree about what they are
/// pinned to, or a cross-surface fold can never rank on both.
///
/// `Ok(None)` ⇒ nothing is configured, and the board bootstraps from the first fold that survives a
/// throwaway-board probe and freezes there — which every verdict then reports as
/// [`AnchorProvenance::BootstrappedFromSubmission`]. `Err` ⇒ the variable is SET and malformed, and
/// the admission is refused rather than downgraded to the bootstrap the operator was configuring
/// their way out of.
fn operator_anchor(game: Game) -> Result<Option<ProofAnchor>, String> {
    dreggnet_game_board::operator_anchor(game)
}

/// The slug → [`Game`] map. An unknown slug is refused rather than defaulted.
fn game_of_slug(slug: &str) -> Option<Game> {
    [Game::MultiwayTug, Game::Automatafl]
        .into_iter()
        .find(|g| g.slug() == slug)
}

/// One fold that is **on the board** — the display facts, joined to the board entry by
/// `completion_id`. Every field here is either a fact the light client attested or a label the
/// module has already said is a label.
#[derive(Clone, Debug)]
pub struct Admitted {
    /// The content-derived row id.
    pub id: String,
    /// Which board.
    pub game: Game,
    /// Which surface earned it.
    pub origin: String,
    /// The attribution key the entry ranks under (the sending surface's custodial identity).
    pub player: String,
    /// Which rules it was earned under (`""` = unstated).
    pub ruleset: String,
    /// The attested turn count — the rank key.
    pub turns: usize,
    /// The board universe the entry lives in.
    pub universe: UniverseId,
    /// The accepted entry's content id — the re-verify key.
    pub completion_id: [u8; 32],
    /// The proof envelope's size (the honest "this is the WHOLE match" line).
    pub proof_len: usize,
    /// The pinned anchor's VK fingerprint prefix (hex) — the board's trust root, shown so a reader
    /// can compare it against the one the sending surface published.
    pub vk8: String,
    /// ⚑ **WHERE THE TRUST ROOT CAME FROM** — the one fact that decides what this row's ✓ is worth.
    /// Rides on every verdict rather than living in a comment.
    pub anchor_provenance: AnchorProvenance,
    /// When this board admitted the fold (unix seconds). The page's only freshness claim.
    pub admitted_at: u64,
}

#[derive(Default)]
struct Inner {
    board: GameBoard,
    /// The per-game trust anchor, pinned ONCE and never re-minted from a submitted proof, PLUS
    /// where it came from. The provenance is stored beside the anchor and not recomputed, because
    /// it is a fact about the pin that happened, not about the environment at read time.
    anchors: BTreeMap<Game, (ProofAnchor, AnchorProvenance)>,
    admitted: Vec<Admitted>,
}

/// **The web's crown board** — one [`GameBoard`] plus the durable rows behind it, behind one
/// `Mutex`. Shared as an axum `State<Arc<CrownIngestState>>`.
pub struct CrownIngestState {
    inner: Mutex<Inner>,
    store: Option<Arc<dyn CrownFoldStore>>,
    /// `blake3(ingest bearer token)`, or `None` when no token is configured — in which case
    /// `POST /crown/ingest` is **fail-closed**. Stored as the hash so the plaintext is never held.
    ingest_token: Option<[u8; 32]>,
}

impl CrownIngestState {
    /// A fresh board with no durable backing and the ingest door fail-closed.
    pub fn new() -> CrownIngestState {
        CrownIngestState {
            inner: Mutex::new(Inner::default()),
            store: None,
            ingest_token: None,
        }
    }

    /// A fresh board backed by a durable [`CrownFoldStore`]. Call
    /// [`load_from_store`](Self::load_from_store) afterwards to re-admit its rows.
    pub fn with_store(store: Arc<dyn CrownFoldStore>) -> CrownIngestState {
        CrownIngestState {
            store: Some(store),
            ..CrownIngestState::new()
        }
    }

    /// Arm the ingest bearer. `None` (or an empty/whitespace token) leaves the door **fail-closed**.
    /// Only the token's `blake3` hash is retained.
    pub fn with_ingest_token(mut self, token: Option<String>) -> CrownIngestState {
        self.ingest_token = token
            .map(Zeroizing::new)
            .filter(|t| !t.trim().is_empty())
            .map(|t| *blake3::hash(t.trim().as_bytes()).as_bytes());
        self
    }

    /// Whether the ingest door is armed at all (an operator token is configured).
    pub fn ingest_armed(&self) -> bool {
        self.ingest_token.is_some()
    }

    /// **Authorize an ingest POST.** Fail-closed: no configured token ⇒ the route is disabled
    /// (`403`); otherwise the request MUST carry `Authorization: Bearer <token>`, constant-time
    /// compared over the `blake3` hashes (`401` on missing / wrong).
    fn authorize(&self, headers: &HeaderMap) -> Result<(), Response> {
        let Some(expected) = self.ingest_token.as_ref() else {
            return Err((
                StatusCode::FORBIDDEN,
                format!(
                    "crown ingest is disabled: set {CROWN_INGEST_TOKEN_ENV} and send it as \
                     `Authorization: Bearer <token>`. An open ingest door lets anyone mint a row \
                     under anyone's label, so it is fail-closed without an operator token."
                ),
            )
                .into_response());
        };
        let presented = headers
            .get(axum::http::header::AUTHORIZATION)
            .and_then(|v| v.to_str().ok())
            .and_then(|v| v.strip_prefix("Bearer "))
            .map(str::trim)
            .filter(|t| !t.is_empty());
        let Some(token) = presented else {
            return Err((
                StatusCode::UNAUTHORIZED,
                "crown ingest requires `Authorization: Bearer <operator token>`",
            )
                .into_response());
        };
        let got = blake3::hash(token.as_bytes());
        if got.as_bytes().ct_eq(expected).into() {
            Ok(())
        } else {
            Err((StatusCode::UNAUTHORIZED, "crown ingest token rejected").into_response())
        }
    }

    /// **THE ONE ADMISSION PATH.** Every row — a live POST and a boot restore alike — reaches the
    /// board through exactly this function, so there is no second, laxer door.
    ///
    /// 1. resolve the game (unknown slug ⇒ refused);
    /// 2. idempotence: a row id already on the board returns the existing [`Admitted`] and submits
    ///    nothing (`rank_entry` pushes unconditionally, so a retried POST would otherwise double-rank);
    /// 3. **pin the anchor**: operator configuration if [`operator_anchor`] supplies one (a
    ///    malformed spec is an `Err` here, never a downgrade), else **probe-before-pin** — verify
    ///    the row against its OWN claimed anchor on a THROWAWAY [`GameBoard`] first, so a corrupt
    ///    or hostile first row cannot freeze the trust root on something nothing verifies against.
    ///    ⚑ The bootstrap arm records [`AnchorProvenance::BootstrappedFromSubmission`] on the
    ///    [`Admitted`], and every surface that renders the row prints it;
    /// 4. `ensure_open` (write-once) + `submit_bytes` — the O(1) light client, the genesis binding,
    ///    the WIN binding, the claimed-turns binding. `Err` here means **nothing is admitted**.
    ///
    /// The caller persists only on `Ok`.
    pub fn admit(&self, row: &StoredFold) -> Result<Admitted, String> {
        let Some(game) = game_of_slug(&row.game) else {
            return Err(format!(
                "no crown board for game `{}` (known: multiway-tug, automatafl)",
                row.game
            ));
        };
        let mut inner = self
            .inner
            .lock()
            .map_err(|_| "board poisoned".to_string())?;

        if let Some(existing) = inner.admitted.iter().find(|a| a.id == row.id) {
            return Ok(existing.clone());
        }

        if !inner.anchors.contains_key(&game) {
            // ⚑ AN OPERATOR ANCHOR REMOVES THE BOOTSTRAP ENTIRELY. Absent one, the first row that
            // SURVIVES a probe pins the board — and the resulting provenance travels with every
            // verdict this board ever prints, because that anchor came from a submitter's wire.
            // A MALFORMED operator spec is refused here, never downgraded: an operator who meant
            // to pin the board must not silently get the submitter-chosen anchor instead.
            let (candidate, provenance) = match operator_anchor(game)? {
                Some(a) => (a, AnchorProvenance::OperatorConfigured),
                None => (row.anchor(), AnchorProvenance::BootstrappedFromSubmission),
            };
            let mut probe = GameBoard::new();
            probe.ensure_open(game, candidate.clone());
            probe
                .submit_bytes(game, &row.player, row.proof.clone(), row.turns)
                .map_err(|e| {
                    format!(
                        "the fold did NOT verify against the anchor it would pin the {} board to \
                         ({e}) — refused, and the board stays unpinned",
                        game.slug()
                    )
                })?;
            if provenance == AnchorProvenance::BootstrappedFromSubmission {
                tracing::warn!(
                    game = game.slug(),
                    env = %dreggnet_game_board::env_var_name(game),
                    "the crown board pinned its trust root to a SUBMITTED fold's own anchor and \
                     froze there — it is now ranking self-reported claims. Set the named variable \
                     to pin it to operator configuration instead."
                );
            }
            inner.anchors.insert(game, (candidate, provenance));
        }
        let (anchor, provenance) = inner
            .anchors
            .get(&game)
            .expect("the anchor was just pinned or already present")
            .clone();
        let universe = inner.board.ensure_open(game, anchor);
        let accepted = inner
            .board
            .submit_bytes(game, &row.player, row.proof.clone(), row.turns)
            .map_err(|e| format!("the proof-carrying board REFUSED the fold: {e}"))?;

        let admitted = Admitted {
            id: row.id.clone(),
            game,
            origin: row.origin.clone(),
            player: row.player.clone(),
            ruleset: row.ruleset.clone(),
            turns: accepted.turns,
            universe,
            completion_id: accepted.completion_id,
            proof_len: row.proof.len(),
            vk8: hex_of(&row.vk[..4]),
            anchor_provenance: provenance,
            admitted_at: row.admitted_at,
        };
        inner.admitted.push(admitted.clone());
        Ok(admitted)
    }

    /// **Admit and persist** — the live-POST path. Persists ONLY after the board accepted.
    pub fn admit_and_persist(&self, row: &StoredFold) -> Result<Admitted, String> {
        let admitted = self.admit(row)?;
        if let Some(store) = &self.store {
            if let Err(e) = store.persist(row) {
                // The fold IS ranked; only its survival across a restart is at risk. Say so loudly
                // rather than fail a request whose verification succeeded.
                tracing::warn!(
                    id = %row.id,
                    error = %e,
                    "a crown fold RANKED on the web board but did not persist — it will not \
                     survive a restart"
                );
            }
        }
        Ok(admitted)
    }

    /// **Boot restore** — put every persisted fold back on a fresh board by RE-SUBMITTING its
    /// proof through [`admit`](Self::admit). A row that does not survive that gate is dropped with
    /// a warning: this is a re-VERIFICATION, not a restoration of trust. No-op with no store.
    pub fn load_from_store(&self) {
        let Some(store) = self.store.clone() else {
            return;
        };
        let rows = match store.list() {
            Ok(rows) => rows,
            Err(e) => {
                tracing::warn!(error = %e, "the crown fold store could not be read — nothing restored");
                return;
            }
        };
        let (mut restored, mut refused) = (0usize, 0usize);
        for row in rows {
            // The id is content-derived, so a DB edit cannot rename one authentic fold into
            // another row: re-derive it and drop the row if it disagrees.
            if fold_id(&row.origin, &row.game, &row.player, &row.proof) != row.id {
                tracing::warn!(id = %row.id, "a persisted crown fold's id is not its content id — dropped");
                refused += 1;
                continue;
            }
            match self.admit(&row) {
                Ok(_) => restored += 1,
                Err(e) => {
                    tracing::warn!(id = %row.id, error = %e, "a persisted crown fold did NOT re-verify and was not restored");
                    refused += 1;
                }
            }
        }
        if restored > 0 || refused > 0 {
            tracing::info!(
                restored,
                refused,
                "web crown board restored folds by re-running the O(1) light client"
            );
        }
    }

    /// **The board as of THIS read** — every admitted row re-verified O(1) against the pinned
    /// anchor, resolved to humans, merged one row per human, ranked by attested turns.
    ///
    /// Blocking (one light-client run per row + one link-store scan); the handlers call it inside
    /// `spawn_blocking`.
    pub fn snapshot(&self) -> Vec<BoardView> {
        // ONE link-store scan for the whole render, never per row.
        let resolver = RootResolver::load();
        let inner = match self.inner.lock() {
            Ok(g) => g,
            Err(_) => return Vec::new(),
        };
        let mut views: Vec<BoardView> = Vec::new();
        for game in [Game::MultiwayTug, Game::Automatafl] {
            if !inner.board.is_open(game) {
                continue;
            }
            let mut rows: Vec<BoardRow> = inner
                .admitted
                .iter()
                .filter(|a| a.game == game)
                .map(|a| {
                    // ⚑ RE-VERIFIED ON THE READ, not read off a stored flag. `reverify` re-runs the
                    // whole-history light client on the STORED envelope against the pinned anchor —
                    // never a replay, because the moves were never posted.
                    let reverified = inner.board.reverify(game, &a.completion_id).ok();
                    BoardRow {
                        id: a.id.clone(),
                        origin: a.origin.clone(),
                        player: a.player.clone(),
                        // DISPLAY / GROUPING ONLY. Attribution is untouched: the entry is ranked
                        // under, and the proof attributed to, the custodial key above. An UNLINKED
                        // key resolves to itself, so an un-linked board renders exactly as it would
                        // with no resolver at all.
                        human: resolver.resolve(&a.player),
                        ruleset: a.ruleset.clone(),
                        turns: a.turns,
                        reverified_turns: reverified,
                        proof_len: a.proof_len,
                        vk8: a.vk8.clone(),
                        admitted_at: a.admitted_at,
                    }
                })
                .collect();
            // Rank by attested turns (lower first); stable tie-break on the id so the page is
            // deterministic.
            rows.sort_by(|a, b| a.turns.cmp(&b.turns).then_with(|| a.id.cmp(&b.id)));
            // ONE ROW PER HUMAN, their best fold. Resolving WITHOUT merging only RELABELS — two
            // platforms of one person still occupy two rows, which is the exact defect the crown
            // board review caught on Discord and the Descent board already fixed.
            let mut seen: Vec<String> = Vec::new();
            rows.retain(|r| {
                if seen.iter().any(|h| h == &r.human) {
                    return false;
                }
                seen.push(r.human.clone());
                true
            });
            views.push(BoardView {
                game,
                universe: inner.board.universe(game),
                // The private-strategy property, asserted alongside non-emptiness (it is vacuously
                // true of an empty board).
                stores_no_moves: inner.board.stores_no_moves(game),
                anchor_provenance: inner.anchors.get(&game).map(|(_, p)| *p),
                rows,
            });
        }
        views
    }
}

impl Default for CrownIngestState {
    fn default() -> Self {
        CrownIngestState::new()
    }
}

/// One game's board as of a read.
#[derive(Clone, Debug)]
pub struct BoardView {
    /// Which game.
    pub game: Game,
    /// The board universe's content address, if the board is open.
    pub universe: Option<UniverseId>,
    /// Every ranked entry is proof-backed and stores NO moves.
    pub stores_no_moves: bool,
    /// ⚑ **WHERE THIS BOARD'S TRUST ROOT CAME FROM.** `None` = the board is open but nothing
    /// pinned it (unreachable today; `ensure_open` and the pin happen together). Every rendering
    /// of this view prints it.
    pub anchor_provenance: Option<AnchorProvenance>,
    /// The ranked rows, best first, one per human.
    pub rows: Vec<BoardRow>,
}

/// One ranked row as of a read.
#[derive(Clone, Debug)]
pub struct BoardRow {
    /// The content-derived row id.
    pub id: String,
    /// Which surface earned it.
    pub origin: String,
    /// The attribution key the entry is ranked under.
    pub player: String,
    /// WHICH HUMAN this row belongs to — the resolved account id when the custodial key is linked,
    /// else the key itself. Used to merge a person's surfaces into one row; never part of any
    /// verification.
    pub human: String,
    /// Which rules it was earned under (`""` = unstated).
    pub ruleset: String,
    /// The turn count the board ranked it by.
    pub turns: usize,
    /// The turn count THIS read's O(1) re-verification re-attested. `None` = the stored envelope no
    /// longer verifies against the pinned anchor, which is shown as a refusal rather than hidden.
    pub reverified_turns: Option<usize>,
    /// The proof envelope's size in bytes.
    pub proof_len: usize,
    /// The pinned anchor's VK fingerprint prefix.
    pub vk8: String,
    /// When this board admitted the fold (unix seconds).
    pub admitted_at: u64,
}

// ═══════════════════════════════════════════════════════════════════════════════
// Router + handlers.
// ═══════════════════════════════════════════════════════════════════════════════

/// **Mount the cross-surface crown board from the environment.**
///
/// * the durable store comes from [`CROWN_DATABASE_URL_ENV`] (the same `DATABASE_URL` the Descent
///   board uses) — unset / unopenable ⇒ in-RAM, logged;
/// * the ingest bearer comes from [`CROWN_INGEST_TOKEN_ENV`] — unset ⇒ `POST /crown/ingest` is
///   fail-closed, logged either way, so "the door is shut" is never a silent state;
/// * the READ surface is mounted unconditionally.
///
/// Additive: the `/crown` prefix overlaps nothing else the app serves.
pub fn crown_ingest_from_env() -> Router {
    let store: Option<Arc<dyn CrownFoldStore>> = match std::env::var(CROWN_DATABASE_URL_ENV) {
        Ok(url) if !url.is_empty() => match SqliteCrownFoldStore::open(&url) {
            Ok(s) => {
                tracing::info!(%url, "crown board: durable sqlite store");
                Some(Arc::new(s))
            }
            Err(e) => {
                tracing::warn!(%url, error = %e, "could not open the crown store — the board is in-RAM this run");
                None
            }
        },
        _ => None,
    };
    let token = std::env::var(CROWN_INGEST_TOKEN_ENV)
        .ok()
        .filter(|t| !t.trim().is_empty());
    if token.is_some() {
        tracing::info!(
            "crown ingest ARMED behind {CROWN_INGEST_TOKEN_ENV} (POST /crown/ingest requires an \
             operator bearer; the proof is verified here regardless)"
        );
    } else {
        tracing::info!(
            "crown ingest FAIL-CLOSED — {CROWN_INGEST_TOKEN_ENV} unset, so POST /crown/ingest \
             refuses every call. GET /crown still serves the board."
        );
    }
    let state = match store {
        Some(s) => CrownIngestState::with_store(s),
        None => CrownIngestState::new(),
    }
    .with_ingest_token(token);
    let state = Arc::new(state);
    state.load_from_store();
    crown_ingest_router(state)
}

/// **Build the crown board router** over a shared [`CrownIngestState`].
///
/// - `POST /crown/ingest` — the bearer-gated, independently-VERIFIED cross-surface result door;
/// - `GET  /crown` — the board, re-verified on every read;
/// - `GET  /crown/results.json` — the same board, machine-readable, so another surface can PULL
///   what was earned here (the reverse direction's transport).
pub fn crown_ingest_router(state: Arc<CrownIngestState>) -> Router {
    Router::new()
        .route("/crown", get(get_board))
        .route("/crown/results.json", get(results_json))
        .route(
            "/crown/ingest",
            post(post_ingest).layer(DefaultBodyLimit::max(MAX_INGEST_BODY_BYTES)),
        )
        .with_state(state)
}

/// `POST /crown/ingest` — admit one finished crown fold from another surface.
///
/// The body is taken as a `String` (not `Json<…>`) so authorization is decided BEFORE anything
/// parses attacker-supplied bytes.
async fn post_ingest(
    State(state): State<Arc<CrownIngestState>>,
    headers: HeaderMap,
    body: String,
) -> Response {
    if let Err(resp) = state.authorize(&headers) {
        return resp;
    }
    let wire: IngestFold = match serde_json::from_str(&body) {
        Ok(w) => w,
        Err(e) => return refused(format!("crown fold JSON: {e}")),
    };
    let Some(vk) = decode_hex32(&wire.vk) else {
        return refused("`vk` must be 64 lowercase hex characters".to_string());
    };
    // ⚑ `player` is the ATTRIBUTION KEY the board ranks under and the link resolver matches, so it
    // is bounded and REFUSED rather than clamped: silently truncating it would file the result
    // under a key that is nobody's. The custodial identities every surface submits are 64 hex.
    if wire.player.trim().is_empty() || wire.player.chars().count() > 128 {
        return refused(
            "`player` must be a non-empty identity of at most 128 characters (a surface's \
             custodial pubkey hex is 64)"
                .to_string(),
        );
    }
    let proof = match BASE64.decode(wire.proof_b64.as_bytes()) {
        Ok(p) if !p.is_empty() => p,
        Ok(_) => return refused("`proof_b64` decoded to an empty envelope".to_string()),
        Err(e) => return refused(format!("`proof_b64` is not valid base64: {e}")),
    };
    let origin = normalize_origin(&wire.origin);
    let row = StoredFold {
        id: fold_id(&origin, &wire.game, &wire.player, &proof),
        game: wire.game.clone(),
        origin,
        player: wire.player.clone(),
        ruleset: clamp_label(&wire.ruleset),
        turns: wire.turns,
        vk,
        genesis_root: wire.genesis_root,
        win_root: wire.win_root,
        proof,
        admitted_at: now_secs(),
    };

    // The light client is the expensive part; keep it off the reactor, exactly as the native
    // Descent lane keeps its settle off it.
    let admitted = match tokio::task::spawn_blocking(move || state.admit_and_persist(&row)).await {
        Ok(Ok(a)) => a,
        Ok(Err(e)) => return refused(e),
        Err(e) => return refused(format!("crown ingest task join: {e}")),
    };

    (StatusCode::OK, Json(ingest_ok_body(&admitted))).into_response()
}

/// **THE ONE PLACE THE WORD `verified` IS WRITTEN ON THIS SURFACE.**
///
/// `accepted` is what always happened on this path: the O(1) light client ran HERE and
/// admitted the envelope against the board's pinned anchor. Whether that is a **trust
/// decision** depends entirely on where the anchor came from, so `verified` is added on the
/// operator-anchored arm ONLY and the key is **ABSENT** otherwise — a consumer testing
/// `verified === true` gets `undefined` for a self-anchored board rather than a softer
/// string it skims past. `anchor_provenance` is the branchable token underneath it.
///
/// Split out of the handler so the property is structural and directly testable; see
/// `the_success_word_is_written_only_for_an_operator_pinned_anchor`.
fn ingest_ok_body(admitted: &Admitted) -> serde_json::Value {
    let prov = admitted.anchor_provenance;
    let mut body = serde_json::json!({
        "accepted": true,
        "ranked": true,
        "kind": "o1-light-client-accept",
        "anchor_provenance": prov.token(),
        "id": admitted.id,
        "game": admitted.game.slug(),
        "origin": admitted.origin,
        "player": admitted.player,
        "ruleset": ruleset_or_unstated(&admitted.ruleset),
        "turns": admitted.turns,
        "proof_bytes": admitted.proof_len,
        "vk8": admitted.vk8,
        "admitted_at": admitted.admitted_at,
        "board": "/crown",
        "detail": format!(
            "the whole-history light client accepted this envelope on this server, just now, \
             against this board's pinned anchor — and {}",
            prov.sentence(admitted.game),
        ),
    });
    if prov.is_trust_decision() {
        body["verified"] = serde_json::Value::Bool(true);
    }
    body
}

/// A refusal that says what was refused and asserts that nothing was retained.
fn refused(error: String) -> Response {
    (
        StatusCode::BAD_REQUEST,
        Json(serde_json::json!({
            // `verified` is deliberately ABSENT here too — it is written on exactly one arm of
            // exactly one handler. `accepted: false` is the refusal's own word.
            "accepted": false,
            "ranked": false,
            "kind": "o1-light-client-accept",
            "error": error,
            "detail": "the crown board refused the fold; nothing was ranked and nothing was stored",
        })),
    )
        .into_response()
}

/// `GET /crown/results.json` — **the machine-readable board**, so another surface can render what
/// was earned here without scraping HTML. Every row is re-verified on this read, and the payload
/// says when: `as_of` is the read, `admitted_at` is when the result arrived. A crown fold is
/// FINISHED, so those two numbers are the whole freshness story — this is never a live view and
/// does not claim to be.
async fn results_json(State(state): State<Arc<CrownIngestState>>) -> Response {
    let views = match tokio::task::spawn_blocking(move || state.snapshot()).await {
        Ok(v) => v,
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": format!("crown board read: {e}") })),
            )
                .into_response();
        }
    };
    let boards: Vec<serde_json::Value> = views
        .iter()
        .map(|v| {
            serde_json::json!({
                "game": v.game.slug(),
                "title": v.game.title(),
                "universe": v.universe.map(|u| hex_of(u.as_bytes())),
                "stores_no_moves": v.stores_no_moves,
                // ⚑ PER BOARD, because the pin is per board. A consumer ranking these rows against
                // any other surface's needs this before it needs anything else here.
                "anchor_provenance": v.anchor_provenance.map(|p| p.token()),
                "anchor_note": v.anchor_provenance.map(|p| p.sentence(v.game)),
                "rows": v.rows.iter().enumerate().map(|(i, r)| serde_json::json!({
                    "rank": i + 1,
                    "id": r.id,
                    "origin": r.origin,
                    "player": r.player,
                    "human": r.human,
                    "ruleset": ruleset_or_unstated(&r.ruleset),
                    "turns": r.turns,
                    "reverified": r.reverified_turns.is_some(),
                    "reverified_turns": r.reverified_turns,
                    "proof_bytes": r.proof_len,
                    "vk8": r.vk8,
                    "admitted_at": r.admitted_at,
                })).collect::<Vec<_>>(),
            })
        })
        .collect();
    Json(serde_json::json!({
        "as_of": now_secs(),
        "verification": "each row re-ran the O(1) whole-history light client on its stored proof \
                         envelope against its board's pinned anchor, on this read. ⚑ What that is \
                         WORTH is `anchor_provenance` on each board below: `operator-configured` \
                         means the anchor is config no submitter can write; \
                         `bootstrapped-from-first-submission` means the board froze onto an anchor \
                         a submitter minted, and is ranking self-reported claims.",
        "boards": boards,
    }))
    .into_response()
}

/// `GET /crown` — the board a stranger reads.
async fn get_board(State(state): State<Arc<CrownIngestState>>) -> Html<String> {
    let armed = state.ingest_armed();
    let views = tokio::task::spawn_blocking(move || state.snapshot())
        .await
        .unwrap_or_default();
    Html(board_page(&views, armed))
}

fn board_page(views: &[BoardView], ingest_armed: bool) -> String {
    let mut sections = String::new();
    if views.is_empty() {
        sections.push_str(
            "<section class=\"deos-section tag-muted\"><h2>No crown has crossed yet</h2>\
             <p class=\"prose\">A row appears here only once its proof passes this server's own \
             O(1) light client against this board's pinned anchor. A result is never listed \
             because a sender said so — though until an operator pins an anchor, the FIRST \
             accepted fold supplies one, and every board says which case it is in.</p>\
             </section>",
        );
    }
    for v in views {
        sections.push_str(&format!(
            "<section class=\"deos-section\"><p class=\"eyebrow\">Succinct fold · O(1) accept</p>\
             <h2>{title}</h2><p class=\"prose\">Every row below is a finished match folded to ONE \
             proof and re-run through the whole-history light client <em>on this request</em> \
             against this board's pinned anchor: no moves were posted, and none are stored. \
             <strong>One row per human, not per account:</strong> a player who has \
             <a href=\"/identity/link\">proven</a> that their chat and web identities are the same \
             person ranks once, on their best fold; an unlinked player is their own human, so \
             nothing groups by accident.</p>",
            title = esc(v.game.title()),
        ));
        // ⚑ THE ANCHOR'S PROVENANCE, ON THE BOARD ITSELF, ABOVE THE ROWS. The rank column is
        // meaningless without it: an accept against a submitter-minted anchor is a consistency
        // check, and a reader must not have to infer that from a footnote.
        match v.anchor_provenance {
            Some(p) if p.is_trust_decision() => sections.push_str(&format!(
                "<div class=\"receipt ok\"><span class=\"dot\"></span>\
                 <span class=\"label\">operator-pinned anchor</span>\
                 <span class=\"detail\">{}</span></div>",
                esc(&p.sentence(v.game)),
            )),
            Some(p) => sections.push_str(&format!(
                "<div class=\"receipt warn\"><span class=\"dot\"></span>\
                 <span class=\"label\">RANKING SELF-REPORTED CLAIMS</span>\
                 <span class=\"detail\">{}</span></div>\
                 <p class=\"prose\"><strong>What that means for the ranking below.</strong> The \
                 proofs are real and this server really did re-run the light client on each of \
                 them just now. But the genesis root and the WIN root every one of them is checked \
                 against were taken from the first fold this board accepted, and frozen. A player \
                 who folds first defines what winning <em>is</em> here — so read this table as \
                 <em>these folds agree with the first fold's own claim about the game</em>, not as \
                 <em>these players won</em>.</p>",
                esc(&p.sentence(v.game)),
            )),
            None => {}
        }
        sections.push_str(&format!(
            "<div class=\"kv\">\
             <div><p class=\"k\">Board universe</p><p class=\"v mono\">{universe}</p></div>\
             <div><p class=\"k\">Moves stored</p><p class=\"v mono\">{moves}</p></div>\
             </div>",
            universe = esc(&v
                .universe
                .map(|u| hex_of(&u.as_bytes()[..8]))
                .unwrap_or_else(|| "not open".to_string())),
            moves = if v.stores_no_moves { "none" } else { "SOME" },
        ));
        if v.rows.is_empty() {
            sections.push_str("<p class=\"tag-muted\">No fold has re-verified on this board.</p>");
        } else {
            sections.push_str(
                "<div class=\"table-wrap\"><table class=\"board\"><thead><tr><th>#</th>\
                 <th>player</th><th>earned on</th><th>ruleset</th><th>turns</th>\
                 <th>re-verified now</th><th>proof</th><th>admitted</th></tr></thead><tbody>",
            );
            for (i, r) in v.rows.iter().enumerate() {
                sections.push_str(&format!(
                    "<tr><td class=\"rank\">{rank}</td>\
                     <td class=\"player mono\">{player}</td>\
                     <td>{origin}</td><td class=\"mono\">{ruleset}</td>\
                     <td class=\"num\">{turns}</td><td>{verdict}</td>\
                     <td class=\"num\">{proof} B</td><td class=\"mono\">{at}</td></tr>",
                    rank = i + 1,
                    // CHAR-wise, never byte-wise: `player` is written by the sending surface, and a
                    // byte slice through a multi-byte character is a panic in a render path.
                    player = esc(&short(&r.player, 12)),
                    origin = esc(&r.origin),
                    ruleset = esc(&ruleset_or_unstated(&r.ruleset)),
                    turns = r.turns,
                    verdict = match r.reverified_turns {
                        Some(t) if t == r.turns => "✓ accepted".to_string(),
                        Some(t) => format!("⚠ re-attested {t} turns"),
                        None => "✗ REFUSED".to_string(),
                    },
                    proof = r.proof_len,
                    at = r.admitted_at,
                ));
            }
            sections.push_str("</tbody></table></div>");
        }
        sections.push_str("</section>");
    }
    let door = if ingest_armed {
        "The cross-surface door is <strong>armed</strong>: an authenticated surface may POST a \
         finished fold to <span class=\"mono\">/crown/ingest</span>, and this server verifies it \
         before it can rank."
    } else {
        "The cross-surface door is <strong>closed</strong> (no operator token configured), so this \
         board holds only what it already admitted. It is closed rather than open because an open \
         ingest lets anyone mint a row under anyone's label."
    };
    let body = format!(
        "<main class=\"session\">\
         <div class=\"page-head\" style=\"padding-top:var(--s4)\">\
         <p class=\"eyebrow\">Re-verified on this request</p>\
         <h1>Crowns · one board, every surface</h1>\
         <p class=\"deck\">A finished match of a portfolio game folds to ONE succinct proof. A crown \
         won in a Discord channel and a crown won here rank on the SAME board, and this server \
         re-runs the whole-history light client itself on every read rather than taking another \
         surface's word for a result. <strong>A proof still needs an anchor, and an anchor is \
         somebody's choice</strong> — each board below says whose.</p></div>\
         <p class=\"prose\">{door}</p>\
         <p class=\"prose\"><strong>These are finished results, not a live view.</strong> Each row \
         states when this board admitted it (unix seconds). Nothing here is a mirror of another \
         surface's screen.</p>\
         {sections}\
         <div class=\"receipt ok\"><span class=\"dot\"></span>\
         <span class=\"label\">re-checked here, not relayed</span>\
         <span class=\"detail\">a result arriving from another surface is admitted only if its \
         proof passes this server's own O(1) light client against this board's pinned anchor — \
         whose provenance is printed on each board above</span></div>\
         <p class=\"prose tag-muted\">Honest scope: the deployed STARK is <em>succinct</em>, not \
         <em>hiding</em>. &ldquo;The moves are never posted&rdquo; is a data-availability privacy \
         property (this board never sees them and nobody publishes them), not a cryptographic \
         claim about the transcript, and the proof inherits the deployed FRI/STARK floor.</p>\
         </main>",
        door = door,
        sections = sections,
    );
    document("Crowns · cross-surface proof board", "crown", &body)
}

// ═══════════════════════════════════════════════════════════════════════════════
// Small helpers.
// ═══════════════════════════════════════════════════════════════════════════════

/// Unix seconds now (`0` if the clock is before the epoch, which no deployment is).
fn now_secs() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

/// Lowercase hex of a byte slice.
fn hex_of(bytes: &[u8]) -> String {
    use std::fmt::Write as _;
    let mut out = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        let _ = write!(out, "{b:02x}");
    }
    out
}

/// Decode a 64-char hex string to 32 bytes (`None` on anything malformed).
fn decode_hex32(s: &str) -> Option<[u8; 32]> {
    let s = s.trim();
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for (i, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(s.get(2 * i..2 * i + 2)?, 16).ok()?;
    }
    Some(out)
}

/// Normalize a claimed origin to one of `KNOWN_ORIGINS` (else `other`). The field is written by
/// an authenticated sender and RENDERED, so it is constrained at the door rather than trusted to be
/// escaped correctly at every later use.
fn normalize_origin(claimed: &str) -> String {
    let c = claimed.trim().to_ascii_lowercase();
    if KNOWN_ORIGINS.contains(&c.as_str()) {
        c
    } else {
        "other".to_string()
    }
}

/// Clamp a free-form label to something a row can hold without becoming the row.
fn clamp_label(s: &str) -> String {
    let t = s.trim();
    t.chars().take(64).collect()
}

/// The first `n` CHARACTERS of a label — never the first `n` bytes. Every identity this board
/// currently holds is hex, but the field is written by another surface and rendered here, and a
/// byte slice through a multi-byte character panics the whole page.
fn short(s: &str, n: usize) -> String {
    s.chars().take(n).collect()
}

/// The ruleset as displayed — never a guess.
fn ruleset_or_unstated(ruleset: &str) -> String {
    if ruleset.trim().is_empty() {
        "unstated".to_string()
    } else {
        ruleset.trim().to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use webauth_core::link_registry::{InMemoryLinkStore, LinkRecord, LinkStore};

    /// The in-tree REAL whole-history proof + its anchor VK — the same fixture
    /// `discord-bot`'s crown tests and `dreggnet-game-board`'s fast board tests read. Folding an
    /// actual game match is minutes-to-hours, so the shared fixture is what makes the happy path
    /// here non-vacuous instead of a stub.
    fn real_proof() -> (Vec<u8>, [u8; 32]) {
        let dir =
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../ugc-dregg/tests/fixtures");
        let bytes = std::fs::read(dir.join("whole_history_proof.bin"))
            .expect("the in-tree real whole-history proof fixture");
        let anchor = std::fs::read_to_string(dir.join("whole_history_anchor.hex"))
            .expect("the fixture's anchor VK");
        let vk = decode_hex32(anchor.trim()).expect("the anchor is 32 hex bytes");
        (bytes, vk)
    }

    /// An honest row built from the real fixture, with the anchor read off the light client's own
    /// attestation of it — exactly what a sending surface's `persist_fold` writes at rank time.
    ///
    /// `None` when the shared fixture does not verify under HEAD. That is a real failure of the
    /// tree rather than of this module, and [`require_row`] turns it into a LOUD red with the
    /// re-bake command, so it is never a test that silently skips itself.
    fn fixture_row(origin: &str, player: &str) -> Option<StoredFold> {
        let (proof, vk) = real_proof();
        let attested = dregg_lightclient::verify_history_bytes(&proof, &RecursionVk(vk)).ok()?;
        Some(StoredFold {
            id: fold_id(origin, Game::Automatafl.slug(), player, &proof),
            game: Game::Automatafl.slug().to_string(),
            origin: origin.to_string(),
            player: player.to_string(),
            ruleset: "descent-2026-07-26".to_string(),
            turns: attested.num_turns,
            vk,
            genesis_root: attested.genesis_root.map(|f| f.0),
            win_root: attested.final_root.map(|f| f.0),
            proof,
            admitted_at: 1_700_000_000,
        })
    }

    fn require_row(origin: &str, player: &str) -> StoredFold {
        fixture_row(origin, player).unwrap_or_else(|| {
            let (proof, vk) = real_proof();
            let reason = dregg_lightclient::verify_history_bytes(&proof, &RecursionVk(vk))
                .err()
                .map(|e| format!("{e:?}"))
                .unwrap_or_else(|| "it verified on the retry".to_string());
            panic!(
                "the shared whole-history proof fixture does not verify under HEAD ({reason}), so \
                 the crown-ingest happy path cannot be driven. This is NOT a crown-ingest \
                 regression. Re-bake the fixture: `DREGG_ALLOW_UNAUDITED_PQ=1 cargo run --release \
                 -p dregg-lightclient --bin produce_history_envelope --features prover -- 3 7`, \
                 base64-decode `proof_bytes_b64` into \
                 ugc-dregg/tests/fixtures/whole_history_proof.bin and write `anchor_hex` (no \
                 trailing newline) to whole_history_anchor.hex."
            )
        })
    }

    /// A row with a real shape and a junk envelope — the forged submission.
    fn junk_row(origin: &str) -> StoredFold {
        let proof = vec![0xFFu8; 64];
        StoredFold {
            id: fold_id(origin, Game::Automatafl.slug(), &"dd".repeat(32), &proof),
            game: Game::Automatafl.slug().to_string(),
            origin: origin.to_string(),
            player: "dd".repeat(32),
            ruleset: String::new(),
            turns: 3,
            vk: [0x11; 32],
            genesis_root: [1, 2, 3, 4, 5, 6, 7, 8],
            win_root: [9, 10, 11, 12, 13, 14, 15, 16],
            proof,
            admitted_at: 1_700_000_001,
        }
    }

    /// ⚑ **THE WHOLE POINT: a result is VERIFIED here, not admitted on the sender's say-so.**
    ///
    /// A forged envelope carrying a perfectly well-formed row — right game, right shape, an anchor
    /// of its own choosing — is refused by the same O(1) tooth a live submission faces, nothing is
    /// ranked, nothing is persisted, and (critically) the refused row does NOT pin the board's
    /// trust anchor. A "trust the bot" endpoint would have ranked this.
    #[test]
    fn a_forged_fold_is_refused_and_pins_nothing() {
        let store = Arc::new(InMemoryCrownFoldStore::new());
        let state = CrownIngestState::with_store(store.clone());
        let err = state
            .admit_and_persist(&junk_row("discord"))
            .expect_err("a junk envelope must be REFUSED by the light client");
        assert!(
            err.contains("did NOT verify") || err.contains("REFUSED"),
            "the refusal must name the verification that failed, got: {err}"
        );
        assert!(
            state.snapshot().is_empty(),
            "a refused fold leaves no board open and no row behind"
        );
        assert!(
            store.list().expect("store reads").is_empty(),
            "nothing may be persisted for a fold the board refused"
        );
        assert!(
            !state
                .inner
                .lock()
                .expect("board")
                .anchors
                .contains_key(&Game::Automatafl),
            "⚑ a fold that cannot verify against its OWN claimed anchor must not PIN the board — \
             otherwise one hostile first row freezes the trust root and refuses every honest crown \
             behind it"
        );
    }

    /// The happy path, driven on the REAL fixture: an honest fold is admitted through
    /// `submit_bytes`, persisted, ranked, re-verified on the read, and stores no moves.
    #[test]
    fn an_honest_fold_is_admitted_ranked_and_reverifies_on_the_read() {
        let row = require_row("discord", &"cc".repeat(32));
        let store = Arc::new(InMemoryCrownFoldStore::new());
        let state = CrownIngestState::with_store(store.clone());
        let admitted = state
            .admit_and_persist(&row)
            .expect("the real fixture verifies against its own attested anchor");
        assert_eq!(admitted.turns, row.turns);
        assert_eq!(store.list().expect("store reads").len(), 1);

        let views = state.snapshot();
        let board = views
            .iter()
            .find(|v| v.game == Game::Automatafl)
            .expect("the automatafl board is open");
        assert!(
            board.stores_no_moves,
            "a proof-backed entry stores the envelope and the attested publics — never moves"
        );
        assert_eq!(board.rows.len(), 1);
        assert_eq!(
            board.rows[0].reverified_turns,
            Some(row.turns),
            "the board re-runs the O(1) light client on the READ, so the verdict shown is this \
             request's and not a stored flag"
        );
        assert_eq!(board.rows[0].origin, "discord");
        assert_eq!(board.rows[0].ruleset, "descent-2026-07-26");
    }

    /// A retried POST does not double-rank. The id is content-derived, so the second admission
    /// returns the first row instead of pushing a second entry for one human.
    #[test]
    fn a_retried_submission_is_idempotent() {
        let row = require_row("discord", &"cc".repeat(32));
        let state = CrownIngestState::new();
        let first = state.admit(&row).expect("the fixture verifies");
        let second = state.admit(&row).expect("a retry is admitted idempotently");
        assert_eq!(first.id, second.id);
        assert_eq!(
            state.snapshot()[0].rows.len(),
            1,
            "`rank_entry` pushes unconditionally, so without the id check a retry would put one \
             human on the board twice"
        );
    }

    /// ⚑ **THE ID NAMESPACE.** The same envelope arriving from two surfaces is two rows, never a
    /// silent overwrite of one by the other.
    #[test]
    fn a_discord_result_and_a_web_result_cannot_collide() {
        let proof = vec![7u8; 32];
        assert_ne!(
            fold_id("discord", "automatafl", "aa", &proof),
            fold_id("web", "automatafl", "aa", &proof),
        );
        assert_ne!(
            fold_id("discord", "automatafl", "aa", &proof),
            fold_id("discord", "multiway-tug", "aa", &proof),
        );
        assert_eq!(
            fold_id("discord", "automatafl", "aa", &proof),
            fold_id("discord", "automatafl", "aa", &proof),
            "the id is a pure function of the content, so a retry re-derives it"
        );
    }

    /// **ATTRIBUTION.** The rule this board files a cross-surface result under, driven on the
    /// registry that has to back it:
    ///
    /// * a Discord custodial key LINKED to a root resolves to that human's stable account id —
    ///   the same id the web key linked to the same root resolves to, so the two rank as one;
    /// * an UNLINKED key resolves to ITSELF, so it files honestly under the custodial key and is
    ///   never merged into anyone;
    /// * an AMBIGUOUS stored prefix resolves to nothing rather than merging two humans.
    ///
    /// Note what is NOT asserted: nothing here rewrites what the board ranked. The entry is still
    /// ranked under, and the proof still attributed to, the custodial key.
    #[test]
    fn attribution_follows_the_link_registry_and_never_invents_a_merge() {
        let root = "aa".repeat(32);
        let discord_key = "11".repeat(32);
        let web_key = "22".repeat(32);
        let unlinked = "33".repeat(32);
        let mut links = InMemoryLinkStore::default();
        links
            .record(&LinkRecord {
                root_pubkey_hex: root.clone(),
                platform: "discord".into(),
                platform_uid: "111".into(),
                custodial_pubkey_hex: discord_key.clone(),
                verified_at: 100,
            })
            .expect("records");
        links
            .record(&LinkRecord {
                root_pubkey_hex: root.clone(),
                platform: "web".into(),
                platform_uid: "K".into(),
                custodial_pubkey_hex: web_key.clone(),
                verified_at: 101,
            })
            .expect("records");
        let resolver = RootResolver::from_store(&links);

        assert_eq!(
            resolver.resolve(&discord_key),
            resolver.resolve(&web_key),
            "a Discord result and a web result from ONE proven human file under one human"
        );
        assert_eq!(
            resolver.resolve(&unlinked),
            unlinked,
            "an UNLINKED Discord result files under its own custodial key — the board never \
             guesses a human the link registry cannot back"
        );
        assert!(
            resolver.resolve_opt(&unlinked).is_none(),
            "and it is honestly reported as unresolved, not as a resolution to itself"
        );
    }

    /// The ruleset string survives the store round-trip and renders as `unstated` when absent —
    /// never as a guess about which rules a result was earned under.
    #[test]
    fn the_ruleset_string_round_trips_and_is_never_guessed() {
        let store = SqliteCrownFoldStore::open(":memory:").expect("an in-memory store opens");
        let mut row = junk_row("telegram");
        row.ruleset = "descent-cap-7".to_string();
        store.persist(&row).expect("persists");
        store.persist(&row).expect("idempotent by id");
        let back = store.list().expect("lists");
        assert_eq!(back.len(), 1, "persist is idempotent by id");
        assert_eq!(back[0], row, "every field round-trips byte-for-byte");
        assert_eq!(ruleset_or_unstated(""), "unstated");
        assert_eq!(ruleset_or_unstated("  x "), "x");
    }

    /// A tampered persisted row does not come back. **Both** teeth are driven, because they refuse
    /// different edits:
    ///
    /// * a DB edit that flips proof bytes but KEEPS the id is caught by the content-id check —
    ///   nothing can be renamed into an authentic row's identity;
    /// * a DB edit that flips proof bytes AND re-derives the id gets past that, and is then refused
    ///   by the light client itself. That is the one that matters: boot restore is a
    ///   re-VERIFICATION, not a restoration of trust.
    #[test]
    fn a_tampered_persisted_row_is_not_restored() {
        let honest = require_row("discord", &"cc".repeat(32));

        // (a) tampered envelope under the ORIGINAL id — the content-id check refuses it.
        let mut kept_id = honest.clone();
        let mid = kept_id.proof.len() / 2;
        kept_id.proof[mid] ^= 0xFF;
        let store_a = Arc::new(InMemoryCrownFoldStore::new());
        store_a.persist(&kept_id).expect("persists");
        let a = CrownIngestState::with_store(store_a);
        a.load_from_store();
        assert!(
            a.snapshot().is_empty(),
            "a row whose id is not its content id must not be restored"
        );

        // (b) tampered envelope with a HONESTLY re-derived id — only the light client can refuse
        // this one, and it must.
        let mut redone = kept_id.clone();
        redone.id = fold_id(&redone.origin, &redone.game, &redone.player, &redone.proof);
        let store_b = Arc::new(InMemoryCrownFoldStore::new());
        store_b.persist(&redone).expect("persists");
        let b = CrownIngestState::with_store(store_b);
        b.load_from_store();
        assert!(
            b.snapshot().is_empty(),
            "⚑ a row whose envelope no longer verifies must not be restored on the strength of \
             having been stored — the restore path is the SAME O(1) accept path a live submission \
             faces"
        );

        // (c) the untampered row restores — so (a) and (b) are refusals, not a broken restore.
        let store_c = Arc::new(InMemoryCrownFoldStore::new());
        store_c.persist(&honest).expect("persists");
        let c = CrownIngestState::with_store(store_c);
        c.load_from_store();
        assert_eq!(c.snapshot()[0].rows.len(), 1);
    }

    /// The ingest door is FAIL-CLOSED with no operator token, and rejects a wrong bearer.
    #[test]
    fn the_ingest_door_is_fail_closed_without_a_token() {
        let closed = CrownIngestState::new();
        assert!(!closed.ingest_armed());
        assert!(
            closed.authorize(&HeaderMap::new()).is_err(),
            "no token configured ⇒ every POST is refused"
        );

        let armed = CrownIngestState::new().with_ingest_token(Some("s3cret".to_string()));
        assert!(armed.ingest_armed());
        assert!(armed.authorize(&HeaderMap::new()).is_err(), "no bearer");
        let mut wrong = HeaderMap::new();
        wrong.insert(
            axum::http::header::AUTHORIZATION,
            "Bearer nope".parse().expect("a header value"),
        );
        assert!(armed.authorize(&wrong).is_err(), "wrong bearer");
        let mut right = HeaderMap::new();
        right.insert(
            axum::http::header::AUTHORIZATION,
            "Bearer s3cret".parse().expect("a header value"),
        );
        assert!(armed.authorize(&right).is_ok());

        // An empty / whitespace token is NOT a token — it leaves the door closed rather than
        // arming it on a value an unset env var would produce.
        assert!(
            !CrownIngestState::new()
                .with_ingest_token(Some("   ".to_string()))
                .ingest_armed()
        );
    }

    /// An origin the board does not know is stored as `other` rather than reflected into the page,
    /// and a label cannot become the row.
    #[test]
    fn a_claimed_origin_is_normalized_at_the_door() {
        assert_eq!(normalize_origin("Discord"), "discord");
        assert_eq!(normalize_origin("<script>"), "other");
        assert_eq!(normalize_origin(""), "other");
        assert_eq!(clamp_label(&"x".repeat(500)).len(), 64);
        // ⚑ CHAR-wise, not byte-wise. A byte slice through a multi-byte character panics, and this
        // label is written by another surface and rendered on a public page.
        assert_eq!(short("ábcdef", 3), "ábc");
        assert_eq!(short("ab", 9), "ab");
    }

    // ═══════════════════════════════════════════════════════════════════════════
    // ⚑ THE PERMANENT CONTROLS for "the board ranks against an anchor a submitter
    // minted, and calls it verified".
    //
    // These are CONTROLS, not injections: they are evaluated on every green pass, and
    // they go red the moment the property they guard stops holding. They need NO env
    // var and NO fixture proof — the shapes they check are pure functions of an
    // `Admitted` / a `BoardView`, which is exactly why `ingest_ok_body` was split out
    // of the handler.
    // ═══════════════════════════════════════════════════════════════════════════

    fn admitted_with(provenance: AnchorProvenance) -> Admitted {
        Admitted {
            id: "row".to_string(),
            game: Game::Automatafl,
            origin: "discord".to_string(),
            player: "aa".repeat(32),
            ruleset: String::new(),
            turns: 7,
            universe: UniverseId::from_bytes([0u8; 32]),
            completion_id: [0u8; 32],
            proof_len: 1234,
            vk8: "deadbeef".to_string(),
            anchor_provenance: provenance,
            admitted_at: 1_700_000_000,
        }
    }

    /// **THE SUCCESS WORD IS WRITTEN IN EXACTLY ONE PLACE, AND ONLY WHEN IT IS EARNED.**
    ///
    /// Measured 2026-07-30: this handler answered `"verified": true` unconditionally, with
    /// the detail string *"nothing was taken on the sender's word"*, while the board's
    /// anchor had been taken from the first sender's wire and frozen. A caller could not
    /// tell the two cases apart at all.
    ///
    /// The shape asserted here is the sibling light-client repair's: the key is ABSENT on
    /// the weaker arm, so `body.verified === true` is `undefined` rather than a softer
    /// string a reader skims past. Re-add an unconditional `verified` and this goes red.
    #[test]
    fn the_success_word_is_written_only_for_an_operator_pinned_anchor() {
        let boot = ingest_ok_body(&admitted_with(AnchorProvenance::BootstrappedFromSubmission));
        assert!(
            boot.get("verified").is_none(),
            "a board pinned to a SUBMITTER's anchor must not report `verified` at all — the \
             key must be ABSENT, not `false` and not a softer string, so a consumer testing \
             `verified === true` gets `undefined`. Got: {boot}"
        );
        assert_eq!(
            boot["accepted"], true,
            "what DID happen must still be reported: the light client ran here and admitted it"
        );
        assert_eq!(
            boot["anchor_provenance"],
            "bootstrapped-from-first-submission"
        );
        let detail = boot["detail"].as_str().unwrap_or_default();
        assert!(
            detail.contains("SELF-REPORTED") && detail.contains("CROWN_ANCHOR_AUTOMATAFL"),
            "the response's own detail must say what the board is doing and how to stop it, \
             not leave it to a page a caller never renders. Got: {detail}"
        );
        assert!(
            !detail.contains("nothing was taken on the sender's word"),
            "the retired claim must stay retired — the sender's word WAS the anchor"
        );

        let pinned = ingest_ok_body(&admitted_with(AnchorProvenance::OperatorConfigured));
        assert_eq!(
            pinned["verified"], true,
            "an operator-pinned board IS a trust decision and must reach the word — a gate \
             that cannot go green is not a gate either"
        );
        assert_eq!(pinned["anchor_provenance"], "operator-configured");
    }

    /// **THE BOARD A STRANGER READS SAYS WHAT IT IS RANKING.**
    ///
    /// The rank column is meaningless without the anchor's provenance, and a reader must not
    /// have to infer it from a footnote. Delete the amber receipt, or paint the bootstrap
    /// arm with `receipt ok`, and this goes red.
    #[test]
    fn the_board_page_says_when_it_is_ranking_self_reported_claims() {
        let view = |p: AnchorProvenance| BoardView {
            game: Game::Automatafl,
            universe: None,
            stores_no_moves: true,
            anchor_provenance: Some(p),
            rows: Vec::new(),
        };

        let boot = board_page(&[view(AnchorProvenance::BootstrappedFromSubmission)], false);
        assert!(
            boot.contains("RANKING SELF-REPORTED CLAIMS"),
            "a board whose trust root came from a submission must SAY SO, in its own chrome, \
             above the rows"
        );
        assert!(
            boot.contains("receipt warn") && !boot.contains("operator-pinned anchor"),
            "the bootstrap arm must be the third state — not the green `receipt ok` a reader \
             reads as a pass"
        );
        assert!(
            boot.contains("frozen") || boot.contains("froze"),
            "the FREEZE is the part that makes this more than a per-submission caveat: the \
             first fold defines the board forever"
        );

        let pinned = board_page(&[view(AnchorProvenance::OperatorConfigured)], false);
        assert!(
            pinned.contains("operator-pinned anchor") && !pinned.contains("SELF-REPORTED"),
            "an operator-pinned board must render the honest strong state"
        );
    }

    /// **A MALFORMED OPERATOR ANCHOR REFUSES THE ADMISSION; IT NEVER DOWNGRADES.**
    ///
    /// The failure this forbids: an operator sets `CROWN_ANCHOR_AUTOMATAFL`, fat-fingers the
    /// spec, and the board silently hands its trust root to the next submitter — the exact
    /// state they were configuring their way out of, now with a config file that says
    /// otherwise. `operator_anchor` returns `Result<Option<_>>` for this reason alone.
    ///
    /// Env vars are process-global, so this test drives the parser directly rather than
    /// racing every other test in this binary for `set_var`. What it pins is the contract
    /// `admit` depends on: malformed ⇒ `Err`, and `Err` propagates (the `?` in `admit`).
    #[test]
    fn a_malformed_operator_anchor_spec_is_an_error_not_a_fallback() {
        let err = dreggnet_game_board::parse_anchor_spec("not-an-anchor")
            .expect_err("a malformed spec must be an Err");
        assert!(
            err.contains("three colon-separated") || err.contains("64 hex"),
            "the refusal must say what the spec should look like, got: {err}"
        );
        // And the arm `admit` takes on that Err is a REFUSAL, because it is `operator_anchor(game)?`
        // — a `.unwrap_or(None)` there would silently reinstate the bootstrap. This asserts the
        // signature that makes the mistake impossible to write by accident.
        fn _assert_result_shape(f: fn(Game) -> Result<Option<ProofAnchor>, String>) -> bool {
            f as usize != 0
        }
        assert!(_assert_result_shape(operator_anchor));
    }
}
