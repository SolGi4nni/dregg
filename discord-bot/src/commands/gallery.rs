//! `/gallery` — the **universe gallery**, wired to the REAL [`ugc_dregg`] registry.
//!
//! This command used to browse "devnet artworks" through four `DevnetClient` calls that
//! every one of them returned [`DevnetError::Unsupported`](crate::devnet::DevnetError)
//! ("not exposed by the current public node API") — a complete UI over four dead stubs,
//! which rendered as "Gallery Unavailable" every single time. The gallery is now the
//! thing dregg actually has: a gallery of **authored universes** on `ugc-dregg`'s real
//! registry + its **no-cheat verifiable leaderboard**.
//!
//! ## The four verbs
//!
//! | subcommand | what it really does |
//! |------------|---------------------|
//! | `list`     | every published [`Universe`] in the registry (name / author / content address) |
//! | `show`     | one universe + its **leaderboard**: verified completions, ranked by turns-to-win |
//! | `publish`  | mints a REAL procgen universe from a committed seed ([`Universe::daily`]) and publishes it — content-addressed, winnable, re-generable byte-for-byte from its seed |
//! | `play`     | submits a run: the moves are re-executed against a FRESH identically-seeded world; only a completion that **provably reaches the win** is accepted + ranked |
//!
//! ## The no-cheat tooth reaches Discord
//!
//! `play` does not trust the player. [`Registry::submit`] re-drives the submitted moves
//! through the real executor on a fresh world and requires the recorded receipt chain
//! re-verifies to the universe's declared WIN state, with a truthful turn count. A forged
//! or incomplete run is REJECTED — and the embed says *why* ([`RejectReason`] is surfaced
//! verbatim, not swallowed). The old `/gallery bid` signing path is repurposed: the
//! player's cipherclerk now signs their submitted run, binding the completion to their
//! custodial identity (see [`sign_run`]).
//!
//! ## Verified author identity + remix lineage (the creator-economy foundation)
//!
//! `publish` no longer stamps a bare author *name*. It **signs the universe with the
//! publisher's cipherclerk** — a real ed25519 attestation over the world's content
//! commitment (mirroring how a `play` run is signed). ugc-dregg binds that verified
//! author key into the content address ([`UniversePlan::attest`]), so authorship is
//! attributable + unforgeable: nobody can publish under another author's key. `publish`
//! also accepts an optional `parent` — a REMIX/fork of an already-published universe,
//! recorded as a content-addressed derivation edge and admitted only if the parent really
//! exists ([`Registry::publish_derived`]). Both survive a restart: the author key +
//! attestation signature + parent link are persisted, and the attestation is re-verified
//! (and the lineage re-checked) on boot.
//!
//! ## Persistence — DURABLE, with boot-time re-verification
//!
//! The live [`Registry`] is still the process-wide `OnceLock<Mutex<Registry>>` cache, but
//! it is now **backed by a durable [`GalleryStore`]**. A published universe's *public
//! source* (name / author / seed-epoch / win) and a submitted completion's *moves +
//! player + claimed turns* are written to the store; on boot [`load_registry`] reads them
//! back and **replays each one through [`Registry::publish`] / [`Registry::submit`]** —
//! which RE-VERIFIES every completion by replay against a fresh, identically-seeded world.
//!
//! Only the minimal, reproducible input is stored — a universe's seed-epoch (not a cached
//! world), a completion's *move sequence* (not a trusted receipt blob). The receipt chain
//! is deterministically re-recorded and re-checked at load, so **a tampered DB row cannot
//! resurrect a cheat**: edit the moves to a non-winning line and the no-cheat gate rejects
//! it (`DidNotWin` / a refused move); edit `claimed_turns` and it rejects (`ResultMismatch`);
//! edit a universe's source/author/epoch and its recomputed content address no longer
//! matches its stored id, so the row is dropped. None of these land on the board.
//!
//! The main loop wires a sqlite [`GalleryStore`] to the bot `Database` (see the wiring note
//! below); tests here drive the whole persist → reload → re-verify cycle against the
//! [`InMemoryGalleryStore`], including the tampered-row rejections.
//!
//! ## Honest scope
//!
//! * **Auctions are gone, not stubbed.** `ugc-dregg` has no auction/bid concept, so
//!   `auctions`/`mybids` are NOT carried forward as dead UI. The bidding *machinery*
//!   (cclerk signing) is repurposed onto `play`, which is a real submission.
//! * **Author identity** is now a *verified* ed25519 key (the publisher's cclerk),
//!   attested over the universe content and bound into its content address — not a
//!   trusted string. What a fuller creator economy still needs (named, not built): **paid
//!   / premium universes + a remix-royalty split** over the `$DREGG` rails, and
//!   **anti-sybil** (staking / rate-limiting a publish). See ugc-dregg's crate docs.
//
// ─── MAIN-LOOP WIRING (what closes the loop; NOT owned by this file) ─────────────
// This module OWNS the `GalleryStore` trait, its `InMemoryGalleryStore` (tests), and the
// boot-replay-reverify (`load_registry`). The main loop wires the persistent backing:
//
//   1. `migrations/005_ugc_gallery.sql` — the two tables (`ugc_universes`,
//      `ugc_completions`). Add the matching inline `CREATE TABLE IF NOT EXISTS` to
//      `Database::connect` (the bot's schema-in-code pattern), and four `Database`
//      methods: `persist_ugc_universe(..)`, `persist_ugc_completion(..)` (both
//      `INSERT OR IGNORE` on the PK), `list_ugc_universes()`, `list_ugc_completions()`.
//   2. A bot-owned `SqliteGalleryStore` implementing `gallery::GalleryStore` over the
//      async `Database` — exactly like `pay::SqliteCreditStore` (sync trait, drives each
//      async query with `tokio::task::block_in_place`). Its four methods map to the four
//      `Database` methods above and translate rows to/from `StoredUniverse` /
//      `StoredCompletion`.
//   3. At boot, ONE call: `gallery::install_store(Box::new(SqliteGalleryStore::new(db, handle)))`.
//      `install_store` records the store AND loads+re-verifies the live registry from it.
//      No `BotState` field is needed — the store is held in this module's `OnceLock`, and
//      the handlers persist through it after each successful publish / play.

use std::sync::{Mutex, OnceLock};

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use ed25519_dalek::{Signer, SigningKey};

use dungeon_on_dregg::DUNGEON;
use ugc_dregg::{
    Accepted, AuthorSignature, Completion, LineageError, Provenance, PublishError, Registry,
    RejectReason, Universe, UniverseId, UniversePlan, WinCondition, record_playthrough,
};

use crate::BotState;
use crate::cipherclerk::{UserCipherclerk, sign_legacy};
use crate::embeds;

// ═══════════════════════════════════════════════════════════════════════════════
// The registry — the real `ugc-dregg` one, in-memory (see the persistence gap above).
// ═══════════════════════════════════════════════════════════════════════════════

/// The live process-wide UGC registry cache.
static REGISTRY: OnceLock<Mutex<Registry>> = OnceLock::new();
/// The durable backing store, installed once by the main loop at boot
/// ([`install_store`]). When present, the live registry is loaded + re-verified from it.
static GALLERY_STORE: OnceLock<Box<dyn GalleryStore + Send + Sync>> = OnceLock::new();

/// The process-wide UGC registry — the live cache. On first touch it is built from the
/// durable [`GalleryStore`] if one is installed (every stored completion re-verified by
/// replay), otherwise from [`seed_registry`]'s built-in dungeon so the gallery is never
/// empty on a cold boot.
fn registry() -> &'static Mutex<Registry> {
    REGISTRY.get_or_init(|| {
        let reg = match GALLERY_STORE.get() {
            Some(store) => load_registry(store.as_ref()),
            None => seed_registry(),
        };
        Mutex::new(reg)
    })
}

/// **Main-loop entry point.** Install the durable store and load the live registry from
/// it (re-verifying every persisted completion by replay). First install wins; call once
/// at boot BEFORE any `/gallery` command is served.
pub fn install_store(store: Box<dyn GalleryStore + Send + Sync>) {
    let _ = GALLERY_STORE.set(store);
    // Force the live registry to initialize from the freshly-installed store now, so the
    // cache already reflects the persisted (and re-verified) state before serving.
    let _ = registry();
}

/// Persist a published universe to the durable store, if one is installed. Called after a
/// successful in-memory publish (never while holding the registry lock).
fn store_universe(u: &StoredUniverse) {
    if let Some(store) = GALLERY_STORE.get() {
        let _ = store.persist_universe(u);
    }
}

/// Persist an accepted completion to the durable store, if one is installed. Called after
/// a successful in-memory play (never while holding the registry lock).
fn store_completion(c: &StoredCompletion) {
    if let Some(store) = GALLERY_STORE.get() {
        let _ = store.persist_completion(c);
    }
}

/// The built-in universe: `dungeon-on-dregg`'s real, winnable salt-shore dungeon
/// (the win = the hoard seized, `gold == 500`, and the scene ENDED), plus one honest
/// par completion so a fresh gallery already shows a *verified* board.
///
/// The par run is recorded through the real executor and submitted through the real
/// no-cheat gate — if it did not genuinely win, it simply would not be on the board.
fn seed_registry() -> Registry {
    let mut reg = Registry::new();

    let Ok(dungeon) = Universe::authored(
        "The Salt Shore Descent",
        "dregg (built-in)",
        DUNGEON,
        WinCondition::ended_with(&[("gold", 500)]),
    ) else {
        return reg;
    };

    let id = reg.publish(dungeon.clone());

    // The minimal winning line: take the lantern, descend the gated stair, claim the
    // hoard. Recorded on a real world-cell; accepted only because it really wins.
    if let Ok(play) = record_playthrough(&dungeon, &[0, 0, 0]) {
        let claimed_turns = play.steps.len();
        let _ = reg.submit(Completion {
            universe: id,
            player: "the-house (par)".to_string(),
            play,
            claimed_turns,
        });
    }

    reg
}

// ═══════════════════════════════════════════════════════════════════════════════
// The durable store — persists the PUBLIC, REPRODUCIBLE input of a universe / completion,
// and replays it through the real no-cheat gate on boot. A tampered row cannot survive.
// ═══════════════════════════════════════════════════════════════════════════════

/// A published universe's **public source** as persisted — everything needed to
/// reconstruct it through a PUBLIC `ugc-dregg` constructor (so reconstruction re-runs the
/// same publish path, not a cached shape). Content-addressed: `id_hex` is the address the
/// world hashed to at publish time, and reconstruction recomputes it — a mismatch means
/// the row was tampered and is dropped.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StoredUniverse {
    /// The universe content address (hex) at publish time — the row PK + tamper check.
    pub id_hex: String,
    /// `"daily"` (procgen from a committed seed-epoch) or `"authored"` (direct spween source).
    pub kind: String,
    /// Display name (derived for `daily`; authoritative for `authored`).
    pub name: String,
    /// The author label.
    pub author: String,
    /// The spween source — the authoritative bytes for `authored`; empty for `daily`
    /// (regenerated byte-for-byte from the seed-epoch).
    pub source: String,
    /// `daily` only: hex of the 32-byte epoch commitment (`blake3(seed_text)`) that
    /// `Universe::daily` regenerates the whole world from.
    pub epoch_hex: Option<String>,
    /// The declared win condition's `(var, value)` vars, as JSON.
    pub win_json: String,
    /// The **parent** content address (hex) this universe remixes/forks, or `None` for a
    /// root. Re-verified on boot: the parent must be a published universe, and it is bound
    /// into this universe's own content address (so a tampered link recomputes a
    /// different `id_hex` and the row is dropped).
    pub parent_id_hex: Option<String>,
    /// The **verified author** ed25519 public key (hex), or `None` for an anonymous
    /// (legacy) universe. Re-verified on boot against `author_sig_hex`.
    pub author_key_hex: Option<String>,
    /// The author's **attestation signature** (hex) over the universe content commitment.
    /// `Some` exactly when `author_key_hex` is; on boot ugc-dregg re-checks it and drops a
    /// forged/tampered attestation.
    pub author_sig_hex: Option<String>,
}

impl StoredUniverse {
    /// The verified-identity + lineage fields as persisted (parent link, author key,
    /// attestation signature) — read straight off a published [`Universe`].
    fn identity_fields(u: &Universe) -> (Option<String>, Option<String>, Option<String>) {
        (
            u.parent().map(|p| hex32(p.as_bytes())),
            u.author_id().map(|a| hex32(a.as_bytes())),
            u.attestation().map(|s| hex64(s.as_bytes())),
        )
    }

    /// The persistable descriptor for a `daily` (procgen) universe. `epoch` is
    /// `blake3(seed_text)` — the commitment `Universe::daily` regenerates from. The
    /// verified author key + attestation + parent link are read off `u`.
    fn daily_desc(id: UniverseId, author: &str, epoch: &[u8; 32], u: &Universe) -> StoredUniverse {
        let (parent_id_hex, author_key_hex, author_sig_hex) = Self::identity_fields(u);
        StoredUniverse {
            id_hex: id_hex(&id),
            kind: "daily".to_string(),
            name: u.name().to_string(),
            author: author.to_string(),
            source: String::new(),
            epoch_hex: Some(hex32(epoch)),
            win_json: serde_json::to_string(&u.win().vars).unwrap_or_else(|_| "[]".to_string()),
            parent_id_hex,
            author_key_hex,
            author_sig_hex,
        }
    }

    /// The persistable descriptor for an `authored` universe (the built-in dungeon, or a
    /// future authored publish). The main loop can call this to persist an authored world;
    /// the current `/gallery publish` only mints `daily` universes.
    #[allow(dead_code)]
    fn authored_desc(u: &Universe) -> StoredUniverse {
        let (parent_id_hex, author_key_hex, author_sig_hex) = Self::identity_fields(u);
        StoredUniverse {
            id_hex: id_hex(&u.id()),
            kind: "authored".to_string(),
            name: u.name().to_string(),
            author: u.author().to_string(),
            source: u.source().to_string(),
            epoch_hex: None,
            win_json: serde_json::to_string(&u.win().vars).unwrap_or_else(|_| "[]".to_string()),
            parent_id_hex,
            author_key_hex,
            author_sig_hex,
        }
    }
}

/// A submitted completion as persisted — the **player + the move sequence** (choice
/// indices) + the claimed turns. The receipt chain is deliberately NOT stored: it is
/// deterministically re-recorded from the moves on a fresh identically-seeded world and
/// re-verified at load. Storing the minimal input (moves, not a trusted blob) means a
/// tampered row is only ever a different move sequence or a lied result — both of which
/// the no-cheat gate re-checks by replay.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StoredCompletion {
    /// Idempotency PK — `blake3(universe_id_hex ‖ player ‖ moves_json)`. A re-submit of the
    /// same run is a no-op; a different run is a different key.
    pub key_hex: String,
    /// The full universe content address (hex) this completion is for.
    pub universe_id_hex: String,
    /// The player's name.
    pub player: String,
    /// The move sequence (choice indices), as a JSON array.
    pub moves_json: String,
    /// The claimed turns-to-win. Stored INDEPENDENTLY of the moves, so a tampered value
    /// (≠ the verified move count) is rejected as `ResultMismatch` on reload.
    pub claimed_turns: i64,
}

impl StoredCompletion {
    /// Build a persistable completion from a resolved (full-hex) universe id, the player,
    /// the moves, and the verified turn count.
    fn new(
        universe_id_hex: &str,
        player: &str,
        moves: &[usize],
        claimed_turns: usize,
    ) -> StoredCompletion {
        let moves_json = serde_json::to_string(moves).unwrap_or_else(|_| "[]".to_string());
        let mut h = blake3::Hasher::new();
        h.update(universe_id_hex.as_bytes());
        h.update(&[0]);
        h.update(player.as_bytes());
        h.update(&[0]);
        h.update(moves_json.as_bytes());
        StoredCompletion {
            key_hex: hex32(h.finalize().as_bytes()),
            universe_id_hex: universe_id_hex.to_string(),
            player: player.to_string(),
            moves_json,
            claimed_turns: claimed_turns as i64,
        }
    }
}

/// The durable gallery store. Sync (interior mutability, `&self`) so the live cache can be
/// backed by it without an async boundary — exactly the shape of `dregg-pay`'s
/// `CreditStore`. The main loop supplies a sqlite impl; tests use [`InMemoryGalleryStore`].
/// Persist methods MUST be idempotent by PK (`INSERT OR IGNORE`), so a double write / a
/// double load never duplicates a universe or a board entry.
pub trait GalleryStore {
    /// Persist a published universe (idempotent by `id_hex`).
    fn persist_universe(&self, u: &StoredUniverse) -> Result<(), String>;
    /// Persist an accepted completion (idempotent by `key_hex`).
    fn persist_completion(&self, c: &StoredCompletion) -> Result<(), String>;
    /// Every persisted universe.
    fn list_universes(&self) -> Result<Vec<StoredUniverse>, String>;
    /// Every persisted completion.
    fn list_completions(&self) -> Result<Vec<StoredCompletion>, String>;
}

/// A thread-safe in-memory [`GalleryStore`] for tests and single-process runs. Idempotent
/// by PK, matching the sqlite impl's `INSERT OR IGNORE`.
#[derive(Default)]
pub struct InMemoryGalleryStore {
    inner: Mutex<InMemGallery>,
}

#[derive(Default)]
struct InMemGallery {
    universes: Vec<StoredUniverse>,
    completions: Vec<StoredCompletion>,
}

impl InMemoryGalleryStore {
    /// A fresh empty store.
    pub fn new() -> InMemoryGalleryStore {
        InMemoryGalleryStore::default()
    }

    /// TEST HOOK: mutate the raw persisted rows, to simulate a **tampered database** (an
    /// operator or attacker editing a row on disk). The reload path must reject whatever
    /// this produces if it no longer re-verifies.
    #[cfg(test)]
    fn tamper(&self, f: impl FnOnce(&mut Vec<StoredUniverse>, &mut Vec<StoredCompletion>)) {
        let mut g = self.inner.lock().expect("gallery store lock");
        let InMemGallery {
            universes,
            completions,
        } = &mut *g;
        f(universes, completions);
    }
}

impl GalleryStore for InMemoryGalleryStore {
    fn persist_universe(&self, u: &StoredUniverse) -> Result<(), String> {
        let mut g = self.inner.lock().expect("gallery store lock");
        if !g.universes.iter().any(|x| x.id_hex == u.id_hex) {
            g.universes.push(u.clone());
        }
        Ok(())
    }
    fn persist_completion(&self, c: &StoredCompletion) -> Result<(), String> {
        let mut g = self.inner.lock().expect("gallery store lock");
        if !g.completions.iter().any(|x| x.key_hex == c.key_hex) {
            g.completions.push(c.clone());
        }
        Ok(())
    }
    fn list_universes(&self) -> Result<Vec<StoredUniverse>, String> {
        Ok(self
            .inner
            .lock()
            .expect("gallery store lock")
            .universes
            .clone())
    }
    fn list_completions(&self) -> Result<Vec<StoredCompletion>, String> {
        Ok(self
            .inner
            .lock()
            .expect("gallery store lock")
            .completions
            .clone())
    }
}

/// **BOOT REPLAY + RE-VERIFY.** Build a live [`Registry`] from the durable store: start
/// from the built-in seed, reconstruct every persisted universe through a real `ugc-dregg`
/// constructor, then replay every persisted completion through [`Registry::submit`] — the
/// no-cheat gate, which re-executes the moves on a fresh identically-seeded world and only
/// ranks a completion that provably reaches the win with a truthful turn count.
///
/// Every rejection here is silent-and-correct: a tampered universe row whose recomputed
/// content address no longer matches its stored id is dropped; a tampered completion
/// (non-winning moves, a refused move, or a lied `claimed_turns`) never lands on the board.
pub fn load_registry(store: &dyn GalleryStore) -> Registry {
    let mut reg = seed_registry();

    // Reconstruct every stored universe (re-verifying its author attestation) and keep
    // only those whose recomputed content address matches the stored id (the tamper
    // check — which also catches a tampered parent link, since the parent is bound in).
    let mut pending: Vec<Universe> = store
        .list_universes()
        .unwrap_or_default()
        .iter()
        .filter_map(|su| {
            let u = reconstruct_universe(su)?;
            (id_hex(&u.id()) == su.id_hex).then_some(u)
        })
        .collect();

    // Publish honoring LINEAGE: a remix is admitted only once its parent is present, so we
    // iterate to a fixpoint (store order is irrelevant). A universe whose parent never
    // appears — dropped as tampered, or a dangling/absent parent — is itself dropped.
    loop {
        let before = pending.len();
        // Keep the ones that could NOT publish yet (parent still absent); retry next pass.
        pending.retain(|u| reg.publish_derived(u.clone()).is_err());
        if pending.len() == before {
            break;
        }
    }

    for sc in store.list_completions().unwrap_or_default() {
        replay_completion(&mut reg, &sc);
    }

    reg
}

/// Reconstruct a universe from its persisted public source, through a PUBLIC constructor.
/// Returns `None` if the row does not reconstruct (a bad kind, a corrupt seed-epoch, a
/// source that no longer parses/compiles, a malformed parent link, or — the tooth — an
/// author attestation that no longer verifies). Such a row is simply dropped.
///
/// The verified author identity + lineage roundtrip here: a signed row is rebuilt through
/// [`UniversePlan::attest`], which RE-CHECKS the ed25519 signature over the content
/// commitment (a forged/tampered `author_sig_hex` fails → dropped); the parent link is
/// bound into the content address, so a tampered `parent_id_hex` recomputes a different
/// id (the caller's `id_hex` tamper check then drops it).
fn reconstruct_universe(su: &StoredUniverse) -> Option<Universe> {
    let parent = match &su.parent_id_hex {
        None => None,
        Some(h) => Some(UniverseId::from_bytes(decode_hex32(h)?)),
    };
    let plan = match su.kind.as_str() {
        "daily" => {
            let epoch = decode_hex32(su.epoch_hex.as_deref()?)?;
            UniversePlan::daily(&su.author, &epoch, parent).ok()?
        }
        "authored" => {
            let vars: Vec<(String, u64)> = serde_json::from_str(&su.win_json).ok()?;
            UniversePlan::authored(
                &su.name,
                &su.author,
                &su.source,
                WinCondition { vars },
                parent,
            )
            .ok()?
        }
        _ => return None,
    };
    match (&su.author_key_hex, &su.author_sig_hex) {
        (Some(k), Some(s)) => {
            let key = decode_hex32(k)?;
            let sig = AuthorSignature::from_bytes(decode_hex64(s)?);
            // A forged/tampered attestation is refused here — the row drops out.
            plan.attest(key, sig).ok()
        }
        // Legacy / anonymous universe: no verified key.
        _ => Some(plan.anonymous()),
    }
}

/// Replay one persisted completion through the no-cheat gate. Re-records the moves on a
/// fresh world and submits with the STORED `claimed_turns`; any rejection (unknown/tampered
/// universe, a refused move, `DidNotWin`, `ResultMismatch`, `FailedVerification`) is dropped
/// — it does not land on the board.
fn replay_completion(reg: &mut Registry, sc: &StoredCompletion) {
    let Some(id) = find_universe(reg, &sc.universe_id_hex) else {
        return;
    };
    let Some(universe) = reg.universe(id).cloned() else {
        return;
    };
    let Ok(moves) = serde_json::from_str::<Vec<usize>>(&sc.moves_json) else {
        return;
    };
    // A tampered (illegal) move sequence is refused by the real executor here.
    let Ok(play) = record_playthrough(&universe, &moves) else {
        return;
    };
    // Submit with the STORED claimed_turns — a tampered value trips ResultMismatch.
    let _ = reg.submit(Completion {
        universe: id,
        player: sc.player.clone(),
        play,
        claimed_turns: sc.claimed_turns as usize,
    });
}

/// Decode a 64-char hex string to 32 bytes (`None` on any malformed input).
fn decode_hex32(s: &str) -> Option<[u8; 32]> {
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for (i, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(s.get(2 * i..2 * i + 2)?, 16).ok()?;
    }
    Some(out)
}

/// Decode a 128-char hex string to 64 bytes — an author attestation signature (`None` on
/// any malformed input).
fn decode_hex64(s: &str) -> Option<[u8; 64]> {
    if s.len() != 128 {
        return None;
    }
    let mut out = [0u8; 64];
    for (i, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(s.get(2 * i..2 * i + 2)?, 16).ok()?;
    }
    Some(out)
}

// ═══════════════════════════════════════════════════════════════════════════════
// The command logic — pure over a `Registry`, so it is DRIVEN by tests without Discord.
// ═══════════════════════════════════════════════════════════════════════════════

/// A universe as the gallery lists it.
#[derive(Clone, Debug)]
struct UniverseSummary {
    id_hex: String,
    name: String,
    author: String,
    provenance: &'static str,
    /// How many verified completions are on its board.
    entries: usize,
}

/// One verified completion on a leaderboard.
#[derive(Clone, Debug)]
struct BoardEntry {
    rank: usize,
    player: String,
    turns: usize,
    completion_hex: String,
}

/// A universe + its no-cheat leaderboard.
#[derive(Clone, Debug)]
struct UniverseView {
    id_hex: String,
    name: String,
    author: String,
    provenance: &'static str,
    /// Whether a procgen universe still regenerates byte-for-byte from its committed
    /// seed (`None` for an authored universe, where there is no seed to check).
    regenerates: Option<bool>,
    /// The declared win condition, rendered.
    win: String,
    /// How many rooms/passages the world has (a cheap "size" the gallery can show).
    passages: usize,
    /// The **verified author** ed25519 public key (hex), or `None` if the universe is
    /// anonymous/legacy. When present, authorship is attributable + unforgeable.
    author_key_hex: Option<String>,
    /// The **parent** content address (hex) this universe remixes, or `None` for a root.
    parent_id_hex: Option<String>,
    board: Vec<BoardEntry>,
}

/// Why a `/gallery play` submission did not land. Every arm is a REAL refusal.
#[derive(Debug)]
enum PlayError {
    /// No universe in the registry matches the given id (or prefix).
    UnknownUniverse,
    /// The `moves` argument did not parse into a move sequence.
    BadMoves(String),
    /// The **real executor refused a move while recording** — e.g. the gated descent
    /// without the lantern. The cheat never even becomes a playthrough.
    RecordRefused(String),
    /// The playthrough recorded, but the registry's no-cheat gate REJECTED it (it did
    /// not re-verify, did not reach the win, or lied about its result).
    Rejected(RejectReason),
}

impl std::fmt::Display for PlayError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PlayError::UnknownUniverse => {
                write!(
                    f,
                    "no published universe matches that id — try `/gallery list`"
                )
            }
            PlayError::BadMoves(e) => write!(f, "could not read your moves: {e}"),
            PlayError::RecordRefused(e) => write!(
                f,
                "the executor REFUSED one of your moves while replaying it: {e}\n\n\
                 That is the gate doing its job — an illegal move is not a move."
            ),
            PlayError::Rejected(r) => write!(
                f,
                "the leaderboard re-verified your run and rejected it: {r}\n\n\
                 The board only ranks completions that provably reach the win."
            ),
        }
    }
}

/// The full 64-hex content address of a universe (what `list` prints and `show`/`play`
/// accept — a unique prefix is enough).
fn id_hex(id: &UniverseId) -> String {
    id.as_bytes().iter().map(|b| format!("{b:02x}")).collect()
}

fn hex32(bytes: &[u8; 32]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn hex64(bytes: &[u8; 64]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn provenance_label(p: &Provenance) -> &'static str {
    match p {
        Provenance::Authored => "authored",
        Provenance::Procgen { .. } => "procgen (committed seed)",
    }
}

/// Resolve a user-typed id (a full content address, or any unambiguous prefix of one)
/// to a published universe.
fn find_universe(reg: &Registry, needle: &str) -> Option<UniverseId> {
    let needle = needle.trim().to_ascii_lowercase();
    if needle.is_empty() {
        return None;
    }
    let mut hits = reg
        .universes()
        .map(|u| u.id())
        .filter(|id| id_hex(id).starts_with(&needle));
    let first = hits.next()?;
    // Ambiguous prefix: refuse rather than silently pick one.
    if hits.next().is_some() {
        None
    } else {
        Some(first)
    }
}

/// **LIST** every published universe.
fn list_universes(reg: &Registry) -> Vec<UniverseSummary> {
    reg.universes()
        .map(|u| UniverseSummary {
            id_hex: id_hex(&u.id()),
            name: u.name().to_string(),
            author: u.author().to_string(),
            provenance: provenance_label(u.provenance()),
            entries: reg.leaderboard(u.id()).len(),
        })
        .collect()
}

/// **SHOW** a universe + its no-cheat leaderboard (verified completions, ranked).
fn show_universe(reg: &Registry, needle: &str) -> Option<UniverseView> {
    let id = find_universe(reg, needle)?;
    let u = reg.universe(id)?;

    let win = if u.win().vars.is_empty() {
        "the scene ENDED".to_string()
    } else {
        let vars = u
            .win()
            .vars
            .iter()
            .map(|(k, v)| format!("`{k} == {v}`"))
            .collect::<Vec<_>>()
            .join(" and ");
        format!("the scene ENDED and {vars}")
    };

    let board = reg
        .leaderboard(id)
        .into_iter()
        .enumerate()
        .map(|(i, e)| BoardEntry {
            rank: i + 1,
            player: e.player.clone(),
            turns: e.turns,
            completion_hex: hex32(&e.completion_id),
        })
        .collect();

    Some(UniverseView {
        id_hex: id_hex(&id),
        name: u.name().to_string(),
        author: u.author().to_string(),
        provenance: provenance_label(u.provenance()),
        regenerates: match u.provenance() {
            Provenance::Procgen { .. } => Some(u.regenerates_from_seed()),
            Provenance::Authored => None,
        },
        win: win.clone(),
        passages: u.source().matches("=== ").count(),
        author_key_hex: u.author_id().map(|a| a.hex()),
        parent_id_hex: u.parent().map(|p| id_hex(&p)),
        board,
    })
}

/// Something that can **attest** a universe: the author's public key + a signer over the
/// content commitment. The bot's implementation ([`CclerkSigner`]) is the publisher's
/// custodial cipherclerk; a test can supply any ed25519 key.
trait UniverseSigner {
    /// The author's ed25519 public key (bound into the universe's content address).
    fn public_key(&self) -> [u8; 32];
    /// Sign the 32-byte content commitment, producing the attestation signature.
    fn sign(&self, commitment: &[u8; 32]) -> AuthorSignature;
}

/// Attest a universe with a Discord user's custodial cipherclerk — the SAME ed25519 key
/// their `play` runs are bound to. Built from the cclerk's raw seed (== its ed25519
/// secret; see `cipherclerk`), so `public_key()` equals the cclerk's identity.
struct CclerkSigner {
    signing_key: SigningKey,
}

impl CclerkSigner {
    fn from_cclerk(cclerk: &UserCipherclerk) -> CclerkSigner {
        CclerkSigner {
            signing_key: SigningKey::from_bytes(cclerk.legacy_secret()),
        }
    }
}

impl UniverseSigner for CclerkSigner {
    fn public_key(&self) -> [u8; 32] {
        self.signing_key.verifying_key().to_bytes()
    }
    fn sign(&self, commitment: &[u8; 32]) -> AuthorSignature {
        AuthorSignature::from_bytes(self.signing_key.sign(commitment).to_bytes())
    }
}

/// Why a `/gallery publish` did not land. Every arm is a REAL refusal.
#[derive(Debug)]
enum PublishFail {
    /// The seed did not produce a deployable universe, or the author attestation did not
    /// verify (a mismatched/forged author key).
    Build(PublishError),
    /// A `parent` was named for a remix, but nothing published matches it.
    UnknownParent(String),
    /// The parent vanished between resolution and publish (a lineage race — should not
    /// happen under the single registry lock, surfaced for completeness).
    Lineage(LineageError),
}

impl std::fmt::Display for PublishFail {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PublishFail::Build(e) => write!(f, "{e}"),
            PublishFail::UnknownParent(needle) => write!(
                f,
                "no published universe matches the parent `{needle}` — try `/gallery list`"
            ),
            PublishFail::Lineage(e) => write!(f, "{e}"),
        }
    }
}

/// **PUBLISH** a real procgen universe from a committed seed, **signed by its author**.
/// The `seed` text is hashed into the 32-byte epoch commitment [`Universe::daily`] derives
/// its verifiable `CommittedSeed` from, so the world is drawn from procgen-dregg's VERIFIED
/// draw stream (never `rand`) and anyone holding the same seed re-derives the byte-identical
/// world. The author `signer` attests it — the ed25519 key is bound into the content
/// address, so authorship is unforgeable. An optional `parent` makes it a REMIX/fork of an
/// already-published universe (refused if the parent does not exist). Idempotent by content
/// address.
fn publish_universe(
    reg: &mut Registry,
    author: &str,
    seed_text: &str,
    parent: Option<&str>,
    signer: &dyn UniverseSigner,
) -> Result<UniverseId, PublishFail> {
    let epoch: [u8; 32] = *blake3::hash(seed_text.as_bytes()).as_bytes();
    let parent_id = match parent {
        None => None,
        Some(needle) => Some(
            find_universe(reg, needle).ok_or_else(|| PublishFail::UnknownParent(needle.into()))?,
        ),
    };
    let plan = UniversePlan::daily(author, &epoch, parent_id).map_err(PublishFail::Build)?;
    let signature = signer.sign(&plan.signing_commitment());
    let universe = plan
        .attest(signer.public_key(), signature)
        .map_err(PublishFail::Build)?;
    reg.publish_derived(universe).map_err(PublishFail::Lineage)
}

/// **PLAY** — submit a run. The moves are recorded on a REAL, freshly-deployed,
/// identically-seeded world (an illegal move is refused *here*, by the executor), and the
/// resulting receipt chain is handed to the registry's no-cheat gate, which re-executes it
/// from scratch and only ranks it if it provably reaches the win.
///
/// The claimed turn count is bound to the true move count, so a `ResultMismatch` is
/// impossible *from this path* — the tampering the gate defends against is a hand-crafted
/// submission, and the gate still checks it.
fn play_universe(
    reg: &mut Registry,
    needle: &str,
    player: &str,
    moves: &[usize],
) -> Result<Accepted, PlayError> {
    let id = find_universe(reg, needle).ok_or(PlayError::UnknownUniverse)?;
    let universe = reg.universe(id).ok_or(PlayError::UnknownUniverse)?.clone();

    let play = record_playthrough(&universe, moves)
        .map_err(|e| PlayError::RecordRefused(e.to_string()))?;
    let claimed_turns = play.steps.len();

    reg.submit(Completion {
        universe: id,
        player: player.to_string(),
        play,
        claimed_turns,
    })
    .map_err(PlayError::Rejected)
}

/// Parse a `moves` argument: choice indices, comma- and/or space-separated
/// (`"0,0,0"`, `"0 0 0"`, `"0, 0, 0"`).
fn parse_moves(raw: &str) -> Result<Vec<usize>, String> {
    let moves: Result<Vec<usize>, _> = raw
        .split([',', ' ', '\t'])
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(|s| {
            s.parse::<usize>()
                .map_err(|_| format!("`{s}` is not a choice index (expected a number like `0`)"))
        })
        .collect();
    let moves = moves?;
    if moves.is_empty() {
        return Err("give at least one move, e.g. `0,0,0`".to_string());
    }
    Ok(moves)
}

// ═══════════════════════════════════════════════════════════════════════════════
// The Discord surface.
// ═══════════════════════════════════════════════════════════════════════════════

/// Register the /gallery command.
pub fn register() -> CreateCommand {
    CreateCommand::new("gallery")
        .description("Browse, publish, and play authored dregg universes (no-cheat leaderboards)")
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "list",
            "List every published universe",
        ))
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "show",
                "Show a universe and its verified leaderboard",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "universe",
                    "Universe id (a prefix of the content address is fine)",
                )
                .required(true),
            ),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "publish",
                "Publish a procgen universe (signed by your wallet key), optionally a remix",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "seed",
                    "Seed text — the same seed always regenerates the same world",
                )
                .required(true),
            )
            .add_sub_option(CreateCommandOption::new(
                CommandOptionType::String,
                "parent",
                "Remix: parent universe id (a prefix of its content address)",
            ))
            .add_sub_option(CreateCommandOption::new(
                CommandOptionType::Boolean,
                "pin",
                "Also pin the canonical payload to the configured IPFS node (durable across gateways)",
            )),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "play",
                "Submit a run — only a verified win is ranked",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "universe",
                    "Universe id (a prefix of the content address is fine)",
                )
                .required(true),
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "moves",
                    "Your choice indices, e.g. 0,0,0",
                )
                .required(true),
            ),
        )
}

/// Handle /gallery interactions.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let subcommand = &command.data.options[0].name;

    match subcommand.as_str() {
        "list" => handle_list(ctx, command).await,
        "show" => handle_show(ctx, command).await,
        "publish" => handle_publish(ctx, command, state).await,
        "play" => handle_play(ctx, command, state).await,
        _ => {}
    }
}

async fn handle_list(ctx: &Context, command: &CommandInteraction) {
    defer_ephemeral(ctx, command).await;

    // Take the registry lock in a tight sync scope — never held across an await.
    let universes = {
        let reg = registry().lock().expect("universe registry lock");
        list_universes(&reg)
    };

    if universes.is_empty() {
        let embed = embeds::dregg_embed("Universe Gallery").description(
            "No universes are published yet. Mint one with `/gallery publish seed:<anything>`.",
        );
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    }

    let mut description = String::new();
    for u in universes.iter().take(10) {
        description.push_str(&format!(
            "**{}** by {}\n{} · {} verified completion(s)\nID: `{}`\n\n",
            u.name,
            u.author,
            u.provenance,
            u.entries,
            &u.id_hex[..16],
        ));
    }
    description.push_str("`/gallery show universe:<id>` for a universe's leaderboard.");

    let embed = embeds::dregg_embed("Universe Gallery")
        .description(description)
        .field("Published", universes.len().to_string(), true);
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

async fn handle_show(ctx: &Context, command: &CommandInteraction) {
    let needle = string_option(command, "universe").unwrap_or_default();
    defer_ephemeral(ctx, command).await;

    let view = {
        let reg = registry().lock().expect("universe registry lock");
        show_universe(&reg, &needle)
    };

    let Some(view) = view else {
        let embed = embeds::error_embed(
            "No Such Universe",
            &format!(
                "Nothing published matches `{needle}` (or the prefix is ambiguous).\n\n\
                 Use `/gallery list` to see what's out there."
            ),
        );
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    };

    // The transport address (#19): the payload CID — content-derived (no network), shown so
    // a stranger can fetch + re-verify the universe off any gateway
    // (`ugc_dregg::ipfs::fetch_universe` re-derives the id; a lying gateway is refused).
    let ipfs_note: Option<String> = {
        let published = {
            let reg = registry().lock().expect("universe registry lock");
            find_universe(&reg, &needle).and_then(|id| reg.universe(id).cloned())
        };
        match published {
            Some(u) => {
                tokio::task::spawn_blocking(move || crate::commands::gallery_ipfs::show_note(&u))
                    .await
                    .ok()
            }
            None => None,
        }
    };

    let mut board = String::new();
    if view.board.is_empty() {
        board.push_str(
            "No verified completions yet — be the first.\n`/gallery play universe:<id> moves:0,0,0`",
        );
    } else {
        for e in view.board.iter().take(10) {
            board.push_str(&format!(
                "**{}.** {} — **{} turn(s)**\n  completion `{}`\n",
                e.rank,
                e.player,
                e.turns,
                &e.completion_hex[..16],
            ));
        }
        board.push_str(
            "\nEvery entry here **re-verified**: its recorded moves were re-executed on a fresh \
             world and reached the win. Nothing is on this board on its word.",
        );
    }

    let provenance = match view.regenerates {
        Some(true) => format!(
            "{} — regenerates byte-for-byte from its seed",
            view.provenance
        ),
        Some(false) => format!("{} — ⚠ does NOT regenerate from its seed", view.provenance),
        None => view.provenance.to_string(),
    };

    let author_line = match &view.author_key_hex {
        Some(key) => format!(
            "by **{}** · verified author ed25519 `{}…`",
            view.author,
            &key[..16.min(key.len())]
        ),
        None => format!("by **{}** (anonymous — no verified key)", view.author),
    };
    let mut embed = embeds::dregg_embed(&view.name)
        .description(format!("{author_line}\n\nID: `{}`", view.id_hex))
        .field("Provenance", provenance, false);
    if let Some(parent) = &view.parent_id_hex {
        embed = embed.field(
            "Remix of",
            format!("`{}…` (a fork in the derivation graph)", &parent[..16]),
            false,
        );
    }
    let mut embed = embed
        .field("Win condition", view.win, false)
        .field("Passages", view.passages.to_string(), true)
        .field("Ranked", view.board.len().to_string(), true)
        .field("No-cheat leaderboard", board, false);
    if let Some(note) = ipfs_note {
        embed = embed.field("IPFS", note, false);
    }
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

async fn handle_publish(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let seed_text = string_option(command, "seed").unwrap_or_default();
    let parent_needle = string_option(command, "parent");
    // The IPFS join (#19): `pin:true` additionally pins the canonical payload to the
    // configured node; the CID is shown either way (it is content-derived).
    let pin = bool_option(command, "pin").unwrap_or(false);
    let author = command.user.name.clone();
    let user_id = command.user.id.get();
    defer_ephemeral(ctx, command).await;

    // The epoch commitment `Universe::daily` regenerates the world from — the same
    // `blake3(seed_text)` `publish_universe` derives internally, captured here so we can
    // persist the universe's reproducible public source.
    let epoch: [u8; 32] = *blake3::hash(seed_text.as_bytes()).as_bytes();

    // The author attests the universe with THEIR custodial cipherclerk — the same ed25519
    // identity their `play` runs are bound to. Deterministic from the bot secret + Discord
    // id, so every publisher has a stable, verifiable author key (no `/cipherclerk create`
    // prerequisite — the key is derivable).
    let cclerk =
        UserCipherclerk::derive(&state.config.bot_secret, user_id, state.federation_id_bytes);
    let signer = CclerkSigner::from_cclerk(&cclerk);

    // Capture the persistable descriptor + view under the lock; persist AFTER releasing it
    // (the store may do blocking sqlite IO — never hold the registry lock across it).
    let result = {
        let mut reg = registry().lock().expect("universe registry lock");
        publish_universe(
            &mut reg,
            &author,
            &seed_text,
            parent_needle.as_deref(),
            &signer,
        )
        .map(|id| {
            let stored = reg
                .universe(id)
                .map(|u| StoredUniverse::daily_desc(id, &author, &epoch, u));
            let view = show_universe(&reg, &id_hex(&id));
            // A clone for the IPFS join — the CID derives (and a pin encodes) OFF the lock.
            let published = reg.universe(id).cloned();
            (stored, view, published)
        })
    };

    match result {
        Ok((stored, Some(view), published)) => {
            // Durable: the published universe survives a restart (re-derived from its
            // seed-epoch, its author attestation + lineage re-verified on boot).
            if let Some(stored) = stored {
                store_universe(&stored);
            }
            let mut embed = embeds::success_embed("Universe Published")
                .description(format!(
                    "**{}** by **{}**\n\nID: `{}`",
                    view.name, view.author, view.id_hex
                ))
                .field("Provenance", view.provenance, true)
                .field("Passages", view.passages.to_string(), true)
                .field("Win condition", view.win.clone(), false);
            if let Some(key) = &view.author_key_hex {
                embed = embed.field(
                    "Verified author",
                    format!(
                        "ed25519 `{}…` — signed by your wallet key and bound into the content \
                         address, so this authorship is unforgeable.",
                        &key[..16.min(key.len())]
                    ),
                    false,
                );
            }
            if let Some(parent) = &view.parent_id_hex {
                embed = embed.field(
                    "Remix of",
                    format!(
                        "`{}…` — a fork recorded in the derivation graph.",
                        &parent[..16]
                    ),
                    false,
                );
            }
            embed = embed
                .field(
                    "Content-addressed",
                    "The id is the hash of the world itself. Republishing the same seed is \
                     idempotent, and anyone holding the seed regenerates this exact world.",
                    false,
                )
                .field(
                    "Play it",
                    format!(
                        "`/gallery play universe:{} moves:0,0,0`",
                        &view.id_hex[..16]
                    ),
                    false,
                );
            // The IPFS join (#19): derive the CID (pure) and, on `pin:true`, pin the payload
            // to the configured node — blocking IO off the async loop; the note reports the
            // node's own refusal honestly.
            if let Some(u) = published {
                let note = tokio::task::spawn_blocking(move || {
                    crate::commands::gallery_ipfs::publish_note(&u, pin)
                })
                .await
                .unwrap_or_else(|e| format!("the IPFS task did not complete: {e}"));
                embed = embed.field("IPFS", note, false);
            }
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Ok((_, None, _)) => {
            let embed = embeds::error_embed(
                "Publish Failed",
                "The published universe could not be shown.",
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Publish Failed", &format!("Publish refused: {e}"));
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

async fn handle_play(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let discord_id = command.user.id.get().to_string();
    let user_id = command.user.id.get();
    let player = command.user.name.clone();

    let needle = string_option(command, "universe").unwrap_or_default();
    let raw_moves = string_option(command, "moves").unwrap_or_default();

    defer_ephemeral(ctx, command).await;

    // A run is signed by the player's custodial cclerk (the old bid-signing path,
    // repurposed): the completion is bound to their Discord-derived identity.
    let has_cclerk = match state.db.get_cell_id(&discord_id).await {
        Ok(Some(_)) => true,
        Ok(None) => {
            let embed = embeds::warning_embed(
                "No Cipherclerk",
                "You need a wallet to submit a run. Use `/start` → **Just create my wallet** (or `/cipherclerk create`).",
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
        Err(e) => {
            let embed = embeds::error_embed("Database Error", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    };
    debug_assert!(has_cclerk);

    let moves = match parse_moves(&raw_moves) {
        Ok(m) => m,
        Err(e) => {
            let embed = embeds::error_embed("Bad Moves", &PlayError::BadMoves(e).to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    };

    let cclerk =
        UserCipherclerk::derive(&state.config.bot_secret, user_id, state.federation_id_bytes);
    let signature = sign_run(&cclerk, &needle, &moves);

    // Resolve the universe to its FULL content address under the lock (the completion is
    // stored against the full id, not the user-typed prefix), then submit.
    let outcome = {
        let mut reg = registry().lock().expect("universe registry lock");
        let resolved_hex = find_universe(&reg, &needle).map(|id| id_hex(&id));
        play_universe(&mut reg, &needle, &player, &moves).map(|acc| (resolved_hex, acc))
    };

    match outcome {
        Ok((resolved_hex, accepted)) => {
            // Durable: the verified completion survives a restart. Only the moves + player
            // + verified turns are stored; the board is rebuilt by REPLAY on boot, so a
            // tampered row cannot resurrect a cheat.
            if let Some(hex) = &resolved_hex {
                store_completion(&StoredCompletion::new(hex, &player, &moves, accepted.turns));
            }
            let embed = embeds::success_embed("Run Verified — You're On The Board")
                .description(
                    "Your moves were **re-executed on a fresh, identically-seeded world** and they \
                     reached the win. That is why you are ranked — not because you said so.",
                )
                .field("Rank", format!("#{}", accepted.rank), true)
                .field("Turns", accepted.turns.to_string(), true)
                .field(
                    "Completion",
                    format!("`{}`", &hex32(&accepted.completion_id)[..16]),
                    true,
                )
                .field(
                    "Signed by your wallet key",
                    format!("`{}`", &signature[..16.min(signature.len())]),
                    false,
                );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Run Rejected", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

/// Sign a submitted run with the player's cipherclerk (the legacy BLAKE3-MAC wire scheme,
/// `cclerk::sign_legacy` — the same machinery the retired auction-bid path used). The body
/// binds the universe and the exact move sequence:
/// `b"run:" + universe + b":" + each move's le bytes`.
fn sign_run(cclerk: &UserCipherclerk, universe: &str, moves: &[usize]) -> String {
    let mut msg = Vec::new();
    msg.extend_from_slice(b"run:");
    msg.extend_from_slice(universe.as_bytes());
    msg.extend_from_slice(b":");
    for m in moves {
        msg.extend_from_slice(&(*m as u64).to_le_bytes());
    }
    sign_legacy(cclerk, &msg)
}

// ─── Helpers ────────────────────────────────────────────────────────────────

/// Pull a required String sub-option out of the invoked subcommand.
fn string_option(command: &CommandInteraction, name: &str) -> Option<String> {
    let CommandDataOptionValue::SubCommand(opts) = &command.data.options.first()?.value else {
        return None;
    };
    opts.iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
}

fn bool_option(command: &CommandInteraction, name: &str) -> Option<bool> {
    let CommandDataOptionValue::SubCommand(opts) = &command.data.options.first()?.value else {
        return None;
    };
    opts.iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::Boolean(b) => Some(*b),
            _ => None,
        })
}

async fn defer_ephemeral(ctx: &Context, command: &CommandInteraction) {
    let _ = command
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Defer(
                CreateInteractionResponseMessage::new().ephemeral(true),
            ),
        )
        .await;
}

// ═══════════════════════════════════════════════════════════════════════════════
// DRIVEN tests — the command's own logic against the REAL `ugc-dregg` registry.
//
// These call exactly what the handlers call (`list_universes` / `show_universe` /
// `publish_universe` / `play_universe`); the handlers are thin embed-renderers over
// them. Each test owns a fresh `Registry`, so nothing leans on the process-wide one.
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use dungeon_on_dregg::{CH_CLAIM, CH_DESCEND, CH_LEAVE_LANTERN, CH_TAKE_LANTERN};

    /// A deterministic author signer for tests — a fixed 32-byte ed25519 secret keyed by
    /// `tag`, so a given tag always yields the same verifiable author identity.
    struct TestSigner {
        key: SigningKey,
    }
    impl TestSigner {
        fn new(tag: u8) -> TestSigner {
            TestSigner {
                key: SigningKey::from_bytes(&[tag; 32]),
            }
        }
    }
    impl UniverseSigner for TestSigner {
        fn public_key(&self) -> [u8; 32] {
            self.key.verifying_key().to_bytes()
        }
        fn sign(&self, commitment: &[u8; 32]) -> AuthorSignature {
            AuthorSignature::from_bytes(self.key.sign(commitment).to_bytes())
        }
    }

    /// Publish a signed procgen universe with a fixed test author (tag `0x11`) and no
    /// parent — the common case for the pre-existing publish/play/leaderboard tests.
    /// Deterministic: same author + seed ⇒ same content address (ed25519 is deterministic
    /// and the id binds the pubkey, not the signature).
    fn publish_signed(reg: &mut Registry, author: &str, seed: &str) -> Result<UniverseId, String> {
        publish_universe(reg, author, seed, None, &TestSigner::new(0x11)).map_err(|e| e.to_string())
    }

    /// A test-owned publish of the real, winnable salt-shore dungeon.
    fn publish_dungeon(reg: &mut Registry) -> UniverseId {
        let u = Universe::authored(
            "The Salt Shore Descent",
            "tester",
            DUNGEON,
            WinCondition::ended_with(&[("gold", 500)]),
        )
        .expect("the built-in dungeon is a deployable universe");
        reg.publish(u)
    }

    /// The generated procgen dungeon is linear: at every room the winning choice is
    /// index 0 (take the key / press onward / descend the gate / seize the hoard).
    fn winning_moves(reg: &Registry, id: UniverseId) -> Vec<usize> {
        let rooms = reg
            .universe(id)
            .expect("published")
            .source()
            .matches("=== room")
            .count();
        vec![0usize; rooms]
    }

    #[test]
    fn the_seeded_gallery_is_not_empty_and_its_par_run_is_verified() {
        // The registry the bot actually boots with.
        let reg = seed_registry();
        let listed = list_universes(&reg);
        assert_eq!(listed.len(), 1, "the built-in dungeon is published");
        assert_eq!(listed[0].name, "The Salt Shore Descent");
        assert_eq!(listed[0].provenance, "authored");
        assert_eq!(
            listed[0].entries, 1,
            "the house's par run is on the board — and it is there only because it \
             re-verified to a real win"
        );

        let view = show_universe(&reg, &listed[0].id_hex).expect("show the built-in universe");
        assert_eq!(view.board.len(), 1);
        assert_eq!(view.board[0].rank, 1);
        assert_eq!(
            view.board[0].turns, 3,
            "the minimal winning line is 3 moves"
        );
        assert!(
            view.win.contains("gold"),
            "the win binds the hoard: {}",
            view.win
        );
    }

    #[test]
    fn publish_then_list_then_leaderboard_end_to_end() {
        let mut reg = Registry::new();
        assert!(list_universes(&reg).is_empty());

        // PUBLISH — a real procgen universe from a committed seed.
        let id = publish_signed(&mut reg, "ember", "gallery-drive-1").expect("publishes");
        let hex = id_hex(&id);

        // LIST — it is there, with its author + provenance.
        let listed = list_universes(&reg);
        assert_eq!(listed.len(), 1);
        assert_eq!(listed[0].author, "ember");
        assert_eq!(listed[0].provenance, "procgen (committed seed)");
        assert_eq!(listed[0].id_hex, hex);
        assert_eq!(listed[0].entries, 0, "a fresh universe has an empty board");

        // The content address is real: the same seed republishes idempotently.
        let again = publish_signed(&mut reg, "ember", "gallery-drive-1").expect("republishes");
        assert_eq!(again, id, "same seed + author ⇒ same content address");
        assert_eq!(list_universes(&reg).len(), 1, "no duplicate was created");

        // ...and a DIFFERENT seed is a different world.
        let other = publish_signed(&mut reg, "ember", "gallery-drive-2").expect("publishes");
        assert_ne!(other, id, "a different seed is a different universe");
        assert_eq!(list_universes(&reg).len(), 2);

        // SHOW — the procgen world regenerates byte-for-byte from its committed seed.
        let view = show_universe(&reg, &hex).expect("show");
        assert_eq!(view.regenerates, Some(true));
        assert!(view.passages >= 4, "the generated dungeon has rooms");

        // PLAY — a REAL winning run against the real executor.
        let moves = winning_moves(&reg, id);
        let accepted =
            play_universe(&mut reg, &hex, "ada", &moves).expect("a real win is accepted");
        assert_eq!(accepted.rank, 1);
        assert_eq!(accepted.turns, moves.len());

        // LEADERBOARD — the verified completion is ranked.
        let view = show_universe(&reg, &hex).expect("show");
        assert_eq!(view.board.len(), 1);
        assert_eq!(view.board[0].player, "ada");
        assert_eq!(view.board[0].rank, 1);
        assert_eq!(view.board[0].turns, moves.len());
        // Target THIS universe by id (two are published; list order is by content address).
        assert_eq!(
            list_universes(&reg)
                .iter()
                .find(|u| u.id_hex == hex)
                .expect("published universe is listed")
                .entries,
            1
        );

        // A prefix of the content address resolves too (what a user actually types).
        assert!(show_universe(&reg, &hex[..16]).is_some());
    }

    #[test]
    fn a_cheat_run_is_rejected_and_never_touches_the_board() {
        let mut reg = Registry::new();
        let id = publish_dungeon(&mut reg);
        let hex = id_hex(&id);

        // An honest win first, so the board is non-empty and we can prove the cheat
        // changes nothing.
        let honest = play_universe(
            &mut reg,
            &hex,
            "ada",
            &[CH_TAKE_LANTERN, CH_DESCEND, CH_CLAIM],
        )
        .expect("the honest 3-move win is accepted");
        assert_eq!(honest.turns, 3);

        // THE CHEAT: skip the lantern, then try the gated descent. The gate
        // (`has_lantern >= 1`) is a real executor `StateConstraint`, not app code — so
        // the move is REFUSED on replay and the run never becomes a completion.
        let cheat = play_universe(
            &mut reg,
            &hex,
            "mallory",
            &[CH_LEAVE_LANTERN, CH_DESCEND, CH_CLAIM],
        );
        assert!(
            matches!(
                cheat,
                Err(PlayError::RecordRefused(_)) | Err(PlayError::Rejected(_))
            ),
            "a keyless descent must be REFUSED, got {cheat:?}"
        );

        // AN INCOMPLETE RUN: real moves, but it never reaches the win. The board
        // rejects it explicitly.
        let partial = play_universe(&mut reg, &hex, "quinn", &[CH_TAKE_LANTERN]);
        assert!(
            matches!(partial, Err(PlayError::Rejected(RejectReason::DidNotWin))),
            "an incomplete run must be rejected as DidNotWin, got {partial:?}"
        );

        // Non-vacuous: NEITHER cheat landed. Only ada is ranked.
        let view = show_universe(&reg, &hex).expect("show");
        assert_eq!(view.board.len(), 1, "no cheat entry landed");
        assert_eq!(view.board[0].player, "ada");
    }

    #[test]
    fn the_board_ranks_by_turns_and_a_slower_real_win_still_counts() {
        let mut reg = Registry::new();
        let id = publish_dungeon(&mut reg);
        let hex = id_hex(&id);

        // bran plays first, but takes a detour (retreat to the shore and back) — a REAL
        // win, just a slower one: 5 moves.
        let bran = play_universe(
            &mut reg,
            &hex,
            "bran",
            &[
                CH_TAKE_LANTERN,
                dungeon_on_dregg::CH_RETREAT,
                CH_TAKE_LANTERN,
                CH_DESCEND,
                CH_CLAIM,
            ],
        )
        .expect("a slower but real win is still accepted");
        assert_eq!(bran.turns, 5);
        assert_eq!(bran.rank, 1, "first on an empty board");

        // ada then plays the minimal line and takes the top slot.
        let ada = play_universe(
            &mut reg,
            &hex,
            "ada",
            &[CH_TAKE_LANTERN, CH_DESCEND, CH_CLAIM],
        )
        .expect("the minimal win is accepted");
        assert_eq!(ada.turns, 3);
        assert_eq!(ada.rank, 1, "fewer turns takes rank 1");

        let view = show_universe(&reg, &hex).expect("show");
        assert_eq!(view.board.len(), 2);
        assert_eq!(view.board[0].player, "ada");
        assert_eq!(view.board[0].turns, 3);
        assert_eq!(view.board[1].player, "bran");
        assert_eq!(view.board[1].turns, 5);
    }

    #[test]
    fn an_unknown_universe_and_bad_moves_are_honest_refusals() {
        let mut reg = Registry::new();
        publish_dungeon(&mut reg);

        assert!(show_universe(&reg, "deadbeef").is_none());
        assert!(matches!(
            play_universe(&mut reg, "deadbeef", "nobody", &[0]),
            Err(PlayError::UnknownUniverse)
        ));

        assert!(parse_moves("").is_err());
        assert!(parse_moves("north").is_err());
        assert_eq!(parse_moves("0,0,0").unwrap(), vec![0, 0, 0]);
        assert_eq!(parse_moves("0 1  2").unwrap(), vec![0, 1, 2]);

        // An out-of-range choice index is refused by the real executor, not by a
        // bounds-check we wrote.
        let hex = list_universes(&reg)[0].id_hex.clone();
        let out = play_universe(&mut reg, &hex, "confused", &[99]);
        assert!(
            matches!(out, Err(PlayError::RecordRefused(_))),
            "an impossible choice is refused by the executor, got {out:?}"
        );
    }

    // ═══════════════════════════════════════════════════════════════════════════
    // DURABLE STORE — persist → reload → RE-VERIFY, and every tampered-row rejection.
    // ═══════════════════════════════════════════════════════════════════════════

    /// Publish a daily universe from `seed` and win it, persisting BOTH to `store`.
    /// Returns the full universe id hex, the winning moves, and the verified turns.
    fn seed_store_with_daily_win(
        store: &InMemoryGalleryStore,
        seed: &str,
        player: &str,
    ) -> (String, Vec<usize>, usize) {
        let epoch: [u8; 32] = *blake3::hash(seed.as_bytes()).as_bytes();
        let mut reg = Registry::new();
        let id = publish_signed(&mut reg, "ember", seed).expect("publishes");
        let idhex = id_hex(&id);
        store
            .persist_universe(&StoredUniverse::daily_desc(
                id,
                "ember",
                &epoch,
                reg.universe(id).expect("published"),
            ))
            .expect("persist universe");
        let moves = winning_moves(&reg, id);
        let accepted = play_universe(&mut reg, &idhex, player, &moves).expect("a real win");
        store
            .persist_completion(&StoredCompletion::new(
                &idhex,
                player,
                &moves,
                accepted.turns,
            ))
            .expect("persist completion");
        (idhex, moves, accepted.turns)
    }

    #[test]
    fn durable_store_persists_and_reload_reverifies_the_board() {
        let store = InMemoryGalleryStore::new();
        let (idhex, moves, turns) = seed_store_with_daily_win(&store, "durable-gallery-1", "ada");

        assert_eq!(
            store.list_universes().unwrap().len(),
            1,
            "universe persisted"
        );
        assert_eq!(
            store.list_completions().unwrap().len(),
            1,
            "completion persisted"
        );

        // A FRESH process: rebuild the live registry from the store alone. Every completion
        // is re-verified by replay on a fresh identically-seeded world.
        let reg2 = load_registry(&store);
        let view = show_universe(&reg2, &idhex).expect("universe survived the restart");
        assert_eq!(
            view.board.len(),
            1,
            "the verified completion was rebuilt by replay"
        );
        assert_eq!(view.board[0].player, "ada");
        assert_eq!(view.board[0].turns, turns);

        // Idempotent: a second load does not duplicate the board entry...
        let reg3 = load_registry(&store);
        assert_eq!(
            show_universe(&reg3, &idhex).unwrap().board.len(),
            1,
            "double-load did not duplicate"
        );
        // ...and re-persisting the identical run is a no-op (idempotency PK).
        store
            .persist_completion(&StoredCompletion::new(&idhex, "ada", &moves, turns))
            .unwrap();
        assert_eq!(store.list_completions().unwrap().len(), 1);
    }

    #[test]
    fn a_tampered_completion_row_does_not_reverify_and_is_off_the_board() {
        let store = InMemoryGalleryStore::new();
        let (idhex, _moves, _turns) =
            seed_store_with_daily_win(&store, "durable-gallery-tamper-moves", "ada");

        // Non-vacuous baseline: the UNtampered store rebuilds a 1-entry board.
        assert_eq!(
            show_universe(&load_registry(&store), &idhex)
                .unwrap()
                .board
                .len(),
            1
        );

        // TAMPER the DB row: rewrite the moves to a non-winning line (take the key and
        // stop — never reach the hoard). This is exactly a forged/edited stored playthrough.
        store.tamper(|_us, cs| {
            for c in cs.iter_mut() {
                c.moves_json = "[0]".to_string();
            }
        });

        let reg = load_registry(&store);
        let view = show_universe(&reg, &idhex).expect("universe still loads");
        assert_eq!(
            view.board.len(),
            0,
            "the tampered completion did NOT re-verify — the no-cheat gate kept it off the board"
        );
    }

    #[test]
    fn a_tampered_claimed_turns_row_is_rejected_as_result_mismatch() {
        let store = InMemoryGalleryStore::new();
        let (idhex, _moves, _turns) =
            seed_store_with_daily_win(&store, "durable-gallery-tamper-turns", "ada");

        // TAMPER: keep the genuinely-winning moves, but LIE about the turn count. The
        // result-binding tooth (`ResultMismatch`) survives persistence.
        store.tamper(|_us, cs| {
            for c in cs.iter_mut() {
                c.claimed_turns += 99;
            }
        });

        let reg = load_registry(&store);
        assert_eq!(
            show_universe(&reg, &idhex).unwrap().board.len(),
            0,
            "a lied claimed_turns trips ResultMismatch on reload"
        );
    }

    #[test]
    fn a_tampered_universe_row_is_dropped_and_takes_its_board_with_it() {
        let store = InMemoryGalleryStore::new();
        let (idhex, _moves, _turns) =
            seed_store_with_daily_win(&store, "durable-gallery-tamper-universe", "ada");

        // Baseline: untampered, the universe + its board come back.
        assert!(show_universe(&load_registry(&store), &idhex).is_some());

        // TAMPER the universe row: change the author so `Universe::daily` reconstructs a
        // DIFFERENT world whose recomputed content address no longer matches the stored id.
        store.tamper(|us, _cs| {
            for u in us.iter_mut() {
                u.author = "mallory".to_string();
            }
        });

        let reg = load_registry(&store);
        assert!(
            show_universe(&reg, &idhex).is_none(),
            "the tampered universe row was dropped (recomputed id != stored id)"
        );
    }

    #[test]
    fn an_authored_universe_and_its_win_roundtrip_through_the_store() {
        let store = InMemoryGalleryStore::new();
        let winning = [CH_TAKE_LANTERN, CH_DESCEND, CH_CLAIM];
        let idhex = {
            let mut reg = Registry::new();
            let id = publish_dungeon(&mut reg);
            let idhex = id_hex(&id);
            store
                .persist_universe(&StoredUniverse::authored_desc(reg.universe(id).unwrap()))
                .unwrap();
            let accepted = play_universe(&mut reg, &idhex, "ada", &winning).expect("real win");
            store
                .persist_completion(&StoredCompletion::new(
                    &idhex,
                    "ada",
                    &winning,
                    accepted.turns,
                ))
                .unwrap();
            idhex
        };

        // Reload reconstructs the authored universe from its stored source + win, and
        // re-verifies the completion.
        let reg = load_registry(&store);
        let view = show_universe(&reg, &idhex).expect("authored universe survived restart");
        assert!(view.win.contains("gold"), "the win condition roundtripped");
        assert_eq!(view.board.len(), 1);
        assert_eq!(view.board[0].turns, 3);
    }

    // ═══════════════════════════════════════════════════════════════════════════
    // VERIFIED AUTHOR IDENTITY + REMIX LINEAGE — the creator-economy foundation,
    // DRIVEN through the /gallery layer (signed publish, forged author refused, remix
    // records lineage, fake parent refused, and both re-verify on gallery boot).
    // ═══════════════════════════════════════════════════════════════════════════

    #[test]
    fn a_signed_publish_binds_a_real_author_key_and_a_forged_author_is_refused() {
        let mut reg = Registry::new();
        let author = TestSigner::new(0x42);

        // HONEST: publish signed by the author's key — it lands AND carries the verified id.
        let id = publish_universe(&mut reg, "ada", "signed-1", None, &author)
            .expect("an honestly-signed publish lands");
        let u = reg.universe(id).expect("published");
        assert!(
            u.is_signed(),
            "the published universe carries a verified author"
        );
        assert_eq!(
            u.author_id().unwrap().as_bytes(),
            &author.public_key(),
            "the bound key is the author's real key"
        );
        // The gallery view surfaces it.
        let view = show_universe(&reg, &id_hex(&id)).unwrap();
        assert_eq!(view.author_key_hex.unwrap(), hex32(&author.public_key()));

        // FORGERY: a signer whose signature does NOT match the pubkey it presents. We build
        // one by hand: present ada's pubkey but sign with mallory's key.
        struct ForgedSigner {
            claim: [u8; 32],
            secret: SigningKey,
        }
        impl UniverseSigner for ForgedSigner {
            fn public_key(&self) -> [u8; 32] {
                self.claim
            }
            fn sign(&self, c: &[u8; 32]) -> AuthorSignature {
                AuthorSignature::from_bytes(self.secret.sign(c).to_bytes())
            }
        }
        let forger = ForgedSigner {
            claim: author.public_key(),                  // claims ada's key…
            secret: SigningKey::from_bytes(&[0xFF; 32]), // …but signs with a different secret
        };
        let out = publish_universe(&mut reg, "ada", "signed-forge", None, &forger);
        assert!(
            matches!(out, Err(PublishFail::Build(PublishError::AuthorSignature))),
            "claiming an author key without its signature must be REFUSED, got {out:?}"
        );
        // Non-vacuous: only the honest universe is registered.
        assert_eq!(
            reg.universes().count(),
            1,
            "the forged publish did not land"
        );
    }

    #[test]
    fn a_remix_records_lineage_and_a_fake_parent_is_refused() {
        let mut reg = Registry::new();
        let author = TestSigner::new(0x7A);

        // A published ROOT.
        let root = publish_universe(&mut reg, "ada", "lineage-root", None, &author).expect("root");
        let root_hex = id_hex(&root);
        assert_eq!(reg.is_root(root), Some(true));

        // A REMIX of it (a prefix of the parent id resolves).
        let remix = publish_universe(
            &mut reg,
            "bran",
            "lineage-remix",
            Some(&root_hex[..16]),
            &author,
        )
        .expect("a remix of a real parent lands");
        assert_eq!(
            reg.parent_of(remix),
            Some(root),
            "the lineage edge is recorded"
        );
        assert_eq!(reg.children_of(root), vec![remix]);
        assert!(reg.lineage_holds());
        // The view shows the remix's parent.
        assert_eq!(
            show_universe(&reg, &id_hex(&remix))
                .unwrap()
                .parent_id_hex
                .unwrap(),
            root_hex
        );

        // A remix of a NON-EXISTENT parent is REFUSED — non-vacuous.
        let out = publish_universe(
            &mut reg,
            "mallory",
            "lineage-orphan",
            Some("deadbeef"),
            &author,
        );
        assert!(
            matches!(out, Err(PublishFail::UnknownParent(_))),
            "a remix of a non-existent parent must be REFUSED, got {out:?}"
        );
        assert_eq!(reg.universes().count(), 2, "the orphan did not land");
    }

    /// Publish a SIGNED root + a SIGNED remix of it, and persist both to `store`.
    /// Returns (root id hex, remix id hex).
    fn seed_store_with_signed_lineage(store: &InMemoryGalleryStore) -> (String, String) {
        let author = TestSigner::new(0x5C);
        let mut reg = Registry::new();

        let root = publish_universe(&mut reg, "ada", "boot-root", None, &author).expect("root");
        let root_hex = id_hex(&root);
        let root_epoch: [u8; 32] = *blake3::hash("boot-root".as_bytes()).as_bytes();
        store
            .persist_universe(&StoredUniverse::daily_desc(
                root,
                "ada",
                &root_epoch,
                reg.universe(root).unwrap(),
            ))
            .unwrap();

        let remix = publish_universe(&mut reg, "bran", "boot-remix", Some(&root_hex), &author)
            .expect("remix");
        let remix_hex = id_hex(&remix);
        let remix_epoch: [u8; 32] = *blake3::hash("boot-remix".as_bytes()).as_bytes();
        store
            .persist_universe(&StoredUniverse::daily_desc(
                remix,
                "bran",
                &remix_epoch,
                reg.universe(remix).unwrap(),
            ))
            .unwrap();

        (root_hex, remix_hex)
    }

    #[test]
    fn the_derivation_graph_and_author_identity_reverify_on_boot() {
        let store = InMemoryGalleryStore::new();
        let (root_hex, remix_hex) = seed_store_with_signed_lineage(&store);

        // A FRESH process: rebuild from the store alone. The author attestations are
        // re-verified and the lineage re-checked (parent published before child).
        let reg = load_registry(&store);
        let root = find_universe(&reg, &root_hex).expect("root survived restart");
        let remix = find_universe(&reg, &remix_hex).expect("remix survived restart");
        assert!(
            reg.universe(root).unwrap().is_signed(),
            "root author re-verified"
        );
        assert!(
            reg.universe(remix).unwrap().is_signed(),
            "remix author re-verified"
        );
        assert_eq!(
            reg.parent_of(remix),
            Some(root),
            "the derivation edge was rebuilt"
        );
        assert!(reg.lineage_holds(), "the reconstructed graph is sound");
    }

    #[test]
    fn a_tampered_lineage_row_fails_and_the_child_drops_off() {
        let store = InMemoryGalleryStore::new();
        let (_root_hex, remix_hex) = seed_store_with_signed_lineage(&store);

        // Baseline: untampered, the remix reconstructs.
        assert!(find_universe(&load_registry(&store), &remix_hex).is_some());

        // TAMPER the lineage: repoint the remix's parent at a universe that isn't there.
        // The parent is bound into the child's content address, so the recomputed id no
        // longer matches the stored id_hex — the row is dropped on reload.
        store.tamper(|us, _cs| {
            for u in us.iter_mut() {
                if u.parent_id_hex.is_some() {
                    u.parent_id_hex = Some("00".repeat(32));
                }
            }
        });

        let reg = load_registry(&store);
        assert!(
            find_universe(&reg, &remix_hex).is_none(),
            "the tampered-lineage remix did NOT re-verify and is off the gallery"
        );
        assert!(reg.lineage_holds(), "no dangling edge survived");
    }

    #[test]
    fn a_tampered_author_signature_row_fails_to_reverify() {
        let store = InMemoryGalleryStore::new();
        let author = TestSigner::new(0x3B);
        let mut reg = Registry::new();
        let id =
            publish_universe(&mut reg, "ada", "boot-authtamper", None, &author).expect("signed");
        let idhex = id_hex(&id);
        let epoch: [u8; 32] = *blake3::hash("boot-authtamper".as_bytes()).as_bytes();
        store
            .persist_universe(&StoredUniverse::daily_desc(
                id,
                "ada",
                &epoch,
                reg.universe(id).unwrap(),
            ))
            .unwrap();

        // Baseline: untampered, it reconstructs (author attestation re-verifies).
        assert!(find_universe(&load_registry(&store), &idhex).is_some());

        // TAMPER the attestation signature — flip a byte. It no longer verifies against the
        // bound key, so `attest` refuses it on reload and the row is dropped.
        store.tamper(|us, _cs| {
            for u in us.iter_mut() {
                if let Some(sig) = &u.author_sig_hex {
                    let mut bytes = sig.clone().into_bytes();
                    bytes[0] ^= 1; // corrupt the first hex nibble
                    u.author_sig_hex = Some(String::from_utf8(bytes).unwrap());
                }
            }
        });

        let reg = load_registry(&store);
        assert!(
            find_universe(&reg, &idhex).is_none(),
            "a forged/tampered author signature must fail re-verification on boot"
        );
    }
}
