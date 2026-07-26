//! # The **table lock** — ONE seat-secret discipline, shared by every seat-locked two-player table.
//!
//! The automatafl front door ([`crate::automatafl_web`]) proved the shape: a table is minted with an
//! unguessable id and two unguessable per-seat secrets, and the act path REFUSES any actor that is
//! not one of those two. This module is that mechanism, lifted out of automatafl so the tug's front
//! door ([`crate::tug_web`]) reuses it **byte-for-byte** rather than growing a second, divergent
//! implementation of seat authorisation. Two implementations of an auth rule is strictly worse than
//! one: the second one is where the hole lives.
//!
//! ## What a lock is
//!
//! A [`TableLock`] is three strings and a route:
//!
//! | | automatafl | tug |
//! |---|---|---|
//! | catalog key | `automatafl` | `tug` |
//! | table prefix | `af1-` | `tug1-` |
//! | seat prefix | `afs1-` | `tugs1-` |
//! | front door | `/automatafl` | `/tug` |
//!
//! and it derives, under ONE server key `K`:
//!
//! * `table id = <prefix><96 random bits>` — not derived from anything a caller supplies, so a
//!   table is not reachable by guessing an id;
//! * `seat label = <seat-prefix>{a|b}-<128 bits of blake3_keyed(K, id‖seat)>`. The catalog turns a
//!   browser's asserted label into its actor (`blake3(label)`), so **holding the label is holding
//!   the seat**, and neither seat's holder can derive the other's.
//!
//! [`enforce`] then refuses any act on a prefixed table from a label that is not one of that
//! table's two — so the seats cannot be stolen by racing to POST first, and the per-viewer
//! hidden-state disclosure (automatafl's sealed move, the tug's hand) cannot be reached by
//! asserting the opponent's label.
//!
//! **Not closed, and deliberately named:** an *ad-hoc* session id (`/offerings/tug/session/mine`)
//! keeps the catalog's open asserted-identity model — seats go to whoever POSTs first, and
//! asserting the other seat's label renders their private state. That is the catalog's identity
//! model, not a game bug; replacing it is a different lane. What this lane DID remove is the
//! publicly-guessable *shared* table both games were advertising from the catalog page.
//!
//! ## The key, and how durable it is
//!
//! `K` is resolved once per process by [`seat_key`], in this order:
//!
//! 1. `DREGGNET_WEB_SEAT_KEY` — 64 hex chars. An operator-pinned key; outstanding links survive
//!    every restart of every replica.
//! 2. `<DREGGNET_WEB_SESSION_DIR>/table-seat-key.bin` — minted `0600` on first boot and reread
//!    afterwards, so a deployment that already keeps durable sessions keeps durable seat links too.
//! 3. Process-random — the pre-existing behaviour, and still the default for a deployment with no
//!    session dir. A restart then invalidates every outstanding link, and the table is REFUSED
//!    rather than silently unlocked (fail-closed).
//!
//! ## The clock
//!
//! [`TableRegistry`] is the minted tables' own record: who sat, when either seat last acted, and
//! how the table ENDED. It is what turns an abandoned match from a permanent zombie into a
//! resolved one — see [`reap`].
//!
//! **Read this before writing copy about a forfeit.** A forfeit is a HOST attestation and nothing
//! more. Neither game's deployed teeth admit a "the clock ran out" turn: automatafl's `winner`
//! register is write-once *under `resolve`* and tug's win register is threshold-gated
//! (`winner==p ⇒ charm_p ≥ 11 ∨ guilds_p ≥ 4`), so there is no method either executor would accept
//! for "B stopped showing up, give it to A" — and inventing one is Lean work, not Rust work. So a
//! forfeit here lands **no receipt and no executor turn**: it is the lobby that minted the table
//! recording how the table ended, and every surface that shows it says so in those words.

use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant};

use dreggnet_offerings::{DreggIdentity, SessionId};

use crate::{CatalogState, hex_bytes, web_identity};

// ─────────────────────────────────────────────────────────────────────────────────────────
// THE SERVER KEY
// ─────────────────────────────────────────────────────────────────────────────────────────

/// The key every per-seat label is derived under. Never served, never logged. Resolution order and
/// its consequences are documented on the module.
pub fn seat_key() -> &'static [u8; 32] {
    static KEY_CELL: OnceLock<[u8; 32]> = OnceLock::new();
    KEY_CELL.get_or_init(resolve_seat_key)
}

fn resolve_seat_key() -> [u8; 32] {
    resolve_process_key(
        "DREGGNET_WEB_SEAT_KEY",
        "table-seat-key.bin",
        "outstanding seat links",
    )
}

/// **Resolve a server-only 32-byte key**, in this order: a hex pin in `env_var`; a file named
/// `file_name` under `DREGGNET_WEB_SESSION_DIR` (read if present, minted + persisted `0600` if
/// not); otherwise fresh per process. `what` names — for the one warning line — the credentials
/// that will not survive a restart if persisting fails.
///
/// Extracted from [`resolve_seat_key`] so [`crate::seed_identity`]'s claimed-identity mac key gets
/// the same ops story rather than a second, subtly different resolution: the same env/file/ephemeral
/// ladder, the same non-fatal write failure, and the same fail-CLOSED consequence (a key that
/// changed makes old credentials stop verifying — it never makes a forged one verify).
pub(crate) fn resolve_process_key(env_var: &str, file_name: &str, what: &str) -> [u8; 32] {
    if let Some(pinned) = std::env::var(env_var)
        .ok()
        .as_deref()
        .and_then(decode_key_hex)
    {
        return pinned;
    }
    if let Some(dir) = std::env::var("DREGGNET_WEB_SESSION_DIR")
        .ok()
        .filter(|d| !d.is_empty())
    {
        let path = std::path::Path::new(&dir).join(file_name);
        if let Some(stored) = read_key_file(&path) {
            return stored;
        }
        let fresh = random_key();
        // A write failure is NOT fatal: the process still has a good key, it just will not survive
        // the next restart. Fail-closed either way (an old link stops verifying), never fail-open.
        if write_key_file(&path, &fresh).is_err() {
            tracing::warn!(
                path = %path.display(),
                what = %what,
                "could not persist a server key — these will not survive a restart"
            );
        }
        return fresh;
    }
    random_key()
}

fn random_key() -> [u8; 32] {
    let mut key = [0_u8; 32];
    getrandom::fill(&mut key).expect("operating-system RNG must mint the table seat key");
    key
}

fn decode_key_hex(raw: &str) -> Option<[u8; 32]> {
    let raw = raw.trim();
    if raw.len() != 64 {
        return None;
    }
    let mut out = [0_u8; 32];
    for (i, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(raw.get(i * 2..i * 2 + 2)?, 16).ok()?;
    }
    Some(out)
}

fn read_key_file(path: &std::path::Path) -> Option<[u8; 32]> {
    let bytes = std::fs::read(path).ok()?;
    <[u8; 32]>::try_from(bytes.as_slice()).ok()
}

fn write_key_file(path: &std::path::Path, key: &[u8; 32]) -> std::io::Result<()> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    // Owner-only from the moment it exists — the file IS every outstanding seat secret.
    #[cfg(unix)]
    {
        use std::io::Write as _;
        use std::os::unix::fs::OpenOptionsExt as _;
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(path)?;
        file.write_all(key)?;
        return Ok(());
    }
    #[cfg(not(unix))]
    {
        std::fs::write(path, key)
    }
}

// ─────────────────────────────────────────────────────────────────────────────────────────
// THE LOCK
// ─────────────────────────────────────────────────────────────────────────────────────────

/// A seat of a two-player table, as it appears in a link (`a` / `b`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SeatSlot {
    /// The link the table's opener keeps (`?seat=a`).
    A,
    /// The link the opener sends (`?seat=b`) — the invite.
    B,
}

impl SeatSlot {
    /// The lowercase letter the link and the label carry.
    pub fn letter(self) -> char {
        match self {
            SeatSlot::A => 'a',
            SeatSlot::B => 'b',
        }
    }

    /// The uppercase label the pages print.
    pub fn label(self) -> &'static str {
        match self {
            SeatSlot::A => "A",
            SeatSlot::B => "B",
        }
    }

    /// The other seat.
    pub fn other(self) -> SeatSlot {
        match self {
            SeatSlot::A => SeatSlot::B,
            SeatSlot::B => SeatSlot::A,
        }
    }

    /// The seat a link's `?seat=` names (case-insensitive), if it names one.
    pub fn parse(raw: &str) -> Option<SeatSlot> {
        match raw.trim().to_ascii_lowercase().as_str() {
            "a" => Some(SeatSlot::A),
            "b" => Some(SeatSlot::B),
            _ => None,
        }
    }

    /// Both seats, in link order.
    pub const BOTH: [SeatSlot; 2] = [SeatSlot::A, SeatSlot::B];
}

/// **A game's table lock** — the three prefixes plus the front-door route. One `static` per
/// seat-locked game; [`ALL`] enumerates them and is what the act path and the reaper iterate.
#[derive(Clone, Copy, Debug)]
pub struct TableLock {
    /// The catalog key this lock guards (`automatafl`, `tug`).
    pub key: &'static str,
    /// The prefix a MINTED table id wears. An id without it is an ad-hoc table on the catalog's
    /// open seat-claiming rules; [`TableLock::is_locked_table`] keys off exactly this.
    pub table_prefix: &'static str,
    /// The prefix a seat label wears.
    pub seat_prefix: &'static str,
    /// The front door (`/automatafl`, `/tug`) — the base of every seat and watch link.
    pub route: &'static str,
    /// The game's display name, for the refusal copy.
    pub game: &'static str,
}

/// The automatafl lock — the original, unchanged in shape or derivation.
pub const AUTOMATAFL: TableLock = TableLock {
    key: "automatafl",
    table_prefix: "af1-",
    seat_prefix: "afs1-",
    route: "/automatafl",
    game: "Automatafl",
};

/// The multiway-tug lock — the same discipline, new prefixes.
pub const TUG: TableLock = TableLock {
    key: "tug",
    table_prefix: "tug1-",
    seat_prefix: "tugs1-",
    route: "/tug",
    game: "Multiway-Tug",
};

/// Every seat-locked game. The act-path gate and the reaper iterate THIS, so a new game gets the
/// lock by being added here and nowhere else.
pub const ALL: [TableLock; 2] = [AUTOMATAFL, TUG];

/// The lock for a catalog key, if that key is seat-lockable.
pub fn lock_for_key(key: &str) -> Option<TableLock> {
    ALL.into_iter().find(|lock| lock.key == key)
}

/// The lock a table id's prefix names, if any.
pub fn lock_of_table(id: &str) -> Option<TableLock> {
    ALL.into_iter().find(|lock| lock.is_locked_table(id))
}

impl TableLock {
    /// **Mint a seat-locked table id** — the prefix plus 96 bits of OS randomness.
    pub fn mint_table_id(&self) -> String {
        let mut bytes = [0_u8; 12];
        getrandom::fill(&mut bytes).expect("operating-system RNG must mint the table id");
        format!("{}{}", self.table_prefix, hex_bytes(&bytes))
    }

    /// **The seat's secret label** — `<seat-prefix>{a|b}-` + 128 bits of `blake3_keyed(K, id‖seat)`.
    /// This IS the browser identity for that seat.
    pub fn seat_label(&self, id: &str, seat: SeatSlot) -> String {
        let mut input = Vec::with_capacity(id.len() + 1);
        input.extend_from_slice(id.as_bytes());
        input.push(seat.letter() as u8);
        let tag = blake3::keyed_hash(seat_key(), &input);
        format!(
            "{}{}-{}",
            self.seat_prefix,
            seat.letter(),
            hex_bytes(&tag.as_bytes()[..16])
        )
    }

    /// The substrate actor a seat's holder acts as — what [`crate::web_identity`] derives from the
    /// seat label, i.e. what the offering sees as the mover.
    pub fn seat_identity(&self, id: &str, seat: SeatSlot) -> DreggIdentity {
        web_identity(&self.seat_label(id, seat))
    }

    /// The seat `label` holds at table `id`, if any. Constant-shape: both seats are always derived
    /// and compared, so a mismatch does not leak which seat was closer.
    pub fn seat_of_label(&self, id: &str, label: &str) -> Option<SeatSlot> {
        let a = self.seat_label(id, SeatSlot::A);
        let b = self.seat_label(id, SeatSlot::B);
        let is_a = constant_time_eq(a.as_bytes(), label.as_bytes());
        let is_b = constant_time_eq(b.as_bytes(), label.as_bytes());
        match (is_a, is_b) {
            (true, _) => Some(SeatSlot::A),
            (_, true) => Some(SeatSlot::B),
            _ => None,
        }
    }

    /// Whether `id` names a table minted under THIS lock.
    pub fn is_locked_table(&self, id: &str) -> bool {
        id.starts_with(self.table_prefix)
    }

    /// The seat link for `seat` at `id` (relative — the deployment's own origin).
    pub fn seat_link(&self, id: &str, seat: SeatSlot) -> String {
        format!(
            "{route}/table/{id}?seat={letter}&key={label}",
            route = self.route,
            id = id,
            letter = seat.letter(),
            label = self.seat_label(id, seat),
        )
    }

    /// The spectator link for `id`.
    pub fn watch_link(&self, id: &str) -> String {
        format!("{}/watch/{}", self.route, id)
    }

    /// The ordinary play surface for `id` (where a seat link lands the browser).
    pub fn table_link(&self, id: &str) -> String {
        format!("/offerings/{}/session/{}", self.key, id)
    }
}

fn constant_time_eq(left: &[u8], right: &[u8]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let mut diff = 0_u8;
    for (l, r) in left.iter().zip(right.iter()) {
        diff |= l ^ r;
    }
    diff == 0
}

// ─────────────────────────────────────────────────────────────────────────────────────────
// THE GATE
// ─────────────────────────────────────────────────────────────────────────────────────────

/// **The gate the generic act route calls, for EVERY seat-locked game.** On a minted table only
/// the two minted seat labels may act — so a stranger who learns the id can neither race in and
/// claim a seat nor reach the per-viewer private disclosure by asserting the other seat's label —
/// and a table this lobby has already RESOLVED (forfeit / resignation) takes no further acts.
/// `Ok(())` on every other route/key, byte-identically to before the lock existed.
///
/// Returns the refusal text to render when the act is not allowed.
pub fn enforce(key: &str, id: &str, actor_label: &str) -> Result<(), String> {
    let Some(lock) = lock_for_key(key).filter(|lock| lock.is_locked_table(id)) else {
        return Ok(());
    };
    if let Some(resolution) = registry().resolution(id) {
        return Err(resolution.refusal());
    }
    if lock.seat_of_label(id, actor_label).is_none() {
        return Err(
            // "seat-locked table" is pinned by `tests/tug_table.rs` and `tests/automatafl_table.rs`
            // and stays verbatim; "nothing committed" was the only word here a player did not own.
            "this is a seat-locked table — open your seat link to sit down (nothing was recorded)"
                .to_string(),
        );
    }
    Ok(())
}

/// **Refuse a whole route on a seat-locked table.** The signed / Telegram Mini App / Discord
/// Activity act routes carry a PUBKEY-DERIVED custodial actor, which can never be one of the two
/// unguessable browser labels a minted table binds its seats to — so admitting one would let a
/// custodial user take a seat the invite link was supposed to hold. Those routes call THIS: it is
/// [`enforce`] with a label no lock can ever mint, so it is `Ok(())` on every ad-hoc id and every
/// non-lockable key, and refuses exactly the minted tables.
pub fn refuse_non_seat_route(key: &str, id: &str) -> Result<(), String> {
    // The empty label matches no seat under any lock (every seat label carries a prefix and 32 hex
    // chars), so this refuses iff `id` names a minted table of `key`.
    debug_assert!(
        ALL.into_iter()
            .all(|lock| lock.seat_of_label(id, "").is_none()),
        "the empty label must never open a seat"
    );
    enforce(key, id, "")
}

/// **Note that a real turn LANDED on a seat-locked table.** The clock measures PROGRESS, not
/// clicking: a refused press moves nothing, so it must not buy the presser another window. Called
/// from the act route after the outcome, never from the gate. A no-op for every other key/id.
pub fn record_landed_act(key: &str, id: &str, actor_label: &str) {
    let Some(lock) = lock_for_key(key).filter(|lock| lock.is_locked_table(id)) else {
        return;
    };
    if let Some(seat) = lock.seat_of_label(id, actor_label) {
        registry().record_act(id, seat, Instant::now());
    }
}

// ─────────────────────────────────────────────────────────────────────────────────────────
// THE REGISTRY — the minted tables' own record, and their clock
// ─────────────────────────────────────────────────────────────────────────────────────────

/// Why a table stopped taking moves.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cause {
    /// A seat's per-turn clock expired with the move still owed.
    Clock,
    /// A seat resigned on purpose.
    Resigned,
}

/// **How a minted table ENDED**, as this lobby records it. Not a proven result and never described
/// as one: no executor turn backs a forfeit (see the module docs).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Resolution {
    /// The seats that failed to act / resigned. Two entries = both sides walked away.
    pub forfeited: Vec<SeatSlot>,
    /// Why.
    pub cause: Cause,
    /// Whether anybody had acted at all when the clock ran out.
    pub started: bool,
}

impl Resolution {
    /// The seat this lobby records as winning: the other one, when exactly ONE side walked away.
    /// `None` for a double abandonment and for a table nobody ever sat at — both of which record
    /// an empty or two-element `forfeited`, so the arity is the whole rule.
    pub fn winner(&self) -> Option<SeatSlot> {
        match self.forfeited.as_slice() {
            [only] => Some(only.other()),
            _ => None,
        }
    }

    /// One line, for a page or a refusal.
    pub fn headline(&self) -> String {
        let verb = match self.cause {
            Cause::Clock => "let the clock run out",
            Cause::Resigned => "resigned",
        };
        if !self.started {
            return "this table expired before either seat made a move — nothing was played"
                .to_string();
        }
        match (self.winner(), self.forfeited.as_slice()) {
            (Some(winner), [loser]) => format!(
                "seat {loser} {verb} — seat {winner} takes the table by forfeit",
                loser = loser.label(),
                winner = winner.label(),
            ),
            _ => format!("both seats {verb} — the table is abandoned, with no winner"),
        }
    }

    /// The refusal an act on a resolved table gets.
    pub fn refusal(&self) -> String {
        format!(
            "this table is over — {}. That is the lobby noting somebody stopped playing: no move \
             was made and there is no receipt for it, so it is not a proven win.",
            self.headline()
        )
    }
}

/// One minted table's record.
#[derive(Clone, Debug)]
pub struct TableRecord {
    /// The lock (and therefore the game) this table belongs to.
    pub lock: TableLock,
    /// When the table was minted.
    pub opened: Instant,
    /// The last act by a seated player, and which seat made it.
    pub last_act: Option<(SeatSlot, Instant)>,
    /// How it ended, once it has.
    pub resolution: Option<Resolution>,
}

impl TableRecord {
    /// Whether anybody has actually made a move here.
    pub fn started(&self) -> bool {
        self.last_act.is_some()
    }

    /// How long the table has been waiting on the move it is owed.
    fn idle_for(&self, now: Instant) -> Duration {
        now.saturating_duration_since(self.last_act.map(|(_, at)| at).unwrap_or(self.opened))
    }
}

/// The minted tables of this process.
#[derive(Default)]
pub struct TableRegistry {
    tables: Mutex<HashMap<String, TableRecord>>,
}

/// The process's table registry.
pub fn registry() -> &'static TableRegistry {
    static CELL: OnceLock<TableRegistry> = OnceLock::new();
    CELL.get_or_init(TableRegistry::default)
}

impl TableRegistry {
    /// Record a freshly minted table.
    pub fn opened(&self, lock: TableLock, id: &str, now: Instant) {
        let mut tables = self.lock();
        tables.insert(
            id.to_string(),
            TableRecord {
                lock,
                opened: now,
                last_act: None,
                resolution: None,
            },
        );
    }

    /// Note that `seat` acted. Ignored on a table this process did not mint (a link left over from
    /// before a restart) and on one already resolved.
    pub fn record_act(&self, id: &str, seat: SeatSlot, now: Instant) {
        let mut tables = self.lock();
        if let Some(record) = tables.get_mut(id) {
            if record.resolution.is_none() {
                record.last_act = Some((seat, now));
            }
        }
    }

    /// How the table ended, if it has.
    pub fn resolution(&self, id: &str) -> Option<Resolution> {
        self.lock().get(id).and_then(|r| r.resolution.clone())
    }

    /// The whole record.
    pub fn record(&self, id: &str) -> Option<TableRecord> {
        self.lock().get(id).cloned()
    }

    /// Write a resolution, once. Returns the resolution now in force (an already-resolved table
    /// keeps its FIRST resolution — a clock cannot overwrite a resignation).
    pub fn resolve(&self, id: &str, resolution: Resolution) -> Option<Resolution> {
        let mut tables = self.lock();
        let record = tables.get_mut(id)?;
        if record.resolution.is_none() {
            record.resolution = Some(resolution);
        }
        record.resolution.clone()
    }

    /// The live (unresolved) tables whose owed move is older than `limit`, oldest first.
    fn stalled(&self, limit: Duration, now: Instant) -> Vec<(String, TableRecord)> {
        let tables = self.lock();
        let mut out: Vec<(String, TableRecord)> = tables
            .iter()
            .filter(|(_, r)| r.resolution.is_none() && r.idle_for(now) >= limit)
            .map(|(id, r)| (id.clone(), r.clone()))
            .collect();
        out.sort_by_key(|(_, r)| r.idle_for(now));
        out.reverse();
        out
    }

    /// How many tables this process has minted (live + resolved).
    pub fn len(&self) -> usize {
        self.lock().len()
    }

    /// Whether the registry holds no tables.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, HashMap<String, TableRecord>> {
        // A panicking holder cannot corrupt a plain map of records; keep serving rather than
        // poisoning every table in the process.
        self.tables.lock().unwrap_or_else(|e| e.into_inner())
    }
}

// ─────────────────────────────────────────────────────────────────────────────────────────
// THE CLOCK
// ─────────────────────────────────────────────────────────────────────────────────────────

/// **The per-turn deadline.** A seat that owes a move and does not make it inside this window
/// forfeits. Ten minutes is chosen for a turn-based board played over a link between two people
/// who are not necessarily in the same room: long enough that thinking, a phone call, or a bad
/// train tunnel does not cost you the game, short enough that a table you were invited to at lunch
/// is resolved by dinner. `DREGGNET_WEB_TABLE_TURN_SECS` overrides it.
pub fn turn_limit() -> Duration {
    static CELL: OnceLock<Duration> = OnceLock::new();
    *CELL.get_or_init(|| env_secs("DREGGNET_WEB_TABLE_TURN_SECS", 600))
}

/// **The deadline for a table nobody ever sat at.** The invite was never opened, or both sides
/// wandered off before the first move. Nothing was played, so nobody forfeits — the table is
/// recorded as expired. `DREGGNET_WEB_TABLE_OPEN_SECS` overrides it.
pub fn open_limit() -> Duration {
    static CELL: OnceLock<Duration> = OnceLock::new();
    *CELL.get_or_init(|| env_secs("DREGGNET_WEB_TABLE_OPEN_SECS", 3600))
}

fn env_secs(name: &str, default: u64) -> Duration {
    let secs = std::env::var(name)
        .ok()
        .and_then(|raw| raw.trim().parse::<u64>().ok())
        .filter(|secs| *secs > 0)
        .unwrap_or(default);
    Duration::from_secs(secs)
}

/// **Resolve `id` if its clock has expired.** Returns the resolution now in force (`None` while
/// the table is still live). Idempotent: a table already resolved keeps its first resolution.
///
/// The delinquency oracle is [`dreggnet_offerings::Offering::actions_for`], asked ONCE PER SEAT as
/// that seat's own derived identity: a seat that is still offered an enabled affordance is a seat
/// that owes a move. That is exactly right for both shapes —
///
/// * tug alternates, so only the seat to move is offered anything;
/// * automatafl is simultaneous, so in `Reveal` the seat that already opened is offered nothing
///   and the seat that never opened is offered the reveal. **That** is the wound this closes: a
///   table stuck in `Reveal` because one seat walked away now ends with that seat forfeiting.
///
/// If BOTH seats still owe a move, both walked away and the table is recorded as a double
/// abandonment with no winner. If NEITHER does the match is already over and nothing is recorded.
pub fn reap_table(state: &CatalogState, id: &str, now: Instant) -> Option<Resolution> {
    let record = registry().record(id)?;
    if let Some(resolution) = record.resolution {
        return Some(resolution);
    }
    let lock = record.lock;
    let limit = if record.started() {
        turn_limit()
    } else {
        open_limit()
    };
    if record.idle_for(now) < limit {
        return None;
    }
    if !record.started() {
        return registry().resolve(
            id,
            Resolution {
                forfeited: Vec::new(),
                cause: Cause::Clock,
                started: false,
            },
        );
    }
    let sid = SessionId::new(id.to_string());
    let owing: Vec<SeatSlot> = SeatSlot::BOTH
        .into_iter()
        .filter(|seat| owes_a_move(state, &lock, &sid, *seat))
        .collect();
    if owing.is_empty() {
        // Nothing is owed — the match reached its own terminal state. Not a forfeit.
        return None;
    }
    registry().resolve(
        id,
        Resolution {
            forfeited: owing,
            cause: Cause::Clock,
            started: true,
        },
    )
}

/// **Resign `seat` at `id`.** A player may always end their own table; this is the only resolution
/// a *user* can cause, and it can only ever cost the person who fires it.
///
/// `started` is TRUE even when no turn has landed. It marks "somebody was here and made a
/// decision", which is exactly what a resignation is — a seat that opens a table and gives it up
/// before its first move has still given it up, and the other seat takes it. Only the CLOCK's
/// nobody-ever-showed-up case records `started: false`.
pub fn resign(id: &str, seat: SeatSlot) -> Option<Resolution> {
    registry().resolve(
        id,
        Resolution {
            forfeited: vec![seat],
            cause: Cause::Resigned,
            started: true,
        },
    )
}

/// Whether `seat` is still offered something to do at this table — the delinquency oracle.
fn owes_a_move(state: &CatalogState, lock: &TableLock, id: &SessionId, seat: SeatSlot) -> bool {
    let viewer = lock.seat_identity(&id.0, seat);
    let key = lock.key.to_string();
    let id = id.clone();
    let probe = viewer.clone();
    state
        .run_offering(lock.key, &viewer, move |host| {
            host.actions_for(&key, &id, &probe)
        })
        .is_some_and(|actions| actions.iter().any(|action| action.enabled))
}

/// **Sweep every minted table** whose clock has expired, resolving each. This is the no-traffic
/// half of the clock: the per-request path below reaps the table a visitor is looking at, and the
/// server binary's periodic sweeper calls THIS so a table nobody is watching still resolves.
/// Returns the ids it resolved.
pub fn reap_all(state: &CatalogState) -> Vec<String> {
    let now = Instant::now();
    // Take the widest window first so one pass covers never-started and stalled tables alike; each
    // candidate re-checks its OWN limit inside `reap_table`.
    let limit = turn_limit().min(open_limit());
    registry()
        .stalled(limit, now)
        .into_iter()
        .filter(|(id, _)| reap_table(state, id, now).is_some())
        .map(|(id, _)| id)
        .collect()
}

/// **The per-request reap.** Every route that touches a seat-locked table calls this first, so the
/// resolution a visitor sees is current as of their own click. Cheap: it costs one map lookup
/// unless the table is actually past its deadline.
pub fn touch(state: &CatalogState, id: &str) -> Option<Resolution> {
    reap_table(state, id, Instant::now())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_seat_label_is_not_derivable_from_the_other_seat_on_either_game() {
        for lock in ALL {
            let id = lock.mint_table_id();
            let a = lock.seat_label(&id, SeatSlot::A);
            let b = lock.seat_label(&id, SeatSlot::B);
            assert_ne!(a, b, "the two seats carry different labels");
            assert_eq!(lock.seat_of_label(&id, &a), Some(SeatSlot::A));
            assert_eq!(lock.seat_of_label(&id, &b), Some(SeatSlot::B));
            // A label minted for ANOTHER table of the same game does not open this one.
            let other = lock.mint_table_id();
            assert_eq!(
                lock.seat_of_label(&id, &lock.seat_label(&other, SeatSlot::A)),
                None
            );
            // And an asserted plain label opens nothing.
            assert_eq!(lock.seat_of_label(&id, "alice"), None);
        }
    }

    #[test]
    fn a_seat_label_from_one_game_does_not_open_the_other() {
        // Both games derive under the SAME server key; the table prefix and the seat prefix are
        // what keep the two namespaces apart, so check that they actually do.
        let tug_id = TUG.mint_table_id();
        let af_id = AUTOMATAFL.mint_table_id();
        assert_eq!(lock_of_table(&tug_id).map(|l| l.key), Some("tug"));
        assert_eq!(lock_of_table(&af_id).map(|l| l.key), Some("automatafl"));
        for seat in SeatSlot::BOTH {
            let tug_label = TUG.seat_label(&tug_id, seat);
            assert_eq!(AUTOMATAFL.seat_of_label(&tug_id, &tug_label), None);
            assert_eq!(AUTOMATAFL.seat_of_label(&af_id, &tug_label), None);
        }
    }

    #[test]
    fn the_gate_only_binds_minted_tables_of_the_matching_key() {
        let tug_id = TUG.mint_table_id();
        assert!(enforce("tug", &tug_id, "alice").is_err());
        assert!(enforce("tug", &tug_id, &TUG.seat_label(&tug_id, SeatSlot::B)).is_ok());
        // The OTHER game's gate does not bind a tug table, and an ad-hoc id keeps the old open
        // behaviour on both.
        assert!(enforce("automatafl", &tug_id, "alice").is_ok());
        assert!(enforce("tug", "tug-hand-rolled", "alice").is_ok());
        assert!(enforce("dungeon", &tug_id, "alice").is_ok());
    }

    #[test]
    fn a_seat_link_round_trips() {
        let id = TUG.mint_table_id();
        let link = TUG.seat_link(&id, SeatSlot::B);
        assert!(link.starts_with(&format!("/tug/table/{id}?seat=b&key=tugs1-b-")));
        assert_eq!(TUG.watch_link(&id), format!("/tug/watch/{id}"));
        assert_eq!(TUG.table_link(&id), format!("/offerings/tug/session/{id}"));
    }

    #[test]
    fn a_resolved_table_refuses_every_further_act_including_a_seated_one() {
        let id = TUG.mint_table_id();
        registry().opened(TUG, &id, Instant::now());
        let seat_b = TUG.seat_label(&id, SeatSlot::B);
        assert!(
            enforce("tug", &id, &seat_b).is_ok(),
            "live table takes acts"
        );
        let resolution = resign(&id, SeatSlot::A).expect("the table is registered");
        assert_eq!(resolution.winner(), Some(SeatSlot::B));
        let refused = enforce("tug", &id, &seat_b).expect_err("a resolved table takes no acts");
        assert!(refused.contains("forfeit"), "{refused}");
        assert!(
            refused.contains("not a proven win"),
            "the refusal must not imply the executor decided this: {refused}"
        );
    }

    #[test]
    fn a_resolution_is_write_once() {
        let id = AUTOMATAFL.mint_table_id();
        registry().opened(AUTOMATAFL, &id, Instant::now());
        registry().record_act(&id, SeatSlot::A, Instant::now());
        let first = resign(&id, SeatSlot::A).expect("registered");
        let second = registry()
            .resolve(
                &id,
                Resolution {
                    forfeited: vec![SeatSlot::B],
                    cause: Cause::Clock,
                    started: true,
                },
            )
            .expect("registered");
        assert_eq!(first, second, "a later clock cannot rewrite a resignation");
        assert_eq!(second.winner(), Some(SeatSlot::B));
    }

    #[test]
    fn an_unstarted_table_expires_without_blaming_anybody() {
        let id = TUG.mint_table_id();
        registry().opened(TUG, &id, Instant::now());
        let record = registry().record(&id).expect("registered");
        assert!(!record.started());
        let resolution = registry()
            .resolve(
                &id,
                Resolution {
                    forfeited: Vec::new(),
                    cause: Cause::Clock,
                    started: false,
                },
            )
            .expect("registered");
        assert_eq!(resolution.winner(), None);
        assert!(resolution.headline().contains("nothing was played"));
    }

    #[test]
    fn a_double_abandonment_names_no_winner() {
        let resolution = Resolution {
            forfeited: vec![SeatSlot::A, SeatSlot::B],
            cause: Cause::Clock,
            started: true,
        };
        assert_eq!(resolution.winner(), None);
        assert!(resolution.headline().contains("no winner"));
    }

    #[test]
    fn the_key_hex_override_is_exact_length_hex_only() {
        assert!(decode_key_hex("nope").is_none());
        assert!(decode_key_hex(&"z".repeat(64)).is_none());
        assert_eq!(decode_key_hex(&"00".repeat(32)), Some([0_u8; 32]));
        assert_eq!(
            decode_key_hex(&format!(" {} ", "ff".repeat(32))),
            Some([0xff_u8; 32])
        );
    }
}
