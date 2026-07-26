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
//! resolved one — see [`reap_table`].
//!
//! **Across a restart the registry is REBUILT, not lost.** Each minted table's whole record — its
//! lock, when it was minted, the last landed act, and its ending once it has one — is written to
//! `<DREGGNET_WEB_SESSION_DIR>/tables/` at the mint and at every landed act, stamped in WALL time,
//! and adopted back the first time this process is asked about that table (or by the sweeper's
//! once-per-process walk of the durable dir). So the turn clock keeps running across a deploy, and
//! a resignation still lands on a table some previous process minted. The declaration and the
//! argument for it are on [`TableRegistry`]'s own fields; the rule they answer to is
//! `docs/reference/RESTART-SEMANTICS.md`.
//!
//! **Read this before writing copy about a forfeit.** A forfeit is a HOST attestation and nothing
//! more. Neither game's deployed teeth admit a "the clock ran out" turn: automatafl's `winner`
//! register is write-once *under `resolve`* and tug's win register is threshold-gated
//! (`winner==p ⇒ charm_p ≥ 11 ∨ guilds_p ≥ 4`), so there is no method either executor would accept
//! for "B stopped showing up, give it to A" — and inventing one is Lean work, not Rust work. So a
//! forfeit here lands **no receipt and no executor turn**: it is the lobby that minted the table
//! recording how the table ended, and every surface that shows it says so in those words.

use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

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
    /// What the two seat links mean at this table, in one sentence for the lobby.
    pub seat_note: &'static str,
    /// **What a spectator can and cannot see here**, in one sentence.
    ///
    /// ⚑ It lives on the LOCK rather than on [`crate::table_door::TableDoor`] because it is now
    /// printed in three places, and a watcher must be promised the same thing in all of them: the
    /// lobby that hands the link over, the spectator page itself, and — since the link became
    /// reachable from a live match — the seated table
    /// ([`crate::table_door::spectator_invite`]). Two copies of this sentence is where the
    /// over-promise would live.
    pub spectator_note: &'static str,
}

/// The automatafl lock — the original, unchanged in shape or derivation.
pub const AUTOMATAFL: TableLock = TableLock {
    key: "automatafl",
    table_prefix: "af1-",
    seat_prefix: "afs1-",
    route: "/automatafl",
    game: "Automatafl",
    seat_note: "(Which side of the board you get, seat A or seat B, is settled by the game when \
                you make your first move; the link decides only that the table is <em>yours</em>.)",
    spectator_note: "Watchers see the live board with both sealed moves hidden, and cannot touch \
                     anything on it.",
};

/// The multiway-tug lock — the same discipline, new prefixes.
pub const TUG: TableLock = TableLock {
    key: "tug",
    table_prefix: "tug1-",
    seat_prefix: "tugs1-",
    route: "/tug",
    game: "Multiway-Tug",
    seat_note: "(Which side you get, seat A or seat B, is settled by the game when you make your \
                first move; the link decides only that the table is <em>yours</em>.)",
    spectator_note: "Watchers see the lanes and the score, and both hands only as a card count and \
                     a fingerprint of the hand, never a card. They cannot touch anything on the \
                     table.",
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
    enforce_in(registry(), key, id, actor_label)
}

/// [`enforce`] against an explicit registry. The process gate is `enforce_in(registry(), …)`; the
/// parameter exists so the restart tests can drive the REAL gate against a registry that has never
/// met the table, which is what a restart is, without touching process-global env.
fn enforce_in(
    tables: &TableRegistry,
    key: &str,
    id: &str,
    actor_label: &str,
) -> Result<(), String> {
    let Some(lock) = lock_for_key(key).filter(|lock| lock.is_locked_table(id)) else {
        return Ok(());
    };
    if let Some(resolution) = tables.resolution(id) {
        return Err(resolution.refusal());
    }
    if lock.seat_of_label(id, actor_label).is_none() {
        return Err(
            // "seat-locked table" is pinned by `tests/tug_table.rs` and `tests/automatafl_table.rs`
            // and stays verbatim; "nothing committed" was the only word here a player did not own.
            "this is a seat-locked table: open your seat link to sit down (nothing was recorded)"
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
    /// ⚑ **The match PLAYED ITSELF OUT** — neither seat is offered an enabled affordance any more,
    /// so by the offering's own account there is no move left to make.
    ///
    /// This is the case the reaper used to record as *nothing at all*: [`reap_table`] saw an empty
    /// `owing` list, said "the match reached its own terminal state. Not a forfeit." and returned
    /// `None` — so a genuinely COMPLETED automatafl or tug match was never written down anywhere,
    /// which is precisely why `/you` had no finished-match history to show.
    ///
    /// It is a READ of the offering, not a verdict of this lobby's: the oracle is
    /// [`dreggnet_offerings::Offering::actions_for`] asked as each seat, and this variant therefore
    /// says only "there is nothing left to play". It names **no winner** — the board itself is the
    /// result, and only the executor's own registers decide it (see the module docs).
    Concluded,
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
    ///
    /// Also `None` for [`Cause::Concluded`], and that is load-bearing rather than incidental: a
    /// match that played itself out has a result, but this lobby is not the thing that knows it.
    pub fn winner(&self) -> Option<SeatSlot> {
        if self.cause == Cause::Concluded {
            return None;
        }
        match self.forfeited.as_slice() {
            [only] => Some(only.other()),
            _ => None,
        }
    }

    /// Whether the match ended by being PLAYED to its end rather than by somebody walking away.
    pub fn concluded(&self) -> bool {
        self.cause == Cause::Concluded
    }

    /// One line, for a page or a refusal.
    pub fn headline(&self) -> String {
        if self.cause == Cause::Concluded {
            return "this table played itself out; neither seat is owed a move, and the final \
                    board is the result"
                .to_string();
        }
        let verb = match self.cause {
            Cause::Clock => "let the clock run out",
            Cause::Resigned => "resigned",
            // Handled above; the branch exists so a new cause cannot silently borrow a verb.
            Cause::Concluded => "played it out",
        };
        if !self.started {
            return "this table expired before either seat made a move; nothing was played"
                .to_string();
        }
        match (self.winner(), self.forfeited.as_slice()) {
            (Some(winner), [loser]) => format!(
                "seat {loser} {verb}; seat {winner} takes the table by forfeit",
                loser = loser.label(),
                winner = winner.label(),
            ),
            _ => format!("both seats {verb}; the table is abandoned, with no winner"),
        }
    }

    /// The refusal an act on a resolved table gets.
    pub fn refusal(&self) -> String {
        if self.cause == Cause::Concluded {
            // A concluded match is not somebody walking away, so it must not be described as one.
            // What it IS: the offering refusing every further move, which is where the result lives.
            return format!(
                "this table is over: {}. The offering itself offers neither seat a move, so \
                 nothing further can land here. Replay the finished match to see how it went.",
                self.headline()
            );
        }
        format!(
            "this table is over: {}. That is the lobby noting somebody stopped playing: no move \
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
    /// The WALL-clock twin of [`opened`](TableRecord::opened) — seconds since the UNIX epoch. The
    /// live clock is always the `Instant`; this exists only so the record can be written down and
    /// wound back after a restart, which is the one thing an `Instant` cannot survive.
    opened_wall: u64,
    /// The wall-clock twin of [`last_act`](TableRecord::last_act)'s `Instant`.
    ///
    /// Private, and written only by [`TableRecord::note_act`], so the stamp the reaper compares and
    /// the stamp a restart reads cannot come to disagree about when the last move landed.
    last_act_wall: Option<u64>,
}

impl TableRecord {
    /// A freshly minted table, stamped on BOTH clocks at once.
    fn minted(lock: TableLock, now: Instant, now_wall: u64) -> TableRecord {
        TableRecord {
            lock,
            opened: now,
            last_act: None,
            resolution: None,
            opened_wall: now_wall,
            last_act_wall: None,
        }
    }

    /// Note an act on both clocks at once — the ONLY writer of `last_act`.
    fn note_act(&mut self, seat: SeatSlot, now: Instant, now_wall: u64) {
        self.last_act = Some((seat, now));
        self.last_act_wall = Some(now_wall);
    }

    /// Whether anybody has actually made a move here.
    pub fn started(&self) -> bool {
        self.last_act.is_some()
    }

    /// How long the table has been waiting on the move it is owed.
    fn idle_for(&self, now: Instant) -> Duration {
        now.saturating_duration_since(self.last_act.map(|(_, at)| at).unwrap_or(self.opened))
    }
}

// ─────────────────────────────────────────────────────────────────────────────────────────
// THE DURABLE RECORD — the whole table, kept across a restart, on a clock that survives one
// ─────────────────────────────────────────────────────────────────────────────────────────

/// ⚑ **Where a table's record is persisted.** `<DREGGNET_WEB_SESSION_DIR>/tables/`, the same root
/// the durable session move-logs live under, so a deployment that already keeps games keeps their
/// tables too. `None` (env unset) → the registry is process-local exactly as it always was.
///
/// **This used to hold only the ENDING**, on an argument that deserves restating because it is half
/// right: the rest of a [`TableRecord`] is a live clock (`Instant`s), which is meaningless across a
/// restart and must not be faked into existence — a resurrected `opened: Instant::now()` on an
/// UNRESOLVED table would hand the reaper a table it thinks nobody has ever moved at, and it would
/// forfeit a live match on a lie.
///
/// That is right about `Instant` and wrong about the conclusion, because `Instant` is not the only
/// clock there is. The record now also carries WALL time — seconds since the UNIX epoch — for the
/// mint and for the last landed act, and adoption rebuilds each `Instant` by winding
/// `Instant::now()` BACK by the wall time that actually elapsed ([`rewind`]). Nothing is fabricated:
/// the reaper judges an adopted table by the time that really passed, and every way the wall clock
/// can misbehave lands on "just adopted", which delays a forfeit rather than causing one.
///
/// What the ending-only store cost instead was the opposite failure, and it was live: a pre-restart
/// table had no record at all, so [`TableRegistry::record`] answered `None`, so [`reap_table`] could
/// never clock-forfeit it and [`resign`] — the ONE resolution a player can cause — was silently
/// dropped while the match kept taking acts. The gate fell open in the *this match can never END*
/// direction. See `docs/reference/RESTART-SEMANTICS.md`.
fn table_record_dir() -> Option<std::path::PathBuf> {
    std::env::var("DREGGNET_WEB_SESSION_DIR")
        .ok()
        .filter(|dir| !dir.is_empty())
        .map(|dir| std::path::Path::new(&dir).join("tables"))
}

/// The stable file NAME for a table id — a content hash, so ANY id (including an ad-hoc one that
/// never came out of [`TableLock::mint_table_id`]) maps to a safe, collision-resistant name. It is
/// also what lets the durable-dir sweep check that a record is filed under the id it claims.
fn table_record_file_name(id: &str) -> String {
    format!("{}.table", blake3::hash(id.as_bytes()).to_hex())
}

/// The stable file for a table id.
fn table_record_path(dir: &std::path::Path, id: &str) -> std::path::PathBuf {
    dir.join(table_record_file_name(id))
}

/// **Wall-clock seconds since the UNIX epoch** — the only clock that means anything across a
/// restart. A clock set before 1970 reads as `0`, which [`rewind`] then treats as an elapsed time
/// no process has been alive for, and therefore as "just adopted".
fn wall_now() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|since| since.as_secs())
        .unwrap_or(0)
}

/// **Rebuild a monotonic `Instant` from a wall-clock stamp**, by winding `now` back the wall time
/// that elapsed since `stamp_wall`.
///
/// Every failure mode lands on `now` — "just adopted" — which DELAYS a forfeit rather than causing
/// one, and that direction is the whole point: this clock's failure mode is ending somebody's live
/// match. A stamp from the FUTURE (the wall clock was stepped back, or was never set) saturates to
/// zero elapsed; an elapsed longer than this process's own monotonic origin fails `checked_sub` and
/// falls back the same way.
fn rewind(now: Instant, now_wall: u64, stamp_wall: u64) -> Instant {
    let elapsed = Duration::from_secs(now_wall.saturating_sub(stamp_wall));
    now.checked_sub(elapsed).unwrap_or(now)
}

/// One table's record as it sits on disk — the decoded form of the one-line wire.
///
/// `id` and `opened_wall` are `Option` because a `v1` file (an existing deployment's, written when
/// only the ENDING was persisted) carries neither. A `v1` record therefore always carries a
/// resolution, and a resolved table never faces the clock, so nothing is lost.
#[derive(Clone, Debug)]
struct DurableTable {
    lock: TableLock,
    id: Option<String>,
    opened_wall: Option<u64>,
    last_act_wall: Option<(SeatSlot, u64)>,
    resolution: Option<Resolution>,
}

impl DurableTable {
    /// **Materialise a live record from a durable one**, rebuilding both `Instant`s from their wall
    /// stamps against a single `(now, now_wall)` reading.
    ///
    /// `None` for an UNRESOLVED record with no mint stamp: that is a table with no honest clock, and
    /// it is refused rather than handed to the reaper with a fabricated one. (Neither wire version
    /// can produce that shape; the arm is the fail-closed floor, not a live path.)
    fn adopt(self, now: Instant, now_wall: u64) -> Option<TableRecord> {
        let opened_wall = match (self.opened_wall, self.resolution.is_some()) {
            (Some(wall), _) => wall,
            (None, true) => now_wall,
            (None, false) => return None,
        };
        Some(TableRecord {
            lock: self.lock,
            opened: rewind(now, now_wall, opened_wall),
            last_act: self
                .last_act_wall
                .map(|(seat, wall)| (seat, rewind(now, now_wall, wall))),
            resolution: self.resolution,
            opened_wall,
            last_act_wall: self.last_act_wall.map(|(_, wall)| wall),
        })
    }
}

/// The one-line wire:
///
/// ```text
/// v2 <TAB> lock key <TAB> table id <TAB> opened(wall secs)
///    <TAB> act seat(a|b|empty) <TAB> act(wall secs|empty)
///    <TAB> started(0|1|empty) <TAB> cause(c|r|x|empty) <TAB> forfeited letters
/// ```
///
/// Tab-separated with no escaping needed — every field is a fixed vocabulary, a decimal, or an id
/// this module minted out of a prefix and hex. The last three fields are ALL empty exactly when the
/// table is still unresolved, which is the shape `v1` could not write down at all.
///
/// `v1` (`v1 <TAB> key <TAB> started <TAB> cause <TAB> forfeited`) is still DECODED — an existing
/// deployment has those files on disk — but is no longer emitted.
fn encode_table_record(id: &str, record: &TableRecord) -> String {
    debug_assert_eq!(
        record.last_act.is_some(),
        record.last_act_wall.is_some(),
        "an act stamp and its wall twin are written together or not at all"
    );
    let (act_seat, act_wall) = match (record.last_act, record.last_act_wall) {
        (Some((seat, _)), Some(wall)) => (seat.letter().to_string(), wall.to_string()),
        _ => (String::new(), String::new()),
    };
    let (started, cause, forfeited) = match &record.resolution {
        None => (String::new(), String::new(), String::new()),
        Some(resolution) => (
            u8::from(resolution.started).to_string(),
            match resolution.cause {
                Cause::Clock => "c",
                Cause::Resigned => "r",
                Cause::Concluded => "x",
            }
            .to_string(),
            resolution
                .forfeited
                .iter()
                .map(|seat| seat.letter())
                .collect(),
        ),
    };
    format!(
        "v2\t{key}\t{id}\t{opened}\t{act_seat}\t{act_wall}\t{started}\t{cause}\t{forfeited}\n",
        key = record.lock.key,
        opened = record.opened_wall,
    )
}

/// Reverse [`encode_table_record`]. A malformed / truncated / unknown-version line decodes as `None`
/// — fail-CLOSED in the safe direction: an unreadable record means "this process knows nothing about
/// that table", which is exactly the pre-durability behaviour, never a fabricated ending and never a
/// fabricated clock.
fn decode_table_record(line: &str) -> Option<DurableTable> {
    let fields: Vec<&str> = line.trim_end_matches(['\n', '\r']).split('\t').collect();
    match (fields.first().copied(), fields.len()) {
        (Some("v1"), 5) => Some(DurableTable {
            lock: lock_for_key(fields[1])?,
            id: None,
            opened_wall: None,
            last_act_wall: None,
            resolution: Some(decode_resolution(fields[2], fields[3], fields[4])?),
        }),
        (Some("v2"), 9) => {
            let lock = lock_for_key(fields[1])?;
            if fields[2].is_empty() {
                return None;
            }
            let opened_wall = fields[3].parse::<u64>().ok()?;
            // A half-written act pair decodes as nothing at all: a seat with no stamp has no clock
            // and a stamp with no seat has no author, and either would be a guess.
            let last_act_wall = match (fields[4], fields[5]) {
                ("", "") => None,
                (seat, at) => Some((SeatSlot::parse(seat)?, at.parse::<u64>().ok()?)),
            };
            let resolution = match (fields[6], fields[7], fields[8]) {
                ("", "", "") => None,
                (started, cause, forfeited) => Some(decode_resolution(started, cause, forfeited)?),
            };
            Some(DurableTable {
                lock,
                id: Some(fields[2].to_string()),
                opened_wall: Some(opened_wall),
                last_act_wall,
                resolution,
            })
        }
        _ => None,
    }
}

/// The ending's three fields, shared by both wire versions.
fn decode_resolution(started: &str, cause: &str, forfeited: &str) -> Option<Resolution> {
    let started = match started {
        "0" => false,
        "1" => true,
        _ => return None,
    };
    let cause = match cause {
        "c" => Cause::Clock,
        "r" => Cause::Resigned,
        "x" => Cause::Concluded,
        _ => return None,
    };
    let mut seats = Vec::new();
    for letter in forfeited.chars() {
        seats.push(SeatSlot::parse(&letter.to_string())?);
    }
    Some(Resolution {
        forfeited: seats,
        cause,
        started,
    })
}

/// The minted tables of this process.
#[derive(Default)]
pub struct TableRegistry {
    /// Who sat at each minted table, when either seat last acted, and how it ended.
    ///
    /// RESTART: **REBUILD.** Empty at boot, and its absence used to fall open in the *this match can
    /// never END* direction — not in the "anyone may act" direction, which is why REFUSE is the
    /// wrong answer here. [`TableRegistry::record`] answered `None` for every table minted by a
    /// previous process, so [`reap_table`] could never clock-forfeit one and a player's own
    /// [`resign`] was silently dropped while the match went on taking acts. Every record is now
    /// written to `<durable root>/<blake3(id)>.table` at the mint and at every landed act, in wall
    /// time, and read back by [`TableRegistry::adopt_durable`] on first touch or by
    /// [`TableRegistry::adopt_backlog`] on the sweeper's once-per-process walk of that directory.
    ///
    /// NOT refuse, deliberately: the act path already demands an unguessable 128-bit seat label
    /// ([`TableLock::seat_of_label`]), so an empty registry never meant "anyone may act". Refusing
    /// every unknown minted table would brick every live game across a deploy, and one failed write
    /// on the persist path would brick a legitimate one — which is the same degrade-and-say-so
    /// posture the seat key itself takes, in the other direction.
    ///
    /// NOT durable when there is no durable root: with `DREGGNET_WEB_SESSION_DIR` unset nothing is
    /// written and nothing is adopted, exactly as before. That deployment already accepts that its
    /// seat links do not survive a restart either, and it fails CLOSED (an old link stops
    /// verifying).
    tables: Mutex<HashMap<String, TableRecord>>,
    /// Table ids this process has already looked for on disk and NOT found. Without it, every act on
    /// a table with no durable record would pay a filesystem probe; with it, exactly one probe per
    /// id per process.
    ///
    /// RESTART: **PROCEED**, deliberately. It is a NEGATIVE cache and nothing more: empty at boot
    /// costs one extra `stat` per unknown id and changes no decision, because the answer it
    /// remembers ("there is no durable record for this id") is exactly what the probe it saves would
    /// return. An adversary who forces a restart gains a `stat`. It is bounded (`ABSENT_CAP`)
    /// because a table id is attacker-choosable from any URL.
    absent: Mutex<std::collections::HashSet<String>>,
    /// The directory the durable records live in, when it must not come from the process
    /// environment — i.e. what [`table_record_dir`] would return, not the session dir above it.
    /// `None` on the process registry. Test-only: `std::env::set_var` is process-global and every
    /// other test in this binary is running concurrently, so a test carries its root HERE.
    dir: Option<std::path::PathBuf>,
    /// Whether [`TableRegistry::adopt_backlog`] has already walked the durable directory. The walk
    /// is once per process: after it, every unresolved durable table is in `tables` and the ordinary
    /// in-RAM sweep covers them.
    swept: AtomicBool,
}

/// The process's table registry.
pub fn registry() -> &'static TableRegistry {
    static CELL: OnceLock<TableRegistry> = OnceLock::new();
    CELL.get_or_init(TableRegistry::default)
}

impl TableRegistry {
    /// A registry whose durable records live in `dir` rather than under the process environment.
    #[cfg(test)]
    fn in_dir(dir: impl Into<std::path::PathBuf>) -> TableRegistry {
        TableRegistry {
            dir: Some(dir.into()),
            ..TableRegistry::default()
        }
    }

    /// Where this registry's durable records live — its own root if it was given one, else the
    /// deployment's.
    fn records_dir(&self) -> Option<std::path::PathBuf> {
        self.dir.clone().or_else(table_record_dir)
    }

    /// Record a freshly minted table.
    ///
    /// The durable write happens HERE, at the mint, and not only at the ending: a table that was
    /// never written down cannot be adopted after a restart, and an un-adoptable table is one whose
    /// clock does not exist and whose seats cannot resign.
    pub fn opened(&self, lock: TableLock, id: &str, now: Instant) {
        let record = TableRecord::minted(lock, now, wall_now());
        self.lock().insert(id.to_string(), record.clone());
        self.persist(id, &record);
    }

    /// Note that `seat` acted. Ignored on a table nothing has ever minted and on one already
    /// resolved — but NOT on one minted before a restart: that table is adopted from its durable
    /// record first, so a landed act refreshes the clock of the table it landed on.
    pub fn record_act(&self, id: &str, seat: SeatSlot, now: Instant) {
        self.ensure_adopted(id);
        let wall = wall_now();
        let updated = {
            let mut tables = self.lock();
            match tables.get_mut(id) {
                Some(record) if record.resolution.is_none() => {
                    record.note_act(seat, now, wall);
                    Some(record.clone())
                }
                _ => None,
            }
        };
        if let Some(record) = updated {
            // This write is what makes the TURN clock survive a restart. Without it an adopted table
            // reads as never-played, and the reaper would judge it on the (much longer) open clock.
            self.persist(id, &record);
        }
    }

    /// **How the table ended, if it has** — from this process's memory, else from the durable record.
    ///
    /// ⚑ The disk read closes a real fail-OPEN. This registry only ever knew the tables THIS process
    /// minted, so after a restart every already-resolved table read as unresolved: the seat labels
    /// re-derive from the persisted seat key, so [`enforce`] let a seated player keep acting on a
    /// match the lobby had already ended. Consulting the durable record makes the ending survive the
    /// restart that the seat links already survive.
    ///
    /// It costs at most ONE filesystem probe per unknown id per process (see the `absent` negative
    /// cache), and zero for a table this process already knows.
    pub fn resolution(&self, id: &str) -> Option<Resolution> {
        self.record(id)?.resolution
    }

    /// The whole record — from this process's memory, else adopted from the durable one.
    pub fn record(&self, id: &str) -> Option<TableRecord> {
        // The guard is scoped EXPLICITLY: `adopt_durable` takes the same lock, so letting a
        // scrutinee temporary live across the fallthrough would deadlock the whole registry.
        let known = {
            let tables = self.lock();
            tables.get(id).cloned()
        };
        match known {
            Some(record) => Some(record),
            None => self.adopt_durable(id),
        }
    }

    /// Materialise `id` from its durable record if this process has not met it yet.
    ///
    /// Takes and releases the map lock, so it must never be called while holding it.
    fn ensure_adopted(&self, id: &str) {
        if self.lock().contains_key(id) {
            return;
        }
        self.adopt_durable(id);
    }

    /// **Adopt a table this process did not mint.** Memoises a HIT into the live map (so later reads
    /// are free) and a MISS into the negative cache only.
    ///
    /// Both an ENDED and a LIVE table are materialised. The live one's clock is not invented: its
    /// `Instant`s are wound back from the wall stamps the durable record carries (see
    /// [`rewind`] and `table_record_dir`).
    fn adopt_durable(&self, id: &str) -> Option<TableRecord> {
        // NO DURABLE DIR, NO DISK: there is nothing to read and therefore nothing to remember, so
        // this path allocates nothing at all for the in-RAM deployment (and for the whole test
        // suite). It also keeps the negative cache from filling up with ids on a server that could
        // never have answered them anyway.
        let dir = self.records_dir()?;
        if self.absent().contains(id) {
            return None;
        }
        let adopted = std::fs::read_to_string(table_record_path(&dir, id))
            .ok()
            .as_deref()
            .and_then(decode_table_record)
            .and_then(|durable| durable.adopt(Instant::now(), wall_now()));
        let Some(record) = adopted else {
            // ⚑ BOUNDED. A table id is attacker-choosable (`af1-` + any 24 hex chars is prefix-legal),
            // so an unbounded negative cache is a memory-growth vector reachable from any URL. Past
            // the cap the cache is dropped and refills; the worst case is that a probe costs one
            // `stat` again, which is exactly the pre-cache cost.
            const ABSENT_CAP: usize = 4096;
            let mut absent = self.absent();
            if absent.len() >= ABSENT_CAP {
                absent.clear();
            }
            absent.insert(id.to_string());
            return None;
        };
        self.lock().insert(id.to_string(), record.clone());
        Some(record)
    }

    /// **Adopt every UNRESOLVED table in the durable directory, once per process.** Returns how many
    /// it took in.
    ///
    /// [`reap_all`] sweeps the live map, and after a restart the live map holds only what somebody
    /// has visited — so a table minted before the restart that nobody ever looks at again would be
    /// invisible to the no-traffic half of the clock, which is exactly the half that exists for
    /// abandoned tables. This walk closes that: after it, every live durable table is in the map and
    /// the ordinary in-RAM sweep covers it.
    ///
    /// Once per process, because it is O(records ever written) and the directory is never GC'd. An
    /// ALREADY-ENDED record is skipped rather than adopted: the clock never judges it, so paging it
    /// in would buy nothing, and the on-demand path still answers for it. A record whose id does not
    /// hash to its own file name is skipped too — a file is only allowed to speak for the table it
    /// is filed under.
    fn adopt_backlog(&self) -> usize {
        if self.swept.swap(true, Ordering::SeqCst) {
            return 0;
        }
        let Some(dir) = self.records_dir() else {
            return 0;
        };
        let Ok(entries) = std::fs::read_dir(&dir) else {
            return 0;
        };
        let mut adopted = 0;
        for entry in entries.flatten() {
            let Some(durable) = std::fs::read_to_string(entry.path())
                .ok()
                .as_deref()
                .and_then(decode_table_record)
            else {
                continue;
            };
            if durable.resolution.is_some() {
                continue;
            }
            // A `v1` record carries no id — and always carries an ending, so it never reaches here.
            let Some(id) = durable.id.clone() else {
                continue;
            };
            if entry.file_name() != std::ffi::OsString::from(table_record_file_name(&id)) {
                continue;
            }
            if self.lock().contains_key(&id) {
                continue;
            }
            let Some(record) = durable.adopt(Instant::now(), wall_now()) else {
                continue;
            };
            self.lock().insert(id, record);
            adopted += 1;
        }
        adopted
    }

    /// Write a resolution, once — **in memory and on disk**. Returns the resolution now in force (an
    /// already-resolved table keeps its FIRST resolution: a clock cannot overwrite a resignation).
    ///
    /// The table is adopted first, so a resignation on a table minted before a restart LANDS instead
    /// of being dropped on the floor. `None` only when nothing anywhere has ever minted this id.
    ///
    /// The durable write happens only on the FIRST resolution, which is the same write-once point,
    /// so the file cannot disagree with memory about how a table ended.
    pub fn resolve(&self, id: &str, resolution: Resolution) -> Option<Resolution> {
        self.ensure_adopted(id);
        let (in_force, newly_written, record) = {
            let mut tables = self.lock();
            let record = tables.get_mut(id)?;
            let fresh = record.resolution.is_none();
            if fresh {
                record.resolution = Some(resolution);
            }
            (record.resolution.clone(), fresh, record.clone())
        };
        if newly_written {
            self.persist(id, &record);
            // It is resolved now, so a stale negative-cache entry must not answer for it.
            self.absent().remove(id);
        }
        in_force
    }

    /// Persist one table's whole record. A write failure is NOT fatal and NOT silent: the process
    /// keeps the correct in-memory record and logs that it will not survive a restart — the same
    /// degrade-and-say-so posture the seat key itself takes, and the reason REFUSE is the wrong
    /// answer for the registry (one bad write would otherwise brick a legitimate live table).
    fn persist(&self, id: &str, record: &TableRecord) {
        let Some(dir) = self.records_dir() else {
            return;
        };
        let path = table_record_path(&dir, id);
        let write = std::fs::create_dir_all(&dir)
            .and_then(|()| std::fs::write(&path, encode_table_record(id, record)));
        if let Err(error) = write {
            tracing::warn!(
                path = %path.display(),
                table = %id,
                error = %error,
                "could not persist a table's record — this table will not survive a restart"
            );
        }
    }

    fn absent(&self) -> std::sync::MutexGuard<'_, std::collections::HashSet<String>> {
        self.absent.lock().unwrap_or_else(|e| e.into_inner())
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
/// abandonment with no winner.
///
/// ⚑ If NEITHER does, the match **PLAYED ITSELF OUT** and is recorded as [`Cause::Concluded`]. That
/// used to return `None` and write down nothing at all — so the one ending a player actually wants
/// (they finished the game) was the one ending this server never kept, which is exactly why `/you`
/// had no finished-match history. It is still not a claim about who won.
///
/// Every newly-written ending also RETIRES the host session ([`archive_finished`]): the durable
/// move-log is archived rather than deleted, so the finished match stays replayable.
pub fn reap_table(state: &CatalogState, id: &str, now: Instant) -> Option<Resolution> {
    reap_table_in(registry(), state, id, now)
}

/// [`reap_table`] against an explicit registry — see [`enforce_in`] for why the parameter exists.
fn reap_table_in(
    tables: &TableRegistry,
    state: &CatalogState,
    id: &str,
    now: Instant,
) -> Option<Resolution> {
    let record = tables.record(id)?;
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
        // Retired like any other ending, and the archive layer does the right thing with it: an
        // UNPLAYED session's genesis is DELETED rather than filed as a finished match (see
        // `SessionResumeStore::archive`), so a table nobody sat at never appears in anyone's history.
        return resolve_and_retire_in(
            tables,
            state,
            id,
            &lock,
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
    let cause = if owing.is_empty() {
        Cause::Concluded
    } else {
        Cause::Clock
    };
    resolve_and_retire_in(
        tables,
        state,
        id,
        &lock,
        Resolution {
            forfeited: owing,
            cause,
            started: true,
        },
    )
}

/// Write `resolution` (write-once) and, if it is the one that took effect, retire the host session so
/// the match becomes a finished, replayable artifact.
fn resolve_and_retire_in(
    tables: &TableRegistry,
    state: &CatalogState,
    id: &str,
    lock: &TableLock,
    resolution: Resolution,
) -> Option<Resolution> {
    let before = tables.resolution(id).is_some();
    let in_force = tables.resolve(id, resolution)?;
    if !before {
        archive_finished(state, lock, id);
    }
    Some(in_force)
}

/// **Retire a finished table's host session.** The world stops being a live session and its durable
/// move-log is ARCHIVED — the finished match keeps its reproducible input, so
/// `/offerings/{key}/session/{id}/verify` can still re-execute it and `/you` can still list it.
///
/// Idempotent and quiet: a session that is already gone (evicted, never opened, closed by a previous
/// pass) simply reports `false`. A failure to retire is not allowed to fail the reap — the ending is
/// already recorded, and a session left live on a resolved table is harmless (every act on it is
/// refused by [`enforce`]) whereas an aborted reap would leave the table unresolved.
pub fn archive_finished(state: &CatalogState, lock: &TableLock, id: &str) -> bool {
    let sid = SessionId::new(id.to_string());
    // Seat A's derived identity is only the ROUTING viewer here (the shared catalog host ignores it
    // for a non-RPG key); nothing about this read is per-seat.
    let viewer = lock.seat_identity(id, SeatSlot::A);
    match state.close_game_session(lock.key, &sid, &viewer) {
        Ok(closed) => closed,
        Err(error) => {
            tracing::warn!(
                table = %id,
                key = %lock.key,
                error = %error,
                "a finished table's session could not be retired; its ending is recorded and every \
                 further act is refused, but the match may not be listed as finished"
            );
            false
        }
    }
}

/// **Resign `seat` at `id`.** A player may always end their own table; this is the only resolution
/// a *user* can cause, and it can only ever cost the person who fires it.
///
/// `started` is TRUE even when no turn has landed. It marks "somebody was here and made a
/// decision", which is exactly what a resignation is — a seat that opens a table and gives it up
/// before its first move has still given it up, and the other seat takes it. Only the CLOCK's
/// nobody-ever-showed-up case records `started: false`.
///
/// It takes the catalog because a resignation ENDS a match, and every ending goes through the one
/// retirement path (`resolve_and_retire_in` → [`archive_finished`]): the world stops being live and
/// its move-log is archived rather than deleted. Threading the state through is deliberate — the
/// alternative (a pure `resign` plus a "remember to retire" call at the route) is exactly the shape
/// that leaves one of two endings un-archived and nobody noticing.
pub fn resign(
    state: &CatalogState,
    lock: &TableLock,
    id: &str,
    seat: SeatSlot,
) -> Option<Resolution> {
    resign_in(registry(), state, lock, id, seat)
}

/// [`resign`] against an explicit registry — see [`enforce_in`] for why the parameter exists.
fn resign_in(
    tables: &TableRegistry,
    state: &CatalogState,
    lock: &TableLock,
    id: &str,
    seat: SeatSlot,
) -> Option<Resolution> {
    resolve_and_retire_in(
        tables,
        state,
        id,
        lock,
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
///
/// The first call of a process also pages in the durable backlog, so "a table nobody is watching"
/// covers the ones minted before a restart as well as the ones minted after it.
pub fn reap_all(state: &CatalogState) -> Vec<String> {
    reap_all_in(registry(), state)
}

/// [`reap_all`] against an explicit registry — see [`enforce_in`] for why the parameter exists.
fn reap_all_in(tables: &TableRegistry, state: &CatalogState) -> Vec<String> {
    tables.adopt_backlog();
    let now = Instant::now();
    // Take the widest window first so one pass covers never-started and stalled tables alike; each
    // candidate re-checks its OWN limit inside `reap_table`.
    let limit = turn_limit().min(open_limit());
    tables
        .stalled(limit, now)
        .into_iter()
        .filter(|(id, _)| reap_table_in(tables, state, id, now).is_some())
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

    /// The resignation a PLAYER fires, as the registry sees it. `resign` itself needs a live catalog
    /// (every ending retires its world), so these registry-level tests write the same resolution
    /// directly; the route `POST {game}/table/{id}/resign` is driven end to end in
    /// `tests/tug_table.rs`, which is where the retirement half is exercised.
    fn resigned(id: &str, seat: SeatSlot) -> Option<Resolution> {
        registry().resolve(
            id,
            Resolution {
                forfeited: vec![seat],
                cause: Cause::Resigned,
                started: true,
            },
        )
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
        let resolution = resigned(&id, SeatSlot::A).expect("the table is registered");
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
        let first = resigned(&id, SeatSlot::A).expect("registered");
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

    /// ⚑ **A match that PLAYED ITSELF OUT is an ending, not a forfeit** — and the copy must not
    /// borrow the walked-away words, because a player who finished their game would read them as an
    /// accusation. It also names no winner: this lobby is not what decides one.
    #[test]
    fn a_concluded_table_reads_as_played_out_and_never_as_abandoned() {
        let resolution = Resolution {
            forfeited: Vec::new(),
            cause: Cause::Concluded,
            started: true,
        };
        assert!(resolution.concluded());
        assert_eq!(
            resolution.winner(),
            None,
            "the lobby must not name a winner for a match the executor decided"
        );
        let headline = resolution.headline();
        assert!(headline.contains("played itself out"), "{headline}");
        for walked_away in ["clock", "abandoned", "forfeit", "resigned"] {
            assert!(
                !headline.contains(walked_away),
                "a finished match must not be described as `{walked_away}`: {headline}"
            );
        }
        let refusal = resolution.refusal();
        assert!(
            !refusal.contains("somebody stopped playing"),
            "the walked-away refusal leaked onto a finished match: {refusal}"
        );
        assert!(
            refusal.contains("Replay the finished match"),
            "a finished match's refusal must point at the replay: {refusal}"
        );

        // NON-VACUOUS: a genuine forfeit still says every one of those words.
        let forfeit = Resolution {
            forfeited: vec![SeatSlot::A],
            cause: Cause::Clock,
            started: true,
        };
        assert!(forfeit.headline().contains("forfeit"));
        assert!(forfeit.refusal().contains("not a proven win"));
        assert!(!forfeit.concluded());
    }

    /// The durable ending round-trips through its one-line wire, and every malformed shape decodes as
    /// `None` — a file this process cannot read must mean "I do not know that this table is over",
    /// never a fabricated ending.
    #[test]
    fn a_table_ending_round_trips_and_refuses_every_malformed_line() {
        for (lock, resolution) in [
            (
                TUG,
                Resolution {
                    forfeited: vec![SeatSlot::B],
                    cause: Cause::Resigned,
                    started: true,
                },
            ),
            (
                AUTOMATAFL,
                Resolution {
                    forfeited: vec![SeatSlot::A, SeatSlot::B],
                    cause: Cause::Clock,
                    started: true,
                },
            ),
            (
                AUTOMATAFL,
                Resolution {
                    forfeited: Vec::new(),
                    cause: Cause::Concluded,
                    started: true,
                },
            ),
            (
                TUG,
                Resolution {
                    forfeited: Vec::new(),
                    cause: Cause::Clock,
                    started: false,
                },
            ),
        ] {
            let line = encode_table_record(
                "tug1-0123456789abcdef01234567",
                &ended(lock, resolution.clone()),
            );
            let back = decode_table_record(&line).unwrap_or_else(|| panic!("decodes: {line:?}"));
            assert_eq!(back.lock.key, lock.key);
            assert_eq!(
                back.resolution,
                Some(resolution),
                "round-trip lost information: {line:?}"
            );
        }
        for bad in [
            "",
            "v1",
            "v2\ttug\t1\tc\ta",
            "v1\tnot-a-game\t1\tc\ta",
            "v1\ttug\t2\tc\ta",
            "v1\ttug\t1\tz\ta",
            "v1\ttug\t1\tc\tq",
            "v1\ttug\t1\tc\ta\textra",
            // …and the same fail-closed floor for `v2`, whose extra fields are extra ways to lie.
            "v3\ttug\ttug1-x\t100\t\t\t1\tc\ta",
            "v2\ttug\ttug1-x\t100\t\t\t1\tc",
            "v2\ttug\ttug1-x\t100\t\t\t1\tc\ta\textra",
            "v2\tnot-a-game\ttug1-x\t100\t\t\t1\tc\ta",
            "v2\ttug\t\t100\t\t\t1\tc\ta",
            "v2\ttug\ttug1-x\t\t\t\t1\tc\ta",
            "v2\ttug\ttug1-x\tnope\t\t\t1\tc\ta",
            "v2\ttug\ttug1-x\t-1\t\t\t1\tc\ta",
            // A half-written act pair: a seat with no stamp, or a stamp with no seat.
            "v2\ttug\ttug1-x\t100\ta\t\t1\tc\ta",
            "v2\ttug\ttug1-x\t100\t\t150\t1\tc\ta",
            "v2\ttug\ttug1-x\t100\tq\t150\t1\tc\ta",
            "v2\ttug\ttug1-x\t100\ta\tnope\t1\tc\ta",
            // A half-written ending: unresolved is all three fields empty, never some of them.
            "v2\ttug\ttug1-x\t100\t\t\t\tc\ta",
            "v2\ttug\ttug1-x\t100\t\t\t1\t\ta",
            "v2\ttug\ttug1-x\t100\t\t\t2\tc\ta",
            "v2\ttug\ttug1-x\t100\t\t\t1\tz\ta",
            "v2\ttug\ttug1-x\t100\t\t\t1\tc\tq",
        ] {
            assert!(
                decode_table_record(bad).is_none(),
                "a malformed record must not decode: {bad:?}"
            );
        }
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

    // ─────────────────────────────────────────────────────────────────────────────────────
    // RESTART SEMANTICS — `docs/reference/RESTART-SEMANTICS.md`, answer 2 (REBUILD).
    //
    // A restart is modelled as what it actually is: a SECOND `TableRegistry` over the same
    // durable root, which has never been told any of the ids the first one minted. Every
    // assertion below is on the DECISION that registry makes, never on the bytes.
    //
    // The root is carried on the registry rather than in `DREGGNET_WEB_SESSION_DIR`, because
    // `std::env::set_var` is process-global and every other test in this binary is running
    // concurrently — a test that sets it would be deciding other tests' durability for them.
    // ─────────────────────────────────────────────────────────────────────────────────────

    /// A resolved record, for the wire round-trip.
    fn ended(lock: TableLock, resolution: Resolution) -> TableRecord {
        TableRecord {
            resolution: Some(resolution),
            ..TableRecord::minted(lock, Instant::now(), 1_700_000_000)
        }
    }

    /// ⚑ **The durable record now carries a LIVE table, not only an ending** — and still reads the
    /// `v1` files a deployment that only ever persisted the ending has on disk.
    #[test]
    fn a_durable_record_round_trips_a_live_table_and_still_decodes_v1() {
        let id = "tug1-0123456789abcdef01234567";
        for last_act in [None, Some((SeatSlot::B, 1_700_000_600_u64))] {
            for resolution in [
                None,
                Some(Resolution {
                    forfeited: vec![SeatSlot::A],
                    cause: Cause::Resigned,
                    started: true,
                }),
            ] {
                let record = TableRecord {
                    lock: TUG,
                    opened: Instant::now(),
                    last_act: last_act.map(|(seat, _)| (seat, Instant::now())),
                    resolution: resolution.clone(),
                    opened_wall: 1_700_000_000,
                    last_act_wall: last_act.map(|(_, wall)| wall),
                };
                let line = encode_table_record(id, &record);
                let back =
                    decode_table_record(&line).unwrap_or_else(|| panic!("decodes: {line:?}"));
                assert_eq!(back.lock.key, "tug");
                assert_eq!(
                    back.id.as_deref(),
                    Some(id),
                    "the id is what the durable-dir sweep addresses the table by: {line:?}"
                );
                assert_eq!(back.opened_wall, Some(1_700_000_000), "{line:?}");
                assert_eq!(back.last_act_wall, last_act, "{line:?}");
                assert_eq!(back.resolution, resolution, "{line:?}");
            }
        }

        // A `v1` file still decodes, losslessly, and still adopts — a resolved table never faces
        // the clock, so the stamps it does not carry decide nothing.
        let v1 = decode_table_record("v1\ttug\t1\tr\tb\n").expect("a v1 ending still decodes");
        assert_eq!(v1.lock.key, "tug");
        assert_eq!(v1.id, None);
        assert_eq!(v1.opened_wall, None);
        assert_eq!(
            v1.resolution,
            Some(Resolution {
                forfeited: vec![SeatSlot::B],
                cause: Cause::Resigned,
                started: true,
            })
        );
        let adopted = v1
            .adopt(Instant::now(), wall_now())
            .expect("a v1 ending adopts");
        assert!(adopted.resolution.is_some());
        assert!(
            !adopted.started(),
            "a v1 file records no act, so none is invented"
        );

        // An UNRESOLVED record with no mint stamp has no honest clock, so it is REFUSED rather
        // than handed to the reaper with a fabricated one. Neither wire version can write that
        // shape; this pins the fail-closed floor of `adopt` itself.
        let clockless = DurableTable {
            lock: TUG,
            id: Some(id.to_string()),
            opened_wall: None,
            last_act_wall: None,
            resolution: None,
        };
        assert!(clockless.adopt(Instant::now(), wall_now()).is_none());
    }

    /// **The rebuilt clock is conservative in every direction a wall clock can go wrong** — each
    /// failure reads as "just adopted", which delays a forfeit rather than causing one.
    #[test]
    fn a_rebuilt_stamp_never_ages_a_table_it_cannot_account_for() {
        // Far enough from this process's monotonic origin that an ordinary rewind is representable
        // however recently the machine booted.
        let now = Instant::now() + Duration::from_secs(86_400);
        assert_eq!(
            now.saturating_duration_since(rewind(now, 1_000_600, 1_000_000)),
            Duration::from_secs(600),
            "ten minutes of wall time is ten minutes of clock"
        );
        assert_eq!(
            rewind(now, 1_000_000, 2_000_000),
            now,
            "a stamp from the future (the wall clock was stepped back) reads as just-adopted"
        );
        assert_eq!(
            rewind(now, u64::MAX, 0),
            now,
            "an elapsed longer than this process has existed reads the same way"
        );
    }

    /// ⚑ **THE RESTART TEST.** A table minted and played before the restart is still a table this
    /// process can decide about after it — with the clock it actually had, not a fresh one.
    ///
    /// Before the durable record carried the whole table, `record()` answered `None` here, so
    /// [`reap_table`] returned `None` on its first line and a pre-restart table could never be
    /// clock-forfeited at all.
    #[test]
    fn a_pre_restart_table_keeps_its_clock_and_can_still_be_reaped() {
        assert!(
            turn_limit() < open_limit(),
            "this test distinguishes the two deadlines, so they must differ"
        );
        let root = tempfile::tempdir().expect("a durable root");
        let state = CatalogState::new();

        // ── before the restart: one table played, one nobody ever sat at ──
        let before = TableRegistry::in_dir(root.path());
        let played = TUG.mint_table_id();
        let untouched = AUTOMATAFL.mint_table_id();
        before.opened(TUG, &played, Instant::now());
        before.opened(AUTOMATAFL, &untouched, Instant::now());
        before.record_act(&played, SeatSlot::A, Instant::now());

        // ── the restart: a registry that has never been told either id ──
        let after = TableRegistry::in_dir(root.path());
        assert!(after.is_empty(), "the restarted registry starts empty");

        let record = after
            .record(&played)
            .expect("a pre-restart table is adopted from its durable record");
        assert_eq!(record.lock.key, "tug");
        assert!(
            record.started(),
            "the act stamp survived, so the TURN clock is the one that applies"
        );
        assert!(
            record.resolution.is_none(),
            "adopting a LIVE table must never fabricate an ending"
        );

        // Inside its window nothing happens — the adopted stamps are the real ones, not a rewind
        // to the beginning of time. This is the non-vacuity check: an adoption that aged the table
        // would forfeit a live match here.
        let now = Instant::now();
        assert!(reap_table_in(&after, &state, &played, now).is_none());
        assert!(reap_table_in(&after, &state, &untouched, now).is_none());

        // Past the TURN deadline the played table resolves. (The recorded CAUSE is the offering's
        // answer to "is either seat owed a move", and this fixture hosts no live tug session for
        // the table; what is under test is that the clock can see the table AT ALL.)
        let past_turn = now + turn_limit() + Duration::from_secs(1);
        assert!(
            reap_table_in(&after, &state, &played, past_turn).is_some(),
            "a pre-restart table past its turn deadline must be reapable"
        );

        // The never-played one is on the longer OPEN clock, so the same instant leaves it live —
        // which is the `opened` stamp being real too, and not the act stamp in disguise.
        assert!(
            reap_table_in(&after, &state, &untouched, past_turn).is_none(),
            "a table nobody sat at is judged on the open clock, not the turn clock"
        );
        let expired = reap_table_in(
            &after,
            &state,
            &untouched,
            now + open_limit() + Duration::from_secs(1),
        )
        .expect("a pre-restart table nobody sat at still expires");
        assert_eq!(expired.cause, Cause::Clock);
        assert!(!expired.started, "nobody played, so nobody forfeits");
        assert!(expired.forfeited.is_empty());
    }

    /// ⚑ **A player's resignation on a pre-restart table used to be SILENTLY DROPPED.** `resolve`
    /// started `tables.get_mut(id)?`, which was `None` for a table this process had not minted, so
    /// nothing was written to memory or disk and the match went on taking acts — the one resolution
    /// a user can cause, failing quietly.
    #[test]
    fn a_pre_restart_resignation_is_recorded_rather_than_silently_dropped() {
        let root = tempfile::tempdir().expect("a durable root");
        let state = CatalogState::new();

        let before = TableRegistry::in_dir(root.path());
        let id = TUG.mint_table_id();
        before.opened(TUG, &id, Instant::now());
        before.record_act(&id, SeatSlot::B, Instant::now());

        // ── the restart ──
        let after = TableRegistry::in_dir(root.path());
        let resolution = resign_in(&after, &state, &TUG, &id, SeatSlot::A)
            .expect("a seated player may always end their own table, restart or no restart");
        assert_eq!(resolution.forfeited, vec![SeatSlot::A]);
        assert_eq!(resolution.cause, Cause::Resigned);
        assert_eq!(
            resolution.winner(),
            Some(SeatSlot::B),
            "a resignation can only ever cost the seat that fires it"
        );

        // And it is durable in ITS turn: the ending survives the NEXT restart too, so this is a
        // rebuilt guard rather than a one-shot repair.
        let later = TableRegistry::in_dir(root.path());
        assert_eq!(
            later.resolution(&id),
            Some(resolution),
            "the resignation reached the disk"
        );
    }

    /// ⚑ **THE AUTHORITY TEST.** A rebuilt gate must be told apart from a deleted one, so both
    /// halves are asserted after the restart: the two seats still get in, and everybody else is
    /// still refused — including, on a table that ENDED before the restart, its own seated player.
    #[test]
    fn the_gate_still_holds_across_a_restart_on_a_live_table_and_on_a_finished_one() {
        let root = tempfile::tempdir().expect("a durable root");
        let state = CatalogState::new();

        let before = TableRegistry::in_dir(root.path());
        let id = TUG.mint_table_id();
        before.opened(TUG, &id, Instant::now());
        before.record_act(&id, SeatSlot::A, Instant::now());
        let seat_a = TUG.seat_label(&id, SeatSlot::A);
        let seat_b = TUG.seat_label(&id, SeatSlot::B);

        // ── the restart. The adopted table is LIVE, so it still takes its own two seats' acts …
        let after = TableRegistry::in_dir(root.path());
        assert!(enforce_in(&after, "tug", &id, &seat_a).is_ok());
        assert!(enforce_in(&after, "tug", &id, &seat_b).is_ok());
        // … and refuses everyone else, BEFORE the substrate and with nothing recorded.
        let another_table = TUG.seat_label(&TUG.mint_table_id(), SeatSlot::A);
        for stranger in ["mallory", "", another_table.as_str()] {
            let refused = enforce_in(&after, "tug", &id, stranger)
                .expect_err("a stranger holds no seat at an adopted table either");
            assert!(refused.contains("seat-locked table"), "{refused}");
        }

        // ── the table ends, and a SECOND restart. The ending is what the gate must rebuild: the
        // seat labels re-derive from the durable key, so without it seat B would keep playing a
        // match the lobby had already ended.
        resign_in(&after, &state, &TUG, &id, SeatSlot::A).expect("seat A resigns");
        let after2 = TableRegistry::in_dir(root.path());
        let refused = enforce_in(&after2, "tug", &id, &seat_b)
            .expect_err("a table that ended before the restart takes no further act");
        assert!(refused.contains("forfeit"), "{refused}");
        assert!(
            refused.contains("not a proven win"),
            "a forfeit must never be described as a proven win: {refused}"
        );
        assert!(
            enforce_in(&after2, "tug", &id, "mallory").is_err(),
            "and the seat lock is still the seat lock"
        );
    }

    /// **The no-traffic half of the clock, across a restart.** [`reap_all`] sweeps the LIVE map, and
    /// after a restart that map holds only what somebody has visited — so a table minted before the
    /// restart that nobody ever looks at again would be invisible to exactly the sweep that exists
    /// for abandoned tables. The durable directory is walked ONCE per process to close that.
    #[test]
    fn the_sweeper_adopts_the_durable_backlog_once_and_skips_the_tables_that_already_ended() {
        let root = tempfile::tempdir().expect("a durable root");
        let before = TableRegistry::in_dir(root.path());
        let live_played = TUG.mint_table_id();
        let live_unplayed = AUTOMATAFL.mint_table_id();
        let over = TUG.mint_table_id();
        before.opened(TUG, &live_played, Instant::now());
        before.opened(AUTOMATAFL, &live_unplayed, Instant::now());
        before.opened(TUG, &over, Instant::now());
        before.record_act(&live_played, SeatSlot::A, Instant::now());
        before
            .resolve(
                &over,
                Resolution {
                    forfeited: vec![SeatSlot::A],
                    cause: Cause::Resigned,
                    started: true,
                },
            )
            .expect("registered");

        // ── the restart: a registry told nothing at all ──
        let after = TableRegistry::in_dir(root.path());
        assert_eq!(
            after.adopt_backlog(),
            2,
            "both LIVE tables are paged in; the finished one is not, because the clock never \
             judges it"
        );
        assert_eq!(
            after.adopt_backlog(),
            0,
            "the durable directory is walked once per process"
        );

        let stalled: Vec<String> = after
            .stalled(Duration::ZERO, Instant::now())
            .into_iter()
            .map(|(id, _)| id)
            .collect();
        assert_eq!(stalled.len(), 2, "{stalled:?}");
        assert!(stalled.contains(&live_played), "{stalled:?}");
        assert!(stalled.contains(&live_unplayed), "{stalled:?}");
        assert!(
            !stalled.contains(&over),
            "a table that already ended is never handed to the reaper: {stalled:?}"
        );

        // The finished one is not LOST by being skipped — it is still answered on demand, which is
        // the path `enforce` takes.
        assert_eq!(
            after.resolution(&over).map(|r| r.cause),
            Some(Cause::Resigned)
        );
    }
}
