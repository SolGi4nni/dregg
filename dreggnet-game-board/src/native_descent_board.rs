//! Replay-verified seasonal leaderboard for the Lean-native Descent.
//!
//! This is deliberately a sibling of [`crate::GameBoard`], not another variant
//! of its FULL-STARK game enum. Native Descent currently exports an exact,
//! actor-bound public journal which can be re-executed through the Lean-emitted
//! program, but it does not yet export the one succinct recursive proof that
//! `ugc-dregg::Registry::submit_proof` requires. Calling the two paths the same
//! thing would erase an important assurance boundary.
//!
//! A live submission carries the exact [`NativeDescentRecord`] and separate
//! [`NativeDescentCompletion`] claimed by the caller. Admission opens a fresh
//! native executor, replays the record, and requires exact player, seed, root,
//! revision, settlement receipt, relic set, and crowned-bit equality. The board
//! retains the minimal public replay witness (actor + commands + completion),
//! rather than trusting cached score fields.
//!
//! Snapshot import is equally fail-closed: the canonical wire has a BLAKE3
//! corruption digest, but that digest is not an operator signature. Its actual
//! no-cheat tooth is that every decoded witness is played again through
//! [`NativeDescentOffering`] and resubmitted through the same admission path.
//! A party able to replace a complete snapshot can replace it with a different
//! *valid* set of runs; deployment authenticity still belongs to signed storage
//! or a consensus log outside this crate.

use std::collections::HashSet;
use std::fmt;

use dreggnet_offerings::native_descent::{
    AssetId, CommittedSeed, NativeDescentBankedNote, NativeDescentCompletion, NativeDescentMove,
    NativeDescentOffering, NativeDescentRecord, Rarity,
};
use dreggnet_offerings::{DreggIdentity, Offering, Outcome, RecordVerify, SessionConfig};

const SNAPSHOT_MAGIC: [u8; 8] = *b"DREGGNDB";
/// v3 carries a settled run's BANKED-RELIC NOTES (the real owned assets the banked custody
/// minted) alongside the relic index list, so a restart image claims the complete completion
/// its fresh re-execution is compared against.
/// v4 carries the season's run day-seed. A v3 image could only describe a seed-derived season
/// and carries no day to restart under, so it is refused rather than restarted on a guess.
const SNAPSHOT_VERSION: u8 = 4;
const SNAPSHOT_DIGEST_DOMAIN: &str = "dregg.native-descent-board.snapshot.v4";
const MAX_SNAPSHOT_BYTES: usize = 32 * 1024 * 1024;
const MAX_ENTRIES: usize = 10_000;
const MAX_ACTOR_BYTES: usize = 512;

/// The intentionally explicit assurance label for this board.
pub const NATIVE_DESCENT_BOARD_ASSURANCE: &str = "Lean-authored transition program; exact public record freshly replay-verified (not a succinct FULL-STARK completion proof)";

/// Immutable identity of one seasonal native-Descent board.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NativeDescentSeason {
    pub season_id: u64,
    /// The normalized native seed (`1..=251`) recorded by the offering.
    pub seed: u8,
    /// **The run day-seed every run on this board deployed on** — the provenance root its banked
    /// relics mint under, and (folded into the genesis root) part of the season's identity.
    ///
    /// A season is a *day's* board: a live daily surface binds this to the day's verified drand
    /// reveal, so the season is over worlds nobody could pre-compute. It is carried explicitly
    /// rather than left implicit in `genesis_root`, because [`NativeDescentSeasonBoard::
    /// reverify`] and the snapshot decode REBUILD runs by re-opening and re-driving their
    /// commands — and a session opened on the wrong provenance root re-derives nothing.
    pub day_seed: CommittedSeed,
    /// The exact genesis journal root re-derived when the board is opened/imported.
    pub genesis_root: [u8; 32],
}

/// Score facts retained only after exact replay.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeDescentStanding {
    pub player: DreggIdentity,
    pub completion_root: [u8; 32],
    pub settlement_receipt_hash: [u8; 32],
    pub crowned: bool,
    pub banked_relics: Vec<u64>,
    pub peak_depth: u64,
    pub turns: usize,
}

/// Admission result, including the run's rank under the current board.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeDescentAccepted {
    pub rank: usize,
    pub standing: NativeDescentStanding,
}

#[derive(Clone, Debug)]
struct ArchivedRun {
    standing: NativeDescentStanding,
    commands: Vec<NativeDescentMove>,
    completion: NativeDescentCompletion,
}

/// Fail-closed errors from live admission or canonical restart.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NativeBoardError {
    InvalidSeasonSeed,
    WrongWorldSeed {
        expected: u8,
        found: u8,
    },
    /// The submitted run's provenance root is not this season's day.
    WrongSeasonDay,
    ReplayRefused(String),
    MissingCompletion,
    PlayerSubstitution,
    CompletionSubstitution,
    DuplicateCompletion,
    UnknownCompletion,
    BoardFull,
    MalformedSnapshot(String),
    SnapshotDigestMismatch,
    SnapshotSeasonMismatch,
}

impl fmt::Display for NativeBoardError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidSeasonSeed => f.write_str("native Descent season seed is not canonical"),
            Self::WrongWorldSeed { expected, found } => {
                write!(
                    f,
                    "run belongs to native seed {found}, board expects {expected}"
                )
            }
            Self::WrongSeasonDay => {
                f.write_str("run's provenance day-seed is not this season's day")
            }
            Self::ReplayRefused(reason) => write!(f, "fresh native replay refused: {reason}"),
            Self::MissingCompletion => f.write_str("run has no terminal bank settlement"),
            Self::PlayerSubstitution => {
                f.write_str("submitted player differs from the replay-bound actor")
            }
            Self::CompletionSubstitution => {
                f.write_str("supplied completion differs from the replay-derived completion")
            }
            Self::DuplicateCompletion => f.write_str("completion is already ranked"),
            Self::UnknownCompletion => f.write_str("completion is not on this native board"),
            Self::BoardFull => f.write_str("native season board reached its fixed entry bound"),
            Self::MalformedSnapshot(reason) => {
                write!(f, "malformed native board snapshot: {reason}")
            }
            Self::SnapshotDigestMismatch => f.write_str("native board snapshot digest mismatch"),
            Self::SnapshotSeasonMismatch => {
                f.write_str("snapshot season identity does not re-derive")
            }
        }
    }
}

impl std::error::Error for NativeBoardError {}

/// A replay-verified leaderboard for one exact native world and season.
///
/// Ranking is lexicographic: Crown banked first, then more banked relics,
/// deeper descent, fewer turns, and finally completion-root order for a stable
/// total ordering. Cached score fields are never accepted over the wire.
pub struct NativeDescentSeasonBoard {
    season: NativeDescentSeason,
    entries: Vec<ArchivedRun>,
    seen: HashSet<[u8; 32]>,
}

impl NativeDescentSeasonBoard {
    /// Open a board over the reproducible, deploy-seed-derived world for `raw_seed` — the
    /// fixture season. A board for a LIVE day's runs is [`open_on_day`](Self::open_on_day):
    /// the runs a live surface produces deploy on their day's provenance root, and a board
    /// opened here would reject every one of them as belonging to another season.
    pub fn open(season_id: u64, raw_seed: u64) -> Result<Self, NativeBoardError> {
        Self::open_with(NativeDescentOffering::new(), season_id, raw_seed)
    }

    /// **Open a board for one exact run day-seed** — the season a live daily surface's runs
    /// belong to. Pass the day-seed those runs carry (`NativeDescentRecord::day_seed`, itself
    /// derived from that day's verified beacon); every admitted run must name it, and reverify
    /// and snapshot-restart re-drive commands under it.
    pub fn open_on_day(
        season_id: u64,
        raw_seed: u64,
        day_seed: CommittedSeed,
    ) -> Result<Self, NativeBoardError> {
        Self::open_with(
            NativeDescentOffering::on_run_day_seed(day_seed),
            season_id,
            raw_seed,
        )
    }

    fn open_with(
        offering: NativeDescentOffering,
        season_id: u64,
        raw_seed: u64,
    ) -> Result<Self, NativeBoardError> {
        let session = offering
            .open(SessionConfig::with_seed(raw_seed))
            .map_err(|error| NativeBoardError::ReplayRefused(error.to_string()))?;
        let record = offering.export_record(&session);
        Ok(Self {
            season: NativeDescentSeason {
                season_id,
                seed: record.seed,
                day_seed: record.day_seed,
                genesis_root: session.root(),
            },
            entries: Vec::new(),
            seen: HashSet::new(),
        })
    }

    /// The offering this board's season re-opens runs through — pinned to the season's own run
    /// day-seed, so a re-drive lands on the same genesis the admitted runs did.
    fn offering(&self) -> NativeDescentOffering {
        NativeDescentOffering::on_run_day_seed(self.season.day_seed)
    }

    fn open_normalized(
        season_id: u64,
        seed: u8,
        day_seed: CommittedSeed,
        claimed_genesis: [u8; 32],
    ) -> Result<Self, NativeBoardError> {
        if !(1..=251).contains(&seed) {
            return Err(NativeBoardError::InvalidSeasonSeed);
        }
        // The offering normalizes raw as `(raw % 251) + 1`; `seed - 1` is the
        // canonical inverse for every normalized seed.
        let board = Self::open_on_day(season_id, u64::from(seed - 1), day_seed)?;
        if board.season.seed != seed || board.season.genesis_root != claimed_genesis {
            return Err(NativeBoardError::SnapshotSeasonMismatch);
        }
        Ok(board)
    }

    pub const fn season(&self) -> NativeDescentSeason {
        self.season
    }

    pub const fn assurance(&self) -> &'static str {
        NATIVE_DESCENT_BOARD_ASSURANCE
    }

    /// Submit an exact native record and exact claimed completion.
    ///
    /// Nothing from either object is trusted as score: a fresh executor replay
    /// derives the completion and state facts again before mutation occurs.
    pub fn submit(
        &mut self,
        player: DreggIdentity,
        record: &NativeDescentRecord,
        completion: &NativeDescentCompletion,
    ) -> Result<NativeDescentAccepted, NativeBoardError> {
        if record.seed != self.season.seed {
            return Err(NativeBoardError::WrongWorldSeed {
                expected: self.season.seed,
                found: record.seed,
            });
        }
        // A season is a day's board. A run whose provenance root is another day's is another
        // season's run, even at the same world seed — and admitting it would leave an entry
        // this board cannot re-drive (reverify and snapshot-restart deploy on the season's
        // day-seed). Refuse it at the door instead.
        if record.day_seed != self.season.day_seed {
            return Err(NativeBoardError::WrongSeasonDay);
        }
        if self.entries.len() >= MAX_ENTRIES {
            return Err(NativeBoardError::BoardFull);
        }
        if self.seen.contains(&completion.root) {
            return Err(NativeBoardError::DuplicateCompletion);
        }

        let offering = NativeDescentOffering::new();
        let replayed = offering
            .resume_record(record)
            .map_err(|error| NativeBoardError::ReplayRefused(error.to_string()))?;
        let derived = replayed
            .completion()
            .cloned()
            .ok_or(NativeBoardError::MissingCompletion)?;

        if replayed.actor() != Some(&player)
            || record.actor.as_ref() != Some(&player)
            || derived.actor != player
        {
            return Err(NativeBoardError::PlayerSubstitution);
        }
        if record.completion.as_ref() != Some(completion)
            || &derived != completion
            || derived.root != record.root
            || derived.root != replayed.root()
            || derived.revision != replayed.revision()
        {
            return Err(NativeBoardError::CompletionSubstitution);
        }

        let standing = NativeDescentStanding {
            player,
            completion_root: derived.root,
            settlement_receipt_hash: derived.settlement_receipt_hash,
            crowned: derived.crowned,
            banked_relics: derived.banked_relics.clone(),
            peak_depth: record
                .events
                .iter()
                .map(|event| event.post.depth)
                .max()
                .unwrap_or(0),
            turns: record.events.len(),
        };
        let archived = ArchivedRun {
            standing: standing.clone(),
            commands: record.events.iter().map(|event| event.command).collect(),
            completion: derived,
        };
        self.seen.insert(standing.completion_root);
        self.entries.push(archived);
        let rank = self
            .leaderboard()
            .iter()
            .position(|candidate| candidate.completion_root == standing.completion_root)
            .expect("newly inserted standing is ranked")
            + 1;
        Ok(NativeDescentAccepted { rank, standing })
    }

    /// Stable ranked view. This clones only public score facts, never receipts
    /// or the command witness retained for restart.
    pub fn leaderboard(&self) -> Vec<NativeDescentStanding> {
        let mut standings: Vec<_> = self
            .entries
            .iter()
            .map(|entry| entry.standing.clone())
            .collect();
        standings.sort_by(|a, b| {
            b.crowned
                .cmp(&a.crowned)
                .then_with(|| b.banked_relics.len().cmp(&a.banked_relics.len()))
                .then_with(|| b.peak_depth.cmp(&a.peak_depth))
                .then_with(|| a.turns.cmp(&b.turns))
                .then_with(|| a.completion_root.cmp(&b.completion_root))
        });
        standings
    }

    /// Independently re-drive one retained replay witness and pass the result
    /// back through the same admission path. This is linear in the public run
    /// length, unlike [`crate::GameBoard::reverify`]'s succinct proof check.
    pub fn reverify(
        &self,
        completion_root: &[u8; 32],
    ) -> Result<NativeDescentStanding, NativeBoardError> {
        let archived = self
            .entries
            .iter()
            .find(|entry| &entry.standing.completion_root == completion_root)
            .ok_or(NativeBoardError::UnknownCompletion)?;
        let offering = self.offering();
        let (record, completion) = drive_commands(
            &offering,
            self.season.seed,
            &archived.standing.player,
            &archived.commands,
        )?;
        if completion != archived.completion {
            return Err(NativeBoardError::CompletionSubstitution);
        }
        let mut fresh = Self::open_normalized(
            self.season.season_id,
            self.season.seed,
            self.season.day_seed,
            self.season.genesis_root,
        )?;
        let accepted = fresh.submit(archived.standing.player.clone(), &record, &completion)?;
        if accepted.standing != archived.standing {
            return Err(NativeBoardError::CompletionSubstitution);
        }
        Ok(accepted.standing)
    }

    /// Canonical restart image. Entries are ordered by completion root rather
    /// than insertion order; all integers are big-endian and lengths bounded.
    pub fn export_canonical(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&SNAPSHOT_MAGIC);
        out.push(SNAPSHOT_VERSION);
        put_u64(&mut out, self.season.season_id);
        out.push(self.season.seed);
        out.extend_from_slice(self.season.day_seed.as_bytes());
        out.extend_from_slice(&self.season.genesis_root);
        put_u32(
            &mut out,
            u32::try_from(self.entries.len()).expect("the fixed board bound fits u32"),
        );

        let mut entries: Vec<_> = self.entries.iter().collect();
        entries.sort_by_key(|entry| entry.standing.completion_root);
        for entry in entries {
            put_bytes_u16(&mut out, entry.standing.player.as_str().as_bytes());
            put_u16(
                &mut out,
                u16::try_from(entry.commands.len())
                    .expect("the fixed native journal bound fits u16"),
            );
            for command in &entry.commands {
                encode_command(&mut out, *command);
            }
            put_u64(&mut out, entry.completion.revision);
            out.extend_from_slice(&entry.completion.root);
            out.extend_from_slice(&entry.completion.settlement_receipt_hash);
            put_u16(
                &mut out,
                u16::try_from(entry.completion.banked_relics.len())
                    .expect("the fixed native relic set fits u16"),
            );
            for relic in &entry.completion.banked_relics {
                put_u64(&mut out, *relic);
            }
            put_u16(
                &mut out,
                u16::try_from(entry.completion.banked_notes.len())
                    .expect("the fixed native relic set fits u16"),
            );
            for note in &entry.completion.banked_notes {
                put_u64(&mut out, note.relic);
                out.extend_from_slice(&note.asset_id.bytes());
                out.push(note.rarity.tag());
                out.extend_from_slice(&note.owner);
            }
            out.push(u8::from(entry.completion.crowned));
        }
        let digest = snapshot_digest(&out);
        out.extend_from_slice(&digest);
        out
    }

    /// Decode a canonical restart image and re-admit every run by fresh native
    /// execution. No cached score or completion field bypasses `submit`.
    pub fn import_canonical(bytes: &[u8]) -> Result<Self, NativeBoardError> {
        if bytes.len() > MAX_SNAPSHOT_BYTES || bytes.len() < 32 {
            return Err(NativeBoardError::MalformedSnapshot(
                "snapshot size is outside the fixed bound".to_string(),
            ));
        }
        let (body, claimed_digest) = bytes.split_at(bytes.len() - 32);
        if snapshot_digest(body).as_slice() != claimed_digest {
            return Err(NativeBoardError::SnapshotDigestMismatch);
        }
        let mut cursor = Cursor::new(body);
        if cursor.array::<8>()? != SNAPSHOT_MAGIC {
            return Err(NativeBoardError::MalformedSnapshot(
                "wrong snapshot magic".to_string(),
            ));
        }
        if cursor.u8()? != SNAPSHOT_VERSION {
            return Err(NativeBoardError::MalformedSnapshot(
                "unsupported snapshot version".to_string(),
            ));
        }
        let season_id = cursor.u64()?;
        let seed = cursor.u8()?;
        let day_seed = CommittedSeed::from_bytes(cursor.array::<32>()?);
        let genesis_root = cursor.array::<32>()?;
        let count = usize::try_from(cursor.u32()?)
            .map_err(|_| malformed("entry count exceeds this target"))?;
        if count > MAX_ENTRIES {
            return Err(NativeBoardError::MalformedSnapshot(
                "entry count exceeds the fixed bound".to_string(),
            ));
        }
        let mut board = Self::open_normalized(season_id, seed, day_seed, genesis_root)?;
        let offering = board.offering();
        let mut previous_root = None;
        for _ in 0..count {
            let actor_bytes = cursor.bytes_u16(MAX_ACTOR_BYTES)?;
            let actor = DreggIdentity(
                std::str::from_utf8(actor_bytes)
                    .map_err(|_| malformed("actor is not UTF-8"))?
                    .to_string(),
            );
            let command_count = usize::from(cursor.u16()?);
            if command_count > dreggnet_offerings::native_descent::MAX_NATIVE_DESCENT_EVENTS {
                return Err(malformed("command count exceeds the native journal bound"));
            }
            let mut commands = Vec::with_capacity(command_count);
            for _ in 0..command_count {
                commands.push(decode_command(&mut cursor)?);
            }
            let claimed = NativeDescentCompletion {
                actor: actor.clone(),
                revision: cursor.u64()?,
                root: cursor.array::<32>()?,
                settlement_receipt_hash: cursor.array::<32>()?,
                banked_relics: {
                    let relics = usize::from(cursor.u16()?);
                    let mut values = Vec::with_capacity(relics);
                    for _ in 0..relics {
                        values.push(cursor.u64()?);
                    }
                    values
                },
                banked_notes: {
                    let notes = usize::from(cursor.u16()?);
                    let mut values = Vec::with_capacity(notes);
                    for _ in 0..notes {
                        values.push(NativeDescentBankedNote {
                            relic: cursor.u64()?,
                            asset_id: AssetId(cursor.array::<32>()?),
                            rarity: Rarity::from_tag(cursor.u8()?)
                                .ok_or_else(|| malformed("rarity tag is not canonical"))?,
                            owner: cursor.array::<32>()?,
                        });
                    }
                    values
                },
                crowned: match cursor.u8()? {
                    0 => false,
                    1 => true,
                    _ => return Err(malformed("crowned flag is not canonical")),
                },
            };
            if previous_root.is_some_and(|root| root >= claimed.root) {
                return Err(malformed(
                    "snapshot entries are not in canonical completion-root order",
                ));
            }
            previous_root = Some(claimed.root);

            let (record, derived) = drive_commands(&offering, seed, &actor, &commands)?;
            if derived != claimed {
                return Err(NativeBoardError::CompletionSubstitution);
            }
            board.submit(actor, &record, &claimed)?;
        }
        cursor.finish()?;
        Ok(board)
    }
}

fn drive_commands(
    offering: &NativeDescentOffering,
    normalized_seed: u8,
    actor: &DreggIdentity,
    commands: &[NativeDescentMove],
) -> Result<(NativeDescentRecord, NativeDescentCompletion), NativeBoardError> {
    if !(1..=251).contains(&normalized_seed) {
        return Err(NativeBoardError::InvalidSeasonSeed);
    }
    let mut session = offering
        .open(SessionConfig::with_seed(u64::from(normalized_seed - 1)))
        .map_err(|error| NativeBoardError::ReplayRefused(error.to_string()))?;
    for command in commands {
        let (turn, arg) = command_action(*command)?;
        let action = offering
            .actions(&session)
            .into_iter()
            .find(|candidate| candidate.turn == turn && candidate.arg == arg)
            .ok_or_else(|| {
                NativeBoardError::ReplayRefused(format!(
                    "native surface omitted archived command {turn}({arg})"
                ))
            })?;
        if !action.enabled {
            return Err(NativeBoardError::ReplayRefused(format!(
                "archived command {turn}({arg}) is disabled at this state"
            )));
        }
        match offering.advance(&mut session, action, actor.clone()) {
            Outcome::Landed { .. } => {}
            Outcome::Refused(reason) => return Err(NativeBoardError::ReplayRefused(reason)),
        }
    }
    let completion = session
        .completion()
        .cloned()
        .ok_or(NativeBoardError::MissingCompletion)?;
    Ok((offering.export_record(&session), completion))
}

fn command_action(command: NativeDescentMove) -> Result<(&'static str, i64), NativeBoardError> {
    match command {
        NativeDescentMove::Delve => Ok(("delve", 0)),
        NativeDescentMove::Unlock { way } => i64::try_from(way)
            .map(|way| ("unlock", way))
            .map_err(|_| malformed("unlock argument exceeds the action wire")),
        NativeDescentMove::Smite => Ok(("smite", 0)),
        NativeDescentMove::Loot { relic } => i64::try_from(relic)
            .map(|relic| ("loot", relic))
            .map_err(|_| malformed("loot argument exceeds the action wire")),
        NativeDescentMove::Flee => Ok(("flee", 0)),
    }
}

fn encode_command(out: &mut Vec<u8>, command: NativeDescentMove) {
    let (tag, arg) = match command {
        NativeDescentMove::Delve => (0, 0),
        NativeDescentMove::Unlock { way } => (1, way),
        NativeDescentMove::Smite => (2, 0),
        NativeDescentMove::Loot { relic } => (3, relic),
        NativeDescentMove::Flee => (4, 0),
    };
    out.push(tag);
    put_u64(out, arg);
}

fn decode_command(cursor: &mut Cursor<'_>) -> Result<NativeDescentMove, NativeBoardError> {
    let tag = cursor.u8()?;
    let arg = cursor.u64()?;
    match (tag, arg) {
        (0, 0) => Ok(NativeDescentMove::Delve),
        (1, way) => Ok(NativeDescentMove::Unlock { way }),
        (2, 0) => Ok(NativeDescentMove::Smite),
        (3, relic) => Ok(NativeDescentMove::Loot { relic }),
        (4, 0) => Ok(NativeDescentMove::Flee),
        _ => Err(malformed("non-canonical native command")),
    }
}

fn snapshot_digest(body: &[u8]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(SNAPSHOT_DIGEST_DOMAIN);
    hasher.update(body);
    *hasher.finalize().as_bytes()
}

fn put_u16(out: &mut Vec<u8>, value: u16) {
    out.extend_from_slice(&value.to_be_bytes());
}

fn put_u32(out: &mut Vec<u8>, value: u32) {
    out.extend_from_slice(&value.to_be_bytes());
}

fn put_u64(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_be_bytes());
}

fn put_bytes_u16(out: &mut Vec<u8>, bytes: &[u8]) {
    put_u16(
        out,
        u16::try_from(bytes.len()).expect("bounded native actor identity fits u16"),
    );
    out.extend_from_slice(bytes);
}

fn malformed(reason: impl Into<String>) -> NativeBoardError {
    NativeBoardError::MalformedSnapshot(reason.into())
}

struct Cursor<'a> {
    bytes: &'a [u8],
    position: usize,
}

impl<'a> Cursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, position: 0 }
    }

    fn u8(&mut self) -> Result<u8, NativeBoardError> {
        Ok(self.array::<1>()?[0])
    }

    fn u16(&mut self) -> Result<u16, NativeBoardError> {
        Ok(u16::from_be_bytes(self.array()?))
    }

    fn u32(&mut self) -> Result<u32, NativeBoardError> {
        Ok(u32::from_be_bytes(self.array()?))
    }

    fn u64(&mut self) -> Result<u64, NativeBoardError> {
        Ok(u64::from_be_bytes(self.array()?))
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N], NativeBoardError> {
        let bytes = self.bytes(N)?;
        let mut out = [0; N];
        out.copy_from_slice(bytes);
        Ok(out)
    }

    fn bytes(&mut self, len: usize) -> Result<&'a [u8], NativeBoardError> {
        let end = self
            .position
            .checked_add(len)
            .ok_or_else(|| malformed("wire position overflow"))?;
        let bytes = self
            .bytes
            .get(self.position..end)
            .ok_or_else(|| malformed("truncated snapshot"))?;
        self.position = end;
        Ok(bytes)
    }

    fn bytes_u16(&mut self, max: usize) -> Result<&'a [u8], NativeBoardError> {
        let len = usize::from(self.u16()?);
        if len > max {
            return Err(malformed("length-prefixed field exceeds its fixed bound"));
        }
        self.bytes(len)
    }

    fn finish(self) -> Result<(), NativeBoardError> {
        if self.position == self.bytes.len() {
            Ok(())
        } else {
            Err(malformed("trailing bytes before the snapshot digest"))
        }
    }
}
