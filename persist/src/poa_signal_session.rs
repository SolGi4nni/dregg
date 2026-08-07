//! Durable custody of one player's judged Signal session.
//!
//! # What a session is, and why it has to be durable
//!
//! Judged Signal is `SignalTriangulation`: 216 codes, five bursts, LOCKED/DRIFT
//! feedback after each. The budget IS the game — an oracle you may query without
//! limit answers 216 questions and the deduction is a formality. So the count of
//! rounds a player has spent against a given (authority, slot) is a fact the node
//! must remember across restarts, and remember for the RIGHT player.
//!
//! An in-memory session map would hand every player a fresh five-round budget on
//! every node restart, against the same installed slot and therefore the same
//! target. That is not a lost feature; it is an unbounded oracle with a delay.
//!
//! # The key is (authority, slot, player), and each part is load-bearing
//!
//! * **authority** — sessions do not cross federations.
//! * **slot** — a new curator slot is a new secret and therefore a new target for
//!   every player. A fresh budget then is correct, and it is why the slot is in the
//!   key rather than being overwritten in place.
//! * **player** — `HiddenInstance.runSeedFor` takes the player key, so two players
//!   in one slot draw DIFFERENT targets
//!   (`SlotDeriveRuntime.fixture_commitment_is_player_independent_but_the_seed_is_not`).
//!   A per-player budget is therefore not merely fair, it is unfarmable: opening
//!   sessions under other keys buys feedback about targets those keys cannot settle.
//!
//! ⚠ Proof of possession of the player key is the NODE's job (the session route
//!   demands an Ed25519 signature over the open/guess statement before it comes
//!   here). Persist checks storage invariants; it does not authenticate a caller.
//!
//! # Persist-then-reveal
//!
//! [`PersistentStore::record_poa_signal_session_round_v1`] appends the round AND its
//! classification in one committed transaction, and the caller must not return the
//! classification to the player until that commit succeeds. The ordering is the whole
//! crash-safety argument: a node that died after answering and before committing would
//! have given away a round for free, every time, to anyone willing to kill it.
//!
//! A player who loses the response instead of the round reads it back from the stored
//! transcript, which is why the record retains the feedback and not only the count.
//! That retention leaks nothing — it is what the player already saw.
//!
//! # What this module does NOT check
//!
//! That `exact`/`present` are the right classification of `guess` is
//! `SignalTriangulation.feedback`, which lives in Lean behind
//! `dregg_poa_signal_feedback`. Persist holds no copy of it and stores what the node
//! was handed. A stored transcript is therefore evidence of what the node SERVED, not
//! independently of the node evidence of what the rule SAYS; the rule is re-applied by
//! the judge when the run settles, and a session that disagreed with it would produce a
//! claim the judge refuses.

use redb::{ReadableTable, ReadableTableMetadata, TableDefinition, WriteTransaction};
use serde::{Deserialize, Serialize};

use crate::{PersistentStore, Result, StoreError};

pub(crate) const POA_SIGNAL_SESSION_V1: TableDefinition<&[u8], &[u8]> =
    TableDefinition::new("poa_signal_session_v1");

/// Schema tag stored in every record.
pub const POA_SIGNAL_SESSION_SCHEMA_V1: &str = "POA-SIGNAL-SESSION-1";

/// The complete action budget of one judged run.
///
/// ⚠ This is `SignalTriangulation.MAX_TURNS`. The two must agree: a store that
/// admitted a sixth round would build a transcript the judge's `replay` refuses at the
/// step, which surfaces to the player as an inexplicable rejection AFTER they paid a
/// turn fee. [`crate::tests`] has no way to check a Lean constant, so this is stated
/// here and the node's session module asserts the pair on every guess it records.
pub const POA_SIGNAL_SESSION_MAX_ROUNDS: usize = 5;

/// One played round: what was submitted, and what the Lean oracle answered.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PoaSignalSessionRoundV1 {
    /// The three submitted bands, each `0..=5`.
    pub guess: [u8; 3],
    /// LOCKED — `SignalTriangulation.Feedback.exact`.
    pub exact: u8,
    /// DRIFT — `SignalTriangulation.Feedback.present`.
    pub present: u8,
}

/// One player's judged session against one installed slot.
///
/// ⚠ There is no target field, no run seed field and no secret field, and there must
/// never be one. The node derives the instance per guess through Lean and keeps only
/// the classification; a session record that cached the answer would put the answer in
/// the same store a read route walks.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PoaSignalSessionV1 {
    schema: String,
    authority_id: [u8; 32],
    slot: u64,
    mission_id: u64,
    player_key: [u8; 32],
    /// The slot commitment this session was opened against — the curator-signed,
    /// PUBLISHED value. Retained so a re-open under a re-installed slot cannot
    /// silently continue a transcript played against a different secret.
    commitment: [u8; 32],
    rounds: Vec<PoaSignalSessionRoundV1>,
    solved: bool,
}

impl PoaSignalSessionV1 {
    pub fn authority_id(&self) -> [u8; 32] {
        self.authority_id
    }

    pub fn slot(&self) -> u64 {
        self.slot
    }

    pub fn mission_id(&self) -> u64 {
        self.mission_id
    }

    pub fn player_key(&self) -> [u8; 32] {
        self.player_key
    }

    pub fn commitment(&self) -> [u8; 32] {
        self.commitment
    }

    pub fn rounds(&self) -> &[PoaSignalSessionRoundV1] {
        &self.rounds
    }

    pub fn solved(&self) -> bool {
        self.solved
    }

    /// Rounds spent. Never exceeds [`POA_SIGNAL_SESSION_MAX_ROUNDS`].
    pub fn rounds_used(&self) -> usize {
        self.rounds.len()
    }

    /// Rounds left. Zero once solved: a solved run is over, and
    /// `SignalTriangulation.solved_refuses` says the same thing about `step`.
    pub fn rounds_remaining(&self) -> usize {
        if self.solved {
            return 0;
        }
        POA_SIGNAL_SESSION_MAX_ROUNDS.saturating_sub(self.rounds.len())
    }

    /// Whether another guess may be recorded. This is `SignalTriangulation.openB`.
    pub fn open(&self) -> bool {
        !self.solved && self.rounds.len() < POA_SIGNAL_SESSION_MAX_ROUNDS
    }

    /// The solving guess, if this session solved. It is the code a settling claim must
    /// carry, and it is only ever a code the player themselves submitted.
    pub fn solving_guess(&self) -> Option<[u8; 3]> {
        if !self.solved {
            return None;
        }
        self.rounds.last().map(|round| round.guess)
    }
}

/// Why a round could not be recorded. Each variant names the REAL cause; a session
/// that fails must not fail as a generic error, because the player is owed the
/// difference between "you are out of bursts" and "you already solved this".
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoaSignalSessionRefusalV1 {
    /// No session is open for these coordinates.
    NoSession,
    /// The run is already solved; it is over.
    AlreadySolved,
    /// All five bursts are spent.
    BudgetExhausted,
    /// A band outside `0..=5`.
    BandOutOfRange,
}

impl std::fmt::Display for PoaSignalSessionRefusalV1 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoSession => write!(f, "no judged Signal session is open for this player"),
            Self::AlreadySolved => write!(f, "this judged Signal run is already solved"),
            Self::BudgetExhausted => write!(
                f,
                "all {POA_SIGNAL_SESSION_MAX_ROUNDS} bursts of this judged Signal run are spent"
            ),
            Self::BandOutOfRange => write!(f, "a Signal band exceeds the base-six bound"),
        }
    }
}

fn integrity(message: impl Into<String>) -> StoreError {
    StoreError::Integrity(message.into())
}

/// `authority_id || slot_be64 || player_key`.
fn session_key(authority_id: [u8; 32], slot: u64, player_key: [u8; 32]) -> Vec<u8> {
    let mut key = Vec::with_capacity(72);
    key.extend_from_slice(&authority_id);
    key.extend_from_slice(&slot.to_be_bytes());
    key.extend_from_slice(&player_key);
    key
}

fn decode(bytes: &[u8]) -> Result<PoaSignalSessionV1> {
    postcard::from_bytes(bytes)
        .map_err(|error| integrity(format!("stored PoA Signal session is unreadable: {error}")))
}

fn encode(record: &PoaSignalSessionV1) -> Result<Vec<u8>> {
    postcard::to_stdvec(record)
        .map_err(|error| integrity(format!("cannot encode PoA Signal session: {error}")))
}

pub(crate) fn initialize_poa_signal_session_tables_v1_in(write: &WriteTransaction) -> Result<()> {
    let _ = write.open_table(POA_SIGNAL_SESSION_V1)?;
    Ok(())
}

impl PersistentStore {
    /// Open a judged session, or hand back the one already in progress.
    ///
    /// ⚑ **IDEMPOTENT, AND THAT IS THE WHOLE POINT.** Re-opening never resets the
    /// budget. A player who reloads the page, loses the response, or restarts the node
    /// gets their transcript back exactly where they left it. Only a NEW SLOT — a new
    /// curator secret, and therefore a new target — starts a new session, and it does
    /// so by being a different key rather than by clearing anything.
    ///
    /// Refuses when the stored session was opened against a different mission or a
    /// different commitment for the same slot. Those coordinates are the instance's
    /// identity; continuing a transcript across them would be scoring guesses about one
    /// target as though they were about another.
    pub fn open_poa_signal_session_v1(
        &self,
        authority_id: [u8; 32],
        slot: u64,
        mission_id: u64,
        player_key: [u8; 32],
        commitment: [u8; 32],
    ) -> Result<PoaSignalSessionV1> {
        let key = session_key(authority_id, slot, player_key);
        let write = self.db.begin_write()?;
        let record = {
            let mut sessions = write.open_table(POA_SIGNAL_SESSION_V1)?;
            let stored = match sessions.get(key.as_slice())? {
                Some(found) => Some(decode(found.value())?),
                None => None,
            };
            match stored {
                Some(existing) => {
                    if existing.mission_id != mission_id || existing.commitment != commitment {
                        return Err(integrity(
                            "a judged Signal session for this player and slot was opened against \
                             a different mission or commitment; refusing to continue a transcript \
                             across instances",
                        ));
                    }
                    existing
                }
                None => {
                    let fresh = PoaSignalSessionV1 {
                        schema: POA_SIGNAL_SESSION_SCHEMA_V1.to_owned(),
                        authority_id,
                        slot,
                        mission_id,
                        player_key,
                        commitment,
                        rounds: Vec::new(),
                        solved: false,
                    };
                    sessions.insert(key.as_slice(), encode(&fresh)?.as_slice())?;
                    fresh
                }
            }
        };
        write.commit()?;
        Ok(record)
    }

    /// Load one session by its coordinates.
    pub fn load_poa_signal_session_v1(
        &self,
        authority_id: [u8; 32],
        slot: u64,
        player_key: [u8; 32],
    ) -> Result<Option<PoaSignalSessionV1>> {
        let read = self.db.begin_read()?;
        let sessions = read.open_table(POA_SIGNAL_SESSION_V1)?;
        let key = session_key(authority_id, slot, player_key);
        match sessions.get(key.as_slice())? {
            Some(found) => decode(found.value()).map(Some),
            None => Ok(None),
        }
    }

    /// Spend one burst: append the guess and the classification Lean returned, in ONE
    /// committed transaction, and return the session as it now stands.
    ///
    /// ⚠ The caller must not reveal `exact`/`present` to the player before this
    /// returns `Ok`. See the module header: answering before committing hands out a
    /// free round to anyone who can crash the node.
    ///
    /// The budget check re-reads inside the write transaction rather than trusting a
    /// value the caller loaded earlier, so two concurrent guesses cannot both see four
    /// rounds spent and both append.
    pub fn record_poa_signal_session_round_v1(
        &self,
        authority_id: [u8; 32],
        slot: u64,
        player_key: [u8; 32],
        round: PoaSignalSessionRoundV1,
    ) -> Result<std::result::Result<PoaSignalSessionV1, PoaSignalSessionRefusalV1>> {
        if round.guess.iter().any(|band| *band > 5) {
            return Ok(Err(PoaSignalSessionRefusalV1::BandOutOfRange));
        }
        let key = session_key(authority_id, slot, player_key);
        let write = self.db.begin_write()?;
        let outcome = {
            let mut sessions = write.open_table(POA_SIGNAL_SESSION_V1)?;
            let Some(found) = sessions.get(key.as_slice())? else {
                drop(sessions);
                write.abort()?;
                return Ok(Err(PoaSignalSessionRefusalV1::NoSession));
            };
            let mut record = decode(found.value())?;
            drop(found);
            if record.solved {
                drop(sessions);
                write.abort()?;
                return Ok(Err(PoaSignalSessionRefusalV1::AlreadySolved));
            }
            if record.rounds.len() >= POA_SIGNAL_SESSION_MAX_ROUNDS {
                drop(sessions);
                write.abort()?;
                return Ok(Err(PoaSignalSessionRefusalV1::BudgetExhausted));
            }
            record.rounds.push(round);
            // `solved` is `exact == 3`, which `SignalTriangulation.accepted_solved_iff_
            // target` proves is equivalent to the guess BEING the target. The node does
            // not get to decide this on any other evidence, and neither does storage.
            record.solved = round.exact == 3;
            sessions.insert(key.as_slice(), encode(&record)?.as_slice())?;
            record
        };
        write.commit()?;
        Ok(Ok(outcome))
    }

    /// Structural audit: every stored record is readable, self-consistent with the key
    /// it is filed under, and within its own budget.
    pub fn audit_poa_signal_sessions_v1(&self) -> Result<()> {
        let read = self.db.begin_read()?;
        let sessions = read.open_table(POA_SIGNAL_SESSION_V1)?;
        if sessions.len()? == 0 {
            return Ok(());
        }
        for entry in sessions.iter()? {
            let (key, value) = entry?;
            let key = key.value();
            if key.len() != 72 {
                return Err(integrity(
                    "PoA Signal session key is not authority_id||slot_be64||player_key",
                ));
            }
            let record = decode(value.value())?;
            let mut authority_id = [0u8; 32];
            authority_id.copy_from_slice(&key[..32]);
            let mut slot_bytes = [0u8; 8];
            slot_bytes.copy_from_slice(&key[32..40]);
            let mut player_key = [0u8; 32];
            player_key.copy_from_slice(&key[40..]);
            if record.schema != POA_SIGNAL_SESSION_SCHEMA_V1 {
                return Err(integrity("stored PoA Signal session names another schema"));
            }
            if record.authority_id != authority_id
                || record.slot != u64::from_be_bytes(slot_bytes)
                || record.player_key != player_key
            {
                return Err(integrity(
                    "stored PoA Signal session does not match the coordinates it is filed under",
                ));
            }
            if record.rounds.len() > POA_SIGNAL_SESSION_MAX_ROUNDS {
                return Err(integrity(
                    "stored PoA Signal session exceeds the five-burst action budget",
                ));
            }
            if record.rounds.iter().any(|r| {
                r.guess.iter().any(|band| *band > 5) || r.exact > 3 || r.exact + r.present > 3
            }) {
                return Err(integrity(
                    "stored PoA Signal session holds a round outside the rule's own bounds",
                ));
            }
            let solved_by_transcript = record.rounds.last().is_some_and(|r| r.exact == 3);
            if record.solved != solved_by_transcript {
                return Err(integrity(
                    "stored PoA Signal session's solved bit disagrees with its transcript",
                ));
            }
        }
        Ok(())
    }
}
