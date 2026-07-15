//! # Canonical faction standing — the one cell the quest / guild / tavern gates read.
//!
//! Before this, each consumer re-derived faction standing by hand: `dreggnet-quest` reconstructs
//! its own `rep_embers` / `ember_quest` program and reads slots by index. That is the integration
//! gap — no *shared* standing a gate reads. This module is that shared reader: a typed
//! [`FactionStanding`] read off a deployed [`Roster`](crate::Roster) world through the canonical
//! slot names ([`rep_var`](crate::roster::rep_var) etc.), so a quest / guild / tavern gate asks
//! `standing.content_available()` instead of hardcoding a slot.
//!
//! It also PERSISTS standing per-identity: [`StandingSnapshot`] captures a world's standing as
//! serializable data, [`StandingStore`] keys snapshots by identity (JSON in/out), and
//! [`StandingSnapshot::restore`] rebuilds a world at the persisted standing — reps, ceilings, and
//! the `WriteOnce` seals all reinstated, so a betrayed faction stays sealed across a save/load.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use spween::Value;
use spween_dregg::WorldCell;

use crate::roster::{FactionDef, Roster, betrayed_var, ceiling_var, quest_var, rep_var};

/// **A faction's standing, read off the committed cell state.** The typed projection a gate reads
/// instead of a raw slot.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FactionStanding {
    /// The faction's stable key.
    pub key: String,
    /// The faction's display name.
    pub name: String,
    /// Current standing (`rep_<key>`) — a `Monotonic` value that only rises.
    pub rep: u64,
    /// The standing the faction's content requires.
    pub threshold: u64,
    /// The faction's current trust ceiling (dropped by rival pledges).
    pub ceiling: u64,
    /// The full trust the faction extends (the ceiling's start value — the bar's scale).
    pub trust_ceiling: u64,
    /// Whether the content is unlocked (`<key>_quest` set).
    pub unlocked: bool,
    /// Whether the faction has been betrayed (`<key>_betrayed` set — a permanent seal).
    pub betrayed: bool,
}

impl FactionStanding {
    /// Standing meets the faction's threshold (before the betrayal seal is considered).
    pub fn meets_threshold(&self) -> bool {
        self.rep >= self.threshold
    }

    /// **The gate a consumer reads.** The faction's content is available iff standing clears the
    /// threshold AND the faction has not been betrayed — exactly the trial's compiled + augmented
    /// teeth (`FieldGte(rep, threshold)` ∧ `FieldEquals(betrayed, 0)`).
    pub fn content_available(&self) -> bool {
        self.meets_threshold() && !self.betrayed
    }

    /// A short human standing label (`betrayed` / `trial unlocked` / `trusted` / `neutral`).
    pub fn label(&self) -> &'static str {
        if self.betrayed {
            "betrayed"
        } else if self.unlocked {
            "trial unlocked"
        } else if self.meets_threshold() {
            "trusted"
        } else {
            "neutral"
        }
    }
}

/// Read one faction's standing off a deployed world.
pub fn read_standing(world: &WorldCell, f: &FactionDef) -> FactionStanding {
    FactionStanding {
        key: f.key.clone(),
        name: f.name.clone(),
        rep: world.read_var(&rep_var(&f.key)),
        threshold: f.threshold,
        ceiling: world.read_var(&ceiling_var(&f.key)),
        trust_ceiling: f.trust_ceiling,
        unlocked: world.read_var(&quest_var(&f.key)) != 0,
        betrayed: world.read_var(&betrayed_var(&f.key)) != 0,
    }
}

/// Read every faction's standing off a deployed world (in roster order).
pub fn read_all(world: &WorldCell, roster: &Roster) -> Vec<FactionStanding> {
    roster
        .factions
        .iter()
        .map(|f| read_standing(world, f))
        .collect()
}

// ── Persistence ─────────────────────────────────────────────────────────────────────────────

/// **A serializable snapshot of a world's faction standing.** Captured off a deployed world,
/// restorable onto a fresh one — the persistence layer a player's standing survives a session on.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StandingSnapshot {
    /// The roster the snapshot was taken against (a restore must use a matching roster).
    pub roster_id: String,
    /// Each faction's standing.
    pub factions: Vec<FactionStanding>,
}

impl StandingSnapshot {
    /// Capture the current standing off `world`.
    pub fn capture(world: &WorldCell, roster: &Roster) -> Self {
        StandingSnapshot {
            roster_id: roster.id.clone(),
            factions: read_all(world, roster),
        }
    }

    /// The captured standing for a faction `key`.
    pub fn faction(&self, key: &str) -> Option<&FactionStanding> {
        self.factions.iter().find(|f| f.key == key)
    }

    /// **Restore the snapshot onto a fresh world.** Deploys `roster` at `seed`, then seeds each
    /// faction's rep / ceiling / unlock / betrayal directly (setup, not turns — the same
    /// `seed_var` path a world's config uses). The reinstated `WriteOnce` seals bite exactly as
    /// they did before the save: a betrayed faction's trial stays refused.
    ///
    /// Errors if the snapshot's roster id does not match `roster` (a snapshot is not portable
    /// across rosters — the slots would not line up).
    pub fn restore(&self, roster: &Roster, seed: u8) -> Result<WorldCell, String> {
        if self.roster_id != roster.id {
            return Err(format!(
                "snapshot roster `{}` does not match `{}`",
                self.roster_id, roster.id
            ));
        }
        let mut world = roster.deploy(seed);
        for fs in &self.factions {
            world.seed_var(&rep_var(&fs.key), Value::Int(fs.rep as i64));
            world.seed_var(&ceiling_var(&fs.key), Value::Int(fs.ceiling as i64));
            world.seed_var(&quest_var(&fs.key), Value::Int(fs.unlocked as i64));
            world.seed_var(&betrayed_var(&fs.key), Value::Int(fs.betrayed as i64));
        }
        Ok(world)
    }
}

/// **Per-identity standing persistence.** Keys [`StandingSnapshot`]s by an identity string (a
/// player key / character id). Serializes whole to JSON — a saved standing ledger the quest /
/// guild / tavern read from and the frontend renders.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct StandingStore {
    entries: BTreeMap<String, StandingSnapshot>,
}

impl StandingStore {
    /// An empty store.
    pub fn new() -> Self {
        StandingStore::default()
    }

    /// Record (or replace) `identity`'s standing.
    pub fn record(&mut self, identity: impl Into<String>, snapshot: StandingSnapshot) {
        self.entries.insert(identity.into(), snapshot);
    }

    /// Capture `world`'s standing under `identity`.
    pub fn record_world(
        &mut self,
        identity: impl Into<String>,
        world: &WorldCell,
        roster: &Roster,
    ) {
        self.record(identity, StandingSnapshot::capture(world, roster));
    }

    /// `identity`'s persisted standing, if any.
    pub fn get(&self, identity: &str) -> Option<&StandingSnapshot> {
        self.entries.get(identity)
    }

    /// The identities with a persisted standing.
    pub fn identities(&self) -> impl Iterator<Item = &String> {
        self.entries.keys()
    }

    /// The number of persisted identities.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the store is empty.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Serialize the whole store to JSON.
    pub fn to_json(&self) -> String {
        serde_json::to_string(self).expect("a standing store serializes")
    }

    /// Restore a store from JSON.
    pub fn from_json(s: &str) -> Result<Self, String> {
        serde_json::from_str(s).map_err(|e| format!("standing store parse: {e}"))
    }
}
