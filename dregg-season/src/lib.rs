//! # `dregg-season` — THE SEASON ABSTRACTION
//!
//! The operating model for The Descent: it runs as **SEASONS** punctuated by
//! protocol upgrades. This crate ties the already-built upgrade pieces —
//! the epoch handshake ([`dregg_epoch`]), the drift taxonomy
//! (`scripts/classify_descriptor_drift.py`), genesis-from-snapshot
//! ([`dregg_genesis_snapshot`]), and the no-cheat leaderboard ([`ugc_dregg`]) —
//! into one coherent Season.
//!
//! ## What a season is
//!
//! A **season is one VK-epoch's run**. A [`Season`] pins an
//! [`EpochManifest`](dregg_epoch::EpochManifest) (its `registry_fp` is the
//! load-bearing VK-epoch identity), names a **content set** (`content_tag`), and
//! carries a **season-scoped** no-cheat leaderboard — a [`ugc_dregg::Registry`],
//! whose every ranked completion provably reaches the win. State (the board, the
//! characters) is scoped to the season.
//!
//! ## What a season boundary is
//!
//! A **season boundary is an upgrade**, classified by the drift taxonomy into one
//! of two [`DriftClass`]es (the two classes `classify_descriptor_drift.py` emits):
//!
//! * **[`DriftClass::TailAppend`]** — new descriptor rows staged at the tail, no
//!   existing member's geometry moved, the deployed VKs are byte-identical: **no
//!   re-genesis**. [`advance_season`] **CONTINUES the same season** — the
//!   `season_id` is unchanged, the leaderboard and characters persist, and only the
//!   epoch tag bumps. A non-breaking upgrade.
//! * **[`DriftClass::GeometryWiden`]** — an existing cohort member's geometry moved
//!   (`trace_width` / the shared PI prefix / membership), so the deployed VK bytes
//!   change and every light client must re-key: a **re-genesis flag-day**. This is
//!   a new VK-epoch — [`advance_season`] **ENDS the season and begins a NEW one**
//!   (a fresh `season_id` + the new epoch, a fresh empty leaderboard).
//!
//! The registry-fingerprint move IS the boundary: a tail-append keeps
//! `registry_fp` ([`dregg_epoch::check_compatibility`] returns `Compatible` — the
//! same VK-epoch); a geometry-widen moves it (`RegistryFpMismatch` — a different
//! VK-epoch). [`epoch_delta_class`] reads exactly this, so the epoch handshake and
//! the drift class agree.
//!
//! ## What carries forward across a boundary
//!
//! A season boundary carries **exactly the opt-in legacy** and resets the rest. The
//! [`CarryForwardPolicy`] decides:
//!
//! * a **HALL-OF-FAME** — the prior season's top-N [`Champion`]s, a durable record
//!   of who won; and/or
//! * a **PRESTIGE** badge — a per-identity, cross-season marker that accrues each
//!   season an identity reaches the hall-of-fame.
//!
//! Both are carried via a real [`GenesisSnapshot`](dregg_genesis_snapshot::GenesisSnapshot)
//! export→seed: each champion / prestige badge is encoded as a content-addressed
//! [`Cell`](dregg_cell::Cell), frozen into a snapshot targeting the new season's
//! genesis, and seeded (validated) into it. The carry therefore **rides
//! genesis-snapshot's tamper-refusal**: a forged hall-of-fame entry (a mutated
//! cell) breaks the migration-voucher binding and is refused on seed. Meanwhile the
//! **active leaderboard and characters RESET** — the new season starts on a fresh
//! empty board.
//!
//! So: a season runs, an upgrade either continues or ends it, and a season boundary
//! carries forward exactly the opt-in legacy while resetting the rest.
//!
//! ## Honest scope
//!
//! REAL here: the season model, the drift-classified boundary (tail-append
//! continues; geometry-widen ends + carries-forward-the-legacy + resets), and the
//! carry-forward over the already-built pieces — driven end-to-end over the real
//! no-cheat board and the real tamper-refusing snapshot.
//!
//! NAMED RESIDUALS (not built here):
//! * **the live wiring** — the bot / node reading the *current* season, and the
//!   operator advancing a season at a real upgrade (feeding the classifier's verdict
//!   into [`advance_season`]);
//! * **the season CONTENT set** — the per-season content ([`SeasonManifest::content_tag`]
//!   is the id; swapping in the actual content is the residual);
//! * **the season schedule / UX** — when a season starts/ends and how it is surfaced.

use std::collections::BTreeMap;
use std::fmt;

use serde::{Deserialize, Serialize};

use dregg_cell::Cell;
use dregg_cell::migration::FederationId;
use dregg_epoch::EpochManifest;
use dregg_genesis_snapshot::{GenesisSnapshot, ImportError, SnapshotError, seed_genesis};
use ugc_dregg::{Registry, UniverseId};

// ═══════════════════════════════════════════════════════════════════════════════
// Drift class — the two classes the descriptor-drift classifier emits.
// ═══════════════════════════════════════════════════════════════════════════════

/// The class of a protocol upgrade — a season boundary's kind. Models the two
/// terminal classes of `scripts/classify_descriptor_drift.py` (its `UNCHANGED`
/// collapses into [`DriftClass::TailAppend`]: both continue the season with no
/// re-genesis). This is the operational question a devnet upgrade asks — *does this
/// change continue a season, or end it?*
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum DriftClass {
    /// New descriptor rows appended at the tail; every existing member keeps its
    /// geometry; the deployed VKs are byte-identical → **no re-genesis**. The season
    /// CONTINUES. (The classifier's `TAIL-APPEND`, and its `UNCHANGED`.)
    TailAppend,
    /// An existing cohort member's geometry moved (`trace_width` / the shared PI
    /// prefix / membership) → the deployed VK bytes change → every light client must
    /// re-key → a **re-genesis flag-day**. The season ENDS; a new one begins. (The
    /// classifier's `GEOMETRY-WIDEN`, its exit code 4.)
    GeometryWiden,
}

impl DriftClass {
    /// Map the classifier's emitted class string (`"UNCHANGED"` / `"TAIL-APPEND"` /
    /// `"GEOMETRY-WIDEN"`) to a [`DriftClass`]. `None` for an unrecognized string.
    /// This is the seam where the operator feeds the CI gate's verdict into
    /// [`advance_season`].
    pub fn from_classifier(class: &str) -> Option<DriftClass> {
        match class {
            "UNCHANGED" | "TAIL-APPEND" => Some(DriftClass::TailAppend),
            "GEOMETRY-WIDEN" => Some(DriftClass::GeometryWiden),
            _ => None,
        }
    }

    /// Whether this upgrade CONTINUES the current season (a tail-append) rather than
    /// ending it into a new one (a geometry-widen). Mirrors the classifier's exit
    /// code: `0` (continue) vs `4` (a wipe-requiring re-genesis).
    pub fn continues_season(&self) -> bool {
        matches!(self, DriftClass::TailAppend)
    }
}

/// Infer the drift class **from the epoch delta itself**: a moved `registry_fp` is a
/// different VK-epoch (a geometry-widen re-genesis); an unchanged one continues the
/// season (a tail-append). This ties the epoch handshake to the drift taxonomy — the
/// same signal [`dregg_epoch::check_compatibility`] keys on (`RegistryFpMismatch`).
pub fn epoch_delta_class(old: &EpochManifest, new: &EpochManifest) -> DriftClass {
    if old.registry_fp != new.registry_fp {
        DriftClass::GeometryWiden
    } else {
        DriftClass::TailAppend
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// Carry-forward policy + the legacy records.
// ═══════════════════════════════════════════════════════════════════════════════

/// The **opt-in** legacy a season boundary carries into the next season. Everything
/// not named here RESETS (the active leaderboard, the characters).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CarryForwardPolicy {
    /// Carry the prior season's **top-N champions** as a durable hall-of-fame. `None`
    /// carries no hall-of-fame.
    pub hall_of_fame_top_n: Option<usize>,
    /// Carry a per-identity **prestige** badge that accrues each honored season.
    pub prestige: bool,
}

impl CarryForwardPolicy {
    /// Carry NOTHING — a clean-slate re-genesis (the baseline wipe).
    pub fn nothing() -> CarryForwardPolicy {
        CarryForwardPolicy {
            hall_of_fame_top_n: None,
            prestige: false,
        }
    }

    /// Carry the top-`n` champions as a hall-of-fame (no prestige).
    pub fn hall_of_fame(n: usize) -> CarryForwardPolicy {
        CarryForwardPolicy {
            hall_of_fame_top_n: Some(n),
            prestige: false,
        }
    }

    /// Also carry a per-identity prestige badge across the boundary.
    pub fn with_prestige(mut self) -> CarryForwardPolicy {
        self.prestige = true;
        self
    }
}

/// A **champion** — one entry of a season's hall-of-fame: an identity that reached
/// the top-N of the season's no-cheat leaderboard, with the verified win it earned
/// its place on. A durable, carry-forward record.
///
/// (No serde: it holds a [`ugc_dregg::UniverseId`], which is not `Serialize`. The
/// tamper-evident on-wire carrier for a champion is its snapshot [`Cell`], not this
/// struct.)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Champion {
    /// The player's display name (from the leaderboard entry).
    pub player: String,
    /// The stable per-identity id derived from the player ([`identity_of`]) — the key
    /// prestige accrues under across seasons.
    pub identity: [u8; 32],
    /// The universe the win was on.
    pub universe: UniverseId,
    /// The verified turns-to-win (lower is better — the rank key).
    pub turns: usize,
    /// The season this win was earned in.
    pub from_season: u64,
    /// The 1-based rank in that season's hall-of-fame.
    pub rank: usize,
}

/// A **prestige** badge — a per-identity, cross-season marker. It accrues each
/// season the identity reaches the hall-of-fame, and remembers their best run.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Prestige {
    /// The stable per-identity id ([`identity_of`]).
    pub identity: [u8; 32],
    /// The player's most-recent display name.
    pub player: String,
    /// How many seasons this identity has reached the hall-of-fame.
    pub seasons_honored: u64,
    /// The best (lowest) turns-to-win across all honored seasons.
    pub best_turns: usize,
}

/// The stable per-identity id for a player — a domain-separated hash of their name.
/// Deterministic, so the same player carries the same prestige across seasons.
pub fn identity_of(player: &str) -> [u8; 32] {
    blake3::derive_key("dregg-season:identity v1", player.as_bytes())
}

// ═══════════════════════════════════════════════════════════════════════════════
// The season manifest.
// ═══════════════════════════════════════════════════════════════════════════════

/// A season's self-description: which VK-epoch it runs, what content it themes, when
/// it started, and what it carries forward when it ends.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SeasonManifest {
    /// The season number (monotone; a geometry-widen boundary increments it).
    pub season_id: u64,
    /// The VK-epoch this season is pinned to. Its `registry_fp` is the load-bearing
    /// identity — a season runs exactly one epoch, and an epoch DELTA (a moved
    /// `registry_fp`) is the season boundary.
    pub epoch: EpochManifest,
    /// The season's content set / theme id (the per-season content is a named
    /// residual; this is its handle).
    pub content_tag: String,
    /// When the season started (a height / timestamp — the operator's clock).
    pub started_at: u64,
    /// What this season carries forward when it ends.
    pub carry_forward: CarryForwardPolicy,
}

// ═══════════════════════════════════════════════════════════════════════════════
// The season.
// ═══════════════════════════════════════════════════════════════════════════════

/// A **season** — one VK-epoch's run of The Descent: its [`SeasonManifest`], its
/// season-scoped no-cheat leaderboard (a [`ugc_dregg::Registry`]), and the carried
/// legacy (the hall-of-fame + prestige seeded from the prior season).
pub struct Season {
    /// The season's manifest (epoch + content + policy).
    pub manifest: SeasonManifest,
    /// The **season-scoped** no-cheat leaderboard. Every ranked completion provably
    /// reaches the win. Persists across a tail-append; RESET (fresh, empty) on a
    /// geometry-widen boundary.
    pub board: Registry,
    /// The hall-of-fame carried into this season (the prior season's champions).
    /// Empty for a genesis season.
    pub hall_of_fame: Vec<Champion>,
    /// The per-identity prestige badges accrued across seasons, keyed by identity.
    pub prestige: BTreeMap<[u8; 32], Prestige>,
}

impl Season {
    /// Begin a **genesis season** — season `season_id` on `epoch`, an empty board, no
    /// carried legacy.
    pub fn genesis(
        season_id: u64,
        epoch: EpochManifest,
        content_tag: impl Into<String>,
        started_at: u64,
        carry_forward: CarryForwardPolicy,
    ) -> Season {
        Season {
            manifest: SeasonManifest {
                season_id,
                epoch,
                content_tag: content_tag.into(),
                started_at,
                carry_forward,
            },
            board: Registry::new(),
            hall_of_fame: Vec::new(),
            prestige: BTreeMap::new(),
        }
    }

    /// The season number.
    pub fn season_id(&self) -> u64 {
        self.manifest.season_id
    }

    /// This season's federation id — the id of the chain that hosts it. Derived from
    /// the season number + the epoch's `registry_fp`, modeling "new committee keys →
    /// a new `federation_id`" at each geometry-widen re-genesis. It is the
    /// source/target a carry-forward snapshot binds.
    pub fn federation_id(&self) -> FederationId {
        season_federation_id(self.manifest.season_id, &self.manifest.epoch)
    }

    /// The season's **top-`n` champions**, gathered across every universe on the
    /// season-scoped board and ranked by turns-to-win (ascending). These are the
    /// hall-of-fame a geometry-widen boundary carries forward.
    pub fn champions(&self, top_n: usize) -> Vec<Champion> {
        let mut all: Vec<(String, UniverseId, usize)> = Vec::new();
        for u in self.board.universes() {
            let id = u.id();
            for e in self.board.leaderboard(id) {
                all.push((e.player.clone(), id, e.turns));
            }
        }
        // Lower turns rank higher; stable for ties (insertion order preserved).
        all.sort_by_key(|(_, _, turns)| *turns);
        all.into_iter()
            .take(top_n)
            .enumerate()
            .map(|(i, (player, universe, turns))| Champion {
                identity: identity_of(&player),
                player,
                universe,
                turns,
                from_season: self.manifest.season_id,
                rank: i + 1,
            })
            .collect()
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// The season boundary.
// ═══════════════════════════════════════════════════════════════════════════════

/// The outcome of [`advance_season`] — an upgrade either continued the season or
/// ended it into a new one.
pub enum SeasonTransition {
    /// A **TAIL-APPEND**: the SAME season continues. The `season_id`, the board, the
    /// hall-of-fame and the prestige are unchanged; only the epoch tag bumped.
    Continued(Season),
    /// A **GEOMETRY-WIDEN**: the season ENDED and a NEW one began. The carried legacy
    /// was seeded into the new season from `carry`; the active board is fresh + empty.
    Boundary {
        /// The new season (fresh board; carried hall-of-fame + prestige).
        season: Season,
        /// The genesis snapshot that carried the legacy forward — the tamper-evident
        /// carrier. Re-seeding it validates the carry; forging any carried cell makes
        /// [`seed_genesis`] refuse it.
        carry: GenesisSnapshot,
        /// How many cells the snapshot carried (champions + prestige badges).
        carried_cells: usize,
    },
}

impl SeasonTransition {
    /// Whether the upgrade ended the season into a new one (a geometry-widen).
    pub fn is_boundary(&self) -> bool {
        matches!(self, SeasonTransition::Boundary { .. })
    }

    /// The resulting season (continued or new).
    pub fn season(&self) -> &Season {
        match self {
            SeasonTransition::Continued(s) => s,
            SeasonTransition::Boundary { season, .. } => season,
        }
    }

    /// Consume the transition and take the resulting season.
    pub fn into_season(self) -> Season {
        match self {
            SeasonTransition::Continued(s) => s,
            SeasonTransition::Boundary { season, .. } => season,
        }
    }
}

/// **THE SEASON BOUNDARY.** Advance `current` across a protocol upgrade to
/// `new_epoch`, classified by `drift`:
///
/// * [`DriftClass::TailAppend`] — CONTINUE the same season: bump the epoch tag, keep
///   the `season_id`, the leaderboard, the characters, the carried legacy. A
///   non-breaking upgrade.
/// * [`DriftClass::GeometryWiden`] — END the season and begin a NEW one: a fresh
///   `season_id` + `new_epoch`, a fresh EMPTY board. The [`CarryForwardPolicy`]
///   decides the opt-in legacy — the top-N hall-of-fame and/or per-identity prestige
///   — which is carried via a [`GenesisSnapshot`] export→seed (so a forged carry is
///   refused), while the active board + characters reset.
///
/// `started_at` stamps the new season's start (ignored on a tail-append — the season
/// did not restart).
pub fn advance_season(
    current: Season,
    new_epoch: EpochManifest,
    drift: DriftClass,
    started_at: u64,
) -> Result<SeasonTransition, SeasonError> {
    match drift {
        // ── A TAIL-APPEND CONTINUES THE SAME SEASON ──────────────────────────────
        DriftClass::TailAppend => {
            let mut s = current;
            // The epoch tag bumps (new staged rows / caveat tags), but the VK-epoch
            // identity (registry_fp) is the same — non-breaking. The season_id, the
            // board, the characters, and the carried legacy all persist.
            s.manifest.epoch = new_epoch;
            Ok(SeasonTransition::Continued(s))
        }

        // ── A GEOMETRY-WIDEN ENDS THE SEASON → A NEW SEASON ─────────────────────
        DriftClass::GeometryWiden => {
            let policy = current.manifest.carry_forward.clone();
            let content_tag = current.manifest.content_tag.clone();
            let new_season_id = current.manifest.season_id + 1;

            // 1. The hall-of-fame: the prior season's top-N champions.
            let champions = match policy.hall_of_fame_top_n {
                Some(n) => current.champions(n),
                None => Vec::new(),
            };

            // 2. Prestige accrual: start from the prior season's badges (carried) and
            //    +1 each identity that just reached the hall-of-fame.
            let mut prestige = if policy.prestige {
                current.prestige.clone()
            } else {
                BTreeMap::new()
            };
            if policy.prestige {
                for c in &champions {
                    let badge = prestige.entry(c.identity).or_insert_with(|| Prestige {
                        identity: c.identity,
                        player: c.player.clone(),
                        seasons_honored: 0,
                        best_turns: usize::MAX,
                    });
                    badge.seasons_honored += 1;
                    badge.best_turns = badge.best_turns.min(c.turns);
                    badge.player = c.player.clone();
                }
            }

            // 3. Encode the legacy as content-addressed cells and freeze them into a
            //    snapshot targeting the NEW season's genesis (source = the old
            //    season's chain, target = the new season's chain).
            let source_fed = current.federation_id();
            let target_fed = season_federation_id(new_season_id, &new_epoch);
            let mut cells: Vec<Cell> = Vec::new();
            for c in &champions {
                cells.push(champion_cell(c));
            }
            // Prestige badges carry deterministically (BTreeMap iteration is sorted).
            for p in prestige.values() {
                cells.push(prestige_cell(p));
            }

            let carry = GenesisSnapshot::export(source_fed, target_fed, started_at, &cells)
                .map_err(SeasonError::Export)?;

            // 4. SEED the new genesis from the snapshot — validates every carried cell
            //    (content-address stability + freeze-state voucher binding). A carry
            //    forged AFTER freeze is refused HERE. The honest legacy seeds cleanly.
            let seeded = seed_genesis(&carry, target_fed).map_err(SeasonError::Import)?;
            let carried_cells = seeded.cells.len();

            // 5. The new season: a fresh EMPTY board (the active leaderboard + the
            //    characters reset), carrying only the opt-in legacy.
            let season = Season {
                manifest: SeasonManifest {
                    season_id: new_season_id,
                    epoch: new_epoch,
                    content_tag,
                    started_at,
                    carry_forward: policy,
                },
                board: Registry::new(),
                hall_of_fame: champions,
                prestige,
            };

            Ok(SeasonTransition::Boundary {
                season,
                carry,
                carried_cells,
            })
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// Cell encoding — a carried champion / prestige badge is a content-addressed cell.
// ═══════════════════════════════════════════════════════════════════════════════

/// Pack a `u64` into a 32-byte cell field's canonical u64 lane (`dregg_cell::field_from_u64`,
/// big-endian bytes `24..32`).
///
/// ⚠ Was little-endian into bytes `0..8`. These values go into `cell.state.fields[0..3]` — the
/// FIXED octet the deployed `setFieldVmDescriptor2-{slot}R24` completion-freezes — so a `0..8`
/// write made the badge cell's fields unprovable and invisible to every kernel-side reader.
/// Gate: `circuit/tests/setfield_encoder_window_gate.rs`.
fn u64_field(v: u64) -> [u8; 32] {
    dregg_cell::field_from_u64(v)
}

/// Encode a [`Champion`] as a content-addressed [`Cell`]. The identity is the cell's
/// public key; the token binds `(season, universe, rank)` so each champion record is
/// a distinct cell; the verified score rides in the balance + state. The snapshot's
/// voucher binds this exact state, so a forged champion is refused on seed.
fn champion_cell(c: &Champion) -> Cell {
    let mut km = Vec::with_capacity(48);
    km.extend_from_slice(&c.from_season.to_le_bytes());
    km.extend_from_slice(c.universe.as_bytes());
    km.extend_from_slice(&(c.rank as u64).to_le_bytes());
    let token = blake3::derive_key("dregg-season:champion-token v1", &km);
    let mut cell = Cell::with_balance(c.identity, token, c.turns as i64);
    cell.state.fields[0] = u64_field(c.from_season);
    cell.state.fields[1] = u64_field(c.rank as u64);
    cell.state.fields[2] = *c.universe.as_bytes();
    cell.state.fields[3] = u64_field(c.turns as u64);
    cell
}

/// Encode a [`Prestige`] badge as a content-addressed [`Cell`]. The token is stable
/// per identity (only the identity keys it), so an identity's badge is the same cell
/// slot across seasons; its accrued count rides in the balance + state.
fn prestige_cell(p: &Prestige) -> Cell {
    let token = blake3::derive_key("dregg-season:prestige-token v1", &p.identity);
    let mut cell = Cell::with_balance(p.identity, token, p.seasons_honored as i64);
    cell.state.fields[0] = u64_field(p.seasons_honored);
    cell.state.fields[1] = u64_field(p.best_turns as u64);
    cell
}

/// A season's federation id — the id of the chain hosting it. Derived from the
/// season number + the epoch's `registry_fp` (a geometry-widen moves `registry_fp`,
/// so a new season mints a new federation id).
fn season_federation_id(season_id: u64, epoch: &EpochManifest) -> FederationId {
    let mut km = Vec::with_capacity(8 + epoch.registry_fp.len());
    km.extend_from_slice(&season_id.to_le_bytes());
    km.extend_from_slice(epoch.registry_fp.as_bytes());
    blake3::derive_key("dregg-season:federation-id v1", &km)
}

// ═══════════════════════════════════════════════════════════════════════════════
// Errors.
// ═══════════════════════════════════════════════════════════════════════════════

/// Why a season boundary could not carry its legacy forward.
#[derive(Debug)]
pub enum SeasonError {
    /// The carry-forward snapshot could not be exported (a broken carried cell).
    Export(SnapshotError),
    /// The carry-forward snapshot did not seed the new genesis — a carried cell
    /// failed validation (a forged legacy record). Rides genesis-snapshot's
    /// tamper-refusal.
    Import(ImportError),
}

impl fmt::Display for SeasonError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SeasonError::Export(e) => write!(f, "season carry-forward export failed: {e}"),
            SeasonError::Import(e) => write!(f, "season carry-forward seed refused: {e}"),
        }
    }
}

impl std::error::Error for SeasonError {}

impl From<SnapshotError> for SeasonError {
    fn from(e: SnapshotError) -> Self {
        SeasonError::Export(e)
    }
}

impl From<ImportError> for SeasonError {
    fn from(e: ImportError) -> Self {
        SeasonError::Import(e)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A local epoch to pin a season to (derived from the real baked constants).
    fn epoch() -> EpochManifest {
        dregg_epoch::local_manifest()
    }

    /// A tail-append successor epoch: the VK-epoch identity (registry_fp) is
    /// UNCHANGED (existing VKs byte-identical) but the tag bumps (a staged tail row).
    fn tail_append_epoch() -> EpochManifest {
        let mut e = epoch();
        e.descriptor_set_tag = format!("{}+tail1", e.descriptor_set_tag);
        e.known_caveat_tags.insert(22); // a staged new caveat tag rides in the tail
        e
    }

    /// A geometry-widen successor epoch: the registry_fp MOVES → a new VK-epoch.
    fn geometry_widen_epoch() -> EpochManifest {
        let mut e = epoch();
        e.registry_fp = "cafebabe".repeat(8); // a different deployed cohort
        e.descriptor_set_tag = "v14-geom/w204/r24".to_string();
        e
    }

    #[test]
    fn drift_class_maps_the_classifier_output() {
        assert_eq!(
            DriftClass::from_classifier("TAIL-APPEND"),
            Some(DriftClass::TailAppend)
        );
        assert_eq!(
            DriftClass::from_classifier("UNCHANGED"),
            Some(DriftClass::TailAppend)
        );
        assert_eq!(
            DriftClass::from_classifier("GEOMETRY-WIDEN"),
            Some(DriftClass::GeometryWiden)
        );
        assert_eq!(DriftClass::from_classifier("nonsense"), None);
        assert!(DriftClass::TailAppend.continues_season());
        assert!(!DriftClass::GeometryWiden.continues_season());
    }

    #[test]
    fn epoch_delta_class_agrees_with_the_handshake() {
        // A tail-append keeps registry_fp (Compatible); a geometry-widen moves it.
        let base = epoch();
        assert_eq!(
            epoch_delta_class(&base, &tail_append_epoch()),
            DriftClass::TailAppend
        );
        assert_eq!(
            epoch_delta_class(&base, &geometry_widen_epoch()),
            DriftClass::GeometryWiden
        );
        // The handshake keys on the same signal.
        assert!(dregg_epoch::check_compatibility(&base, &base).is_compatible());
        assert!(matches!(
            dregg_epoch::check_compatibility(&base, &geometry_widen_epoch()),
            dregg_epoch::EpochCompat::RegistryFpMismatch { .. }
        ));
    }

    #[test]
    fn genesis_season_starts_empty() {
        let s = Season::genesis(
            1,
            epoch(),
            "the-descent:s1",
            1000,
            CarryForwardPolicy::hall_of_fame(3).with_prestige(),
        );
        assert_eq!(s.season_id(), 1);
        assert!(s.hall_of_fame.is_empty());
        assert!(s.prestige.is_empty());
        assert!(s.champions(3).is_empty());
    }

    #[test]
    fn federation_id_moves_only_on_a_geometry_widen() {
        let s1 = Season::genesis(1, epoch(), "s1", 0, CarryForwardPolicy::nothing());
        // Same epoch, same season → same fed id.
        let s1b = Season::genesis(1, epoch(), "s1", 0, CarryForwardPolicy::nothing());
        assert_eq!(s1.federation_id(), s1b.federation_id());
        // A new season on a widened epoch → a different fed id.
        let s2 = Season::genesis(
            2,
            geometry_widen_epoch(),
            "s2",
            0,
            CarryForwardPolicy::nothing(),
        );
        assert_ne!(s1.federation_id(), s2.federation_id());
    }
}
