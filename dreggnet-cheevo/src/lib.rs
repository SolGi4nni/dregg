//! # `dreggnet-cheevo` — un-fakeable, SOULBOUND achievements over verified runs.
//!
//! THE CROWN of the game-infra roadmap. An **achievement** is not a claim a client
//! asserts — it is an **anchored predicate over a verified run**, re-checkable by anyone:
//!
//! * **reached-depth `>= N`** — the run's `depth` var peaked at or above `N`;
//! * **a no-death clear** — the run WON and a hazard flag (`dead` / `shield_broken`)
//!   was never tripped over the whole trajectory;
//! * **a speed clear** — the run WON in `<= max_turns` verified turns;
//! * **a season-champion** — the identity reached the top-N of a season's no-cheat
//!   hall-of-fame (itself built only from verified wins).
//!
//! ## The two teeth
//!
//! **Earned, not claimed.** [`CheevoLedger::earn`] first runs `ugc-dregg`'s
//! [`verify_completion`] — the no-cheat gate that RE-EXECUTES the submitted run against a
//! fresh, identically-seeded world and requires it reach the declared win. A forged /
//! edited / incomplete run is REFUSED here ([`CheevoError::RunRejected`]) and earns
//! nothing. Only then is the anchored predicate evaluated over the run's *real committed
//! trajectory* (the per-step slot vectors the replay verifier vouched are faithful). A
//! run that verifies but does not satisfy the predicate earns nothing
//! ([`CheevoError::PredicateNotMet`]) — the predicate is NON-VACUOUS.
//!
//! **Soulbound, not tradeable.** An earned cheevo MINTS a [`dreggnet_asset`] note owned
//! by the earner, but a cheevo has **no transfer path**: [`CheevoLedger::attempt_transfer`]
//! is refused unconditionally ([`CheevoError::Soulbound`]) — a cheevo can't be sold. The
//! note stays owner-bound (the ledger exposes no owner-change), and each cheevo carries a
//! **seal** — a content address over `earner | achievement | universe | run | witness`.
//! [`CheevoLedger::reverify_run`] re-runs the whole gate + re-derives the seal, so a
//! tampered / re-bound (laundered onto a buyer) cheevo record is refused
//! ([`CheevoError::Tampered`]).
//!
//! ## Provenance-bound
//!
//! A cheevo carries the [`Cheevo::completion_id`] (the run anchor over the receipt chain)
//! and the [`Cheevo::witness`] (WHY it was earned — the peak depth, the turn count, the
//! championship rank), so it is a re-verifiable PROOF you earned it, not a badge someone
//! handed you.
//!
//! ## Honest scope + named residuals
//!
//! REAL here: the anchored predicates over the ugc no-cheat verify (a forged run earns
//! nothing), the non-vacuous predicate evaluation over the run's real trajectory, and the
//! soulbound mint (earned, un-transferable, provenance-bound) — all DRIVEN in
//! `tests/cheevos.rs`. The earner identity is the deterministic per-player key; soulbound
//! is enforced at THIS layer (no transfer method + the seal binding), which is the honest
//! resolution of the property today.
//!
//! NAMED RESIDUALS (not built here):
//! * **A ZK-proof-backed cheevo** (Lane-D-gated) — prove the achievement predicate WITHOUT
//!   revealing the run. The predicate + the soulbound mint are buildable now against the
//!   replay-verify; the succinct proof of the predicate is the frontier. (ugc's
//!   `verify_proof_completion` already gives an O(1) win-proof path; a predicate circuit
//!   over the trajectory is the missing leg.)
//! * **An executor-level soulbound note program** — a `WriteOnce(owner)` cell program that
//!   refuses a transfer turn cryptographically at the ISA (vs. this layer's refusal).
//! * **The Solana NFT export** — minting an earned cheevo out as an on-chain soulbound NFT.
//! * **A whole attested cheevo tree** — an accumulator of an identity's cheevos.

use blake3::Hasher;
use dregg_season::{Champion, Season};
use dreggnet_asset::{AssetId, AssetWorld};
use spween_dregg::{Playthrough, compile_scene, parse};
use ugc_dregg::{Completion, RejectReason, Universe, UniverseId, verify_completion};

/// Domain tag for the run anchor (over the player + the receipt chain).
const DOMAIN_RUN_ANCHOR: &[u8] = b"dreggnet-cheevo/run-anchor/v1";
/// Domain tag for a champion anchor (over the season + universe + identity + turns).
const DOMAIN_CHAMPION_ANCHOR: &[u8] = b"dreggnet-cheevo/champion-anchor/v1";
/// Domain tag for the soulbound seal (binds earner|achievement|universe|run|witness).
const DOMAIN_SEAL: &[u8] = b"dreggnet-cheevo/soulbound-seal/v1";

// ═══════════════════════════════════════════════════════════════════════════════
// The achievement predicate.
// ═══════════════════════════════════════════════════════════════════════════════

/// An **anchored achievement predicate** — the shape of an un-fakeable achievement. Each
/// is a predicate over a VERIFIED run (or, for [`Achievement::SeasonChampion`], over a
/// season's no-cheat hall-of-fame). The `var`/`flag` name a spween scene variable read
/// off the run's real committed trajectory (the same projection the executor uses).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Achievement {
    /// **Reached depth.** The run's `var` (e.g. `"depth"`) peaked at `>= min` at some
    /// point in the trajectory. (The run need not still be at that depth at the win.)
    ReachedDepth {
        /// The scene variable that tracks depth.
        var: String,
        /// The minimum peak depth to earn the cheevo.
        min: u64,
    },
    /// **A no-death (flawless) clear.** The run WON (guaranteed by the no-cheat gate) and
    /// `flag` (e.g. `"dead"` or `"shield_broken"`) was `0` across the ENTIRE trajectory —
    /// the hazard was never tripped. A run that won but tripped the flag earns nothing.
    NoDeathClear {
        /// The hazard flag that must have stayed `0` for the whole run.
        flag: String,
    },
    /// **A speed clear.** The run WON in `<= max_turns` verified turns (the verified move
    /// count, bound by the no-cheat gate — a lied turn count was already refused there).
    SpeedClear {
        /// The maximum verified turns to earn the cheevo.
        max_turns: usize,
    },
    /// **A season champion.** The identity reached the top-`top_n` of a season's no-cheat
    /// hall-of-fame — earned via [`CheevoLedger::earn_champion`], since it is a predicate
    /// over the whole season board (every entry of which provably reached the win), not a
    /// single completion.
    SeasonChampion {
        /// The hall-of-fame cutoff.
        top_n: usize,
    },
}

impl Achievement {
    /// A stable slug for the achievement kind (for display / indexing).
    pub fn slug(&self) -> &'static str {
        match self {
            Achievement::ReachedDepth { .. } => "reached-depth",
            Achievement::NoDeathClear { .. } => "no-death-clear",
            Achievement::SpeedClear { .. } => "speed-clear",
            Achievement::SeasonChampion { .. } => "season-champion",
        }
    }
}

/// **Why** an achievement was earned — the evidence the predicate produced over the
/// verified run. Part of a cheevo's provenance (re-derivable on [`CheevoLedger::reverify_run`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Witness {
    /// The peak depth the run actually reached (>= the required `min`).
    Depth {
        /// The observed peak of the depth var over the trajectory.
        peak: u64,
        /// The `min` the achievement required.
        min: u64,
    },
    /// The hazard flag stayed `0` for the whole (winning) run.
    NoDeath {
        /// The flag that was never tripped.
        flag: String,
    },
    /// The run won in `turns` verified turns (<= the required `max_turns`).
    Speed {
        /// The verified turn count.
        turns: usize,
        /// The `max_turns` the achievement required.
        max_turns: usize,
    },
    /// The identity placed at `rank` in the season's top-`top_n` hall-of-fame.
    Champion {
        /// The hall-of-fame cutoff.
        top_n: usize,
        /// The 1-based rank achieved.
        rank: usize,
        /// The verified turns of the championship run.
        turns: usize,
    },
}

/// Serialize a witness into the seal (a canonical, injective byte encoding).
fn witness_bytes(w: &Witness) -> Vec<u8> {
    let mut v = Vec::new();
    match w {
        Witness::Depth { peak, min } => {
            v.push(0);
            v.extend_from_slice(&peak.to_le_bytes());
            v.extend_from_slice(&min.to_le_bytes());
        }
        Witness::NoDeath { flag } => {
            v.push(1);
            v.extend_from_slice(&(flag.len() as u64).to_le_bytes());
            v.extend_from_slice(flag.as_bytes());
        }
        Witness::Speed { turns, max_turns } => {
            v.push(2);
            v.extend_from_slice(&(*turns as u64).to_le_bytes());
            v.extend_from_slice(&(*max_turns as u64).to_le_bytes());
        }
        Witness::Champion { top_n, rank, turns } => {
            v.push(3);
            v.extend_from_slice(&(*top_n as u64).to_le_bytes());
            v.extend_from_slice(&(*rank as u64).to_le_bytes());
            v.extend_from_slice(&(*turns as u64).to_le_bytes());
        }
    }
    v
}

/// Serialize an achievement into the seal (a canonical, injective byte encoding).
fn achievement_bytes(a: &Achievement) -> Vec<u8> {
    let mut v = Vec::new();
    match a {
        Achievement::ReachedDepth { var, min } => {
            v.push(0);
            v.extend_from_slice(&(var.len() as u64).to_le_bytes());
            v.extend_from_slice(var.as_bytes());
            v.extend_from_slice(&min.to_le_bytes());
        }
        Achievement::NoDeathClear { flag } => {
            v.push(1);
            v.extend_from_slice(&(flag.len() as u64).to_le_bytes());
            v.extend_from_slice(flag.as_bytes());
        }
        Achievement::SpeedClear { max_turns } => {
            v.push(2);
            v.extend_from_slice(&(*max_turns as u64).to_le_bytes());
        }
        Achievement::SeasonChampion { top_n } => {
            v.push(3);
            v.extend_from_slice(&(*top_n as u64).to_le_bytes());
        }
    }
    v
}

// ═══════════════════════════════════════════════════════════════════════════════
// The earned cheevo.
// ═══════════════════════════════════════════════════════════════════════════════

/// An **earned achievement** — a re-verifiable PROOF, minted as a soulbound asset. Bound
/// to the earner (the note owner + the seal), carrying the provenance of the verified run
/// it is a predicate over.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cheevo {
    /// The predicate that was satisfied.
    pub achievement: Achievement,
    /// Why it was earned (peak depth / turn count / rank) — re-derivable on reverify.
    pub witness: Witness,
    /// The identity this cheevo is SOULBOUND to (the minted note's owner key,
    /// deterministic in the player). No transfer path can move it away.
    pub earner: [u8; 32],
    /// The player's display name.
    pub player: String,
    /// The universe the run was on.
    pub universe: UniverseId,
    /// The run anchor — a content address over the player + the run's receipt chain (or,
    /// for a champion, over the season+universe+identity+turns). The provenance handle.
    pub completion_id: [u8; 32],
    /// The verified turns-to-win of the run that earned it.
    pub turns: usize,
    /// The SOULBOUND asset minted for this cheevo — a `dreggnet-asset` note owned by the
    /// earner, content-addressed by the seal.
    pub note: AssetId,
    /// The soulbound seal — `blake3(earner | achievement | universe | run | witness)`. The
    /// note's mint seed, and the tamper check: a re-bound/edited cheevo fails to re-derive it.
    pub seal: [u8; 32],
}

impl Cheevo {
    /// Whether this cheevo's stored [`Cheevo::seal`] is the genuine content address of its
    /// fields — a cheap integrity check (a record whose earner/achievement/witness was
    /// edited no longer matches its seal).
    pub fn seal_intact(&self) -> bool {
        seal_of(
            &self.earner,
            &self.achievement,
            self.universe,
            &self.completion_id,
            &self.witness,
        ) == self.seal
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// Errors — every arm a real refusal.
// ═══════════════════════════════════════════════════════════════════════════════

/// Why a cheevo could not be earned or re-verified. Every arm is a real refusal — a cheevo
/// is un-fakeable + soulbound by construction.
#[derive(Clone, Debug)]
pub enum CheevoError {
    /// **The anchored run failed the ugc no-cheat verify** — a forged / edited / incomplete
    /// / result-tampered run. It earns NOTHING. This is the no-cheat tooth biting.
    RunRejected(RejectReason),
    /// The run verified, but it **does not satisfy the achievement predicate** (the peak
    /// depth was too shallow, the hazard was tripped, the clear was too slow). NON-VACUOUS.
    PredicateNotMet(String),
    /// The achievement names a variable the universe's scene does not define — the
    /// predicate is not evaluable against this universe.
    UnknownVar(String),
    /// **A cheevo cannot be transferred.** Soulbound: there is no sell path.
    Soulbound,
    /// The player is not a top-N champion of the given season.
    NotAChampion,
    /// **A re-verified cheevo record is tampered** — its seal does not re-derive, its
    /// witness does not match the re-checked run, or the soulbound note is no longer owned
    /// by the earner. A laundered / forged cheevo record is refused here.
    Tampered(String),
}

impl std::fmt::Display for CheevoError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CheevoError::RunRejected(r) => write!(f, "the anchored run is not a verified win: {r}"),
            CheevoError::PredicateNotMet(why) => {
                write!(f, "the run verified but did not earn the cheevo: {why}")
            }
            CheevoError::UnknownVar(v) => {
                write!(f, "the universe's scene defines no variable `{v}`")
            }
            CheevoError::Soulbound => {
                write!(
                    f,
                    "a cheevo is soulbound — it cannot be transferred or sold"
                )
            }
            CheevoError::NotAChampion => {
                write!(f, "the player is not a top-N champion of the season")
            }
            CheevoError::Tampered(why) => write!(f, "the cheevo record is tampered: {why}"),
        }
    }
}

impl std::error::Error for CheevoError {}

// ═══════════════════════════════════════════════════════════════════════════════
// The cheevo ledger.
// ═══════════════════════════════════════════════════════════════════════════════

/// The **soulbound cheevo ledger** — earns achievements over verified runs and mints them
/// as soulbound assets. It owns a [`dreggnet_asset::AssetWorld`] for the minted notes, but
/// exposes NO transfer path: a cheevo, once earned, stays bound to its earner.
pub struct CheevoLedger {
    assets: AssetWorld,
    minted: Vec<Cheevo>,
}

impl Default for CheevoLedger {
    fn default() -> Self {
        Self::new()
    }
}

impl CheevoLedger {
    /// A fresh cheevo ledger (no cheevos minted).
    pub fn new() -> CheevoLedger {
        CheevoLedger {
            assets: AssetWorld::new(),
            minted: Vec::new(),
        }
    }

    /// **EARN a cheevo** for `achievement` from a real run:
    ///
    /// 1. **The no-cheat gate.** Run [`verify_completion`] — re-execute `completion`
    ///    against a fresh identically-seeded world and require it reach the win. A forged /
    ///    edited / incomplete / result-tampered run is REFUSED ([`CheevoError::RunRejected`])
    ///    and earns nothing.
    /// 2. **The anchored predicate.** Evaluate `achievement` over the run's real committed
    ///    trajectory. A run that verifies but does not satisfy it earns nothing
    ///    ([`CheevoError::PredicateNotMet`]).
    /// 3. **The soulbound mint.** Mint a `dreggnet-asset` note owned by the earner,
    ///    content-addressed by the seal, carrying the run's provenance.
    ///
    /// Idempotent by seal: earning the same achievement on the same run returns the
    /// existing cheevo (it does not double-mint).
    pub fn earn(
        &mut self,
        universe: &Universe,
        completion: &Completion,
        achievement: Achievement,
    ) -> Result<Cheevo, CheevoError> {
        // (1) THE NO-CHEAT GATE. A forged / insufficient run dies here.
        let turns = verify_completion(universe, completion).map_err(CheevoError::RunRejected)?;

        // (2) THE ANCHORED PREDICATE over the verified trajectory.
        let witness = eval_run_predicate(universe, completion, &achievement)?;

        // (3) THE SOULBOUND MINT, bound to the earner + the run's provenance.
        let player = completion.player.clone();
        let anchor = run_anchor(&player, &completion.play);
        Ok(self.mint_cheevo(achievement, witness, player, universe.id(), anchor, turns))
    }

    /// **EARN a season-champion cheevo** — the champion predicate over a season's no-cheat
    /// hall-of-fame. `season.champions(top_n)` is derived ENTIRELY from the season's board
    /// (a [`ugc_dregg::Registry`]), every entry of which already passed the no-cheat verify
    /// — so a championship is backed by verified wins. A player who did not place top-`top_n`
    /// earns nothing ([`CheevoError::NotAChampion`]).
    pub fn earn_champion(
        &mut self,
        season: &Season,
        player: &str,
        top_n: usize,
    ) -> Result<Cheevo, CheevoError> {
        let champions = season.champions(top_n);
        let champ = champions
            .iter()
            .find(|c| c.player == player)
            .ok_or(CheevoError::NotAChampion)?;

        let achievement = Achievement::SeasonChampion { top_n };
        let witness = Witness::Champion {
            top_n,
            rank: champ.rank,
            turns: champ.turns,
        };
        let anchor = champion_anchor(champ);
        Ok(self.mint_cheevo(
            achievement,
            witness,
            player.to_string(),
            champ.universe,
            anchor,
            champ.turns,
        ))
    }

    /// Mint (or return the idempotent existing) cheevo — the shared soulbound-mint tail.
    fn mint_cheevo(
        &mut self,
        achievement: Achievement,
        witness: Witness,
        player: String,
        universe: UniverseId,
        anchor: [u8; 32],
        turns: usize,
    ) -> Cheevo {
        let earner = self.assets.pubkey_of(&player);
        let seal = seal_of(&earner, &achievement, universe, &anchor, &witness);

        // Idempotent: the seal is the identity of a (player, achievement, run) cheevo.
        if let Some(existing) = self.minted.iter().find(|c| c.seal == seal) {
            return existing.clone();
        }

        // The soulbound note: a dreggnet-asset note owned by the earner, content-addressed
        // by the seal (its mint seed). The ledger exposes no path to move its ownership.
        let note = self.assets.mint(&player, &seal);
        let cheevo = Cheevo {
            achievement,
            witness,
            earner,
            player,
            universe,
            completion_id: anchor,
            turns,
            note,
            seal,
        };
        self.minted.push(cheevo.clone());
        cheevo
    }

    /// **THE SOULBOUND TOOTH.** A cheevo cannot be transferred or sold — the transfer path
    /// is refused unconditionally. (Contrast a plain [`dreggnet_asset`] note, whose owner
    /// CAN sign a transfer; a cheevo has no such path.) Always [`CheevoError::Soulbound`].
    pub fn attempt_transfer(&self, _cheevo: &Cheevo, _to: &str) -> Result<(), CheevoError> {
        Err(CheevoError::Soulbound)
    }

    /// **INDEPENDENTLY re-verify** an earned run-cheevo — anyone can run this against the
    /// public universe + the recorded run:
    ///
    /// 1. the seal re-derives (the record is not tampered / re-bound to a buyer);
    /// 2. the anchored run RE-PASSES the ugc no-cheat verify (still a verified win);
    /// 3. the predicate RE-HOLDS over the run (the same witness);
    /// 4. the run anchor matches (this cheevo is for THIS run);
    /// 5. the soulbound note is still owned by the earner (ownership never moved).
    ///
    /// A tampered / laundered / forged cheevo is refused ([`CheevoError::Tampered`]).
    pub fn reverify_run(
        &self,
        cheevo: &Cheevo,
        universe: &Universe,
        completion: &Completion,
    ) -> Result<(), CheevoError> {
        // (1) Seal integrity — a re-bound (earner swapped to a buyer) or edited record fails.
        if !cheevo.seal_intact() {
            return Err(CheevoError::Tampered(
                "seal does not match the record's fields".into(),
            ));
        }
        // (2) The run re-passes the no-cheat verify.
        verify_completion(universe, completion).map_err(CheevoError::RunRejected)?;
        // (3) The predicate re-holds with the same witness.
        let witness = eval_run_predicate(universe, completion, &cheevo.achievement)?;
        if witness != cheevo.witness {
            return Err(CheevoError::Tampered(format!(
                "witness changed on re-check: {witness:?} != {:?}",
                cheevo.witness
            )));
        }
        // (4) The run anchor binds this cheevo to this run.
        let anchor = run_anchor(&completion.player, &completion.play);
        if anchor != cheevo.completion_id {
            return Err(CheevoError::Tampered(
                "run anchor does not match the cheevo's provenance".into(),
            ));
        }
        // (5) The soulbound note is still owned by the earner (never transferred away).
        self.check_soulbound_owner(cheevo)?;
        Ok(())
    }

    /// **Re-verify an earned champion-cheevo** against the season's live hall-of-fame: the
    /// seal re-derives, the player is still a top-N champion at the recorded rank/turns, and
    /// the soulbound note is still owned by the earner.
    pub fn reverify_champion(&self, cheevo: &Cheevo, season: &Season) -> Result<(), CheevoError> {
        if !cheevo.seal_intact() {
            return Err(CheevoError::Tampered(
                "seal does not match the record's fields".into(),
            ));
        }
        let Achievement::SeasonChampion { top_n } = cheevo.achievement else {
            return Err(CheevoError::Tampered(
                "not a champion cheevo — use reverify_run".into(),
            ));
        };
        let champions = season.champions(top_n);
        let champ = champions
            .iter()
            .find(|c| c.player == cheevo.player)
            .ok_or(CheevoError::NotAChampion)?;
        let expect = Witness::Champion {
            top_n,
            rank: champ.rank,
            turns: champ.turns,
        };
        if expect != cheevo.witness {
            return Err(CheevoError::Tampered(
                "the champion's rank/turns changed on re-check".into(),
            ));
        }
        self.check_soulbound_owner(cheevo)?;
        Ok(())
    }

    /// The soulbound owner check: the minted note is still owned by the earner. There is no
    /// ledger path to change it; if the underlying note were ever moved, this would refuse.
    fn check_soulbound_owner(&self, cheevo: &Cheevo) -> Result<(), CheevoError> {
        match self.assets.current_owner(cheevo.note) {
            Some(owner) if owner == cheevo.earner => Ok(()),
            Some(_) => Err(CheevoError::Tampered(
                "the soulbound note is no longer owned by the earner".into(),
            )),
            None => Err(CheevoError::Tampered(
                "the soulbound note is missing".into(),
            )),
        }
    }

    /// Every cheevo minted so far (in mint order).
    pub fn minted(&self) -> &[Cheevo] {
        &self.minted
    }

    /// The stable per-player earner identity (the minted note's owner key). Deterministic
    /// in the player name — the same player is soulbound the same identity.
    pub fn earner_of(&mut self, player: &str) -> [u8; 32] {
        self.assets.pubkey_of(player)
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// Predicate evaluation over a verified run.
// ═══════════════════════════════════════════════════════════════════════════════

/// Evaluate an anchored predicate over a run's real committed trajectory. The caller has
/// ALREADY passed the no-cheat gate (so the trajectory is faithful + the run reached the
/// win). Returns the [`Witness`] on success, or a non-vacuous refusal.
fn eval_run_predicate(
    universe: &Universe,
    completion: &Completion,
    achievement: &Achievement,
) -> Result<Witness, CheevoError> {
    match achievement {
        Achievement::ReachedDepth { var, min } => {
            let slot = slot_of(universe, var)?;
            let peak = trajectory(&completion.play)
                .map(|st| st.get(slot).copied().unwrap_or(0))
                .max()
                .unwrap_or(0);
            if peak >= *min {
                Ok(Witness::Depth { peak, min: *min })
            } else {
                Err(CheevoError::PredicateNotMet(format!(
                    "peak `{var}` was {peak}, below the required {min}"
                )))
            }
        }
        Achievement::NoDeathClear { flag } => {
            let slot = slot_of(universe, flag)?;
            let tripped =
                trajectory(&completion.play).any(|st| st.get(slot).copied().unwrap_or(0) != 0);
            if tripped {
                Err(CheevoError::PredicateNotMet(format!(
                    "`{flag}` was tripped during the run — not a flawless clear"
                )))
            } else {
                Ok(Witness::NoDeath { flag: flag.clone() })
            }
        }
        Achievement::SpeedClear { max_turns } => {
            let turns = completion.play.steps.len();
            if turns <= *max_turns {
                Ok(Witness::Speed {
                    turns,
                    max_turns: *max_turns,
                })
            } else {
                Err(CheevoError::PredicateNotMet(format!(
                    "the clear took {turns} turns, above the max {max_turns}"
                )))
            }
        }
        Achievement::SeasonChampion { .. } => Err(CheevoError::PredicateNotMet(
            "a season-champion cheevo is earned via earn_champion, not a single run".into(),
        )),
    }
}

/// The run's committed state trajectory: genesis, then each step's post-state. Each is the
/// world-cell's full slot vector, so a var slot indexes directly into it.
fn trajectory(play: &Playthrough) -> impl Iterator<Item = &Vec<u64>> {
    std::iter::once(&play.genesis_state).chain(play.steps.iter().map(|s| &s.state))
}

/// Reconstruct a scene variable's slot from the universe's PUBLIC source — the same
/// var->slot projection the executor compiled. This is how a predicate reads the run's real
/// vars WITHOUT any private access to the universe: anyone holding the public source gets
/// the identical map.
fn slot_of(universe: &Universe, var: &str) -> Result<usize, CheevoError> {
    let scene = parse(universe.source(), "cheevo-eval.scene")
        .map_err(|_| CheevoError::UnknownVar(var.to_string()))?;
    let compiled = compile_scene(&scene).map_err(|_| CheevoError::UnknownVar(var.to_string()))?;
    compiled
        .var_slots
        .get(var)
        .copied()
        .ok_or_else(|| CheevoError::UnknownVar(var.to_string()))
}

// ═══════════════════════════════════════════════════════════════════════════════
// Content addressing — the run anchor + the soulbound seal.
// ═══════════════════════════════════════════════════════════════════════════════

fn domain_hasher(tag: &[u8]) -> Hasher {
    let mut h = Hasher::new();
    h.update(&(tag.len() as u64).to_le_bytes());
    h.update(tag);
    h
}

fn field(h: &mut Hasher, bytes: &[u8]) {
    h.update(&(bytes.len() as u64).to_le_bytes());
    h.update(bytes);
}

/// The **run anchor** — a content address over the player + the run's receipt chain (each
/// committed turn hash). Binds the cheevo to the un-retconnable receipt chain the no-cheat
/// verifier vouched; a re-verifier reproducing the same run reproduces this anchor.
fn run_anchor(player: &str, play: &Playthrough) -> [u8; 32] {
    let mut h = domain_hasher(DOMAIN_RUN_ANCHOR);
    field(&mut h, player.as_bytes());
    for r in play.receipts() {
        h.update(&r.turn_hash);
    }
    *h.finalize().as_bytes()
}

/// The **champion anchor** — a content address over the season, universe, identity, and
/// turns of a hall-of-fame placement (there is no single receipt chain for a championship;
/// it is a predicate over the whole board).
fn champion_anchor(champ: &Champion) -> [u8; 32] {
    let mut h = domain_hasher(DOMAIN_CHAMPION_ANCHOR);
    h.update(&champ.from_season.to_le_bytes());
    field(&mut h, champ.universe.as_bytes());
    field(&mut h, &champ.identity);
    h.update(&(champ.turns as u64).to_le_bytes());
    h.update(&(champ.rank as u64).to_le_bytes());
    *h.finalize().as_bytes()
}

/// The **soulbound seal** — `blake3(earner | achievement | universe | run | witness)`. It
/// is the note's content-addressing mint seed AND the tamper check: a cheevo record whose
/// earner (a buyer), achievement, or witness was edited no longer re-derives its seal, so a
/// laundered / forged record is refused on re-verify.
fn seal_of(
    earner: &[u8; 32],
    achievement: &Achievement,
    universe: UniverseId,
    anchor: &[u8; 32],
    witness: &Witness,
) -> [u8; 32] {
    let mut h = domain_hasher(DOMAIN_SEAL);
    field(&mut h, earner);
    field(&mut h, &achievement_bytes(achievement));
    field(&mut h, universe.as_bytes());
    field(&mut h, anchor);
    field(&mut h, &witness_bytes(witness));
    *h.finalize().as_bytes()
}
