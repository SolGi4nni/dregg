//! # `dreggnet-adventure` — the Lean-native Descent, integrated.
//!
//! The run in this loop is the real
//! [`NativeDescentOffering`](dreggnet_offerings::native_descent::NativeDescentOffering):
//! its transition program is emitted from Lean and every recorded command is replayed
//! through a fresh executor before progression accepts it.  The single handoff object is
//! [`NativeDescentRun`], whose [`NativeDescentCompletion`] names the actor, exact terminal
//! journal root, settlement receipt, and banked relics.
//!
//! The older feature APIs for cheevos, guild ranking, quests, and seasons are specialized
//! to `ugc_dregg::Completion`, a different executable language.  This crate therefore does
//! not manufacture a synthetic UGC mirror of the native run.  Its small native adapters
//! ([`NativeCheevoLedger`], [`NativeGuild`], [`CompletionGatedQuest`], and
//! [`NativeSeason`]) all call [`NativeDescentRun::verify_crowned`] and bind their records to
//! the exact native completion root.  They reuse the real soulbound asset, guild-capability,
//! faction-giver, and season-manifest primitives while the shared feature crates acquire a
//! verifier-generic completion interface.
//!
//! Party and loadout are enforced preconditions of [`Adventure::play`].  They are not yet
//! folded into the native Descent world cell: the native offering intentionally exposes no
//! external loadout commitment input.  That remaining composition seam is named rather than
//! represented as if a separate aid cell altered the Lean-native run.

use std::collections::HashSet;

use dregg_types::PublicKey;
use dreggnet_asset::{AssetId, AssetWorld};
use dreggnet_cheevo::{Achievement, Aggregate, Cmp, Witness};
use dreggnet_guild::{Guild, GuildStats};
use dreggnet_offerings::native_descent::{
    NativeDescentCompletion, NativeDescentOffering, NativeDescentRecord, NativeDescentSession,
};
use dreggnet_offerings::{Action, Offering, Outcome, RecordVerify, SessionConfig};
use dungeon_on_dregg::collective::Custodian;
use dungeon_on_dregg::descent::{DELVE, FLEE, LOOT, SMITE, UNLOCK};
use dungeon_on_dregg::loot::{LootDraw, roll_drop};
use procgen_dregg::CommittedSeed;

pub use dreggnet_offerings::DreggIdentity;

const NATIVE_CHEEVO_DOMAIN: &str = "dreggnet-adventure/native-cheevo/v1";
const NATIVE_WORLD_SEED_DOMAIN: &str = "dreggnet-adventure/native-world-seed/v1";

/// The exact eighteen-move crowned line driven by the Lean model's own test battery.
pub const CROWNED_LINE: [(&str, i64); 18] = [
    (DELVE, 0),
    (SMITE, 0),
    (LOOT, 1),
    (UNLOCK, 2),
    (DELVE, 0),
    (SMITE, 0),
    (LOOT, 2),
    (UNLOCK, 3),
    (DELVE, 0),
    (SMITE, 0),
    (SMITE, 0),
    (LOOT, 3),
    (UNLOCK, 4),
    (DELVE, 0),
    (SMITE, 0),
    (SMITE, 0),
    (LOOT, 0),
    (FLEE, 0),
];

// ─────────────────────────────────────────────────────────────────────────────
// One identity across party custody, native actor, assets, and guild membership.
// ─────────────────────────────────────────────────────────────────────────────

#[derive(Clone, Debug)]
pub struct PlayerIdentity {
    name: String,
}

impl PlayerIdentity {
    pub fn new(name: impl Into<String>) -> Self {
        Self { name: name.into() }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn holder_label(&self) -> &str {
        &self.name
    }

    pub fn guild_member(&self) -> DreggIdentity {
        DreggIdentity(self.name.clone())
    }

    pub fn custodian(&self) -> Custodian {
        Custodian::demo(&self.name)
    }

    pub fn seat_pk(&self) -> PublicKey {
        self.custodian().public_key()
    }
}

/// A stable committed seed used by the daily adventure and its companion draw.
pub fn today_seed() -> CommittedSeed {
    CommittedSeed::from_bytes([0x7D; 32])
}

fn native_session_seed(seed: &CommittedSeed) -> u64 {
    let mut h = blake3::Hasher::new_derive_key(NATIVE_WORLD_SEED_DOMAIN);
    h.update(seed.as_bytes());
    let mut raw = [0u8; 8];
    raw.copy_from_slice(&h.finalize().as_bytes()[..8]);
    u64::from_le_bytes(raw)
}

/// A native world's immutable identity: normalized deploy seed plus the exact
/// Lean-program-bound genesis journal root.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct NativeDescentWorld {
    pub seed: u8,
    pub root: [u8; 32],
}

/// Open a fresh Lean-native Descent for `seed` and return its immutable world identity.
pub fn open_descent(
    seed: &CommittedSeed,
) -> Result<
    (
        NativeDescentOffering,
        NativeDescentSession,
        NativeDescentWorld,
    ),
    String,
> {
    let offering = NativeDescentOffering::new();
    let session = offering
        .open(SessionConfig::with_seed(native_session_seed(seed)))
        .map_err(|error| format!("the native Descent did not deploy: {error}"))?;
    let record = offering.export_record(&session);
    let world = NativeDescentWorld {
        seed: record.seed,
        root: session.root(),
    };
    Ok((offering, session, world))
}

/// A fresh offering for callers that do not need a session yet.
pub fn descent_offering() -> NativeDescentOffering {
    NativeDescentOffering::new()
}

fn offered_action(
    offering: &NativeDescentOffering,
    session: &NativeDescentSession,
    turn: &str,
    arg: i64,
) -> Result<Action, String> {
    offering
        .actions(session)
        .into_iter()
        .find(|action| action.turn == turn && action.arg == arg)
        .ok_or_else(|| format!("the native surface omitted {turn}({arg})"))
}

/// Drive the exact crowned run through the offering surface.  Every step is submitted
/// to the Lean-program-backed executor; a disabled or refused step aborts the run.
pub fn drive_descent_to_win(
    offering: &NativeDescentOffering,
    session: &mut NativeDescentSession,
    actor: &DreggIdentity,
) -> Result<(), String> {
    for (index, (turn, arg)) in CROWNED_LINE.iter().copied().enumerate() {
        let action = offered_action(offering, session, turn, arg)?;
        if !action.enabled {
            return Err(format!(
                "native crowned step {} was not enabled: {turn}({arg})",
                index + 1
            ));
        }
        match offering.advance(session, action, actor.clone()) {
            Outcome::Landed { ended, .. } => {
                let should_end = index + 1 == CROWNED_LINE.len();
                if ended != should_end {
                    return Err(format!(
                        "native crowned step {} had terminal={ended}, expected {should_end}",
                        index + 1
                    ));
                }
            }
            Outcome::Refused(reason) => {
                return Err(format!(
                    "native crowned step {} refused at {turn}({arg}): {reason}",
                    index + 1
                ));
            }
        }
    }
    Ok(())
}

/// The one portable native run object handed to progression systems.
///
/// `record` is untrusted until [`verify`](Self::verify) or
/// [`verify_crowned`](Self::verify_crowned) re-executes it.  `completion` is retained as a
/// separate object deliberately: every consumer receives the same value and the verifier
/// requires it to equal the terminal completion re-derived from `record`.
#[derive(Clone, Debug)]
pub struct NativeDescentRun {
    pub world: NativeDescentWorld,
    pub record: NativeDescentRecord,
    pub completion: NativeDescentCompletion,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeRunFacts {
    pub actor: DreggIdentity,
    pub turns: usize,
    pub peak_depth: u64,
    pub final_depth: u64,
    pub banked_relics: Vec<usize>,
    pub crowned: bool,
}

impl NativeDescentRun {
    /// Re-execute the complete public record through a fresh native executor and require
    /// the exact terminal completion and world genesis to match.
    pub fn verify(&self) -> Result<NativeRunFacts, String> {
        if self.record.seed != self.world.seed {
            return Err("the run record names a different native world seed".to_string());
        }

        // NativeDescentOffering normalizes cfg seed as `(raw % 251) + 1`; every
        // normalized seed therefore has this canonical inverse.
        let raw_seed = u64::from(self.world.seed.saturating_sub(1));
        let offering = NativeDescentOffering::new();
        let genesis = offering
            .open(SessionConfig::with_seed(raw_seed))
            .map_err(|error| format!("the native world did not re-open: {error}"))?;
        if genesis.root() != self.world.root {
            return Err("the native world genesis root does not re-derive".to_string());
        }

        let replayed = offering
            .resume_record(&self.record)
            .map_err(|error| format!("the native run did not replay: {error}"))?;
        let report = offering.verify(&replayed);
        if !report.verified {
            return Err(format!(
                "the replayed native run did not verify: {}",
                report.detail
            ));
        }
        let derived = replayed
            .completion()
            .ok_or_else(|| "the native run has no terminal bank settlement".to_string())?;
        if derived != &self.completion {
            return Err("the supplied native completion differs from replay".to_string());
        }
        if self.completion.root != self.record.root {
            return Err(
                "the native completion is not the record's exact terminal head".to_string(),
            );
        }
        let actor = replayed
            .actor()
            .cloned()
            .ok_or_else(|| "the terminal run has no bound actor".to_string())?;
        if actor != self.completion.actor {
            return Err("the terminal completion substituted the run actor".to_string());
        }
        let turns = replayed.revision() as usize;
        if self.completion.revision as usize != turns {
            return Err("the terminal completion substituted the verified turn count".to_string());
        }
        let peak_depth = self
            .record
            .events
            .iter()
            .map(|event| event.post.depth)
            .max()
            .unwrap_or(0);
        Ok(NativeRunFacts {
            actor,
            turns,
            peak_depth,
            final_depth: replayed.game().sim().depth,
            banked_relics: derived.banked_relics.clone(),
            crowned: derived.crowned,
        })
    }

    /// The progression gate: exact replay plus the banked Crown of the Deep.
    pub fn verify_crowned(&self) -> Result<NativeRunFacts, String> {
        let facts = self.verify()?;
        if !facts.crowned || !facts.banked_relics.contains(&0) {
            return Err("the native run settled without banking the Crown of the Deep".to_string());
        }
        Ok(facts)
    }

    pub fn completion_root(&self) -> [u8; 32] {
        self.completion.root
    }
}

/// Build the single progression object from a live session after exact replay.
pub fn run_object(
    offering: &NativeDescentOffering,
    session: &NativeDescentSession,
    world: NativeDescentWorld,
) -> Result<NativeDescentRun, String> {
    let report = offering.verify(session);
    if !report.verified {
        return Err(format!(
            "the native session did not verify: {}",
            report.detail
        ));
    }
    let completion = session
        .completion()
        .cloned()
        .ok_or_else(|| "the native session has not banked a completion".to_string())?;
    let run = NativeDescentRun {
        world,
        record: offering.export_record(session),
        completion,
    };
    run.verify_crowned()?;
    Ok(run)
}

fn play_on_seed(
    who: &PlayerIdentity,
    seed: &CommittedSeed,
) -> Result<
    (
        NativeDescentOffering,
        NativeDescentSession,
        NativeDescentRun,
    ),
    String,
> {
    let (offering, mut session, world) = open_descent(seed)?;
    drive_descent_to_win(&offering, &mut session, &who.guild_member())?;
    let run = run_object(&offering, &session, world)?;
    Ok((offering, session, run))
}

/// Open and complete today's Lean-native Descent.
pub fn play_a_winning_descent(
    who: &PlayerIdentity,
) -> Result<
    (
        NativeDescentOffering,
        NativeDescentSession,
        NativeDescentRun,
    ),
    String,
> {
    play_on_seed(who, &today_seed())
}

// ─────────────────────────────────────────────────────────────────────────────
// Native completion adapters for the UGC-specialized progression crates.
// ─────────────────────────────────────────────────────────────────────────────

/// Faction-gated start plus native-replay-gated, one-shot turn-in.
pub struct CompletionGatedQuest {
    giver: dreggnet_quest::giver::FactionGatedGiverWorld,
    world: NativeDescentWorld,
    turned_in: Option<[u8; 32]>,
}

impl CompletionGatedQuest {
    pub fn post(world: NativeDescentWorld) -> Self {
        Self {
            giver: dreggnet_quest::giver::FactionGatedGiverWorld::deploy(),
            world,
            turned_in: None,
        }
    }

    pub fn is_started(&self) -> bool {
        self.giver.read(
            self.giver.giver(),
            dreggnet_quest::giver::GRANTED_SLOT as usize,
        ) == dreggnet_quest::giver::EMBER_QUEST_VALUE
    }

    pub fn is_turned_in(&self) -> bool {
        self.turned_in.is_some()
    }

    pub fn earn_standing(&self) {
        self.giver.earn_standing();
    }

    pub fn start(&self) -> Result<(), String> {
        self.giver.grant_honest().map(|_| ())
    }

    pub fn turn_in(&mut self, run: &NativeDescentRun) -> Result<usize, String> {
        if !self.is_started() {
            return Err("the Descent quest has not passed its faction gate".to_string());
        }
        if self.turned_in.is_some() {
            return Err("the Descent quest has already consumed a completion".to_string());
        }
        if run.world != self.world {
            return Err("the completion belongs to a different native Descent world".to_string());
        }
        let facts = run.verify_crowned()?;
        self.turned_in = Some(run.completion_root());
        Ok(facts.turns)
    }
}

#[derive(Clone, Debug)]
pub struct NativeCheevo {
    pub achievement: Achievement,
    pub witness: Witness,
    pub player: String,
    pub world_root: [u8; 32],
    pub completion_root: [u8; 32],
    pub turns: usize,
    pub note: AssetId,
    pub seal: [u8; 32],
}

/// Adventure-local cheevo adapter over native replay.  The credential note uses the
/// same ISA-enforced soulbound asset primitive as `dreggnet-cheevo`.
pub struct NativeCheevoLedger {
    assets: AssetWorld,
    minted: Vec<NativeCheevo>,
}

impl Default for NativeCheevoLedger {
    fn default() -> Self {
        Self::new()
    }
}

impl NativeCheevoLedger {
    pub fn new() -> Self {
        Self {
            assets: AssetWorld::new(),
            minted: Vec::new(),
        }
    }

    pub fn earn(
        &mut self,
        run: &NativeDescentRun,
        achievement: Achievement,
    ) -> Result<NativeCheevo, String> {
        let facts = run.verify_crowned()?;
        if facts.actor.as_str() != run.completion.actor.as_str() {
            return Err("the cheevo actor differs from the native completion".to_string());
        }
        let witness = eval_native_achievement(run, &facts, &achievement)?;
        self.mint(
            achievement,
            witness,
            facts.actor.as_str(),
            run.world.root,
            run.completion_root(),
            facts.turns,
        )
    }

    pub fn earn_champion(
        &mut self,
        season: &NativeSeason,
        player: &str,
        top_n: usize,
    ) -> Result<NativeCheevo, String> {
        let champion = season
            .champions(top_n)
            .into_iter()
            .find(|champion| champion.player == player)
            .ok_or_else(|| "the player did not place in the native season".to_string())?;
        self.mint(
            Achievement::SeasonChampion { top_n },
            Witness::Champion {
                top_n,
                rank: champion.rank,
                turns: champion.turns,
            },
            player,
            champion.world_root,
            champion.completion_root,
            champion.turns,
        )
    }

    fn mint(
        &mut self,
        achievement: Achievement,
        witness: Witness,
        player: &str,
        world_root: [u8; 32],
        completion_root: [u8; 32],
        turns: usize,
    ) -> Result<NativeCheevo, String> {
        let seal = native_cheevo_seal(
            player,
            world_root,
            completion_root,
            turns,
            &achievement,
            &witness,
        );
        if let Some(existing) = self.minted.iter().find(|cheevo| cheevo.seal == seal) {
            return Ok(existing.clone());
        }
        let note = self.assets.mint_soulbound(player, &seal);
        if !self.assets.is_soulbound(note) {
            return Err("the native cheevo note did not mint soulbound".to_string());
        }
        let cheevo = NativeCheevo {
            achievement,
            witness,
            player: player.to_string(),
            world_root,
            completion_root,
            turns,
            note,
            seal,
        };
        self.minted.push(cheevo.clone());
        Ok(cheevo)
    }

    pub fn reverify(
        &mut self,
        cheevo: &NativeCheevo,
        run: &NativeDescentRun,
    ) -> Result<(), String> {
        let facts = run.verify_crowned()?;
        let witness = eval_native_achievement(run, &facts, &cheevo.achievement)?;
        let seal = native_cheevo_seal(
            facts.actor.as_str(),
            run.world.root,
            run.completion_root(),
            facts.turns,
            &cheevo.achievement,
            &witness,
        );
        if witness != cheevo.witness
            || seal != cheevo.seal
            || cheevo.player != facts.actor.as_str()
            || cheevo.world_root != run.world.root
            || cheevo.completion_root != run.completion_root()
            || cheevo.turns != facts.turns
        {
            return Err("the native cheevo is not bound to this replayed completion".to_string());
        }
        let owner = self.assets.pubkey_of(&cheevo.player);
        if self.assets.current_owner(cheevo.note) != Some(owner)
            || !self.assets.is_soulbound(cheevo.note)
        {
            return Err("the native cheevo's soulbound note is missing or moved".to_string());
        }
        Ok(())
    }

    /// Drive a real transfer attempt and succeed only when the ISA refuses it.
    pub fn prove_soulbound(&mut self, cheevo: &NativeCheevo, to: &str) -> Result<(), String> {
        if !self.assets.is_soulbound(cheevo.note) {
            return Err("the credential note is not marked soulbound".to_string());
        }
        match self.assets.transfer(cheevo.note, &cheevo.player, to) {
            Ok(_) => Err("the executor admitted a soulbound credential transfer".to_string()),
            Err(_) => Ok(()),
        }
    }
}

fn native_cheevo_seal(
    player: &str,
    world_root: [u8; 32],
    completion_root: [u8; 32],
    turns: usize,
    achievement: &Achievement,
    witness: &Witness,
) -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key(NATIVE_CHEEVO_DOMAIN);
    h.update(&(player.len() as u64).to_be_bytes());
    h.update(player.as_bytes());
    h.update(&world_root);
    h.update(&completion_root);
    h.update(&(turns as u64).to_be_bytes());
    hash_achievement(&mut h, achievement);
    hash_witness(&mut h, witness);
    *h.finalize().as_bytes()
}

fn hash_string(hasher: &mut blake3::Hasher, value: &str) {
    hasher.update(&(value.len() as u64).to_be_bytes());
    hasher.update(value.as_bytes());
}

fn hash_achievement(hasher: &mut blake3::Hasher, achievement: &Achievement) {
    match achievement {
        Achievement::ReachedDepth { var, min } => {
            hasher.update(&[0]);
            hash_string(hasher, var);
            hasher.update(&min.to_be_bytes());
        }
        Achievement::NoDeathClear { flag } => {
            hasher.update(&[1]);
            hash_string(hasher, flag);
        }
        Achievement::SpeedClear { max_turns } => {
            hasher.update(&[2]);
            hasher.update(&(*max_turns as u64).to_be_bytes());
        }
        Achievement::SeasonChampion { top_n } => {
            hasher.update(&[3]);
            hasher.update(&(*top_n as u64).to_be_bytes());
        }
        Achievement::VarThreshold {
            label,
            var,
            agg,
            cmp,
            value,
        } => {
            hasher.update(&[4]);
            hash_string(hasher, label);
            hash_string(hasher, var);
            hasher.update(&[aggregate_tag(*agg), comparison_tag(*cmp)]);
            hasher.update(&value.to_be_bytes());
        }
        Achievement::All { label, parts } => {
            hasher.update(&[5]);
            hash_string(hasher, label);
            hasher.update(&(parts.len() as u64).to_be_bytes());
            for part in parts {
                hash_achievement(hasher, part);
            }
        }
    }
}

fn hash_witness(hasher: &mut blake3::Hasher, witness: &Witness) {
    match witness {
        Witness::Depth { peak, min } => {
            hasher.update(&[0]);
            hasher.update(&peak.to_be_bytes());
            hasher.update(&min.to_be_bytes());
        }
        Witness::NoDeath { flag } => {
            hasher.update(&[1]);
            hash_string(hasher, flag);
        }
        Witness::Speed { turns, max_turns } => {
            hasher.update(&[2]);
            hasher.update(&(*turns as u64).to_be_bytes());
            hasher.update(&(*max_turns as u64).to_be_bytes());
        }
        Witness::Champion { top_n, rank, turns } => {
            hasher.update(&[3]);
            hasher.update(&(*top_n as u64).to_be_bytes());
            hasher.update(&(*rank as u64).to_be_bytes());
            hasher.update(&(*turns as u64).to_be_bytes());
        }
        Witness::Threshold { var, observed } => {
            hasher.update(&[4]);
            hash_string(hasher, var);
            hasher.update(&observed.to_be_bytes());
        }
        Witness::Composite { parts } => {
            hasher.update(&[5]);
            hasher.update(&(parts.len() as u64).to_be_bytes());
            for part in parts {
                hash_witness(hasher, part);
            }
        }
    }
}

fn aggregate_tag(aggregate: Aggregate) -> u8 {
    match aggregate {
        Aggregate::Peak => 0,
        Aggregate::Trough => 1,
        Aggregate::Final => 2,
        Aggregate::Initial => 3,
        Aggregate::Sum => 4,
    }
}

fn comparison_tag(comparison: Cmp) -> u8 {
    match comparison {
        Cmp::Ge => 0,
        Cmp::Gt => 1,
        Cmp::Le => 2,
        Cmp::Lt => 3,
        Cmp::Eq => 4,
        Cmp::Ne => 5,
    }
}

fn values_for(run: &NativeDescentRun, var: &str) -> Result<Vec<u64>, String> {
    let mut values = vec![match var {
        "depth" | "spent" | "wounds" | "fate" | "pack" | "bank" => 0,
        _ => return Err(format!("the native Descent defines no statistic {var:?}")),
    }];
    values.extend(run.record.events.iter().map(|event| match var {
        "depth" => event.post.depth,
        "spent" => event.post.spent,
        "wounds" => event.post.wounds,
        "fate" => event.post.fate,
        "pack" => event.post.pack(),
        "bank" => event.post.bank(),
        _ => unreachable!("validated above"),
    }));
    Ok(values)
}

fn reduce(values: &[u64], aggregate: Aggregate) -> u64 {
    match aggregate {
        Aggregate::Peak => values.iter().copied().max().unwrap_or(0),
        Aggregate::Trough => values.iter().copied().min().unwrap_or(0),
        Aggregate::Final => values.last().copied().unwrap_or(0),
        Aggregate::Initial => values.first().copied().unwrap_or(0),
        Aggregate::Sum => values.iter().copied().fold(0, u64::saturating_add),
    }
}

fn comparison_holds(lhs: u64, comparison: Cmp, rhs: u64) -> bool {
    match comparison {
        Cmp::Ge => lhs >= rhs,
        Cmp::Gt => lhs > rhs,
        Cmp::Le => lhs <= rhs,
        Cmp::Lt => lhs < rhs,
        Cmp::Eq => lhs == rhs,
        Cmp::Ne => lhs != rhs,
    }
}

fn eval_native_achievement(
    run: &NativeDescentRun,
    facts: &NativeRunFacts,
    achievement: &Achievement,
) -> Result<Witness, String> {
    match achievement {
        Achievement::ReachedDepth { var, min } => {
            let peak = values_for(run, var)?.into_iter().max().unwrap_or(0);
            if peak < *min {
                return Err(format!("native peak {var}={peak} is below {min}"));
            }
            Ok(Witness::Depth { peak, min: *min })
        }
        Achievement::SpeedClear { max_turns } => {
            if facts.turns > *max_turns {
                return Err(format!(
                    "native clear took {} turns, over {max_turns}",
                    facts.turns
                ));
            }
            Ok(Witness::Speed {
                turns: facts.turns,
                max_turns: *max_turns,
            })
        }
        Achievement::VarThreshold {
            var,
            agg,
            cmp,
            value,
            ..
        } => {
            let observed = reduce(&values_for(run, var)?, *agg);
            if !comparison_holds(observed, *cmp, *value) {
                return Err(format!(
                    "native {var} statistic {observed} did not satisfy {cmp:?} {value}"
                ));
            }
            Ok(Witness::Threshold {
                var: var.clone(),
                observed,
            })
        }
        Achievement::All { parts, .. } => {
            if parts.is_empty() {
                return Err("an empty native achievement conjunction is not earnable".to_string());
            }
            let parts = parts
                .iter()
                .map(|part| eval_native_achievement(run, facts, part))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Witness::Composite { parts })
        }
        Achievement::NoDeathClear { .. } => Err(
            "the native Descent has terminal banking, not the old character `dead` statistic"
                .to_string(),
        ),
        Achievement::SeasonChampion { .. } => {
            Err("a champion cheevo must come from NativeSeason".to_string())
        }
    }
}

/// A native-clear board wrapped around the real guild capability set.
pub struct NativeGuild {
    guild: Guild,
    seen: HashSet<[u8; 32]>,
    stats: GuildStats,
}

impl NativeGuild {
    pub fn form(name: impl Into<String>) -> Self {
        Self {
            guild: Guild::form(name),
            seen: HashSet::new(),
            stats: GuildStats::default(),
        }
    }

    pub fn admit(&mut self, who: &DreggIdentity) {
        self.guild.admit(who);
        self.stats.members = self.guild.roster().count();
    }

    pub fn record_clear(
        &mut self,
        who: &DreggIdentity,
        run: &NativeDescentRun,
    ) -> Result<usize, String> {
        if !self.guild.is_member(who) {
            return Err(format!(
                "{} does not hold the guild capability",
                who.as_str()
            ));
        }
        if self.seen.contains(&run.completion_root()) {
            return Err("the guild already counted this native completion".to_string());
        }
        let facts = run.verify_crowned()?;
        if &facts.actor != who {
            return Err("the guild member did not author this native completion".to_string());
        }
        let member_cell = self
            .guild
            .member_cell(who)
            .ok_or_else(|| "the enrolled member has no guild cell".to_string())?;
        if !self.guild.act_on_guild(member_cell).committed() {
            return Err("the member's cap-gated guild handoff did not commit".to_string());
        }
        self.seen.insert(run.completion_root());
        self.stats.verified_clears += 1;
        self.stats.total_turns += facts.turns;
        self.stats.survivors += 1;
        Ok(facts.turns)
    }

    pub fn stats(&self) -> GuildStats {
        self.stats
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeChampion {
    pub player: String,
    pub world_root: [u8; 32],
    pub completion_root: [u8; 32],
    pub turns: usize,
    pub rank: usize,
}

#[derive(Clone, Debug)]
struct NativeSeasonEntry {
    player: String,
    world_root: [u8; 32],
    completion_root: [u8; 32],
    turns: usize,
}

/// A native replay board attached to a real `dregg-season` manifest.
pub struct NativeSeason {
    season: dregg_season::Season,
    entries: Vec<NativeSeasonEntry>,
    seen: HashSet<[u8; 32]>,
}

impl NativeSeason {
    pub fn genesis(
        season_id: u64,
        content_tag: impl Into<String>,
        started_at: u64,
        policy: dregg_season::CarryForwardPolicy,
    ) -> Self {
        Self {
            season: dregg_season::Season::genesis(
                season_id,
                dregg_epoch::local_manifest(),
                content_tag,
                started_at,
                policy,
            ),
            entries: Vec::new(),
            seen: HashSet::new(),
        }
    }

    pub fn season_id(&self) -> u64 {
        self.season.season_id()
    }

    pub fn submit(&mut self, run: &NativeDescentRun) -> Result<usize, String> {
        if self.seen.contains(&run.completion_root()) {
            return Err("the native season already contains this completion".to_string());
        }
        let facts = run.verify_crowned()?;
        self.seen.insert(run.completion_root());
        self.entries.push(NativeSeasonEntry {
            player: facts.actor.as_str().to_string(),
            world_root: run.world.root,
            completion_root: run.completion_root(),
            turns: facts.turns,
        });
        Ok(facts.turns)
    }

    pub fn champions(&self, top_n: usize) -> Vec<NativeChampion> {
        let mut entries = self.entries.clone();
        entries.sort_by_key(|entry| entry.turns);
        entries
            .into_iter()
            .take(top_n)
            .enumerate()
            .map(|(index, entry)| NativeChampion {
                player: entry.player,
                world_root: entry.world_root,
                completion_root: entry.completion_root,
                turns: entry.turns,
                rank: index + 1,
            })
            .collect()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Native banked relic -> verified fair loot -> craft sink -> identical trade note.
// ─────────────────────────────────────────────────────────────────────────────

pub const RELIC_MATERIAL_KIND: &str = "essence:native-descent";

pub fn descent_relic_recipe() -> dreggnet_craft::Recipe {
    use dreggnet_craft::{GearSlot, GearTemplate, Recipe};
    Recipe::gear(
        "forge:native-descent-relic",
        &[RELIC_MATERIAL_KIND, RELIC_MATERIAL_KIND],
        GearTemplate {
            slot: GearSlot::Weapon,
            rune: 0xDE5CE7,
            base_might: 30,
            base_ward: 6,
            base_guile: 6,
        },
    )
}

fn run_loot_draws(run: &NativeDescentRun) -> Result<Vec<LootDraw>, String> {
    let facts = run.verify_crowned()?;
    if facts.banked_relics.len() < 2 {
        return Err("the crowned settlement banked fewer than two forge inputs".to_string());
    }
    let seed = CommittedSeed::from_bytes(run.completion_root());
    Ok(facts
        .banked_relics
        .iter()
        .take(2)
        .map(|relic| {
            roll_drop(
                &seed,
                &format!("native-descent:banked-relic-{relic}"),
                *relic as u64,
            )
        })
        .collect())
}

struct ForgedRunLoot {
    forge: dreggnet_craft::CraftForge,
    relic: AssetId,
    drops: Vec<LootDraw>,
}

fn forge_run_loot(run: &NativeDescentRun, who: &PlayerIdentity) -> Result<ForgedRunLoot, String> {
    use dreggnet_craft::{CraftForge, RecipeBook, roll_craft};

    let recipe = descent_relic_recipe();
    let mut book = RecipeBook::new();
    book.register(recipe.clone());
    let mut forge = CraftForge::with_book(book);
    let drops = run_loot_draws(run)?;
    let inputs = drops
        .iter()
        .map(|drop| {
            forge
                .mint_loot_material(who.holder_label(), RELIC_MATERIAL_KIND, drop)
                .map_err(|error| format!("the native run's fair drop was refused: {error:?}"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let beacon = CommittedSeed::from_bytes(run.completion_root());
    let draw = roll_craft(&beacon, &recipe, &inputs);
    let relic = forge
        .craft(who.holder_label(), &draw)
        .map_err(|error| format!("the native run's loot did not forge: {error:?}"))?
        .output()
        .map(|output| output.asset_id)
        .ok_or_else(|| "the safe native Descent recipe produced no relic".to_string())?;
    Ok(ForgedRunLoot {
        forge,
        relic,
        drops,
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// Public end-to-end adventure.
// ─────────────────────────────────────────────────────────────────────────────

#[derive(Clone, Debug)]
pub struct AdventureError {
    pub phase: &'static str,
    pub reason: String,
}

impl AdventureError {
    fn at(phase: &'static str, reason: impl Into<String>) -> Self {
        Self {
            phase,
            reason: reason.into(),
        }
    }
}

impl std::fmt::Display for AdventureError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "adventure phase `{}`: {}", self.phase, self.reason)
    }
}

impl std::error::Error for AdventureError {}

#[derive(Clone, Debug)]
pub struct AdventureReport {
    pub hero: String,
    pub party_seats: usize,
    pub loot_split: Vec<u64>,
    pub gear_aid_fired: bool,
    pub companion_level: u64,
    pub companion_buff: u64,
    pub quest_started: bool,
    pub run_won: bool,
    pub world_root: [u8; 32],
    pub completion_root: [u8; 32],
    pub banked_relics: Vec<usize>,
    pub turns_to_win: usize,
    pub cheevo_earned: bool,
    pub guild_clears: usize,
    pub guild_turns: usize,
    pub quest_turned_in: bool,
    pub verified_loot_drops: usize,
    pub relic_id: [u8; 32],
    pub relic_lineage_len: usize,
    pub relic_buyer: String,
    pub season_champion: bool,
}

impl AdventureReport {
    pub fn summary_lines(&self) -> Vec<String> {
        vec![
            format!(
                "{} mustered {} seats; the committed split was {:?}.",
                self.hero, self.party_seats, self.loot_split
            ),
            format!(
                "Loadout preconditions: gear {}; level-{} companion buff {}.",
                if self.gear_aid_fired {
                    "armed"
                } else {
                    "failed"
                },
                self.companion_level,
                self.companion_buff
            ),
            format!(
                "Lean-native Descent: {} banked relics in {} replayed turns (root {}).",
                self.banked_relics.len(),
                self.turns_to_win,
                short_root(self.completion_root)
            ),
            format!(
                "One native completion: cheevo {}, guild {} clear(s)/{} turns, quest {}.",
                if self.cheevo_earned {
                    "earned"
                } else {
                    "missed"
                },
                self.guild_clears,
                self.guild_turns,
                if self.quest_turned_in {
                    "accepted"
                } else {
                    "refused"
                }
            ),
            format!(
                "{} verified fair drops forged one note, traded to {} (lineage {}).",
                self.verified_loot_drops, self.relic_buyer, self.relic_lineage_len
            ),
            format!(
                "Native season: {}.",
                if self.season_champion {
                    "hall-of-fame champion"
                } else {
                    "unplaced"
                }
            ),
        ]
    }
}

fn short_root(root: [u8; 32]) -> String {
    root[..6].iter().map(|byte| format!("{byte:02x}")).collect()
}

pub struct Adventure {
    hero: PlayerIdentity,
    seed: CommittedSeed,
}

impl Adventure {
    pub fn daily(hero: PlayerIdentity) -> Self {
        Self {
            hero,
            seed: today_seed(),
        }
    }

    pub fn on_seed(hero: PlayerIdentity, seed: CommittedSeed) -> Self {
        Self { hero, seed }
    }

    pub fn hero(&self) -> &PlayerIdentity {
        &self.hero
    }

    pub fn play(&self) -> Result<AdventureReport, AdventureError> {
        use dregg_season::CarryForwardPolicy;
        use dreggnet_companion::{CompanionRoost, roll_hatch};
        use dreggnet_gear::{Armory, Loadout, Rarity as GearRarity, StatBlock};
        use dreggnet_party::{Party, PartyMove, Role};
        use dreggnet_trade::{LegSpec, TradeSide, TradeWorld};

        const DEPTH_CHEEVO_MIN: u64 = 4;
        const COMPANION_AID_LEVEL: u64 = 2;
        const BUYER: &str = "Corvane";

        let hero = &self.hero;

        // The hero is a real seat, rather than merely sharing a label with a fixed demo roster.
        let mut party = Party::muster_with_roster([
            (Role::Tank, hero.name().to_string()),
            (Role::Scout, format!("{}-scout", hero.name())),
            (Role::Mage, format!("{}-mage", hero.name())),
            (Role::Healer, format!("{}-healer", hero.name())),
        ])
        .map_err(|error| AdventureError::at("party", error.to_string()))?;
        if party.seat(0).electorate_seat().pk != hero.seat_pk() {
            return Err(AdventureError::at(
                "party",
                "the native run actor is not the Tank seat's custody identity",
            ));
        }
        if !party.act_in_role(0).committed() || !party.act(1, PartyMove::GuardFront).refused() {
            return Err(AdventureError::at(
                "party",
                "the seated role capability/refusal pair did not hold",
            ));
        }
        let split = [40u64, 20, 20, 20];
        if !party.split_loot(&split).committed() {
            return Err(AdventureError::at("party", "the loot split was refused"));
        }

        // Loadout is an honest precondition.  The native world currently has no external
        // commitment input, so we do not claim this separate aid cell changed its state.
        let mut armory = Armory::new();
        armory.pubkey_of(hero.holder_label());
        let gear = armory.forge(
            hero.holder_label(),
            StatBlock::weapon(GearRarity::Legendary, 12, 0xDE5CE7),
        );
        let mut loadout = Loadout::new(armory, gear, None);
        if loadout.gate.use_ability_honest().is_ok() {
            return Err(AdventureError::at("loadout", "unequipped gear aid landed"));
        }
        loadout
            .equip(hero.holder_label())
            .map_err(|error| AdventureError::at("loadout", format!("equip: {error:?}")))?;
        loadout
            .gate
            .use_ability_honest()
            .map_err(|error| AdventureError::at("loadout", format!("gear aid: {error:?}")))?;
        let gear_aid_fired = loadout.gate.ability_unlocked();

        let mut roost = CompanionRoost::new();
        roost.pubkey_of(hero.holder_label());
        let companion = roost
            .hatch(
                hero.holder_label(),
                &roll_hatch(&self.seed, "companion:native-descent-drake", 0),
            )
            .map_err(|error| AdventureError::at("loadout", format!("hatch: {error:?}")))?;
        let mut buff = roost.arm_buff(&companion, COMPANION_AID_LEVEL);
        roost
            .raise_to(&companion, 1)
            .map_err(|error| AdventureError::at("loadout", format!("raise: {error:?}")))?;
        if roost
            .attempt_buff(&mut buff, hero.holder_label(), true)
            .is_ok()
        {
            return Err(AdventureError::at(
                "loadout",
                "under-level companion buff landed",
            ));
        }
        roost
            .raise_to(&companion, COMPANION_AID_LEVEL)
            .map_err(|error| AdventureError::at("loadout", format!("raise: {error:?}")))?;
        roost
            .attempt_buff(&mut buff, hero.holder_label(), true)
            .map_err(|error| AdventureError::at("loadout", format!("buff: {error:?}")))?;
        let companion_buff = roost.buff_value(&buff);

        // Post and start the faction-gated quest against the exact native genesis before play.
        let (offering, mut session, world) =
            open_descent(&self.seed).map_err(|error| AdventureError::at("run", error))?;
        let mut quest = CompletionGatedQuest::post(world);
        if quest.start().is_ok() {
            return Err(AdventureError::at(
                "quest",
                "the faction-locked quest opened without standing",
            ));
        }
        quest.earn_standing();
        quest
            .start()
            .map_err(|error| AdventureError::at("quest", error))?;

        drive_descent_to_win(&offering, &mut session, &hero.guild_member())
            .map_err(|error| AdventureError::at("run", error))?;
        let run = run_object(&offering, &session, world)
            .map_err(|error| AdventureError::at("run", error))?;
        let facts = run
            .verify_crowned()
            .map_err(|error| AdventureError::at("run", error))?;

        // All progression consumes the same native completion root and independently replays.
        let mut cheevos = NativeCheevoLedger::new();
        let cheevo = cheevos
            .earn(
                &run,
                Achievement::ReachedDepth {
                    var: "depth".to_string(),
                    min: DEPTH_CHEEVO_MIN,
                },
            )
            .map_err(|error| AdventureError::at("cheevo", error))?;
        cheevos
            .reverify(&cheevo, &run)
            .map_err(|error| AdventureError::at("cheevo", error))?;

        let mut guild = NativeGuild::form("The Native Descent Vanguard");
        guild.admit(&hero.guild_member());
        let guild_turns = guild
            .record_clear(&hero.guild_member(), &run)
            .map_err(|error| AdventureError::at("guild", error))?;
        let quest_turns = quest
            .turn_in(&run)
            .map_err(|error| AdventureError::at("quest", error))?;
        if cheevo.turns != guild_turns || quest_turns != guild_turns {
            return Err(AdventureError::at(
                "handoff",
                "native cheevo, guild, and quest disagree on the completion",
            ));
        }

        // Source two materials through the verified loot tooth, consume them in the forge,
        // and pass the exact output ledger into the atomic trade.
        let forged =
            forge_run_loot(&run, hero).map_err(|error| AdventureError::at("craft", error))?;
        let verified_loot_drops = forged.drops.len();
        let relic = forged.relic;
        let mut market = TradeWorld::with_assets(forged.forge.into_assets());
        market.fund_dregg(BUYER, 100);
        let mut trade = market.open_trade(
            hero.holder_label(),
            LegSpec::Asset(relic),
            BUYER,
            LegSpec::Dregg(50),
        );
        market
            .deposit(&mut trade, TradeSide::A)
            .map_err(|error| AdventureError::at("trade", format!("seller: {error:?}")))?;
        market
            .deposit(&mut trade, TradeSide::B)
            .map_err(|error| AdventureError::at("trade", format!("buyer: {error:?}")))?;
        market
            .settle(&mut trade)
            .map_err(|error| AdventureError::at("trade", format!("settle: {error:?}")))?;
        let provenance = market.verify_provenance(relic);
        if !provenance.verified {
            return Err(AdventureError::at("trade", provenance.reasons.join("; ")));
        }

        let mut season = NativeSeason::genesis(
            1,
            "the-native-descent:s1",
            1000,
            CarryForwardPolicy::hall_of_fame(3).with_prestige(),
        );
        season
            .submit(&run)
            .map_err(|error| AdventureError::at("season", error))?;
        let champion = cheevos
            .earn_champion(&season, hero.name(), 3)
            .map_err(|error| AdventureError::at("season", error))?;
        if champion.completion_root != run.completion_root() {
            return Err(AdventureError::at(
                "season",
                "the champion credential drifted from the native completion",
            ));
        }

        Ok(AdventureReport {
            hero: hero.name().to_string(),
            party_seats: party.seat_count(),
            loot_split: split.to_vec(),
            gear_aid_fired,
            companion_level: COMPANION_AID_LEVEL,
            companion_buff,
            quest_started: quest.is_started(),
            run_won: facts.crowned,
            world_root: run.world.root,
            completion_root: run.completion_root(),
            banked_relics: facts.banked_relics,
            turns_to_win: facts.turns,
            cheevo_earned: true,
            guild_clears: guild.stats().verified_clears,
            guild_turns,
            quest_turned_in: quest.is_turned_in(),
            verified_loot_drops,
            relic_id: relic.0,
            relic_lineage_len: provenance.length,
            relic_buyer: BUYER.to_string(),
            season_champion: true,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use dregg_season::CarryForwardPolicy;
    use dreggnet_craft::{CraftForge, RecipeBook};
    use dreggnet_party::{Party, Role};

    fn hero() -> PlayerIdentity {
        PlayerIdentity::new("Aster-native-tank")
    }

    fn won() -> (
        NativeDescentOffering,
        NativeDescentSession,
        NativeDescentRun,
    ) {
        play_a_winning_descent(&hero()).expect("the Lean-native crowned line lands")
    }

    #[test]
    fn crowned_run_is_native_restartable_and_completion_bound() {
        let (offering, session, run) = won();
        let facts = run.verify_crowned().expect("fresh executor replay");
        assert_eq!(facts.turns, CROWNED_LINE.len());
        assert_eq!(facts.peak_depth, 4);
        assert_eq!(facts.banked_relics, vec![0, 1, 2, 3]);
        assert_eq!(run.completion_root(), session.root());
        assert_eq!(
            run.completion.settlement_receipt_hash,
            session
                .events()
                .last()
                .expect("flee event")
                .receipt
                .receipt_hash()
        );

        let restarted = offering
            .resume_record(&run.record)
            .expect("public record replays into a fresh native executor");
        assert_eq!(restarted.root(), run.completion_root());
        assert_eq!(restarted.completion(), Some(&run.completion));
    }

    #[test]
    fn wrong_actor_and_tampered_replay_are_anti_ghost() {
        let (offering, mut session, _) = open_descent(&today_seed()).expect("open native");
        let alice = hero().guild_member();
        let mallory = DreggIdentity("Mallory".to_string());

        let locked = offered_action(&offering, &session, UNLOCK, 2).expect("unlock affordance");
        let root = session.root();
        assert!(!locked.enabled);
        assert!(matches!(
            offering.advance(&mut session, locked, mallory.clone()),
            Outcome::Refused(_)
        ));
        assert_eq!(session.root(), root);
        assert_eq!(session.actor(), None);

        let delve = offered_action(&offering, &session, DELVE, 0).expect("delve");
        assert!(matches!(
            offering.advance(&mut session, delve, alice.clone()),
            Outcome::Landed { .. }
        ));
        let smite = offered_action(&offering, &session, SMITE, 0).expect("smite");
        let bound_root = session.root();
        assert!(matches!(
            offering.advance(&mut session, smite, mallory),
            Outcome::Refused(_)
        ));
        assert_eq!(session.root(), bound_root);
        assert_eq!(session.actor(), Some(&alice));

        let (_, _, run) = won();
        let mut tampered = run.clone();
        tampered.record.events[0].command =
            dreggnet_offerings::native_descent::NativeDescentMove::Smite;
        assert!(tampered.verify_crowned().is_err());
    }

    #[test]
    fn quest_refuses_wrong_world_forgery_and_replay() {
        let (_, _, run) = won();
        let mut quest = CompletionGatedQuest::post(run.world);
        assert!(quest.turn_in(&run).is_err(), "not started");
        assert!(quest.start().is_err(), "no faction standing");
        quest.earn_standing();
        quest.start().expect("standing opens quest");

        let (_, _, other) = play_on_seed(&hero(), &CommittedSeed::from_bytes([0x33; 32]))
            .expect("other native world");
        assert!(quest.turn_in(&other).is_err(), "wrong world refused");

        let mut forged = run.clone();
        forged.completion.root[0] ^= 1;
        assert!(quest.turn_in(&forged).is_err(), "forged completion refused");
        assert!(!quest.is_turned_in(), "failed attempts are anti-ghost");

        assert_eq!(quest.turn_in(&run).expect("honest completion"), 18);
        assert!(quest.turn_in(&run).is_err(), "one completion cannot replay");
    }

    #[test]
    fn one_native_completion_drives_cheevo_guild_quest_and_season() {
        let (_, _, run) = won();
        let hero = hero();
        let root = run.completion_root();

        let mut cheevos = NativeCheevoLedger::new();
        let cheevo = cheevos
            .earn(
                &run,
                Achievement::ReachedDepth {
                    var: "depth".to_string(),
                    min: 4,
                },
            )
            .expect("native replay earns depth cheevo");
        assert_eq!(cheevo.completion_root, root);
        cheevos.reverify(&cheevo, &run).expect("cheevo replays");
        cheevos
            .prove_soulbound(&cheevo, "badge-buyer")
            .expect("ISA refuses transfer");

        let mut guild = NativeGuild::form("Native Vanguard");
        let who = hero.guild_member();
        assert!(guild.record_clear(&who, &run).is_err(), "nonmember refused");
        guild.admit(&who);
        assert_eq!(guild.record_clear(&who, &run).expect("member clear"), 18);
        assert!(guild.record_clear(&who, &run).is_err(), "replay refused");
        assert_eq!(guild.stats().verified_clears, 1);

        let mut quest = CompletionGatedQuest::post(run.world);
        quest.earn_standing();
        quest.start().expect("start");
        assert_eq!(quest.turn_in(&run).expect("turn in"), 18);

        let mut season = NativeSeason::genesis(
            7,
            "native-descent:test",
            1,
            CarryForwardPolicy::hall_of_fame(3),
        );
        assert_eq!(season.submit(&run).expect("season entry"), 18);
        assert!(season.submit(&run).is_err(), "season replay refused");
        let champions = season.champions(3);
        assert_eq!(champions[0].completion_root, root);
        let champion = cheevos
            .earn_champion(&season, hero.name(), 3)
            .expect("native champion cheevo");
        assert_eq!(champion.completion_root, root);
    }

    #[test]
    fn forged_native_run_advances_no_progression_system() {
        let (_, _, run) = won();
        let hero = hero();
        let mut forged = run.clone();
        forged.record.events[1].post.depth += 1;

        let mut cheevos = NativeCheevoLedger::new();
        assert!(cheevo_depth(&mut cheevos, &forged).is_err());

        let mut guild = NativeGuild::form("Native Vanguard");
        guild.admit(&hero.guild_member());
        assert!(guild.record_clear(&hero.guild_member(), &forged).is_err());
        assert_eq!(guild.stats().verified_clears, 0);

        let mut quest = CompletionGatedQuest::post(run.world);
        quest.earn_standing();
        quest.start().expect("start");
        assert!(quest.turn_in(&forged).is_err());
        assert!(!quest.is_turned_in());

        let mut season = NativeSeason::genesis(
            8,
            "native-descent:test",
            1,
            CarryForwardPolicy::hall_of_fame(3),
        );
        assert!(season.submit(&forged).is_err());
        assert!(season.champions(3).is_empty());
    }

    fn cheevo_depth(
        ledger: &mut NativeCheevoLedger,
        run: &NativeDescentRun,
    ) -> Result<NativeCheevo, String> {
        ledger.earn(
            run,
            Achievement::ReachedDepth {
                var: "depth".to_string(),
                min: 4,
            },
        )
    }

    #[test]
    fn live_loot_path_verifies_drops_and_refuses_a_forgery() {
        let (_, _, run) = won();
        let hero = hero();
        let forged = forge_run_loot(&run, &hero).expect("live verified loot path");
        assert_eq!(forged.drops.len(), 2);
        for drop in &forged.drops {
            dungeon_on_dregg::loot::reverify_drop(drop).expect("drop re-verifies");
            assert_eq!(drop.run_seed.as_bytes(), &run.completion_root());
        }

        let mut bad = forged.drops[0].clone();
        bad.roll = (bad.roll + 1) % 100;
        let mut book = RecipeBook::new();
        book.register(descent_relic_recipe());
        let mut probe = CraftForge::with_book(book);
        assert!(
            probe
                .mint_loot_material(hero.holder_label(), RELIC_MATERIAL_KIND, &bad)
                .is_err(),
            "a rewritten fair draw mints no material"
        );
    }

    #[test]
    fn public_adventure_runs_end_to_end_on_native_completion() {
        let hero = hero();
        let report = Adventure::daily(hero.clone())
            .play()
            .expect("full native adventure");
        assert_eq!(report.hero, hero.name());
        assert_eq!(report.party_seats, 4);
        assert_eq!(report.loot_split, vec![40, 20, 20, 20]);
        assert!(report.gear_aid_fired);
        assert_eq!(report.companion_buff, 2);
        assert!(report.quest_started && report.quest_turned_in);
        assert!(report.run_won && report.banked_relics.contains(&0));
        assert_eq!(report.turns_to_win, 18);
        assert!(report.cheevo_earned && report.season_champion);
        assert_eq!(report.guild_clears, 1);
        assert_eq!(report.guild_turns, report.turns_to_win);
        assert_eq!(report.verified_loot_drops, 2);
        assert_eq!(report.relic_lineage_len, 3);
        assert_ne!(report.world_root, report.completion_root);
        assert!(
            report
                .summary_lines()
                .iter()
                .any(|line| line.contains("Lean-native"))
        );

        let party = Party::muster_with_roster([
            (Role::Tank, hero.name().to_string()),
            (Role::Scout, "s".to_string()),
            (Role::Mage, "m".to_string()),
            (Role::Healer, "h".to_string()),
        ])
        .expect("hero-seated party");
        assert_eq!(party.seat(0).electorate_seat().pk, hero.seat_pk());
    }
}
