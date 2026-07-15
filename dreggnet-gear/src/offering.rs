//! # `offering` — the loadout + talent tree as frontend-agnostic [`Offering`]s.
//!
//! Gear and talents were reachable ONLY from `dreggnet-adventure` (as a loadout). This module
//! lifts them onto the [`dreggnet_offerings::Offering`] surface, so — exactly like
//! `dreggnet-surfaces` — writing `render -> ViewNode` ONCE lights up EVERY frontend (the native
//! cockpit, `deos-view`'s web / discord / telegram / wechat renderers, the test `MockFrontend`).
//!
//! * [`LoadoutOffering`] — a **playable** equip surface over [`crate::Loadout`]: forge a piece
//!   of gear (owned asset), EQUIP it (a real "own AND equip" turn — a non-owner is a real
//!   refusal), and USE its cross-cell ability (the [`ObservedFieldEquals`] kernel gate — refused
//!   before equip, commits after). Each `advance` fires a real committed turn.
//!
//! * [`TalentTreeOffering`] — a **playable** talent surface over the RESPEC-capable tree
//!   ([`crate::talents::respec_talent_tree_story`]): CLAIM an echoes-gated / prereq-gated /
//!   class-gated talent, or RESPEC (bump the generation, clear the tree, re-pick). Talents cost
//!   death-earned echoes, never $DREGG — the no-P2W teeth ride into the surface unchanged.
//!
//! ## Honest scope
//!
//! Both are *playable* (their `advance` fires a real committed turn; an illegal move is a real
//! executor refusal that commits nothing — the anti-ghost tooth). NAMED NEXT (a shared change,
//! not built here — it edits `dreggnet-surfaces`): the one-line `register_surfaces` mount that
//! adds these two beside the other eight (kept out of THIS crate to avoid touching the sibling).

use deos_view::{MenuItem, ViewNode};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};

use crate::gear::{Armory, EquipError, Loadout};
use crate::statblock::{GearSlot, Rarity, StatBlock};
use crate::talents::{
    self, RESPEC_PRICE, TALENT_TREE, Talent, claim_talent_gen, generation, has_talent_gen, respec,
};
use dungeon_on_dregg::meta;
use dungeon_on_dregg::progression::{self, MAGE};
use spween_dregg::WorldCell;

// ── local ViewNode builders (this crate's copy of the surfaces vocab) ────────────────────────

fn text(s: impl Into<String>) -> ViewNode {
    ViewNode::Text(s.into())
}
fn section(title: impl Into<String>, tag: &str, children: Vec<ViewNode>) -> ViewNode {
    ViewNode::Section {
        title: title.into(),
        tag: tag.to_string(),
        children,
    }
}
fn row(cells: Vec<ViewNode>) -> ViewNode {
    ViewNode::Row(cells)
}
fn pill(t: impl Into<String>, tag: &str) -> ViewNode {
    ViewNode::Pill {
        text: t.into(),
        tag: tag.to_string(),
        slot: None,
        cases: Vec::new(),
    }
}
fn menu(items: Vec<MenuItem>) -> ViewNode {
    ViewNode::Menu { items }
}
fn action_menu(actions: Vec<Action>) -> Vec<MenuItem> {
    actions
        .into_iter()
        .map(|a| MenuItem {
            label: a.label,
            turn: a.turn,
            arg: a.arg,
            enabled: a.enabled,
        })
        .collect()
}

fn rarity_label(r: Rarity) -> &'static str {
    match r {
        Rarity::Common => "common",
        Rarity::Uncommon => "uncommon",
        Rarity::Rare => "rare",
        Rarity::Legendary => "legendary",
    }
}
fn rarity_tag(r: Rarity) -> &'static str {
    match r {
        Rarity::Legendary => "warn",
        Rarity::Rare => "accent",
        Rarity::Uncommon => "good",
        Rarity::Common => "muted",
    }
}
fn slot_label(s: GearSlot) -> &'static str {
    match s {
        GearSlot::Weapon => "weapon",
        GearSlot::Armor => "armor",
        GearSlot::Trinket => "trinket",
    }
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// LoadoutOffering — the equip surface.
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// The affordance verbs.
pub const TURN_EQUIP: &str = "equip";
/// Use the equipped gear's cross-cell ability.
pub const TURN_USE: &str = "use_ability";

/// The player who forges + owns + equips the loadout gear.
const PLAYER: &str = "player";

/// A live loadout session — the owned-gear armory + the cross-cell equip world.
pub struct LoadoutSession {
    loadout: Loadout,
    equipped: bool,
    turns: usize,
}

impl LoadoutSession {
    /// Whether the gear is equipped (reached its finalized equip root).
    pub fn equipped(&self) -> bool {
        self.equipped
    }
    /// Whether the cross-cell ability has fired.
    pub fn ability_unlocked(&self) -> bool {
        self.loadout.gate.ability_unlocked()
    }
    /// The committed turn count.
    pub fn turns(&self) -> usize {
        self.turns
    }
}

/// **The loadout offering** — a stateless factory. Each [`open`](Offering::open) forges a fresh
/// piece of gear (deterministic in the seed) owned by [`PLAYER`] and deploys its equip world.
pub struct LoadoutOffering;

impl LoadoutOffering {
    /// A fresh loadout offering.
    pub fn new() -> Self {
        LoadoutOffering
    }
}

impl Default for LoadoutOffering {
    fn default() -> Self {
        LoadoutOffering::new()
    }
}

impl Offering for LoadoutOffering {
    type Session = LoadoutSession;

    fn open(&self, cfg: SessionConfig) -> Result<LoadoutSession, OfferingError> {
        let seed = cfg.seed.unwrap_or(0);
        let mut armory = Armory::new();
        armory.pubkey_of(PLAYER);
        // A legendary weapon forged deterministically from the session seed.
        let stats = StatBlock::weapon(Rarity::Legendary, 12 + (seed % 8), 0xF1A3E ^ seed);
        let gear = armory.forge(PLAYER, stats);
        let loadout = Loadout::new(armory, gear, None);
        Ok(LoadoutSession {
            loadout,
            equipped: false,
            turns: 0,
        })
    }

    fn actions(&self, s: &LoadoutSession) -> Vec<Action> {
        vec![
            Action::new(
                if s.equipped {
                    "Equipped"
                } else {
                    "Equip the gear"
                },
                TURN_EQUIP,
                0,
                !s.equipped,
            ),
            Action::new(
                "Use the gear ability",
                TURN_USE,
                0,
                s.equipped && !s.loadout.gate.ability_unlocked(),
            ),
        ]
    }

    fn advance(&self, s: &mut LoadoutSession, input: Action, _actor: DreggIdentity) -> Outcome {
        match input.turn.as_str() {
            TURN_EQUIP => match s.loadout.equip_with_receipt(PLAYER) {
                Ok(receipt) => {
                    s.equipped = true;
                    s.turns += 1;
                    Outcome::Landed {
                        receipt,
                        ended: false,
                    }
                }
                Err(EquipError::NotOwner(e)) => Outcome::Refused(format!("not the owner: {e}")),
                Err(EquipError::GateRefused(r)) => Outcome::Refused(format!("equip refused: {r}")),
            },
            TURN_USE => match s.loadout.gate.use_ability_honest() {
                Ok(receipt) => {
                    s.turns += 1;
                    Outcome::Landed {
                        receipt,
                        ended: false,
                    }
                }
                Err(r) => Outcome::Refused(format!("ability refused: {r}")),
            },
            other => Outcome::Refused(format!("unknown loadout affordance: {other}")),
        }
    }

    /// Re-verify the gear asset's provenance (its content-addressed lineage re-derives + the
    /// asset layer re-reads it live).
    fn verify(&self, s: &LoadoutSession) -> VerifyReport {
        let report = s.loadout.armory.verify_provenance(s.loadout.gear());
        if report.verified {
            VerifyReport::ok(s.turns)
        } else {
            VerifyReport::broken(s.turns, format!("gear provenance broke: {report:?}"))
        }
    }

    fn render(&self, s: &LoadoutSession) -> Surface {
        let stats = s.loadout.gear().stats;
        let mut children = Vec::new();

        children.push(section(
            "Gear",
            "accent",
            vec![
                row(vec![
                    text("Rarity"),
                    pill(rarity_label(stats.rarity), rarity_tag(stats.rarity)),
                    text("Slot"),
                    pill(slot_label(stats.slot), "muted"),
                ]),
                text(format!(
                    "might {} · ward {} · guile {} · rune {:#x}",
                    stats.might, stats.ward, stats.guile, stats.rune
                )),
            ],
        ));

        let (eq_text, eq_tag) = if s.equipped {
            ("equipped", "good")
        } else {
            ("not equipped", "muted")
        };
        let (ab_text, ab_tag) = if s.loadout.gate.ability_unlocked() {
            ("ability unlocked", "genuine")
        } else {
            ("ability locked", "muted")
        };
        children.push(section(
            "Status",
            "muted",
            vec![row(vec![pill(eq_text, eq_tag), pill(ab_text, ab_tag)])],
        ));

        children.push(section(
            "Actions",
            "accent",
            vec![menu(action_menu(self.actions(s)))],
        ));
        children.push(section(
            "Verified turns",
            "genuine",
            vec![text(s.turns.to_string())],
        ));

        Surface(section(
            "Loadout — equip owned gear, unlock its cross-cell ability",
            "accent",
            children,
        ))
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// TalentTreeOffering — the talent surface.
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// Claim a talent (`arg` = the talent index in [`TALENT_TREE`]).
pub const TURN_CLAIM: &str = "claim_talent";
/// Respec (bump the generation, clear the tree).
pub const TURN_RESPEC: &str = "respec";

/// A live talent-tree session — a RESPEC-capable hero cell that has already died once (so it
/// has banked death-earned echoes to spend on the tree) + the committed turn count.
pub struct TalentSession {
    hero: WorldCell,
    turns: usize,
    /// The committed turn hashes (accumulated as `advance` lands them) — the session's own
    /// receipt chain (`WorldCell` does not expose its receipts, so the offering records them).
    receipts: Vec<[u8; 32]>,
}

impl TalentSession {
    /// The hero's accrued death-echoes.
    pub fn echoes(&self) -> u64 {
        meta::echoes(&self.hero)
    }
    /// The current respec generation.
    pub fn generation(&self) -> u64 {
        generation(&self.hero)
    }
    /// Whether `talent` is held in the current generation.
    pub fn has(&self, talent: Talent) -> bool {
        has_talent_gen(&self.hero, talent)
    }
    /// The committed turn count.
    pub fn turns(&self) -> usize {
        self.turns
    }
}

/// **The talent-tree offering** — a stateless factory. Each [`open`](Offering::open) deploys a
/// RESPEC-capable Mage hero, kills it once, and banks echoes at a seed-derived depth (so the
/// surface can drive real claims + respecs).
pub struct TalentTreeOffering;

impl TalentTreeOffering {
    /// A fresh talent-tree offering.
    pub fn new() -> Self {
        TalentTreeOffering
    }

    fn talent_enabled(&self, s: &TalentSession, t: Talent) -> bool {
        if s.has(t) {
            return false;
        }
        if s.echoes() < t.price {
            return false;
        }
        if let Some(prereq) = t.prereq_slot {
            // The prereq talent must be held in the current generation.
            let held = TALENT_TREE
                .iter()
                .find(|x| x.slot == prereq)
                .map(|x| s.has(*x))
                .unwrap_or(false);
            if !held {
                return false;
            }
        }
        if let Some(class) = t.class {
            // The hero's class (read off the real CLASS_SLOT via its registered var) must match.
            if s.hero.read_var("class") != class {
                return false;
            }
        }
        true
    }
}

impl Default for TalentTreeOffering {
    fn default() -> Self {
        TalentTreeOffering::new()
    }
}

impl Offering for TalentTreeOffering {
    type Session = TalentSession;

    fn open(&self, cfg: SessionConfig) -> Result<TalentSession, OfferingError> {
        let seed = cfg.seed.unwrap_or(0);
        let hero = talents::deploy_respec_hero((seed as u8) | 0x80);
        progression::choose_class(&hero, MAGE)
            .map_err(|e| OfferingError::Deploy(format!("class: {e}")))?;
        progression::perish(&hero).map_err(|e| OfferingError::Deploy(format!("death: {e}")))?;
        // A death at a seed-derived depth banks echoes (10 + 5*depth); depth>=6 => >=40 echoes,
        // enough for Ironhide (30) + a respec (20).
        let depth = 6 + (seed % 6);
        meta::grant_echoes(&hero, depth)
            .map_err(|e| OfferingError::Deploy(format!("echoes: {e}")))?;
        Ok(TalentSession {
            hero,
            turns: 0,
            receipts: Vec::new(),
        })
    }

    fn actions(&self, s: &TalentSession) -> Vec<Action> {
        let mut actions: Vec<Action> = TALENT_TREE
            .iter()
            .enumerate()
            .map(|(i, t)| {
                Action::new(
                    format!("Claim {} ({} echoes)", t.name, t.price),
                    TURN_CLAIM,
                    i as i64,
                    self.talent_enabled(s, *t),
                )
            })
            .collect();
        actions.push(Action::new(
            format!("Respec ({RESPEC_PRICE} echoes)"),
            TURN_RESPEC,
            0,
            s.echoes() >= RESPEC_PRICE,
        ));
        actions
    }

    fn advance(&self, s: &mut TalentSession, input: Action, _actor: DreggIdentity) -> Outcome {
        match input.turn.as_str() {
            TURN_CLAIM => {
                let idx = input.arg.max(0) as usize;
                let Some(t) = TALENT_TREE.get(idx).copied() else {
                    return Outcome::Refused(format!("no talent #{idx}"));
                };
                match claim_talent_gen(&s.hero, t) {
                    Ok(receipt) => {
                        s.turns += 1;
                        s.receipts.push(receipt.turn_hash);
                        Outcome::Landed {
                            receipt,
                            ended: false,
                        }
                    }
                    Err(e) => Outcome::Refused(format!("claim `{}` refused: {e}", t.name)),
                }
            }
            TURN_RESPEC => match respec(&s.hero) {
                Ok(receipt) => {
                    s.turns += 1;
                    s.receipts.push(receipt.turn_hash);
                    Outcome::Landed {
                        receipt,
                        ended: false,
                    }
                }
                Err(e) => Outcome::Refused(format!("respec refused: {e}")),
            },
            other => Outcome::Refused(format!("unknown talent affordance: {other}")),
        }
    }

    /// Re-verify the session's committed receipt chain: every landed turn carries a real,
    /// distinct, non-zero turn hash (a genuine executor-admitted move, never a ghost).
    fn verify(&self, s: &TalentSession) -> VerifyReport {
        let mut seen = std::collections::HashSet::new();
        for h in &s.receipts {
            if *h == [0u8; 32] {
                return VerifyReport::broken(s.receipts.len(), "a committed turn has a zero hash");
            }
            if !seen.insert(*h) {
                return VerifyReport::broken(s.receipts.len(), "a turn hash repeats (replayed)");
            }
        }
        VerifyReport::ok(s.receipts.len())
    }

    fn render(&self, s: &TalentSession) -> Surface {
        let mut children = Vec::new();
        children.push(section(
            "Hero",
            "muted",
            vec![text(format!(
                "echoes {} · generation {} · turns {}",
                s.echoes(),
                s.generation(),
                s.turns
            ))],
        ));

        let mut rows: Vec<ViewNode> = vec![row(vec![
            text("Talent"),
            text("Price"),
            text("Gate"),
            text("Status"),
        ])];
        for t in TALENT_TREE {
            let gate = match (t.prereq_slot, t.class) {
                (Some(_), _) => "prereq",
                (_, Some(MAGE)) => "mage",
                (_, Some(_)) => "class",
                _ => "—",
            };
            let (status, tag) = if s.has(t) {
                ("held", "genuine")
            } else if self.talent_enabled(s, t) {
                ("available", "good")
            } else {
                ("locked", "muted")
            };
            rows.push(row(vec![
                text(t.name),
                text(t.price.to_string()),
                text(gate),
                pill(status, tag),
            ]));
        }
        children.push(section("Talents", "accent", vec![ViewNode::Table(rows)]));
        children.push(section(
            "Actions",
            "accent",
            vec![menu(action_menu(self.actions(s)))],
        ));

        Surface(section(
            "Talents — spend death-earned echoes (never $DREGG); respec to re-pick",
            "accent",
            children,
        ))
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The loadout offering drives the real equip→ability loop: equip commits, the ability
    /// then commits, and the gear provenance verifies. A use BEFORE equip is a real refusal.
    #[test]
    fn loadout_offering_drives_the_equip_loop() {
        let off = LoadoutOffering::new();
        let mut s = off.open(SessionConfig::with_seed(3)).expect("open");
        let who = DreggIdentity("player".into());

        // Use before equip → refused (the cross-cell gate is fail-closed).
        let early = off.advance(&mut s, Action::new("", TURN_USE, 0, true), who.clone());
        assert!(!early.landed(), "ability refused before equip: {early:?}");

        // Equip → lands.
        let eq = off.advance(&mut s, Action::new("", TURN_EQUIP, 0, true), who.clone());
        assert!(eq.landed(), "equip lands: {eq:?}");
        assert!(s.equipped());

        // Use → lands.
        let use_ = off.advance(&mut s, Action::new("", TURN_USE, 0, true), who);
        assert!(use_.landed(), "ability lands after equip: {use_:?}");
        assert!(s.ability_unlocked());

        assert!(off.verify(&s).verified, "gear provenance verifies");
        // The render surface is a real ViewNode tree (the do-once frontend reach).
        assert!(matches!(off.render(&s).view(), ViewNode::Section { .. }));
    }

    /// The talent offering drives real echoes-gated claims + a respec: Ironhide is claimable
    /// with banked echoes, a respec clears it, and a below-price claim / an unknown affordance
    /// is a real refusal.
    #[test]
    fn talent_offering_drives_claims_and_respec() {
        let off = TalentTreeOffering::new();
        let mut s = off.open(SessionConfig::with_seed(0)).expect("open");
        let who = DreggIdentity("player".into());
        assert!(s.echoes() >= 30, "the demo hero banked enough echoes");

        // Claim Ironhide (index 0) → lands + held.
        let claim = off.advance(&mut s, Action::new("", TURN_CLAIM, 0, true), who.clone());
        assert!(claim.landed(), "Ironhide claim lands: {claim:?}");
        assert!(s.has(TALENT_TREE[0]), "Ironhide held");

        // Respec → lands, generation bumps, Ironhide cleared.
        let rs = off.advance(&mut s, Action::new("", TURN_RESPEC, 0, true), who.clone());
        assert!(rs.landed(), "respec lands: {rs:?}");
        assert_eq!(s.generation(), 1);
        assert!(!s.has(TALENT_TREE[0]), "respec cleared Ironhide");

        // A Warrior-only talent (Battle Fury, index 3) is refused for this Mage hero.
        let wrong = off.advance(&mut s, Action::new("", TURN_CLAIM, 3, true), who.clone());
        assert!(
            !wrong.landed(),
            "a Mage cannot claim the Warrior talent: {wrong:?}"
        );

        // An unknown affordance is a real refusal.
        let bogus = off.advance(&mut s, Action::new("", "nonsense", 0, true), who);
        assert!(!bogus.landed());

        assert!(off.verify(&s).verified, "the hero receipt chain verifies");
    }
}
