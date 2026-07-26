//! # `CompanionOffering` — a **playable hatch + collection** over [`dreggnet_companion`].
//!
//! A companion is an owned [`dreggnet_asset`] identity FUSED with a real XP-gated leveling cell.
//! This Offering surfaces the two motions that read as play: **HATCH** a companion from a
//! provably-fair draw ([`roll_hatch`]) — minting a real owned note whose rarity is the re-derivable
//! draw tail — and **RAISE** it, each level a real XP-gated committed turn (a level-up without the
//! earned XP is a real executor refusal — a companion cannot be faked-leveled). The collection
//! renders as a `Table` of your companions + their live levels off the substrate.
//!
//! ## Honest scope
//!
//! This is a *playable* Offering. A hatch mints a real companion (and fires its genesis leveling
//! turn — level 0 → 1, which needs no XP — carried as the [`Outcome::Landed`] receipt); a RAISE
//! earns each level's XP floor then levels, a chain of real committed turns. A **force-level**
//! ([`TURN_OVERLEVEL`]) without the earned XP is a real [`CompanionError::Refused`] gate refusal
//! that commits nothing (non-vacuous: the same companion levels once RAISEd). NAMED NEXT (not built
//! here): the cross-cell buff activation ([`CompanionRoost::attempt_buff`] — needs a run buff-cell
//! surface), companion trading through the escrow-market swap, and abilities/breeding (the
//! `dreggnet_companion` residuals).

use dreggnet_companion::{Companion, CompanionRoost, roll_hatch};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};
use dungeon_on_dregg::loot::Rarity;
use procgen_dregg::CommittedSeed;

use crate::{action_menu, menu, pill, row, section, short_hex, text};
use deos_view::ViewNode;

/// The affordance verb a player fires to hatch a companion (`arg` = the species index).
pub const TURN_HATCH: &str = "hatch";
/// The affordance verb a player fires to raise a companion one level (`arg` = the companion index) —
/// earns the level's XP floor then levels (a chain of real committed turns).
pub const TURN_RAISE: &str = "raise";
/// The affordance verb that ATTEMPTS a level-up WITHOUT earning the XP (`arg` = the companion index)
/// — the XP-gate probe: a real refusal that commits nothing (a companion cannot be faked-leveled).
pub const TURN_OVERLEVEL: &str = "overlevel";

/// The keeper label — owns every companion identity note in the shared [`CompanionRoost`].
const KEEPER: &str = "keeper";

/// A hatched companion in the collection — the fused [`Companion`] plus its display name.
struct Hatched {
    comp: Companion,
    name: String,
}

/// **A live companion session** over the real [`CompanionRoost`] — the keeper, the hatchable
/// species, the collection of hatched companions, the committed beacon the fair draws anchor to,
/// and the committed-turn count.
pub struct CompanionSession {
    roost: CompanionRoost,
    keeper: String,
    beacon: CommittedSeed,
    species: Vec<String>,
    hatched: Vec<Hatched>,
    next_seq: u64,
    turns: usize,
}

impl CompanionSession {
    /// The number of companions in the collection.
    pub fn len(&self) -> usize {
        self.hatched.len()
    }
    /// Whether the collection is empty.
    pub fn is_empty(&self) -> bool {
        self.hatched.is_empty()
    }
    /// The committed-turn count (hatch genesis levels + raises).
    pub fn turns(&self) -> usize {
        self.turns
    }
    /// The live committed level of companion `idx`.
    pub fn level_of(&self, idx: usize) -> u64 {
        self.hatched
            .get(idx)
            .map(|h| self.roost.level_of(&h.comp))
            .unwrap_or(0)
    }
}

/// **The companion offering** — a stateless factory over the roost substrate. Each
/// [`open`](Offering::open) deploys a fresh roost seeded with a starter companion + a set of
/// hatchable species ([`demo`](Self::demo)) or empty ([`new`](Self::new)).
pub struct CompanionOffering {
    seed_starter: bool,
}

impl CompanionOffering {
    /// A fresh roost with no starter companion (the empty-collection surface).
    pub fn new() -> Self {
        CompanionOffering {
            seed_starter: false,
        }
    }

    /// A DEMO roost seeded with one starter companion (the web/discord register state).
    pub fn demo() -> Self {
        CompanionOffering { seed_starter: true }
    }

    fn hatch_into(s: &mut CompanionSession, species: &str) -> Result<(), String> {
        let draw = roll_hatch(&s.beacon, species, s.next_seq);
        s.next_seq += 1;
        let comp = s.roost.hatch(&s.keeper, &draw).map_err(|e| e.to_string())?;
        // The genesis leveling turn (0 → 1 needs no XP) — a real committed turn (the collection
        // enters at level 1). Kept so the hatch surfaces a first-class receipt.
        let _ = s.roost.try_level_up(&comp).map_err(|e| e.to_string())?;
        let name = format!("{species} #{}", s.hatched.len() + 1);
        s.hatched.push(Hatched { comp, name });
        Ok(())
    }

    fn do_hatch(&self, s: &mut CompanionSession, idx: usize) -> Outcome {
        let Some(species) = s.species.get(idx).cloned() else {
            return Outcome::Refused(format!("no species #{idx} to hatch"));
        };
        let draw = roll_hatch(&s.beacon, &species, s.next_seq);
        s.next_seq += 1;
        match s.roost.hatch(&s.keeper, &draw) {
            Ok(comp) => {
                let receipt = match s.roost.try_level_up(&comp) {
                    Ok(r) => r,
                    Err(e) => return Outcome::Refused(format!("genesis level refused: {e}")),
                };
                s.turns += 1;
                let name = format!("{species} #{}", s.hatched.len() + 1);
                s.hatched.push(Hatched { comp, name });
                Outcome::Landed {
                    receipt,
                    ended: false,
                }
            }
            Err(e) => Outcome::Refused(format!("hatch `{species}` refused: {e}")),
        }
    }

    fn do_raise(&self, s: &mut CompanionSession, idx: usize) -> Outcome {
        let Some(h) = s.hatched.get(idx) else {
            return Outcome::Refused(format!("no companion #{idx} in the collection"));
        };
        let comp = h.comp.clone();
        let target = s.roost.level_of(&comp) + 1;
        match s.roost.raise_to(&comp, target) {
            Ok(receipts) => {
                let n = receipts.len();
                match receipts.into_iter().last() {
                    Some(receipt) => {
                        s.turns += n;
                        Outcome::Landed {
                            receipt,
                            ended: false,
                        }
                    }
                    None => Outcome::Refused("the companion is already at that level".into()),
                }
            }
            Err(e) => Outcome::Refused(format!("raise refused: {e}")),
        }
    }

    fn do_overlevel(&self, s: &mut CompanionSession, idx: usize) -> Outcome {
        let Some(h) = s.hatched.get(idx) else {
            return Outcome::Refused(format!("no companion #{idx} in the collection"));
        };
        let comp = h.comp.clone();
        // A level-up with NO earned XP — the executor's FieldGte gate refuses it (non-vacuous: a
        // real RAISE of the same companion lands).
        match s.roost.try_level_up(&comp) {
            Ok(receipt) => {
                s.turns += 1;
                Outcome::Landed {
                    receipt,
                    ended: false,
                }
            }
            Err(e) => Outcome::Refused(format!("force-level refused (XP gate): {e}")),
        }
    }
}

impl Default for CompanionOffering {
    fn default() -> Self {
        CompanionOffering::new()
    }
}

impl Offering for CompanionOffering {
    type Session = CompanionSession;

    fn open(&self, cfg: SessionConfig) -> Result<CompanionSession, OfferingError> {
        let byte = cfg.seed.map(|s| s as u8).unwrap_or(11);
        let mut s = CompanionSession {
            roost: CompanionRoost::new(),
            keeper: KEEPER.to_string(),
            beacon: CommittedSeed::from_bytes([byte; 32]),
            species: vec![
                "companion:frostwyrm".to_string(),
                "companion:emberpup".to_string(),
                "companion:wisp".to_string(),
            ],
            hatched: Vec::new(),
            next_seq: 0,
            turns: 0,
        };
        if self.seed_starter {
            // A starter companion so the collection renders populated (a real fair hatch).
            let species = s.species[0].clone();
            Self::hatch_into(&mut s, &species)
                .map_err(|e| OfferingError::Deploy(format!("seed the starter companion: {e}")))?;
        }
        Ok(s)
    }

    fn actions(&self, s: &CompanionSession) -> Vec<Action> {
        let mut out = Vec::new();
        for (i, sp) in s.species.iter().enumerate() {
            out.push(Action::new(
                format!("Hatch {sp}"),
                TURN_HATCH,
                i as i64,
                true,
            ));
        }
        for (i, h) in s.hatched.iter().enumerate() {
            let lvl = s.roost.level_of(&h.comp);
            out.push(Action::new(
                format!("Raise {} (L{} → L{})", h.name, lvl, lvl + 1),
                TURN_RAISE,
                i as i64,
                !s.roost.is_dead(&h.comp),
            ));
        }
        out
    }

    fn advance(&self, s: &mut CompanionSession, input: Action, _actor: DreggIdentity) -> Outcome {
        let idx = input.arg.max(0) as usize;
        match input.turn.as_str() {
            TURN_HATCH => self.do_hatch(s, idx),
            TURN_RAISE => self.do_raise(s, idx),
            TURN_OVERLEVEL => self.do_overlevel(s, idx),
            other => Outcome::Refused(format!("unknown companion affordance: {other}")),
        }
    }

    /// Re-verify every companion's owned-identity lineage off the real asset substrate.
    fn verify(&self, s: &CompanionSession) -> VerifyReport {
        for h in &s.hatched {
            let report = s.roost.verify_identity(h.comp.asset_id);
            if !report.verified {
                return VerifyReport::broken(
                    s.turns,
                    format!("`{}` identity broke: {}", h.name, report.reasons.join("; ")),
                );
            }
        }
        VerifyReport::ok(s.turns)
    }

    fn render(&self, s: &CompanionSession) -> Surface {
        let mut children: Vec<ViewNode> = Vec::new();

        // THE DIRECTIVE, first — the one sentence saying what to do NOW. The shared skin promotes
        // the leading paragraph of an `accent` plaque; without one, a page states only what IS.
        let alive = s
            .hatched
            .iter()
            .filter(|h| !s.roost.is_dead(&h.comp))
            .count();
        children.push(section(
            "Your next move",
            "accent",
            vec![
                text(if s.is_empty() {
                    format!(
                        "Hatch your first companion — pick one of the {} species below and press \
                         Hatch. The roll is committed as a real turn, so the rarity you get is one \
                         nobody could choose after seeing it.",
                        s.species.len()
                    )
                } else if alive == 0 {
                    "Every companion in this roost has died — a dead one can no longer be raised. \
                     Hatch a new egg to start again."
                        .to_string()
                } else {
                    format!(
                        "Press Raise on one of your {alive} living companion(s) to spend a turn on \
                         it: each Raise commits exactly one level. Or hatch another egg from the \
                         species list."
                    )
                }),
                row(vec![
                    pill(
                        format!("{} companion(s)", s.len()),
                        if s.is_empty() { "muted" } else { "good" },
                    ),
                    pill(
                        format!("{alive} living"),
                        if alive == 0 { "bad" } else { "good" },
                    ),
                ]),
            ],
        ));

        children.push(section(
            "Roost",
            "muted",
            vec![text(format!(
                "keeper {} · companions {} · turns {}",
                s.keeper,
                s.len(),
                s.turns,
            ))],
        ));

        // The collection — a Table of owned companions + their live levels off the substrate.
        if s.is_empty() {
            children.push(section(
                "Companions",
                "muted",
                vec![text("No companions yet — hatch one from an egg.")],
            ));
        } else {
            let mut rows: Vec<ViewNode> = vec![row(vec![
                text("Companion"),
                text("Rarity"),
                text("Level"),
                text("XP"),
                text("Provenance"),
                text("Owner"),
            ])];
            for h in &s.hatched {
                let rarity = s.roost.rarity_of(h.comp.asset_id).unwrap_or(h.comp.rarity);
                let rtag = match rarity {
                    Rarity::Legendary => "warn",
                    Rarity::Rare => "accent",
                    _ => "muted",
                };
                let report = s.roost.verify_identity(h.comp.asset_id);
                let prov = if report.verified {
                    format!("v{} ✓", report.length)
                } else {
                    format!("v{} ✗", report.length)
                };
                let owner = s
                    .roost
                    .owner_of(h.comp.asset_id)
                    .map(|pk| short_hex(&pk))
                    .unwrap_or_else(|| "—".into());
                rows.push(row(vec![
                    text(&h.name),
                    pill(rarity.label(), rtag),
                    text(s.roost.level_of(&h.comp).to_string()),
                    text(s.roost.xp_of(&h.comp).to_string()),
                    pill(prov, if report.verified { "good" } else { "bad" }),
                    text(owner),
                ]));
            }
            children.push(section("Companions", "accent", vec![ViewNode::Table(rows)]));
        }

        // Hatch + raise affordances (a Section{Menu}).
        let acts = action_menu(self.actions(s));
        if !acts.is_empty() {
            children.push(section("Actions", "accent", vec![menu(acts)]));
        }

        children.push(section(
            "Verified turns",
            "genuine",
            vec![text(s.turns.to_string())],
        ));

        Surface(section(
            "DreggNet Companions — hatch + raise",
            "accent",
            children,
        ))
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}
