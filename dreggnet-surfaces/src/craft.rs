//! # `CraftOffering` — a **playable forge loop** over [`dreggnet_craft`].
//!
//! The economy's first real SINK, surfaced as an Offering. A crafter picks a recipe, the forge
//! CONSUMES its input materials (real owned notes, provably destroyed on-chain — the
//! [`dreggnet_craft`] sink tooth), rolls a **provably-fair** quality off a committed beacon
//! ([`roll_craft`]), and MINTS a real owned output note whose content address binds the recipe +
//! inputs + roll. Every `advance` fires a real craft turn on the substrate.
//!
//! ## Honest scope
//!
//! This is a *playable* Offering: a legal craft mints a real output (and commits a genuine
//! owner-signed turn on the freshly-forged note, carried as the [`Outcome::Landed`] receipt); an
//! illegal one — too few live inputs for the recipe floor, or inputs already consumed — is a real
//! [`CraftError`](dreggnet_craft::CraftError) refusal that mints NOTHING (anti-ghost). The recipes
//! come from the forge's COMMITTED [`RecipeBook`](dreggnet_craft::RecipeBook): a craft can only
//! present a recipe the catalog holds (bring-your-own odds are forbidden), and every material is a
//! typed [`MaterialKind`](dreggnet_craft::MaterialKind) matching the recipe it feeds. The forge's
//! internal input-sink spends are themselves real committed, owner-signed burns; the Offering
//! additionally commits an owner-claim turn on the output to carry a first-class [`TurnReceipt`]
//! for the render seam. NAMED NEXT (not built here): risky recipes (botch/partial bands) surfaced
//! as a playable gamble, and routing a commissioned craft through the escrow-market swap.
//!
//! ## The forged item does not stop here
//!
//! [`CraftOffering::in_world`] opens the forge onto a [`SharedWorld`] — the ONE ledger
//! [`crate::inventory`] and [`crate::trade`] also stand on. A craft then MINTS INTO that ledger and
//! appends the output to the shared registry, so the note the player just forged IS the note their
//! inventory lists and their market can sell: object-identical at the note-cell, no re-mint. See
//! [`crate::world`] for the seam. [`CraftOffering::new`] keeps the old siloed shape (a private
//! world per session) for a standalone forge demo.

use dreggnet_asset::AssetId;
use dreggnet_craft::{CraftOutcome, CraftQuality, CraftResolution, roll_craft};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};
use procgen_dregg::CommittedSeed;

use crate::world::{ItemRecord, Origin, SharedWorld, ask_for_quality};
use crate::{action_menu, menu, pill, row, section, short_hex, text};
use deos_view::ViewNode;

/// The affordance verb a crafter fires to forge a recipe (`arg` = the recipe index).
pub const TURN_CRAFT: &str = "craft";

/// The crafter label of a SILOED forge ([`CraftOffering::new`]). A shared forge crafts as its
/// world's canonical player instead — the one identity the inventory and market key on too.
const CRAFTER: &str = "crafter";

/// **A live forge session** over the real [`CraftForge`](dreggnet_craft::CraftForge) — a handle on
/// the world holding the forge (its materials, its bench, its ledger), the crafter label, the
/// committed beacon the fair draw anchors to, and this session's committed craft-turn count.
pub struct CraftSession {
    world: SharedWorld,
    crafter: String,
    beacon: CommittedSeed,
    turns: usize,
}

impl CraftSession {
    /// The number of committed craft turns so far.
    pub fn turns(&self) -> usize {
        self.turns
    }
    /// The number of outputs this crafter has forged into the world (read off the shared registry).
    pub fn output_count(&self) -> usize {
        self.output_ids().len()
    }
    /// How many materials are still live (unconsumed) on the bench.
    pub fn live_material_count(&self) -> usize {
        let w = self.world.read();
        (0..w.materials().len())
            .filter(|&i| w.material_live(i))
            .count()
    }
    /// **The asset ids this forge has crafted**, in forge order — the real notes on the shared
    /// ledger. In a shared world these are the very ids [`crate::InventoryOffering`] lists.
    pub fn output_ids(&self) -> Vec<AssetId> {
        let w = self.world.read();
        w.items()
            .iter()
            .filter(|r| r.origin.is_crafted() && r.owner == self.crafter)
            .map(|r| r.asset)
            .collect()
    }
    /// The current holder LABEL of `asset` off the forge's ledger. In a shared world this is how
    /// the forge SEES a move another surface made (a gift, a sale) — the share, observed.
    pub fn holder_of(&self, asset: AssetId) -> Option<String> {
        self.world.write().holder_label(asset)
    }
    /// The world this forge stands on (the handle a sibling surface shares).
    pub fn world(&self) -> &SharedWorld {
        &self.world
    }
}

/// **The craft offering** — a factory over the forge substrate. [`new`](Self::new) opens a private
/// world per session (a standalone forge); [`in_world`](Self::in_world) opens onto a
/// [`SharedWorld`] so the forged note reaches the inventory + market surfaces.
pub struct CraftOffering {
    world: Option<SharedWorld>,
}

impl CraftOffering {
    /// A SILOED craft offering — each [`open`](Offering::open) stands up its own world and stocks a
    /// fresh crafter with materials + a bench. Nothing forged here reaches another surface.
    pub fn new() -> Self {
        CraftOffering { world: None }
    }

    /// **A craft offering onto a SHARED world** — every session forges into `world`'s one ledger and
    /// registers the output on its canonical player's shelf, so [`crate::InventoryOffering::in_world`]
    /// and [`crate::TradeOffering::in_world`] over the same handle see the EXACT crafted note.
    pub fn in_world(world: SharedWorld) -> Self {
        CraftOffering { world: Some(world) }
    }

    fn do_craft(&self, s: &mut CraftSession, idx: usize) -> Outcome {
        // Read the bench's craft context out under a SHORT borrow (the forge is borrowed mutably
        // below; a live guard across the craft would panic on the re-borrow).
        let ctx = {
            let w = s.world.read();
            w.benches().get(idx).map(|b| {
                (
                    b.recipe.clone(),
                    b.label.clone(),
                    b.inputs
                        .iter()
                        .filter_map(|&i| w.materials().get(i))
                        .map(|m| m.asset)
                        .collect::<Vec<AssetId>>(),
                )
            })
        };
        let Some((recipe, label, input_assets)) = ctx else {
            return Outcome::Refused(format!("no recipe #{idx} on the bench"));
        };

        // The fair draw off the committed beacon (deterministic in beacon/recipe/inputs). The
        // forge looks the recipe up in its COMMITTED catalog by `draw.recipe_id`, so the odds
        // are the catalog's, never the caller's.
        let draw = roll_craft(&s.beacon, &recipe, &input_assets);

        let mut w = s.world.write();
        // THE FORGE: re-verify the fair draw, burn the inputs on-chain (the owner-signed sink),
        // mint the output INTO THE SHARED LEDGER. A forged draw, an unknown recipe, or a
        // wrong/too-few-input craft is refused with NO burn and NO mint (anti-ghost).
        match w.forge_mut().craft(&s.crafter, &draw) {
            Ok(CraftResolution::Crafted(out)) => {
                // A genuine committed owner-signed turn on the freshly-forged note — the crafter
                // claims what it forged. Carries the first-class receipt for the seam.
                let claim = w
                    .assets()
                    .transfer(out.asset_id, &s.crafter, &s.crafter)
                    .expect("the crafter can claim its own freshly-minted output note");
                // THE HANDOFF: the crafted note joins the shared registry on the crafter's shelf.
                // No second mint, no look-alike — the id is the note the forge just put on THIS
                // ledger, and the rarity the market and inventory render is its fair-draw quality.
                let crafter = s.crafter.clone();
                w.register_item(ItemRecord {
                    asset: out.asset_id,
                    name: label.clone(),
                    rarity: out.quality.label().to_string(),
                    kind: "gear".to_string(),
                    owner: crafter,
                    price: ask_for_quality(out.quality),
                    listed: false,
                    sold: false,
                    origin: Origin::Crafted {
                        recipe: label,
                        outcome: out.outcome,
                    },
                });
                drop(w);
                s.turns += 1;
                Outcome::Landed {
                    receipt: claim.spend,
                    ended: false,
                }
            }
            // The surface's recipes are all SAFE (their odds sit wholly on success), so a botch
            // is unreachable here; handle it honestly if a risky recipe is ever benched.
            Ok(CraftResolution::Botched(receipt)) => Outcome::Refused(format!(
                "craft `{label}` botched — the {} materials were consumed, no item forged",
                receipt.consumed.len()
            )),
            Err(e) => Outcome::Refused(format!("craft `{label}` refused: {e}")),
        }
    }
}

impl Default for CraftOffering {
    fn default() -> Self {
        CraftOffering::new()
    }
}

impl Offering for CraftOffering {
    type Session = CraftSession;

    fn open(&self, cfg: SessionConfig) -> Result<CraftSession, OfferingError> {
        // SHARED: adopt the world (already seeded — its bench, its ledger, its registry are the
        // ones the sibling surfaces read). SILOED: stand up a private world and stock it, exactly
        // as this surface always did.
        let world = match &self.world {
            Some(w) => w.clone(),
            None => {
                let w = SharedWorld::new(CRAFTER);
                w.seed_craft_bench();
                w
            }
        };
        let crafter = world.player();
        // The committed beacon (a Descent day-seed stand-in); the seed pins a deterministic day.
        let byte = cfg.seed.map(|s| s as u8).unwrap_or(7);
        Ok(CraftSession {
            world,
            crafter,
            beacon: CommittedSeed::from_bytes([byte; 32]),
            turns: 0,
        })
    }

    fn actions(&self, s: &CraftSession) -> Vec<Action> {
        let w = s.world.read();
        w.benches()
            .iter()
            .enumerate()
            .map(|(i, b)| {
                let have = w.live_inputs(b);
                let need = b.recipe.input_count();
                Action::new(
                    format!("Forge {} ({}/{} inputs)", b.label, have, need),
                    TURN_CRAFT,
                    i as i64,
                    have >= need,
                )
            })
            .collect()
    }

    fn advance(&self, s: &mut CraftSession, input: Action, _actor: DreggIdentity) -> Outcome {
        let idx = input.arg.max(0) as usize;
        match input.turn.as_str() {
            TURN_CRAFT => self.do_craft(s, idx),
            other => Outcome::Refused(format!("unknown craft affordance: {other}")),
        }
    }

    /// Re-verify every forged output's provenance (its content-addressed lineage re-derives + the
    /// asset layer re-reads it live), and every consumed input is provably gone on-chain.
    fn verify(&self, s: &CraftSession) -> VerifyReport {
        let w = s.world.read();
        for r in w.items().iter().filter(|r| r.origin.is_crafted()) {
            let report = w.forge().asset_provenance(r.asset);
            if !report.verified {
                return VerifyReport::broken(
                    s.turns,
                    format!("`{}` provenance broke: {:?}", r.name, report.reasons),
                );
            }
        }
        for m in w.materials() {
            if w.forge().is_destroyed(m.asset) {
                // A consumed material is burned on-chain (the owner-signed sink): it must have
                // NO live owner. A "destroyed" note that still reports an owner would be a real
                // break (the sink did not fire).
                if w.forge().owner_of(m.asset).is_some() {
                    return VerifyReport::broken(
                        s.turns,
                        format!("`{}` was consumed but is still owned/live", m.name),
                    );
                }
            }
        }
        VerifyReport::ok(s.turns)
    }

    fn render(&self, s: &CraftSession) -> Surface {
        let mut children: Vec<ViewNode> = Vec::new();

        children.push(section(
            "Forge",
            "muted",
            vec![text(format!(
                "crafter {} · live materials {} · forged {} · turns {}",
                s.crafter,
                s.live_material_count(),
                s.output_count(),
                s.turns,
            ))],
        ));

        // The materials — a Table with a live/consumed status pill + provenance version count.
        // (Snapshotted out from under a SHORT borrow; the tree is built after the guard drops.)
        let mats: Vec<(String, bool, usize)> = {
            let w = s.world.read();
            w.materials()
                .iter()
                .enumerate()
                .map(|(i, m)| {
                    (
                        m.name.clone(),
                        w.material_live(i),
                        w.forge().asset_provenance(m.asset).length,
                    )
                })
                .collect()
        };
        let mut mat_rows: Vec<ViewNode> = vec![row(vec![
            text("Material"),
            text("Status"),
            text("Provenance"),
        ])];
        for (name, live, versions) in &mats {
            let (status, tag) = if *live {
                ("live", "good")
            } else {
                ("consumed", "muted")
            };
            mat_rows.push(row(vec![
                text(name),
                pill(status, tag),
                text(format!("v{versions}")),
            ]));
        }
        children.push(section(
            "Materials",
            "accent",
            vec![ViewNode::Table(mat_rows)],
        ));

        // The recipes — a Section{Menu} of craft affordances (a below-floor recipe shows dimmed).
        let acts = action_menu(self.actions(s));
        if !acts.is_empty() {
            children.push(section("Recipes", "accent", vec![menu(acts)]));
        }

        // The forged outputs — a Table binding each to its recipe + fair-draw quality, read off the
        // shared registry + the shared ledger (the OWNER column is a live substrate read, so if a
        // sibling surface gifted or sold what this forge made, it shows here).
        let forged: Vec<(String, CraftQuality, CraftOutcome, String)> = {
            let mut w = s.world.write();
            let rows: Vec<(String, CraftQuality, CraftOutcome, AssetId)> = w
                .items()
                .iter()
                .filter_map(|r| match &r.origin {
                    Origin::Crafted { recipe, outcome } if r.owner == s.crafter => Some((
                        recipe.clone(),
                        w.forge()
                            .quality_of(r.asset)
                            .unwrap_or(CraftQuality::Common),
                        *outcome,
                        r.asset,
                    )),
                    _ => None,
                })
                .collect();
            rows.into_iter()
                .map(|(recipe, q, o, asset)| {
                    let owner = w
                        .assets()
                        .current_owner(asset)
                        .map(|pk| short_hex(&pk))
                        .unwrap_or_else(|| "—".into());
                    (recipe, q, o, owner)
                })
                .collect()
        };
        if !forged.is_empty() {
            let mut out_rows: Vec<ViewNode> = vec![row(vec![
                text("Item"),
                text("Quality"),
                text("Outcome"),
                text("Owner"),
            ])];
            for (recipe, quality, outcome, owner) in &forged {
                let tag = match quality {
                    CraftQuality::Legendary => "warn",
                    CraftQuality::Rare => "accent",
                    _ => "muted",
                };
                out_rows.push(row(vec![
                    text(recipe),
                    pill(quality.label(), tag),
                    text(outcome.label()),
                    text(owner),
                ]));
            }
            children.push(section(
                "Forged",
                "genuine",
                vec![ViewNode::Table(out_rows)],
            ));
        }

        children.push(section(
            "Verified turns",
            "genuine",
            vec![text(s.turns.to_string())],
        ));

        Surface(section(
            "DreggNet Forge — a provably-fair craft loop",
            "accent",
            children,
        ))
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}
