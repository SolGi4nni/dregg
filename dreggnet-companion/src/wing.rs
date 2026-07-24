//! # `wing` — THE WING: two raised companions ATTUNED, composed through the Braid.
//!
//! This module is the companion game's **content on the Braid hook**. A player who has raised
//! two companions can *attune* them into a **wing**: a lasting pairing whose worth to the
//! handler — the wing's **attunement** — is not either creature's stat line but a law-governed
//! composition of both.
//!
//! ```text
//!   attunement = 10·warden.level              (the lead's raised level)
//!              +  6·consort.level             (the wingmate's)
//!              -  2·warden.spent              (the lead's spent abilities — fatigue)
//!              +  3·warden.level · consort.level     ← THE BOND      (a product)
//!              +  4·warden.rarity · consort.rarity   ← THE RESONANCE (a product)
//! ```
//!
//! ## Why this needs the Braid and not a cell predicate
//!
//! The companion crate's existing gates are the kernel's declarative vocabulary:
//! [`StateConstraint::FieldGte`](dregg_app_framework::StateConstraint) for the XP floor,
//! `ObservedFieldEquals` + `FieldGte` for the cross-cell `>=` buff. That vocabulary is
//! **linear** (`AffineLe` / `AffineEq`): it can compare a committed field to a constant, and it
//! can bind one cell's field to a peer's, but it cannot **multiply two committed state values**.
//!
//! The last two terms above are exactly that product. "A wing is worth more than the sum of its
//! members" and "two matched tails resonate" are *nonlinear* statements about two creatures'
//! committed state, so they are not expressible as a buff cell's predicate at any level of
//! cleverness. They are what the general composition AIR
//! ([`dregg_param_compose`](dregg_braid_hook)) exists for, and the wing is this game's first
//! ride on it.
//!
//! ## Say the substrate out loud
//!
//! **This module authors no AIR, no constraint, and no gadget.** It supplies *content only*:
//! role tags, a param schema, coefficients, a versioned law id, the projection of committed
//! game state into params, and the in-fiction meaning of the composed number. The circuit is
//! `dregg-param-compose`'s general Custom-VK composition AIR, reached through
//! [`dregg_braid_hook::compose_entity`]; the outcome→cell weld is the deployed app-root fold
//! atom, reached through `dregg_braid_hook::fold`. A wing-law **v2** (say, a class-synergy
//! knot over the already-projected `class` param) is a new `ruleset_root` under the SAME
//! verification key — not an AIR edit.
//!
//! ## What the wing IS, on-chain
//!
//! [`CompanionRoost::attune_wing`] deploys an **attunement cell**: a real sovereign
//! [`dregg_cell::Cell`] whose committed wide plane carries the warden's projection and whose
//! committed native `fields[0..8]` octet carries the composition's `outcome_commitment`. Under
//! the `prove` feature, `Wing::seal` lands it through the deployed app-root fold node, so the
//! published attunement and the committed octet are tied in-circuit: a wing whose cell claims an
//! attunement its sub-proof did not compose has **no satisfying fold**.
//!
//! ## The projection is real committed state
//!
//! Three of the four params are read straight off the companion's live leveling cell — `level`
//! ([`LEVEL_SLOT`](dungeon_on_dregg::progression::LEVEL_SLOT)), `class`, `abilities_used` — the
//! same committed fields the XP gate and the cross-cell buff read. The fourth, `rarity`, is the
//! fair-hatch tier, and [`CompanionRoost::attune_wing`] **re-verifies the hatch**
//! ([`reverify_hatch`]) before projecting it, so a rewritten rarity is refused before any cell is
//! deployed. Level a companion up and the wing's attunement moves by exactly the law's delta —
//! the composition is over the game's real state, not a parallel sheet.
//!
//! ## Honest scope
//!
//! * **Real:** the ownership / permadeath / consumed / self-attune / forged-hatch gates (each a
//!   refusal that deploys nothing); the projection off committed cell fields; the composition
//!   through the general AIR; the attunement cell's committed octet; and — under `prove` — the
//!   honest fold accepting and a forged octet being refused by the app-root connect.
//! * **A named seam:** the attunement cell is a *distinct* cell (the same shape as the crate's
//!   existing buff cell, which also observes a companion rather than living inside it), deployed
//!   by the hook's [`deploy_entity`](dregg_braid_hook::deploy_entity) rather than by a roost turn
//!   — the companion's own leveling cell already spends native slots 1..6 on `xp`/`level`/`class`/
//!   `ability`/`dead`, which is precisely the octet the app-root weld indexes.
//! * **The attunement-cell namespace is the hook's full cell-key width.** Each wing is deployed
//!   at [`entity_key`](dregg_braid_hook::entity_key) of the roost's next wing ordinal — an
//!   injective `u64` encoding, so two wings never collide onto one cell id and a roost is not
//!   capped at some small number of live wings. (This crate's earlier residual — the hook's `u8`
//!   seed capping a roost at 255 attunement cells — was closed in the hook, where it belonged.)

use dregg_app_framework::CellId;
use dregg_braid_hook::{
    Comp, ComposeError, ComposeShape, DeployedEntity, Knot, LandedComposition, LinearTerm, Ruleset,
    Subject, compose_entity, entity_key,
};
use dreggnet_asset::AssetId;

use crate::{Companion, CompanionError, CompanionRoost, rarity_rank, reverify_hatch};

// ── The wing's content: roles, param schema, law ────────────────────────────────────

/// The role tag of the wing's **lead** — the companion the attunement cell is deployed around
/// (its projection rides the cell's committed wide plane). A role is an opaque `u64` the law
/// addresses by value; the vocabulary is this game's, never the AIR's.
pub const ROLE_WARDEN: u64 = 0x5741_5244; // "WARD"

/// The role tag of the wing's **wingmate**.
pub const ROLE_CONSORT: u64 = 0x434f_4e53; // "CONS"

/// Param slot 0 — the companion's committed `level` (the XP-gated progression field).
pub const P_LEVEL: usize = 0;
/// Param slot 1 — the fair-hatch rarity rank (`0 = common .. 3 = legendary`).
pub const P_RARITY: usize = 1;
/// Param slot 2 — the companion's committed `class` (`0` = unchosen). Projected and bound into
/// `subjects_root`, but NOT read by wing-law v1: a v2 adding a class-synergy knot is a new
/// ruleset root under the same VK.
pub const P_CLASS: usize = 2;
/// Param slot 3 — the companion's committed `abilities_used` (spent kit = fatigue).
pub const P_SPENT: usize = 3;

/// The wing schema's active param width. Slots at or past this are canonically zero and a law
/// term addressing one is refused.
pub const WING_PARAM_COUNT: usize = 4;

/// Catalog id of the wing composition law.
pub const WING_LAW_ID: u64 = 0x5749_4e47; // "WING"
/// Version of the wing law. A rebalance mints a new `ruleset_root`; it never changes what an
/// already-sealed wing's receipt meant.
pub const WING_LAW_VERSION: u64 = 1;

/// The lead's raised level, per level.
pub const CO_WARDEN_LEVEL: i64 = 10;
/// The wingmate's raised level, per level.
pub const CO_CONSORT_LEVEL: i64 = 6;
/// The lead's fatigue — each ability it has spent drags on the pairing.
pub const CO_WARDEN_FATIGUE: i64 = -2;
/// **THE BOND** — the nonlinear term. Two well-raised companions attune superlinearly.
pub const CO_BOND: i64 = 3;
/// **THE RESONANCE** — the nonlinear term over the fair-hatch tiers. Two matched tails resonate;
/// pairing a legendary with a common does not.
pub const CO_RESONANCE: i64 = 4;

/// Rows the wing's composition leaf is proven over in the app-root fold.
pub const WING_FOLD_ROWS: usize = 2;

/// **THE WING LAW** — three linear terms and two knots, addressed by role.
pub fn wing_law() -> Ruleset {
    Ruleset {
        id: WING_LAW_ID,
        version: WING_LAW_VERSION,
        linear: vec![
            LinearTerm {
                role: ROLE_WARDEN,
                param: P_LEVEL,
                coeff: CO_WARDEN_LEVEL,
            },
            LinearTerm {
                role: ROLE_CONSORT,
                param: P_LEVEL,
                coeff: CO_CONSORT_LEVEL,
            },
            LinearTerm {
                role: ROLE_WARDEN,
                param: P_SPENT,
                coeff: CO_WARDEN_FATIGUE,
            },
        ],
        knots: vec![
            Knot {
                role_a: ROLE_WARDEN,
                param_a: P_LEVEL,
                role_b: ROLE_CONSORT,
                param_b: P_LEVEL,
                coeff: CO_BOND,
            },
            Knot {
                role_a: ROLE_WARDEN,
                param_a: P_RARITY,
                role_b: ROLE_CONSORT,
                param_b: P_RARITY,
                coeff: CO_RESONANCE,
            },
        ],
    }
}

/// **THE WING SHAPE** — the VK class the wing's compositions ride: at most 3 subjects, 4 params
/// each, 3 linear terms, 2 knots. The bounds are *fuel*, not content: the third subject slot is
/// deliberate headroom (a future third role — a roost, a rider — composes under the SAME
/// verification key), and so is the unread `class` param.
pub fn wing_shape() -> ComposeShape {
    ComposeShape::new(3, WING_PARAM_COUNT, 3, 2)
}

/// The **Braid identity** of a companion: the low 28 bits of its content-addressed
/// [`AssetId`].
///
/// The AIR range-checks identities to the shape's 28-bit namespace (wider and the in-circuit
/// ordering comparison goes vacuous), so the projection layer must supply a bounded handle. That
/// this handle faithfully names a distinct companion is *this* layer's obligation, not the AIR's
/// — which is why [`CompanionRoost::attune_wing`] refuses a wing whose two members collide here
/// instead of composing them as one subject.
pub fn braid_identity(asset: AssetId) -> u64 {
    let b = asset.bytes();
    u64::from(u32::from_le_bytes([b[0], b[1], b[2], b[3]])) & ((1u64 << 28) - 1)
}

// ── The wing ────────────────────────────────────────────────────────────────────────

/// An **attuned wing** — two companions composed through the Braid, with the composed attunement
/// committed to a real attunement cell.
pub struct Wing {
    /// The handler who attuned it (the owner of both companions at attunement time).
    pub handler: [u8; 32],
    /// The lead companion (its projection rides the attunement cell's committed wide plane).
    pub warden: AssetId,
    /// The wingmate.
    pub consort: AssetId,
    /// The two projections that were composed — the params as read off committed state.
    pub projection: Vec<Subject>,
    /// **The attunement** — the composed outcome of [`wing_law`] over the projection.
    pub attunement: i128,
    /// The attunement cell (a real sovereign cell; its native `fields[0..8]` octet carries the
    /// composition's `outcome_commitment`).
    pub cell: CellId,
    /// The deployed entity behind that cell (its pre-state is the fold's `before`).
    pub entity: DeployedEntity,
    /// The landed composition: the sub-proof PIs, the pre/post commitments, and the app-root
    /// binding declaration the deployed chain prover routes the custom turn through.
    pub landed: LandedComposition,
}

impl Wing {
    /// The wing's members' projections, `(warden, consort)`.
    pub fn subjects(&self) -> (&Subject, &Subject) {
        (&self.projection[0], &self.projection[1])
    }

    /// **The outcome→cell weld, fast shadow.** True iff the attunement cell's committed native
    /// octet carries exactly the sub-proof's published `outcome_commitment` — the equality
    /// [`Wing::seal`]'s fold enforces in-circuit.
    pub fn outcome_welded(&self) -> bool {
        self.landed.harness_verify_outcome_welded()
    }

    /// **Seal the wing** (feature `prove`): land the composition through the deployed app-root
    /// fold node, tying the published attunement to the attunement cell's committed octet. Slow
    /// (a real recursion). An honest wing folds; a cell whose committed octet disagrees with the
    /// composed attunement has no satisfying fold and is refused.
    #[cfg(feature = "prove")]
    pub fn seal(&self) -> Result<(), CompanionError> {
        use dregg_braid_hook::fold::{fold_composition_app_root, honest_after};
        fold_composition_app_root(
            &self.entity.cell,
            &honest_after(&self.landed),
            &self.landed,
            WING_FOLD_ROWS,
        )
        .map_err(CompanionError::Refused)
    }
}

/// **Re-derive a wing's attunement from its projection under the named law** — the tooth that
/// refuses a *claimed* attunement. Recomposes [`wing_law`] over the wing's own projected subjects
/// and checks the result is the attunement the wing carries.
///
/// This is the host-side re-derivation (the same posture as [`reverify_hatch`]); the in-circuit
/// twin is that the composition AIR re-checks the outcome against the witnessed coefficients
/// bound to `ruleset_root`, and the app-root fold ties that outcome to the committed cell octet.
pub fn reverify_attunement(wing: &Wing) -> Result<i128, CompanionError> {
    let comp = Comp {
        subjects: wing.projection.clone(),
        ruleset: wing_law(),
        param_count: WING_PARAM_COUNT,
    };
    let composed = comp.compose().map_err(compose_err)?;
    if composed.outcome != wing.attunement {
        return Err(CompanionError::Forged(format!(
            "the claimed attunement {} is not the law's composition {}",
            wing.attunement, composed.outcome
        )));
    }
    Ok(composed.outcome)
}

fn compose_err(e: ComposeError) -> CompanionError {
    CompanionError::Compose(e.to_string())
}

// ── The roost surface ───────────────────────────────────────────────────────────────

impl CompanionRoost {
    /// Project a companion into a wing [`Subject`] — its params READ off committed state (level,
    /// class, abilities_used) plus its re-verified fair-hatch rarity tier.
    fn project_companion(&self, comp: &Companion, role: u64) -> Subject {
        Subject {
            identity: braid_identity(comp.asset_id),
            role,
            params: vec![
                self.level_of(comp) as i64,
                i64::from(rarity_rank(comp.rarity)),
                self.class_of(comp) as i64,
                self.abilities_used_of(comp) as i64,
            ],
        }
    }

    /// **ATTUNE A WING** — compose two of a handler's raised companions into a wing through the
    /// Braid, and commit the composed attunement to a real attunement cell.
    ///
    /// The gates (each refusing before anything is deployed, mirroring
    /// [`breed`](CompanionRoost::breed)): both companions must be known to this roost, un-consumed,
    /// owned by `handler` at attunement time (the asset layer's ownership read), alive (the
    /// committed `WriteOnce` `dead` flag), distinct, carrying a re-verifiable fair hatch, and
    /// projecting to distinct Braid identities.
    ///
    /// On success the params are read off the companions' live committed cells, composed under
    /// [`wing_law`] through [`dregg_braid_hook::compose_entity`], and the resulting
    /// `outcome_commitment` is committed to the attunement cell's native `fields[0..8]` octet with
    /// the app-root binding declared. Under the `prove` feature `Wing::seal` lands that through
    /// the deployed fold node.
    pub fn attune_wing(
        &mut self,
        handler: &str,
        warden: &Companion,
        consort: &Companion,
    ) -> Result<Wing, CompanionError> {
        let pk = self.assets.pubkey_of(handler);

        if warden.asset_id.bytes() == consort.asset_id.bytes() {
            return Err(CompanionError::Ineligible(
                "a companion cannot be attuned to itself".into(),
            ));
        }

        // Resolve both handles to the ROOST'S OWN records before anything is read off them: the
        // projection must be of the companion this roost hatched, never of a caller-supplied
        // struct whose `cell` / `rarity` fields could name someone else's progression.
        let known = |roost: &Self, id: AssetId| {
            roost
                .companions
                .get(&id.bytes())
                .cloned()
                .ok_or(CompanionError::Unknown)
        };
        let warden = known(self, warden.asset_id)?;
        let consort = known(self, consort.asset_id)?;

        for c in [&warden, &consort] {
            if self.consumed.contains(&c.asset_id.bytes()) {
                return Err(CompanionError::Consumed);
            }
            if self.assets.current_owner(c.asset_id) != Some(pk) {
                return Err(CompanionError::NotOwner);
            }
            if self.is_dead(c) {
                return Err(CompanionError::Ineligible(
                    "a dead companion cannot fly in a wing".into(),
                ));
            }
            // The rarity param is the fair-hatch tier, so the hatch is re-verified before it is
            // projected: a rewritten rarity is refused here, not carried into the composition.
            let hatch = self
                .hatches
                .get(&c.asset_id.bytes())
                .ok_or(CompanionError::Unknown)?
                .clone();
            reverify_hatch(&hatch)?;
        }

        let warden_subject = self.project_companion(&warden, ROLE_WARDEN);
        let consort_subject = self.project_companion(&consort, ROLE_CONSORT);
        if warden_subject.identity == consort_subject.identity {
            return Err(CompanionError::Ineligible(
                "the two companions collide in the 28-bit Braid identity namespace".into(),
            ));
        }

        // The attunement cell's key: the roost's next wing ordinal, injectively encoded into the
        // hook's full cell-key width. Distinct wings therefore land on distinct cells with no
        // small cap to run out of — but the counter is still advanced with a CHECKED add and the
        // exhausted case still refuses, because "the id space wrapped" must never be spelled
        // "two wings share a cell".
        let ordinal = self.next_wing_ordinal.ok_or_else(|| {
            CompanionError::Ineligible("this roost's attunement-cell ordinals are exhausted".into())
        })?;
        self.next_wing_ordinal = ordinal.checked_add(1);

        let (entity, landed) = compose_entity(
            entity_key(ordinal),
            0,
            warden_subject.clone(),
            std::slice::from_ref(&consort_subject),
            wing_law(),
            wing_shape(),
            WING_PARAM_COUNT,
        )
        .map_err(compose_err)?;

        Ok(Wing {
            handler: pk,
            warden: warden.asset_id,
            consort: consort.asset_id,
            projection: vec![warden_subject, consort_subject],
            attunement: landed.outcome,
            cell: entity.cell_id(),
            entity,
            landed,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::{CompanionRoost, HatchBeacon, roll_hatch};

    /// **Widening removed the CAP, not the refusal.** The roost's ordinal counter still advances
    /// with a checked add, and an exhausted counter still refuses — because the only thing worse
    /// than "you cannot attune another wing" is "your new wing quietly landed on someone else's
    /// attunement cell". `u64::MAX` attunements is not reachable by play, so the exhausted state
    /// is installed directly here (a crate-internal test, on the real roost) rather than driven
    /// to; what is being checked is that the branch refuses and deploys nothing.
    #[test]
    fn an_exhausted_ordinal_refuses_rather_than_wrapping_onto_a_live_cell() {
        let mut roost = CompanionRoost::new();
        let draw_w = roll_hatch(&HatchBeacon::from_bytes([7; 32]), "companion:frostwyrm", 0);
        let draw_c = roll_hatch(&HatchBeacon::from_bytes([7; 32]), "companion:emberling", 0);
        let warden = roost.hatch("ember", &draw_w).expect("a fair hatch mints");
        let consort = roost.hatch("ember", &draw_c).expect("a fair hatch mints");
        roost.raise_to(&warden, 2).expect("the warden raises");

        // The last available ordinal still attunes...
        roost.next_wing_ordinal = Some(u64::MAX);
        let last = roost
            .attune_wing("ember", &warden, &consort)
            .expect("the final ordinal is still a usable cell");
        assert_eq!(
            roost.next_wing_ordinal, None,
            "the counter is now exhausted"
        );

        // ...and the next one refuses, without minting a second wing on `last`'s cell.
        // (`match`, not `expect_err`: a `Wing` carries live cell/composition state and has no
        // `Debug`, and the test only needs the error arm.)
        let refused = match roost.attune_wing("ember", &warden, &consort) {
            Ok(_) => panic!("an exhausted ordinal must refuse"),
            Err(e) => e,
        };
        match refused {
            crate::CompanionError::Ineligible(why) => assert!(
                why.contains("exhausted"),
                "the refusal must name the exhausted namespace: {why}"
            ),
            other => panic!("expected an Ineligible refusal, got {other:?}"),
        }
        assert_eq!(
            roost.next_wing_ordinal, None,
            "a refusal does not advance the counter either"
        );
        let _ = last;
    }
}
