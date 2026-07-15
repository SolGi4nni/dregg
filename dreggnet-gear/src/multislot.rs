//! # `multislot` — a MULTI-SLOT loadout + a real multi-peer SET-BONUS conjunction.
//!
//! [`crate::gear::Loadout`] gates ONE run-cell ability on ONE equipped gear peer. A real
//! adventurer, though, wears a WHOLE loadout at once — a weapon AND armor AND a trinket — and
//! a **set bonus** is the reward for equipping the full set. This module is that:
//!
//! * [`MultiLoadout`] holds up to one piece per [`GearSlot`] (weapon / armor / trinket),
//!   enforcing **slot distinctness** — a second weapon is a real [`SlotError`] (you cannot
//!   wear two swords), and a piece whose block declares a different slot than the one it is
//!   filed under is refused. Each piece is a real owned [`crate::Gear`] asset.
//!
//! * [`SetBonusGate`] is the KERNEL tooth: ONE run/character cell whose set-bonus ability is
//!   gated on a **conjunction of [`ObservedFieldEquals`](StateConstraint::ObservedFieldEquals)**,
//!   one per equipped gear cell. The set-bonus turn writes each slot's ability field to the
//!   equipped-gear owner tag AND carries a per-peer Merkle-open witness; the executor admits it
//!   IFF **every** equipped gear cell is at its finalized equip root (a partial set fails
//!   closed) AND every ability field matches its peer AND every witness is present. So "the set
//!   bonus fires BECAUSE the whole set is owned + equipped" is a multi-cell kernel predicate —
//!   the multi-peer generalization of the single-gear gate (the set-bonus residual `gear.rs`
//!   named, now built).
//!
//! ## Honest scope — named residuals
//!
//! REAL + DRIVEN: the slot-distinct multi-piece loadout, the multi-peer set-bonus conjunction
//! (refused on a partial set / a stripped witness / a divergent value; commits on the full
//! set), and per-piece owned-asset gear. The set is FIXED at deploy (you choose your loadout,
//! then the gate is pinned at those pieces' finalized roots); an *incremental* re-pin as pieces
//! swap in/out, and the same production cross-node finalized-root channel `gear.rs` names, are
//! the residuals. The multi-cell PREDICATE and the fail-closed authority are real here.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellProgram, EmbeddedExecutor,
    FieldElement, StateConstraint, TurnReceipt,
};
use dregg_cell::state::FIELD_ZERO;

use dungeon_on_dregg::multicell::{OWNER_SLOT, actor_tag, peer_finalized_witness};

use crate::gear::{DRIVER_SEED, GEAR_FEDERATION, Gear, issue, set_field, world_cell};
use crate::statblock::GearSlot;

/// The run cell's ability slot for a given gear slot (weapon→0, armor→1, trinket→2) — each
/// gated on its own equipped-gear peer. Reuses the slot's stable wire tag.
fn ability_slot(slot: GearSlot) -> u8 {
    slot.tag()
}

/// The gear cell seed for a slot — distinct per slot so the three gear cells are distinct
/// cells in the ONE shared executor (the cross-cell reads need distinct peer identities).
fn gear_cell_seed(slot: GearSlot) -> u8 {
    0x70 + slot.tag()
}
/// The run/character cell seed (the single cell the set bonus lands on).
const RUN_CELL_SEED: u8 = 0x7F;

/// Why a piece could not be filed into a [`MultiLoadout`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SlotError {
    /// A piece is already filed in this slot (you cannot wear two of the same slot).
    SlotOccupied(GearSlot),
    /// The piece's stat-block slot does not match the slot it is being filed under.
    SlotMismatch {
        /// The slot the caller filed it under.
        filed: GearSlot,
        /// The slot the piece's block actually declares.
        declared: GearSlot,
    },
}

impl std::fmt::Display for SlotError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SlotError::SlotOccupied(s) => write!(f, "the {s:?} slot is already filled"),
            SlotError::SlotMismatch { filed, declared } => {
                write!(f, "a {declared:?} piece cannot fill the {filed:?} slot")
            }
        }
    }
}

/// **A multi-slot loadout** — up to one owned [`Gear`] per [`GearSlot`], slot-distinct. Build
/// it by [`Self::equip_piece`]-ing pieces, then [`Self::deploy_set_bonus`] to pin the
/// multi-peer set-bonus gate at the chosen set.
#[derive(Default)]
pub struct MultiLoadout {
    weapon: Option<Gear>,
    armor: Option<Gear>,
    trinket: Option<Gear>,
}

impl MultiLoadout {
    /// An empty loadout (no pieces).
    pub fn new() -> Self {
        MultiLoadout::default()
    }

    fn slot_ref(&self, slot: GearSlot) -> &Option<Gear> {
        match slot {
            GearSlot::Weapon => &self.weapon,
            GearSlot::Armor => &self.armor,
            GearSlot::Trinket => &self.trinket,
        }
    }
    fn slot_mut(&mut self, slot: GearSlot) -> &mut Option<Gear> {
        match slot {
            GearSlot::Weapon => &mut self.weapon,
            GearSlot::Armor => &mut self.armor,
            GearSlot::Trinket => &mut self.trinket,
        }
    }

    /// **File a piece into its slot.** The piece's own [`StatBlock`](crate::StatBlock) declares
    /// its slot; a piece whose declared slot differs from `slot` is a [`SlotError::SlotMismatch`],
    /// and a slot already filled is a [`SlotError::SlotOccupied`] (slot distinctness — no two
    /// weapons). Ownership is enforced at the asset layer when the set bonus is claimed.
    pub fn equip_piece(&mut self, slot: GearSlot, gear: Gear) -> Result<(), SlotError> {
        if gear.stats.slot != slot {
            return Err(SlotError::SlotMismatch {
                filed: slot,
                declared: gear.stats.slot,
            });
        }
        if self.slot_ref(slot).is_some() {
            return Err(SlotError::SlotOccupied(slot));
        }
        *self.slot_mut(slot) = Some(gear);
        Ok(())
    }

    /// The pieces filed, in a stable slot order (weapon, armor, trinket) — the set the bonus
    /// gates on.
    pub fn pieces(&self) -> Vec<(GearSlot, Gear)> {
        let mut out = Vec::new();
        for slot in [GearSlot::Weapon, GearSlot::Armor, GearSlot::Trinket] {
            if let Some(g) = self.slot_ref(slot) {
                out.push((slot, *g));
            }
        }
        out
    }

    /// How many slots are filled.
    pub fn filled(&self) -> usize {
        self.pieces().len()
    }

    /// **Deploy the multi-peer set-bonus gate** over the currently-filed pieces. The gate is a
    /// single run cell whose set-bonus ability is a conjunction of one
    /// [`ObservedFieldEquals`](StateConstraint::ObservedFieldEquals) per piece — it fires only
    /// when the WHOLE filed set is equipped. Requires at least one piece.
    pub fn deploy_set_bonus(&self) -> SetBonusGate {
        SetBonusGate::deploy(self.pieces())
    }
}

/// Assemble the multi-cell set-bonus world: one gear cell per equipped piece (WriteOnce owner)
/// plus one run cell. When `gate_roots` is `Some`, the run cell's set-bonus ability is gated on
/// the per-peer conjunction pinned at those finalized roots; `None` leaves the run cell ungated
/// (the dry-run that computes the roots).
fn assemble(
    pieces: &[(GearSlot, Gear)],
    gate_roots: Option<&[[u8; 32]]>,
) -> (
    EmbeddedExecutor,
    AppCipherclerk,
    CellId,
    Vec<CellId>,
    CellId,
) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::from_seed(DRIVER_SEED), GEAR_FEDERATION);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let driver = cclerk.cell_id();

    // A gear cell per piece — its OWNER slot WRITE-ONCE (first-equipper wins).
    let mut gear_ids = Vec::with_capacity(pieces.len());
    for (slot, gear) in pieces {
        let cell = world_cell(
            gear_cell_seed(*slot),
            gear.cell_token(),
            CellProgram::Predicate(vec![StateConstraint::WriteOnce { index: OWNER_SLOT }]),
        );
        gear_ids.push(cell.id());
        exec.ensure_cell(cell).expect("gear cell inserts");
    }

    // The run cell — gated on the PEER conjunction once we know every finalized root.
    let run_token = {
        let mut h = blake3::Hasher::new_derive_key("dreggnet-gear-multislot-run-v1");
        for (_slot, gear) in pieces {
            h.update(&gear.cell_token());
        }
        *h.finalize().as_bytes()
    };
    let run_program = match gate_roots {
        Some(roots) => {
            let mut constraints = Vec::with_capacity(pieces.len());
            for (i, ((slot, _gear), root)) in pieces.iter().zip(roots.iter()).enumerate() {
                constraints.push(StateConstraint::ObservedFieldEquals {
                    local_field: ability_slot(*slot),
                    source_cell: *gear_ids[i].as_bytes(),
                    source_field: OWNER_SLOT,
                    at_root: *root,
                    proof_witness_index: i,
                });
            }
            CellProgram::Predicate(constraints)
        }
        None => CellProgram::None,
    };
    let run = world_cell(RUN_CELL_SEED, run_token, run_program);
    let run_id = run.id();
    exec.ensure_cell(run).expect("run cell inserts");

    exec.with_ledger_mut(|ledger| {
        if let Some(agent) = ledger.get_mut(&driver) {
            for id in &gear_ids {
                agent.capabilities.grant(*id, AuthRequired::None);
            }
            agent.capabilities.grant(run_id, AuthRequired::None);
        }
    });

    (exec, cclerk, driver, gear_ids, run_id)
}

/// Compute each piece's post-equip finalized commitment (the per-peer roots the conjunction
/// pins) — a throwaway world equips every gear cell and reads each committed commitment.
fn finalized_roots(pieces: &[(GearSlot, Gear)]) -> Vec<[u8; 32]> {
    let (exec, cclerk, driver, gear_ids, _run) = assemble(pieces, None);
    let tag = actor_tag(driver);
    for id in &gear_ids {
        issue(
            &exec,
            &cclerk,
            *id,
            "equip",
            vec![set_field(*id, OWNER_SLOT as usize, tag)],
            vec![],
        )
        .expect("the dry-run equip commits");
    }
    exec.with_ledger_mut(|ledger| {
        gear_ids
            .iter()
            .map(|id| {
                ledger
                    .get(id)
                    .expect("gear present after equip")
                    .state_commitment()
            })
            .collect()
    })
}

/// **The live multi-peer set-bonus world** — the shared executor holding every equipped gear
/// cell + the run cell, and the per-peer finalized roots the set-bonus conjunction pins.
pub struct SetBonusGate {
    exec: EmbeddedExecutor,
    cclerk: AppCipherclerk,
    driver: CellId,
    slots: Vec<GearSlot>,
    gear_cells: Vec<CellId>,
    run_cell: CellId,
    gate_roots: Vec<[u8; 32]>,
}

impl SetBonusGate {
    /// Deploy the set-bonus world over `pieces`, pinning each piece's gate at its post-equip
    /// finalized commitment.
    pub fn deploy(pieces: Vec<(GearSlot, Gear)>) -> SetBonusGate {
        assert!(!pieces.is_empty(), "a set bonus needs at least one piece");
        let gate_roots = finalized_roots(&pieces);
        let (exec, cclerk, driver, gear_cells, run_cell) = assemble(&pieces, Some(&gate_roots));
        let slots = pieces.iter().map(|(s, _)| *s).collect();
        SetBonusGate {
            exec,
            cclerk,
            driver,
            slots,
            gear_cells,
            run_cell,
            gate_roots,
        }
    }

    /// The identity tag an equip stamps for this driver.
    pub fn tag(&self) -> FieldElement {
        actor_tag(self.driver)
    }

    /// The run/character cell id (where the set bonus lands).
    pub fn run_cell(&self) -> CellId {
        self.run_cell
    }

    /// The number of pieces in the set.
    pub fn piece_count(&self) -> usize {
        self.gear_cells.len()
    }

    /// **Equip one piece** — a real turn on that gear cell's OWN cell, stamping the equipper
    /// tag into its WRITE-ONCE owner slot. `which` is the index into the deployed set (in the
    /// stable weapon/armor/trinket order).
    pub fn equip(&self, which: usize) -> Result<TurnReceipt, String> {
        let cell = self.gear_cells[which];
        let tag = self.tag();
        issue(
            &self.exec,
            &self.cclerk,
            cell,
            "equip",
            vec![set_field(cell, OWNER_SLOT as usize, tag)],
            vec![],
        )
    }

    /// Equip EVERY piece in the set (the full loadout).
    pub fn equip_all(&self) -> Result<(), String> {
        for i in 0..self.gear_cells.len() {
            self.equip(i)?;
        }
        Ok(())
    }

    /// Whether gear cell `which` has reached its pinned finalized equip root (is equipped).
    pub fn is_equipped(&self, which: usize) -> bool {
        self.exec
            .with_ledger_mut(|l| l.get(&self.gear_cells[which]).map(|c| c.state_commitment()))
            .map(|root| root == self.gate_roots[which])
            .unwrap_or(false)
    }

    /// **Attempt the set bonus** — one run-cell turn writing each slot's ability field to
    /// `value` and carrying `witnesses.len()` Merkle-open witnesses. The executor admits it IFF
    /// EVERY peer `ObservedFieldEquals` passes: every gear cell at its finalized root, every
    /// ability field == its peer's owner tag, every witness present. `full_witness == false`
    /// strips the witnesses (fail-closed); a wrong `value` diverges (refused).
    pub fn use_set_bonus_with(
        &self,
        value: FieldElement,
        full_witness: bool,
    ) -> Result<TurnReceipt, String> {
        let effects = self
            .slots
            .iter()
            .map(|slot| set_field(self.run_cell, ability_slot(*slot) as usize, value))
            .collect();
        let blobs = if full_witness {
            self.gate_roots
                .iter()
                .map(|r| peer_finalized_witness(*r))
                .collect()
        } else {
            Vec::new()
        };
        issue(
            &self.exec,
            &self.cclerk,
            self.run_cell,
            "use_set_bonus",
            effects,
            blobs,
        )
    }

    /// The HONEST set-bonus use: each ability field == the equipped owner tag, every witness
    /// attached — what commits once the WHOLE set is equipped.
    pub fn use_set_bonus(&self) -> Result<TurnReceipt, String> {
        self.use_set_bonus_with(self.tag(), true)
    }

    /// Whether the set bonus has committed (every slot's ability field is set).
    pub fn set_bonus_active(&self) -> bool {
        let state = self.exec.cell_state(self.run_cell);
        match state {
            Some(s) => self
                .slots
                .iter()
                .all(|slot| s.fields[ability_slot(*slot) as usize] != FIELD_ZERO),
            None => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gear::Armory;
    use crate::statblock::{Rarity, StatBlock};

    fn full_set(armory: &mut Armory, smith: &str) -> MultiLoadout {
        let mut lo = MultiLoadout::new();
        lo.equip_piece(
            GearSlot::Weapon,
            armory.forge(smith, StatBlock::weapon(Rarity::Legendary, 12, 0xF1A3E)),
        )
        .expect("weapon fits the weapon slot");
        lo.equip_piece(
            GearSlot::Armor,
            armory.forge(smith, StatBlock::armor(Rarity::Rare, 9, 0xA12)),
        )
        .expect("armor fits the armor slot");
        lo.equip_piece(
            GearSlot::Trinket,
            armory.forge(smith, StatBlock::trinket(Rarity::Uncommon, 4, 0x7)),
        )
        .expect("trinket fits the trinket slot");
        lo
    }

    /// Slot distinctness: a second weapon is refused (SlotOccupied), and a weapon filed into
    /// the armor slot is refused (SlotMismatch). One piece per slot, and the piece's declared
    /// slot must match.
    #[test]
    fn a_loadout_is_slot_distinct() {
        let mut armory = Armory::new();
        armory.pubkey_of("alice");
        let mut lo = MultiLoadout::new();
        lo.equip_piece(
            GearSlot::Weapon,
            armory.forge("alice", StatBlock::weapon(Rarity::Common, 3, 1)),
        )
        .expect("first weapon fits");

        let second = armory.forge("alice", StatBlock::weapon(Rarity::Rare, 8, 2));
        assert_eq!(
            lo.equip_piece(GearSlot::Weapon, second),
            Err(SlotError::SlotOccupied(GearSlot::Weapon)),
            "a second weapon cannot be worn"
        );

        let a_weapon = armory.forge("alice", StatBlock::weapon(Rarity::Common, 3, 3));
        assert_eq!(
            lo.equip_piece(GearSlot::Armor, a_weapon),
            Err(SlotError::SlotMismatch {
                filed: GearSlot::Armor,
                declared: GearSlot::Weapon,
            }),
            "a weapon cannot fill the armor slot"
        );
        assert_eq!(lo.filled(), 1);
    }

    /// THE MULTI-PEER SET-BONUS CONJUNCTION (non-vacuous): with a three-piece set, the set
    /// bonus is REFUSED while any piece is un-equipped (a partial set fails the conjunction
    /// closed) and COMMITS only once EVERY piece is equipped — the same honest set-bonus turn,
    /// the equips the only pivot.
    #[test]
    fn the_set_bonus_needs_the_whole_set_equipped() {
        let mut armory = Armory::new();
        armory.pubkey_of("alice");
        let lo = full_set(&mut armory, "alice");
        let gate = lo.deploy_set_bonus();
        assert_eq!(gate.piece_count(), 3);

        // Nothing equipped → refused.
        assert!(
            gate.use_set_bonus().is_err(),
            "the set bonus refuses with no piece equipped"
        );

        // Equip weapon + armor only (2/3) → still refused (the trinket peer fails closed).
        gate.equip(0).expect("equip weapon");
        gate.equip(1).expect("equip armor");
        assert!(gate.is_equipped(0) && gate.is_equipped(1) && !gate.is_equipped(2));
        assert!(
            gate.use_set_bonus().is_err(),
            "a partial (2/3) set still refuses the bonus"
        );
        assert!(
            !gate.set_bonus_active(),
            "anti-ghost: not active on a partial set"
        );

        // Equip the trinket → the full set → the SAME honest turn now commits.
        gate.equip(2).expect("equip trinket");
        gate.use_set_bonus()
            .expect("the whole set equipped fires the set bonus");
        assert!(gate.set_bonus_active(), "the set bonus is active");
    }

    /// A spoofed set bonus is refused even with the whole set equipped: a stripped witness set
    /// fails closed, and a divergent value (not the equipped owner tag) is refused. The
    /// multi-peer tooth bites — no client `if`.
    #[test]
    fn a_spoofed_set_bonus_is_refused() {
        let mut armory = Armory::new();
        armory.pubkey_of("alice");
        let lo = full_set(&mut armory, "alice");
        let gate = lo.deploy_set_bonus();
        gate.equip_all().expect("equip the whole set");

        // Stripped witnesses — the conjunction fails closed.
        assert!(
            gate.use_set_bonus_with(gate.tag(), false).is_err(),
            "a stripped witness set fails the set bonus closed"
        );

        // A divergent value (not the real owner tag).
        let mut wrong = gate.tag();
        wrong[1] ^= 0xAA;
        assert!(
            gate.use_set_bonus_with(wrong, true).is_err(),
            "a divergent set-bonus value is refused"
        );
        assert!(!gate.set_bonus_active(), "anti-ghost: no spoof fired");

        // The honest use still commits.
        gate.use_set_bonus().expect("the honest set bonus commits");
        assert!(gate.set_bonus_active());
    }
}
