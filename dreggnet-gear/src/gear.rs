//! # `gear` — equippable, cross-cell-ownership-gated GEAR.
//!
//! A piece of gear is TWO real dregg constructions bound together:
//!
//! 1. **An owned [`dreggnet_asset`] note** (the [`Armory`]). Ownership is the executor's
//!    signature gate — a turn on the asset must verify under the asset cell's own key —
//!    so a **non-owner cannot equip**: equipping requires proving current ownership (an
//!    owner-signed operation on the asset), and a non-owner's attempt is a real
//!    [`dreggnet_asset::AssetError::Refused`] (a cryptographic refusal, not a client
//!    `if`). The gear PERSISTS across runs (the asset lineage survives every run) and is
//!    UN-DUPABLE (double-spend is a type error). Its rarity/traits are content-committed:
//!    the [`crate::statblock::StatBlock::traits_root`] is the mint seed, so the
//!    [`dreggnet_asset::AssetId`] binds the exact stat block.
//!
//! 2. **A cross-cell equip gate** (the [`EquipGate`]) on the REAL `multicell`
//!    [`StateConstraint::ObservedFieldEquals`] primitive. The gear item and the
//!    run/character cell are distinct cells sharing ONE executor ledger; the run cell's
//!    ability is gated by an `ObservedFieldEquals` naming the PEER gear cell's owner slot
//!    at the gear's post-EQUIP finalized root. So "the flaming-sword ability unlocks
//!    BECAUSE you equipped the sword at a finalized root" is a KERNEL predicate the
//!    executor re-checks across cells:
//!    * **before equip** the gear is not at the pinned root ⇒ the finalized-root
//!      authority has no binding ⇒ the ability turn is REFUSED (fail-closed);
//!    * **after a real equip turn** the gear reaches the pinned root ⇒ the authority
//!      binds owner→tag ⇒ the ability turn setting `ability == tag` (with the Merkle-open
//!      witness) COMMITS;
//!    * a **spoofed equip** — claiming the ability with the gear un-equipped, or a
//!      divergent value, or a stripped witness — is REFUSED.
//!
//! The [`Loadout`] composes them: `equip` FIRST proves asset ownership (a non-owner is
//! refused HERE, cryptographically) and only THEN stamps the gear cell (reaching the
//! finalized root that unlocks the ability). "Own AND equip to use" is thus enforced by
//! two real teeth — the asset signature gate and the cross-cell `ObservedFieldEquals` —
//! not a single-cell `if`.
//!
//! ## Durability (optional wear sink)
//!
//! An [`EquipGate`] deployed with a wear cap tracks a `wear` counter on the run cell:
//! each ability use advances it ([`StrictMonotonic`](StateConstraint::StrictMonotonic))
//! bounded by [`FieldLteField`](StateConstraint::FieldLteField)`(wear <= wear_cap)`, so
//! after `cap` uses the gear is spent and further use is REFUSED — a real
//! monotone SINK (the economy's durability faucet-drain).
//!
//! ## Honest scope — named residuals
//!
//! REAL + DRIVEN: owned asset gear (non-owner refused), the cross-cell equip gate
//! (refused-without / commits-with / spoof-refused, non-vacuous), across-run persistence,
//! the wear sink. NAMED RESIDUALS: multi-slot loadouts (weapon+armor+trinket at once) and
//! **set bonuses** (a multi-peer conjunction of `ObservedFieldEquals`); binding-on-equip
//! vs freely-tradeable (a policy field on the block); respec (a sink that clears the
//! equip); and the production **cross-node** finality source — here the gear + run cells
//! share ONE embedded ledger and the host recomputes the peer value from the committed
//! ledger (the `multicell` model); a cross-node finalized-root channel would let the run
//! cell gate on a gear note living on a DIFFERENT node's ledger. The cross-cell PREDICATE,
//! the fail-closed authority, and the asset ownership gate are real here.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellProgram, Effect, EmbeddedExecutor,
    FieldElement, StateConstraint, TurnReceipt, field_from_u64,
};
use dregg_cell::state::FIELD_ZERO;
use dregg_cell::{Cell, Permissions};
use dregg_turn::action::WitnessBlob;

use dreggnet_asset::{AssetError, AssetId, AssetWorld, ProvenanceReport};
// Reuse the REAL cross-cell helpers `multicell` proved: the actor tag a claim stamps and
// the Merkle-open witness the gated turn carries.
use dungeon_on_dregg::multicell::{OWNER_SLOT, actor_tag, peer_finalized_witness};

use crate::statblock::StatBlock;

/// The run cell's gated ABILITY slot — the write admitted only against the equipped-gear
/// peer condition (`ObservedFieldEquals`).
pub const ABILITY_SLOT: u8 = 0;
/// The run cell's `wear` slot — the durability sink (`StrictMonotonic`, bounded by the
/// cap). Advanced on every ability use.
pub const WEAR_SLOT: u8 = 1;
/// The run cell's `wear_cap` slot — the durability ceiling (seeded at deploy; the
/// `FieldLteField(wear <= wear_cap)` tooth reads it).
pub const WEAR_CAP_SLOT: u8 = 2;

/// The federation the equip world's turns commit under.
pub(crate) const GEAR_FEDERATION: [u8; 32] = [0x6E; 32];
/// A FIXED driver seed — so the dry-run pinning the finalized equip root and the real
/// world share ONE driver identity (mirrors `multicell`'s `DRIVER_SEED`).
pub(crate) const DRIVER_SEED: [u8; 64] = [0x6D; 64];

const GEAR_CELL_SEED: u8 = 0x6A;
const RUN_CELL_SEED: u8 = 0x6B;

// ═══════════════════════════════════════════════════════════════════════════════
// The owned-asset layer — gear is a real `dreggnet-asset`.
// ═══════════════════════════════════════════════════════════════════════════════

/// A forged piece of gear: its stable [`AssetId`] (content-committing the stat block via
/// the traits_root mint seed) plus the block itself.
#[derive(Clone, Copy, Debug)]
pub struct Gear {
    /// The stable, content-addressed asset id — commits the stat block (mint seed =
    /// [`StatBlock::traits_root`]) and is the cross-cell / cross-run handle.
    pub asset_id: AssetId,
    /// The gear's immutable stat/trait block.
    pub stats: StatBlock,
}

impl Gear {
    /// The content-addressed token binding the run-world gear cell to this owned asset —
    /// `blake3(asset_id ‖ traits_root)`. The equip world's gear cell carries this token,
    /// so the peer cell the ability gates on is provably the SAME item as the asset.
    pub fn cell_token(&self) -> [u8; 32] {
        let mut h = blake3::Hasher::new_derive_key("dreggnet-gear-cell-token-v1");
        h.update(&self.asset_id.bytes());
        h.update(&self.stats.traits_root());
        *h.finalize().as_bytes()
    }
}

/// **The armory** — the owned-gear surface over a set of sovereign holder ledgers
/// ([`dreggnet_asset::AssetWorld`]). Forging mints a real owned asset; the ownership
/// proof an equip requires (an owner-signed self-transfer) is refereed by the asset
/// layer's signature gate.
pub struct Armory {
    world: AssetWorld,
}

impl Default for Armory {
    fn default() -> Self {
        Self::new()
    }
}

impl Armory {
    /// A fresh armory (no smiths, no gear).
    pub fn new() -> Self {
        Armory {
            world: AssetWorld::new(),
        }
    }

    /// The deterministic pubkey of `label` (creating the holder identity if new).
    pub fn pubkey_of(&mut self, label: &str) -> [u8; 32] {
        self.world.pubkey_of(label)
    }

    /// **Forge a piece of gear**, owned by `smith_label`, carrying `stats`. The stat
    /// block's [`StatBlock::traits_root`] is the mint seed, so the returned [`Gear`]'s
    /// [`AssetId`] content-commits the exact block (rarity + traits bound to the asset).
    pub fn forge(&mut self, smith_label: &str, stats: StatBlock) -> Gear {
        let asset_id = self.world.mint(smith_label, &stats.traits_root());
        Gear { asset_id, stats }
    }

    /// **Forge gear FROM a provably-fair craft outcome** — the craft→gear pipe. The craft
    /// outcome (its quality tag + recipe id + fair roll + content commitment) lowers to a
    /// [`StatBlock`] via [`StatBlock::from_forge`] (quality→rarity, recipe→slot, roll→stats,
    /// commitment→rune), and that block is forged into a real owned asset owned by
    /// `smith_label`. So a forged item is DIRECTLY an equippable piece of gear whose stat
    /// block is provably its craft's outcome (deterministic in the inputs), carried by the
    /// same content-address keystone. `dreggnet-craft` (which depends on this crate) calls this
    /// with its `CraftDraw` fields — the primitive signature keeps the pipe cycle-free.
    pub fn forge_from_craft(
        &mut self,
        smith_label: &str,
        quality_tag: u8,
        recipe_id: &str,
        roll: u64,
        commitment: &[u8],
    ) -> Gear {
        let stats = StatBlock::from_forge(quality_tag, recipe_id, roll, commitment);
        self.forge(smith_label, stats)
    }

    /// **Prove current ownership of `gear` by `holder_label`** — an owner-signed
    /// self-transfer (spend the tail version, mint a same-owner successor). Only the
    /// REAL current owner can sign the tail spend, so a non-owner is a cryptographic
    /// [`AssetError::Refused`]. This is the ownership tooth an equip rides: the gear
    /// stays with its owner (a fresh bound version) and a stranger cannot pass it.
    pub fn prove_ownership(&mut self, gear: &Gear, holder_label: &str) -> Result<(), AssetError> {
        self.world
            .transfer(gear.asset_id, holder_label, holder_label)
            .map(|_| ())
    }

    /// **Transfer `gear` to a new holder** — a real owner-signed asset transfer (the gear
    /// changes hands; a non-owner sender is refused, a double-spend is refused). The gear
    /// PERSISTS as a lineage across the trade. (Named residual: binding-on-equip would gate
    /// this on the gear being un-equipped.)
    pub fn transfer(
        &mut self,
        gear: &Gear,
        from_label: &str,
        to_label: &str,
    ) -> Result<(), AssetError> {
        self.world
            .transfer(gear.asset_id, from_label, to_label)
            .map(|_| ())
    }

    /// The current owner's pubkey for `gear` (the tail version's owner).
    pub fn current_owner(&self, gear: &Gear) -> Option<[u8; 32]> {
        self.world.current_owner(gear.asset_id)
    }

    /// Re-verify `gear`'s provenance lineage (content-addressed links + on-chain spent
    /// re-reads) — the gear is un-forgeable and its whole history checks.
    pub fn verify_provenance(&self, gear: &Gear) -> ProvenanceReport {
        self.world.verify_provenance(gear.asset_id)
    }

    /// The number of versions in `gear`'s lineage (1 after forge, +1 per equip-proof /
    /// transfer) — the gear's real, growing on-ledger history.
    pub fn lineage_len(&self, gear: &Gear) -> usize {
        self.world.lineage_len(gear.asset_id)
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// The cross-cell equip gate — the run cell's ability gated on the PEER gear cell.
// ═══════════════════════════════════════════════════════════════════════════════

/// A cell whose permissions gate nothing (every op `AuthRequired::None`) — so the
/// cross-cell GATE (`ObservedFieldEquals`), not a per-cell signature mismatch, is what a
/// test observes. (Ownership is enforced at the ASSET layer, above.) Mirrors
/// `multicell::open_permissions`.
pub(crate) fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

/// Build an open world cell with `token` identity and `program`, deterministic in `seed`.
pub(crate) fn world_cell(seed: u8, token: [u8; 32], program: CellProgram) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, token, 0);
    cell.permissions = open_permissions();
    cell.program = program;
    cell
}

/// The run cell's program: the cross-cell equip gate, plus (when `wear_cap` is set) the
/// durability wear sink. A `Predicate` ANDs its constraints onto every run-cell turn (the
/// only run-cell turn is an ability use), exactly the proven `multicell` gate shape.
fn run_program(gear_cell: &CellId, gate_root: [u8; 32], wear_cap: Option<u64>) -> CellProgram {
    let mut constraints = vec![StateConstraint::ObservedFieldEquals {
        local_field: ABILITY_SLOT,
        source_cell: *gear_cell.as_bytes(),
        source_field: OWNER_SLOT,
        at_root: gate_root,
        proof_witness_index: 0,
    }];
    if wear_cap.is_some() {
        // Durability: each ability use advances `wear` (StrictMonotonic) and it must stay
        // within the seeded `wear_cap` (a cross-slot ceiling) — a real monotone sink.
        constraints.push(StateConstraint::StrictMonotonic { index: WEAR_SLOT });
        constraints.push(StateConstraint::FieldLteField {
            left_index: WEAR_SLOT,
            right_index: WEAR_CAP_SLOT,
        });
    }
    CellProgram::Predicate(constraints)
}

/// Assemble the equip world's cells (gear + run) on a fresh executor and grant the driver
/// caps to both. `gate_root` installs the run cell's cross-cell gate at that finalized
/// gear root; `None` leaves the run cell ungated (the dry-run that computes the root).
fn assemble(
    gear_token: [u8; 32],
    gate_root: Option<[u8; 32]>,
    wear_cap: Option<u64>,
) -> (EmbeddedExecutor, AppCipherclerk, CellId, CellId, CellId) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::from_seed(DRIVER_SEED), GEAR_FEDERATION);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let driver = cclerk.cell_id();

    // The GEAR item — its OWN cell, token = the asset-bound content address. Its OWNER
    // slot is WRITE-ONCE: equipping stamps the equipper's tag once (first-equipper-wins).
    let gear = world_cell(
        GEAR_CELL_SEED,
        gear_token,
        CellProgram::Predicate(vec![StateConstraint::WriteOnce { index: OWNER_SLOT }]),
    );
    let gear_id = gear.id();

    // The RUN / character cell — gated on the PEER gear cell once we know its equipped root.
    let run_token = {
        let mut h = blake3::Hasher::new_derive_key("dreggnet-gear-run-cell-v1");
        h.update(&gear_token);
        *h.finalize().as_bytes()
    };
    let run_program = match gate_root {
        Some(at_root) => run_program(&gear_id, at_root, wear_cap),
        None => CellProgram::None,
    };
    let run = world_cell(RUN_CELL_SEED, run_token, run_program);
    let run_id = run.id();

    exec.ensure_cell(gear).expect("gear cell inserts");
    exec.ensure_cell(run).expect("run cell inserts");

    exec.with_ledger_mut(|ledger| {
        if let Some(agent) = ledger.get_mut(&driver) {
            agent.capabilities.grant(gear_id, AuthRequired::None);
            agent.capabilities.grant(run_id, AuthRequired::None);
        }
        // Seed the durability ceiling on the run cell (a setup write, not a turn).
        if let Some(cap) = wear_cap {
            if let Some(run_cell) = ledger.get_mut(&run_id) {
                run_cell
                    .state
                    .set_field(WEAR_CAP_SLOT as usize, field_from_u64(cap));
            }
        }
    });

    (exec, cclerk, driver, gear_id, run_id)
}

/// Compute the gear cell's **post-equip finalized commitment** — the finalized peer root
/// the run cell's cross-cell gate pins. A throwaway world equips the gear with a real turn
/// and reads the resulting committed commitment. Deterministic: the real world's gear
/// reaches the byte-identical commitment after the same equip. Mirrors
/// `multicell::finalized_take_root`.
fn finalized_equip_root(gear_token: [u8; 32]) -> [u8; 32] {
    let (exec, cclerk, driver, gear_id, _run) = assemble(gear_token, None, None);
    let tag = actor_tag(driver);
    issue(
        &exec,
        &cclerk,
        gear_id,
        "equip",
        vec![set_field(gear_id, OWNER_SLOT as usize, tag)],
        vec![],
    )
    .expect("the dry-run equip commits");
    exec.with_ledger_mut(|ledger| {
        ledger
            .get(&gear_id)
            .expect("gear present after equip")
            .state_commitment()
    })
}

/// A `SetField` effect on `cell`'s slot `index`.
pub(crate) fn set_field(cell: CellId, index: usize, value: FieldElement) -> Effect {
    Effect::SetField { cell, index, value }
}

/// Build, sign (over the attached witness blobs), wrap, and submit one turn — a real
/// cap-bounded turn the executor admits IFF every cap AND every touched cell's program
/// admits it. Mirrors `multicell::issue`.
pub(crate) fn issue(
    exec: &EmbeddedExecutor,
    cclerk: &AppCipherclerk,
    target: CellId,
    method: &str,
    effects: Vec<Effect>,
    witness_blobs: Vec<WitnessBlob>,
) -> Result<TurnReceipt, String> {
    let mut action = cclerk.make_action(target, method, effects);
    action.witness_blobs = witness_blobs;
    let action = cclerk.sign_action(action);
    let turn = cclerk.make_turn(action);
    exec.submit_turn(&turn).map_err(|e| e.to_string())
}

/// **The live equip world** — the shared executor ledger holding the gear cell + the run
/// cell, plus the finalized gear root the run cell's cross-cell gate pins.
pub struct EquipGate {
    exec: EmbeddedExecutor,
    cclerk: AppCipherclerk,
    driver: CellId,
    gear_cell: CellId,
    run_cell: CellId,
    gate_root: [u8; 32],
}

impl EquipGate {
    /// Deploy the equip world for `gear`, pinning the run cell's cross-cell gate at the
    /// gear's post-equip finalized commitment. `wear_cap` (if any) installs the durability
    /// sink.
    pub fn deploy(gear: &Gear, wear_cap: Option<u64>) -> EquipGate {
        let gear_token = gear.cell_token();
        let gate_root = finalized_equip_root(gear_token);
        let (exec, cclerk, driver, gear_cell, run_cell) =
            assemble(gear_token, Some(gate_root), wear_cap);
        EquipGate {
            exec,
            cclerk,
            driver,
            gear_cell,
            run_cell,
            gate_root,
        }
    }

    /// The gear item cell id — its OWN cell, content-bound to the asset.
    pub fn gear_cell(&self) -> CellId {
        self.gear_cell
    }
    /// The run / character cell id.
    pub fn run_cell(&self) -> CellId {
        self.run_cell
    }
    /// The finalized gear root the cross-cell gate pins.
    pub fn gate_root(&self) -> [u8; 32] {
        self.gate_root
    }
    /// The identity tag an equip stamps for this driver (the value the ability unlocks to).
    pub fn tag(&self) -> FieldElement {
        actor_tag(self.driver)
    }

    /// Read a cell's slot from the committed ledger.
    pub fn read(&self, cell: CellId, slot: usize) -> Option<FieldElement> {
        self.exec.cell_state(cell).map(|s| s.fields[slot])
    }
    /// The gear cell's live committed state commitment (its finalized root right now).
    pub fn gear_root(&self) -> [u8; 32] {
        self.exec
            .with_ledger_mut(|l| l.get(&self.gear_cell).map(|c| c.state_commitment()))
            .unwrap_or([0u8; 32])
    }

    /// **Equip the gear** — a real turn on the gear item's OWN cell, stamping the equipper
    /// tag into its WRITE-ONCE owner slot. After it, the gear's finalized commitment IS
    /// [`Self::gate_root`], so the run cell's cross-cell ability gate can open.
    pub fn equip(&self) -> Result<TurnReceipt, String> {
        let tag = self.tag();
        issue(
            &self.exec,
            &self.cclerk,
            self.gear_cell,
            "equip",
            vec![set_field(self.gear_cell, OWNER_SLOT as usize, tag)],
            vec![],
        )
    }

    /// Attempt the gated ability use — writes `ability_value` into the run cell's ABILITY
    /// slot, carrying the Merkle-open witness iff `with_witness`, and advancing `wear` iff
    /// the durability sink is installed. The executor admits IFF the run cell's
    /// `ObservedFieldEquals` passes (gear at the gate root AND `ability_value ==
    /// gear.OWNER` AND witness present) AND the wear teeth pass.
    pub fn use_ability(
        &self,
        ability_value: FieldElement,
        with_witness: bool,
    ) -> Result<TurnReceipt, String> {
        let blobs = if with_witness {
            vec![peer_finalized_witness(self.gate_root)]
        } else {
            vec![]
        };
        let mut effects = vec![set_field(
            self.run_cell,
            ABILITY_SLOT as usize,
            ability_value,
        )];
        // If the durability sink is installed, advance wear on this use.
        let has_wear = self
            .read(self.run_cell, WEAR_CAP_SLOT as usize)
            .map(|c| c != FIELD_ZERO)
            .unwrap_or(false);
        if has_wear {
            let old = self
                .read(self.run_cell, WEAR_SLOT as usize)
                .map(field_to_u64)
                .unwrap_or(0);
            effects.push(set_field(
                self.run_cell,
                WEAR_SLOT as usize,
                field_from_u64(old + 1),
            ));
        }
        issue(
            &self.exec,
            &self.cclerk,
            self.run_cell,
            "use_ability",
            effects,
            blobs,
        )
    }

    /// The HONEST ability use: value == the gear's equipped owner tag, witness attached —
    /// what commits once the gear is really equipped.
    pub fn use_ability_honest(&self) -> Result<TurnReceipt, String> {
        self.use_ability(self.tag(), true)
    }

    /// Whether the gated ability has committed (the run cell's ABILITY slot is set).
    pub fn ability_unlocked(&self) -> bool {
        self.read(self.run_cell, ABILITY_SLOT as usize)
            .map(|v| v != FIELD_ZERO)
            .unwrap_or(false)
    }
    /// The current committed wear (the durability sink's spent counter).
    pub fn wear(&self) -> u64 {
        self.read(self.run_cell, WEAR_SLOT as usize)
            .map(field_to_u64)
            .unwrap_or(0)
    }
}

/// The inverse of [`field_from_u64`], which stores the value big-endian in bytes `[24..32]`.
pub(crate) fn field_to_u64(f: FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

// ═══════════════════════════════════════════════════════════════════════════════
// The loadout — composing the two teeth into "own AND equip to use".
// ═══════════════════════════════════════════════════════════════════════════════

/// A player's **loadout** for one piece of gear: the owned asset (the [`Armory`]) + the
/// live cross-cell equip world (the [`EquipGate`]). [`Self::equip`] enforces "own AND
/// equip": it FIRST proves asset ownership (a non-owner is refused cryptographically) and
/// only THEN stamps the gear cell — so the ability cannot unlock without BOTH teeth.
pub struct Loadout {
    /// The owned-gear armory (the asset ledger).
    pub armory: Armory,
    /// The live cross-cell equip world.
    pub gate: EquipGate,
    gear: Gear,
}

/// Why a loadout equip could not complete.
#[derive(Debug)]
pub enum EquipError {
    /// The equipper does not own the gear — the asset layer's signature gate refused the
    /// ownership proof (a non-owner cannot equip).
    NotOwner(AssetError),
    /// The cross-cell equip turn was refused by the executor.
    GateRefused(String),
}

impl std::fmt::Display for EquipError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EquipError::NotOwner(e) => write!(f, "not the owner: {e}"),
            EquipError::GateRefused(r) => write!(f, "equip gate refused: {r}"),
        }
    }
}

impl Loadout {
    /// Build a loadout for `gear` (already forged in `armory`), with an optional
    /// durability cap.
    pub fn new(armory: Armory, gear: Gear, wear_cap: Option<u64>) -> Self {
        let gate = EquipGate::deploy(&gear, wear_cap);
        Loadout { armory, gate, gear }
    }

    /// **Equip the gear as `holder_label`** — the "own AND equip" conjunction:
    /// 1. prove asset ownership (an owner-signed self-transfer); a NON-OWNER is refused
    ///    here (the asset signature gate) and the gear cell is never stamped;
    /// 2. stamp the gear cell (the cross-cell equip turn), reaching the finalized root
    ///    that unlocks the run cell's ability.
    pub fn equip(&mut self, holder_label: &str) -> Result<(), EquipError> {
        self.armory
            .prove_ownership(&self.gear, holder_label)
            .map_err(EquipError::NotOwner)?;
        self.gate.equip().map_err(EquipError::GateRefused)?;
        Ok(())
    }

    /// **Equip and return the cross-cell equip [`TurnReceipt`]** — the same "own AND equip"
    /// conjunction as [`Self::equip`], but surfacing the real committed equip turn's receipt
    /// (for an [`Offering`](dreggnet_offerings::Offering)'s `Outcome::Landed`). A non-owner is
    /// still refused at the ownership proof (nothing stamped).
    pub fn equip_with_receipt(&mut self, holder_label: &str) -> Result<TurnReceipt, EquipError> {
        self.armory
            .prove_ownership(&self.gear, holder_label)
            .map_err(EquipError::NotOwner)?;
        self.gate.equip().map_err(EquipError::GateRefused)
    }

    /// The owned gear.
    pub fn gear(&self) -> &Gear {
        &self.gear
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::statblock::Rarity;

    fn flaming_sword() -> StatBlock {
        // A legendary weapon whose rune keys the flaming-sword ability.
        StatBlock::weapon(Rarity::Legendary, 12, 0xF1A3E)
    }

    /// The gear is a real OWNED asset content-bound to its stat block: forging mints an
    /// asset owned by the smith, whose id commits the traits_root — a DIFFERENT block
    /// forges a DIFFERENT asset id (rarity/traits provably bound), and the same block
    /// forges the same id (deterministic content address).
    #[test]
    fn forged_gear_is_an_owned_content_bound_asset() {
        let mut armory = Armory::new();
        let alice = armory.pubkey_of("alice");
        let gear = armory.forge("alice", flaming_sword());

        // Owned by the smith.
        assert_eq!(
            armory.current_owner(&gear),
            Some(alice),
            "the smith owns the forged gear"
        );
        assert!(
            armory.verify_provenance(&gear).verified,
            "the mint's provenance verifies"
        );

        // The asset id content-commits the stat block: a rarer variant is a different asset.
        let mut armory2 = Armory::new();
        armory2.pubkey_of("alice");
        let common = armory2.forge("alice", StatBlock::weapon(Rarity::Common, 12, 0xF1A3E));
        assert_ne!(
            gear.asset_id, common.asset_id,
            "a different stat block (rarity) content-forges a different asset id"
        );

        // The same smith + same block is the same content address (deterministic).
        let mut armory3 = Armory::new();
        armory3.pubkey_of("alice");
        let same = armory3.forge("alice", flaming_sword());
        assert_eq!(
            gear.asset_id, same.asset_id,
            "same block → same content-addressed asset id"
        );
    }

    /// A NON-OWNER cannot equip: the asset layer's signature gate refuses the ownership
    /// proof (a self-transfer only the real owner can sign), so the gear cell is never
    /// stamped and the ability stays LOCKED. The owner, by contrast, equips and unlocks.
    #[test]
    fn a_non_owner_cannot_equip() {
        let mut armory = Armory::new();
        armory.pubkey_of("alice");
        armory.pubkey_of("mallory");
        let gear = armory.forge("alice", flaming_sword());
        let mut loadout = Loadout::new(armory, gear, None);

        // Mallory does not own the sword — the ownership proof is a cryptographic refusal.
        let refused = loadout.equip("mallory");
        assert!(
            matches!(refused, Err(EquipError::NotOwner(_))),
            "a non-owner's equip is refused by the asset signature gate, got {refused:?}"
        );
        // The ability is still locked (the gear cell was never stamped).
        let locked = loadout.gate.use_ability_honest();
        assert!(
            locked.is_err(),
            "with no valid equip, the cross-cell ability stays refused, got {locked:?}"
        );
        assert!(
            !loadout.gate.ability_unlocked(),
            "anti-ghost: ability never fired"
        );

        // The rightful owner CAN equip + unlock.
        loadout.equip("alice").expect("the owner equips");
        loadout
            .gate
            .use_ability_honest()
            .expect("the equipped owner unlocks the ability");
        assert!(loadout.gate.ability_unlocked());
    }

    /// THE CROSS-CELL GATE (non-vacuous): the ability is REFUSED before the gear is
    /// equipped (the gear is not at the pinned root ⇒ the authority has no binding) and
    /// COMMITS after a real equip — the SAME honest ability turn, the equip the only pivot.
    #[test]
    fn equipping_unlocks_the_cross_cell_ability() {
        let mut armory = Armory::new();
        armory.pubkey_of("alice");
        let gear = armory.forge("alice", flaming_sword());
        let mut loadout = Loadout::new(armory, gear, None);

        // BEFORE equip: gear is not at the gate root ⇒ the ability is refused (fail-closed).
        assert_ne!(
            loadout.gate.gear_root(),
            loadout.gate.gate_root(),
            "gear is not equipped yet"
        );
        let before = loadout.gate.use_ability_honest();
        assert!(
            before.is_err(),
            "the cross-cell ability must refuse before the gear is equipped, got {before:?}"
        );
        assert_eq!(
            loadout
                .gate
                .read(loadout.gate.run_cell(), ABILITY_SLOT as usize),
            Some([0u8; 32]),
            "anti-ghost: ability slot untouched"
        );

        // Equip (own + stamp) → gear reaches the pinned root.
        loadout.equip("alice").expect("the owner equips");
        assert_eq!(
            loadout.gate.gear_root(),
            loadout.gate.gate_root(),
            "the gear is now AT the finalized equip root"
        );

        // AFTER equip: the SAME honest ability turn commits — its admission read the PEER cell.
        let after = loadout
            .gate
            .use_ability_honest()
            .expect("with the gear equipped + the witness, the ability unlocks");
        assert_ne!(after.turn_hash, [0u8; 32]);
        assert!(loadout.gate.ability_unlocked());
    }

    /// A SPOOFED equip is refused from every angle, even after a real equip:
    /// * a stripped witness fails closed;
    /// * a divergent ability value (not the gear's owner) is refused;
    /// and BEFORE any equip, the honest value+witness is refused too (the peer condition
    /// is not met). The cross-cell tooth bites — no client `if` to bypass.
    #[test]
    fn a_spoofed_equip_is_refused() {
        let mut armory = Armory::new();
        armory.pubkey_of("alice");
        let gear = armory.forge("alice", flaming_sword());
        let mut loadout = Loadout::new(armory, gear, None);

        // Spoof 1 — claim the ability with the gear UN-equipped (honest value + witness).
        let spoof_unequipped = loadout.gate.use_ability(loadout.gate.tag(), true);
        assert!(spoof_unequipped.is_err(), "claiming un-equipped is refused");

        loadout.equip("alice").expect("the owner equips");

        // Spoof 2 — a stripped witness (peer condition met, but no Merkle-open proof).
        let spoof_no_witness = loadout.gate.use_ability(loadout.gate.tag(), false);
        assert!(spoof_no_witness.is_err(), "a stripped witness fails closed");

        // Spoof 3 — a divergent value (not the gear's real owner tag).
        let mut wrong = loadout.gate.tag();
        wrong[1] ^= 0xAA;
        let spoof_wrong = loadout.gate.use_ability(wrong, true);
        assert!(spoof_wrong.is_err(), "a divergent ability value is refused");

        // Anti-ghost: no spoof committed.
        assert!(
            !loadout.gate.ability_unlocked(),
            "no spoof fired the ability"
        );

        // The honest use still commits.
        loadout
            .gate
            .use_ability_honest()
            .expect("the honest use commits");
        assert!(loadout.gate.ability_unlocked());
    }

    /// The gear PERSISTS across runs: after a run equips + uses the sword, the asset is
    /// still owned by alice and its provenance verifies; a NEW run (a fresh equip world for
    /// the SAME asset) re-equips and unlocks again — the owned asset is the durable thing.
    #[test]
    fn gear_persists_across_runs() {
        let mut armory = Armory::new();
        let alice = armory.pubkey_of("alice");
        let gear = armory.forge("alice", flaming_sword());

        // Run 1 — equip + use, then reclaim the persistent asset ledger.
        let mut loadout = Loadout::new(armory, gear, None);
        loadout.equip("alice").expect("run 1 equip");
        loadout.gate.use_ability_honest().expect("run 1 ability");
        assert!(loadout.gate.ability_unlocked());
        let Loadout { armory, .. } = loadout;

        // The asset persisted: still owned by alice, provenance clean, lineage grew (the
        // equip's ownership proof is a real self-transfer version).
        assert_eq!(
            armory.current_owner(&gear),
            Some(alice),
            "still alice's after run 1"
        );
        let report = armory.verify_provenance(&gear);
        assert!(
            report.verified,
            "provenance verifies across the run: {report:?}"
        );
        assert!(
            armory.lineage_len(&gear) >= 2,
            "the equip proof grew the lineage"
        );

        // Run 2 — a brand-new equip world for the SAME durable asset re-unlocks.
        let mut loadout2 = Loadout::new(armory, gear, None);
        loadout2
            .equip("alice")
            .expect("run 2 equip (the gear carried over)");
        loadout2.gate.use_ability_honest().expect("run 2 ability");
        assert!(loadout2.gate.ability_unlocked());
    }

    /// DURABILITY (the wear sink): with a wear cap of 2, the first two ability uses commit
    /// (wear 0→1→2) and the third is REFUSED (would push wear past the cap) — a real
    /// monotone sink that spends the gear down.
    #[test]
    fn durability_is_a_monotone_wear_sink() {
        let mut armory = Armory::new();
        armory.pubkey_of("alice");
        let gear = armory.forge("alice", flaming_sword());
        let mut loadout = Loadout::new(armory, gear, Some(2));

        loadout.equip("alice").expect("equip");
        loadout.gate.use_ability_honest().expect("use 1 (wear 0→1)");
        assert_eq!(loadout.gate.wear(), 1);
        loadout.gate.use_ability_honest().expect("use 2 (wear 1→2)");
        assert_eq!(loadout.gate.wear(), 2);

        // The third use would push wear to 3 > cap 2 — refused by FieldLteField.
        let spent = loadout.gate.use_ability_honest();
        assert!(
            spent.is_err(),
            "a use past the durability cap is refused (the gear is spent), got {spent:?}"
        );
        assert_eq!(
            loadout.gate.wear(),
            2,
            "anti-ghost: wear did not pass the cap"
        );
    }
}
