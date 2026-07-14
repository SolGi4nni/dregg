//! # `dreggnet-companion` — an owned ASSET fused with a leveling CELL: a provable bond.
//!
//! COMPANIONS (GAME-INFRA-ROADMAP progression #5). A **companion** is two real dregg
//! constructions FUSED:
//!
//! * an **owned identity** — a [`dreggnet_asset`] note, HATCHED from a provably-fair draw
//!   ([`procgen_dregg::verified_stream`] over a committed seed), owned by the player's key.
//!   Its rarity is the draw tail (a fair-hatched legendary is a *provable* ~3% flex, not a
//!   claim), its lineage is content-addressed, and — being an asset — it is **tradeable**
//!   (the owner-gated transfer) and **un-dupable** (a version spends exactly once; a
//!   double-spend is a real executor refusal).
//! * a **progression cell** — the REAL [`dungeon_on_dregg::progression`] `hero_story`
//!   leveling program, reused verbatim and hosted in a shared executor. XP is a monotone
//!   cell slot; a level-up is a real turn GATED on `FieldGte(xp, threshold(L))`, so a
//!   companion **cannot be faked-leveled** (a level-up without the earned XP is a real
//!   refusal). The hardcore `dead` slot is `WriteOnce`-final: a companion's death is
//!   un-forgeable and un-undoable — the bond has real stakes.
//!
//! ## The fusion: a buff that applies CROSS-CELL because the companion is at level N
//!
//! The point of fusing the two is that a RUN can gate an aid on the companion's progression
//! as a **kernel predicate**, not host bookkeeping. The leveling cell and a run's **buff
//! cell** share ONE [`EmbeddedExecutor`], so the buff cell carries the [`multicell`] pattern
//! — a [`StateConstraint::ObservedFieldEquals`] naming the companion's `level` slot at the
//! finalized commitment it reaches upon hitting the required level ([`checkpoint_root`]):
//!
//! * **below the required level** the companion's live commitment is NOT the checkpoint root
//!   ⇒ the executor's finalized-root authority has no binding for it ⇒ the buff turn is
//!   REFUSED (fail-closed);
//! * **at the required level** the companion's commitment IS the checkpoint root ⇒ the
//!   authority binds `level -> N` ⇒ the buff turn (writing the level value, with the witness)
//!   COMMITS. Its admission read ANOTHER cell's state — the companion's — as a real predicate.
//!
//! Combined with the asset-layer ownership check, the buff reads exactly "this aid applies
//! BECAUSE you own a companion at level N". Below-level: refused. At-level: commits.
//!
//! ## What a companion CANNOT be
//!
//! * **faked-leveled** — the level-up gate is the XP-gated executor tooth (a level-up
//!   without the XP mints nothing);
//! * **duped** — the identity is a [`dreggnet_asset`] version; a double-spend of a spent
//!   version is refused by its own `StrictMonotonic(spent)` tooth;
//! * **resurrected** — the hardcore `dead` slot is `WriteOnce`; a dead companion's
//!   resurrection is refused and it earns nothing thereafter.
//!
//! And the **bond** — that you genuinely RAISED it across runs — is a provable receipt
//! chain: the leveling turns chain (`pre == prev.post`) and the asset lineage re-verifies.
//!
//! ## Honest scope — what is real, what is a named seam
//!
//! REAL, DRIVEN in [`mod tests`] against the real executor-refereed layers: the fair hatch
//! (owned, content-addressed, rarity re-derivable; a forged hatch mints nothing), the
//! XP-gated leveling (a premature level-up is a real refusal), the cross-cell buff (refused
//! below level, commits at level — the `ObservedFieldEquals` bites), the un-dupable identity
//! (a double-spend refused), the `WriteOnce`-final permadeath, and the receipt-chain bond.
//!
//! The identity note lives in the asset layer's sovereign holder ledger; the leveling + buff
//! cells live in a shared RUN executor, and a companion BINDS the two (its [`AssetId`] to its
//! leveling cell). As in [`multicell`], the embedded host recomputes the peer's finalized
//! value from its own committed ledger (turns commit synchronously); a production finalized-
//! root channel furnishing the peer root from an independently-finalized chain is the named
//! transport add. The cross-cell gate pins a SPECIFIC level checkpoint (the
//! `ObservedFieldEquals` equality-at-root semantics); a native cross-cell `>=` predicate
//! (buff applies at level N *or higher*) is a named residual. Other NAMED residuals: a
//! companion's ABILITIES (an ability keyed to the companion's level/rarity), BREEDING (two
//! companions -> an egg via a fair draw, the [`dreggnet_craft`]-style two-input sink),
//! companion TRADING through the `escrow-market` swap (the transfer primitive is here), and
//! richer permadeath BONDS (a death-earned keepsake).

use std::collections::{HashMap, HashSet};

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellProgram, Effect, EmbeddedExecutor,
    FieldElement, StateConstraint, TurnReceipt, field_from_u64,
};
use dregg_cell::{Cell, Permissions};
use dregg_turn::action::{WitnessBlob, WitnessKind};
use dreggnet_asset::{AssetError, AssetId, AssetWorld, ProvenanceReport, TransferReceipt};
use dungeon_on_dregg::loot::{Rarity, rarity_of_roll};
use dungeon_on_dregg::progression::{
    DEAD_SLOT, GAIN_XP_METHOD, HARDCORE_PERISH_METHOD, HARDCORE_RESURRECT_METHOD, LEVEL_SLOT,
    XP_SLOT, hero_story, level_up_method, xp_threshold,
};
use procgen_dregg::CommittedSeed;

// ── Fair-hatch constants ───────────────────────────────────────────────────────────

/// The index of the hatch rarity draw within the verified procgen stream (well under the
/// committed `DRAW_COUNT` budget, so the draw is always in range).
const HATCH_DRAW_INDEX: u32 = 0;

/// The face count of a hatch draw — a `d100` (`0..100`), so the rarity tiers (shared with
/// [`dungeon_on_dregg::loot`]) carve a clean percentage distribution.
const RARITY_FACES: u64 = 100;

/// The domain tag folded into a hatch seed derivation (so a hatch draw stream can never
/// collide with the loot / craft / dungeon-generation streams that share a beacon).
const DOMAIN_HATCH_SEED: &[u8] = b"dreggnet-companion/hatch-seed/v1";

/// The domain tag for a hatch's content commitment (the companion asset's mint seed).
const DOMAIN_HATCH_COMMIT: &[u8] = b"dreggnet-companion/hatch-commitment/v1";

// ── The shared RUN executor (leveling + buff cells) ─────────────────────────────────

/// The buff cell's marker slot — the gated write, admitted only against the cross-cell
/// level condition. Written to the companion's level value; the `ObservedFieldEquals`
/// tooth admits it IFF that equals the peer companion's `level` at the checkpoint root.
const BUFF_SLOT: u8 = 0;

/// The federation the run's leveling/buff turns commit under (a fixed run federation id).
const RUN_FEDERATION: [u8; 32] = [0xC0; 32];

/// A FIXED run-driver seed — so the [`checkpoint_root`] dry-run (which redeploys a
/// companion's leveling cell to read its at-level commitment) and the live roost share ONE
/// driver identity, exactly the [`multicell`] `DRIVER_SEED` discipline.
const RUN_DRIVER_SEED: [u8; 64] = [0x2C; 64];

/// A stable byte tag for a rarity (folded into the hatch commitment so the rarity is bound
/// into the companion asset's content address). Mirrors the loot layer's private tag.
fn rarity_tag(r: Rarity) -> u8 {
    match r {
        Rarity::Common => 0,
        Rarity::Uncommon => 1,
        Rarity::Rare => 2,
        Rarity::Legendary => 3,
    }
}

/// Derive the **hatch seed** for a companion from a committed beacon value, the species
/// label, and a sequence — a domain-separated hash, so every hatch draws a fresh,
/// reproducible, beacon-bound stream (a verifier who holds the beacon re-derives it).
pub fn derive_hatch_seed(beacon: &CommittedSeed, species: &str, seq: u64) -> CommittedSeed {
    let mut h = blake3::Hasher::new();
    h.update(&(DOMAIN_HATCH_SEED.len() as u64).to_le_bytes());
    h.update(DOMAIN_HATCH_SEED);
    h.update(beacon.as_bytes());
    h.update(&(species.len() as u64).to_le_bytes());
    h.update(species.as_bytes());
    h.update(&seq.to_le_bytes());
    CommittedSeed::from_bytes(*h.finalize().as_bytes())
}

/// A resolved, provably-fair hatch: the beacon/species/seq it came from, the committed
/// hatch seed it was drawn from, the raw fair-draw face, and the rarity that face fixes.
/// [`reverify_hatch`] re-derives it from the committed seed alone, so a forged (fabricated /
/// rewritten) hatch is caught before any companion is minted.
#[derive(Clone, Debug)]
pub struct HatchDraw {
    /// The committed beacon value the hatch is anchored to (its provenance root; in the
    /// flagship the verified drand-beacon day-seed).
    pub beacon: CommittedSeed,
    /// The species / egg label the hatch came from (e.g. `"companion:frostwyrm"`).
    pub species: String,
    /// The hatch's sequence (distinct hatches under one beacon use distinct seqs).
    pub seq: u64,
    /// The committed hatch seed the fair draw was taken from ([`derive_hatch_seed`]).
    pub hatch_seed: CommittedSeed,
    /// The raw fair-draw face (`0..100`).
    pub roll: u64,
    /// The rarity the roll fixes (the [`dungeon_on_dregg::loot`] distribution).
    pub rarity: Rarity,
}

impl HatchDraw {
    /// The display line for a hatch (the roll/rarity are content-bound).
    pub fn describe(&self) -> String {
        format!(
            "{} hatch of `{}` (roll {}/{})",
            self.rarity.label(),
            self.species,
            self.roll,
            RARITY_FACES,
        )
    }
}

/// **Roll a real, provably-fair hatch** for a species under a committed beacon. Derives the
/// committed hatch seed, runs the VERIFIED procgen stream, and reads the fair-draw face + its
/// rarity. Deterministic in `(beacon, species, seq)` — the same context always re-derives
/// the identical draw (the fairness anchor is the committed seed; a player cannot grind a
/// favourable rarity without a different beacon/species/seq).
pub fn roll_hatch(beacon: &CommittedSeed, species: &str, seq: u64) -> HatchDraw {
    let hatch_seed = derive_hatch_seed(beacon, species, seq);
    let (_req, _ev, stream) = procgen_dregg::verified_stream(&hatch_seed);
    let roll = stream
        .draw_bounded(HATCH_DRAW_INDEX, RARITY_FACES)
        .expect("the hatch draw index is within the committed budget and RARITY_FACES > 0");
    HatchDraw {
        beacon: *beacon,
        species: species.to_string(),
        seq,
        hatch_seed,
        roll,
        rarity: rarity_of_roll(roll),
    }
}

/// **Re-verify a hatch is a real fair draw** — the tooth that refuses a forged hatch.
/// Recomputes the hatch seed from the claimed beacon/species/seq (a mismatch = a forged
/// provenance), re-derives the honest roll from the committed seed through the same verified
/// procgen stream, and confirms the claimed roll + rarity are exactly the fair draw's. A
/// fabricated legendary — a claim with no real draw, or a rewritten roll/rarity — fails here.
pub fn reverify_hatch(draw: &HatchDraw) -> Result<(), CompanionError> {
    let expect_seed = derive_hatch_seed(&draw.beacon, &draw.species, draw.seq);
    if expect_seed != draw.hatch_seed {
        return Err(CompanionError::Forged(
            "the hatch seed is not bound to the claimed beacon/species/seq".to_string(),
        ));
    }
    let (_req, _ev, stream) = procgen_dregg::verified_stream(&draw.hatch_seed);
    let true_roll = stream
        .draw_bounded(HATCH_DRAW_INDEX, RARITY_FACES)
        .map_err(|e| CompanionError::Forged(format!("the fair draw did not re-derive: {e:?}")))?;
    if true_roll != draw.roll {
        return Err(CompanionError::Forged(format!(
            "the claimed roll {} is not the fair draw {true_roll}",
            draw.roll
        )));
    }
    if rarity_of_roll(true_roll) != draw.rarity {
        return Err(CompanionError::Forged(format!(
            "the claimed rarity {:?} is not the roll's",
            draw.rarity
        )));
    }
    Ok(())
}

/// The hatch's **content commitment** — the mint seed the companion asset is minted under,
/// binding the beacon, the hatch seed, the fair roll, the rarity, and the species. The
/// companion's [`AssetId`] is derived from `blake3(player_pk ‖ this)`, so the companion's
/// content address itself encodes the hatch it came from (its provenance).
fn hatch_commitment(draw: &HatchDraw) -> Vec<u8> {
    let mut h = blake3::Hasher::new();
    h.update(&(DOMAIN_HATCH_COMMIT.len() as u64).to_le_bytes());
    h.update(DOMAIN_HATCH_COMMIT);
    h.update(draw.beacon.as_bytes());
    h.update(draw.hatch_seed.as_bytes());
    h.update(&draw.roll.to_le_bytes());
    h.update(&[rarity_tag(draw.rarity)]);
    h.update(&(draw.species.len() as u64).to_le_bytes());
    h.update(draw.species.as_bytes());
    h.finalize().as_bytes().to_vec()
}

/// A hatched **companion** — the fusion. Its [`AssetId`] is the owned, content-addressed
/// identity (in the asset layer); its `cell` is the real leveling cell (in the shared run
/// executor). Together they are the provable bond: an un-dupable identity you genuinely
/// raised.
#[derive(Clone, Debug)]
pub struct Companion {
    /// The stable, content-addressed asset id — the owned identity (the cross-cell handle a
    /// market names it by), bound to the hatch it came from.
    pub asset_id: AssetId,
    /// The hatch rarity (the fair-draw tier — a legendary is a provable flex).
    pub rarity: Rarity,
    /// The current owner's pubkey (at hatch, the player's key).
    pub owner: [u8; 32],
    /// The companion's leveling cell id (in the shared run executor). The cross-cell buff
    /// gate observes THIS cell's `level` slot.
    pub cell: CellId,
    /// The stable seed the leveling cell was deployed under — [`checkpoint_root`] redeploys
    /// the identical cell in a throwaway executor to read its at-level commitment.
    pub(crate) seed: u32,
}

/// A **run buff gate** — a real cross-cell predicate cell pinned at a companion's finalized
/// level-N checkpoint. [`CompanionRoost::attempt_buff`] drives a turn on it; the executor
/// admits it IFF the companion is AT the checkpoint (its live commitment == [`Self::checkpoint`])
/// and the written value matches the companion's `level` at that root.
#[derive(Clone, Debug)]
pub struct BuffGate {
    /// The buff cell (its `ObservedFieldEquals` names the companion's `level` slot).
    pub buff_cell: CellId,
    /// The companion level this buff requires.
    pub required_level: u64,
    /// The companion's finalized commitment upon reaching `required_level` — the pinned root.
    pub checkpoint: [u8; 32],
    /// The companion asset the buff belongs to (its owner is re-checked at activation).
    pub asset_id: AssetId,
    /// The companion's leveling cell the gate observes.
    pub companion_cell: CellId,
}

/// Why a companion operation could not complete.
#[derive(Clone, Debug)]
pub enum CompanionError {
    /// The claimed hatch is not a real fair draw (a fabricated / rewritten hatch) — no
    /// companion is minted. Carries the exact mismatch.
    Forged(String),
    /// This exact hatch has already been claimed (a hatch mints exactly once).
    AlreadyHatched,
    /// The acting player is not the companion asset's current owner (the asset-layer
    /// ownership gate) — a buff cannot be activated by a non-owner.
    NotOwner,
    /// A real executor refusal on the shared run executor — a premature (un-earned) level-up,
    /// a below-level buff (the cross-cell gate fails closed), a dead companion's earn/level,
    /// or a resurrection (the `WriteOnce` `dead` tooth). The receipt-why is carried.
    Refused(String),
    /// The underlying asset layer refused an operation (a non-owner / double-spend transfer,
    /// or an unknown asset). Carries the asset error.
    Asset(AssetError),
    /// No companion with this asset id has been hatched in this roost.
    Unknown,
}

impl std::fmt::Display for CompanionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompanionError::Forged(w) => write!(f, "forged hatch refused: {w}"),
            CompanionError::AlreadyHatched => write!(f, "this hatch was already claimed"),
            CompanionError::NotOwner => write!(f, "not the companion's owner"),
            CompanionError::Refused(w) => write!(f, "run turn refused: {w}"),
            CompanionError::Asset(e) => write!(f, "asset layer refused: {e}"),
            CompanionError::Unknown => write!(f, "unknown companion"),
        }
    }
}

impl std::error::Error for CompanionError {}

// ── Shared-executor cell assembly (mirrors `multicell`) ─────────────────────────────

/// A cell whose permissions gate nothing (every op `AuthRequired::None`) — the leveling /
/// buff cells the run driver acts on. The load-bearing teeth are the leveling program's
/// XP gate + `WriteOnce(dead)`, and the buff cell's cross-cell `ObservedFieldEquals`; the
/// per-cell permissions are opened so a gate, not a signature-permission mismatch, is what a
/// test observes.
fn open_permissions() -> Permissions {
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

/// Build an open run cell with `program` installed, deterministic in `seed`.
fn run_cell(seed: u32, program: CellProgram) -> Cell {
    let mut pk = [0u8; 32];
    pk[..4].copy_from_slice(&seed.to_le_bytes());
    pk[31] = (seed as u8).wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], 0);
    cell.permissions = open_permissions();
    cell.program = program;
    cell
}

/// A fresh run executor + its driver identity + the driver cell id (the [`multicell`] driver
/// discipline, one serial writer over the run's leveling/buff cell graph).
fn fresh_run() -> (EmbeddedExecutor, AppCipherclerk, CellId) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::from_seed(RUN_DRIVER_SEED), RUN_FEDERATION);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let driver = cclerk.cell_id();
    (exec, cclerk, driver)
}

/// Insert `cell` into `exec` and grant the run driver a cap reaching it (an ungranted target
/// is a real `CapabilityNotHeld` refusal; the cross-cell gate is a SEPARATE tooth on top).
fn install(exec: &EmbeddedExecutor, driver: CellId, cell: Cell) -> CellId {
    let id = cell.id();
    exec.ensure_cell(cell).expect("run cell inserts");
    exec.with_ledger_mut(|ledger| {
        if let Some(agent) = ledger.get_mut(&driver) {
            agent.capabilities.grant(id, AuthRequired::None);
        }
    });
    id
}

/// Deploy a companion **leveling cell** — the REAL `progression::hero_story` program
/// (XP-gated levels + the `WriteOnce` hardcore `dead` flag) reused verbatim — into `exec`.
fn deploy_leveling(exec: &EmbeddedExecutor, driver: CellId, seed: u32) -> CellId {
    install(exec, driver, run_cell(seed, hero_story().program))
}

/// A `SetField` effect on `cell`'s slot `index`.
fn set_field(cell: CellId, index: u8, value: FieldElement) -> Effect {
    Effect::SetField {
        cell,
        index: index as usize,
        value,
    }
}

/// Build, sign (over the attached witness blobs), wrap, and submit one run turn — a real
/// cap-bounded turn `exec` admits IFF every cap AND the touched cell's program admits it.
fn issue(
    exec: &EmbeddedExecutor,
    cclerk: &AppCipherclerk,
    target: CellId,
    method: &str,
    effects: Vec<Effect>,
    witness_blobs: Vec<WitnessBlob>,
) -> Result<TurnReceipt, String> {
    let mut action = cclerk.make_action(target, method, effects);
    action.witness_blobs = witness_blobs;
    // Re-sign AFTER attaching the witness (the signature covers `Action::hash`, which covers
    // `witness_blobs` — a witness bolted on post-signing would be a bad sig).
    let action = cclerk.sign_action(action);
    let turn = cclerk.make_turn(action);
    exec.submit_turn(&turn).map_err(|e| e.to_string())
}

/// Read a leveling/buff cell's committed `slot` as a `u64` (the `field_from_u64` big-endian
/// low-8-bytes layout).
fn read_u64(exec: &EmbeddedExecutor, cell: CellId, slot: u8) -> u64 {
    exec.cell_state(cell)
        .map(|s| {
            let f = s.fields[slot as usize];
            u64::from_be_bytes(f[24..32].try_into().expect("8 bytes"))
        })
        .unwrap_or(0)
}

/// The companion's live committed state commitment (its finalized root right now).
fn commitment_of(exec: &EmbeddedExecutor, cell: CellId) -> [u8; 32] {
    exec.with_ledger_mut(|l| l.get(&cell).map(|c| c.state_commitment()))
        .unwrap_or([0u8; 32])
}

// ── The canonical raising path (deterministic, so a checkpoint re-derives) ───────────

/// Earn XP on a leveling cell — a real `gain_xp` turn setting `xp += amount`. The executor's
/// `StrictMonotonic(xp)` (plus the global `Monotonic`) admits a real positive gain; the earn
/// case is also gated `FieldEquals(dead, 0)`, so a dead companion earns nothing.
fn lvl_train(
    exec: &EmbeddedExecutor,
    cclerk: &AppCipherclerk,
    cell: CellId,
    amount: u64,
) -> Result<TurnReceipt, String> {
    let new_xp = read_u64(exec, cell, XP_SLOT) + amount;
    issue(
        exec,
        cclerk,
        cell,
        GAIN_XP_METHOD,
        vec![set_field(cell, XP_SLOT, field_from_u64(new_xp))],
        vec![],
    )
}

/// Attempt to level a leveling cell to `target` — a real `level_up_to_target` turn. The
/// executor GATES it on `FieldGte(xp, xp_threshold(target))` + `FieldDelta(level, +1)` (one
/// step from `target-1`) + `FieldEquals(dead, 0)`. Without the earned XP the kernel REFUSES
/// it and nothing commits — a companion cannot be faked-leveled.
fn lvl_level(
    exec: &EmbeddedExecutor,
    cclerk: &AppCipherclerk,
    cell: CellId,
    target: u64,
) -> Result<TurnReceipt, String> {
    issue(
        exec,
        cclerk,
        cell,
        &level_up_method(target),
        vec![set_field(cell, LEVEL_SLOT, field_from_u64(target))],
        vec![],
    )
}

/// **The canonical raising path** to `target` (`1..=MAX_LEVEL`). For each level `L` above the
/// current one it earns EXACTLY `xp_threshold(L)` cumulative XP then levels to `L`. Prefix-
/// consistent (raising to `target-1` then to `target` visits the same states as raising to
/// `target` in one go) and driver-independent in the resulting commitments (the cell's field
/// VALUES are the pinned thresholds), so [`checkpoint_root`]'s dry-run re-derives the same
/// finalized commitment at each level.
fn raise_to(
    exec: &EmbeddedExecutor,
    cclerk: &AppCipherclerk,
    cell: CellId,
    target: u64,
) -> Result<(), String> {
    while read_u64(exec, cell, LEVEL_SLOT) < target {
        let next = read_u64(exec, cell, LEVEL_SLOT) + 1;
        let need = xp_threshold(next);
        let cur = read_u64(exec, cell, XP_SLOT);
        if cur < need {
            lvl_train(exec, cclerk, cell, need - cur)?;
        }
        lvl_level(exec, cclerk, cell, next)?;
    }
    Ok(())
}

/// **The finalized commitment a companion (deployed under `seed`) reaches upon hitting
/// `target`** — the root a buff gate pins. A throwaway run executor redeploys the identical
/// leveling cell (same `seed`) and raises it via the canonical path; the live companion,
/// raised the same way, reaches the byte-identical commitment. This is the only piece the
/// embedded harness precomputes (the [`multicell::finalized_take_root`] discipline); a
/// production finality source would surface this root from the committed chain / light client.
pub fn checkpoint_root(seed: u32, target: u64) -> [u8; 32] {
    let (exec, cclerk, driver) = fresh_run();
    let cell = deploy_leveling(&exec, driver, seed);
    raise_to(&exec, &cclerk, cell, target).expect("the canonical raise commits in the dry-run");
    commitment_of(&exec, cell)
}

// ── The roost ───────────────────────────────────────────────────────────────────────

/// **The companion roost** — the hatch / raise / buff / trade surface. It binds the two
/// substrates: an [`AssetWorld`] carrying each companion's owned identity note (hatch, trade,
/// double-spend refusal, provenance), and a shared RUN [`EmbeddedExecutor`] carrying the
/// leveling cells + buff cells (the XP-gated progression + the cross-cell buff gate). A
/// [`Companion`] fuses an [`AssetId`] to its leveling cell.
pub struct CompanionRoost {
    /// The owned-identity layer (hatch mint, trade, double-spend refusal, provenance).
    assets: AssetWorld,
    /// The shared run executor: leveling cells + buff cells (the cross-cell gate needs ONE
    /// ledger so a buff cell can observe a peer companion cell).
    exec: EmbeddedExecutor,
    /// The run driver (one serial writer over the run cell graph).
    cclerk: AppCipherclerk,
    driver: CellId,
    /// asset_id bytes -> the hatched companion.
    companions: HashMap<[u8; 32], Companion>,
    /// asset_id bytes -> the hatch it was minted from (its provenance record).
    hatches: HashMap<[u8; 32], HatchDraw>,
    /// The hatch commitments already claimed (a hatch mints exactly once).
    claimed: HashSet<Vec<u8>>,
    /// The next run-cell seed (distinct per leveling / buff cell in the shared executor).
    next_seed: u32,
}

impl Default for CompanionRoost {
    fn default() -> Self {
        Self::new()
    }
}

impl CompanionRoost {
    /// A fresh roost (no players, no companions).
    pub fn new() -> Self {
        let (exec, cclerk, driver) = fresh_run();
        CompanionRoost {
            assets: AssetWorld::new(),
            exec,
            cclerk,
            driver,
            companions: HashMap::new(),
            hatches: HashMap::new(),
            claimed: HashSet::new(),
            next_seed: 1,
        }
    }

    /// The deterministic pubkey of a player label (creating the identity if new).
    pub fn pubkey_of(&mut self, label: &str) -> [u8; 32] {
        self.assets.pubkey_of(label)
    }

    fn take_seed(&mut self) -> u32 {
        let s = self.next_seed;
        self.next_seed += 1;
        s
    }

    /// **Hatch a companion** for `player` from a fair draw — the forged-hatch gate + the
    /// mint + the leveling-cell deploy. The hatch is re-verified as a real fair draw
    /// ([`reverify_hatch`]); a forged hatch mints NOTHING. A verified hatch mints a
    /// [`dreggnet_asset`] note owned by `player` under the hatch's content commitment (so the
    /// companion's [`AssetId`] encodes the hatch it came from), and deploys the REAL leveling
    /// cell in the run executor. The two are FUSED as a [`Companion`].
    pub fn hatch(&mut self, player: &str, draw: &HatchDraw) -> Result<Companion, CompanionError> {
        reverify_hatch(draw)?;

        let commit = hatch_commitment(draw);
        if !self.claimed.insert(commit.clone()) {
            return Err(CompanionError::AlreadyHatched);
        }

        // The mint seed IS the hatch commitment, so the companion's asset id encodes the hatch.
        let asset_id = self.assets.mint(player, &commit);
        let owner = self
            .assets
            .current_owner(asset_id)
            .expect("a freshly-hatched companion has an owner");

        // The fused leveling cell — the real XP-gated progression program.
        let seed = self.take_seed();
        let cell = deploy_leveling(&self.exec, self.driver, seed);

        let comp = Companion {
            asset_id,
            rarity: draw.rarity,
            owner,
            cell,
            seed,
        };
        self.companions.insert(asset_id.bytes(), comp.clone());
        self.hatches.insert(asset_id.bytes(), draw.clone());
        Ok(comp)
    }

    // ── Leveling (the XP-gated progression; un-fakeable) ────────────────────────────

    /// **Earn XP** for a companion — a real `gain_xp` turn. A dead companion's earn is
    /// REFUSED (the earn case is gated `FieldEquals(dead, 0)`).
    pub fn train(&mut self, comp: &Companion, amount: u64) -> Result<TurnReceipt, CompanionError> {
        lvl_train(&self.exec, &self.cclerk, comp.cell, amount).map_err(CompanionError::Refused)
    }

    /// **Attempt to level a companion up by one** — a real `level_up_to_(current+1)` turn.
    /// The executor GATES it on the earned-XP floor; without the XP it is a real refusal and
    /// nothing commits (a companion cannot be faked-leveled). Returns the target level's
    /// receipt on commit.
    pub fn try_level_up(&mut self, comp: &Companion) -> Result<TurnReceipt, CompanionError> {
        let target = self.level_of(comp) + 1;
        lvl_level(&self.exec, &self.cclerk, comp.cell, target).map_err(CompanionError::Refused)
    }

    /// **Raise a companion to `target`** via the canonical path (earn each level's XP floor,
    /// then level). Returns the level-up receipts (each chains `pre == prev.post`).
    pub fn raise_to(
        &mut self,
        comp: &Companion,
        target: u64,
    ) -> Result<Vec<TurnReceipt>, CompanionError> {
        let mut receipts = Vec::new();
        while self.level_of(comp) < target {
            let next = self.level_of(comp) + 1;
            let need = xp_threshold(next);
            let cur = self.xp_of(comp);
            if cur < need {
                self.train(comp, need - cur)?;
            }
            receipts.push(self.try_level_up(comp)?);
        }
        Ok(receipts)
    }

    /// The companion's committed `level`.
    pub fn level_of(&self, comp: &Companion) -> u64 {
        read_u64(&self.exec, comp.cell, LEVEL_SLOT)
    }
    /// The companion's committed `xp`.
    pub fn xp_of(&self, comp: &Companion) -> u64 {
        read_u64(&self.exec, comp.cell, XP_SLOT)
    }
    /// Whether the companion is (hardcore-)dead — the committed `dead` flag is set.
    pub fn is_dead(&self, comp: &Companion) -> bool {
        read_u64(&self.exec, comp.cell, DEAD_SLOT) != 0
    }

    // ── Hardcore permadeath (WriteOnce-final) ───────────────────────────────────────

    /// **Kill a companion (HARDCORE)** — a real committed `perish` turn setting `dead = 1`.
    /// The global `WriteOnce(dead)` makes it a one-time, un-undoable write.
    pub fn perish(&mut self, comp: &Companion) -> Result<TurnReceipt, CompanionError> {
        issue(
            &self.exec,
            &self.cclerk,
            comp.cell,
            HARDCORE_PERISH_METHOD,
            vec![set_field(comp.cell, DEAD_SLOT, field_from_u64(1))],
            vec![],
        )
        .map_err(CompanionError::Refused)
    }

    /// **Attempt to resurrect a companion** — a real `resurrect` turn writing `dead = 0`. On a
    /// dead companion the global `WriteOnce(dead)` bars the `1 -> 0` change and the executor
    /// REFUSES it: hardcore death is FINAL.
    pub fn attempt_resurrect(&mut self, comp: &Companion) -> Result<TurnReceipt, CompanionError> {
        issue(
            &self.exec,
            &self.cclerk,
            comp.cell,
            HARDCORE_RESURRECT_METHOD,
            vec![set_field(comp.cell, DEAD_SLOT, field_from_u64(0))],
            vec![],
        )
        .map_err(CompanionError::Refused)
    }

    // ── The cross-cell buff (the fusion payoff) ─────────────────────────────────────

    /// **Arm a run buff** requiring the companion at `required_level` — deploys a real
    /// cross-cell gate cell into the run executor. Its [`StateConstraint::ObservedFieldEquals`]
    /// names the companion's `level` slot at the finalized level-`required_level` checkpoint
    /// ([`checkpoint_root`]). Below that level the companion's live commitment is NOT the
    /// checkpoint ⇒ the buff fails closed; at that level it commits.
    pub fn arm_buff(&mut self, comp: &Companion, required_level: u64) -> BuffGate {
        let checkpoint = checkpoint_root(comp.seed, required_level);
        let seed = self.take_seed();
        let buff_program = CellProgram::Predicate(vec![StateConstraint::ObservedFieldEquals {
            local_field: BUFF_SLOT,
            source_cell: *comp.cell.as_bytes(),
            source_field: LEVEL_SLOT,
            at_root: checkpoint,
            proof_witness_index: 0,
        }]);
        let buff_cell = install(&self.exec, self.driver, run_cell(seed, buff_program));
        BuffGate {
            buff_cell,
            required_level,
            checkpoint,
            asset_id: comp.asset_id,
            companion_cell: comp.cell,
        }
    }

    /// **Attempt to activate a buff** — the cross-cell aid. `player` must OWN the companion
    /// asset (the asset-layer ownership gate; a non-owner is [`CompanionError::NotOwner`]).
    /// Then a real turn writes the required level into the buff cell (carrying the Merkle-open
    /// witness iff `with_witness`); the executor's `ObservedFieldEquals` admits it IFF the
    /// companion is AT the checkpoint (its live commitment == the pinned root) AND the written
    /// value == the companion's `level` there AND the witness is present. Below level, or with
    /// a stripped witness, it is a real refusal.
    pub fn attempt_buff(
        &mut self,
        gate: &BuffGate,
        player: &str,
        with_witness: bool,
    ) -> Result<TurnReceipt, CompanionError> {
        let pk = self.assets.pubkey_of(player);
        if self.assets.current_owner(gate.asset_id) != Some(pk) {
            return Err(CompanionError::NotOwner);
        }
        let blobs = if with_witness {
            vec![WitnessBlob::new(
                WitnessKind::MerklePath,
                gate.checkpoint.to_vec(),
            )]
        } else {
            vec![]
        };
        issue(
            &self.exec,
            &self.cclerk,
            gate.buff_cell,
            "companion/buff",
            vec![set_field(
                gate.buff_cell,
                BUFF_SLOT,
                field_from_u64(gate.required_level),
            )],
            blobs,
        )
        .map_err(CompanionError::Refused)
    }

    /// The committed value written into a buff cell (`0` until the buff commits, then the
    /// required level).
    pub fn buff_value(&self, gate: &BuffGate) -> u64 {
        read_u64(&self.exec, gate.buff_cell, BUFF_SLOT)
    }

    // ── The owned identity (trade, double-spend refusal, provenance) ────────────────

    /// **Trade a companion** from `from` to `to` — the asset layer's owner-gated transfer. A
    /// non-owner `from` is a real cryptographic refusal; an owner's transfer spends the
    /// current version and mints a successor owned by `to`. The companion's recorded owner is
    /// updated on commit.
    pub fn trade(
        &mut self,
        asset_id: AssetId,
        from: &str,
        to: &str,
    ) -> Result<TransferReceipt, CompanionError> {
        let receipt = self
            .assets
            .transfer(asset_id, from, to)
            .map_err(CompanionError::Asset)?;
        if let Some(comp) = self.companions.get_mut(&asset_id.bytes()) {
            comp.owner = receipt.new_owner;
        }
        Ok(receipt)
    }

    /// **Attempt to double-spend a companion version** (an adversarial dupe probe) — the
    /// version's holder re-signs a spend on it. An already-spent version (e.g. an origin that
    /// was traded away) is REFUSED by the asset layer's `StrictMonotonic(spent)` tooth: a
    /// companion cannot be duped. `version_index` is the lineage position (0 = the origin).
    pub fn attempt_dupe(
        &self,
        asset_id: AssetId,
        version_index: usize,
    ) -> Result<TurnReceipt, CompanionError> {
        self.assets
            .attempt_respend(asset_id, version_index)
            .map_err(CompanionError::Asset)
    }

    /// The current owner's pubkey of a companion (from the asset layer).
    pub fn owner_of(&self, asset_id: AssetId) -> Option<[u8; 32]> {
        self.assets.current_owner(asset_id)
    }
    /// The rarity of a companion (from its recorded hatch).
    pub fn rarity_of(&self, asset_id: AssetId) -> Option<Rarity> {
        self.hatches.get(&asset_id.bytes()).map(|d| d.rarity)
    }
    /// The hatch a companion was hatched from (its fair-draw provenance).
    pub fn hatch_of(&self, asset_id: AssetId) -> Option<&HatchDraw> {
        self.hatches.get(&asset_id.bytes())
    }
    /// The asset layer's provenance report for a companion (its owned-identity lineage
    /// re-verifies + on-chain spent re-reads) — the same executor-refereed check
    /// [`dreggnet_asset`] exposes.
    pub fn verify_identity(&self, asset_id: AssetId) -> ProvenanceReport {
        self.assets.verify_provenance(asset_id)
    }
    /// How many companions this roost has hatched (the anti-ghost witness: a refused forged
    /// hatch mints NOTHING, so it does not move this count).
    pub fn companion_count(&self) -> usize {
        self.companions.len()
    }
}

#[cfg(test)]
mod tests {
    //! COMPANIONS, DRIVEN on the real layers: a companion HATCHES from a fair draw (owned,
    //! content-addressed, rarity re-derivable; a forged hatch mints nothing); it LEVELS via
    //! XP-gated turns (a level-up without the XP refused — can't be faked-leveled); its buff
    //! APPLIES cross-cell only at the required level (below-level refused, at-level commits —
    //! the `ObservedFieldEquals` bites); it can't be DUPED (a double-spend refused); hardcore
    //! permadeath is `WriteOnce`-final; and the level/bond persists as a receipt chain.
    use super::*;

    /// A committed beacon standing in for a Descent day (the verified drand day-seed).
    fn beacon(byte: u8) -> CommittedSeed {
        CommittedSeed::from_bytes([byte; 32])
    }

    /// Search for a beacon whose named-species hatch draws the target rarity (the draw is a
    /// pure function of the context, so this scans the deterministic distribution).
    fn find_beacon_for(species: &str, want: Rarity) -> CommittedSeed {
        for b in 0u16..=255 {
            let s = beacon(b as u8);
            if roll_hatch(&s, species, 0).rarity == want {
                return s;
            }
        }
        panic!("no beacon in 0..256 hatches {want:?} from `{species}`");
    }

    /// A fair hatch MINTS a real owned, content-addressed companion whose provenance binds
    /// the beacon it hatched from — and its owned-identity lineage re-verifies.
    #[test]
    fn a_fair_hatch_mints_a_real_owned_companion() {
        let mut roost = CompanionRoost::new();
        let alice_pk = roost.pubkey_of("alice");
        let draw = roll_hatch(&beacon(7), "companion:frostwyrm", 0);
        let comp = roost.hatch("alice", &draw).expect("a real hatch mints");

        assert_eq!(comp.owner, alice_pk, "the companion is owned by the player");
        assert_eq!(
            roost.owner_of(comp.asset_id),
            Some(alice_pk),
            "the asset layer agrees the player owns it"
        );
        let h = roost.hatch_of(comp.asset_id).expect("hatch recorded");
        assert_eq!(h.beacon, beacon(7), "provenance binds the hatch beacon");
        assert_eq!(h.roll, draw.roll, "provenance binds the fair draw");
        let prov = roost.verify_identity(comp.asset_id);
        assert!(
            prov.verified,
            "the identity lineage re-verifies: {:?}",
            prov.reasons
        );
        assert_eq!(prov.length, 1, "a fresh hatch is a length-1 lineage");
        // A fresh companion begins at level 0 / xp 0, alive.
        assert_eq!(roost.level_of(&comp), 0);
        assert_eq!(roost.xp_of(&comp), 0);
        assert!(!roost.is_dead(&comp));
    }

    /// A LEGENDARY vs a COMMON companion is decided by the FAIR DRAW — the rarity is the
    /// draw's distribution, re-derivable by anyone, not a claim.
    #[test]
    fn a_legendary_vs_a_common_hatch_is_the_fair_draw() {
        let species = "companion:drake";
        let leg = roll_hatch(&find_beacon_for(species, Rarity::Legendary), species, 0);
        let com = roll_hatch(&find_beacon_for(species, Rarity::Common), species, 0);
        assert_eq!(leg.rarity, Rarity::Legendary);
        assert_eq!(com.rarity, Rarity::Common);
        reverify_hatch(&leg).expect("the legendary is a real fair draw");
        reverify_hatch(&com).expect("the common is a real fair draw");
        assert!(
            leg.roll >= 97 && com.roll < 60,
            "the tiers reflect the draw faces"
        );

        let mut roost = CompanionRoost::new();
        let l = roost.hatch("hero", &leg).expect("the legendary hatches");
        let c = roost.hatch("hero", &com).expect("the common hatches");
        assert_eq!(roost.rarity_of(l.asset_id), Some(Rarity::Legendary));
        assert_eq!(roost.rarity_of(c.asset_id), Some(Rarity::Common));
        assert_ne!(
            l.asset_id.bytes(),
            c.asset_id.bytes(),
            "different hatches are different companions"
        );
    }

    /// A FORGED hatch — a companion claimed with a rewritten roll (a fabricated legendary the
    /// seed never produced) — is REFUSED with no mint. Non-vacuous: the honest hatch mints.
    #[test]
    fn a_forged_hatch_mints_nothing() {
        let mut roost = CompanionRoost::new();
        let honest = roll_hatch(&beacon(3), "companion:egg", 0);

        let forged_roll = if honest.roll == 99 { 98 } else { 99 };
        let mut forged = honest.clone();
        forged.roll = forged_roll;
        forged.rarity = Rarity::Legendary;

        let out = roost.hatch("cheater", &forged);
        assert!(
            matches!(out, Err(CompanionError::Forged(_))),
            "a fabricated legendary hatch is refused, got {out:?}"
        );
        assert_eq!(
            roost.companion_count(),
            0,
            "no companion minted for the forged hatch"
        );

        let comp = roost
            .hatch("cheater", &honest)
            .expect("the honest hatch mints");
        assert_eq!(roost.rarity_of(comp.asset_id), Some(honest.rarity));
        assert_eq!(
            roost.companion_count(),
            1,
            "exactly the honest hatch is a companion"
        );
    }

    /// THE LEVEL GATE (non-vacuous): a companion with too little XP is REFUSED by the
    /// executor's `FieldGte` gate — a real refusal that commits nothing (still its old
    /// level). The SAME move commits once the XP is earned. A companion cannot be faked-leveled.
    #[test]
    fn a_companion_cannot_be_faked_leveled() {
        let mut roost = CompanionRoost::new();
        let draw = roll_hatch(&beacon(11), "companion:pup", 0);
        let comp = roost.hatch("owner", &draw).expect("hatch");

        roost
            .try_level_up(&comp)
            .expect("reaching level 1 needs no XP");
        assert_eq!(roost.level_of(&comp), 1);

        // Earn SOME XP, but not enough for level 2 (needs 100).
        roost.train(&comp, 50).expect("earning 50 XP commits");

        // PREMATURE: leveling to 2 needs xp >= 100; with 50 it is a REAL refusal.
        let refused = roost.try_level_up(&comp);
        assert!(
            matches!(refused, Err(CompanionError::Refused(_))),
            "a level-up without the earned XP is refused, got {refused:?}"
        );
        assert_eq!(roost.level_of(&comp), 1, "anti-ghost: still level 1");
        assert_eq!(roost.xp_of(&comp), 50, "XP untouched by the refused turn");

        // Now EARN the rest and drive the SAME move — it commits.
        roost.train(&comp, 60).expect("earning 60 more XP commits");
        let r = roost
            .try_level_up(&comp)
            .expect("with 110 XP >= 100, the level-up commits");
        assert_eq!(roost.level_of(&comp), 2, "leveled up to 2");
        assert_ne!(r.turn_hash, [0u8; 32], "a genuine committed turn");
    }

    /// THE CROSS-CELL BUFF (non-vacuous, both legs): a run buff requires the companion at
    /// level 3. Armed while the companion is at level 2, the buff is REFUSED (the companion's
    /// commitment is not the checkpoint root — the `ObservedFieldEquals` fails closed). Raise
    /// the SAME companion to level 3 and the SAME buff turn COMMITS — its admission read the
    /// companion cell's level. The buff applies BECAUSE the companion is at the required level.
    #[test]
    fn the_buff_applies_cross_cell_only_at_the_required_level() {
        let mut roost = CompanionRoost::new();
        let draw = roll_hatch(&beacon(13), "companion:wisp", 0);
        let comp = roost.hatch("alice", &draw).expect("hatch");

        // Raise to level 2 — BELOW the buff's required level 3.
        roost.raise_to(&comp, 2).expect("raise to level 2");
        assert_eq!(roost.level_of(&comp), 2);

        // Arm the buff (requires level 3). Its gate pins the companion's level-3 checkpoint.
        let gate = roost.arm_buff(&comp, 3);

        // BELOW LEVEL: the buff is refused (fail-closed — companion not at the checkpoint).
        let refused = roost.attempt_buff(&gate, "alice", true);
        assert!(
            refused.is_err(),
            "the buff must refuse below the required level, got {refused:?}"
        );
        assert_eq!(
            roost.buff_value(&gate),
            0,
            "anti-ghost: the buff did not apply"
        );

        // Raise the SAME companion to level 3 — now AT the checkpoint.
        roost.raise_to(&comp, 3).expect("raise to level 3");
        assert_eq!(roost.level_of(&comp), 3);

        // AT LEVEL: the same buff turn commits — the cross-cell gate bit.
        let ok = roost
            .attempt_buff(&gate, "alice", true)
            .expect("at level 3, the buff applies");
        assert_ne!(ok.turn_hash, [0u8; 32]);
        assert_eq!(
            roost.buff_value(&gate),
            3,
            "the buff applied to the companion's level value"
        );
    }

    /// The buff gate is fail-closed to forgery and ownership: at the required level, a
    /// STRIPPED witness is refused, and a NON-OWNER cannot activate the buff even at level.
    #[test]
    fn the_buff_is_fail_closed_to_forgery_and_ownership() {
        let mut roost = CompanionRoost::new();
        let draw = roll_hatch(&beacon(17), "companion:owl", 0);
        let comp = roost.hatch("alice", &draw).expect("hatch");
        roost.raise_to(&comp, 3).expect("raise to level 3");
        let gate = roost.arm_buff(&comp, 3);

        // A stripped witness fails closed even at the right level.
        let no_witness = roost.attempt_buff(&gate, "alice", false);
        assert!(
            no_witness.is_err(),
            "a stripped-witness buff fails closed, got {no_witness:?}"
        );
        assert_eq!(roost.buff_value(&gate), 0, "the buff did not apply");

        // A non-owner cannot activate the buff (the asset-layer ownership gate).
        let not_owner = roost.attempt_buff(&gate, "mallory", true);
        assert!(
            matches!(not_owner, Err(CompanionError::NotOwner)),
            "a non-owner buff is refused, got {not_owner:?}"
        );
        assert_eq!(roost.buff_value(&gate), 0);

        // The owner with the witness, at level, commits.
        roost
            .attempt_buff(&gate, "alice", true)
            .expect("owner at level applies the buff");
        assert_eq!(roost.buff_value(&gate), 3);
    }

    /// A companion CANNOT be DUPED: after a trade the origin version is spent, and a
    /// double-spend of it is refused by the asset layer's `StrictMonotonic(spent)` tooth. The
    /// identity lineage still re-verifies (mint + one transfer = two versions, no dupe).
    #[test]
    fn a_companion_cannot_be_duped() {
        let mut roost = CompanionRoost::new();
        let alice_pk = roost.pubkey_of("alice");
        let bob_pk = roost.pubkey_of("bob");
        let draw = roll_hatch(&beacon(19), "companion:fox", 0);
        let comp = roost.hatch("alice", &draw).expect("hatch");
        assert_eq!(roost.owner_of(comp.asset_id), Some(alice_pk));

        // Trade alice -> bob (spends the origin, mints a successor owned by bob).
        roost
            .trade(comp.asset_id, "alice", "bob")
            .expect("the owner's trade commits");
        assert_eq!(
            roost.owner_of(comp.asset_id),
            Some(bob_pk),
            "the companion is now bob's"
        );

        // DUPE PROBE: re-spend the origin (version 0, already spent) — refused.
        let dupe = roost.attempt_dupe(comp.asset_id, 0);
        assert!(
            matches!(dupe, Err(CompanionError::Asset(AssetError::Refused(_)))),
            "a double-spend of the companion origin is refused, got {dupe:?}"
        );
        // A non-owner trade is also refused (the owner-gate) — mallory cannot move bob's.
        let forged = roost.trade(comp.asset_id, "mallory", "eve");
        assert!(
            matches!(forged, Err(CompanionError::Asset(AssetError::Refused(_)))),
            "a non-owner trade is refused, got {forged:?}"
        );
        // The lineage still re-verifies: exactly the one real transfer, no dupe.
        let prov = roost.verify_identity(comp.asset_id);
        assert!(
            prov.verified,
            "post-trade lineage verifies: {:?}",
            prov.reasons
        );
        assert_eq!(prov.length, 2, "mint + one transfer = two versions");
    }

    /// HARDCORE permadeath is `WriteOnce`-FINAL (non-vacuous). A companion earns and levels;
    /// a real `perish` sets `dead = 1`; then a resurrection is a REAL refusal (`WriteOnce`
    /// bars `1 -> 0`) AND a dead companion earns nothing. The bond has real stakes.
    #[test]
    fn hardcore_permadeath_is_writeonce_final() {
        let mut roost = CompanionRoost::new();
        let draw = roll_hatch(&beacon(23), "companion:moth", 0);
        let comp = roost.hatch("owner", &draw).expect("hatch");
        roost.raise_to(&comp, 2).expect("raise to level 2");
        assert!(!roost.is_dead(&comp));

        let d = roost.perish(&comp).expect("the death turn commits");
        assert_ne!(d.turn_hash, [0u8; 32]);
        assert!(roost.is_dead(&comp), "the companion is dead");

        let res = roost.attempt_resurrect(&comp);
        assert!(
            matches!(res, Err(CompanionError::Refused(_))),
            "resurrecting a dead companion is refused, got {res:?}"
        );
        assert!(roost.is_dead(&comp), "anti-ghost: still dead");

        let earn = roost.train(&comp, 100);
        assert!(
            matches!(earn, Err(CompanionError::Refused(_))),
            "a dead companion cannot earn XP, got {earn:?}"
        );
    }

    /// THE BOND is a provable receipt chain: raising a companion across a run is a chain of
    /// committed leveling turns (`pre == prev.post`), and after it all the owned-identity
    /// lineage still re-verifies — the level you genuinely raised persists.
    #[test]
    fn the_bond_is_a_receipt_chain_that_persists() {
        let mut roost = CompanionRoost::new();
        let draw = roll_hatch(&beacon(29), "companion:hound", 0);
        let comp = roost.hatch("owner", &draw).expect("hatch");

        // Drive the raise as an explicit arc, collecting EVERY committed turn (each earn and
        // each level-up) in order — the whole run is one receipt chain.
        let mut chain = Vec::new();
        chain.push(roost.try_level_up(&comp).expect("reach level 1")); // free (threshold 1 == 0)
        chain.push(
            roost
                .train(&comp, xp_threshold(2))
                .expect("earn to the level-2 floor"),
        );
        chain.push(roost.try_level_up(&comp).expect("level 2"));
        chain.push(
            roost
                .train(&comp, xp_threshold(3) - xp_threshold(2))
                .expect("earn to the level-3 floor"),
        );
        chain.push(roost.try_level_up(&comp).expect("level 3"));

        assert!(chain.len() >= 4, "the run is several real committed turns");
        for w in chain.windows(2) {
            assert_eq!(
                w[1].pre_state_hash, w[0].post_state_hash,
                "the run receipts chain: pre == prev.post"
            );
        }
        assert_eq!(
            roost.level_of(&comp),
            3,
            "the raised level persists on the ledger"
        );
        assert!(
            roost.xp_of(&comp) >= xp_threshold(3),
            "the earned XP persists"
        );

        // The owned identity still re-verifies — the bond is intact.
        let prov = roost.verify_identity(comp.asset_id);
        assert!(
            prov.verified,
            "the identity lineage re-verifies: {:?}",
            prov.reasons
        );

        // The checkpoint is stable: re-deriving the level-3 root matches the live companion —
        // the raise is reproducible (the bond persists as a re-derivable fact across runs).
        assert_eq!(
            checkpoint_root(comp.seed, 3),
            commitment_of(&roost.exec, comp.cell),
            "the level-3 checkpoint re-derives"
        );
    }
}
