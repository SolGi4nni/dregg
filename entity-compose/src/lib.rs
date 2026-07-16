//! # entity-compose — the HOARDLIGHT substrate, wired end to end, game-free
//!
//! This crate stands up a real **ENTITY** and lands a real **composition turn**, composing
//! four already-built, already-committed pieces that had never been wired together before:
//!
//! 1. **A param-carrying entity** — a [`dregg_cell::Cell`] whose *wide extended plane*
//!    (`set_field_ext` at key `>= 16` → the committed `fields_map`) carries a bounded typed
//!    param vector. The params are genuinely IN the cell's state: they move its v9 chip
//!    commitment (the value the Door welds).
//! 2. **`dregg-param-compose`** — the GENERAL Custom-VK AIR proving
//!    `outcome = Σ_linear coeff·P[role].params[i] + Σ_knots coeff·P[a].params[i]·P[b].params[j]`
//!    over N typed subjects composed by a versioned, publicly-committed ruleset.
//! 3. **The Door** (`dregg_turn::action::Effect::Custom`) — a custom proof reaches
//!    `TurnExecutor::execute`, which verifies the VK, the registry dispatch, and the STATE
//!    WELD (`pis[0..8] == the cell's stored commitment`, `pis[8..16] == the claimed new`).
//! 4. **The cell** — the outcome is committed to the entity's cell, welded to its real
//!    pre/post state.
//!
//! ## The generic vocabulary is the point
//!
//! Everything here speaks in `subjects`, `params`, `roles`, `knots`, `ruleset`, `outcome` —
//! never a creature, a stat, or a rule. HOARDLIGHT's living world is ONE ruleset root + its
//! content (params) over this substrate, exactly as a new `dregg-param-compose` game is a new
//! ruleset root and not an AIR edit. Nothing in this crate is dragon-specific.
//!
//! ## What composes end to end vs. the named residual (HONEST SCOPE)
//!
//! **What composes, driven through the real executor** (`tests/end_to_end.rs`):
//! a real entity's params determine its v9 commitment; a composition READ from those params
//! proves under the ruleset; the turn carrying it passes the Door and the state weld against
//! the entity's REAL commitment; a proof about a DIFFERENT entity (different params → different
//! commitment) is refused by the weld; a composition the ruleset does not license has no
//! satisfying witness. The realistic composition rides `dregg-param-compose`'s 803-column leaf
//! (`tests/budget.rs`), and the composition leaf really proves + binds its commitment
//! (`tests/leaf_prove.rs`, `#[ignore]`, minutes).
//!
//! **The named residual — the outcome→cell-field weld.** The substrate binds the *whole cell*
//! transition (`old8`/`new8`), and this crate writes the composition's `outcome_commitment`
//! into the POST cell's wide plane so that `new8` genuinely reflects a state that carries the
//! outcome ([`LandedComposition::post_state_carries_outcome`]). But **nothing in-circuit or
//! in-executor yet FORCES** the post cell's wide field to equal the sub-proof's published
//! `outcome_commitment` public input — the host wrote both. The state weld checks only the
//! `[old8 ‖ new8]` prefix, not the app PIs, so a host could write outcome `X` into the cell
//! while the sub-proof commits outcome `Y`, and the Door would not notice.
//! [`LandedComposition::harness_verify_outcome_welded`] performs exactly the comparison the
//! kernel is missing — off to the side, as a harness check. Closing it *for real* is a single
//! **executor atom**: "the new state's wide field `[OUTCOME_WIDE_BASE .. +8]` equals the
//! sub-proof's `outcome_commitment` PI". That atom is cell-state-layout-aware (it names a wide
//! key), which is why it lives at the app/executor layer and not inside the game-free AIR. It
//! is the precise, single missing gate — named, with its shape demonstrated here.

use dregg_cell::commitment::{
    self, V9RotationContext, bytes32_to_felt8, compute_canonical_state_commitment_v9_8,
};
use dregg_cell::{Cell, CellId, CellMode, Ledger};
use dregg_circuit::field::BabyBear;
use dregg_param_compose::air::{ComposeAir, build};
use dregg_param_compose::model::{ComposeError, Composition, Ruleset, Subject};
use dregg_param_compose::pi;
use dregg_param_compose::shape::ComposeShape;

pub use dregg_param_compose::model::{Knot, LinearTerm};
pub use dregg_param_compose::{ComposeShape as Shape, Composition as Comp};

/// Wide-plane base key for an entity's projection (`identity` at `base`, `role` at `base+1`,
/// `params[i]` at `base+2+i`). Keys `>= 16` land in the committed `fields_map`, so the
/// projection is part of the cell's state commitment. Chosen at 16, the first wide key.
pub const PROJECTION_WIDE_BASE: u64 = 16;

/// Wide-plane base key for the published `outcome_commitment` (8 felts, one per wide slot).
/// Deliberately far above the projection so a small param vector never collides with it.
pub const OUTCOME_WIDE_BASE: u64 = 64;

/// Encode a single BabyBear as a 32-byte `FieldElement` (the low 4 bytes carry the felt; the
/// rest are zero) — used for the published `outcome_commitment` felts.
pub fn felt_to_fe(f: BabyBear) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[..4].copy_from_slice(&f.0.to_le_bytes());
    out
}

/// Encode an unsigned scalar (identity / role) as a wide-plane `FieldElement` (LE, round-trips).
pub fn u64_to_fe(v: u64) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[..8].copy_from_slice(&v.to_le_bytes());
    out
}

/// Encode a signed param value as a wide-plane `FieldElement` (two's-complement LE, round-trips
/// EXACTLY). What matters for the substrate: a DIFFERENT value yields a different `fields_root`,
/// hence a different commitment — and it reads back bit-for-bit.
pub fn param_to_fe(v: i64) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[..8].copy_from_slice(&v.to_le_bytes());
    out
}

fn read_u64_fe(cell: &Cell, key: u64) -> u64 {
    let fe = cell.state.fields_root_membership(key).unwrap_or([0u8; 32]);
    let mut b = [0u8; 8];
    b.copy_from_slice(&fe[..8]);
    u64::from_le_bytes(b)
}

fn read_i64_fe(cell: &Cell, key: u64) -> i64 {
    read_u64_fe(cell, key) as i64
}

/// Write an entity's projection (identity, role, params) into a cell's wide plane at `base`.
/// After this the cell's state commitment is a function of the projection.
pub fn install_projection(cell: &mut Cell, base: u64, s: &Subject) {
    cell.state.set_field_ext(base, u64_to_fe(s.identity));
    cell.state.set_field_ext(base + 1, u64_to_fe(s.role));
    for (i, &p) in s.params.iter().enumerate() {
        cell.state
            .set_field_ext(base + 2 + i as u64, param_to_fe(p));
    }
}

/// Read an entity's projection back OUT of the committed wide plane (via `fields_root_membership`,
/// so a read only succeeds when the recomputed `fields_root` matches the stored one) — the
/// round-trip that makes "the params ARE the subjects" real rather than carried alongside.
pub fn read_projection(cell: &Cell, base: u64, param_count: usize) -> Subject {
    Subject {
        identity: read_u64_fe(cell, base),
        role: read_u64_fe(cell, base + 1),
        params: (0..param_count as u64)
            .map(|i| read_i64_fe(cell, base + 2 + i))
            .collect(),
    }
}

/// Compute a cell's canonical **v9 chip commitment** — the 32-byte value the Custom-VK Door
/// welds (`old8`/`new8` = `bytes32_to_felt8` of this). The wide `fields_map` is folded in, so
/// this moves when the entity's params move.
pub fn v9_commitment(cell: &Cell) -> ([u8; 32], V9RotationContext) {
    let mut ctx_ledger = Ledger::new();
    let _ = ctx_ledger.insert_cell(cell.clone());
    let ctx = V9RotationContext {
        cells_root: dregg_turn::rotation_witness::cells_root(&ctx_ledger),
        nullifier_root: dregg_circuit::heap_root::empty_heap_root_8(),
        commitments_root: dregg_circuit::heap_root::empty_heap_root_8(),
        revoked_root: dregg_turn::rotation_witness::empty_revoked_root_8(),
        iroot: dregg_turn::rotation_witness::iroot(&[]),
        material: Default::default(),
    };
    let commitment = compute_canonical_state_commitment_v9_8(cell, &ctx);
    (commitment, ctx)
}

fn open_permissions() -> dregg_cell::Permissions {
    use dregg_cell::AuthRequired;
    dregg_cell::Permissions {
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

/// A deployed sovereign entity: a cell whose wide plane carries its projection, its v9
/// commitment (the Door's `old8` source), and the projection itself (the composition subject).
#[derive(Clone)]
pub struct DeployedEntity {
    pub cell: Cell,
    pub subject: Subject,
    pub ctx: V9RotationContext,
    pub commitment: [u8; 32],
}

impl DeployedEntity {
    pub fn cell_id(&self) -> CellId {
        self.cell.id()
    }
    /// The Door's `old8` — the pre-state root the state weld compares against the cell's
    /// registered sovereign commitment.
    pub fn old8(&self) -> [BabyBear; 8] {
        bytes32_to_felt8(&self.commitment)
    }
    /// Register this entity as a sovereign cell at its real commitment (the pre-state the
    /// executor reads as `old_commit8`) and return a ledger carrying it.
    pub fn into_registered_ledger(self) -> (CellId, Ledger, Self) {
        let cell_id = self.cell.id();
        let mut ledger = Ledger::new();
        ledger
            .register_sovereign_cell(cell_id, self.commitment)
            .expect("sovereign registration");
        let _ = ledger.insert_cell(self.cell.clone());
        (cell_id, ledger, self)
    }
}

/// Deploy a primary entity: a sovereign cell whose wide plane carries `subject`'s projection.
pub fn deploy_entity(seed: u8, balance: i64, subject: Subject) -> DeployedEntity {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell.mode = CellMode::Sovereign;
    install_projection(&mut cell, PROJECTION_WIDE_BASE, &subject);
    let (commitment, ctx) = v9_commitment(&cell);
    DeployedEntity {
        cell,
        subject,
        ctx,
        commitment,
    }
}

/// The result of composing a primary entity's params (+ partners) into a committed outcome and
/// packaging it as a state-welded custom sub-proof ready to land through the Door.
pub struct LandedComposition {
    /// The primary entity whose cell the turn lands on.
    pub cell_id: CellId,
    /// The composition (subjects read from the entity + partners, the ruleset).
    pub composition: Composition,
    pub shape: ComposeShape,
    /// The exact composed outcome (`i128`, the AIR's field twin is `fb(outcome)`).
    pub outcome: i128,
    /// The 8-felt `outcome_commitment` (both the sub-proof's PI and what the post cell carries).
    pub outcome_commitment: Vec<BabyBear>,
    /// The Door's `old8` (the entity's real pre-state commitment).
    pub old_commitment: [u8; 32],
    /// The Door's claimed `new8` — the commitment of a POST cell carrying the outcome.
    pub new_commitment: [u8; 32],
    /// The post cell (a clone of the entity's cell with `outcome_commitment` in its wide plane).
    pub post_cell: Cell,
    /// The composition sub-proof's public inputs `[old8 ‖ new8 ‖ ..app]`.
    pub pis: Vec<BabyBear>,
}

impl LandedComposition {
    /// The sub-proof PIs as `u32` (the wire form `CustomProgramProof::public_inputs` carries).
    pub fn pis_u32(&self) -> Vec<u32> {
        self.pis.iter().map(|f| f.0).collect()
    }

    /// **The outcome→cell-field weld, at current resolution.** Returns true iff the POST cell's
    /// wide plane at `OUTCOME_WIDE_BASE` carries EXACTLY the sub-proof's published
    /// `outcome_commitment` — the property the missing executor atom would ENFORCE. Here the
    /// host arranged it (and this reads it back through the committed `fields_root`), so a
    /// `true` says "the shape is closeable and the post state does carry the outcome"; it does
    /// NOT say the kernel forces it. See the crate doc's honest-scope section.
    pub fn harness_verify_outcome_welded(&self) -> bool {
        let base = pi::outcome_commitment_base();
        for (j, expect) in self.outcome_commitment.iter().enumerate() {
            let Some(fe) = self
                .post_cell
                .state
                .get_field_ext(OUTCOME_WIDE_BASE + j as u64)
            else {
                return false;
            };
            if fe != felt_to_fe(*expect) {
                return false;
            }
            // ...and it is the same value the sub-proof published as its outcome PI.
            if self.pis[base + j] != *expect {
                return false;
            }
        }
        true
    }

    /// Whether the honest composition self-accepts (the fast `air_accepts` shadow of "the leaf
    /// proves"). A composition the ruleset does not license returns false — no turn to carry.
    pub fn air_accepts(&self) -> bool {
        // Rebuild the AIR to evaluate the emitted constraints over the emitted witness row.
        let old8 = bytes32_to_felt8(&self.old_commitment);
        let new8 = bytes32_to_felt8(&self.new_commitment);
        build(&self.shape, &self.composition, &old8, &new8)
            .map(|a| a.builder.air_accepts())
            .unwrap_or(false)
    }
}

/// Compose a primary entity's params (read from its wide plane) with zero or more `partners`
/// under `ruleset` at `shape`, and package the result as a state-welded custom sub-proof
/// bound to the entity's REAL pre/post commitments.
///
/// The POST cell is the entity's cell with the composition's `outcome_commitment` written into
/// its wide plane at [`OUTCOME_WIDE_BASE`], so `new8` genuinely reflects a state carrying the
/// outcome (the shape of the outcome→cell-field weld; see the crate doc).
pub fn compose_onto(
    entity: &DeployedEntity,
    partners: &[Subject],
    ruleset: Ruleset,
    shape: ComposeShape,
    param_count: usize,
) -> Result<LandedComposition, ComposeError> {
    // THE READ: the primary subject is READ from the entity cell's committed wide plane, not
    // carried alongside — the params genuinely ARE the composition's subject.
    let primary = read_projection(
        &entity.cell,
        PROJECTION_WIDE_BASE,
        entity.subject.params.len(),
    );
    debug_assert_eq!(
        primary, entity.subject,
        "the wide-plane projection must round-trip to the deployed subject"
    );
    let mut subjects = vec![primary];
    subjects.extend_from_slice(partners);
    let composition = Composition {
        subjects,
        ruleset,
        param_count,
    };

    let composed = composition.compose()?;
    let outcome_commitment = composition.outcome_commitment(&shape)?;

    let old_commitment = entity.commitment;
    let old8 = bytes32_to_felt8(&old_commitment);

    // The POST cell carries the outcome in its wide plane -> its commitment is `new8`.
    let mut post_cell = entity.cell.clone();
    for (j, f) in outcome_commitment.iter().enumerate() {
        post_cell
            .state
            .set_field_ext(OUTCOME_WIDE_BASE + j as u64, felt_to_fe(*f));
    }
    let (new_commitment, _post_ctx) = v9_commitment(&post_cell);
    let new8 = bytes32_to_felt8(&new_commitment);

    // Build the AIR bound to the entity's REAL (old8, new8) and package its genuine PIs.
    let air: ComposeAir = build(&shape, &composition, &old8, &new8)?;
    debug_assert!(
        air.builder.air_accepts(),
        "a well-formed composition must self-accept"
    );
    let pis = air.builder.pis.clone();

    Ok(LandedComposition {
        cell_id: entity.cell_id(),
        composition,
        shape,
        outcome: composed.outcome,
        outcome_commitment,
        old_commitment,
        new_commitment,
        post_cell,
        pis,
    })
}

/// Sanity re-exports so a downstream (a HOARDLIGHT ruleset) builds subjects/rulesets without
/// depending on `dregg-param-compose` directly.
pub use dregg_param_compose::model::{
    ComposeError as EntityComposeError, Ruleset as EntityRuleset,
};

/// Convenience: the v9 chip commitment as the Door's 8-felt form.
pub fn commitment_felt8(commitment: &[u8; 32]) -> [BabyBear; 8] {
    bytes32_to_felt8(commitment)
}

/// The composition program's circuit descriptor (a function of the SHAPE, not the content —
/// see `dregg-param-compose`'s `two_unrelated_rulesets_share_one_vk`). Its serialization is the
/// `program_bytes` a genuine v2 `vk_hash` binds, so a turn names the composition program's own
/// verification key rather than a stand-in.
pub fn program_descriptor(
    shape: &ComposeShape,
    comp: &Composition,
) -> dregg_circuit::dsl::circuit::CircuitDescriptor {
    let air = build(shape, comp, &[BabyBear::ZERO; 8], &[BabyBear::ZERO; 8])
        .expect("the composition program descriptor builds");
    air.builder.descriptor()
}

/// Re-export the raw commitment helper for tests that want to assert the executor's comparand.
pub use commitment::bytes32_to_felt8 as door_felt8;
