//! # `trace_rotated` — THE LIVE rotated (R=24) trace generator (G1).
//!
//! `docs/ROTATION-CUTOVER.md` §5 deferred the rotated trace BUILDER: the staged keystones
//! (`EffectVmEmitRotationV3.lean`) prove the rotated R=24 cohort sound and the staged probe
//! measures the SHAPE, but the LIVE machinery that turns a real turn into the 311-column
//! rotated trace existed ONLY hand-welded inside `circuit/tests/effect_vm_rotation_flip.rs`
//! (`fill_block` / `fill_caveat`). This module PROMOTES that hand-welding into a genuine
//! generator: from the v1 186-column trace (`generate_effect_vm_trace`) plus the per-turn
//! producer witness limbs, it emits the rotated 311-column trace — the two rotated blocks
//! (BEFORE / AFTER) + the widened-caveat region + every chained `wireCommitR` digest — and
//! the 38-PI vector (34 v1 + 4 appended) the staged registry descriptor
//! (`transferVmDescriptor2R24`) pins.
//!
//! ## Law #1 — the shapes come from Lean
//!
//! Every quantity this module computes matches a Lean definition (the Rust interprets, never
//! invents):
//!
//! * the 31-limb absorption ORDER is `EffectVmEmitRotationV3.preLimbsAt`
//!   (cells_root · r0..r23 · cap_root · nullifier_root · heap_root · lifecycle · epoch ·
//!   committed_height, then iroot LAST) — the caller's `RotatedBlockWitness::pre_limbs` is
//!   already in this order (it is the producer `dregg_turn::rotation_witness::produce`'s
//!   output);
//! * the welds (`r0↔balance_lo`, `r1↔nonce`, `r2↔balance_hi`, `r3..r10↔fields`,
//!   `cap_root↔cap_root`) are `EffectVmEmitRotationV3.weldsAt` — overridden here per-row from
//!   THAT row's own v1 state block so the weld gates `colEq` hold on EVERY row;
//! * the chained commitment is `EffectVmEmitRotationR.wireCommitR` (4-wide head, 3-wide chip
//!   groups while ≥ 3 pre-iroot limbs remain, the iroot absorbed ALONE last, arity ∈ {2,4}) —
//!   byte-identical to the staged probe builder (`descriptor_ir2::rotation_probe_trace_r`),
//!   the producer's `wire_commit`, and `effect_vm_descriptors::rotation_layout_for`;
//! * the caveat manifest + chained `caveatCommit` are
//!   `EffectVmEmitRotationCaveat.{RotCaveatManifest, caveatCommit}` (1 count + 4 × 7-felt
//!   entries `[type_tag, domain_tag, key, p0..p3]`, then a 10-site chain).
//!
//! The four appended PI carriers land on the columns the staged registry descriptor's
//! `pi_binding` constraints pin (verified against the committed TSV): PI 34 ← row-0
//! before-block `state_commit` (col 218), PI 35 ← last-row after-block `state_commit`
//! (col 261), PI 36 ← last-row after-block `committed_height` limb (col 259), PI 37 ←
//! last-row caveat-region `caveat_commit` (col 310).
//!
//! ## STAGED-ADDITIVE
//!
//! NOTHING on the live v1 wire path calls this generator: the live 186-column trace +
//! IR-v1 prover stay the byte-identical default. This is the rotated path BESIDE it, behind
//! the IR-v2 route in `sdk::full_turn_proof` (gated). The flag-day descriptor regen + VK
//! bump is a SEPARATE deliberate act (G2/G5).

use super::columns::rotation::caveat as cav;
use super::columns::{STATE_AFTER_BASE, STATE_BEFORE_BASE, state};
use super::{EFFECT_VM_WIDTH, generate_effect_vm_trace};
use crate::effect_vm::{CellState, Effect};
use crate::field::BabyBear;
use crate::poseidon2::hash_many;

// ============================================================================
// The rotated appendix geometry (Lean `EffectVmEmitRotationV3`, R = 24).
// ============================================================================

/// The v1 main-table width the rotated appendix extends.
pub const V1_WIDTH: usize = EFFECT_VM_WIDTH; // 186

/// The CONFIRMED rotated register count (ember 2026-06-12, `ROTATION-CUTOVER.md` §2b).
pub const NUM_REGISTERS: usize = 24;

/// The number of pre-iroot absorption limbs (cells_root · r0..r23 · cap/nullifier/heap roots
/// · lifecycle · epoch · committed_height). Lean `preLimbsAt_length = 31` at R = 24.
pub const NUM_PRE_LIMBS: usize = 1 + NUM_REGISTERS + 3 + 3; // 31

/// A rotated block: 31 limbs + iroot + state_commit + 10 chain carriers = 43 columns
/// (`rotation_layout_for(24).probe_width`).
pub const B_SPAN: usize = 43;
/// The widened-caveat region: 29 manifest + 9 chain + 1 commit = 39 columns.
pub const C_SPAN: usize = 39;
/// The appendix: two blocks + the caveat region.
pub const APPENDIX: usize = 2 * B_SPAN + C_SPAN; // 125
/// The rotated trace width.
pub const ROT_WIDTH: usize = V1_WIDTH + APPENDIX; // 311

/// In-block offset of the `cap_root` limb (the welded cap-root, limb 25).
pub const B_CAP_ROOT: usize = 25;
/// In-block offset of the `committed_height` limb (limb 30).
pub const B_COMMITTED_HEIGHT: usize = 30;
/// In-block offset of the iroot carrier (absorbed last, limb 31).
pub const B_IROOT: usize = 31;
/// In-block offset of the `state_commit` carrier (the chain's final digest).
pub const B_STATE_COMMIT: usize = 32;
/// In-block base of the chained-absorption intermediate carriers (10 sites, 33..=42).
pub const B_CHAIN_BASE: usize = 33;

/// Absolute base column of the BEFORE rotated block.
pub const BEFORE_BASE: usize = V1_WIDTH; // 186
/// Absolute base column of the AFTER rotated block.
pub const AFTER_BASE: usize = V1_WIDTH + B_SPAN; // 229
/// Absolute base column of the widened-caveat region.
pub const CAVEAT_BASE: usize = V1_WIDTH + 2 * B_SPAN; // 272

/// The number of v1 public inputs the rotated PI vector prefixes (`ACTIVE_BASE_COUNT`).
pub const V1_PI_COUNT: usize = 34;
/// The rotated public-input count (34 v1 + 4 appended).
pub const ROT_PI_COUNT: usize = 38;

// ============================================================================
// Generator inputs (producer-witness shaped, dependency-free).
// ============================================================================

/// One rotated state-block witness for a single cell's before/after `RecordKernelState`.
///
/// `pre_limbs` is the 31-limb absorption vector in the Lean-pinned order
/// (`EffectVmEmitRotationV3.preLimbsAt`); `iroot` is the receipt-index MMR root absorbed
/// LAST. This is exactly the data `dregg_turn::rotation_witness::RotationWitness` carries —
/// the producer bridge (in `turn` / `sdk` / the flip test, which depend on both crates)
/// constructs a `RotatedBlockWitness` from a `RotationWitness`'s `pre_limbs` + `iroot`. The
/// generator lives in `dregg-circuit` (which cannot depend on `dregg-turn`), so it takes the
/// limbs directly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RotatedBlockWitness {
    /// The 31 pre-iroot limbs, in absorption order.
    pub pre_limbs: Vec<BabyBear>,
    /// The receipt-index MMR root (absorbed last).
    pub iroot: BabyBear,
}

impl RotatedBlockWitness {
    /// Build from raw limbs, validating the count.
    pub fn new(pre_limbs: Vec<BabyBear>, iroot: BabyBear) -> Result<Self, String> {
        if pre_limbs.len() != NUM_PRE_LIMBS {
            return Err(format!(
                "RotatedBlockWitness: need {NUM_PRE_LIMBS} pre-iroot limbs at R={NUM_REGISTERS}, \
                 got {}",
                pre_limbs.len()
            ));
        }
        Ok(Self { pre_limbs, iroot })
    }
}

/// One widened-caveat entry: the constraint type tag, the DOMAIN tag (registers 0 · heap 1,
/// `cav::DOMAIN_REGISTERS` / `cav::DOMAIN_HEAP`), the in-domain key (a register index in the
/// registers domain, an arbitrary heap-key felt in the heap domain), and up to 4 params. The
/// Rust twin of Lean `EffectVmEmitRotationCaveat.RotCaveatEntry` (7-felt packing).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RotatedCaveatEntry {
    pub type_tag: u32,
    pub domain_tag: u32,
    pub key: BabyBear,
    pub params: [BabyBear; 4],
}

/// The fixed-size caveat manifest the rotated region carries: 1 count + 4 entries × 7 felts
/// = 29 felts. Lean `EffectVmEmitRotationCaveat.RotCaveatManifest`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RotatedCaveatManifest {
    pub entries: [RotatedCaveatEntry; cav::MAX_CAVEATS],
}

impl RotatedCaveatManifest {
    /// The count of non-empty entries (`type_tag != 0`, scanning from entry 0; the manifest
    /// keeps the live convention that active entries are a prefix).
    fn count(&self) -> u32 {
        self.entries.iter().take_while(|e| e.type_tag != 0).count() as u32
    }
}

// ============================================================================
// THE GENERATOR.
// ============================================================================

/// Generate the LIVE rotated (R = 24) trace + 38-PI vector for one transfer-shaped turn.
///
/// `initial_state` / `effects` drive the v1 trace (`generate_effect_vm_trace`); `before_w` /
/// `after_w` are the per-turn producer witnesses for the acting cell's before/after
/// `RecordKernelState` (their `pre_limbs` weld to the v1 state block by construction —
/// `r0↔balance_lo`, …, `cap_root↔cap_root`); `caveat` is the turn's widened-caveat manifest.
///
/// The rotated blocks + caveat region are filled on EVERY row (the welds + PI pins read
/// first/last; a uniform fill keeps the weld gates true on padding rows too). Every chained
/// `wireCommitR` / `caveatCommit` digest is GENUINE (computed from this row's own limbs), so
/// the four appended PI carriers are bound, not free wires.
///
/// Returns `(trace, public_inputs)` ready for `descriptor_ir2::prove_vm_descriptor2` against
/// `transferVmDescriptor2R24`.
pub fn generate_rotated_effect_vm_trace(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    if before_w.pre_limbs.len() != NUM_PRE_LIMBS || after_w.pre_limbs.len() != NUM_PRE_LIMBS {
        return Err(format!(
            "rotated generator: each block witness needs {NUM_PRE_LIMBS} pre-iroot limbs"
        ));
    }

    // The v1 reference trace + PIs — the byte-identical live machinery.
    let (mut trace, pis) = generate_effect_vm_trace(initial_state, effects);
    if trace.is_empty() {
        return Err("rotated generator: v1 trace is empty".into());
    }
    if trace[0].len() != V1_WIDTH {
        return Err(format!(
            "rotated generator: v1 trace width {} != {V1_WIDTH}",
            trace[0].len()
        ));
    }
    if pis.len() < V1_PI_COUNT {
        return Err(format!(
            "rotated generator: v1 PI vector {} shorter than {V1_PI_COUNT}",
            pis.len()
        ));
    }

    // Widen each row to the rotated width and fill the appendix.
    for row in trace.iter_mut() {
        row.resize(ROT_WIDTH, BabyBear::ZERO);
        fill_block(row, BEFORE_BASE, STATE_BEFORE_BASE, before_w);
        fill_block(row, AFTER_BASE, STATE_AFTER_BASE, after_w);
        fill_caveat(row, CAVEAT_BASE, caveat);
    }

    // The four appended PIs, read from the trace carriers the descriptor's pin constraints
    // bind. (The pins are `pi_binding` constraints, so these reads must agree with the
    // committed columns 218 / 261 / 259 / 310.)
    let r0 = &trace[0];
    let last = &trace[trace.len() - 1];
    let mut dpis: Vec<BabyBear> = pis[..V1_PI_COUNT].to_vec();
    dpis.push(r0[BEFORE_BASE + B_STATE_COMMIT]); // PI 34: rotated OLD commit (col 218)
    dpis.push(last[AFTER_BASE + B_STATE_COMMIT]); // PI 35: rotated NEW commit (col 261)
    dpis.push(last[AFTER_BASE + B_COMMITTED_HEIGHT]); // PI 36: committed height (col 259)
    dpis.push(last[CAVEAT_BASE + C_SPAN - 1]); // PI 37: caveat commit (col 310)
    debug_assert_eq!(dpis.len(), ROT_PI_COUNT);

    Ok((trace, dpis))
}

/// Fill one rotated block (BEFORE or AFTER) at `base` for ONE row. The WELDED limbs
/// (r0↔balance_lo, r1↔nonce, r2↔balance_hi, r3..r10↔fields, cap_root) are copied from THAT
/// row's own v1 state block at `state_base` (so the weld gates hold on EVERY row, including
/// the NoOp padding rows whose v1 state block differs from the active row); the WITNESS-
/// CARRIED limbs (cells_root, the map roots, lifecycle, epoch, committed_height, iroot,
/// r11..r23) come from the per-turn producer witness `w` (turn-invariant). Then the genuine
/// chained `wireCommitR` digests are computed on this row's own limbs.
///
/// The chained-absorption logic is byte-identical to `descriptor_ir2::rotation_probe_trace_r`,
/// the producer's `wire_commit`, and the Lean `wireCommitR`.
fn fill_block(row: &mut [BabyBear], base: usize, state_base: usize, w: &RotatedBlockWitness) {
    // witness-carried limbs from the producer (turn-invariant).
    for i in 0..NUM_PRE_LIMBS {
        row[base + i] = w.pre_limbs[i];
    }
    // welded limbs OVERRIDE from this row's own v1 state block (per-row truth) —
    // `EffectVmEmitRotationV3.weldsAt`.
    row[base + 1] = row[state_base + state::BALANCE_LO]; // r0
    row[base + 2] = row[state_base + state::NONCE]; // r1
    row[base + 3] = row[state_base + state::BALANCE_HI]; // r2
    for i in 0..8 {
        row[base + 4 + i] = row[state_base + state::FIELD_BASE + i]; // r3..r10
    }
    row[base + B_CAP_ROOT] = row[state_base + state::CAP_ROOT]; // cap_root
    row[base + B_IROOT] = w.iroot;

    // chained absorption: 4-wide head, 3-wide chip groups while ≥ 3 pre-iroot limbs remain,
    // the iroot on its own arity-2 final site → state_commit.
    let mut d = hash_many(&[row[base], row[base + 1], row[base + 2], row[base + 3]]);
    let mut chain = 0usize;
    row[base + B_CHAIN_BASE + chain] = d;
    chain += 1;
    let mut col = 4;
    while col < NUM_PRE_LIMBS {
        let remaining = NUM_PRE_LIMBS - col;
        if remaining >= 3 {
            d = hash_many(&[d, row[base + col], row[base + col + 1], row[base + col + 2]]);
            col += 3;
        } else {
            d = hash_many(&[d, row[base + col]]);
            col += 1;
        }
        row[base + B_CHAIN_BASE + chain] = d;
        chain += 1;
    }
    // the iroot rides its own arity-2 final site → state_commit.
    let commit = hash_many(&[d, row[base + B_IROOT]]);
    row[base + B_STATE_COMMIT] = commit;
}

/// Fill the widened-caveat region at `base` (29-felt manifest + 9 chain + commit) from the
/// turn's manifest. The chained `caveatCommit` is genuine (Lean
/// `EffectVmEmitRotationCaveat.caveatCommit`). A register (slot) operand can never alias a
/// heap operand (the `caveat_operand_no_aliasing` keystone — the domain tag separates them).
fn fill_caveat(row: &mut [BabyBear], base: usize, m: &RotatedCaveatManifest) {
    // manifest: count + 4 × 7-felt entries `[type_tag, domain_tag, key, p0..p3]`.
    row[base] = BabyBear::new(m.count());
    for (idx, e) in m.entries.iter().enumerate() {
        let eb = base + 1 + idx * cav::ENTRY_SIZE;
        row[eb] = BabyBear::new(e.type_tag);
        row[eb + 1] = BabyBear::new(e.domain_tag);
        row[eb + 2] = e.key;
        row[eb + 3] = e.params[0];
        row[eb + 4] = e.params[1];
        row[eb + 5] = e.params[2];
        row[eb + 6] = e.params[3];
    }
    // chained caveat commitment over the 29 manifest felts: 4-wide head, 3-wide body, tail.
    let manifest = cav::MANIFEST_SIZE; // 29
    let chain_base = base + manifest; // 9 carriers
    let commit_col = chain_base + cav::NUM_CHAIN; // base + 29 + 9 = base + 38
    let mut d = hash_many(&[row[base], row[base + 1], row[base + 2], row[base + 3]]);
    let mut chain = 0usize;
    row[chain_base + chain] = d;
    chain += 1;
    let mut col = 4;
    while col < manifest {
        let remaining = manifest - col;
        if remaining >= 3 {
            d = hash_many(&[d, row[base + col], row[base + col + 1], row[base + col + 2]]);
            col += 3;
        } else {
            d = hash_many(&[d, row[base + col]]);
            col += 1;
        }
        row[chain_base + chain] = d;
        chain += 1;
    }
    row[commit_col] = d;
}

/// Resolve the rotated registry descriptor NAME for one effect's v1 selector — the
/// `*VmDescriptor2R24` member of `V3_STAGED_REGISTRY_TSV` whose rotated shape proves THIS
/// effect. The cohort is the 36 graduated descriptors the Lean `EffectVmEmitRotationV3.
/// v3Registry` emits (28 base + 8 per-slot `setField`); the trace the rotated generator emits
/// is the SAME shape (311 cols + 38 PIs) for every member (the appendix is parametric, not
/// per-effect — `rotateV3`), so this resolver picks WHICH per-effect constraint family the
/// IR-v2 prover enforces on the shared trace.
///
/// `None` for a selector OUTSIDE this cohort (a non-cohort effect has no rotated descriptor —
/// the caller fails closed rather than proving the wrong shape). The `SetField` family
/// (selector 2) routes to the per-slot descriptor by the field index via
/// [`rotated_set_field_descriptor_name`].
///
/// NOTE: the rotated cohort is the v3Registry's exact membership (36 members) — the 28
/// v2-graduated descriptors (incl. the cap-crown `RevokeCapability` and `Custom`) PLUS the 8
/// LIVE-path effects the STEP 1 widening added (`GrantCapability`, `MakeSovereign`, `CreateCell`,
/// `CreateCellFromFactory`, `SpawnWithDelegation`, `ReceiptArchive`, `CellUnseal`, `EmitEvent`).
/// The HONEST RESIDUE is now EMPTY: `Custom` (8) was the last selector without a rotated
/// descriptor; it GRADUATED via the new accumulator / recursive-proof-binding constraint kind
/// (`DescriptorIR2.ProofBind`), so EVERY live selector resolves and the cutover can delete v1 with
/// zero residue.
pub fn rotated_descriptor_name(selector: usize) -> Option<&'static str> {
    use super::columns::sel;
    Some(match selector {
        s if s == sel::TRANSFER => "transferVmDescriptor2R24",
        s if s == sel::BURN => "burnVmDescriptor2R24",
        s if s == sel::BRIDGE_MINT => "mintVmDescriptor2R24",
        s if s == sel::NOTE_SPEND => "noteSpendVmDescriptor2R24",
        s if s == sel::NOTE_CREATE => "noteCreateVmDescriptor2R24",
        s if s == sel::CELL_SEAL => "cellSealVmDescriptor2R24",
        s if s == sel::CELL_DESTROY => "cellDestroyVmDescriptor2R24",
        s if s == sel::REFUSAL => "refusalVmDescriptor2R24",
        s if s == sel::SET_PERMISSIONS => "setPermsVmDescriptor2R24",
        s if s == sel::SET_VERIFICATION_KEY => "setVKVmDescriptor2R24",
        s if s == sel::EXERCISE_VIA_CAPABILITY => "exerciseVmDescriptor2R24",
        s if s == sel::PIPELINED_SEND => "pipelinedSendVmDescriptor2R24",
        s if s == sel::REFRESH_DELEGATION => "refreshVmDescriptor2R24",
        s if s == sel::INCREMENT_NONCE => "incrementNonceVmDescriptor2R24",
        s if s == sel::REVOKE_DELEGATION => "revokeVmDescriptor2R24",
        s if s == sel::INTRODUCE => "introduceVmDescriptor2R24",
        s if s == sel::ATTENUATE_CAPABILITY => "attenuateVmDescriptor2R24",
        // The COHORT-WIDENING (STEP 1 / ROTATION-CUTOVER §2c): the eight LIVE-path effects the
        // Lean `v3Registry` now emits rotated descriptors for via `rotateV3`. GrantCapability
        // rides the BARE unattenuated cap-root grant template (`grantCapVmDescriptor2R24`),
        // distinct from the ATTENUATE_CAPABILITY phase-B descriptor.
        s if s == sel::GRANT_CAP => "grantCapVmDescriptor2R24",
        s if s == sel::MAKE_SOVEREIGN => "makeSovereignVmDescriptor2R24",
        s if s == sel::CREATE_CELL_FROM_FACTORY => "factoryVmDescriptor2R24",
        s if s == sel::EMIT_EVENT => "emitEventVmDescriptor2R24",
        s if s == sel::CREATE_CELL => "createCellVmDescriptor2R24",
        s if s == sel::SPAWN_WITH_DELEGATION => "spawnVmDescriptor2R24",
        s if s == sel::CELL_UNSEAL => "cellUnsealVmDescriptor2R24",
        s if s == sel::RECEIPT_ARCHIVE => "receiptArchiveVmDescriptor2R24",
        // GRADUATED (cap-crown): RevokeCapability (24) now has a rotated descriptor — the cap-REMOVAL
        // leg `revokeCapabilityVmDescriptor2R24` (held-membership map-read + ZERO-value remove-write,
        // NO submask). The pre-graduation pinned-digest advance is gone.
        s if s == sel::REVOKE_CAPABILITY => "revokeCapabilityVmDescriptor2R24",
        // GRADUATED (recursive-proof binding): Custom (8) now has a rotated descriptor — the
        // `customVmDescriptor2R24` leg carries the `proof_bind` op (`DescriptorIR2.ProofBind`)
        // that ties the row's `custom_proof_commitment` to a VERIFYING external sub-proof of the
        // recursion engine. THE LAST rotation-cutover residue closed; the residue is now EMPTY,
        // so the cutover can delete v1 with zero residue.
        s if s == sel::CUSTOM => "customVmDescriptor2R24",
        // The residue is EMPTY: every LIVE selector resolves above. NoOp and unknown selectors
        // fail closed.
        _ => return None,
    })
}

/// Resolve the per-slot `SetField` rotated descriptor name for a concrete field index
/// (`setFieldVmDescriptor2-{0..7}R24`), or the dynamic descriptor for an out-of-range /
/// runtime index.
pub fn rotated_set_field_descriptor_name(field_idx: u32) -> &'static str {
    match field_idx {
        0 => "setFieldVmDescriptor2-0R24",
        1 => "setFieldVmDescriptor2-1R24",
        2 => "setFieldVmDescriptor2-2R24",
        3 => "setFieldVmDescriptor2-3R24",
        4 => "setFieldVmDescriptor2-4R24",
        5 => "setFieldVmDescriptor2-5R24",
        6 => "setFieldVmDescriptor2-6R24",
        7 => "setFieldVmDescriptor2-7R24",
        _ => "setFieldDynVmDescriptor2R24",
    }
}

/// Resolve the rotated registry descriptor name for one EFFECT (the cohort-general entry
/// point the live prover uses). The `SetField` family routes by field index; every other
/// graduated effect routes by its selector. `None` for a non-cohort effect.
pub fn rotated_descriptor_name_for_effect(effect: &Effect) -> Option<&'static str> {
    match effect {
        Effect::SetField { field_idx, .. } => Some(rotated_set_field_descriptor_name(*field_idx)),
        Effect::NoOp => None,
        other => rotated_descriptor_name(super::effect_selector(other)),
    }
}

/// The cohort-general caveat manifest for a turn: by default EMPTY (most effects carry no
/// in-circuit caveat operand — the manifest's `count = 0` and every entry is the zero
/// sentinel, which `fill_caveat` commits to a well-defined `caveatCommit`). A turn that
/// genuinely carries slot/heap caveats supplies a populated manifest via the SDK bridge; the
/// rotated shape is identical either way (the appendix width does not change with the count).
pub fn empty_caveat_manifest() -> RotatedCaveatManifest {
    RotatedCaveatManifest::default()
}

/// The honest transfer-turn caveat manifest the flip test + the cutover use: ONE register
/// caveat (entry 0, domain registers, key = register 3) and one HEAP-KEY caveat (entry 1,
/// domain heap, key well beyond u8 range). The remaining slots stay empty.
pub fn transfer_caveat_manifest() -> RotatedCaveatManifest {
    let mut m = RotatedCaveatManifest::default();
    m.entries[0] = RotatedCaveatEntry {
        type_tag: 1,
        domain_tag: cav::DOMAIN_REGISTERS,
        key: BabyBear::new(3),
        params: [BabyBear::ZERO; 4],
    };
    m.entries[1] = RotatedCaveatEntry {
        type_tag: 1,
        domain_tag: cav::DOMAIN_HEAP,
        key: BabyBear::new(123_456_789),
        params: [BabyBear::ZERO; 4],
    };
    m
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
    use std::collections::BTreeSet;

    /// The rotated descriptor resolvers cover EXACTLY the registry's 36 cohort members:
    /// every name the resolvers can return is in the registry, and every registry member is
    /// reachable from some effect. This is the cohort-completeness tooth — the rotated
    /// generator can prove every effect the rotated registry emitted a descriptor for, and
    /// names nothing the registry lacks (fail-closed for non-cohort effects).
    #[test]
    fn resolvers_cover_exactly_the_rotated_registry() {
        let registry: BTreeSet<&str> = V3_STAGED_REGISTRY_TSV
            .lines()
            .filter_map(|l| l.split('\t').next())
            .filter(|s| !s.is_empty())
            .collect();
        assert_eq!(registry.len(), 36, "the rotated registry has 36 members");

        // Every name the resolvers produce: the 17 selector-mapped base effects, the cap-crown
        // RevokeCapability, the Custom recursive-proof-binding leg, the 8 STEP-1-widened LIVE-path
        // effects, the dynamic setField, and the 8 per-slot setFields.
        let mut reached: BTreeSet<&str> = BTreeSet::new();
        for &name in &[
            rotated_descriptor_name(super::super::columns::sel::TRANSFER).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::BURN).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::BRIDGE_MINT).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::NOTE_SPEND).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::NOTE_CREATE).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::CELL_SEAL).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::CELL_DESTROY).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::REFUSAL).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::SET_PERMISSIONS).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::SET_VERIFICATION_KEY).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::EXERCISE_VIA_CAPABILITY).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::PIPELINED_SEND).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::REFRESH_DELEGATION).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::INCREMENT_NONCE).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::REVOKE_DELEGATION).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::INTRODUCE).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::ATTENUATE_CAPABILITY).unwrap(),
            // GRADUATED cap-crown:
            rotated_descriptor_name(super::super::columns::sel::REVOKE_CAPABILITY).unwrap(),
            // GRADUATED recursive-proof binding (the last residue, now closed):
            rotated_descriptor_name(super::super::columns::sel::CUSTOM).unwrap(),
            // STEP-1 widened:
            rotated_descriptor_name(super::super::columns::sel::GRANT_CAP).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::MAKE_SOVEREIGN).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::CREATE_CELL_FROM_FACTORY).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::EMIT_EVENT).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::CREATE_CELL).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::SPAWN_WITH_DELEGATION).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::CELL_UNSEAL).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::RECEIPT_ARCHIVE).unwrap(),
            rotated_set_field_descriptor_name(99), // dynamic
        ] {
            reached.insert(name);
        }
        for i in 0..8 {
            reached.insert(rotated_set_field_descriptor_name(i));
        }
        assert_eq!(reached.len(), 36, "the resolvers reach 36 distinct names");
        assert_eq!(
            reached, registry,
            "the resolver names are EXACTLY the rotated registry's members"
        );
    }

    /// The honest residue is now EMPTY: every LIVE selector resolves to a rotated descriptor.
    /// `Custom` (8) was the LAST residue; it GRADUATED via the recursive-proof-binding constraint
    /// kind (`DescriptorIR2.ProofBind`) and now resolves to `customVmDescriptor2R24`. Only the
    /// structural non-effects (NoOp) and unknown selectors fail closed — there is no longer any
    /// LIVE effect the rotated registry lacks a descriptor for, so the cutover can delete v1 with
    /// zero residue. (`RevokeCapability` (24) GRADUATED earlier via the cap-crown.)
    #[test]
    fn residue_is_empty_every_live_selector_resolves() {
        // NoOp is a structural non-effect (no row), not a residue — it correctly resolves to None.
        assert_eq!(rotated_descriptor_name_for_effect(&Effect::NoOp), None);
        // THE LAST RESIDUE CLOSED: Custom (8) now resolves to its recursive-proof-binding descriptor.
        assert_eq!(
            rotated_descriptor_name(super::super::columns::sel::CUSTOM),
            Some("customVmDescriptor2R24")
        );
        // RevokeCapability (24) GRADUATED earlier via the cap-crown.
        assert_eq!(
            rotated_descriptor_name(super::super::columns::sel::REVOKE_CAPABILITY),
            Some("revokeCapabilityVmDescriptor2R24")
        );
    }
}
