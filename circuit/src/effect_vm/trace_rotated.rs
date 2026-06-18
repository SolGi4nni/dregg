//! # `trace_rotated` — THE LIVE rotated (R=24) trace generator (G1).
//!
//! `docs/ROTATION-CUTOVER.md` §5 deferred the rotated trace BUILDER: the staged keystones
//! (`EffectVmEmitRotationV3.lean`) prove the rotated R=24 cohort sound and the staged probe
//! measures the SHAPE, but the LIVE machinery that turns a real turn into the 315-column
//! rotated trace existed ONLY hand-welded inside `circuit/tests/effect_vm_rotation_flip.rs`
//! (`fill_block` / `fill_caveat`). This module PROMOTES that hand-welding into a genuine
//! generator: from the v1 186-column trace (`generate_effect_vm_trace`) plus the per-turn
//! producer witness limbs, it emits the rotated 315-column trace — the two rotated blocks
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
pub const V1_WIDTH: usize = EFFECT_VM_WIDTH; // 187 (P0-2 record-digest aux column)

/// The CONFIRMED rotated register count (ember 2026-06-12, `ROTATION-CUTOVER.md` §2b).
pub const NUM_REGISTERS: usize = 24;

/// The number of pre-iroot absorption limbs (cells_root · r0..r23 · cap_root · nullifier_root ·
/// **commitments_root** · heap_root · lifecycle · epoch · committed_height). Lean
/// `preLimbsAt_length = 32` at R = 24, after the `commitments_root` flag-day widening
/// (NUM_PRE_LIMBS 31→32 — the noteCreate commitment-set's committed home).
pub const NUM_PRE_LIMBS: usize = 1 + NUM_REGISTERS + 4 + 3; // 32 (the 4 map roots: cap/nullifier/commitments/heap)

/// A rotated block: 32 limbs + iroot + state_commit + 11 chain carriers = 45 columns. The 32-limb
/// body chunks as a 4-wide head + nine 3-wide groups + ONE arity-2 leftover (limb 31) + the iroot
/// alone, so there is ONE more chain carrier than the bare 31-limb shape (B_SPAN 43→45).
pub const B_SPAN: usize = 45;
/// The widened-caveat region: 29 manifest + 9 chain + 1 commit = 39 columns.
pub const C_SPAN: usize = 39;
/// The appendix: two blocks + the caveat region.
pub const APPENDIX: usize = 2 * B_SPAN + C_SPAN; // 129
/// The rotated trace width.
pub const ROT_WIDTH: usize = V1_WIDTH + APPENDIX; // 315

/// In-block offset of the AUTHORITY-DIGEST limb (r23, limb 24) — the single felt
/// folding ALL authority-bearing cell state no other rotated limb carries
/// (permissions / VK / delegate / delegation / program / mode / token_id +
/// visibility / commitments / proved / side-table roots + fields[8..16]). This IS
/// the EffectVM `CellState::record_digest` (the v1-prefix OLD_COMMIT's fourth root
/// input), so the v1 OLD_COMMIT binds the SAME authority residue the rotated weld
/// carries — closing audit P0-2 across BOTH legs.
pub const B_AUTHORITY_DIGEST: usize = 24;
/// Alias used by the record-forcing pin (`record_pin_offset`): the setPermissions/setVK post
/// `record_digest` limb IS the authority-digest limb (r23, limb 24). Lean `B_RECORD_DIGEST`.
pub const B_RECORD_DIGEST: usize = B_AUTHORITY_DIGEST;
/// In-block offset of the per-cell `lifecycle` felt limb (limb 29 in `preLimbsAt`, shifted +1 by
/// `commitments_root`), filled by the producer witness `rotation_witness.rs::lifecycle_felt`. The
/// forced limb for the lifecycle flips (cellSeal/cellUnseal/cellDestroy). Lean
/// `EffectVmEmitRotationV3.B_LIFECYCLE`.
pub const B_LIFECYCLE: usize = 29;
/// In-block offset of the `cap_root` limb (the welded cap-root, limb 25).
pub const B_CAP_ROOT: usize = 25;
/// nullifier-root offset inside a block (limb 26) — the deployed nullifier accumulator's
/// openable sorted-Poseidon2 root the noteSpend grow-gate (`nullifierFreshOp` / `nullifierInsertOp`)
/// opens against.
pub const B_NULLIFIER_ROOT: usize = 26;
/// commitments-root offset inside a block (limb 27) — the flag-day committed shielded-set root
/// the noteCreate grow-gate (`commitmentsInsertOp`) opens against. Rides AFTER nullifier_root,
/// shifting heap/lifecycle/epoch/committed_height each by one (Lean `B_COMMITMENTS_ROOT`).
pub const B_COMMITMENTS_ROOT: usize = 27;
/// heap-root offset inside a block (limb 28, shifted +1 by `commitments_root`).
pub const B_HEAP_ROOT: usize = 28;
/// In-block offset of the `committed_height` limb (limb 31, shifted +1).
pub const B_COMMITTED_HEIGHT: usize = 31;
/// In-block offset of the iroot carrier (absorbed last, limb 32).
pub const B_IROOT: usize = 32;
/// In-block offset of the `state_commit` carrier (the chain's final digest).
pub const B_STATE_COMMIT: usize = 33;
/// In-block base of the chained-absorption intermediate carriers (11 sites, 34..=44).
pub const B_CHAIN_BASE: usize = 34;

/// Absolute base column of the BEFORE rotated block.
pub const BEFORE_BASE: usize = V1_WIDTH; // 186
/// Absolute base column of the AFTER rotated block.
pub const AFTER_BASE: usize = V1_WIDTH + B_SPAN; // 232
/// Absolute base column of the widened-caveat region.
pub const CAVEAT_BASE: usize = V1_WIDTH + 2 * B_SPAN; // 277

/// The number of v1 public inputs the rotated PI vector prefixes (`ACTIVE_BASE_COUNT`).
pub const V1_PI_COUNT: usize = 34;
/// The rotated public-input count (34 v1 + 4 appended).
pub const ROT_PI_COUNT: usize = 38;
/// The rotated NOTE-SPEND public-input count (the 38-PI rotated prefix + the appended
/// nullifier slot at index 38 — `EffectVmEmitRotationV3.noteSpendV3`, the C4 last-flip-gate
/// close). Only the note-spend cohort member carries this fifth pin.
pub const ROT_NULLIFIER_PI_COUNT: usize = 39;
/// The rotated PI slot carrying the spend row's folded nullifier (the C4 weld). Equals
/// `ROT_PI_COUNT` — the first slot past the four rotated commit pins.
pub const ROT_NULLIFIER_PI: usize = ROT_PI_COUNT;

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
    /// The 32 pre-iroot limbs, in absorption order.
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

    // THE C4 LAST-FLIP-GATE (note-spend nullifier weld): a NoteSpend turn rotates against the
    // `noteSpendVmDescriptor2R24` descriptor, which carries a FIFTH appended PI pin
    // (`EffectVmEmitRotationV3.noteSpendV3`) welding the spend row's folded nullifier
    // (`param::NULLIFIER = param0`, col `PARAM_BASE + 0`) to rotated PI slot 38 on the FIRST
    // row — the rotated analog of the v1 hand-AIR D5 cross-binding (offset 198). The note-spend
    // spend is laid on row 0 (`generate_effect_vm_trace`'s `Effect::NoteSpend` arm), so the pin
    // reads `r0[PARAM_BASE + param::NULLIFIER]`. We append it ONLY for a NoteSpend lead effect,
    // matching the descriptor's 39-PI shape (the prover asserts `pis.len() == piCount`); the
    // other 35 cohort members keep the 38-PI vector. This lets a note-spending turn rotate:
    // `verify_full_turn` step 8 reads PI[38] instead of refusing the rotated leg.
    if matches!(effects.first(), Some(Effect::NoteSpend { .. })) {
        use super::columns::{PARAM_BASE, param};

        // SINGLE-SPEND INVARIANT (the soundness tooth must survive rotation). The v1 hand-AIR
        // gate is PER-ROW (`s_notespend·(param0 − PI[NOTESPEND_NULLIFIER])` on EVERY spend row)
        // AND v1 surfaces ONE nullifier into the single PI slot — so a turn with two DISTINCT
        // nullifiers is UNSAT on v1 (`trace.rs` D5: "multi-distinct-nullifier proofs need PI
        // extension — deferred"). The rotated weld is a FIRST-row pin against the SAME single PI
        // slot (PI[38]), cross-checked by `verify_full_turn` step 8 against the one freshness
        // proof. A second NoteSpend on a NON-first row would be UNPINNED by the rotated
        // descriptor and ESCAPE the freshness check — a double-spend the v1 leg forbids. So the
        // rotated note-spend leg accepts exactly ONE spend row (v1's single-nullifier shape); a
        // multi-NoteSpend turn fails closed here and falls back to the v1 leg. Without this the
        // rotation would WEAKEN no-double-spend (a regressed tooth), not preserve it.
        let spend_count = effects
            .iter()
            .filter(|e| matches!(e, Effect::NoteSpend { .. }))
            .count();
        if spend_count != 1 {
            return Err(format!(
                "rotated note-spend leg supports exactly one spend row (the single-nullifier \
                 freshness shape), got {spend_count}; a multi-NoteSpend turn must use the v1 leg \
                 (where a second distinct nullifier is UNSAT). Rotating it would leave the \
                 non-first spend unpinned and ESCAPE the no-double-spend freshness check."
            ));
        }

        dpis.push(r0[PARAM_BASE + param::NULLIFIER]); // PI 38: the spend row's folded nullifier
        debug_assert_eq!(dpis.len(), ROT_NULLIFIER_PI_COUNT);
    }

    // THE RECORD-FORCING PIN (the deployment-soundness close for the 7 binds-but-unforced
    // effects: cellSeal/cellUnseal/cellDestroy/setPermissions/setVK + the audit writes
    // refusal/receiptArchive — `EffectVmEmitRotationV3.rotateV3WithRecordPin`). The rotated AFTER
    // block CARRIES the per-cell write (limb `B_LIFECYCLE = 29` for the lifecycle flips, limb
    // `B_RECORD_DIGEST = 24` for the permissions/VK record-digest AND the audit-slot writes —
    // refusal/receiptArchive set a named record field in `fields_root`, which the r23 authority
    // digest folds), and the rolled-up commitment BINDS it — but bare `rotateV3` does NOT FORCE
    // the AFTER limb to the correctly-written value. The descriptor for these seven carries a
    // FIFTH last-row PI pin welding that limb to rotated PI slot 38; a frozen-lifecycle /
    // un-written-record / frozen-audit-slot AFTER block FAILS the pin and is UNSAT. We push the
    // honest post value (read from the LAST row's AFTER block, exactly the column the pin binds)
    // so the honest trace satisfies it; the verifier recomputes PI[38] from the committed
    // pre-state + the effect, so a forgery cannot match it. The 33 other cohort members keep the
    // 38-PI vector.
    if let Some(off) = record_pin_offset(effects.first()) {
        dpis.push(last[AFTER_BASE + off]); // PI 38: the correctly-written post lifecycle / record digest
        debug_assert_eq!(dpis.len(), ROT_PI_COUNT + 1);
    }

    // THE ACCOUNTS-SET GROW-GATE PIN (createCell / factory / spawn — the deployment-real account
    // set-insert close). The live `{createCell,factory,spawn}VmDescriptor2R24` carry a FIFTH pin
    // welding the new-cell key (`param0`, col `PARAM_BASE + 0` — the `Effect::CreateCell`/`Spawn`/
    // `Factory` arm writes the child id there on row 0) to rotated PI slot 38, plus the two
    // `cells_root` map-ops (limb 0) that force the accounts set-insert. We push the row-0 new-cell
    // key so the honest trace matches the 39-PI shape; the openable before/after cells trees are
    // threaded by `generate_rotated_create_cell_trace_with_accounts_tree`. Mirrors Lean
    // `EffectVmEmitRotationV3.{createCellV3,factoryV3,spawnV3}`.
    if let Some(key_col) = new_cell_key_param_col(effects.first()) {
        use super::columns::PARAM_BASE;
        dpis.push(r0[PARAM_BASE + key_col]); // PI 38: the new-cell key
        debug_assert_eq!(dpis.len(), ROT_NULLIFIER_PI_COUNT);
    }

    // THE COMMITMENTS-SET GROW-GATE PIN (noteCreate — the deployment-real commitment set-insert
    // close, the `commitments_root` flag-day). The live `noteCreateVmDescriptor2R24` carries a FIFTH
    // pin welding the published note commitment (`param0`, col `PARAM_BASE + 0` — the
    // `Effect::NoteCreate` arm writes the commitment there on row 0) to rotated PI slot 38, plus the
    // `commitmentsInsertOp` map-op (limb 27) that forces the commitment set-insert. We push the row-0
    // commitment so the honest trace matches the 39-PI shape; the openable before/after commitments
    // trees are threaded by `generate_rotated_note_create_trace_with_commitments_tree`. Mirrors Lean
    // `EffectVmEmitRotationV3.noteCreateV3`.
    if matches!(effects.first(), Some(Effect::NoteCreate { .. })) {
        use super::columns::{PARAM_BASE, param};
        dpis.push(r0[PARAM_BASE + param::NULLIFIER]); // PI 38: the published note commitment (param0)
        debug_assert_eq!(dpis.len(), ROT_NULLIFIER_PI_COUNT);
    }

    Ok((trace, dpis))
}

/// **THE DEPLOYMENT-REAL noteSpend nullifier-tree wiring (the kernel-set grow-gate's witness).**
///
/// The live `noteSpendVmDescriptor2R24` now carries two map-ops gated by the spend selector — the
/// `nullifierFreshOp` (`.absent`: the published nullifier is a NON-MEMBER of the BEFORE nullifier
/// tree — the in-circuit double-spend tooth) and `nullifierInsertOp` (`.write`: the AFTER root IS
/// the genuine sorted insert of the nullifier). Those map-ops open the rotated `nullifier_root`
/// limb (limb 26) against a real sorted-Poseidon2 tree. The bare generator carries limb 26 as a
/// turn-invariant `hash_bytes` witness, which the map-ops cannot open.
///
/// This wrapper makes limb 26 the DEPLOYED openable accumulator root for a NoteSpend turn:
///   * `before_nullifiers` are the existing nullifier-set leaves (the spent nullifier MUST be
///     absent — the freshness precondition; the `.absent` op refuses a double-spend);
///   * limb 26 of EVERY before-block is overwritten with the BEFORE tree's root, and limb 26 of
///     every after-block with the root of the BEFORE tree PLUS the inserted spent nullifier (the
///     set-insert the `.write` op forces);
///   * the affected `wireCommitR` chain + `STATE_COMMIT` carriers are recomputed in place, and the
///     OLD/NEW rotated commit PIs are re-derived, so the published commitment binds the grown set;
///   * the BEFORE tree's leaves are returned as the single `map_heaps` entry the prover threads
///     into `prove_vm_descriptor2` to resolve both map-ops.
///
/// The nullifier's leaf key is the spend row's folded `param0` (`PARAM_BASE + param::NULLIFIER` —
/// the SAME felt PI[38] pins), and the inserted leaf value is the note value (`param::NOTE_VALUE_LO`),
/// so the gate's key/value are the row's own published columns. Returns `(trace, dpis, map_heaps)`.
pub fn generate_rotated_note_spend_trace_with_nullifier_tree(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    before_nullifiers: &[crate::heap_root::HeapLeaf],
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>, Vec<Vec<crate::heap_root::HeapLeaf>>), String> {
    use super::columns::{PARAM_BASE, param};
    use crate::heap_root::{CanonicalHeapTree, HEAP_TREE_DEPTH, HeapLeaf};

    if !matches!(effects.first(), Some(Effect::NoteSpend { .. })) {
        return Err("nullifier-tree wiring is only for a NoteSpend lead effect".into());
    }

    // The base rotated trace (carries the welds, the v1 economic block, the nullifier PI[38]).
    let (mut trace, mut dpis) =
        generate_rotated_effect_vm_trace(initial_state, effects, before_w, after_w, caveat)?;

    // The spent nullifier's leaf key + value, read from the spend row (row 0).
    let nf_key = trace[0][PARAM_BASE + param::NULLIFIER];
    let nf_value = trace[0][PARAM_BASE + param::NOTE_VALUE_LO];

    // The BEFORE tree (the deployed accumulator before the spend) and the AFTER tree (= BEFORE +
    // the inserted nullifier leaf). The spent nullifier MUST be absent from BEFORE — the freshness
    // precondition the `.absent` op enforces; a double-spend has no bracketing witness and the
    // prover REFUSES it.
    let before_tree = CanonicalHeapTree::new(before_nullifiers.to_vec(), HEAP_TREE_DEPTH);
    if before_tree.position_of(nf_key).is_some() {
        return Err(
            "double-spend: the nullifier is already in the BEFORE nullifier tree — the in-circuit \
             freshness (`.absent`) op has no bracketing witness and refuses the turn"
                .into(),
        );
    }
    let before_root = before_tree.root();
    let mut after_leaves = before_nullifiers.to_vec();
    after_leaves.push(HeapLeaf {
        addr: nf_key,
        value: nf_value,
    });
    let after_root = CanonicalHeapTree::new(after_leaves.clone(), HEAP_TREE_DEPTH).root();

    // Override limb 26 of BOTH blocks on EVERY row with the openable accumulator roots, then
    // recompute the dependent chained commitments so the published `STATE_COMMIT` binds the grown
    // set. (The bare limb-26 `hash_bytes` witness is replaced by the real tree roots.)
    for row in trace.iter_mut() {
        row[BEFORE_BASE + B_NULLIFIER_ROOT] = before_root;
        row[AFTER_BASE + B_NULLIFIER_ROOT] = after_root;
        recompute_block_commit(row, BEFORE_BASE);
        recompute_block_commit(row, AFTER_BASE);
    }

    // Re-derive the OLD/NEW rotated commit PIs (the limb-26 override moved the commitments).
    let r0_commit = trace[0][BEFORE_BASE + B_STATE_COMMIT];
    let last_commit = trace[trace.len() - 1][AFTER_BASE + B_STATE_COMMIT];
    dpis[V1_PI_COUNT] = r0_commit; // PI 34: rotated OLD commit
    dpis[V1_PI_COUNT + 1] = last_commit; // PI 35: rotated NEW commit

    Ok((trace, dpis, vec![before_nullifiers.to_vec()]))
}

/// The deployed `cells_root` (limb 0 of the rotated block) — the openable sorted-Poseidon2 accounts
/// accumulator. The createCell/factory/spawn descriptors (`EffectVmEmitRotationV3.{createCellV3,
/// factoryV3,spawnV3}`) now carry two map-ops on it: `cellsFreshOp` (`.absent`: the new-cell key is
/// a NON-MEMBER of the BEFORE accounts tree — no id collision) and `cellsInsertOp` (`.insert`: the
/// AFTER root IS the genuine sorted insert of the new-cell key).
const B_CELLS_ROOT: usize = 0;

/// **THE DEPLOYMENT-REAL createCell / factory / spawn accounts-tree wiring (the accounts-set
/// grow-gate's witness).** The clone of `generate_rotated_note_spend_trace_with_nullifier_tree` for
/// the `cells_root` limb (limb 0): it makes limb 0 the openable accounts accumulator for a
/// createCell/factory/spawn turn.
///   * `before_accounts` are the existing account-set leaves (the new-cell key MUST be absent — the
///     no-collision precondition the `.absent` op enforces);
///   * limb 0 of every before-block is overwritten with the BEFORE tree's root, and limb 0 of every
///     after-block with the root of BEFORE + the inserted new-cell key (the set-insert the `.insert`
///     op forces);
///   * the affected `wireCommitR` chain + `STATE_COMMIT` carriers are recomputed in place, and the
///     OLD/NEW rotated commit PIs are re-derived so the published commitment binds the grown set;
///   * the BEFORE tree's leaves are returned as the single `map_heaps` entry the prover threads.
/// The new-cell key column is `param0` for createCell/spawn, `param1` (CHILD_VK_DERIVED) for factory
/// (`new_cell_key_param_col`). Returns `(trace, dpis, map_heaps)`.
pub fn generate_rotated_create_cell_trace_with_accounts_tree(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    before_accounts: &[crate::heap_root::HeapLeaf],
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>, Vec<Vec<crate::heap_root::HeapLeaf>>), String> {
    use super::columns::PARAM_BASE;
    use crate::heap_root::{CanonicalHeapTree, HEAP_TREE_DEPTH, HeapLeaf};

    let key_col = new_cell_key_param_col(effects.first()).ok_or_else(|| {
        "accounts-tree wiring is only for a CreateCell / CreateCellFromFactory / SpawnWithDelegation \
         lead effect"
            .to_string()
    })?;

    // The base rotated trace (carries the welds, the v1 economic block, the new-cell-key PI[38]).
    let (mut trace, mut dpis) =
        generate_rotated_effect_vm_trace(initial_state, effects, before_w, after_w, caveat)?;

    // The new-cell key, read from the create row (row 0).
    let cell_key = trace[0][PARAM_BASE + key_col];

    // The BEFORE accounts tree and the AFTER tree (= BEFORE + the inserted new-cell key). The
    // new-cell key MUST be absent from BEFORE — the no-collision precondition the `.absent` op
    // enforces; a re-creation of an existing cell has no bracketing witness and the prover REFUSES.
    let before_tree = CanonicalHeapTree::new(before_accounts.to_vec(), HEAP_TREE_DEPTH);
    if before_tree.position_of(cell_key).is_some() {
        return Err(
            "account-id collision: the new-cell key is already in the BEFORE accounts tree — the \
             in-circuit no-collision (`.absent`) op has no bracketing witness and refuses the turn"
                .into(),
        );
    }
    let before_root = before_tree.root();
    let mut after_leaves = before_accounts.to_vec();
    after_leaves.push(HeapLeaf {
        addr: cell_key,
        value: cell_key, // the born-empty cell rides its own key as its leaf value.
    });
    let after_root = CanonicalHeapTree::new(after_leaves.clone(), HEAP_TREE_DEPTH).root();

    // Override limb 0 of BOTH blocks on EVERY row with the openable accumulator roots, then
    // recompute the dependent chained commitments so the published `STATE_COMMIT` binds the grown
    // set.
    for row in trace.iter_mut() {
        row[BEFORE_BASE + B_CELLS_ROOT] = before_root;
        row[AFTER_BASE + B_CELLS_ROOT] = after_root;
        recompute_block_commit(row, BEFORE_BASE);
        recompute_block_commit(row, AFTER_BASE);
    }

    // Re-derive the OLD/NEW rotated commit PIs (the limb-0 override moved the commitments).
    dpis[V1_PI_COUNT] = trace[0][BEFORE_BASE + B_STATE_COMMIT]; // PI 34: rotated OLD commit
    dpis[V1_PI_COUNT + 1] = trace[trace.len() - 1][AFTER_BASE + B_STATE_COMMIT]; // PI 35: NEW commit

    Ok((trace, dpis, vec![before_accounts.to_vec()]))
}

/// **THE DEPLOYMENT-REAL noteCreate commitments-tree wiring (the commitments-set grow-gate's
/// witness).** The clone of `generate_rotated_note_spend_trace_with_nullifier_tree` for the
/// `commitments_root` limb (limb 27 — the flag-day new committed shielded-set root): it makes limb
/// 27 the openable commitments accumulator for a noteCreate turn.
///   * `before_commitments` are the existing note-commitment-set leaves;
///   * limb 27 of every before-block is overwritten with the BEFORE tree's root, and limb 27 of
///     every after-block with the root of BEFORE + the inserted note commitment (the set-insert the
///     `commitmentsInsertOp .insert` op forces);
///   * the affected `wireCommitR` chain + `STATE_COMMIT` carriers are recomputed in place, and the
///     OLD/NEW rotated commit PIs are re-derived so the published commitment binds the grown set;
///   * the BEFORE tree's leaves are returned as the single `map_heaps` entry the prover threads.
/// The commitment key column is `param0` (`Effect::NoteCreate { commitment }`); the inserted leaf
/// value is the note value (`param::NOTE_VALUE_LO = param1`). NoteCreate is append-only, so there
/// is NO `.absent` freshness precondition (a re-published commitment is admissible). Returns
/// `(trace, dpis, map_heaps)`.
pub fn generate_rotated_note_create_trace_with_commitments_tree(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    before_commitments: &[crate::heap_root::HeapLeaf],
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>, Vec<Vec<crate::heap_root::HeapLeaf>>), String> {
    use super::columns::{PARAM_BASE, param};
    use crate::heap_root::{CanonicalHeapTree, HEAP_TREE_DEPTH, HeapLeaf};

    if !matches!(effects.first(), Some(Effect::NoteCreate { .. })) {
        return Err("commitments-tree wiring is only for a NoteCreate lead effect".into());
    }

    // The base rotated trace (carries the welds, the v1 economic block, the commitment PI[38]).
    let (mut trace, mut dpis) =
        generate_rotated_effect_vm_trace(initial_state, effects, before_w, after_w, caveat)?;

    // The note commitment's leaf key (param0) + value (param1), read from the create row (row 0).
    let cm_key = trace[0][PARAM_BASE + param::NULLIFIER]; // param0 (the commitment rides param slot 0)
    let cm_value = trace[0][PARAM_BASE + param::NOTE_VALUE_LO];

    // The BEFORE commitments tree and the AFTER tree (= BEFORE + the inserted commitment). NoteCreate
    // is append-only — no `.absent` freshness precondition.
    let before_tree = CanonicalHeapTree::new(before_commitments.to_vec(), HEAP_TREE_DEPTH);
    let before_root = before_tree.root();
    let mut after_leaves = before_commitments.to_vec();
    after_leaves.push(HeapLeaf {
        addr: cm_key,
        value: cm_value,
    });
    let after_root = CanonicalHeapTree::new(after_leaves.clone(), HEAP_TREE_DEPTH).root();

    // Override limb 27 of BOTH blocks on EVERY row with the openable accumulator roots, then
    // recompute the dependent chained commitments so the published `STATE_COMMIT` binds the grown
    // set.
    for row in trace.iter_mut() {
        row[BEFORE_BASE + B_COMMITMENTS_ROOT] = before_root;
        row[AFTER_BASE + B_COMMITMENTS_ROOT] = after_root;
        recompute_block_commit(row, BEFORE_BASE);
        recompute_block_commit(row, AFTER_BASE);
    }

    // Re-derive the OLD/NEW rotated commit PIs (the limb-27 override moved the commitments).
    dpis[V1_PI_COUNT] = trace[0][BEFORE_BASE + B_STATE_COMMIT]; // PI 34: rotated OLD commit
    dpis[V1_PI_COUNT + 1] = trace[trace.len() - 1][AFTER_BASE + B_STATE_COMMIT]; // PI 35: NEW commit

    Ok((trace, dpis, vec![before_commitments.to_vec()]))
}

/// The in-AFTER-block limb offset the record-forcing pin welds for a given lead effect, or
/// `None` for the 35 cohort members that carry no record pin. The lifecycle flips force the
/// per-cell `lifecycle` felt (limb 29); the permissions/VK writes force the per-cell
/// `authority_digest` / `record_digest` (limb 24 = r23). Mirrors the Lean routing in
/// `EffectVmEmitRotationV3.v3Registry` (`cellSealV3` … `setVKV3`).
fn record_pin_offset(lead: Option<&Effect>) -> Option<usize> {
    match lead {
        Some(Effect::CellSeal { .. })
        | Some(Effect::CellUnseal { .. })
        | Some(Effect::CellDestroy { .. }) => Some(B_LIFECYCLE),
        Some(Effect::SetPermissions { .. }) | Some(Effect::SetVerificationKey { .. }) => {
            Some(B_RECORD_DIGEST)
        }
        // `ReceiptArchive` writes the cell LIFECYCLE (`Archived`) in the deployed `apply_receipt_archive`
        // (`c.archive(checkpoint)`), which `lifecycle_felt` (limb `B_LIFECYCLE = 29`) folds into a
        // distinct `Archived` felt — NOT the r23 authority residue. So the genuine mover is the
        // lifecycle limb; the record-forcing pin (`receiptArchiveV3`) welds limb 29 to PI 38 and the
        // verifier anchors `lifecycle_felt_cell(post_cell)`. A frozen-lifecycle archive forgery is
        // UNSAT. Mirrors Lean `EffectVmEmitRotationV3.receiptArchiveV3` (`rotateV3WithRecordPin
        // B_LIFECYCLE …`).
        Some(Effect::ReceiptArchive { .. }) => Some(B_LIFECYCLE),
        // `Refusal` writes the WELDED `fields[4]` indexed slot + bumps the nonce in the deployed
        // `apply_refusal`, ALIGNED to the Lean SPEC `TurnExecutorFull.refusalField` (the audit lands
        // in the EXT `fields_root`, which `compute_authority_digest_felt` FOLDS into the r23 authority
        // residue, `B_RECORD_DIGEST`). So the AFTER `record_digest` limb MOVES on a genuine refusal; the
        // record-forcing pin (`refusalV3`) welds it to PI 38, and the verifier anchors
        // `compute_authority_digest_felt(post_cell)`. A frozen-audit refusal forgery is UNSAT. Mirrors
        // Lean `EffectVmEmitRotationV3.refusalV3`.
        Some(Effect::Refusal { .. }) => Some(B_RECORD_DIGEST),
        _ => None,
    }
}

/// The param column carrying the new-cell key for the accounts-set grow-gate family
/// (createCell / factory / spawn), or `None` otherwise. createCell/spawn write the new-cell id
/// into `param0`; factory writes the factory VK into `param0` and the DERIVED CHILD VK into
/// `param1` — so the factory's new-cell key (and the column its grow-gate + PI[38] pin reference)
/// is `param1`. Mirrors Lean `EffectVmEmitRotationV3.{NEW_CELL_KEY_PARAM_COL,
/// FACTORY_CHILD_KEY_PARAM_COL}` (the gate key columns of `{createCellV3,factoryV3,spawnV3}`).
fn new_cell_key_param_col(lead: Option<&Effect>) -> Option<usize> {
    match lead {
        Some(Effect::CreateCell { .. }) | Some(Effect::SpawnWithDelegation { .. }) => Some(0),
        Some(Effect::CreateCellFromFactory { .. }) => {
            Some(super::columns::param::CHILD_VK_DERIVED)
        }
        _ => None,
    }
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
    row[base..base + NUM_PRE_LIMBS].copy_from_slice(&w.pre_limbs[..NUM_PRE_LIMBS]);
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
/// is the SAME shape (315 cols + 38 PIs) for every member (the appendix is parametric, not
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

// ============================================================================
// THE CAP-OPEN APPENDIX (Lean `Dregg2.Circuit.Emit.CapOpenEmit` —
// `attenuateCapOpenEffV3`, descriptor `dregg-effectvm-attenuateA-v1-rot24-v3-capopen-eff`).
//
// The cap-open appendix EXTENDS the rotated base trace with 59 columns
// that OPEN the deployed depth-16 cap-tree at a write-mask leaf whose target is the
// turn's `src`. The Lean constraints (`DeployedCapOpen.Satisfied`) realize:
//   * 1 leaf chip-absorb (arity 7: the 7 leaf fields → leafDigest);
//   * 16 node chip-absorbs (arity 3: `[FACT_MARK, left, right]` → node), folded by the
//     direction bits from the leaf digest up to the root;
//   * 16 dir-bool gates, a rootPin (node[15] == capRoot), a targetBind (leaf[1] == src),
//     and the FAITHFUL two-axis facet × tier: transferFacet (leaf[3] mask_lo == EFFECT_TRANSFER),
//     facetHi (leaf[4] mask_hi == 0), authTag (leaf[2] auth_tag == Signature).
//
// CRITICAL HASH SEAM (Lean `DeployedCapTree.nodeOf` / `capLeafDigest`): the chip lookups
// realize `hash_many`-ABSORB nodes — `hash_many(&[FACT_MARK, left, right])` and
// `hash_many(&[7 leaf fields])` — NOT `poseidon2::hash_fact` (which uses a different state
// layout). The IR-v2 interpreter auto-gathers the chip table from these lookup tuples, so
// filling the cap-open columns with genuine `hash_many` values makes every lookup land on a
// real (arity, padded_inputs, hash) chip row. ZERO hand-authored constraint semantics here —
// only column FILLS; the declared Lean chip lookups + base gates do all the enforcement.
// ============================================================================

/// The deployed cap-tree depth (`CapOpenEmit.DEPTH = 16`).
pub const CAP_OPEN_DEPTH: usize = 16;
/// The base column of the cap-open appendix (`CAP_OPEN_BASE = ROT_WIDTH = 315`).
pub const CAP_OPEN_BASE: usize = ROT_WIDTH; // 315
/// The width of the FULL `EffectMask` bit decomposition (residual (a) — GENUINE MEMBERSHIP). The
/// decoded facet is the full `u32` mask `maskOfLimbs(mask_lo, mask_hi) = mask_lo + mask_hi·65536`
/// (`EFFECT_ALL = 0xFFFF_FFFF`), so the decomposition spans all 32 bits: any deployed effect-kind bit
/// `1 << n` (`n < 32`, up to `EFFECT_ATTENUATE_CAPABILITY = 1 << 23`) is selectable AND a broad cap
/// (`mask_hi = 0xFFFF`) decomposes fully. The Lean twin is `DeployedCapOpen.MASK16_BITS`.
pub const CAP_OPEN_MASK_BITS: usize = 32;
/// The cap-open appendix span: 7 leaf + 1 leafDigest + 16×(sib,dir,node) + capRoot + src + effBit
/// + 32 mask-bit columns = 91. The trailing 32 mask-bit columns carry the boolean decomposition of
/// the FULL effect mask the genuine SUBMASK facet gate (`maskBitBoolGate`/`maskReconGate`/
/// `selectedBitGate`) reads — NOT the over-strict equality `mask_lo == effBit` (and NO `mask_hi == 0`
/// pin, so a broad `EFFECT_ALL` cap is admitted).
pub const CAP_OPEN_SPAN: usize = 7 + 1 + 3 * CAP_OPEN_DEPTH + 3 + CAP_OPEN_MASK_BITS; // 91
/// The cap-open trace width (`ROT_WIDTH + 91`).
pub const CAP_OPEN_WIDTH: usize = ROT_WIDTH + CAP_OPEN_SPAN;

/// The `FACT_MARK` node-tag felt (`DeployedCapTree.FACT_MARK = 0xFACF`).
pub const FACT_MARK: u32 = 0xFACF; // 64207
/// The leaf `mask_lo` the FAITHFUL two-axis facet gate (`DeployedCapOpen.transferFacetGate`)
/// pins: `EFFECT_TRANSFER = 1 << 1 = 2` (`FacetAuthority.EFFECT_TRANSFER`). The decoded facet
/// `maskOfLimbs mask_lo mask_hi` permits the `EFFECT_TRANSFER` effect-kind bit. This REPLACES
/// the toy `writeMaskGate` (`mask_lo == 3`).
pub const WRITE_MASK_LO: u32 = 2;
/// The leaf `mask_hi` the `facetHiGate` pins (`== 0`, so the decoded facet is exactly `mask_lo`).
pub const FACET_MASK_HI: u32 = 0;
/// The leaf `auth_tag` the `authTagGate` pins: the `Signature` tier byte `1`
/// (`tierOfTag 1 = .signature`).
pub const SIGNATURE_AUTH_TAG: u32 = 1;

/// One cap-membership witness: the 7 leaf fields (in `CapOpenCols` order
/// `[slot_hash, target, auth_tag, mask_lo, mask_hi, expiry, breadstuff]`), the 16 sibling
/// digests + direction bits of the membership path, the recomposed `cap_root`, and the
/// turn's `src` cell id. A `recomposes()` self-check rebuilds the root from the leaf digest
/// over the path (ABSORB-node `hash_many`, NOT `hash_fact`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CapOpenWitness {
    /// The 7 cap-leaf fields (`slot_hash, target, auth_tag, mask_lo, mask_hi, expiry, breadstuff`).
    pub leaf: [BabyBear; 7],
    /// The 16 sibling digests of the membership path.
    pub siblings: [BabyBear; CAP_OPEN_DEPTH],
    /// The 16 direction bits (0 ⇒ cur is the LEFT child at that level).
    pub directions: [u8; CAP_OPEN_DEPTH],
    /// The recomposed committed cap-tree root (must equal node[15]).
    pub cap_root: BabyBear,
    /// The turn's source-cell id (must equal `leaf[1]`, the leaf target).
    pub src: BabyBear,
    /// **(residual (a))** The turn's ACTUAL effect-kind bit (`EFFECT_<kind> = 1 << n`), written to
    /// the `effBit` column (`base + 58`). The descriptor's `effBitGateFor` pins it; the general
    /// `facetEffGate` binds `leaf.mask_lo == eff_bit` — so the cap must permit THAT effect-kind.
    /// `EFFECT_TRANSFER (= WRITE_MASK_LO = 2)` for the transfer/attenuate legs; each fan-out leg
    /// carries its own bit (delegate = `1<<16`, introduce = `1<<13`, grantCap = `1<<2`, …).
    pub eff_bit: u32,
}

/// The leaf digest: the SINGLE rate-8 chip absorb of the 7 leaf fields (arity 7), byte-identical
/// to `cap_root::CapLeaf::digest` and the Lean `capLeafDigest = sponge ∘ leafFields`. ONE chip
/// row (no length tag; lanes 0..6 = the genuine fields), so the IR-v2 chip realizes it as one
/// lookup — the unification that discharges `SchemeRealizedByChip`.
pub fn cap_leaf_digest(leaf: &[BabyBear; 7]) -> BabyBear {
    crate::cap_root::cap_chip_absorb(leaf)
}

/// One node hash: the arity-3 rate-8 chip absorb of `[FACT_MARK, left, right]` (Lean
/// `nodeOf = sponge [FACT_MARK, l, r]`), byte-identical to `cap_root::cap_node`. ONE chip row
/// (FACT_MARK rides rate lane 0, length tag 3 in lane 4) — NOT the capacity-tagged `hash_fact`.
pub fn cap_node(left: BabyBear, right: BabyBear) -> BabyBear {
    crate::cap_root::cap_chip_absorb(&[BabyBear::new(FACT_MARK), left, right])
}

/// Mix `(cur, sib)` by the direction bit into `(left, right)` (Lean `leftExpr`/`rightExpr`):
/// `dir = 0 ⇒ (cur, sib)` (cur is LEFT), `dir = 1 ⇒ (sib, cur)`.
fn cap_mix(cur: BabyBear, sib: BabyBear, dir: u8) -> (BabyBear, BabyBear) {
    if dir == 0 {
        (cur, sib)
    } else {
        (sib, cur)
    }
}

impl CapOpenWitness {
    /// Recompute the root from the leaf digest over the `(sib, dir)` path using ABSORB-node
    /// `hash_many` compression. The self-check the fold's soundness rests on.
    pub fn recomposes(&self) -> BabyBear {
        let mut cur = cap_leaf_digest(&self.leaf);
        for lvl in 0..CAP_OPEN_DEPTH {
            let (l, r) = cap_mix(cur, self.siblings[lvl], self.directions[lvl]);
            cur = cap_node(l, r);
        }
        cur
    }

    /// Build a cap-open witness from a c-list of leaves and a chosen position. The depth-16
    /// ABSORB-node tree is laid over `1 << DEPTH` leaf slots; the chosen leaf rides `position`,
    /// the rest are zero-leaf padding (`hash_many(&[0;7])`). The membership `(siblings,
    /// directions)` path + the recomposed root are computed; `src` is pinned to `leaf[1]` so
    /// the target gate holds. The chosen leaf MUST carry the FAITHFUL two-axis facet × tier the
    /// descriptor's gates pin: `mask_lo == EFFECT_TRANSFER (2)` (`transferFacetGate`), `mask_hi
    /// == 0` (`facetHiGate`), and `auth_tag == Signature (1)` (`authTagGate`).
    pub fn build(leaves: &[[BabyBear; 7]], position: usize) -> Result<Self, String> {
        Self::build_for(leaves, position, WRITE_MASK_LO)
    }

    /// **`build_for` (THE FAN-OUT path builder).** Like [`Self::build`] but for an ARBITRARY
    /// effect-kind bit `eff_bit` (the chosen leaf's `mask_lo` must equal `eff_bit`, not the constant
    /// EFFECT_TRANSFER), and WITHOUT the `auth_tag == Signature` pin (the fan-out `capOpenConstraintsEff`
    /// appendix reads the DECODED tier). `build` is the `eff_bit := EFFECT_TRANSFER` instance.
    pub fn build_for(
        leaves: &[[BabyBear; 7]],
        position: usize,
        eff_bit: u32,
    ) -> Result<Self, String> {
        if position >= leaves.len() {
            return Err(format!(
                "cap-open witness: position {position} >= {} leaves",
                leaves.len()
            ));
        }
        let chosen = leaves[position];
        if chosen.len() != 7 {
            return Err("cap-open witness: leaf must carry 7 fields".into());
        }
        // GENUINE SUBMASK MEMBERSHIP (residual (a)): the chosen cap's facet must PERMIT the
        // effect-kind bit `eff_bit` over the FULL mask `maskOfLimbs(mask_lo, mask_hi)` — `(eff_bit &
        // full_mask) == eff_bit`, the kernel's `is_effect_permitted` for a single bit (`facet.rs:123`),
        // NOT the over-strict equality `mask_lo == eff_bit`. A BROAD honest cap (`EFFECT_ALL`, mask_lo =
        // 0xFFFF, mask_hi = 0xFFFF) PASSES — there is NO `mask_hi == 0` pin.
        let chosen_full_mask: u64 =
            chosen[3].as_u32() as u64 + (chosen[4].as_u32() as u64) * 65536;
        if (eff_bit as u64 & chosen_full_mask) != eff_bit as u64 {
            return Err(format!(
                "cap-open witness: chosen leaf full mask {chosen_full_mask} (mask_lo {}, mask_hi {}) \
                 does not PERMIT the effect-kind bit {eff_bit} (the facetEffGate submask membership bites)",
                chosen[3].as_u32(),
                chosen[4].as_u32()
            ));
        }
        // residual (a): NO tier pin — the effect-general cap-open appendix (`capOpenConstraintsEff`)
        // DECODES the tier off `auth_tag` rather than pinning Signature, so a cap of ANY tier builds.
        // Lay the depth-16 tree: level 0 = the leaf-digest layer over 2^16 slots, the chosen
        // leaf at `position`, all others the zero-leaf padding digest. We materialize ONLY the
        // path: at each level we need the sibling digest, which is the OTHER child of the
        // current node. For a sparse tree with a single non-padding leaf, every sibling subtree
        // is a uniform-padding subtree whose root is a known per-level constant.
        let zero_leaf = cap_leaf_digest(&[BabyBear::ZERO; 7]);
        // per-level padding subtree roots: pad[0] = zero leaf digest; pad[k+1] = node(pad,pad).
        let mut pad = [BabyBear::ZERO; CAP_OPEN_DEPTH + 1];
        pad[0] = zero_leaf;
        for k in 0..CAP_OPEN_DEPTH {
            pad[k + 1] = cap_node(pad[k], pad[k]);
        }
        let mut siblings = [BabyBear::ZERO; CAP_OPEN_DEPTH];
        let mut directions = [0u8; CAP_OPEN_DEPTH];
        let mut idx = position;
        let mut cur = cap_leaf_digest(&chosen);
        for lvl in 0..CAP_OPEN_DEPTH {
            let dir = (idx & 1) as u8; // 0 ⇒ cur is LEFT child, sibling on the RIGHT.
            // The sibling subtree at this level is uniform padding (single non-pad leaf).
            let sib = pad[lvl];
            siblings[lvl] = sib;
            directions[lvl] = dir;
            let (l, r) = cap_mix(cur, sib, dir);
            cur = cap_node(l, r);
            idx >>= 1;
        }
        let w = Self {
            leaf: chosen,
            siblings,
            directions,
            cap_root: cur,
            src: chosen[1],
            eff_bit: WRITE_MASK_LO,
        };
        debug_assert_eq!(w.recomposes(), w.cap_root, "cap-open witness must recompose");
        Ok(w)
    }

    /// Build a cap-open trace witness from the actor's REAL consumed capability — a 7-field
    /// [`crate::cap_root::CapLeaf`] plus the depth-16 `(sibling, direction)` membership path opened
    /// against the holder's pre-state `capability_root`. This is the prove-site bridge: the c-list
    /// opening the turn carries (`TurnReceipt::consumed_capabilities`, threaded through the SDK's
    /// `CapMembershipWitness`) and `CapOpenWitness` is the trace-column shape [`widen_to_cap_open`]
    /// fills. Both are field-for-field twins (same 7-field [`cap_leaf_digest`], same absorb-node
    /// fold via [`cap_node`]); this converts the dynamically-sized path to the fixed depth-16 arrays
    /// the appendix declares, RECOMPOSES the committed root from the leaf digest, and pins
    /// `src := leaf.target` so the `targetBindGate` holds.
    ///
    /// Fails closed when:
    ///   * the membership path is not exactly [`CAP_OPEN_DEPTH`] levels (the deployed depth);
    ///   * the leaf does not satisfy the FAITHFUL two-axis facet × tier the descriptor's gates pin
    ///     (`mask_lo == EFFECT_TRANSFER`, `mask_hi == 0`, `auth_tag == Signature`) — i.e. the
    ///     consumed cap does not actually confer the transfer authority the open asserts.
    pub fn from_membership(
        leaf: &crate::cap_root::CapLeaf,
        siblings: &[BabyBear],
        directions: &[u8],
    ) -> Result<Self, String> {
        // residual (a): the LIVE transfer/attenuate cap-open now routes the effect-GENERAL
        // descriptors (`transferCapOpenEffVmDescriptor2R24` / `attenuateCapOpenEffVmDescriptor2R24`),
        // whose `capOpenConstraintsEff 1` appendix DECODES the tier off `auth_tag` (no Signature
        // pin) and checks the genuine SUBMASK facet membership. So an honest cap of ANY tier
        // (None/Signature/…) and ANY broad mask that PERMITS Transfer proves — we drop the old
        // `auth_tag == Signature` pin and defer to the submask check in `from_membership_for`.
        Self::from_membership_for(leaf, siblings, directions, WRITE_MASK_LO)
    }

    /// **`from_membership_for` (THE FAN-OUT GENERAL CONSTRUCTOR, residual (a)).** Build a cap-open
    /// trace witness for an ARBITRARY effect-kind bit `eff_bit` (`EFFECT_<kind> = 1 << n`): the
    /// consumed cap's facet must permit THAT effect-kind. The general `facetEffGate` binds
    /// `leaf.mask_lo == eff_bit`, so we require `leaf.mask_lo == eff_bit` (NOT the constant
    /// EFFECT_TRANSFER) and `mask_hi == 0`. The TIER rides the DECODED `auth_tag` (the
    /// `SatisfiedEff` row carries no `authTagGate` constant pin), so any committed `auth_tag` is
    /// accepted here — the off-circuit AuthContext supplies a `provided` the decoded tier admits.
    /// `from_membership` is the `eff_bit := EFFECT_TRANSFER` instance.
    pub fn from_membership_for(
        leaf: &crate::cap_root::CapLeaf,
        siblings: &[BabyBear],
        directions: &[u8],
        eff_bit: u32,
    ) -> Result<Self, String> {
        if siblings.len() != CAP_OPEN_DEPTH || directions.len() != CAP_OPEN_DEPTH {
            return Err(format!(
                "cap-open from_membership: path depth ({} sib / {} dir) != deployed depth {CAP_OPEN_DEPTH}",
                siblings.len(),
                directions.len()
            ));
        }
        let leaf: [BabyBear; 7] = [
            leaf.slot_hash,
            leaf.target,
            leaf.auth_tag,
            leaf.mask_lo,
            leaf.mask_hi,
            leaf.expiry,
            leaf.breadstuff,
        ];
        // GENUINE SUBMASK MEMBERSHIP (residual (a)): the consumed cap's facet must PERMIT the
        // effect-kind bit `eff_bit` over the FULL mask `maskOfLimbs(mask_lo, mask_hi)` — `(eff_bit &
        // full_mask) == eff_bit`, the kernel's `is_effect_permitted` for a single bit, NOT the
        // over-strict equality `mask_lo == eff_bit`. A BROAD honest cap (`EFFECT_ALL`, mask_lo = 0xFFFF,
        // mask_hi = 0xFFFF) PASSES; a cap that does NOT carry bit `n` is refused. NO `mask_hi == 0` pin.
        let full_mask: u64 = leaf[3].as_u32() as u64 + (leaf[4].as_u32() as u64) * 65536;
        if (eff_bit as u64 & full_mask) != eff_bit as u64 {
            return Err(format!(
                "cap-open from_membership: leaf full mask {full_mask} (mask_lo {}, mask_hi {}) does not \
                 PERMIT effect-kind bit {eff_bit} (the consumed cap does not permit the turn's \
                 effect-kind — the facetEffGate submask bites)",
                leaf[3].as_u32(),
                leaf[4].as_u32()
            ));
        }
        let mut sib_arr = [BabyBear::ZERO; CAP_OPEN_DEPTH];
        let mut dir_arr = [0u8; CAP_OPEN_DEPTH];
        sib_arr.copy_from_slice(siblings);
        dir_arr.copy_from_slice(directions);
        // The committed root IS the recomposition of THIS path from the genuine leaf digest — the
        // value the rootPin gate binds. (A fabricated leaf / tampered sibling yields a different
        // root; the chip-lookup membership chain then opens a tree whose root the descriptor's
        // rootPin does not match its own seeded `cap_root` column — UNSAT in-circuit.)
        let mut cur = cap_leaf_digest(&leaf);
        for lvl in 0..CAP_OPEN_DEPTH {
            let (l, r) = cap_mix(cur, sib_arr[lvl], dir_arr[lvl]);
            cur = cap_node(l, r);
        }
        let w = Self {
            leaf,
            siblings: sib_arr,
            directions: dir_arr,
            cap_root: cur,
            src: leaf[1],
            eff_bit,
        };
        debug_assert_eq!(w.recomposes(), w.cap_root, "cap-open from_membership recompose");
        Ok(w)
    }
}

/// Fill the 59 cap-open columns at `base` for ONE row from `w` (Lean `CapOpenCols` layout):
///   * leaf field `i` at `base + i` (i = 0..6);
///   * `leafDigest = hash_many(&leaf)` at `base + 7`;
///   * level `lvl`: `sib` at `base + 8 + 3·lvl`, `dir` at `base + 9 + 3·lvl`,
///     `node = hash_many(&[FACT_MARK, left, right])` at `base + 10 + 3·lvl`;
///   * `capRoot` at `base + 56`, `src` at `base + 57`, `effBit` at `base + 58`.
///
/// The `effBit` column (residual (a)) carries the turn's ACTUAL effect-kind bit, pinned by the
/// descriptor's `effBitGate` to `EFFECT_TRANSFER (= WRITE_MASK_LO)` for this transfer cap-open;
/// the `facetEffGate` then binds `leaf.mask_lo == effBit` (the leaf's facet is bound to the
/// committed effect column, NOT a literal constant). The top node (`lvl = 15`) MUST equal
/// `w.cap_root` (asserted). Every digest is a genuine `hash_many`-absorb, so the auto-gathered
/// chip table carries a matching row for each of the 1 + 16 chip lookups.
pub fn fill_cap_open(row: &mut [BabyBear], base: usize, w: &CapOpenWitness) {
    for (i, &f) in w.leaf.iter().enumerate() {
        row[base + i] = f;
    }
    let leaf_digest = cap_leaf_digest(&w.leaf);
    row[base + 7] = leaf_digest;
    let mut cur = leaf_digest;
    for lvl in 0..CAP_OPEN_DEPTH {
        let sib = w.siblings[lvl];
        let dir = w.directions[lvl];
        let (l, r) = cap_mix(cur, sib, dir);
        let node = cap_node(l, r);
        row[base + 8 + 3 * lvl] = sib;
        row[base + 9 + 3 * lvl] = BabyBear::new(dir as u32);
        row[base + 10 + 3 * lvl] = node;
        cur = node;
    }
    debug_assert_eq!(cur, w.cap_root, "cap-open fill: top node must equal cap_root");
    row[base + 56] = w.cap_root;
    row[base + 57] = w.src;
    // residual (a): the committed effect-bit column. Carries the turn's ACTUAL effect-kind bit
    // (`w.eff_bit` — EFFECT_TRANSFER for transfer/attenuate, each fan-out leg its own `1<<n`); the
    // `effBitGateFor` pins it.
    row[base + 58] = BabyBear::new(w.eff_bit);
    // residual (a) — GENUINE MEMBERSHIP: the 32-bit decomposition of the FULL effect mask
    // `maskOfLimbs(mask_lo, mask_hi) = mask_lo + mask_hi·65536` (leaf fields 3 + 4) at `base + 59 + i`.
    // The `maskBitBoolGate` booleans each bit, `maskReconGate` binds `full_mask = Σ bitᵢ·2ⁱ`, and
    // `selectedBitGate n` gates bit `n` (where `eff_bit = 1<<n`) set — the genuine `(eff_bit &
    // full_mask) == eff_bit` SUBMASK, NOT the over-strict equality `mask_lo == eff_bit`. A BROAD honest
    // cap (`EFFECT_ALL`, mask_lo = 0xFFFF, mask_hi = 0xFFFF) decomposes with bit `n` set, so it PERMITS
    // the effect — and no `mask_hi == 0` pin rejects it.
    let full_mask: u64 = w.leaf[3].as_u32() as u64 + (w.leaf[4].as_u32() as u64) * 65536;
    for i in 0..CAP_OPEN_MASK_BITS {
        row[base + 59 + i] = BabyBear::new(((full_mask >> i) & 1) as u32);
    }
}

/// Recompute one rotated block's chained `wireCommitR` digests + `state_commit` from the limbs
/// ALREADY present in the row (cols `base..base+NUM_PRE_LIMBS` + the iroot at `base+B_IROOT`).
/// Byte-identical to [`fill_block`]'s chain, but reads the limbs in place rather than from a
/// witness — used after an in-place limb PATCH (e.g. a nonce-passthrough fixup) so the chain
/// carriers + state_commit stay consistent with the patched limbs.
fn recompute_block_commit(row: &mut [BabyBear], base: usize) {
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
    row[base + B_STATE_COMMIT] = hash_many(&[d, row[base + B_IROOT]]);
}

/// Test helper: recompute EVERY row's AFTER-block chained commitment in place (after an in-place
/// limb patch, e.g. forging the after `nullifier_root` to test the grow-gate tooth). Exposed for
/// the rotation-flip adversarial tests; not used on any honest path.
#[doc(hidden)]
pub fn recompute_after_blocks_for_test(trace: &mut [Vec<BabyBear>]) {
    for row in trace.iter_mut() {
        recompute_block_commit(row, AFTER_BASE);
    }
}

/// Recompute one v1 state block's STATE_COMMIT intermediates + digest from the block's state
/// columns, byte-identical to the descriptor's STATE_COMMIT poseidon lookups (arity-4
/// `hash_many` of `[s0..s3]`, `[s4..s7]`, `[s8..s11]` → three intermediates, then arity-4
/// `hash_many([i1, i2, i3, 0])` → the STATE_COMMIT). `state_base` is the block's column base
/// (54 for before, 76 for after); `i1/i2/i3` are the AUX intermediate carriers the lookups bind.
fn recompute_v1_state_commit(
    row: &mut [BabyBear],
    state_base: usize,
    i1: usize,
    i2: usize,
    i3: usize,
) {
    use super::columns::state;
    let s = state_base;
    row[i1] = hash_many(&[row[s], row[s + 1], row[s + 2], row[s + 3]]);
    row[i2] = hash_many(&[row[s + 4], row[s + 5], row[s + 6], row[s + 7]]);
    row[i3] = hash_many(&[row[s + 8], row[s + 9], row[s + 10], row[s + 11]]);
    row[s + state::STATE_COMMIT] =
        hash_many(&[row[i1], row[i2], row[i3], BabyBear::ZERO]);
}

/// Make a generated rotated AttenuateCapability trace satisfy the `attenuateV3` base
/// constraints' phase-B bindings the bare `generate_rotated_effect_vm_trace` output does not
/// carry. THE WITNESS WIRINGS (column FILLS only — ZERO hand-authored constraint semantics):
///
///   * **nonce PASSTHROUGH (frozen)** — the attenuate descriptor pins `after.nonce ==
///     before.nonce` (an UNCONDITIONAL gate) AND the cross-row continuity transition
///     `next.before == local.after`. `generate_effect_vm_trace` TICKS the nonce on every effect
///     row (so each row's after-nonce, and the next row's before-nonce, climbs); attenuate's
///     audited shape is a nonce PASSTHROUGH (the cap-root advance is the state move). So we
///     FREEZE the nonce to row 0's before-nonce across BOTH state blocks on EVERY row — making
///     `after.nonce == before.nonce` hold and the per-row blocks identical so continuity holds.
///   * **cap-root advance binding** — the descriptor pins `after.cap_root == param2`; the
///     generator leaves param2 at 0, so we wire it to the row's own advanced after-cap-root.
///
/// After freezing the nonce we REBUILD every dependent commitment so the whole trace stays
/// internally genuine: the v1 BEFORE + AFTER STATE_COMMIT chains (the descriptor's poseidon
/// lookups), the before-state-commit cross-row continuity carrier, and the rotated BEFORE +
/// AFTER blocks' welded nonce limb + chained `wireCommitR` state_commit. Then the four rotated
/// PI carriers are re-read from the rebuilt trace. Returns the corrected 38-PI vector. Widen
/// the patched 315-wide trace to the cap-open shape with [`widen_to_cap_open`].
pub fn patch_attenuate_base_for_cap_open(
    trace: &mut [Vec<BabyBear>],
    pis: &[BabyBear],
) -> Result<Vec<BabyBear>, String> {
    use super::columns::state;
    if trace.is_empty() {
        return Err("patch_attenuate_base: empty trace".into());
    }
    if trace[0].len() != ROT_WIDTH {
        return Err(format!(
            "patch_attenuate_base: trace width {} != {ROT_WIDTH}",
            trace[0].len()
        ));
    }
    if pis.len() < ROT_PI_COUNT {
        return Err(format!(
            "patch_attenuate_base: PI vector {} shorter than {ROT_PI_COUNT}",
            pis.len()
        ));
    }
    let sb = STATE_BEFORE_BASE; // 54
    let sa = STATE_AFTER_BASE; // 76
    let before_nonce_col = sb + state::NONCE; // 56
    let after_nonce_col = sa + state::NONCE; // 78
    let after_cap_root_col = sa + state::CAP_ROOT; // 87
    let param2_col = super::columns::PARAM_BASE + 2; // 70
    // The AUX STATE_COMMIT intermediate carriers the v1 lookups bind. The generator wrote the
    // AFTER-block intermediates at AUX_BASE+8..10 (`aux_off::STATE_INTER1..3`); the descriptor's
    // BEFORE-block STATE_COMMIT (col `sb + STATE_COMMIT`) carries no in-descriptor lookup (it is
    // only consumed by the cross-row continuity), so we recompute it consistently from the
    // (frozen) before-state and reuse the same arity-4 chain shape via scratch intermediates
    // that we DO NOT need to land on bound columns — but to stay byte-identical we land the
    // after-block intermediates on their bound carriers.
    let a_i1 = super::columns::AUX_BASE + 8; // 98
    let a_i2 = super::columns::AUX_BASE + 9; // 99
    let a_i3 = super::columns::AUX_BASE + 10; // 100

    // The frozen nonce: row 0's before-nonce (the turn's pre-state nonce — attenuate does not
    // tick it).
    let frozen_nonce = trace[0][before_nonce_col];

    for row in trace.iter_mut() {
        // (1) FREEZE the nonce in BOTH v1 state blocks + the rotated block r1 welds.
        row[before_nonce_col] = frozen_nonce;
        row[after_nonce_col] = frozen_nonce;
        row[BEFORE_BASE + 2] = frozen_nonce; // rotated before-block r1 (nonce) weld
        row[AFTER_BASE + 2] = frozen_nonce; // rotated after-block r1 (nonce) weld
        // (2) cap-root advance binding: param2 := after.cap_root.
        row[param2_col] = row[after_cap_root_col];
        // (3) rebuild the v1 AFTER STATE_COMMIT chain (the descriptor's bound poseidon lookups).
        recompute_v1_state_commit(row, sa, a_i1, a_i2, a_i3);
        // (4) rebuild the v1 BEFORE STATE_COMMIT (consumed by cross-row continuity). We compute
        //     it with the SAME arity-4 chain into scratch and land only the digest column; the
        //     before-block intermediates are not bound to any in-descriptor lookup.
        let bi1 = hash_many(&[row[sb], row[sb + 1], row[sb + 2], row[sb + 3]]);
        let bi2 = hash_many(&[row[sb + 4], row[sb + 5], row[sb + 6], row[sb + 7]]);
        let bi3 = hash_many(&[row[sb + 8], row[sb + 9], row[sb + 10], row[sb + 11]]);
        row[sb + state::STATE_COMMIT] = hash_many(&[bi1, bi2, bi3, BabyBear::ZERO]);
        // (5) rebuild both rotated blocks' chained `wireCommitR` digests over the frozen limbs.
        recompute_block_commit(row, BEFORE_BASE);
        recompute_block_commit(row, AFTER_BASE);
    }

    // The four rotated PI carriers, re-read from the rebuilt trace (same columns the descriptor's
    // pin constraints bind: 218 / 261 / 259 / 310).
    let r0 = &trace[0];
    let last = &trace[trace.len() - 1];
    let mut dpis: Vec<BabyBear> = pis[..ROT_PI_COUNT].to_vec();
    dpis[34] = r0[BEFORE_BASE + B_STATE_COMMIT]; // rotated OLD commit
    dpis[35] = last[AFTER_BASE + B_STATE_COMMIT]; // rotated NEW commit
    dpis[36] = last[AFTER_BASE + B_COMMITTED_HEIGHT]; // committed height (unchanged)
    dpis[37] = last[CAVEAT_BASE + C_SPAN - 1]; // caveat commit (unchanged)
    Ok(dpis)
}

/// Widen an already-built rotated base trace (`ROT_WIDTH`-wide) to the `CAP_OPEN_WIDTH`-wide
/// cap-open trace, filling the 59 cap-open columns on EVERY row uniformly with `w` (so the every-row base
/// gates — dir-bool, rootPin, targetBind, transferFacet/facetHi/authTag — hold on every row).
/// The base trace's own 315 columns + 38 PIs are unchanged; the cap-open appendix is purely
/// additive. The base trace MUST be a 315-wide rotated trace the base `attenuateV3`
/// constraints already accept (e.g. from [`generate_rotated_effect_vm_trace`] on an
/// AttenuateCapability turn).
pub fn widen_to_cap_open(trace: &mut [Vec<BabyBear>], w: &CapOpenWitness) -> Result<(), String> {
    if trace.is_empty() {
        return Err("cap-open widen: empty base trace".into());
    }
    if trace[0].len() != ROT_WIDTH {
        return Err(format!(
            "cap-open widen: base trace width {} != {ROT_WIDTH}",
            trace[0].len()
        ));
    }
    if w.recomposes() != w.cap_root {
        return Err("cap-open widen: witness does not recompose its cap_root".into());
    }
    for row in trace.iter_mut() {
        row.resize(CAP_OPEN_WIDTH, BabyBear::ZERO);
        fill_cap_open(row, CAP_OPEN_BASE, w);
    }
    Ok(())
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
        // The cap-open members (the LIVE `transferCapOpenEffV3`/`attenuateCapOpenEffV3` + 6 fan-out) are SELF-VERIFY /
        // cap-PRESENCE-routed descriptors: they carry the 59-column cap-membership appendix and are
        // NOT reached by the effect→descriptor resolvers (no live effect selects them by kind; the
        // rotated generator widens a base trace into them explicitly via `widen_to_cap_open` when a
        // consumed-cap witness is present). So they are excluded from the resolver-cohort
        // completeness audit — the resolvers must still cover EXACTLY the 36 rotated cohort members.
        let registry: BTreeSet<&str> = V3_STAGED_REGISTRY_TSV
            .lines()
            .filter_map(|l| l.split('\t').next())
            // exclude ALL cap-open authority members (the Signature-pinned `…CapOpenVmDescriptor2R24`
            // AND the live effect-general `…CapOpenEffVmDescriptor2R24`): they are self-verify /
            // cap-PRESENCE-routed, not reached by the effect→descriptor resolvers.
            .filter(|s| {
                !s.is_empty()
                    && !s.ends_with("CapOpenVmDescriptor2R24")
                    && !s.ends_with("CapOpenEffVmDescriptor2R24")
            })
            .collect();
        assert_eq!(
            registry.len(),
            36,
            "the rotated resolver cohort has 36 members (cap-open is self-verify-only)"
        );

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
