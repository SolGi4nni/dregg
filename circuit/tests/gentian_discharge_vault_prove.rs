//! # GENTIAN discharge/vault (tags 18/19) — REAL-STARK EXERCISE over the Lean-emitted STAGED
//! satisfaction descriptors (ADDITIVE — a new test file only; no deployed descriptor, registry, VK,
//! or routing is touched).
//!
//! The escrow (tag 17) weld is the done template: `settleEscrowSatVmDescriptor2R24` emitted into the
//! staged registry + a genuine producer + `gentian_carrier_floor_prove` real STARKs. This file makes
//! tags 18/19 match that doneness MINUS the registry row: it parses the Lean-emitted v12
//! descriptors DIRECTLY from the checked-in fixtures (`tests/fixtures/{discharge,vault}-sat-v3-staged.json`,
//! the byte output of `metatheory/EmitDischargeVaultSat.lean` over
//! `Dregg2.Deos.{DischargeSatDescriptor,VaultSatDescriptor}`), welds the corresponding floor-decode
//! gates (`discharge_weld::discharge_floor_gates` / `vault_weld::vault_floor_gates`) on top — the
//! exact gentian pattern — and drives real `--release` STARKs through the genuine rotated
//! settle-carrier producer + the EXPORTED production aux-fills
//! (`fill_discharge_aux` / `fill_vault_aux`).
//!
//! ## What this file establishes (empirical, real STARKs)
//!
//!  * the DRIFT TOOTH: the Lean-emitted descriptors carry EXACTLY the Rust builders' satisfaction
//!    gates (`discharge_satisfaction_gates(0,1,2)` / `vault_satisfaction_gates(0,1)`), byte-for-byte,
//!    at the v12 geometry (`trace_width` derived through the canonical constants on BOTH sides);
//!  * an HONEST discharge settle (cursor +period, total +amount, due ≤ clock) PROVES + VERIFIES;
//!  * an HONEST vault deposit (fair mint, `Ta·m ≤ Sa·d`) PROVES + VERIFIES;
//!  * the SIX gate-mechanic forge arms are REFUSED: EARLY discharge (clock < due) / CURSOR-NOT-ADVANCED
//!    (replay) / WRONG-AMOUNT; ZERO-MINT inflation (ERC-4626) / OVER-MINT dilution / NO-DEPOSIT;
//!  * the THREE G5 FREE-PARAM-BIND forge arms are REFUSED: a FORGED PERIOD / FORGED AMOUNT (a producer
//!    scalar filled to satisfy the gate but ≠ the committed caveat term) and a FABRICATED CLOCK (a
//!    scalar ≠ the published block height) — the binds close the last free-param soundness hole.
//!
//! ## STAGED — what still rides the BIG-BANG regen (the named riders)
//!
//!  * the `rotation-v3-staged-registry.tsv` rows for `dischargeSatVmDescriptor2R24` /
//!    `vaultSatVmDescriptor2R24` (+ the `EmitRotationV3.lean` emit lines) and the drift-gate FP pins
//!    in `effect_vm_descriptors.rs`;
//!  * the caveat-manifest COVERAGE tie (routing a declared-18/19 turn through these descriptors,
//!    `rotated_descriptor_name_for_declared_*`);
//!  * the welded VK commit + live admission (the descriptor/registry big-bang). NOTE: the
//!    free-param BINDING itself is now CLOSED here (G5) — `discharge_weld::discharge_floor_gates`
//!    carries the slot-selected param bind (`period`/`amount` → the committed caveat params, PI 45)
//!    and the clock bind (`clock` → the published block height, PI 44), and the three forge arms below
//!    prove it bites; only the committed VK for the welded descriptor still rides the big-bang.
//!
//! SLOW (full batch STARKs). Run:
//!   `cargo test -p dregg-circuit --test gentian_discharge_vault_prove --release -- --nocapture \
//!    --test-threads=1`

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::CellState;
use dregg_circuit::effect_vm::columns::rotation::caveat as cav;
use dregg_circuit::effect_vm::discharge_weld::{
    DISCHARGE_SEL_COL, DUE_BITS, FLOOR_DISCHARGE_COL, discharge_floor_gates,
    discharge_satisfaction_gates, due_bit_col, fill_discharge_aux,
};
use dregg_circuit::effect_vm::pi::{
    SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION, SLOT_CAVEAT_TAG_VAULT_DEPOSIT,
};
use dregg_circuit::effect_vm::satisfaction_weld::before_field_col;
use dregg_circuit::effect_vm::trace_rotated::{
    GRAD_ROT_WIDTH, RotatedBlockWitness, RotatedCaveatEntry, RotatedCaveatManifest,
    generate_rotated_settle_escrow_trace_forged,
};
use dregg_circuit::effect_vm::vault_weld::{
    CARRY_BITS, FLOOR_VAULT_COL, LIMB_BITS, VAULT_SEL_COL, fill_vault_aux, vault_floor_gates,
    vault_satisfaction_gates,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint};
use dregg_turn::rotation_witness as rw;

// The Lean-emitted v12 staged descriptors (see the module header; regen-riders NAMED there).
const DISCHARGE_JSON: &str = include_str!("fixtures/discharge-sat-v3-staged.json");
const VAULT_JSON: &str = include_str!("fixtures/vault-sat-v3-staged.json");

// Slots: discharge cur/tot/due = fields 0/1/2; vault asset/share = fields 0/1 (the emitted defs).
const CUR: usize = 0;
const TOT: usize = 1;
const DUE: usize = 2;
const ASSET: usize = 0;
const SHARE: usize = 1;

// The honest discharge schedule: cursor 1000→1100 (+period 100), total 0→50 (+amount 50),
// committed due block 1000, clock 1000 (due ≤ clock).
const PERIOD: u32 = 100;
const AMOUNT: u32 = 50;
const DUE_BLOCK: u32 = 1000;
const CLOCK: u32 = 1000;

// ----------------------------------------------------------------------------------------------------
// Fixtures (residue-free producer cell + rotation witnesses) — the gentian pattern.
// ----------------------------------------------------------------------------------------------------

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

fn producer_cell(balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("pre-iroot limbs")
}

/// The carrier inputs. `due_block` seeds `initial_state.fields[DUE]` (frozen through the settle —
/// the committed due block both blocks read); zero for the vault arms. `committed_height` is the
/// cell's committed block height — it rides pre-limb 31 → the AFTER-block `committed_height` column
/// (PI 44), which the G5 clock-bind pins `CLOCK_COL` to (the REAL published clock).
fn carrier_inputs(
    due_block: u32,
    committed_height: u32,
) -> (CellState, RotatedBlockWitness, RotatedBlockWitness) {
    let balance: i64 = 100_000;
    let mut initial_state = CellState::new(balance as u64, 0);
    initial_state.fields[DUE] = BabyBear::new(due_block);
    let mut cell = producer_cell(balance);
    cell.state.set_committed_height(committed_height as u64);
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let w = rw::produce(
        &cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        &Default::default(),
    );
    (initial_state, bridge(&w), bridge(&w))
}

/// A capacity-declaring caveat manifest: slot 0 type tag = `tag` (18 or 19), bound into the
/// caveat-commit chain (PI 45) like the escrow manifest in the gentian escrow exercise. `params`
/// carries the DECLARED capacity terms (discharge: `[period, amount, 0, 0]`) — the committed terms
/// the G5 bind gates pin the producer `PERIOD_COL`/`AMOUNT_COL` scalars to.
fn capacity_manifest_with_params(tag: u32, params: [u32; 4]) -> RotatedCaveatManifest {
    let mut m = RotatedCaveatManifest::default();
    m.entries[0] = RotatedCaveatEntry {
        type_tag: tag,
        domain_tag: cav::DOMAIN_REGISTERS,
        key: BabyBear::ZERO,
        params: params.map(BabyBear::new),
    };
    m
}

/// The zero-param manifest (vault: the no-dilution gate reads state directly, no declared scalars).
fn capacity_manifest(tag: u32) -> RotatedCaveatManifest {
    capacity_manifest_with_params(tag, [0; 4])
}

fn mem() -> MemBoundaryWitness {
    MemBoundaryWitness::default()
}
type Heaps = Vec<Vec<dregg_circuit::heap_root::HeapLeaf>>;

/// Does the descriptor accept this (trace, dpis)? `prove` may panic/refuse on an unsatisfiable
/// witness; `verify` is the real acceptance. Returns `true` iff a verifying proof exists.
fn accepts(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], dpis: &[BabyBear]) -> bool {
    let heaps: Heaps = vec![];
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_vm_descriptor2(desc, trace, dpis, &mem(), &heaps)
    })) {
        Ok(Ok(proof)) => verify_vm_descriptor2(desc, &proof, dpis).is_ok(),
        Ok(Err(_)) | Err(_) => false,
    }
}

/// Extract the selector-gated gate bodies (`mul(var sel_col, _)`) from a constraint list.
fn sel_gated_bodies(
    constraints: &[dregg_circuit::descriptor_ir2::VmConstraint2],
) -> Vec<&LeanExpr> {
    use dregg_circuit::descriptor_ir2::VmConstraint2;
    constraints
        .iter()
        .filter_map(|c| match c {
            VmConstraint2::Base(VmConstraint::Gate(body)) => match body {
                LeanExpr::Mul(l, _) if **l == LeanExpr::Var(DISCHARGE_SEL_COL) => Some(body),
                _ => None,
            },
            _ => None,
        })
        .collect()
}

// ----------------------------------------------------------------------------------------------------
// The welded carrier descriptors: parse the Lean-emitted staged descriptor, weld the floor gates.
// ----------------------------------------------------------------------------------------------------

fn discharge_descriptor() -> EffectVmDescriptor2 {
    let mut desc = parse_vm_descriptor2(DISCHARGE_JSON).expect("Lean-emitted discharge descriptor");
    assert_eq!(
        desc.public_input_count, 47,
        "rotated 46 + the selector slot"
    );
    assert_eq!(
        desc.trace_width,
        due_bit_col(DUE_BITS - 1) + 1,
        "the Lean-emitted width matches the Rust v12 aux-column derivation (canonical constants)"
    );
    desc.name = format!("{}-gentian-demo", desc.name);
    desc.constraints.extend(discharge_floor_gates()); // the floor weld adds NO public input
    desc
}

fn vault_descriptor() -> EffectVmDescriptor2 {
    let mut desc = parse_vm_descriptor2(VAULT_JSON).expect("Lean-emitted vault descriptor");
    assert_eq!(
        desc.public_input_count, 47,
        "rotated 46 + the selector slot"
    );
    assert_eq!(
        desc.trace_width,
        GRAD_ROT_WIDTH + 16 + 34 + 24 * LIMB_BITS + 4 * CARRY_BITS,
        "the Lean-emitted width matches the Rust v12 aux-column derivation (canonical constants)"
    );
    desc.name = format!("{}-gentian-demo", desc.name);
    desc.constraints.extend(vault_floor_gates()); // the floor weld adds NO public input
    desc
}

/// The full-control discharge settle-carrier builder — the DECLARED (committed manifest) terms +
/// published height are separated from the PRODUCER-FILLED scalars so the G5 forge arms can drive
/// them apart. Legs CUR/TOT flip `before → after`; the committed due block rides frozen slot DUE;
/// `declared_*`/`published_height` land in the caveat params + committed-height column (the committed
/// carriers), `fill_*` in the producer scalar columns (`PERIOD_COL`/`AMOUNT_COL`/`CLOCK_COL`).
#[allow(clippy::too_many_arguments)]
fn discharge_trace_ex(
    desc: &EffectVmDescriptor2,
    before: (u32, u32),
    after: (u32, u32),
    declared_period: u32,
    declared_amount: u32,
    published_height: u32,
    fill_period: u32,
    fill_amount: u32,
    fill_clock: u32,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let (st, bw, aw) = carrier_inputs(DUE_BLOCK, published_height);
    let m = capacity_manifest_with_params(
        SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION,
        [declared_period, declared_amount, 0, 0],
    );
    let (mut trace, dpis) =
        generate_rotated_settle_escrow_trace_forged(&st, &bw, &aw, &m, CUR, TOT, before, after)
            .expect("the discharge settle carrier must generate");
    assert_eq!(dpis.len(), 47);
    fill_discharge_aux(
        &mut trace,
        desc.trace_width,
        DUE,
        fill_period,
        fill_amount,
        fill_clock,
    );
    (trace, dpis)
}

/// The HONEST-terms discharge trace: the declared manifest terms EQUAL the filled scalars and the
/// published height EQUALS the filled clock — the baseline for the honest / due-ness / cursor /
/// wrong-amount arms (where `before`/`after`/`clock` vary but the terms track the fill).
fn discharge_trace(
    desc: &EffectVmDescriptor2,
    before: (u32, u32),
    after: (u32, u32),
    clock: u32,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    discharge_trace_ex(
        desc, before, after, PERIOD, AMOUNT, /*published_height*/ clock, PERIOD, AMOUNT,
        /*fill_clock*/ clock,
    )
}

/// Build a vault deposit-carrier trace: legs ASSET/SHARE flip `before → after`, the exported
/// production aux-fill fills the limb/product/borrow/range columns.
fn vault_trace(
    desc: &EffectVmDescriptor2,
    before: (u32, u32),
    after: (u32, u32),
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let (st, bw, aw) = carrier_inputs(0, 0);
    let m = capacity_manifest(SLOT_CAVEAT_TAG_VAULT_DEPOSIT);
    let (mut trace, dpis) =
        generate_rotated_settle_escrow_trace_forged(&st, &bw, &aw, &m, ASSET, SHARE, before, after)
            .expect("the vault deposit carrier must generate");
    assert_eq!(dpis.len(), 47);
    fill_vault_aux(&mut trace, desc.trace_width, ASSET, SHARE);
    (trace, dpis)
}

// ====================================================================================================
// DRIFT TEETH (fast, no STARK): the Lean-emitted descriptors carry EXACTLY the Rust builders' gates.
// ====================================================================================================

#[test]
fn lean_emitted_discharge_descriptor_matches_rust_builders() {
    let desc = parse_vm_descriptor2(DISCHARGE_JSON).expect("parses");
    let emitted = sel_gated_bodies(&desc.constraints);
    let built = discharge_satisfaction_gates(CUR, TOT, DUE);
    let built_bodies = sel_gated_bodies(&built);
    assert_eq!(
        built_bodies.len(),
        3 + 2 * DUE_BITS + 2,
        "3 relation gates + two 28-bit booleanity blocks + two assemblies"
    );
    assert_eq!(
        emitted, built_bodies,
        "the Lean-emitted discharge descriptor carries the Rust builders' gate bodies byte-for-byte \
         (offsets derived through the canonical v12 constants on BOTH sides)"
    );
}

#[test]
fn lean_emitted_vault_descriptor_matches_rust_builders() {
    let desc = parse_vm_descriptor2(VAULT_JSON).expect("parses");
    // VAULT_SEL_COL == DISCHARGE_SEL_COL (the shared free param slot) — one extractor serves both.
    assert_eq!(VAULT_SEL_COL, DISCHARGE_SEL_COL);
    let emitted = sel_gated_bodies(&desc.constraints);
    let built = vault_satisfaction_gates(ASSET, SHARE);
    let built_bodies = sel_gated_bodies(&built);
    assert_eq!(
        built_bodies.len(),
        6 + 8 + 9 + (24 * LIMB_BITS + 4 * CARRY_BITS) + 28,
        "6 core + 8 product + 9 borrow + one bool per bit + one assembly per spec"
    );
    assert_eq!(
        emitted, built_bodies,
        "the Lean-emitted vault descriptor carries the Rust builders' gate bodies byte-for-byte"
    );
}

// ====================================================================================================
// POSITIVE CONTROL 1: the HONEST discharge settle PROVES + VERIFIES (real STARK) — cursor +period,
// total +amount, due (1000) ≤ clock (1000), discharge declared, selector forced on the settle row.
// ====================================================================================================
#[test]
fn honest_discharge_settle_proves_and_verifies() {
    let desc = discharge_descriptor();
    let (trace, dpis) = discharge_trace(&desc, (1000, 0), (1100, 50), CLOCK);
    assert_eq!(
        trace[0][FLOOR_DISCHARGE_COL],
        BabyBear::ONE,
        "discharge declared ⟹ floor 1"
    );
    assert_eq!(
        trace[0][DISCHARGE_SEL_COL],
        BabyBear::ONE,
        "generator selector ON on the settle row"
    );
    assert_eq!(
        trace[0][before_field_col(DUE)],
        BabyBear::new(DUE_BLOCK),
        "the committed due block rides the frozen field slot"
    );
    assert!(trace.len() > 1, "a real settle trace has padding rows");
    assert!(
        accepts(&desc, &trace, &dpis),
        "the HONEST discharge settle MUST prove + verify against the Lean-emitted descriptor"
    );
    eprintln!("DISCHARGE (honest settle): PROVED + VERIFIED.");
}

// ====================================================================================================
// TOOTH D1 — an EARLY discharge (clock 999 < committed due 1000) is REFUSED: the wrapped difference
// has no DUE_BITS decomposition, the range-assembly gate bites.
// ====================================================================================================
#[test]
fn early_discharge_refused() {
    let desc = discharge_descriptor();
    let (trace, dpis) = discharge_trace(&desc, (1000, 0), (1100, 50), /*clock*/ 999);
    assert!(
        !accepts(&desc, &trace, &dpis),
        "an EARLY discharge (clock < due) MUST be refused"
    );
    eprintln!("DISCHARGE (early, clock 999 < due 1000): REFUSED.");
}

// ====================================================================================================
// TOOTH D2 — a REPLAY leaving the one-shot cursor unadvanced (no +period) is REFUSED: the cursor
// gate bites.
// ====================================================================================================
#[test]
fn cursor_not_advanced_refused() {
    let desc = discharge_descriptor();
    let (trace, dpis) = discharge_trace(&desc, (1000, 0), (/*after_cur*/ 1000, 50), CLOCK);
    assert!(
        !accepts(&desc, &trace, &dpis),
        "a non-advanced cursor MUST be refused"
    );
    eprintln!("DISCHARGE (cursor not advanced): REFUSED.");
}

// ====================================================================================================
// TOOTH D3 — a WRONG-AMOUNT discharge (total advanced by 9999 ≠ amount 50) is REFUSED: the total
// gate bites.
// ====================================================================================================
#[test]
fn wrong_amount_discharge_refused() {
    let desc = discharge_descriptor();
    let (trace, dpis) = discharge_trace(&desc, (1000, 0), (1100, /*after_tot*/ 9999), CLOCK);
    assert!(
        !accepts(&desc, &trace, &dpis),
        "a wrong-amount discharge MUST be refused"
    );
    eprintln!("DISCHARGE (wrong amount): REFUSED.");
}

// ====================================================================================================
// TOOTH D4 (G5 FREE-PARAM BIND) — a FORGED PERIOD is REFUSED. The declared caveat period is 100, but
// the forger discharges by 999: advance the cursor by 999 AND fill PERIOD_COL = 999 so the SATISFACTION
// cursor gate still vanishes. Without the bind this proves (the period was a free param); WITH the bind,
// the slot-selected gate bit·(committed 100 − 999) bites → UNSAT. This is what makes the bind real.
// ====================================================================================================
#[test]
fn forged_period_discharge_refused() {
    let desc = discharge_descriptor();
    let (trace, dpis) = discharge_trace_ex(
        &desc,
        (1000, 0),
        (/*after_cur*/ 1999, 50), // advance by the FORGED period 999
        /*declared_period*/ 100,
        /*declared_amount*/ AMOUNT,
        /*published_height*/ CLOCK,
        /*fill_period*/ 999, // satisfaction cursor gate now vanishes...
        /*fill_amount*/ AMOUNT,
        /*fill_clock*/ CLOCK,
    );
    assert!(
        !accepts(&desc, &trace, &dpis),
        "a forged period (scalar ≠ committed caveat term) MUST be refused by the bind gate"
    );
    eprintln!("DISCHARGE (forged period 999 ≠ committed 100): REFUSED.");
}

// ====================================================================================================
// TOOTH D5 (G5 FREE-PARAM BIND) — a FORGED AMOUNT is REFUSED. Declared amount 50; the forger discharges
// 9999: advance the total by 9999 AND fill AMOUNT_COL = 9999 so the satisfaction total gate vanishes —
// the bind gate bit·(committed 50 − 9999) bites → UNSAT.
// ====================================================================================================
#[test]
fn forged_amount_discharge_refused() {
    let desc = discharge_descriptor();
    let (trace, dpis) = discharge_trace_ex(
        &desc,
        (1000, 0),
        (1100, /*after_tot*/ 9999),
        /*declared_period*/ PERIOD,
        /*declared_amount*/ 50,
        /*published_height*/ CLOCK,
        /*fill_period*/ PERIOD,
        /*fill_amount*/ 9999, // satisfaction total gate now vanishes...
        /*fill_clock*/ CLOCK,
    );
    assert!(
        !accepts(&desc, &trace, &dpis),
        "a forged amount (scalar ≠ committed caveat term) MUST be refused by the bind gate"
    );
    eprintln!("DISCHARGE (forged amount 9999 ≠ committed 50): REFUSED.");
}

// ====================================================================================================
// TOOTH D6 (G5 FREE-PARAM BIND) — a FABRICATED CLOCK is REFUSED. The published block height is 999 (an
// obligation due at 1000 is genuinely NOT yet due). The forger fabricates CLOCK_COL = 1000 to pass the
// due-ness range gadget (1000 ≥ 1000) — but the clock-bind sel·(CLOCK_COL 1000 − published 999) bites
// → UNSAT. Without the bind, the forger claims due-ness at an invented clock.
// ====================================================================================================
#[test]
fn fabricated_clock_discharge_refused() {
    let desc = discharge_descriptor();
    let (trace, dpis) = discharge_trace_ex(
        &desc,
        (1000, 0),
        (1100, 50),
        /*declared_period*/ PERIOD,
        /*declared_amount*/ AMOUNT,
        /*published_height*/
        999, // the REAL chain height (obligation due 1000 is NOT due yet)
        /*fill_period*/ PERIOD,
        /*fill_amount*/ AMOUNT,
        /*fill_clock*/ 1000, // fabricated clock to fake due-ness
    );
    assert!(
        !accepts(&desc, &trace, &dpis),
        "a fabricated clock (scalar ≠ published block height) MUST be refused by the clock-bind gate"
    );
    eprintln!("DISCHARGE (fabricated clock 1000 ≠ published 999): REFUSED.");
}

// ====================================================================================================
// POSITIVE CONTROL 2: the HONEST vault deposit PROVES + VERIFIES (real STARK) — established vault
// Ta=2, Sa=4; deposit d=10, m=20: fair (2·20 = 4·10), vault declared, selector forced.
// ====================================================================================================
#[test]
fn honest_vault_deposit_proves_and_verifies() {
    let desc = vault_descriptor();
    let (trace, dpis) = vault_trace(&desc, (2, 4), (12, 24));
    assert_eq!(
        trace[0][FLOOR_VAULT_COL],
        BabyBear::ONE,
        "vault declared ⟹ floor 1"
    );
    assert_eq!(
        trace[0][VAULT_SEL_COL],
        BabyBear::ONE,
        "generator selector ON on the settle row"
    );
    assert!(
        accepts(&desc, &trace, &dpis),
        "the HONEST fair-mint vault deposit MUST prove + verify against the Lean-emitted descriptor"
    );
    eprintln!("VAULT (honest fair-mint deposit): PROVED + VERIFIED.");
}

// ====================================================================================================
// TOOTH V1 — the ZERO-MINT inflation attack (ERC-4626 first-depositor: positive deposit, zero
// shares minted) is REFUSED: the is-nonzero(m) gate bites.
// ====================================================================================================
#[test]
fn vault_zero_mint_inflation_refused() {
    let desc = vault_descriptor();
    let (trace, dpis) = vault_trace(&desc, (2, 4), (12, /*after_shares*/ 4));
    assert!(
        !accepts(&desc, &trace, &dpis),
        "a zero-mint (inflation) deposit MUST be refused"
    );
    eprintln!("VAULT (zero-mint inflation): REFUSED.");
}

// ====================================================================================================
// TOOTH V2 — an OVER-MINT dilution (21 shares for a deposit of 10: Ta·m = 2·21 = 42 > Sa·d = 40)
// is REFUSED: the borrow comparison produces a final borrow, the no-borrow gate bites.
// ====================================================================================================
#[test]
fn vault_over_mint_dilution_refused() {
    let desc = vault_descriptor();
    let (trace, dpis) = vault_trace(&desc, (2, 4), (12, /*after_shares*/ 25));
    assert!(
        !accepts(&desc, &trace, &dpis),
        "an over-mint (diluting) deposit MUST be refused"
    );
    eprintln!("VAULT (over-mint dilution): REFUSED.");
}

// ====================================================================================================
// TOOTH V3 — a NO-DEPOSIT mint (shares minted, total assets unmoved) is REFUSED: the is-nonzero(d)
// gate bites.
// ====================================================================================================
#[test]
fn vault_no_deposit_refused() {
    let desc = vault_descriptor();
    let (trace, dpis) = vault_trace(&desc, (2, 4), (/*after_assets*/ 2, 24));
    assert!(
        !accepts(&desc, &trace, &dpis),
        "a no-deposit mint MUST be refused"
    );
    eprintln!("VAULT (no-deposit mint): REFUSED.");
}
