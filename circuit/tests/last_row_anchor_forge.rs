//! # THE LAST-ROW ANCHOR FORGE — is a turn's published endpoint algebraically FORCED?
//!
//! ## The claim under test
//!
//! `descriptor_ir2.rs`'s own ⚑ comment states the deployed semantics: `VmConstraint::Gate` is
//! asserted under `builder.is_transition()`, so **every `Gate` body is vacuous on the last row**
//! (Lean models it exactly — `VmConstraint.holdsVm .gate` is `True` when `isLast`). The same is
//! true of `VmConstraint::Transition`, which is the only thing tying one row's AFTER block to the
//! next row's BEFORE block.
//!
//! Every deployed wide member publishes its 8-felt **NEW anchor** — the value `ivc_turn_chain`'s
//! fold consumes as the turn's endpoint — as `PiBinding { row: Last, .. }` over the final wide
//! commit carrier. The prediction under test: *the last row's AFTER state is forced by nothing
//! row-local, so a prover can rewrite it, recompute that row's Poseidon2 chip chain honestly
//! (which is just hashing), rebuild the PI vector, and publish a forged endpoint at the cost of one
//! honest proving run.*
//!
//! ## What this file does
//!
//! It runs the attack and its **paired control**, and the pair is the whole point:
//!
//!   * [`last_row_after_anchor_forge_accepts`] — an honest wide transfer, then **row `n−1` only**:
//!     rewrite the after-balance in both the v1 face and the rotated block, re-derive every
//!     Poseidon2 chip site on that row from its own inputs (the honest prover's own hashing — no
//!     constraint is weakened), rebuild the PI vector from the mutated trace, prove, verify.
//!   * [`transition_covered_row_forge_is_refused`] — **byte-identical mutation, one row earlier**
//!     (`n−2`, which the transition domain DOES cover). Same helper, same repair, same PI rebuild.
//!
//! Without the control an ACCEPT is not attributable: it could be a mis-built trace, a harness
//! error, or a descriptor that accepts everything. With it, the ONLY difference between the two
//! runs is the row index, so an ACCEPT/REFUSE split is the transition-domain selector and nothing
//! else.
//!
//! [`free_pin_census_over_the_deployed_registry`],
//! [`cap_open_tb_free_column_forge_and_its_anchor_control`] and
//! [`mint_free_pin_forge_and_its_reconstruction_control`] measure the second, DISTINCT hazard the
//! same audit predicted: PI slots pinned to a column **no other constraint mentions**, so the
//! prover picks the column AND the published value. Note these pins are on the FIRST row, so
//! last-row vacuity is not what makes them free — nothing referencing the column is. Each is
//! exercised end-to-end INCLUDING the deployed anchor/reconstruction that compensates for it, and
//! that compensation is the difference between them and the endpoint forge above.
//!
//! ## ⚑ INVERTED — the hole is CLOSED, and these now assert the refusal
//!
//! This file was written asserting the hole was OPEN, and it MEASURED that. The repair landed in
//! the Lean emitters (`Dregg2/Circuit/Emit/LastRowFrameHardening.lean`, wired into all three
//! deployed emit probes): every row-local `gate` body is now lowered as a WHOLE-domain
//! `windowGate { on_transition: false }`, so the last row carries the frame/economic algebra it
//! was missing. The descriptors were re-emitted and the three registry fingerprints rotated.
//!
//! The assertions below were then inverted DELIBERATELY, one by one, and this note is the record
//! of it — per the file's own original instruction that a repair "must delete or invert this file
//! deliberately — it must never start passing quietly". What each one says now:
//!
//!   * [`deployed_members_all_carry_last_row_algebra`] — was `covered == ["refusal…"]` (1 of 57).
//!     Now `covered == every member` (57 of 57), and ZERO transition-domain `Gate`s survive.
//!   * [`last_row_after_anchor_forge_is_refused`] — was "PROVES and VERIFIES". Now REFUSED at the
//!     prover: `constraints not satisfied on row 63: failed constraints = [#0, #37]`.
//!   * [`last_row_forge_cannot_publish_the_canonical_commitment_of_an_attacker_chosen_cell`] — the
//!     wire-shaped whole-block substitution. The byte-equality measurement is KEPT (the published
//!     anchor WOULD be `wire_commit_8_chip` of the attacker's cell), and the acceptance is
//!     inverted: the proof is now refused, so that equality never reaches a verifier.
//!   * [`transition_covered_row_forge_is_refused`] — **UNCHANGED, not one character**. It refused
//!     before the repair with `[#0, #14, #26, #37]` and it refuses after with the SAME FOUR. That
//!     is the evidence the repair did not simply break the harness.
//!
//! The last-row refusal names TWO constraints where the covered row names four: `#0` and `#37` are
//! the row-local gates that now fire on both rows, and `#14`/`#26` are `transition` constraints,
//! which are DELIBERATELY still transition-domain-only — their bodies read the NEXT row, which on
//! the last row is the wrap row. The last row's BEFORE block is forced by the INCOMING transition
//! from row `n−2`; the newly-live gates carry it the rest of the way to the AFTER block.
//!
//! ## ⚑ What this file does NOT say is closed
//!
//! [`free_pin_census_over_the_deployed_registry`],
//! [`cap_open_tb_free_column_forge_and_its_anchor_control`] and
//! [`mint_free_pin_forge_and_its_reconstruction_control`] are UNCHANGED and still GREEN, because
//! the second hazard is still open: **173 PI slots across the 57 wide members are pinned to a
//! column no other constraint mentions.** Those pins are free because nothing REFERENCES the
//! column, not because of last-row vacuity — a whole-domain gate over columns the descriptor never
//! names would change nothing. They are compensated at the wire (the executor overwrites those PIs
//! from the trusted turn), and that compensation, not the AIR, is what stops them.
//!
//! Read-only w.r.t. `circuit/src`: nothing here is a fix.

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    DreggStarkConfig, EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, TableSem,
    VmConstraint2, WindowExpr, chip_absorb_all_lanes, eval_lean_expr, parse_vm_descriptor2,
    prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::{
    CAP_OPEN_TB_PI_ACTOR, CAP_OPEN_TB_PI_DST, CapOpenWitness, FACET_MASK_HI, RotatedBlockWitness,
    SIGNATURE_AUTH_TAG, WRITE_MASK_LO, anchor_cap_open_turn_pins,
    generate_rotated_effect_vm_descriptor_and_trace_wide,
    generate_rotated_transfer_cap_open_tb_wide, transfer_caveat_manifest,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::{WIDE_REGISTRY_STAGED_TSV, WIDE_UMEM_WELD_REGISTRY_TSV};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::HeapLeaf;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};
use dregg_turn::rotation_witness as rw;

/// The v1-face column holding the AFTER balance low limb (`STATE_AFTER_BASE + state::BALANCE_LO`).
/// It is range-checked into the 30-bit limb table on EVERY row, so a forged value must stay under
/// `2^30` — that is the only price the attack pays.
const V1_AFTER_BAL_LO: usize = dregg_circuit::effect_vm::columns::STATE_AFTER_BASE
    + dregg_circuit::effect_vm::columns::state::BALANCE_LO;

/// The in-block offset of the balance-low limb inside a rotated state block: `fill_block` lays
/// `row[base + 1] = row[state_base + BALANCE_LO]`, so limb 1 IS the balance the wide commitment
/// chain absorbs. Asserted against the honest trace before anything is mutated.
const ROT_LIMB_BALANCE_LO: usize = 1;

/// The PI slot `mintVmDescriptor2R24` publishes its mint identity at (`ROT_PI_COUNT`, the felt
/// `note_spend_mint_hash_felt` / DECO payment identity — `BRIDGE_MINT_HASH_PI`).
const MINT_HASH_PI: usize = dregg_circuit::effect_vm::trace_rotated::ROT_PI_COUNT;

/// The forged AFTER balance. Under `2^30` so the 30-bit range lookup on the v1 face still holds —
/// and 10_000× the honest turn's endpoint, so a forged anchor cannot be mistaken for rounding.
const FORGED_BALANCE: u32 = 999_999_999;

// ─────────────────────────────────────────────────────────────────────────────
// Honest producer setup (the deployed wide dispatcher, verbatim)
// ─────────────────────────────────────────────────────────────────────────────

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

fn producer_cell(balance: i64, nonce: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("pre-iroot limbs")
}

/// One honest wide transfer leg through the DEPLOYED wide dispatcher — the same call
/// `wide_new_members_cover::fresh_fold_leaf_mints_and_proves_both_bodies` makes for the
/// avail-hardened `transferVmDescriptor2R24`. Returns everything `prove_vm_descriptor2` needs.
#[allow(clippy::type_complexity)]
fn honest_wide_transfer() -> (
    EffectVmDescriptor2,
    Vec<Vec<BabyBear>>,
    Vec<BabyBear>,
    Vec<Vec<HeapLeaf>>,
    MemBoundaryWitness,
) {
    let before_balance: i64 = 100_000;
    let amount: u64 = 50;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance - amount as i64, 1);
    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nr = dregg_circuit::heap_root::empty_heap_root_8();
    let cr = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[5u8; 32], [6u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &nr,
        &cr,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &nr,
        &cr,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let membership_teeth = (BabyBear::new(0xA11CE), BabyBear::new(0xF00D));
    generate_rotated_effect_vm_descriptor_and_trace_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &transfer_caveat_manifest(),
        None,
        None,
        None,
        Some(membership_teeth),
    )
    .expect("the honest wide transfer leg MUST dispatch")
}

// ─────────────────────────────────────────────────────────────────────────────
// Descriptor-driven helpers — every column index below is READ OUT OF THE DEPLOYED
// DESCRIPTOR, never transcribed. A re-emit that moves a column changes what these
// find; it cannot make them silently miss.
// ─────────────────────────────────────────────────────────────────────────────

/// The wire id of the member's Poseidon2 chip table.
fn poseidon2_table_id(desc: &EffectVmDescriptor2) -> usize {
    desc.tables
        .iter()
        .find(|t| t.sem == TableSem::Poseidon2Chip)
        .map(|t| t.id)
        .expect("every wide member declares a poseidon2 chip table")
}

/// One Poseidon2 chip site as the descriptor states it: `(arity, 16 input exprs, 8 output cols)`.
/// The committed tuple is `[arity, in0..in15, out0..out7]` (25 entries).
struct ChipSite {
    arity: usize,
    inputs: Vec<LeanExpr>,
    outputs: Vec<usize>,
}

fn chip_sites(desc: &EffectVmDescriptor2) -> Vec<ChipSite> {
    let tid = poseidon2_table_id(desc);
    let mut out = Vec::new();
    for k in &desc.constraints {
        let VmConstraint2::Lookup(l) = k else {
            continue;
        };
        if l.table != tid {
            continue;
        }
        assert_eq!(
            l.tuple.len(),
            25,
            "a poseidon2 chip lookup tuple is [arity, 16 in, 8 out]"
        );
        let LeanExpr::Const(arity) = l.tuple[0] else {
            panic!("a chip site's arity lane must be a constant")
        };
        let outputs: Vec<usize> = l.tuple[17..25]
            .iter()
            .map(|e| match e {
                LeanExpr::Var(c) => *c,
                other => panic!("a chip site's output lane must be a column, got {other:?}"),
            })
            .collect();
        out.push(ChipSite {
            arity: arity as usize,
            inputs: l.tuple[1..17].to_vec(),
            outputs,
        });
    }
    out
}

/// **The honest prover's own hashing, re-run on ONE row.** Recompute every Poseidon2 chip site's 8
/// output lanes from that site's own declared inputs, to fixpoint (the sites form a chain, and the
/// descriptor's emission order is not guaranteed to be topological). This WEAKENS NOTHING: it
/// re-derives exactly what the chip lookup argument forces. Returns the number of sweeps taken.
///
/// Panics if it has not converged — a non-convergent chain would mean the forge silently shipped an
/// inconsistent chip lane and the resulting refusal would be misattributed.
fn rehash_row(sites: &[ChipSite], row: &mut [BabyBear]) -> usize {
    for sweep in 1..=64 {
        let mut changed = false;
        for s in sites {
            let ins: Vec<BabyBear> = s.inputs[..s.arity]
                .iter()
                .map(|e| eval_lean_expr(e, row))
                .collect();
            let lanes = chip_absorb_all_lanes(s.arity, &ins);
            for (j, &c) in s.outputs.iter().enumerate() {
                if row[c] != lanes[j] {
                    row[c] = lanes[j];
                    changed = true;
                }
            }
        }
        if !changed {
            return sweep;
        }
    }
    panic!("the chip chain did not reach a fixpoint in 64 sweeps");
}

/// Rebuild the published PI vector from the (possibly mutated) trace, exactly as an honest producer
/// does: every `PiBinding` reads its pinned column off its pinned row.
fn rebuild_pis(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &mut [BabyBear]) {
    let last = trace.len() - 1;
    for k in &desc.constraints {
        if let VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index }) = k {
            let r = match row {
                VmRow::First => 0,
                VmRow::Last => last,
            };
            pis[*pi_index] = trace[r][*col];
        }
    }
}

/// The 8 columns carrying the published NEW anchor: the `Last`-row `PiBinding` columns whose PI
/// indices are the top 8 of the member's PI vector (the wide AFTER commit carrier).
fn after_anchor_cols(desc: &EffectVmDescriptor2) -> Vec<usize> {
    let mut pins: Vec<(usize, usize)> = desc
        .constraints
        .iter()
        .filter_map(|k| match k {
            VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::Last,
                col,
                pi_index,
            }) => Some((*pi_index, *col)),
            _ => None,
        })
        .collect();
    pins.sort_unstable();
    let n = desc.public_input_count;
    let anchor: Vec<usize> = pins
        .iter()
        .filter(|(pi, _)| *pi >= n - 8)
        .map(|(_, c)| *c)
        .collect();
    assert_eq!(
        anchor.len(),
        8,
        "the member's top 8 PIs must be the 8-felt AFTER anchor, pinned on the LAST row"
    );
    anchor
}

/// Walk the chip chain backwards from the AFTER anchor and return the distinct **limb** columns it
/// absorbs (the non-`prev8` input lanes). Their minimum is the rotated AFTER block's base column in
/// the member's COMPACTED frame — derived, never transcribed.
fn after_chain_limb_base(desc: &EffectVmDescriptor2) -> usize {
    let sites = chip_sites(desc);
    let anchor = after_anchor_cols(desc);
    let by_out: std::collections::HashMap<Vec<usize>, &ChipSite> =
        sites.iter().map(|s| (s.outputs.clone(), s)).collect();

    let mut limbs: Vec<usize> = Vec::new();
    let mut cur = anchor;
    let mut seen = std::collections::HashSet::new();
    while let Some(site) = by_out.get(&cur) {
        if !seen.insert(cur.clone()) {
            break;
        }
        // arity 4 = the chain head (4 limbs); arity 9/11 = prev8 ‖ limbs.
        let limb_lanes: &[LeanExpr] = if site.arity == 4 {
            &site.inputs[0..4]
        } else {
            &site.inputs[8..site.arity]
        };
        for e in limb_lanes {
            if let LeanExpr::Var(c) = e {
                limbs.push(*c);
            }
        }
        if site.arity == 4 {
            break;
        }
        let prev: Vec<usize> = site.inputs[0..8]
            .iter()
            .map(|e| match e {
                LeanExpr::Var(c) => *c,
                _ => usize::MAX,
            })
            .collect();
        if prev.contains(&usize::MAX) {
            break;
        }
        cur = prev;
    }
    limbs.sort_unstable();
    limbs.dedup();
    assert!(
        limbs.len() > 100,
        "the AFTER anchor chain must absorb the whole rotated block ({} limbs found)",
        limbs.len()
    );
    limbs[0]
}

/// Run a prove attempt, converting a panic into an `Err` so a refusal is never confused with a
/// crash and every refusal carries its text.
fn try_prove(
    desc: &EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    pis: &[BabyBear],
    mb: &MemBoundaryWitness,
    heaps: &[Vec<HeapLeaf>],
) -> Result<Ir2BatchProof<DreggStarkConfig>, String> {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_vm_descriptor2(desc, trace, pis, mb, heaps)
    })) {
        Ok(r) => r,
        Err(p) => {
            let m = p
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_else(|| "<non-string panic>".to_string());
            Err(format!("PANIC: {m}"))
        }
    }
}

/// **The mutation, parameterised only by the row it lands on.** Rewrite the AFTER balance in the v1
/// face AND in the rotated block, re-derive that row's whole chip chain honestly, and rebuild the
/// published PI vector. Returns the mutated `(trace, pis)`.
fn forge_after_balance_at_row(
    desc: &EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    pis: &[BabyBear],
    row: usize,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let limb_base = after_chain_limb_base(desc);
    let rot_bal = limb_base + ROT_LIMB_BALANCE_LO;
    assert_eq!(
        trace[row][V1_AFTER_BAL_LO], trace[row][rot_bal],
        "the honest producer copies the v1 AFTER balance into rotated limb {ROT_LIMB_BALANCE_LO} \
         (v1 col {V1_AFTER_BAL_LO}, rotated col {rot_bal}) — if this no longer holds the layout \
         moved and this forge is aiming at the wrong column"
    );
    let mut t = trace.to_vec();
    let sites = chip_sites(desc);
    t[row][V1_AFTER_BAL_LO] = BabyBear::new(FORGED_BALANCE);
    t[row][rot_bal] = BabyBear::new(FORGED_BALANCE);
    let sweeps = rehash_row(&sites, &mut t[row]);
    eprintln!("  forge@row {row}: chip chain re-derived honestly in {sweeps} sweeps");
    let mut p = pis.to_vec();
    rebuild_pis(desc, &t, &mut p);
    (t, p)
}

// ─────────────────────────────────────────────────────────────────────────────
// 0. The structural read, MEASURED over the whole deployed registry
// ─────────────────────────────────────────────────────────────────────────────

/// **INVERTED.** Across both deployed wide registries: how many members emit constraints that are
/// live on the last row other than a `Last` boundary pin — a `Boundary`, or a whole-domain
/// `WindowGate { on_transition: false }`.
///
/// Before the repair this measured **1 of 57** (`refusalVmDescriptor2R24` alone). It now measures
/// **57 of 57**, and additionally that ZERO transition-domain `Gate`s survive anywhere — the Lean
/// `hardenLastRow` moved every one of them onto the whole domain, so there is no residue to be
/// vacuous on the last row.
#[test]
fn deployed_members_all_carry_last_row_algebra() {
    for (label, tsv) in [
        ("WIDE_REGISTRY_STAGED_TSV", WIDE_REGISTRY_STAGED_TSV),
        ("WIDE_UMEM_WELD_REGISTRY_TSV", WIDE_UMEM_WELD_REGISTRY_TSV),
    ] {
        let mut total = 0usize;
        let mut uncovered: Vec<String> = Vec::new();
        let mut unhardened: Vec<(String, usize)> = Vec::new();
        let mut total_whole_domain = 0usize;
        for line in tsv.lines() {
            let mut it = line.splitn(3, '\t');
            let (Some(key), Some(_), Some(json)) = (it.next(), it.next(), it.next()) else {
                continue;
            };
            let d = parse_vm_descriptor2(json).unwrap_or_else(|e| panic!("{key} parses: {e}"));
            total += 1;
            let has_last_row_algebra = d.constraints.iter().any(|k| {
                matches!(k, VmConstraint2::Base(VmConstraint::Boundary { .. }))
                    || matches!(k, VmConstraint2::WindowGate(w) if !w.on_transition)
            });
            let residual_gates = d
                .constraints
                .iter()
                .filter(|k| matches!(k, VmConstraint2::Base(VmConstraint::Gate(_))))
                .count();
            if residual_gates != 0 {
                unhardened.push((key.to_string(), residual_gates));
            }
            if !has_last_row_algebra {
                uncovered.push(key.to_string());
            }
            total_whole_domain += d
                .constraints
                .iter()
                .filter(|k| matches!(k, VmConstraint2::WindowGate(w) if !w.on_transition))
                .count();
        }
        eprintln!(
            "{label}: {total} members, {total_whole_domain} whole-domain windowGates, \
             {} members WITHOUT last-row-live algebra",
            uncovered.len()
        );
        assert_eq!(total, 57, "{label} member count");
        assert!(
            uncovered.is_empty(),
            "MEASURED (inverted 2026-07-30): every deployed member must emit algebra that survives \
             on the LAST row — the row it pins its published 8-felt AFTER anchor on. Before the \
             Lean `hardenLastRow` flag day exactly ONE member did (`refusalVmDescriptor2R24`) and \
             the last-row anchor forge below ACCEPTED. If this list is non-empty again, a member \
             was re-emitted without the hardening: {uncovered:?}"
        );
        assert!(
            unhardened.is_empty(),
            "MEASURED (inverted 2026-07-30): NO transition-domain `Gate` may survive in a deployed \
             member — `holdsVm .gate` is definitionally `True` on the last row, so any residue is \
             a body that silently stops being asserted there. Members still carrying one: \
             {unhardened:?}"
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 1. THE LAST-ROW FORGE, and its paired control
// ─────────────────────────────────────────────────────────────────────────────

/// **THE FORGE, INVERTED.** Honest wide transfer; then on row `n−1` ONLY, rewrite the AFTER
/// balance, re-derive the Poseidon2 chip chain honestly, rebuild the PI vector, prove.
///
/// This test asserted an ACCEPT and measured one. It now asserts the REFUSAL, and the refusal is
/// `constraints not satisfied on row 63: failed constraints = [#0, #37]` — the economic frame gate
/// and the AFTER-balance limb recomposition, both of which used to be multiplied to zero on that
/// row by `builder.is_transition()`.
///
/// The honest baseline is kept AHEAD of the mutation and is the thing that makes the refusal mean
/// something: the same descriptor, the same producer, the same PI rebuild, one row different.
/// Without it a green run here would be indistinguishable from a descriptor that refuses
/// everything.
#[test]
fn last_row_after_anchor_forge_is_refused() {
    let (desc, trace, dpis, heaps, mb) = honest_wide_transfer();
    let n = trace.len();
    eprintln!(
        "member {} — width {}, PIs {}, rows {n}",
        desc.name, desc.trace_width, desc.public_input_count
    );
    assert!(n >= 3, "need at least 3 rows for a covered-row control");

    // BASELINE: the honest leg proves and verifies. Without this a later refusal is not a
    // measurement of anything.
    let honest_proof = try_prove(&desc, &trace, &dpis, &mb, &heaps)
        .unwrap_or_else(|e| panic!("the HONEST wide transfer must prove: {e}"));
    verify_vm_descriptor2(&desc, &honest_proof, &dpis)
        .unwrap_or_else(|e| panic!("the HONEST wide transfer must verify: {e}"));
    let anchor_cols = after_anchor_cols(&desc);
    let honest_anchor: Vec<BabyBear> = anchor_cols.iter().map(|&c| trace[n - 1][c]).collect();
    eprintln!("  honest NEW anchor (cols {anchor_cols:?}): {honest_anchor:?}");

    // THE FORGE, on the last row only.
    let (ftrace, fpis) = forge_after_balance_at_row(&desc, &trace, &dpis, n - 1);
    let forged_anchor: Vec<BabyBear> = anchor_cols.iter().map(|&c| ftrace[n - 1][c]).collect();
    assert_ne!(
        honest_anchor, forged_anchor,
        "the forge must actually move the published anchor, or it measures nothing"
    );
    eprintln!("  forged NEW anchor: {forged_anchor:?}");

    // The forged PI vector IS self-consistent with the mutated trace — every `Last` pin agrees —
    // so nothing about the PI layout is what refuses it. Only the row-local algebra can.
    let n_pi = desc.public_input_count;
    assert_ne!(
        &dpis[n_pi - 8..],
        &fpis[n_pi - 8..],
        "the forge must still MOVE the published 8-felt NEW anchor, or the refusal below is not a \
         measurement of anything"
    );

    let outcome = try_prove(&desc, &ftrace, &fpis, &mb, &heaps)
        .and_then(|p| verify_vm_descriptor2(&desc, &p, &fpis).map_err(|e| format!("verify: {e}")));
    let err = match outcome {
        Ok(()) => panic!(
            "⚑ THE LAST-ROW ANCHOR FORGE IS OPEN AGAIN. {} published a NEW anchor committing to \
             balance {} where the honest turn ended at {} — the value `ivc_turn_chain`'s fold \
             consumes as this turn's endpoint, for the cost of one honest proving run and one \
             rehash. This test was INVERTED on 2026-07-30 when the Lean `hardenLastRow` flag day \
             closed it; an ACCEPT here means a member was re-emitted without the hardening, or \
             `windowGate {{ on_transition: false }}` stopped being asserted on the whole domain.",
            desc.name,
            FORGED_BALANCE,
            trace[n - 1][V1_AFTER_BAL_LO].as_u32()
        ),
        Err(e) => e,
    };
    eprintln!("LAST-ROW FORGE REFUSED: {err}");

    // The refusal must be a CONSTRAINT failure on the LAST row, not a shape/arity complaint —
    // otherwise the hole could be open and merely masked by a harness error.
    let lowered = err.to_lowercase();
    for bogus in [
        "width",
        "arity",
        "public_input_count",
        "degree_bits",
        "not in ",
    ] {
        assert!(
            !lowered.contains(bogus),
            "the last-row refusal must be a CONSTRAINT failure, not a shape error \
             (saw {bogus:?} in: {err})"
        );
    }
    assert!(
        err.contains(&format!("row {}", n - 1)),
        "the refusal must name the LAST row ({}), or it is refusing for some other reason: {err}",
        n - 1
    );
    eprintln!(
        "MEASURED — the forged endpoint is REFUSED on row {} by the now-whole-domain frame gates.",
        n - 1
    );
}

/// **THE FORGE IN ITS WIRE-SHAPED FORM, INVERTED.** The test above moves one limb. This one
/// replaces the last row's ENTIRE rotated AFTER block with the limbs of a cell the attacker picked.
///
/// The BYTE-EQUALITY MEASUREMENT IS KEPT and still asserted, because it is what named the wire
/// reach: the anchor such a trace would publish is byte-equal to `wire_commit_8_chip` of the
/// attacker's cell, i.e. exactly what an honest producer would publish for that cell — so a
/// submitter setting `turn.execution_proof_new_commitment` to it satisfies
/// `proof_verify.rs`'s PI override by construction. What is INVERTED is the acceptance: that trace
/// no longer proves, so the equality never reaches a verifier.
///
/// Keeping the equality rather than deleting it is deliberate. It is the statement of what the
/// wire would have done, and it stays true; only the AIR now stands in front of it.
#[test]
fn last_row_forge_cannot_publish_the_canonical_commitment_of_an_attacker_chosen_cell() {
    use dregg_circuit::effect_vm::trace_rotated::{B_IROOT, NUM_PRE_LIMBS};

    let (desc, trace, dpis, heaps, mb) = honest_wide_transfer();
    let n = trace.len();
    let base = after_chain_limb_base(&desc);

    // The attacker's cell: same identity, a balance the turn never produced.
    let mut ledger = Ledger::new();
    let forged_cell = producer_cell(FORGED_BALANCE as i64, 1);
    ledger.insert_cell(forged_cell.clone()).unwrap();
    let nr = dregg_circuit::heap_root::empty_heap_root_8();
    let cr = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[5u8; 32], [6u8; 32]];
    let forged_w = rw::produce(
        &forged_cell,
        &ledger,
        &nr,
        &cr,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    assert_eq!(forged_w.pre_limbs.len(), NUM_PRE_LIMBS);

    // Row n−1 ONLY: the whole AFTER block becomes the attacker's cell.
    let mut t = trace.clone();
    for (j, l) in forged_w.pre_limbs.iter().enumerate() {
        t[n - 1][base + j] = *l;
    }
    t[n - 1][base + B_IROOT] = forged_w.iroot;
    t[n - 1][V1_AFTER_BAL_LO] = BabyBear::new(FORGED_BALANCE);
    let sites = chip_sites(&desc);
    rehash_row(&sites, &mut t[n - 1]);
    let mut p = dpis.clone();
    rebuild_pis(&desc, &t, &mut p);

    // THE EQUALITY THAT MATTERS: the published anchor IS the executor's own anchoring primitive
    // applied to the attacker's cell — the same call `effect_vm_wide_roundtrip`'s executor-anchor
    // differential makes for the honest BEFORE side.
    let expected =
        dregg_circuit::poseidon2::wire_commit_8_chip(&forged_w.pre_limbs, forged_w.iroot);
    let published: Vec<BabyBear> = p[desc.public_input_count - 8..].to_vec();
    assert_eq!(
        published,
        expected.to_vec(),
        "the published NEW anchor must be the canonical 8-felt commitment of the attacker's cell — \
         otherwise this measures a corrupted trace, not a forgery the wire would accept"
    );

    let outcome = try_prove(&desc, &t, &p, &mb, &heaps)
        .and_then(|pr| verify_vm_descriptor2(&desc, &pr, &p).map_err(|e| format!("verify: {e}")));
    let last_err = match outcome {
        Ok(()) => panic!(
            "⚑ THE WIRE-SHAPED LAST-ROW FORGE IS OPEN AGAIN: the published NEW anchor is \
             `wire_commit_8_chip` of an ATTACKER-CHOSEN cell (balance {FORGED_BALANCE}) and the \
             proof VERIFIES. A submitter setting `execution_proof_new_commitment` to this same \
             8-felt value satisfies `proof_verify.rs`'s PI override by construction, and the \
             executor writes it to the ledger."
        ),
        Err(e) => e,
    };
    eprintln!(
        "WIRE-SHAPED LAST-ROW FORGE REFUSED at row {}: {last_err}",
        n - 1
    );
    assert!(
        last_err.contains(&format!("row {}", n - 1)),
        "the whole-block substitution must be refused ON THE LAST ROW: {last_err}"
    );

    // ITS OWN PAIRED CONTROL, UNCHANGED: the SAME whole-block substitution one row earlier is
    // REFUSED, exactly as it was before the repair. Both rows now refuse; the control's continued
    // refusal is what shows the last-row refusal is the algebra and not a broken harness.
    let mut c = trace.clone();
    for (j, l) in forged_w.pre_limbs.iter().enumerate() {
        c[n - 2][base + j] = *l;
    }
    c[n - 2][base + B_IROOT] = forged_w.iroot;
    c[n - 2][V1_AFTER_BAL_LO] = BabyBear::new(FORGED_BALANCE);
    rehash_row(&sites, &mut c[n - 2]);
    let mut cp = dpis.clone();
    rebuild_pis(&desc, &c, &mut cp);
    let control = try_prove(&desc, &c, &cp, &mb, &heaps)
        .and_then(|pr| verify_vm_descriptor2(&desc, &pr, &cp).map_err(|e| format!("verify: {e}")));
    let err = match control {
        Ok(()) => panic!(
            "CONTROL FAILED: the SAME whole-block substitution on a TRANSITION-COVERED row was \
             ACCEPTED. The last-row REFUSAL above is then not attributable to the algebra."
        ),
        Err(e) => e,
    };
    eprintln!("CONTROL (whole-block substitution at row n-2) REFUSED: {err}");
    let lowered = err.to_lowercase();
    for bogus in [
        "width",
        "arity",
        "public_input_count",
        "degree_bits",
        "not in ",
    ] {
        assert!(
            !lowered.contains(bogus),
            "the control's refusal must be a CONSTRAINT failure, not a shape error \
             (saw {bogus:?} in: {err})"
        );
    }
}

/// **THE PAIRED CONTROL.** The byte-identical mutation one row earlier — row `n−2`, which the
/// transition domain DOES cover. Same helper, same honest rehash, same PI rebuild. It must be
/// REFUSED, and the refusal must be a constraint failure rather than a shape or arity error.
///
/// This is what makes the ACCEPT above attributable to the transition-domain selector: the two runs
/// differ in exactly one integer.
#[test]
fn transition_covered_row_forge_is_refused() {
    let (desc, trace, dpis, heaps, mb) = honest_wide_transfer();
    let n = trace.len();
    assert!(n >= 3);

    let (ctrace, cpis) = forge_after_balance_at_row(&desc, &trace, &dpis, n - 2);
    // The mutation LANDED — otherwise a refusal would be measuring the honest trace.
    assert_ne!(
        ctrace[n - 2][V1_AFTER_BAL_LO],
        trace[n - 2][V1_AFTER_BAL_LO],
        "the control mutation must actually change row n-2"
    );
    // And it is the SAME mutation: the forged value is identical to the last-row run's.
    assert_eq!(
        ctrace[n - 2][V1_AFTER_BAL_LO],
        BabyBear::new(FORGED_BALANCE)
    );

    let outcome = try_prove(&desc, &ctrace, &cpis, &mb, &heaps)
        .and_then(|p| verify_vm_descriptor2(&desc, &p, &cpis).map_err(|e| format!("verify: {e}")));
    let err = match outcome {
        Ok(()) => panic!(
            "CONTROL FAILED: the SAME mutation on a TRANSITION-COVERED row (n-2) was ACCEPTED. \
             The last-row ACCEPT is then NOT attributable to last-row vacuity — this descriptor \
             does not constrain the AFTER block on any row, which is a strictly larger finding \
             and must be reported as such rather than as the predicted hole."
        ),
        Err(e) => e,
    };
    eprintln!("CONTROL (row n-2, transition-covered) REFUSED: {err}");
    // A refusal that is really a shape/arity/witness-plumbing complaint would not attribute either.
    let lowered = err.to_lowercase();
    for bogus in [
        "width",
        "arity",
        "public_input_count",
        "degree_bits",
        "not in ",
    ] {
        assert!(
            !lowered.contains(bogus),
            "the control's refusal must be a CONSTRAINT failure, not a shape error \
             (saw {bogus:?} in: {err})"
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 2/3. THE FREE-COLUMN CLASS — a PI pinned to a column nothing else mentions
// ─────────────────────────────────────────────────────────────────────────────

/// Every column the member mentions ANYWHERE other than in a `PiBinding`.
fn non_pin_referenced_cols(desc: &EffectVmDescriptor2) -> std::collections::HashSet<usize> {
    fn vars(e: &LeanExpr, acc: &mut std::collections::HashSet<usize>) {
        match e {
            LeanExpr::Var(c) => {
                acc.insert(*c);
            }
            LeanExpr::Const(_) => {}
            LeanExpr::Add(a, b) | LeanExpr::Mul(a, b) => {
                vars(a, acc);
                vars(b, acc);
            }
        }
    }
    let mut acc = std::collections::HashSet::new();
    for k in &desc.constraints {
        match k {
            VmConstraint2::Base(VmConstraint::Gate(b))
            | VmConstraint2::Base(VmConstraint::Boundary { body: b, .. }) => vars(b, &mut acc),
            VmConstraint2::Base(VmConstraint::Transition { .. }) => {
                // the two state blocks are named structurally, not by expression
                let sb = dregg_circuit::effect_vm::columns::STATE_BEFORE_BASE;
                let sa = dregg_circuit::effect_vm::columns::STATE_AFTER_BASE;
                if let VmConstraint2::Base(VmConstraint::Transition { hi, lo }) = k {
                    acc.insert(sb + hi);
                    acc.insert(sa + lo);
                }
            }
            VmConstraint2::Base(VmConstraint::PiBinding { .. }) => {}
            VmConstraint2::Lookup(l) => {
                for e in &l.tuple {
                    vars(e, &mut acc);
                }
            }
            VmConstraint2::WindowGate(w) => {
                // window bodies range over local ‖ next; treat every named index as referenced
                fn wvars(e: &WindowExpr, acc: &mut std::collections::HashSet<usize>) {
                    match e {
                        WindowExpr::Loc(c) | WindowExpr::Nxt(c) => {
                            acc.insert(*c);
                        }
                        WindowExpr::Const(_) => {}
                        WindowExpr::Add(a, b) | WindowExpr::Mul(a, b) => {
                            wvars(a, acc);
                            wvars(b, acc);
                        }
                    }
                }
                wvars(&w.body, &mut acc);
            }
            _ => {}
        }
    }
    acc
}

/// **THE FREE-COLUMN CENSUS, MEASURED.** A `PiBinding` whose column appears in NO other constraint
/// means the prover chooses the column and the published value together — the pin is satisfied by
/// construction and publishes whatever the prover wants.
#[test]
fn free_pin_census_over_the_deployed_registry() {
    let mut total_members = 0usize;
    let mut total_free = 0usize;
    let mut worst: Vec<(String, Vec<usize>)> = Vec::new();
    for line in WIDE_REGISTRY_STAGED_TSV.lines() {
        let mut it = line.splitn(3, '\t');
        let (Some(key), Some(_), Some(json)) = (it.next(), it.next(), it.next()) else {
            continue;
        };
        let d = parse_vm_descriptor2(json).unwrap();
        let referenced = non_pin_referenced_cols(&d);
        let mut free: Vec<usize> = d
            .constraints
            .iter()
            .filter_map(|k| match k {
                VmConstraint2::Base(VmConstraint::PiBinding { col, pi_index, .. })
                    if !referenced.contains(col) =>
                {
                    Some(*pi_index)
                }
                _ => None,
            })
            .collect();
        free.sort_unstable();
        total_members += 1;
        total_free += free.len();
        if !free.is_empty() {
            worst.push((key.to_string(), free));
        }
    }
    worst.sort_by_key(|(_, f)| std::cmp::Reverse(f.len()));
    eprintln!(
        "FREE-PIN CENSUS over {total_members} deployed wide members: {total_free} PI slots pinned to a column no other constraint mentions"
    );
    for (k, f) in worst.iter().take(12) {
        eprintln!("   {k}: PIs {f:?}");
    }
    assert!(
        total_free > 0,
        "MEASURED: no free pins remain — the class named by the audit is closed and this test \
         should be retired rather than relaxed"
    );
}

/// **THE `transferCapOpenTB` FREE-COLUMN FORGE, end to end — INCLUDING the compensating control
/// the deployed verifier already carries.** The audit predicted cols 928/929 (PIs 47/48, the turn's
/// actor and destination) accept arbitrary values. Measured in two halves:
///
///   (a) at the AIR alone: a self-consistent forged (column, PI) pair proves and verifies;
///   (b) through the DEPLOYED light-client anchor (`anchor_cap_open_turn_pins`, which overwrites
///       those PIs from the TRUSTED turn before verifying): the same proof is REFUSED.
///
/// (b) is the paired control and it is also the answer: the free column is real, and the wire is
/// not fooled by it, because the light client does not read the prover's value.
#[test]
fn cap_open_tb_free_column_forge_and_its_anchor_control() {
    let name = "transferCapOpenTBVmDescriptor2R24";
    let json = WIDE_REGISTRY_STAGED_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some(name) {
                let _ = it.next();
                it.next()
            } else {
                None
            }
        })
        .expect("member present");
    let desc = parse_vm_descriptor2(json).unwrap();

    let before_balance: i64 = 100_000;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::Transfer {
        amount: 1_000,
        direction: 1,
    }];
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance - 1_000, 1);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nr = dregg_circuit::heap_root::empty_heap_root_8();
    let cr = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32], [4u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &nr,
        &cr,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &nr,
        &cr,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let src_felt: u32 = 7_777;
    let chosen: [BabyBear; 7] = [
        BabyBear::new(0xA11CE),
        BabyBear::new(src_felt),
        BabyBear::new(SIGNATURE_AUTH_TAG),
        BabyBear::new(WRITE_MASK_LO),
        BabyBear::new(FACET_MASK_HI),
        BabyBear::new(0x00FF_FFFF),
        BabyBear::new(42),
    ];
    let other: [BabyBear; 7] = [
        BabyBear::new(0xBEEF),
        BabyBear::new(123),
        BabyBear::new(1),
        BabyBear::new(1),
        BabyBear::new(0),
        BabyBear::new(9),
        BabyBear::new(0),
    ];
    let cap_open = CapOpenWitness::build(&[other, chosen], 1).expect("cap-open witness");
    let src = BabyBear::new(src_felt);
    let (trace, dpis) = generate_rotated_transfer_cap_open_tb_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &transfer_caveat_manifest(),
        &cap_open,
        src,
        src,
        src,
    )
    .expect("wide cap-open-TB generation");

    // The two pinned columns, READ OUT OF THE DESCRIPTOR.
    let pin_col = |pi_want: usize| -> (usize, VmRow) {
        desc.constraints
            .iter()
            .find_map(|k| match k {
                VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index })
                    if *pi_index == pi_want =>
                {
                    Some((*col, *row))
                }
                _ => None,
            })
            .unwrap_or_else(|| panic!("PI {pi_want} is pinned"))
    };
    let (actor_col, actor_row) = pin_col(CAP_OPEN_TB_PI_ACTOR);
    let (dst_col, dst_row) = pin_col(CAP_OPEN_TB_PI_DST);
    let referenced = non_pin_referenced_cols(&desc);
    eprintln!(
        "{name}: actor PI {CAP_OPEN_TB_PI_ACTOR} -> col {actor_col} ({actor_row:?}), \
         dst PI {CAP_OPEN_TB_PI_DST} -> col {dst_col} ({dst_row:?}); \
         referenced elsewhere: actor={} dst={}",
        referenced.contains(&actor_col),
        referenced.contains(&dst_col)
    );

    let mut t = trace.clone();
    let mut p = dpis.clone();
    let forged_actor = BabyBear::new(0x0DEA_DBEE);
    let forged_dst = BabyBear::new(0x0BAD_F00D % 2_013_265_921);
    let r_actor = match actor_row {
        VmRow::First => 0,
        VmRow::Last => t.len() - 1,
    };
    let r_dst = match dst_row {
        VmRow::First => 0,
        VmRow::Last => t.len() - 1,
    };
    t[r_actor][actor_col] = forged_actor;
    t[r_dst][dst_col] = forged_dst;
    p[CAP_OPEN_TB_PI_ACTOR] = forged_actor;
    p[CAP_OPEN_TB_PI_DST] = forged_dst;

    let mb = MemBoundaryWitness::default();
    let heaps: Vec<Vec<HeapLeaf>> = vec![];
    let air_level = try_prove(&desc, &t, &p, &mb, &heaps).and_then(|proof| {
        verify_vm_descriptor2(&desc, &proof, &p)
            .map(|()| proof)
            .map_err(|e| format!("verify: {e}"))
    });
    match &air_level {
        Ok(proof) => {
            eprintln!(
                "MEASURED — {name} AIR-LEVEL: a forged actor/dst pair (self-consistent column+PI) \
                 PROVES and VERIFIES. The pin is satisfied by construction."
            );
            // (b) THE DEPLOYED CONTROL: the light client re-derives those PIs from the trusted
            // turn. The same proof must then be REFUSED.
            let mut anchored = p.clone();
            anchor_cap_open_turn_pins(&mut anchored, src, src, src);
            let anchored_result = verify_vm_descriptor2(&desc, proof, &anchored);
            assert!(
                anchored_result.is_err(),
                "CONTROL FAILED: the forged proof survived the deployed trusted-turn anchor \
                 (`anchor_cap_open_turn_pins`). If the anchor no longer bites, the free column IS \
                 a wire-level forgery."
            );
            eprintln!(
                "CONTROL — {name}: the DEPLOYED light-client anchor REFUSES the same proof: {}",
                anchored_result.unwrap_err()
            );
        }
        Err(e) => panic!(
            "{name} free-column forge REFUTED at the AIR: {e}\n\
             The audit predicted this ACCEPTS."
        ),
    }
}

/// **THE `mint` PIN — a PI bound to a column nothing else touches.** `mintVmDescriptor2R24` pins
/// PI 46 to col 68 (`PARAM_BASE + param::MINT_HASH`) on the FIRST row. Measured above: that column
/// appears in no gate, no lookup, no transition — so the prover chooses the column AND the
/// published mint identity, and the pin holds by construction.
///
/// Measured in the same two halves as the cap-open pins:
///   (a) at the AIR: an arbitrary self-consistent (col 68, PI 46) pair proves and verifies;
///   (b) under the DEPLOYED reconstruction — the executor recomputes the mint identity from the
///       turn's own carrier witness rather than reading the prover's — the same proof is REFUSED.
#[test]
fn mint_free_pin_forge_and_its_reconstruction_control() {
    let name = "mintVmDescriptor2R24";
    let st = CellState::new(100_000, 0);
    let honest_mint_hash = BabyBear::new(0x00C0_FFEE);
    let value_full: u64 = 4_242;
    let effects = vec![Effect::BridgeMint {
        value_lo: BabyBear::new(value_full as u32),
        mint_hash: honest_mint_hash,
        value_full,
    }];
    let before_cell = producer_cell(100_000, 0);
    let after_cell = producer_cell(100_000 + value_full as i64, 1);
    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nr = dregg_circuit::heap_root::empty_heap_root_8();
    let cr = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[9u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &nr,
        &cr,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &nr,
        &cr,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let (desc, trace, dpis, heaps, mb) = generate_rotated_effect_vm_descriptor_and_trace_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &dregg_circuit::effect_vm::trace_rotated::empty_caveat_manifest(),
        None,
        None,
        None,
        None,
    )
    .expect("the honest bridge-mint leg MUST dispatch");

    // The pinned column, READ OUT OF THE DESCRIPTOR — and its reference count.
    let (col, row) = desc
        .constraints
        .iter()
        .find_map(|k| match k {
            VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index })
                if *pi_index == MINT_HASH_PI =>
            {
                Some((*col, *row))
            }
            _ => None,
        })
        .expect("mint pins PI 46");
    let referenced = non_pin_referenced_cols(&desc);
    eprintln!(
        "{name}: mint-hash PI {MINT_HASH_PI} -> col {col} ({row:?}); referenced elsewhere: {}",
        referenced.contains(&col)
    );
    assert_eq!(
        dpis[MINT_HASH_PI], honest_mint_hash,
        "the honest leg publishes the real mint hash"
    );

    let r = match row {
        VmRow::First => 0,
        VmRow::Last => trace.len() - 1,
    };
    let forged_hash = BabyBear::new(0x0BAD_1DEA);
    let mut t = trace.clone();
    let mut p = dpis.clone();
    t[r][col] = forged_hash;
    p[MINT_HASH_PI] = forged_hash;
    // Re-derive the chip chains anyway, so an ACCEPT cannot be attributed to a stale lane.
    let sites = chip_sites(&desc);
    rehash_row(&sites, &mut t[r]);
    rebuild_pis(&desc, &t, &mut p);
    assert_eq!(p[MINT_HASH_PI], forged_hash);

    let proof = match try_prove(&desc, &t, &p, &mb, &heaps) {
        Ok(pr) => pr,
        Err(e) => panic!("{name} free-pin forge REFUTED at the prover: {e}"),
    };
    verify_vm_descriptor2(&desc, &proof, &p)
        .unwrap_or_else(|e| panic!("{name} free-pin forge REFUTED at the verifier: {e}"));
    eprintln!(
        "MEASURED — {name} AIR-LEVEL: an ARBITRARY mint identity (col {col} = PI {MINT_HASH_PI} = \
         {forged_hash:?}) proves and verifies; the honest turn minted under {honest_mint_hash:?}."
    );

    // THE CONTROL: the deployed verifier does not read the prover's slot — it reconstructs the
    // mint identity from the turn's own carrier witness. Substitute the reconstructed value.
    let mut reconstructed = p.clone();
    reconstructed[MINT_HASH_PI] = honest_mint_hash;
    let control = verify_vm_descriptor2(&desc, &proof, &reconstructed);
    assert!(
        control.is_err(),
        "CONTROL FAILED: the forged proof survived an executor-reconstructed mint identity. \
         If the reconstruction no longer bites, the free pin IS a wire-level forgery."
    );
    eprintln!(
        "CONTROL — {name}: under the executor-reconstructed identity the same proof is REFUSED: {}",
        control.unwrap_err()
    );
}
