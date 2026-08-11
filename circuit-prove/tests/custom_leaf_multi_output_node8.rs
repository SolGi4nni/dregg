//! **Multi-output chip sites lower into a foldable custom leaf** — the `MerkleHash8`
//! (native 8-felt `cap_node8`, arity-16) carrier, driven.
//!
//! ## The gap this closes
//!
//! `custom_leaf_lowering` REFUSED `ConstraintExpr::MerkleHash8` on the stated ground that
//! "this IR-v2 chip adapter carries single-output (out0) chip sites only". That refusal was
//! an ADAPTER limitation, never a soundness boundary:
//!
//! * the `TID_P2` chip tuple was ALWAYS 8-output on the wire
//!   (`CHIP_TUPLE_LEN = 1 + CHIP_RATE + 8`);
//! * the chip-table AIR ALWAYS equality-bound `out0..out7` to the genuine `perm(ins)[0..8]`;
//! * arity 16 was ALREADY in the chip AIR's arity set `{0,2,3,4,7,11,16}`, already seeds all
//!   16 permutation lanes from genuine inputs, and the chip table already mints node8 rows;
//! * `cap_root::cap_node8(L8, R8)` is DEFINED as
//!   `chip_absorb_all_lanes(CHIP_NODE8_ARITY, L8 ‖ R8)` — literally one arity-16 chip absorb.
//!
//! The ONLY blocker was `chip_lookup_site` hard-coding "lane 0 is the output, lanes 1..7 are
//! anonymous witnesses". Teaching it a `ChipOut::Lanes8` shape lets a multi-output site hand
//! all 8 lanes to PROGRAM-OWNED columns.
//!
//! ## Why it matters (the ~31-bit → ~124-bit flip)
//!
//! A leaf that must FOLD an 8-felt Merkle tree had only single-output hashes, whose lane-0
//! digest is ~31 bits — a 2^31 second-preimage, i.e. minutes of grinding. The workaround is
//! W parallel domain-separated chains (param-compose's route: 8 lanes × 46 blocks = 368
//! `Hash4to1` sites, 400 columns vs 50 at W=1 — the +350). A multi-output site reaches the
//! same ~124-bit floor as ONE site costing ZERO extra columns.
//!
//! ## The carrier driven here
//!
//! [`dregg_circuit::dsl::cap_membership`] — a REAL deployed-shape program (the standalone
//! capability-membership leg, `CanonicalCapTree` since Phase H-CAP-8), not a synthetic. Its
//! ONLY fold blocker was this refusal: 16 rows (one per tree level), 33 columns
//! `[cur8, left8, right8, parent8, dir]`, one `MerkleHash8` per row, `Transition` chain
//! continuity, and 16-felt PIs `[leaf_digest(8) ‖ cap_root(8)]`.

use std::collections::HashMap;

use dregg_circuit::cap_root::{CAP_DIGEST_W, CAP_TREE_DEPTH, cap_node8};
use dregg_circuit::custom_leaf_lowering::cellprogram_to_descriptor2;
use dregg_circuit::descriptor_ir2::{
    CHIP_NODE8_ARITY, CHIP_OUT_LANES, CHIP_RATE, CHIP_TUPLE_LEN, TID_P2, VmConstraint2,
};
use dregg_circuit::dsl::cap_membership::{
    cap_membership_circuit_descriptor, col, generate_cap_membership_trace,
};
use dregg_circuit::dsl::circuit::{CellProgram, CircuitDescriptor, ConstraintExpr};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::LeanExpr;
use dregg_circuit::refusal::{assert_violated_constraint_not_bus, must_refuse_or_unsat_panic};
use dregg_circuit_prove::binding_tooth::report_refusal;
use dregg_circuit_prove::custom_leaf_adapter::{
    prove_custom_leaf, prove_custom_leaf_with_commitment, read_exposed_pi_commitment,
};
use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;

// ============================================================================
// witness helpers
// ============================================================================

/// Turn a raw `cap_membership` trace into the `column-name -> per-row values` witness map
/// `CellProgram::generate_trace` consumes.
fn witness_from_trace(desc: &CircuitDescriptor, trace: &[Vec<BabyBear>]) -> WitnessMap {
    let mut w: WitnessMap = HashMap::new();
    for c in &desc.columns {
        w.insert(
            c.name.clone(),
            trace.iter().map(|row| row[c.index]).collect(),
        );
    }
    w
}

type WitnessMap = HashMap<String, Vec<BabyBear>>;

/// An 8-felt digest from a small seed (distinct lanes, so a lane-0-only binding would be
/// visibly weaker than an 8-lane one).
fn digest8(seed: u32) -> [BabyBear; CAP_DIGEST_W] {
    core::array::from_fn(|i| BabyBear::new(seed.wrapping_mul(1000).wrapping_add(i as u32) + 1))
}

/// An honest `CAP_TREE_DEPTH`-level path: distinct 8-felt siblings, alternating directions.
fn honest_path() -> (
    [BabyBear; CAP_DIGEST_W],
    Vec<[BabyBear; CAP_DIGEST_W]>,
    Vec<u8>,
) {
    let leaf = digest8(7);
    let sibs: Vec<[BabyBear; CAP_DIGEST_W]> = (0..CAP_TREE_DEPTH)
        .map(|l| digest8(100 + l as u32))
        .collect();
    let dirs: Vec<u8> = (0..CAP_TREE_DEPTH).map(|l| (l % 2) as u8).collect();
    (leaf, sibs, dirs)
}

/// The honest cap-membership program + witness + PIs, ready for `prove_custom_leaf`.
fn honest_cap_membership() -> (CellProgram, WitnessMap, Vec<BabyBear>) {
    let desc = cap_membership_circuit_descriptor();
    let (leaf, sibs, dirs) = honest_path();
    let (trace, pis) = generate_cap_membership_trace(leaf, &sibs, &dirs).expect("honest path");
    let w = witness_from_trace(&desc, &trace);
    (CellProgram::new(desc, 1), w, pis)
}

// ============================================================================
// 1. THE LOWERING — a multi-output site is ONE arity-16 chip lookup, costing NOTHING
// ============================================================================

/// `MerkleHash8` lowers to exactly ONE `TID_P2` chip lookup per site, at arity 16, whose
/// tuple is `[16, left8 ‖ right8, parent8]` — all 8 outputs PROGRAM-OWNED, so the lowered
/// trace width is the program's OWN width: a multi-output site allocates ZERO lane columns.
#[test]
fn merkle_hash8_lowers_to_one_arity16_chip_site_costing_zero_columns() {
    let desc = cap_membership_circuit_descriptor();
    let base_width = desc.trace_width;
    let program = CellProgram::new(desc, 1);
    let desc2 = cellprogram_to_descriptor2(&program).expect("MerkleHash8 must now lower");

    // THE PAYOFF: zero lane columns. A single-output site would have cost 7 EACH.
    assert_eq!(
        desc2.trace_width, base_width,
        "a multi-output site is free: all 8 lanes are program-owned columns"
    );

    let chip: Vec<_> = desc2
        .constraints
        .iter()
        .filter_map(|c| match c {
            VmConstraint2::Lookup(l) if l.table == TID_P2 => Some(l),
            _ => None,
        })
        .collect();
    // The program is one ROW per tree level, so the per-row node8 site is ONE constraint
    // firing on all `CAP_TREE_DEPTH` rows — one chip lookup in the descriptor, 16 absorbs.
    assert_eq!(
        chip.len(),
        1,
        "the per-row node8 site is exactly one chip lookup"
    );

    for l in &chip {
        assert_eq!(l.tuple.len(), CHIP_TUPLE_LEN);
        // arity tag = 16 (the full-width node8 compression).
        assert!(
            matches!(l.tuple[0], LeanExpr::Const(a) if a == CHIP_NODE8_ARITY as i64),
            "node8 rides the arity-16 chip row"
        );
        // ins = left8 ‖ right8, seeding all 16 lanes with GENUINE inputs (no padding,
        // no arity-tag lane) — byte-identical to `cap_node8`'s `chip_absorb_all_lanes`.
        for i in 0..CAP_DIGEST_W {
            assert!(
                matches!(l.tuple[1 + i], LeanExpr::Var(c) if c == col::LEFT + i),
                "chip input {i} must be left8[{i}]"
            );
            assert!(
                matches!(l.tuple[1 + CAP_DIGEST_W + i], LeanExpr::Var(c) if c == col::RIGHT + i),
                "chip input {} must be right8[{i}]",
                CAP_DIGEST_W + i
            );
        }
        assert_eq!(
            CHIP_RATE, CHIP_NODE8_ARITY,
            "arity 16 exactly fills the rate"
        );
        // ALL 8 outputs are the program's own parent8 columns — this is the ~124-bit bind.
        for i in 0..CHIP_OUT_LANES {
            assert!(
                matches!(l.tuple[1 + CHIP_RATE + i], LeanExpr::Var(c) if c == col::PARENT + i),
                "chip output lane {i} must be the program's parent8[{i}] column, \
                 not an anonymous witness — THIS is what makes the digest 8-felt"
            );
        }
    }
}

/// **The ~124-bit claim, made concrete.** The site binds all 8 genuine permutation lanes,
/// and those lanes are DISTINCT and each ~31 bits — so the per-node collision floor is the
/// full 8-felt width, not lane 0 alone. A lane-0-only bind would let any of the 2^31-ish
/// preimages sharing lane 0 pass; binding 8 lanes needs a genuine 8-felt collision.
#[test]
fn node8_digest_is_eight_genuine_felts_not_a_lane0_projection() {
    let l = digest8(1);
    let r = digest8(2);
    let out = cap_node8(l, r);

    // All 8 lanes are genuinely distinct — the digest carries ~8×31 bits of entropy, so the
    // birthday floor is ~124 bits (the deployed FRI/STARK posture), not ~15.5.
    for i in 0..CAP_DIGEST_W {
        for j in (i + 1)..CAP_DIGEST_W {
            assert_ne!(
                out[i], out[j],
                "lanes {i}/{j} must be distinct permutation lanes"
            );
        }
    }
    // Flipping ONE input lane moves EVERY output lane (so no output lane is a passthrough).
    let mut r2 = r;
    r2[3] = r2[3] + BabyBear::new(1);
    let out2 = cap_node8(l, r2);
    for i in 0..CAP_DIGEST_W {
        assert_ne!(out[i], out2[i], "output lane {i} must depend on the inputs");
    }

    // And the site the lowering emits binds EVERY one of those lanes (not just out0):
    // the tuple's 8 output slots are 8 DISTINCT program columns.
    let program = CellProgram::new(cap_membership_circuit_descriptor(), 1);
    let desc2 = cellprogram_to_descriptor2(&program).expect("lowers");
    let l0 = desc2
        .constraints
        .iter()
        .find_map(|c| match c {
            VmConstraint2::Lookup(l) if l.table == TID_P2 => Some(l),
            _ => None,
        })
        .expect("a chip site");
    let outs: Vec<usize> = (0..CHIP_OUT_LANES)
        .map(|i| match l0.tuple[1 + CHIP_RATE + i] {
            LeanExpr::Var(c) => c,
            _ => panic!("output lane {i} must be a bare column"),
        })
        .collect();
    let uniq: std::collections::BTreeSet<_> = outs.iter().collect();
    assert_eq!(
        uniq.len(),
        CHIP_OUT_LANES,
        "8 DISTINCT bound output columns"
    );
}

// ============================================================================
// 2. SINGLE-OUTPUT LOWERING IS UNCHANGED
// ============================================================================

/// The single-output shape is UNTOUCHED by the multi-output extension: a `Hash2to1` site
/// still emits `[2, a, b, 0…, Var(out0), Var(lane_base..lane_base+6)]` with the 7 lane
/// columns allocated past the base width. The expected tuple is built BY HAND here (not by
/// calling the lowering's own helper), so this is an independent check of the shape, not a
/// tautology.
#[test]
fn single_output_lowering_is_byte_identical() {
    use dregg_circuit::dsl::circuit::{BoundaryDef, BoundaryRow, ColumnDef, ColumnKind};

    let base_width = 3usize; // a, b, out
    let desc = CircuitDescriptor {
        name: "single-output-shape-probe".into(),
        trace_width: base_width,
        max_degree: 7,
        columns: vec![
            ColumnDef {
                name: "a".into(),
                index: 0,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "b".into(),
                index: 1,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "out".into(),
                index: 2,
                kind: ColumnKind::Hash,
            },
        ],
        constraints: vec![ConstraintExpr::Hash2to1 {
            output_col: 2,
            input_col_a: 0,
            input_col_b: 1,
        }],
        boundaries: vec![BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: 2,
            pi_index: 0,
        }],
        public_input_count: 1,
        lookup_tables: vec![],
    };
    let program = CellProgram::new(desc, 1);
    let desc2 = cellprogram_to_descriptor2(&program).expect("single-output lowers");

    // Still +7 columns for the one site (lanes 1..7), exactly as before.
    assert_eq!(desc2.trace_width, base_width + (CHIP_OUT_LANES - 1));

    let l = desc2
        .constraints
        .iter()
        .find_map(|c| match c {
            VmConstraint2::Lookup(l) if l.table == TID_P2 => Some(l),
            _ => None,
        })
        .expect("one chip lookup");

    // The hand-built expected tuple: [2, a, b, 0×(RATE-2), out0, lane1..lane7].
    let mut expected: Vec<LeanExpr> = vec![LeanExpr::Const(2)];
    expected.push(LeanExpr::Var(0));
    expected.push(LeanExpr::Var(1));
    for _ in 2..CHIP_RATE {
        expected.push(LeanExpr::Const(0));
    }
    expected.push(LeanExpr::Var(2)); // out0 = the program's digest column
    for j in 0..(CHIP_OUT_LANES - 1) {
        expected.push(LeanExpr::Var(base_width + j)); // freshly allocated lanes 1..7
    }
    assert_eq!(
        l.tuple, expected,
        "the single-output tuple shape must be byte-identical to the pre-extension lowering"
    );
}

// ============================================================================
// 3. THE COLUMN PAYOFF — one multi-output site vs the 8-chain workaround
// ============================================================================

/// **The measured delta.** To reach a ~124-bit digest a foldable leaf must either use ONE
/// multi-output `MerkleHash8` site (this change) or W=8 parallel domain-separated
/// single-output chains (the deployed workaround). This measures both at the SAME statement
/// (a `CAP_TREE_DEPTH`-level 8-felt Merkle path) through the SAME lowering.
#[test]
fn column_payoff_one_node8_site_vs_eight_single_output_chains() {
    use dregg_circuit::dsl::circuit::{ColumnDef, ColumnKind};

    // --- (a) the multi-output route: cap_membership as it stands, one MerkleHash8/level.
    let node8_desc = cap_membership_circuit_descriptor();
    let node8_base = node8_desc.trace_width;
    let node8_program = CellProgram::new(node8_desc, 1);
    let node8_lowered = cellprogram_to_descriptor2(&node8_program).expect("node8 lowers");
    let node8_sites = node8_lowered
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
        .count();

    // --- (b) the 8-chain workaround: to bind 8 felts of parent with SINGLE-output sites you
    // need 8 domain-separated `Hash4to1` sites per level (one per lane), each squeezing its
    // own lane-0 digest into its own output column. Build that shape and lower it.
    let mut columns: Vec<ColumnDef> = Vec::new();
    let mut constraints: Vec<ConstraintExpr> = Vec::new();
    let mut w = 0usize;
    let newcol = |columns: &mut Vec<ColumnDef>, w: &mut usize, name: String| -> usize {
        let i = *w;
        columns.push(ColumnDef {
            name,
            index: i,
            kind: ColumnKind::Value,
        });
        *w += 1;
        i
    };
    // cur8 / left8 / right8 / parent8 / dir — the SAME state the node8 route carries.
    let mut chain_cols = Vec::new();
    for tag in ["cur", "left", "right", "parent"] {
        for i in 0..CAP_DIGEST_W {
            chain_cols.push(newcol(&mut columns, &mut w, format!("{tag}{i}")));
        }
    }
    let _dir = newcol(&mut columns, &mut w, "dir".into());
    let left_base = CAP_DIGEST_W;
    let right_base = 2 * CAP_DIGEST_W;
    let parent_base = 3 * CAP_DIGEST_W;
    // Per output lane: one Hash4to1 site absorbing 4 of the 16 child felts. A REAL 8-felt
    // bind over 16 inputs needs the whole preimage per lane, so each lane runs a CHAIN of
    // ceil(16/3) = 6 blocks (3 felts absorbed per block alongside the rolling accumulator) —
    // the param-compose `wide_chain` shape: 1 IV column + 1 output column per block.
    const BLOCKS: usize = 6;
    for lane in 0..CAP_DIGEST_W {
        let iv = newcol(&mut columns, &mut w, format!("l{lane}_iv"));
        let mut acc = iv;
        for b in 0..BLOCKS {
            let out = newcol(&mut columns, &mut w, format!("l{lane}_b{b}"));
            let f = |k: usize| -> usize {
                let idx = (b * 3 + k) % (2 * CAP_DIGEST_W);
                if idx < CAP_DIGEST_W {
                    left_base + idx
                } else {
                    right_base + idx - CAP_DIGEST_W
                }
            };
            constraints.push(ConstraintExpr::Hash4to1 {
                output_col: out,
                input_cols: [acc, f(0), f(1), f(2)],
            });
            acc = out;
        }
        // the lane's final block IS that lane of the parent digest.
        constraints.push(ConstraintExpr::Equality {
            col_a: acc,
            col_b: parent_base + lane,
        });
    }
    let chains_desc = CircuitDescriptor {
        name: "eight-chain-workaround".into(),
        trace_width: w,
        max_degree: 7,
        columns,
        constraints,
        boundaries: vec![],
        public_input_count: 0,
        lookup_tables: vec![],
    };
    let chains_base = chains_desc.trace_width;
    let chains_program = CellProgram::new(chains_desc, 1);
    let chains_lowered = cellprogram_to_descriptor2(&chains_program).expect("chains lower");
    let chains_sites = chains_lowered
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
        .count();

    eprintln!(
        "
  ~124-bit binding of ONE 8-felt Merkle level, two routes:

    multi-output (MerkleHash8, THIS change):
      program columns   {node8_base}
      lowered width     {n8w}  (+{n8lanes} lane columns)
      chip sites/row    {node8_sites}  (arity 16; {depth} rows = {depth} absorbs)

    8-chain workaround (single-output Hash4to1, the deployed route):
      program columns   {chains_base}
      lowered width     {chw}  (+{chlanes} lane columns)
      chip sites/row    {chains_sites}  (arity 4; 8 lanes x 6 blocks)

    delta for the same ~124-bit bind:  {dcols} columns, {dsites} chip sites
",
        node8_base = node8_base,
        n8w = node8_lowered.trace_width,
        n8lanes = node8_lowered.trace_width - node8_base,
        node8_sites = node8_sites,
        depth = CAP_TREE_DEPTH,
        chains_base = chains_base,
        chw = chains_lowered.trace_width,
        chlanes = chains_lowered.trace_width - chains_base,
        chains_sites = chains_sites,
        dcols = chains_lowered.trace_width as i64 - node8_lowered.trace_width as i64,
        dsites = chains_sites as i64 - node8_sites as i64,
    );

    // The multi-output route allocates NO lane columns at all.
    assert_eq!(node8_lowered.trace_width, node8_base);
    // The 8-chain route pays 7 lane columns for EVERY one of its 48 sites, on top of its
    // own IV + block columns — and buys the same ~124 bits.
    assert_eq!(
        chains_lowered.trace_width - chains_base,
        chains_sites * (CHIP_OUT_LANES - 1)
    );
    assert!(
        chains_lowered.trace_width > node8_lowered.trace_width * 4,
        "the 8-chain workaround must be dramatically wider for the same binding"
    );
}

// ============================================================================
// 4. DRIVEN — proves, folds, verifies (SLOW: `--ignored`)
// ============================================================================

/// **THE POSITIVE POLE.** The honest `cap_membership` path — a REAL 8-felt `cap_node8`
/// Merkle tree, ~124-bit per node — PROVES as a foldable IR-v2 leaf and its recursion wrap
/// VERIFIES. Before this change `lower_cellprogram` returned `Err` and this leaf could not
/// exist at all: a pure light client folding the per-turn tree could never witness an 8-felt
/// capability-membership leg.
#[test]
#[ignore = "slow: full IR-v2 prove + recursion leaf wrap (run with --ignored)"]
fn honest_node8_cap_membership_proves_folds_and_verifies() {
    let (program, w, pis) = honest_cap_membership();
    assert_eq!(
        pis.len(),
        2 * CAP_DIGEST_W,
        "[leaf_digest(8) ‖ cap_root(8)]"
    );
    let config = ir2_leaf_wrap_config();
    // FOLDS + VERIFIES: the leaf wrap performs the in-circuit FRI verify of the inner IR-v2
    // batch and balances the WitnessChecks bus — a leaf that did not fold would error here.
    prove_custom_leaf(&program, &w, CAP_TREE_DEPTH, &pis, &config)
        .expect("the honest 8-felt cap-membership path must prove + fold as a custom leaf");
}

/// **The fold contract is UNWEAKENED.** The multi-output site changes only the leaf's
/// INTERNAL constraints; the leaf's exposed claim still binds exactly what it bound before —
/// the in-circuit PI commitment over the leaf's REAL bound descriptor PIs, byte-for-byte
/// equal to the host `custom_proof_pi_commitment` the deployed-default state node connects
/// as `[commitment(8) ‖ pis[0..16]]`. A node8 leaf is connected by the SAME node, with the
/// SAME 8-felt commitment, over the SAME 16 PIs.
#[test]
#[ignore = "slow: full IR-v2 prove + recursion leaf wrap (run with --ignored)"]
fn node8_leaf_exposes_the_same_pi_commitment_the_node_connects() {
    let (program, w, pis) = honest_cap_membership();
    assert_eq!(
        pis.len(),
        2 * CAP_DIGEST_W,
        "[leaf_digest(8) ‖ cap_root(8)]"
    );
    let config = ir2_leaf_wrap_config();
    let out = prove_custom_leaf_with_commitment(&program, &w, CAP_TREE_DEPTH, &pis, &config)
        .expect("the node8 leaf must prove with its PI commitment exposed");
    let exposed = read_exposed_pi_commitment(&out).expect("the leaf exposes an 8-felt claim");
    let host = custom_proof_pi_commitment(&pis);
    assert_eq!(
        exposed, host,
        "the node8 leaf's in-circuit claim must equal the host commitment over its 16 PIs — \
         the fold contract binds exactly what it bound before"
    );
}

/// **THE NEGATIVE POLE.** A tampered INPUT to the multi-output site (a forged 8-felt
/// sibling) is REFUSED. The forged level's `parent8` no longer equals
/// `cap_node8(left8, right8)`, so the chip lookup's `out[i] == perm(ins)[i]` equalities have
/// no serving chip row — and the honest root PI is still pinned. The site is load-bearing.
#[test]
#[ignore = "slow: full IR-v2 prove + recursion leaf wrap (run with --ignored)"]
fn forged_sibling_into_the_node8_site_is_refused() {
    let (program, mut w, pis) = honest_cap_membership();
    // FORGE: corrupt ONE lane of the level-1 sibling without recomputing parents/chain.
    // dirs[1] = 1 ⇒ at level 1 the sibling sits in the LEFT slot.
    let v = w.get_mut("left0").expect("left0 column");
    v[1] = v[1] + BabyBear::new(1);
    let config = ir2_leaf_wrap_config();
    let refusal = must_refuse_or_unsat_panic("a FORGED 8-felt sibling into the node8 site", || {
        prove_custom_leaf(&program, &w, CAP_TREE_DEPTH, &pis, &config)
    });
    // NAME THE REFUSAL, MEASURED FIRST (2026-08-10, --release, this exact fixture):
    //   OodEvaluationMismatch { index: Some(0) }
    // The bare `must_refuse_or_unsat_panic` here DISCARDED its result, so an FRI fault, an OOM
    // or a trace-shape error read identically to the forgery being caught. The subject is
    // a violated CONSTRAINT (`OodEvaluationMismatch` deployed / `constraints not
    // satisfied on row` in debug): the node8 site's lane pins are emitted gates.
    report_refusal(
        "a FORGED 8-felt sibling into the node8 site",
        &refusal.reason(),
    );
    assert_violated_constraint_not_bus(
        "a FORGED 8-felt sibling into the node8 site",
        &refusal.reason(),
    );
}

/// **THE CANARY — the multi-output site is what refuses the forgery.** Neuter it (drop the
/// `MerkleHash8` constraint, leaving every OTHER constraint of the program intact) and the
/// SAME forged witness that was just refused now FOLDS: with nothing tying `parent8` to
/// `cap_node8(left8, right8)`, a prover picks the honest parents and the forged sibling is
/// free. So the refusal above is the SITE's doing, not the boundary pins' or the chain's.
///
/// This is the proof-integrity discipline: a green refusal means nothing until you show the
/// gate is what produced it.
#[test]
#[ignore = "slow: full IR-v2 prove + recursion leaf wrap (run with --ignored)"]
fn canary_neutering_the_node8_site_lets_the_forgery_fold() {
    // The neutered program: cap_membership MINUS its MerkleHash8 sites.
    let mut desc = cap_membership_circuit_descriptor();
    let before = desc.constraints.len();
    desc.constraints
        .retain(|c| !matches!(c, ConstraintExpr::MerkleHash8 { .. }));
    assert_eq!(
        before - desc.constraints.len(),
        1,
        "exactly the one MerkleHash8 site is neutered; every other constraint stays"
    );
    let neutered = CellProgram::new(desc, 1);

    // The SAME forged witness the load-bearing test refuses. `parent8` keeps its HONEST
    // values (so the chain + root pin still hold); only the sibling is forged.
    let real_desc = cap_membership_circuit_descriptor();
    let (leaf, sibs, dirs) = honest_path();
    let (trace, pis) = generate_cap_membership_trace(leaf, &sibs, &dirs).expect("honest path");
    let mut w = witness_from_trace(&real_desc, &trace);
    let v = w.get_mut("left0").expect("left0 column");
    v[1] = v[1] + BabyBear::new(1);

    let config = ir2_leaf_wrap_config();
    prove_custom_leaf(&neutered, &w, CAP_TREE_DEPTH, &pis, &config).expect(
        "CANARY: with the node8 site neutered the forged sibling MUST fold — if this fails, \
         the refusal in `forged_sibling_into_the_node8_site_is_refused` is coming from some \
         OTHER constraint and the multi-output site is not load-bearing",
    );
}
