//! # `dregg-mina-finalize-scalars::v1` — Pickles' finalize conjuncts 3 and 4, in-AIR, both polarities.
//!
//! ## What this descriptor is
//!
//! The Wrap-side `ft_eval0` (C5: ζ-power ladder, `zkPolyR`, the witnessed inverse forced by a
//! `den·DINV = 1` gate, the two permutation folds), the FULL 47-entry `combined_inner_product`
//! ξ-fold (C8, with the in-AIR `ft_eval0` in slot 3), and `perm_scalars` (the `plonk_checks`
//! comparison list is `[perm]`) — 301 sound field ops at the Pallas-scalar prime, one op per row,
//! on the scheduled substrate (one-hot phase register, allocator-assigned value slots, complement
//! -masked carries). Lean-authored end to end (`MinaFinalizeScalars.lean`); this file parses,
//! proves and refuses. It authors nothing.
//!
//! ## ⚑ WHERE EACH FORCING LIVES — the table this suite measures
//!
//! * conjunct 3 (`cipCorrect`): IN-AIR here — the final eq gates compare the claimed cip against
//!   the trace's own ξ-fold. §3 is its refusal.
//! * conjunct 4 (`plonkChecksPassed`): IN-AIR here — the perm eq gates. §4 is its refusal.
//! * the 89 eval/challenge/prefix input blocks: AT THE FOLD (phase-2 chain / phase-1 chain /
//!   endo-lift instances / conjunction instances) — not this file's subject.
//! * ⚑⚑ the `LCT` port (the gate-linearization constant term): **WELDED TO NOTHING YET.** §5 is
//!   the measured exhibit — an adversarial trace that moves `LCT` and recomputes the cip claim
//!   PROVES AND VERIFIES. `cipActualOf` is affine in `LCT`, so until the gate-linearization leaf
//!   lands, the in-AIR cip check narrows the claim's SHAPE (a fold of the block's own welded
//!   evals at a ported constant) and does not bind its VALUE. Conjunct 3 must be reported with
//!   this sentence attached.
//!
//! ## The fixture is the real block
//!
//! Mina devnet block 539508's own Wrap wire: the 47-entry es columns at ζ and ζω, its raw β/γ,
//! mapped α/ζ/ξ/r, `combined_inner_product` from `proof.oracles(…)`, and o1-labs' own
//! `perm_scalars` value. The two claim decimals are pinned below against the Lean fixtures'
//! numbers (`MinaRealBlockGate.CIP`, `MinaWrapGroupGate.PERM_SCALAR`) — two sources, one value.
//!
//! ## Prerequisite — the witnesses
//!
//! The four 512×4461 traces (~9 MB each) are NOT tracked. Emit them (compiled):
//!
//! ```text
//! cd metatheory && lake build mina_finalize_scalars_emit
//! ./.lake/build/bin/mina_finalize_scalars_emit ../circuit/tests/fixtures
//! ```
//!
//! Run: `cargo test -p dregg-circuit --release --test mina_finalize_scalars_proves -- --nocapture`
//! (RELEASE, deliberately: algebraic refusals are `debug_assert` panics in debug and clean
//! `Err(..)` in release.)

use std::path::PathBuf;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    prove_vm_descriptor2_unchecked, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::refusal::assert_violated_constraint_not_bus;

/// The Lean-emitted layout, pinned. `MinaFinalizeScalars.fs_width_eq` / `fs_pi_count_eq` /
/// `fs_constraint_count` are the same numbers from the authoring side.
const NAME: &str = "dregg-mina-finalize-scalars::v1";
const WIDTH: usize = 4461;
const ROWS: usize = 512;
const PI_COUNT: usize = 3296;
const CONSTRAINTS: usize = 27319;
const SK: usize = 32;

/// PI block indices (value order — `MinaFinalizeScalars` §1).
const V_EZ5: usize = 5;
const V_CIPCL: usize = 99;
const V_PERMCL: usize = 100;
const V_LCT: usize = 102;

/// `MinaRealBlockGate.CIP` — the block's own `combined_inner_product` (Fq, decimal).
const CIP_DEC: &str =
    "4948131480779179767533860900716273683919559147195747550813387244823367375127";
/// `MinaWrapGroupGate.PERM_SCALAR` — o1-labs' own `perm_scalars` value on the same block.
const PERM_DEC: &str =
    "20751602151633737401462851548350130147491954693090596112024602804092692290009";

fn fixture_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

fn read_fixture(name: &str) -> String {
    let path = fixture_dir().join(name);
    std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "fixture {} missing ({e}).\nEmit the finalize-scalars artifacts first (COMPILED):\n  \
             cd metatheory && lake build mina_finalize_scalars_emit \\\n    \
             && ./.lake/build/bin/mina_finalize_scalars_emit ../circuit/tests/fixtures",
            path.display()
        )
    })
}

fn descriptor() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(&read_fixture("mina-finalize-scalars.json"))
        .expect("the Lean-emitted finalize-scalars descriptor parses")
}

fn trace(name: &str) -> Vec<Vec<BabyBear>> {
    let t: Vec<Vec<BabyBear>> = read_fixture(name)
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|c| BabyBear::new(c.parse::<u32>().expect("cell is a u32 decimal")))
                .collect()
        })
        .collect();
    assert_eq!(t.len(), ROWS, "the Lean-emitted trace is {ROWS} rows");
    assert!(
        t.iter().all(|r| r.len() == WIDTH),
        "every row is {WIDTH} wide"
    );
    t
}

fn pis(name: &str) -> Vec<BabyBear> {
    let p: Vec<BabyBear> = read_fixture(name)
        .split_whitespace()
        .map(|c| BabyBear::new(c.parse::<u32>().expect("PI limb is a u32 decimal")))
        .collect();
    assert_eq!(p.len(), PI_COUNT);
    p
}

/// Recompose a 32-limb base-2^8 PI block into a decimal string (big-number, no u128 overflow).
fn block_decimal(p: &[BabyBear], block: usize) -> String {
    // decimal big-int accumulator over limbs, most-significant first
    let mut acc: Vec<u32> = vec![0]; // little-endian base 1e9
    let push_mul_add = |acc: &mut Vec<u32>, mul: u64, add: u64| {
        let mut carry = add;
        for d in acc.iter_mut() {
            let v = (*d as u64) * mul + carry;
            *d = (v % 1_000_000_000) as u32;
            carry = v / 1_000_000_000;
        }
        while carry > 0 {
            acc.push((carry % 1_000_000_000) as u32);
            carry /= 1_000_000_000;
        }
    };
    for i in (0..SK).rev() {
        push_mul_add(&mut acc, 256, u64::from(p[SK * block + i].as_u32()));
    }
    let mut s = String::new();
    for (i, d) in acc.iter().rev().enumerate() {
        if i == 0 {
            s.push_str(&d.to_string());
        } else {
            s.push_str(&format!("{d:09}"));
        }
    }
    s
}

fn prove_and_verify_adversarial(
    d: &EffectVmDescriptor2,
    t: &[Vec<BabyBear>],
    p: &[BabyBear],
) -> Result<(), String> {
    let proof = prove_vm_descriptor2_unchecked(d, t, p, &MemBoundaryWitness::default(), &[])?;
    verify_vm_descriptor2(d, &proof, p)
}

// ============================================================================
// §0 — SHAPE, and the two claim decimals against their Lean sources.
// ============================================================================

#[test]
fn the_descriptor_declares_what_the_lean_file_proves() {
    let d = descriptor();
    assert_eq!(d.name, NAME);
    assert_eq!(d.trace_width, WIDTH);
    assert_eq!(d.public_input_count, PI_COUNT);
    assert_eq!(
        d.constraints.len(),
        CONSTRAINTS,
        "the constraint census moved; re-pin `fs_constraint_count` and this test together"
    );
    println!("\n§0 {NAME}: {WIDTH} cols x {ROWS} rows, {PI_COUNT} PIs, {CONSTRAINTS} constraints");
}

#[test]
fn the_honest_claims_are_the_blocks_own_numbers() {
    let p = pis("mina-finalize-scalars-pis.txt");
    assert_eq!(
        block_decimal(&p, V_CIPCL),
        CIP_DEC,
        "the cip claim block must recompose to the block's own combined_inner_product"
    );
    assert_eq!(
        block_decimal(&p, V_PERMCL),
        PERM_DEC,
        "the perm claim block must recompose to o1-labs' own perm_scalars value"
    );
    println!("§0b the two claim blocks ARE proof.oracles' cip and perm_scalars, limb-recomposed.");
}

// ============================================================================
// §1 — FALSIFIER INTEGRITY, before any verdict is read.
// ============================================================================

#[test]
fn the_eval_falsifier_moves_the_wire_and_keeps_the_claims() {
    let honest = trace("mina-finalize-scalars-trace.txt");
    let forged = trace("mina-finalize-scalars-forged-eval-trace.txt");
    let hp = pis("mina-finalize-scalars-pis.txt");
    let fp = pis("mina-finalize-scalars-forged-eval-pis.txt");

    // The PI delta lives entirely inside EZ_5's block (a `+1` can carry across limbs), and it
    // is non-empty — the falsifier is checked to falsify before any verdict is read.
    let moved_pi: Vec<usize> = (0..PI_COUNT).filter(|&i| hp[i] != fp[i]).collect();
    assert!(!moved_pi.is_empty(), "the forgery moved nothing");
    assert!(
        moved_pi
            .iter()
            .all(|&i| (SK * V_EZ5..SK * (V_EZ5 + 1)).contains(&i)),
        "the forgery must move only EZ_5's limbs, moved: {moved_pi:?}"
    );
    // …and the claims are untouched.
    assert_eq!(block_decimal(&fp, V_CIPCL), CIP_DEC);
    assert_eq!(block_decimal(&fp, V_PERMCL), PERM_DEC);

    // The trace delta is real and in-width: the bumped input propagates through the fold.
    let mut moved_cells = 0usize;
    for (hr, fr) in honest.iter().zip(forged.iter()) {
        for (hc, fc) in hr.iter().zip(fr.iter()) {
            if hc != fc {
                moved_cells += 1;
            }
        }
    }
    assert!(
        moved_cells > 1000,
        "a bumped eval must propagate through the ξ-fold; {moved_cells} moved cells is a no-op \
         falsifier"
    );
    let max_cell = forged
        .iter()
        .flat_map(|r| r.iter())
        .map(|c| c.as_u32())
        .max()
        .unwrap();
    assert!(
        max_cell < (1 << 16) + (1 << 15),
        "every forged cell stays inside the declared widths (max {max_cell}); a range lookup must \
         not be what refuses"
    );
    println!(
        "§1 falsifier integrity: 1 PI limb moved, {moved_cells} trace cells follow, all in-width."
    );
}

// ============================================================================
// §2 — THE ACCEPT POLE.
// ============================================================================

#[test]
fn the_honest_trace_proves_and_verifies() {
    let d = descriptor();
    let t = trace("mina-finalize-scalars-trace.txt");
    let p = pis("mina-finalize-scalars-pis.txt");
    let t0 = std::time::Instant::now();
    let proof = prove_vm_descriptor2(&d, &t, &p, &MemBoundaryWitness::default(), &[])
        .expect("the real block's finalize scalars prove");
    verify_vm_descriptor2(&d, &proof, &p).expect("and verify");
    println!(
        "\n§2 ⚑ conjuncts 3 and 4 PROVE on block 539508's own wire ({} ms).",
        t0.elapsed().as_millis()
    );
}

// ============================================================================
// §3/§4 — THE REFUSE POLES, named and the AIR's.
// ============================================================================

#[test]
fn a_moved_eval_is_refused_by_the_cip_equality() {
    let d = descriptor();
    let t = trace("mina-finalize-scalars-forged-eval-trace.txt");
    let p = pis("mina-finalize-scalars-forged-eval-pis.txt");
    let err = prove_and_verify_adversarial(&d, &t, &p)
        .expect_err("a moved eval with the original cip claim must be refused");
    assert_violated_constraint_not_bus("finalize-scalars eval forgery", &err);
    println!("§3 refusal: {err}");
}

#[test]
fn a_moved_perm_claim_is_refused_by_the_perm_equality() {
    let d = descriptor();
    let t = trace("mina-finalize-scalars-forged-perm-trace.txt");
    let p = pis("mina-finalize-scalars-forged-perm-pis.txt");
    let err =
        prove_and_verify_adversarial(&d, &t, &p).expect_err("a moved perm claim must be refused");
    assert_violated_constraint_not_bus("finalize-scalars perm forgery", &err);
    println!("§4 refusal: {err}");
}

// ============================================================================
// §5 — ⚑⚑ THE PORT EXHIBIT: the LCT family PROVES. Labeled, measured, not hidden.
// ============================================================================

/// ⚑ An adversarial trace that bumps `LCT` and RECOMPUTES the cip claim to match is ACCEPTED —
/// two verifying proofs of this descriptor whose cip claims differ. That is the `LCT` port's
/// one-parameter family, exhibited the way `the_transcript_ordered_chain_and_its_shift_both_prove`
/// exhibits the `delta` orbit. The closure is the gate-linearization leaf (`gateLinConst` over
/// the same welded eval blocks); until it lands, no report may call conjunct 3 "closed" without
/// naming this family.
#[test]
fn the_lct_port_admits_a_shifted_accepting_claim() {
    let d = descriptor();
    let t = trace("mina-finalize-scalars-lct-shift-trace.txt");
    let p = pis("mina-finalize-scalars-lct-shift-pis.txt");
    // The exhibit's integrity: the LCT block moved, the cip claim moved WITH it.
    let hp = pis("mina-finalize-scalars-pis.txt");
    assert_ne!(
        block_decimal(&p, V_LCT),
        block_decimal(&hp, V_LCT),
        "the exhibit must actually move the port"
    );
    assert_ne!(
        block_decimal(&p, V_CIPCL),
        CIP_DEC,
        "the shifted family's cip claim must differ from the block's"
    );
    prove_and_verify_adversarial(&d, &t, &p)
        .expect("⚑ the shifted-LCT trace PROVES — the port is open until the linearization leaf");
    println!(
        "\n§5 ⚑⚑ THE PORT, MEASURED: two accepting cip claims, one block, differing only in LCT."
    );
}
