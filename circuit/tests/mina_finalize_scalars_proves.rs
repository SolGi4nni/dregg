//! # `dregg-mina-finalize-scalars::v2` — Pickles' finalize conjuncts 3 and 4, in-AIR, both
//! polarities — and the `lct-shift` falsifier REFUSED.
//!
//! ## What this descriptor is
//!
//! The Wrap-side `ft_eval0` (C5: ζ-power ladder, `zkPolyR`, the witnessed inverse forced by a
//! `den·DINV = 1` gate, the two permutation folds), the FULL 47-entry `combined_inner_product`
//! ξ-fold (C8, with the in-AIR `ft_eval0` in slot 3), `perm_scalars` (the `plonk_checks`
//! comparison list is `[perm]`) — **and, new at v2, `gateLinConst`'s six transcribed gate
//! bodies, whose closing eq gate forces the `LCT` claim block against the trace's own
//! derivation** — 1046 sound field ops at the Pallas-scalar prime, one op per row, on the
//! scheduled substrate. Lean-authored end to end (`MinaFinalizeScalarsProg.lean` +
//! `MinaFinalizeScalars.lean`); this file parses, proves and refuses. It authors nothing.
//!
//! ## ⚑ WHERE EACH FORCING LIVES — the table this suite measures
//!
//! * conjunct 3 (`cipCorrect`): IN-AIR here, WHOLE — the final eq gates compare the claimed cip
//!   against the trace's own ξ-fold, whose `ft_eval0` slot is computed in-AIR and whose `LCT`
//!   subtraction is forced by the stage-11 gate-linearization eq. §3 and §5 are its refusals.
//! * conjunct 4 (`plonkChecksPassed`): IN-AIR here — the perm eq gates. §4 is its refusal.
//! * the 89 eval/challenge/prefix input blocks: AT THE FOLD (phase-2 chain / phase-1 chain /
//!   endo-lift instances / conjunction instances) — not this file's subject.
//! * ⚑⚑ the `LCT` claim: **FORCED IN-AIR by stage 11.** Through `d09e89817` (v1) the `lct-shift`
//!   trace — `LCT` bumped, cip claim recomputed — PROVED AND VERIFIED, the port's one-parameter
//!   family of accepting claims. §5 now measures that exact family REFUSED, falsifier integrity
//!   asserted before the verdict.
//!
//! ## The fixture is the real block
//!
//! Mina devnet block 539508's own Wrap wire: the 47-entry es columns at ζ and ζω, its raw β/γ,
//! mapped α/ζ/ξ/r, `combined_inner_product` from `proof.oracles(…)`, o1-labs' own
//! `perm_scalars` value, and the block's own linearization constant term. The three claim
//! decimals are pinned below against the Lean fixtures' numbers (`MinaRealBlockGate.CIP`,
//! `MinaWrapGroupGate.PERM_SCALAR`, `MinaRealBlockGate.LCT`) — two sources, one value each.
//!
//! ## Prerequisite — the witnesses
//!
//! The four 2048×WIDTH traces (tens of MB each) are NOT tracked. Emit them (compiled):
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
const NAME: &str = "dregg-mina-finalize-scalars::v2";
const WIDTH: usize = 5750;
const ROWS: usize = 2048;
const PI_COUNT: usize = 3296;
const CONSTRAINTS: usize = 64324;
const SK: usize = 32;

/// PI block indices (value order — `MinaFinalizeScalarsProg` §1).
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
/// `MinaRealBlockGate.LCT` — the block's own `PolishToken::evaluate(constant_term)`, the value
/// stage 11's eq gate forces the `LCT` claim to be.
const LCT_DEC: &str =
    "7793608285860009894060515823405052926352109106930816519423248903121210044125";

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
// §0 — SHAPE, and the three claim decimals against their Lean sources.
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
    assert_eq!(
        block_decimal(&p, V_LCT),
        LCT_DEC,
        "the LCT claim block must recompose to the block's own linearization constant term"
    );
    println!(
        "§0b the three claim blocks ARE proof.oracles' cip, perm_scalars and the block's LCT, \
         limb-recomposed."
    );
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
    assert_eq!(block_decimal(&fp, V_LCT), LCT_DEC);

    // The trace delta is real and in-width: the bumped input propagates through the fold and
    // (at v2) through the gate-linearization bodies.
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
        "\n§2 ⚑ conjuncts 3 and 4 PROVE on block 539508's own wire, gate-linearization included \
         ({} ms).",
        t0.elapsed().as_millis()
    );
}

// ============================================================================
// §3/§4 — THE REFUSE POLES, named and the AIR's.
// ============================================================================

#[test]
fn a_moved_eval_is_refused() {
    let d = descriptor();
    let t = trace("mina-finalize-scalars-forged-eval-trace.txt");
    let p = pis("mina-finalize-scalars-forged-eval-pis.txt");
    let err = prove_and_verify_adversarial(&d, &t, &p)
        .expect_err("a moved eval with the original claims must be refused");
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
// §5 — ⚑⚑ THE `lct-shift` FALSIFIER, REFUSED. The v1 accepting family is closed.
// ============================================================================

/// ⚑⚑ Through v1 (`d09e89817`) THIS EXACT TRACE FAMILY PROVED AND VERIFIED: `LCT` bumped, the
/// cip claim recomputed to match — two verifying proofs whose cip claims differed, the `LCT`
/// port's one-parameter family. Stage 11 (the gate-linearization leaf) eq-forces the `LCT`
/// claim against the trace's own `gateLinConst` derivation, so the same generator now produces
/// a trace the AIR REFUSES. Falsifier integrity is asserted BEFORE the verdict: the `LCT`
/// block moved, the cip claim moved WITH it (the family genuinely re-aims the cip equality),
/// and the refusal is a constraint's, not a bus's.
#[test]
fn the_lct_shift_forgery_is_refused_by_the_gate_linearization() {
    let d = descriptor();
    let t = trace("mina-finalize-scalars-lct-shift-trace.txt");
    let p = pis("mina-finalize-scalars-lct-shift-pis.txt");
    // Falsifier integrity, before any verdict: the LCT block moved, the cip claim moved WITH
    // it — this is the exact shape that ACCEPTED at v1.
    let hp = pis("mina-finalize-scalars-pis.txt");
    assert_ne!(
        block_decimal(&p, V_LCT),
        block_decimal(&hp, V_LCT),
        "the falsifier must actually move the LCT claim"
    );
    assert_ne!(
        block_decimal(&p, V_CIPCL),
        CIP_DEC,
        "the shifted family's cip claim must differ from the block's (the cip equality is \
         re-aimed, so what refuses is the LCT weld, not the cip check)"
    );
    let err = prove_and_verify_adversarial(&d, &t, &p)
        .expect_err("⚑ the lct-shift trace must now be REFUSED — the port is closed");
    assert_violated_constraint_not_bus("finalize-scalars lct-shift forgery", &err);
    println!(
        "\n§5 ⚑⚑ THE `lct-shift` FAMILY, REFUSED: {err}\n    (at v1 this exact generator's trace \
         proved and verified)"
    );
}
