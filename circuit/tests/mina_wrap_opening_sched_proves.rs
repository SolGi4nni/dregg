//! # `dregg-mina-wrap-opening-sched::v1` — the IPA OPENING relation, in-AIR, on the scheduled
//! row, both polarities — and the `sg` slot is a PIN, not a witness.
//!
//! ## What this descriptor is
//!
//! Statement (B) of `SRS::verify` on Mina devnet block 539508 — `Σ c·chal⁻¹·L + c·chal·R + c·CC
//! + (c·cip − z₁b₀)·U − z₁·sg − z₂·H + delta = O` (`wrap_verifier.ml:383`/`:422`,
//! `ipa.rs:409-425`) — as a 35-addend chain of complete additions on the scheduled substrate
//! (33 rows per addition, 581 declared / 1,599 committed columns), where EVERY addend is a
//! descriptor constant forced by its block's phase-0 window gates, the `−z₁·sg` term is slot 0,
//! and the affine `sg` is published at `PI[192..255]`. Lean-authored end to end
//! (`MinaWrapOpeningSched.lean`); this file parses, proves and refuses. It authors nothing.
//!
//! ## ⚑ WHY THE FORGERY TRACE IS THE POINT
//!
//! `opening_is_vacuous_when_sg_is_free` (Lean, two files) says (B) with a free `sg` refutes
//! NOTHING: solve `sg := z₁⁻¹(c·Q + delta − z₁b₀U − z₂H)` and the check passes at every value of
//! everything else. The `forged-sg` trace IS that move, executed at the block's own numbers: the
//! aggregate slot re-scaled onto `ft_comm` and the `sg` slot SOLVED — its chain terminates at the
//! identity (`the_solved_addend_closes_the_forged_chain`, kernel-checked). §3 asserts the AIR
//! REFUSES it anyway, by constraint and not by bus: the `sg` slot is pinned. That is
//! `pinned_sg_makes_the_opening_refute` operating as an emitted gate.
//!
//! ## ⚠ What a green here does NOT establish
//!
//! P10 (extraction) untouched; statement (A) `sg = ⟨s, srs.g⟩` deferred, not discharged here;
//! the term scaling runs in the EMITTER; the chain-level forcing walk for blocks past the first
//! is per-leg-forced, not composed (`MinaWrapOpeningSched.lean` §7's named undone work) — these
//! refusals are the behavioural half of that pair.
//!
//! ## Prerequisite — the witnesses
//!
//! The three 2048×581 traces (~5 MB each) are NOT tracked. Emit them (compiled):
//!
//! ```text
//! cd metatheory && lake build mina_wrap_opening_sched_emit
//! ./.lake/build/bin/mina_wrap_opening_sched_emit ../circuit/tests/fixtures
//! ```
//!
//! Run: `cargo test -p dregg-circuit --release --test mina_wrap_opening_sched_proves -- --nocapture`

use std::path::PathBuf;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    prove_vm_descriptor2_unchecked, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::refusal::assert_violated_constraint_not_bus;

/// The Lean-emitted layout, pinned. `MinaWrapOpeningSched.open_w_eq` /
/// `openingSchedDesc_constraint_count` are the same numbers from the authoring side.
const NAME: &str = "dregg-mina-wrap-opening-sched::v1";
const WIDTH: usize = 581;
const ROWS: usize = 2048;
const PI_COUNT: usize = 256;
const CONSTRAINTS: usize = 6404;
const SK: usize = 32;

/// `MinaWrapOpeningGate.SG` — block 539508's own `opening.sg`, affine (decimal).
const SG_X_DEC: &str =
    "27645747947874706201841804187493007015446820953018417773890030413191100025813";
const SG_Y_DEC: &str =
    "22431124833386818350144521797175752507845644373717877723958129425730786166045";

fn fixture_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

fn read_fixture(name: &str) -> String {
    let path = fixture_dir().join(name);
    std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "fixture {} missing ({e}).\nEmit the opening-sched artifacts first (COMPILED):\n  \
             cd metatheory && lake build mina_wrap_opening_sched_emit \\\n    \
             && ./.lake/build/bin/mina_wrap_opening_sched_emit ../circuit/tests/fixtures",
            path.display()
        )
    })
}

fn descriptor() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(&read_fixture("mina-wrap-opening-sched.json"))
        .expect("the Lean-emitted opening-sched descriptor parses")
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
fn block_decimal(p: &[BabyBear], lo: usize) -> String {
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
        push_mul_add(&mut acc, 256, u64::from(p[lo + i].as_u32()));
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
// §0 — SHAPE, and the published `sg` against its Lean source.
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
        "the constraint census moved; re-pin `openingSchedDesc_constraint_count` and this test \
         together"
    );
    println!("\n§0 {NAME}: {WIDTH} cols x {ROWS} rows, {PI_COUNT} PIs, {CONSTRAINTS} constraints");
}

#[test]
fn the_published_sg_is_the_blocks_own() {
    let p = pis("mina-wrap-opening-sched-pis.txt");
    assert_eq!(
        block_decimal(&p, 192),
        SG_X_DEC,
        "PI[192..224] must recompose to block 539508's own opening.sg.x"
    );
    assert_eq!(
        block_decimal(&p, 224),
        SG_Y_DEC,
        "PI[224..256] must recompose to block 539508's own opening.sg.y"
    );
    // …and the chain's endpoints: acc_in is the projective identity (0 : 1 : 0).
    assert!((0..SK).all(|i| p[i] == BabyBear::new(0)), "acc_in.X = 0");
    assert_eq!(p[SK].as_u32(), 1, "acc_in.Y = 1");
    assert!(
        (SK + 1..2 * SK).all(|i| p[i] == BabyBear::new(0)),
        "acc_in.Y high limbs"
    );
    assert!(
        (2 * SK..3 * SK).all(|i| p[i] == BabyBear::new(0)),
        "acc_in.Z = 0"
    );
    println!("§0b PI[192..256] IS opening.sg, limb-recomposed; the chain seeds at O.");
}

// ============================================================================
// §1 — FALSIFIER INTEGRITY, before any verdict is read.
// ============================================================================

#[test]
fn the_solved_sg_falsifier_moves_the_slot_and_keeps_the_publication() {
    let honest = trace("mina-wrap-opening-sched-trace.txt");
    let forged = trace("mina-wrap-opening-sched-forged-sg-trace.txt");
    let hp = pis("mina-wrap-opening-sched-pis.txt");
    let fp = pis("mina-wrap-opening-sched-forged-sg-pis.txt");

    // The published sg is UNTOUCHED by the forgery — the forger wants the descriptor's claim.
    assert_eq!(block_decimal(&fp, 192), SG_X_DEC);
    assert_eq!(block_decimal(&fp, 224), SG_Y_DEC);
    // The acc endpoints both terminate at an identity representative: X and Z lanes vanish.
    for p in [&hp, &fp] {
        for i in 0..SK {
            assert_eq!(p[3 * SK + i], BabyBear::new(0), "acc_out.X limb {i}");
            assert_eq!(p[5 * SK + i], BabyBear::new(0), "acc_out.Z limb {i}");
        }
    }
    // The trace delta is real, in-width, and includes block 0's addend cells (rows 0..33).
    let mut moved_cells = 0usize;
    let mut moved_block0 = 0usize;
    for (ri, (hr, fr)) in honest.iter().zip(forged.iter()).enumerate() {
        for (hc, fc) in hr.iter().zip(fr.iter()) {
            if hc != fc {
                moved_cells += 1;
                if ri < 33 {
                    moved_block0 += 1;
                }
            }
        }
    }
    assert!(
        moved_block0 > 0,
        "the forgery must move block 0's cells — the solved sg slot lives there"
    );
    assert!(
        moved_cells > 1000,
        "a solved sg propagates through the whole fold; {moved_cells} moved cells is a no-op \
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
        "every forged cell stays inside the declared widths (max {max_cell}); a range lookup \
         must not be what refuses"
    );
    println!(
        "§1 falsifier integrity: {moved_cells} cells moved ({moved_block0} in block 0), all \
         in-width, publication kept."
    );
}

// ============================================================================
// §2 — THE ACCEPT POLE.
// ============================================================================

#[test]
fn the_honest_trace_proves_and_verifies() {
    let d = descriptor();
    let t = trace("mina-wrap-opening-sched-trace.txt");
    let p = pis("mina-wrap-opening-sched-pis.txt");
    let t0 = std::time::Instant::now();
    let proof = prove_vm_descriptor2(&d, &t, &p, &MemBoundaryWitness::default(), &[])
        .expect("block 539508's opening relation proves on the scheduled row");
    verify_vm_descriptor2(&d, &proof, &p).expect("and verifies");
    println!(
        "\n§2 ⚑ the IPA OPENING relation PROVES in-circuit on block 539508's own opening ({} ms).",
        t0.elapsed().as_millis()
    );
}

// ============================================================================
// §3 — ⚑⚑ THE REFUSE POLE THAT IS THE FILE'S POINT: the solved-sg forgery.
// ============================================================================

/// ⚑⚑ The forged trace's chain CLOSES — as a group equation the forgery is perfect
/// (`the_solved_addend_closes_the_forged_chain`, kernel). The AIR refuses it anyway, because the
/// `sg` slot is a descriptor constant: `pinned_sg_makes_the_opening_refute`, as an emitted gate.
#[test]
fn a_solved_sg_that_closes_the_equation_is_refused_by_the_pin() {
    let d = descriptor();
    let t = trace("mina-wrap-opening-sched-forged-sg-trace.txt");
    let p = pis("mina-wrap-opening-sched-forged-sg-pis.txt");
    let err = prove_and_verify_adversarial(&d, &t, &p)
        .expect_err("a solved sg with a moved aggregate must be refused despite closing");
    assert_violated_constraint_not_bus("opening solved-sg forgery", &err);
    println!("§3 refusal (the vacuity's own witness, refused by the manifest pin): {err}");
}

// ============================================================================
// §4 — the arithmetic tooth: a corrupted fold is refused by the op gates.
// ============================================================================

#[test]
fn a_corrupted_fold_is_refused_by_the_op_gates() {
    let d = descriptor();
    let t = trace("mina-wrap-opening-sched-forged-fold-trace.txt");
    let p = pis("mina-wrap-opening-sched-forged-fold-pis.txt");
    let err = prove_and_verify_adversarial(&d, &t, &p)
        .expect_err("a corrupted complete addition must be refused");
    assert_violated_constraint_not_bus("opening corrupted-fold forgery", &err);
    println!("§4 refusal: {err}");
}

// ============================================================================
// §5 — the publication is welded: an honest proof does not verify against a moved sg claim.
// ============================================================================

#[test]
fn the_published_sg_cannot_be_swapped_under_an_honest_proof() {
    let d = descriptor();
    let t = trace("mina-wrap-opening-sched-trace.txt");
    let p = pis("mina-wrap-opening-sched-pis.txt");
    let proof = prove_vm_descriptor2(&d, &t, &p, &MemBoundaryWitness::default(), &[])
        .expect("honest proof");
    let mut tampered = p.clone();
    tampered[192] = BabyBear::new(tampered[192].as_u32() ^ 1);
    verify_vm_descriptor2(&d, &proof, &tampered)
        .expect_err("a moved sg.x limb in the public claim must refuse verification");
    println!("§5 the sg publication is bound to the proof, not a label.");
}
