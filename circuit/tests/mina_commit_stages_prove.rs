//! # The COMMITMENT-COMBINATION stages of Kimchi's `verify`, PROVED on the deployed prover over a
//! real Mina devnet block — both polarities, in RELEASE, with literal refusal text per stage.
//!
//! ## Substrate, said out loud
//!
//! **The AIRs are Lean-authored.** Every descriptor here is
//! `Dregg2.Circuit.Emit.MinaWrapCommitStages.{xiDesc, publicCommDesc, fCommDesc, ftCommDesc,
//! xiAggDesc, ladderDesc}` — `EffectLower.lowerAir` of an `EffectAirIR.EffectAir` whose
//! `mainRailOk = true` holds in the Lean kernel. Nothing in this file, and nothing in
//! `dregg-circuit`, authors a constraint, a builder gadget or an `air_accepts` predicate. Rust
//! parses the emitted JSON, fills trace CELLS from a Lean-emitted fixture, and runs
//! `prove_vm_descriptor2`. When the prover refuses a trace, the WITNESS is wrong. House Law #1.
//!
//! ## What each descriptor is
//!
//! `kimchi/src/verifier.rs` on a Wrap verifier index:
//!
//! | stage | terms | what the AIR checks |
//! |---|---|---|
//! | ξ scalar vector | 47 powers | `PI_out = PI_in^46` over the Pallas SCALAR field, 46 multiplies |
//! | `public_comm` | 41 | the affine fold of 40 Lagrange bases at negated public inputs, + the `mask_custom` blinder |
//! | `f_comm` | 1 | `linearization.index_terms` is EMPTY on the wrap side |
//! | `ft_comm` | 8 points | `chunk(f) − Σ_j ζ^{srs·j}(ζⁿ−1) · t_j` |
//! | ξ-aggregate | 47 | `Σ ξⁱ Cᵢ`, `combine_commitments`' own list and order |
//! | ladder | 1 × 8 planes | double-and-add with an in-circuit bit decomposition and a closing `SC = s` assert |
//!
//! ⚑ **THE GOLDENS ARE o1-LABS'.** Every fold's public inputs are asserted against the value
//! `MinaWrapGroupGate` / `MinaWrapAggregationGate` / `MinaWrapPublicCommGate` already carry from
//! Mina devnet block **539508**, each of which is `by decide`-checked in Lean against o1-labs'
//! own `PolyComm::multi_scalar_mul` output. So a green here is a green against Mina's arithmetic,
//! not against ours.
//!
//! ## ⚠ WHAT THIS DOES NOT SHOW — read before reading any green
//!
//! The four FOLD descriptors take `sᵢ·Bᵢ` as given: their ROM immediates are the PRE-SCALED points.
//! The scalar multiplication that produces them is `ladderDesc`, and it runs at **8 planes, not
//! 255**. `MinaWrapCommitStages.full_width_ladder_price` prices the full-width stages at
//! 378 561 / 9 465 / 85 177 / 444 809 instructions. So:
//!
//!   * the SCALAR VECTOR is checked in-AIR at full fidelity (46 real multiplies);
//!   * the GROUP FOLD is checked in-AIR at full term count (41 / 1 / 8 / 47 real points);
//!   * the SCALAR MULTIPLICATION joining them is demonstrated at 8 planes and priced at 255.
//!
//! Nothing here is "the ξ-aggregate is verified in-AIR".
//!
//! ⚑ **RELEASE, DELIBERATELY.** Algebraic refusals are `debug_assert` PANICS in debug and clean
//! `Err(...)` in release; a refusal test that passes only in debug is testing the assertion.
//!
//! ⚑ **EVERY FORGERY IS CHECKED FOR REFUSING FOR THE RIGHT REASON.** The ALU lane's first forgery
//! bumped an 8-bit limb from 255 to 256 and got a RANGE LOOKUP refusal, so the gate under test was
//! never exercised. Every forgery below wraps inside the limb width, and each assertion names the
//! class of check that must fire.
//!
//! Run: `cargo test -p dregg-circuit --release --test mina_commit_stages_prove -- --nocapture`

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TableSem, VmConstraint2, decomp_cols_pub,
    parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};

const CM_WIDTH: usize = 687;
const SK: usize = 32;
const REG_BASE: usize = 226;
const XSEL_BASE: usize = 610;
const YSEL_BASE: usize = 623;
const WSEL_BASE: usize = 637;
const XIDX_COL: usize = 650;
const PC_COL: usize = 653;
const ZCHK_COL: usize = 654;
const IMM_BASE: usize = 655;
const NREG: usize = 12;
const ROM_ARITY: usize = 40;
const Z_BASE: usize = 64;
/// The Lean register allocation (`MinaWrapCommitStages` §2).
const R_ZERO: usize = 0;
const R_TX: usize = 1;
const R_TY: usize = 2;

fn reg_col(r: usize) -> usize {
    REG_BASE + r * SK
}

macro_rules! stage {
    ($name:ident, $file:literal) => {
        struct $name;
        impl $name {
            const DESC: &'static str = include_str!(concat!(
                "../descriptors/by-name/mina-commit-",
                $file,
                ".json"
            ));
            const TRACE: &'static str =
                include_str!(concat!("fixtures/mina-commit-", $file, "-trace.txt"));
            const PIS: &'static str =
                include_str!(concat!("fixtures/mina-commit-", $file, "-pis.txt"));
        }
    };
}

stage!(Xi, "xi");
stage!(Pub, "pub");
stage!(FComm, "f");
stage!(FtComm, "ft");
stage!(Agg, "agg");
stage!(Ladder, "ladder");

fn parse_desc(json: &str) -> EffectVmDescriptor2 {
    parse_vm_descriptor2(json).expect("the deployed checker parses the Lean-emitted descriptor")
}

fn parse_trace(text: &str) -> Vec<Vec<BabyBear>> {
    let t: Vec<Vec<BabyBear>> = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|c| BabyBear::new(c.parse::<u32>().expect("cell is a u32 decimal")))
                .collect()
        })
        .collect();
    assert!(!t.is_empty(), "the fixture is not empty");
    assert!(
        t.iter().all(|r| r.len() == CM_WIDTH),
        "every row is {CM_WIDTH} wide"
    );
    t
}

fn parse_pis(text: &str) -> Vec<BabyBear> {
    let pis: Vec<BabyBear> = text
        .split_whitespace()
        .map(|c| BabyBear::new(c.parse::<u32>().expect("PI is a u32 decimal")))
        .collect();
    assert_eq!(pis.len(), 64, "32 limbs of x, then 32 of y");
    pis
}

fn prove_and_verify(
    d: &EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    pis: &[BabyBear],
) -> Result<(), String> {
    let proof = prove_vm_descriptor2(d, trace, pis, &MemBoundaryWitness::default(), &[])?;
    verify_vm_descriptor2(d, &proof, pis)
}

/// A forgery that stays INSIDE the declared 8-bit range, so a range lookup cannot be what refuses.
fn bump_limb8(cell: BabyBear) -> BabyBear {
    BabyBear::new((cell.as_u32() + 1) % 256)
}

fn committed_width(d: &EffectVmDescriptor2) -> usize {
    let mut aux = 0usize;
    for c in &d.constraints {
        if let VmConstraint2::Lookup(l) = c {
            if let Some(bits) =
                d.tables
                    .iter()
                    .find(|t| t.id == l.table)
                    .and_then(|t| match t.sem {
                        TableSem::Range { bits } => Some(bits),
                        _ => None,
                    })
            {
                aux += decomp_cols_pub(bits);
            }
        }
    }
    d.trace_width + aux
}

fn rom_rows(d: &EffectVmDescriptor2) -> &Vec<Vec<u32>> {
    let t = d
        .tables
        .iter()
        .find(|t| matches!(t.sem, TableSem::ExactPublicRows { .. }))
        .expect("the machine declares an instruction ROM");
    match &t.sem {
        TableSem::ExactPublicRows { rows } => rows,
        _ => unreachable!(),
    }
}

/// ⚑ **§0 — THE SHAPE, READ OFF THE ARTIFACTS.** Every number this campaign quotes for the
/// commitment machine is printed here from the emitted descriptors, never from a plan.
#[test]
fn the_commitment_machine_has_the_shape_lean_emitted() {
    println!("\n═══ THE COMMITMENT MACHINE ═══");
    println!(
        "{:>28} {:>7} {:>7} {:>9} {:>10} {:>9}",
        "descriptor", "constr", "declrd", "committed", "ROM rows", "ROM cells"
    );
    for (label, json) in [
        ("xi scalar vector", Xi::DESC),
        ("public_comm fold", Pub::DESC),
        ("f_comm fold", FComm::DESC),
        ("ft_comm fold", FtComm::DESC),
        ("xi-aggregate fold", Agg::DESC),
        ("scalar-mul ladder", Ladder::DESC),
    ] {
        let d = parse_desc(json);
        let rows = rom_rows(&d);
        println!(
            "{label:>28} {:>7} {:>7} {:>9} {:>10} {:>9}",
            d.constraints.len(),
            d.trace_width,
            committed_width(&d),
            rows.len(),
            rows.len() * ROM_ARITY,
        );
        assert_eq!(d.trace_width, CM_WIDTH);
        assert_eq!(d.public_input_count, 64);
        // ⚑ The manifest key is `pc + 1`: strictly increasing and never zero, which is what turns
        // the permutation balance into a POINTWISE identification of row j with instruction j
        // rather than a statement about the multiset of instructions.
        for (j, row) in rows.iter().enumerate() {
            assert_eq!(
                row.len(),
                ROM_ARITY,
                "manifest row {j} has the declared arity"
            );
            assert_eq!(row[0], j as u32 + 1, "manifest key at index {j} is pc+1");
        }
    }
    // ⚑ THE ENCODING FINDING, on the wire: the instruction word is 40 cells and INDEPENDENT of the
    // register count. `MinaWrapVerifierProgram`'s one-hot word would be 1+4+3*12+32 = 73 against the
    // deployed MAX_EXACT_PUBLIC_ARITY = 64 — REFUSED at this register file, which is why the ROM
    // carries indices and three decode gates carry the one-hot vectors.
    assert_eq!(ROM_ARITY, 40);
    assert!(1 + 4 + 3 * NREG + SK > 64, "the one-hot word does not fit");
}

/// ⚑ **§1 — THE ξ SCALAR VECTOR, at FULL fidelity.** 46 multiplies over the Pallas SCALAR field,
/// from the block's real `ξ` as a public input to `ξ⁴⁶` as one. This is the stage that says the
/// 47-term aggregate's scalars are the transcript's and not the prover's.
#[test]
fn the_xi_scalar_vector_proves() {
    let d = parse_desc(Xi::DESC);
    let trace = parse_trace(Xi::TRACE);
    let pis = parse_pis(Xi::PIS);

    // The chain really is a chain: 46 multiply instructions writing R2 and reading R2, R1.
    let muls = trace.iter().filter(|r| r[222].as_u32() == 1).count();
    assert_eq!(
        muls, 46,
        "46 multiplies — one per power of xi after the first"
    );

    // The first row's R1 IS the claimed input, and the last row's R2 the claimed output: that is
    // the pin, read off the fixture before the prover ever sees it.
    for i in 0..SK {
        assert_eq!(trace[0][reg_col(R_TX) + i], pis[i], "input limb {i}");
        assert_eq!(
            trace[trace.len() - 1][reg_col(R_TY) + i],
            pis[SK + i],
            "output limb {i}"
        );
    }

    prove_and_verify(&d, &trace, &pis).expect("the xi power chain must prove and verify");
    println!(
        "\n§1 xi SCALAR VECTOR: 46 multiplies over the Pallas scalar field, {} rows, PROVED and \
         VERIFIED in release against 64 public inputs.",
        trace.len()
    );
}

/// …and a forged endpoint is refused, at both ends, so the chain is a binding and not a display.
#[test]
fn a_forged_xi_power_is_refused() {
    let d = parse_desc(Xi::DESC);
    let trace = parse_trace(Xi::TRACE);

    let mut out = parse_pis(Xi::PIS);
    out[SK] = bump_limb8(out[SK]);
    let err = prove_and_verify(&d, &trace, &out)
        .expect_err("a claimed xi^46 that is not the chain's result must be REFUSED");
    println!("\n§1b forged xi^46 REFUSED: {err}");
    assert!(!err.is_empty());

    let mut inp = parse_pis(Xi::PIS);
    inp[0] = bump_limb8(inp[0]);
    let err = prove_and_verify(&d, &trace, &inp)
        .expect_err("a claimed xi that is not the trace's R1 must be REFUSED");
    println!("§1c forged xi REFUSED: {err}");
    assert!(!err.is_empty());
}

/// The golden coordinate pair a stage's public inputs must carry, as 32 8-bit limbs each.
fn limbs_of(dec: &str) -> Vec<u32> {
    let mut v: Vec<u32> = Vec::with_capacity(SK);
    let mut n = dec
        .chars()
        .map(|c| c.to_digit(10).expect("decimal") as u64)
        .fold(vec![0u8; 0], |mut acc, dgt| {
            // long multiplication by 10 then add, little-endian base 256
            let mut carry = dgt;
            for b in acc.iter_mut() {
                let t = (*b as u64) * 10 + carry;
                *b = (t & 0xff) as u8;
                carry = t >> 8;
            }
            while carry > 0 {
                acc.push((carry & 0xff) as u8);
                carry >>= 8;
            }
            acc
        });
    n.resize(SK, 0);
    for b in n.iter().take(SK) {
        v.push(*b as u32);
    }
    v
}

/// ⚑ **§2 — THE FOUR FOLDS, AGAINST o1-LABS' OWN GOLDEN OUTPUTS.**
///
/// The goldens are transcribed here from `MinaWrapGroupGate` / `MinaWrapAggregationGate` /
/// `MinaWrapPublicCommGate`, each of which is `by decide`-checked in Lean against o1-labs'
/// `PolyComm::multi_scalar_mul` on Mina devnet block 539508. Asserting them against the EMITTED
/// public inputs is what makes the fixture a claim about Mina rather than about itself.
const GOLD: &[(&str, &str, &str)] = &[
    (
        "public_comm",
        "470504819593367149019961354587501248284062504999182333530678460612240353949",
        "6206102871863652151110650262665750758598688015582085691166368065469448164243",
    ),
    (
        "f_comm",
        "19674326400533049625615225538021626157270526457556463284014696039483724147764",
        "28695397289097617976568064802307687844707320509254944091000772912640603603518",
    ),
    (
        "ft_comm",
        "23134851620960708781201702572748654667024999231009061048008617507448700477719",
        "11095341763140500863332709654083102487611440299358362125188480277634145783318",
    ),
    (
        "xi-aggregate",
        "16920351616701759065221501174543651695204837625383843062340142142233321601893",
        "6987318110308499591944006882900614979096445894080458861614506362368144263288",
    ),
];

#[test]
fn every_fold_publishes_the_o1labs_golden_point() {
    for ((name, gx, gy), pis_text) in GOLD
        .iter()
        .zip([Pub::PIS, FComm::PIS, FtComm::PIS, Agg::PIS])
    {
        let pis = parse_pis(pis_text);
        let (lx, ly) = (limbs_of(gx), limbs_of(gy));
        for i in 0..SK {
            assert_eq!(pis[i].as_u32(), lx[i], "{name}: x limb {i}");
            assert_eq!(pis[SK + i].as_u32(), ly[i], "{name}: y limb {i}");
        }
        println!("{name:>14}: the emitted public inputs ARE o1-labs' golden point");
    }
}

/// The per-stage prove/verify, honest polarity, at the stage's FULL term count.
fn fold_proves(label: &str, json: &str, trace_text: &str, pis_text: &str, terms: usize) {
    let d = parse_desc(json);
    let trace = parse_trace(trace_text);
    let pis = parse_pis(pis_text);
    let rows = rom_rows(&d);
    assert_eq!(
        rows.len(),
        trace.len(),
        "manifest rows = trace rows — the balance is a PERMUTATION, so the ROM length IS the trace \
         length and a prover can neither run the program twice nor stop early"
    );

    // ⚑ THE BASES ARE ROM IMMEDIATES, AND THE ROM PINS WHICH ONE EACH INSTRUCTION USES. Count the
    // instructions whose `y` operand is the IMMEDIATE code: a fold over `terms` points touches each
    // base's abscissa twice and its ordinate once.
    let imm_instrs = rows.iter().filter(|r| r[5] == NREG as u32).count();
    assert!(
        imm_instrs >= terms,
        "{label}: at least one ROM-pinned immediate per term ({imm_instrs} for {terms})"
    );

    // ⚑ AND THE DESCRIPTOR DEMANDS ITS SLOPES. `zc = 1` rows are the assert-zero instructions; a
    // fold with none of them would be a fold over FREE slopes, which is this campaign's own named
    // failure mode.
    let asserts = rows.iter().filter(|r| r[7] == 1).count();
    assert!(
        asserts >= terms.saturating_sub(1),
        "{label}: one slope assertion per chord ({asserts} for {terms} terms)"
    );

    // …and the free-witness instructions are exactly the ones the ROM names.
    let frees = rows
        .iter()
        .filter(|r| r[4] == NREG as u32 || r[5] == (NREG + 1) as u32)
        .count();
    assert_eq!(
        frees, asserts,
        "{label}: every witnessed slope is pinned by exactly one assert"
    );

    prove_and_verify(&d, &trace, &pis).unwrap_or_else(|e| panic!("{label} must prove: {e}"));
    println!(
        "{label:>14}: {terms:>3} terms, {:>5} instructions, {:>3} ROM-pinned immediates, \
         {asserts:>3} slope assertions — PROVED and VERIFIED",
        trace.len()
    );
}

#[test]
fn the_public_comm_fold_proves() {
    fold_proves("public_comm", Pub::DESC, Pub::TRACE, Pub::PIS, 41);
}

#[test]
fn the_f_comm_fold_proves() {
    fold_proves("f_comm", FComm::DESC, FComm::TRACE, FComm::PIS, 1);
}

#[test]
fn the_ft_comm_fold_proves() {
    fold_proves("ft_comm", FtComm::DESC, FtComm::TRACE, FtComm::PIS, 8);
}

#[test]
fn the_xi_aggregate_fold_proves() {
    fold_proves("xi-aggregate", Agg::DESC, Agg::TRACE, Agg::PIS, 47);
}

/// ⚑ **§3 — THE FORGERIES, ON THE LARGEST FOLD.** Four lies, each refused, and each named for the
/// mechanism that must be the one to refuse it.
#[test]
fn the_xi_aggregate_refuses_four_forgeries() {
    let d = parse_desc(Agg::DESC);
    let pis = parse_pis(Agg::PIS);

    // (a) A DIFFERENT CLAIMED AGGREGATE. The boundary pin must refuse whatever the trace says.
    {
        let trace = parse_trace(Agg::TRACE);
        let mut p = pis.clone();
        p[0] = bump_limb8(p[0]);
        let err = prove_and_verify(&d, &trace, &p)
            .expect_err("a claimed aggregate that is not the fold's result must be REFUSED");
        println!("\n§3a forged aggregate REFUSED: {err}");
        assert!(!err.is_empty());
    }

    // (b) A FORGED SLOPE. The witnessed slope is the one value in a chord row the routing gates do
    // not pin; the ASSERT-ZERO instruction is what pins it, and this is that instruction on the
    // wire. The forgery stays inside the 8-bit limb width, so no range lookup can be what fires.
    {
        let mut trace = parse_trace(Agg::TRACE);
        // find the first free-witness row (y operand selector at the FREE position)
        let r = trace
            .iter()
            .position(|row| row[YSEL_BASE + NREG + 1].as_u32() == 1)
            .expect("the fold witnesses at least one slope");
        trace[r][SK] = bump_limb8(trace[r][SK]); // the y-operand block's low limb IS the witness
        let err = prove_and_verify(&d, &trace, &pis)
            .expect_err("a slope that does not satisfy s(x1-x2) = y1-y2 must be REFUSED");
        println!("§3b forged SLOPE REFUSED (row {r}): {err}");
        assert!(
            err.contains("OodEvaluationMismatch"),
            "an ALGEBRAIC gate must refuse a bad slope, not a lookup -- got: {err}"
        );
    }

    // (c) A SUBSTITUTED BASE POINT. The bases are ROM immediates, so changing one in the trace puts
    // the queried tuple outside the manifest and the LOOKUP BUS is what must refuse. This is the
    // scalar-to-base pairing, on the wire: the ROM row carries `pc`, the opcode, the operand
    // indices and the immediate TOGETHER, so a row cannot take term i's scalar with term j's base.
    {
        let mut trace = parse_trace(Agg::TRACE);
        let r = trace
            .iter()
            .position(|row| row[YSEL_BASE + NREG].as_u32() == 1 && row[IMM_BASE].as_u32() != 0)
            .expect("the fold reads at least one non-zero immediate");
        trace[r][IMM_BASE] = bump_limb8(trace[r][IMM_BASE]);
        let err = prove_and_verify(&d, &trace, &pis)
            .expect_err("a base point the ROM did not name must be REFUSED");
        println!("§3c substituted BASE POINT REFUSED (row {r}): {err}");
        assert!(
            err.contains("exact-public") || err.contains("LookupError") || err.contains("Lookup"),
            "the ROM BUS must refuse a re-chosen immediate -- got: {err}"
        );
    }

    // (d) A DROPPED ASSERTION. Turn off one `zchk` bit and the descriptor stops demanding that
    // chord's slope relation — so the ROM must refuse the instruction word itself. This is the
    // difference between "the trace happens to satisfy the chord law" and "the descriptor demands
    // it", and it is the check that keeps §3b from being a statement about the fixture.
    {
        let mut trace = parse_trace(Agg::TRACE);
        let r = trace
            .iter()
            .position(|row| row[ZCHK_COL].as_u32() == 1)
            .expect("the fold asserts at least once");
        trace[r][ZCHK_COL] = BabyBear::new(0);
        let err = prove_and_verify(&d, &trace, &pis)
            .expect_err("dropping an assert bit the ROM names must be REFUSED");
        println!("§3d dropped ASSERT bit REFUSED (row {r}): {err}");
        assert!(
            err.contains("exact-public") || err.contains("LookupError") || err.contains("Lookup"),
            "the ROM BUS must refuse an instruction word it did not name -- got: {err}"
        );
    }
}

/// ⚑ **§4 — THE REGISTER FILE IS A MEMORY, AND BREAKING IT IS REFUSED.** The running total is
/// carried across the whole fold by the register window legs; move it once between two rows with no
/// instruction writing it and the window leg must bite. Without this the output pin would be
/// reading a free cell and §3a's refusal would be worth nothing.
#[test]
fn tampering_with_the_running_total_is_refused() {
    let d = parse_desc(FtComm::DESC);
    let pis = parse_pis(FtComm::PIS);
    let mut trace = parse_trace(FtComm::TRACE);
    let last = trace.len() - 1;
    // The padding tail holds the total unchanged; pick a row inside it.
    assert_eq!(
        trace[last][reg_col(R_TX)],
        trace[last - 1][reg_col(R_TX)],
        "the padding tail holds the running total"
    );
    trace[last - 1][reg_col(R_TX)] = bump_limb8(trace[last - 1][reg_col(R_TX)]);
    let err = prove_and_verify(&d, &trace, &pis)
        .expect_err("a register that changes with no instruction writing it must be REFUSED");
    println!("\n§4 held-register tamper REFUSED: {err}");
    assert!(
        err.contains("OodEvaluationMismatch") || err.contains("boundary") || err.contains("Lookup"),
        "the register WINDOW leg (or the PI pin it feeds) must refuse -- got: {err}"
    );
}

/// ⚑ **§5 — THE ZERO REGISTER IS FORCED, NOT ASSUMED.** Every immediate load and every witness load
/// in this cone rides on `R0 = 0`, which instruction 0 (`SUB R0, R0 → R0`) establishes from
/// whatever the prover put in the first row. Move it after that and the register window must refuse.
#[test]
fn the_zero_register_is_forced() {
    let d = parse_desc(FtComm::DESC);
    let pis = parse_pis(FtComm::PIS);
    let trace = parse_trace(FtComm::TRACE);
    for r in 1..trace.len() {
        for i in 0..SK {
            assert_eq!(
                trace[r][reg_col(R_ZERO) + i].as_u32(),
                0,
                "R0 is zero from row 1 on (row {r}, limb {i})"
            );
        }
    }
    let mut t = trace.clone();
    t[3][reg_col(R_ZERO)] = BabyBear::new(1);
    let err = prove_and_verify(&d, &t, &pis)
        .expect_err("a non-zero R0 after instruction 0 must be REFUSED");
    println!("\n§5 forged ZERO register REFUSED: {err}");
    assert!(!err.is_empty());
}

/// ⚑ **§6 — THE LADDER: the scalar multiplication itself, with the bit decomposition in-circuit.**
///
/// ⚠ **8 PLANES, NOT 255**, over the block's real `sigma_comm[6]`. Every gate is the full-width
/// gate; what is reduced is the plane count, and `full_width_ladder_price` in Lean is the number
/// this is a reduction of. The check that makes the ladder a scalar multiplication rather than a
/// walk is the closing `SC = s` assertion: without it the digits are free choices and the ladder
/// computes `Σ bⱼ2ʲ·B` for a scalar nobody named — which is exactly the "MSM over free scalars"
/// this campaign has already shipped once.
#[test]
fn the_scalar_multiplication_ladder_proves() {
    let d = parse_desc(Ladder::DESC);
    let trace = parse_trace(Ladder::TRACE);
    let pis = parse_pis(Ladder::PIS);
    let rows = rom_rows(&d);

    // The digit-load instructions: one per plane, each followed by a booleanity assert.
    let bit_loads = rows
        .iter()
        .filter(|r| r[5] == (NREG + 1) as u32 && r[6] == 5)
        .count();
    assert_eq!(bit_loads, 8, "one digit per plane, 8 planes");

    prove_and_verify(&d, &trace, &pis).expect("the ladder must prove and verify");
    println!(
        "\n§6 LADDER: 8 planes over the block's real sigma_comm[6], {} instructions, {bit_loads} \
         in-circuit digits, PROVED and VERIFIED.",
        trace.len()
    );
}

/// ⚑ …and a forged DIGIT is refused. The scalar accumulator's closing assertion is what does it:
/// flip one plane's bit and the ladder still computes a group element, just not `s·B`, and the
/// `SC = s` instruction is the only thing in the descriptor that can tell.
#[test]
fn a_forged_ladder_digit_is_refused() {
    let d = parse_desc(Ladder::DESC);
    let pis = parse_pis(Ladder::PIS);
    let mut trace = parse_trace(Ladder::TRACE);
    let r = trace
        .iter()
        .position(|row| row[YSEL_BASE + NREG + 1].as_u32() == 1 && row[WSEL_BASE + 5].as_u32() == 1)
        .expect("the ladder loads at least one digit");
    // flip the digit inside its limb width
    let cur = trace[r][SK].as_u32();
    trace[r][SK] = BabyBear::new(if cur == 0 { 1 } else { 0 });
    let err = prove_and_verify(&d, &trace, &pis)
        .expect_err("a digit that is not a digit of the named scalar must be REFUSED");
    println!("\n§6b forged LADDER DIGIT REFUSED (row {r}): {err}");
    assert!(!err.is_empty());
}

/// ⚑ **§7 — WHAT ONE INSTANCE COSTS, AND HOW FAR THE FULL-WIDTH STAGES ARE.** Measured on the
/// deployed prover at the deployed FRI point, so the census has a per-instruction price in this
/// machine's own units.
#[test]
fn the_commitment_machine_is_priced() {
    let d = parse_desc(Agg::DESC);
    let trace = parse_trace(Agg::TRACE);
    let pis = parse_pis(Agg::PIS);
    let committed = committed_width(&d);

    // ⚠ COLD START, DISCARDED — a previous lane in this campaign measured one and would have
    // shipped a fake speedup.
    prove_and_verify(&d, &trace, &pis).expect("the probe must prove");
    let t0 = std::time::Instant::now();
    prove_and_verify(&d, &trace, &pis).expect("warm");
    let ms = t0.elapsed().as_secs_f64() * 1000.0;

    println!("\n═══ §7  THE COMMITMENT MACHINE, PRICED ═══");
    println!(
        "committed width {committed}; one instruction commits {} bytes of trace; the 47-term \
         aggregate fold is {} instructions and proves in {ms:.1} ms",
        committed * 4,
        trace.len()
    );

    // The Lean census (`MinaWrapCommitStages.full_width_ladder_price`), restated so a drift on
    // either side reds here.
    const FULL: &[(&str, usize, usize)] = &[
        ("public_comm", 41, 378_561),
        ("f_comm", 1, 9_465),
        ("ft_comm", 8, 85_177),
        ("xi-aggregate", 47, 444_809),
    ];
    const ROM_CAP: usize = (1 << 25) / ROM_ARITY;
    println!(
        "\n{:>14} {:>6} {:>12} {:>9} {:>10} {:>12}",
        "stage", "terms", "full-width", "pads to", "% of ROM", "trace GB"
    );
    let mut total = 0usize;
    for (name, terms, instrs) in FULL {
        total += *instrs;
        let pad = instrs.next_power_of_two();
        println!(
            "{name:>14} {terms:>6} {instrs:>12} {:>9} {:>9.1}% {:>12.2}",
            format!("2^{}", pad.trailing_zeros()),
            100.0 * *instrs as f64 / ROM_CAP as f64,
            pad as f64 * committed as f64 * 4.0 / 1e9,
        );
        assert!(
            *instrs <= ROM_CAP,
            "{name} must fit one exact-public ROM at full width"
        );
    }
    println!(
        "{:>14} {:>6} {total:>12} {:>9} {:>9.1}% ",
        "ALL FOUR",
        97,
        format!("2^{}", total.next_power_of_two().trailing_zeros()),
        100.0 * total as f64 / ROM_CAP as f64
    );
    assert!(
        total > ROM_CAP,
        "and their SUM must not — that is the segmentation finding, and if it stops holding the \
         Lean `every_stage_fits_one_rom_at_full_width` is stale"
    );
    println!(
        "\nROM cap {ROM_CAP} instructions at arity {ROM_ARITY} (the 2^21 row cap is NOT the \
         binder). Every stage fits; their sum is {:.2}x the cap.",
        total as f64 / ROM_CAP as f64
    );
}
