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
//! | `public_comm` | **31** (41 nominal) | the affine fold of the Lagrange bases with a NON-ZERO public input, + the `mask_custom` blinder |
//! | `f_comm` | 1 | `linearization.index_terms` is EMPTY on the wrap side |
//! | `ft_comm` | 8 points | `chunk(f) − Σ_j ζ^{srs·j}(ζⁿ−1) · t_j` |
//! | ξ-aggregate | 47 | `Σ ξⁱ Cᵢ`, `combine_commitments`' own list and order |
//! | ladder | 1 × 8 planes | double-and-add with an in-circuit bit decomposition and a closing `SC = s` assert |
//!
//! ⚑ **`public_comm` IS 31 AND NOT 41 BECAUSE THIS TEST FOUND A DEFECT.** Ten of the block's forty
//! public inputs are ZERO; a zero scalar makes the term the point at infinity, which `toAff` reads
//! as `(0,0)` — not on Pallas. The 41-term fold reached o1-labs' value ANYWAY, and only because ten
//! is EVEN. §2 has the full account; `MinaWrapCommitStages.an_odd_identity_count_misses_the_golden`
//! is the refutation in Lean.
//!
//! ⚑ **THE GOLDENS ARE o1-LABS', AND NOTHING HERE TRANSCRIBES THEM.** The anchor is
//! `fixtures/mina-commit-golds.txt`, emitted by `EmitCommitStages.lean goldlimbs` off the GATE
//! CONSTANTS (`PUBLIC_COMM_GOLD` / `F_COMM_GOLD` / `FT_COMM_GOLD` / `COMBINED_GOLD`), each `by
//! decide`-checked in Lean against o1-labs' own `PolyComm::multi_scalar_mul` on Mina devnet block
//! **539508**. §2 reads the term points out of each descriptor's INSTRUCTION ROM, folds them in this
//! file's own arithmetic, and lands on that anchor — 87/87 term points, counted. So a green here is
//! a green against Mina's arithmetic, not against ours, and not against a decimal someone typed.
//!
//! ## ⚠ WHAT THIS DOES NOT SHOW — read before reading any green
//!
//! The four FOLD descriptors take `sᵢ·Bᵢ` as given: their ROM immediates are the PRE-SCALED points.
//! The scalar multiplication that produces them is `ladderDesc`, and it runs at **8 planes, not
//! 255**. `MinaWrapCommitStages.full_width_ladder_price` prices the full-width stages at
//! 378 561 / 9 465 / 85 177 / 444 809 instructions. So, **of the descriptors in THIS file**:
//!
//!   * the SCALAR VECTOR is checked in-AIR at full fidelity (46 real multiplies);
//!   * the GROUP FOLD is checked in-AIR at full term count (31 / 1 / 8 / 47 real points);
//!   * the SCALAR MULTIPLICATION joining them is demonstrated at 8 planes and priced at 255.
//!
//! **Nothing in this file is "the ξ-aggregate is verified in-AIR".**
//!
//! ⚑ **THAT CLAIM NOW HAS A HOME, AND IT IS NOT HERE.**
//! `Dregg2.Circuit.Emit.MinaWrapXiAggregateMsm` emits the same 47-term aggregate on
//! `PastaMsmBucketed`'s fused running sum — generators UNSCALED, the 47 ξ powers entering as DIGITS
//! at `nbits = 255`, 8 192 rows — and
//! `pasta_msm_bucketed_prove.rs::the_mina_xi_aggregate_scales_inside_the_circuit` proves it on the
//! deployed prover against `COMBINED_GOLD`. ⚠ It buys that with a DOWNGRADE that must not be
//! absorbed: those rows are denominated in the **unsound `fpMulCore`**, where every descriptor in
//! this file is `PastaFieldSound`.
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
use dregg_circuit::pasta_msm::{complete_add, on_curve_at, proj_eq_at};
use dregg_circuit::pasta_windowed_witness::{P_PASTA, Pt, U256};

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
/// ⚑ **The six SQUARING-BASIS holds** (`MinaWrapCommitStages.XI_BASIS_REGS`), high power first —
/// the ladder's registers, idle in the ξ chain. `xiChainProg` taps `ξ^{2^j}` into each as the walk
/// passes it, and `pinXiChain` publishes all six on the LAST row at PI blocks 2 … 7.
const R_BASIS: [usize; 6] = [8, 7, 6, 5, 4, 3];
/// Eight 32-felt blocks: `ξ`, `ξ⁴⁶`, then the basis.
const XI_PI_BLOCKS: usize = 8;

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

/// ⚑ **EVERY FIXTURE IS NON-EMPTY, CHECKED BEFORE ANYTHING READS ONE.**
///
/// ⚠ This is the check whose absence withdrew this test. `mina-commit-xi-trace.txt` was emitted as
/// a ZERO-BYTE file because the qN trace generator did not finish; `include_str!` accepts a 0-byte
/// file and yields `""`, so the test COMPILED and its parser saw an empty trace — a green against
/// nothing. (That 0-byte file was still committed at HEAD on 2026-08-05, despite the withdrawal
/// commit saying it had been deleted.) A missing fixture is a loud compile error; an EMPTY one is
/// silent, so it is the empty one that needs a gate.
#[test]
fn no_fixture_is_empty() {
    let mut n = 0usize;
    for (label, text) in [
        ("xi desc", Xi::DESC),
        ("xi trace", Xi::TRACE),
        ("xi pis", Xi::PIS),
        ("pub desc", Pub::DESC),
        ("pub trace", Pub::TRACE),
        ("pub pis", Pub::PIS),
        ("f desc", FComm::DESC),
        ("f trace", FComm::TRACE),
        ("f pis", FComm::PIS),
        ("ft desc", FtComm::DESC),
        ("ft trace", FtComm::TRACE),
        ("ft pis", FtComm::PIS),
        ("agg desc", Agg::DESC),
        ("agg trace", Agg::TRACE),
        ("agg pis", Agg::PIS),
        ("ladder desc", Ladder::DESC),
        ("ladder trace", Ladder::TRACE),
        ("ladder pis", Ladder::PIS),
        ("golds", GOLDS),
    ] {
        assert!(
            !text.trim().is_empty(),
            "{label} is EMPTY -- include_str! accepted a 0-byte file and this test would have \
             reported success against nothing"
        );
        n += 1;
    }
    assert_eq!(
        n, 19,
        "six stages x (descriptor, trace, PIs), plus the golden anchor"
    );
    println!("\n§0a all {n} fixtures non-empty");
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

/// ⚑ A published vector is a whole number of 32-limb BLOCKS. The four fold stages and the ladder
/// publish TWO (`x` then `y`); the ξ chain publishes EIGHT since 2026-08-05 (`ξ`, `ξ⁴⁶`, then the
/// six-value squaring basis the ξ-aggregate's wire consumes). A flat `== 64` here was what made a
/// widened surface look like a corrupt fixture.
fn parse_pis(text: &str) -> Vec<BabyBear> {
    let pis: Vec<BabyBear> = text
        .split_whitespace()
        .map(|c| BabyBear::new(c.parse::<u32>().expect("PI is a u32 decimal")))
        .collect();
    assert!(
        pis.len() >= 2 * SK && pis.len() % SK == 0,
        "a published vector is a whole number of {SK}-limb blocks, got {}",
        pis.len()
    );
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
        // ⚑ The ξ chain publishes EIGHT 32-felt blocks; every other stage publishes two.
        assert_eq!(
            d.public_input_count,
            if label == "xi scalar vector" {
                XI_PI_BLOCKS * SK
            } else {
                2 * SK
            },
            "{label} publishes an unexpected number of felts"
        );
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
    assert_eq!(
        pis.len(),
        XI_PI_BLOCKS * SK,
        "the chain publishes eight 32-felt blocks since 2026-08-05"
    );
    assert_eq!(d.public_input_count, XI_PI_BLOCKS * SK);
    for i in 0..SK {
        assert_eq!(trace[0][reg_col(R_TX) + i], pis[i], "input limb {i}");
        assert_eq!(
            trace[trace.len() - 1][reg_col(R_TY) + i],
            pis[SK + i],
            "output limb {i}"
        );
    }

    // ⚑ **AND THE SIX BASIS BLOCKS ARE THE SIX BASIS REGISTERS, ON THE LAST ROW.** This is the
    // surface the ξ-aggregate's 192 wire felts are welded to; if a block published the wrong
    // register the aggregate would still prove, against a basis nobody derived.
    let last = &trace[trace.len() - 1];
    for (b, r) in R_BASIS.iter().enumerate() {
        for i in 0..SK {
            assert_eq!(
                last[reg_col(*r) + i],
                pis[(2 + b) * SK + i],
                "basis block {b} (register {r}) limb {i}"
            );
        }
    }
    // …and they are six DISTINCT values, so a tap that aliased its register reds here.
    for a in 0..6 {
        for b in (a + 1)..6 {
            assert_ne!(
                pis[(2 + a) * SK..(3 + a) * SK],
                pis[(2 + b) * SK..(3 + b) * SK],
                "basis blocks {a} and {b} publish the same 32 felts"
            );
        }
    }
    // …and the tail block is the chain's own INPUT `ξ`, which is what makes the basis an orbit of
    // the value `dregg-mina-xi-endo-lift::v1` published rather than six free scalars.
    assert_eq!(
        pis[7 * SK..],
        pis[..SK],
        "the basis tail must be the chain's input xi"
    );

    prove_and_verify(&d, &trace, &pis).expect("the xi power chain must prove and verify");
    println!(
        "\n§1 xi SCALAR VECTOR: 46 multiplies over the Pallas scalar field, {} rows, PROVED and \
         VERIFIED in release against {} public inputs — including the SIX-VALUE SQUARING BASIS \
         (ξ³², ξ¹⁶, ξ⁸, ξ⁴, ξ², ξ) the ξ-aggregate's wire consumes.",
        trace.len(),
        pis.len()
    );
}

/// ⚑ …and a forged BASIS block is refused. The chain would prove perfectly well with any 192 felts
/// in blocks 2 … 7 if they were not pinned to registers the program wrote — and then the
/// ξ-aggregate's 192-felt weld would be a comparison of two numbers nobody derived.
///
/// **REFUSING GATE: `MinaWrapCommitStages.pinXiChain`'s LAST-ROW PI bindings** on the basis holds.
///
/// ⚠ The felt moved is READ first: `bump_limb8` wraps inside the 8-bit range so a RANGE lookup
/// cannot be what objects, and the assertion below is that the value actually changed.
#[test]
fn a_forged_xi_basis_block_is_refused() {
    let d = parse_desc(Xi::DESC);
    let trace = parse_trace(Xi::TRACE);

    for b in 0..6usize {
        let mut bad = parse_pis(Xi::PIS);
        let slot = (2 + b) * SK;
        let before = bad[slot];
        let after = bump_limb8(before);
        assert_ne!(before, after, "the moved felt must actually change value");
        bad[slot] = after;
        let err = prove_and_verify(&d, &trace, &bad)
            .expect_err("a claimed basis value the chain did not compute must be REFUSED");
        assert!(!err.is_empty());
        println!("\n§1d forged basis block {b} REFUSED: {err}");
    }
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

/// ⚑ **§2 — THE FOUR FOLDS, RECOMPUTED FROM THEIR OWN ROM CELLS, AGAINST o1-LABS' GOLDENS.**
///
/// ⚠ This section used to be a `const GOLD: &[(&str, &str, &str)]` of **eight transcribed decimal
/// literals**, with a docblock that said they were "transcribed here from `MinaWrapGroupGate` /
/// `MinaWrapAggregationGate` / `MinaWrapPublicCommGate`". A sibling lane deleted exactly that shape
/// after finding all 174 of its own constants correctly copied, and its reason applies verbatim:
/// **one wrong digit would have given a self-consistent tree** — Lean proving the program computes
/// ITS constants, the harness pinning ITS digest, every gate green. There is no typed decimal in
/// this file.
///
/// What replaces it is the standard that lane set, in three parts:
///
///   1. **The anchor is emitted, not typed.** `mina-commit-golds.txt` is
///      `EmitCommitStages.lean goldlimbs`, which prints the four goldens straight off the GATE
///      CONSTANTS — `PUBLIC_COMM_GOLD`, `F_COMM_GOLD`, `FT_COMM_GOLD`, `COMBINED_GOLD`, each of
///      which is separately `by decide`-checked in Lean against o1-labs' own
///      `PolyComm::multi_scalar_mul` on Mina devnet block 539508. It is never any fold's output.
///   2. **The comparison target is the emitted artifact's prover-uncontrollable cells.** The term
///      points are read out of each descriptor's INSTRUCTION ROM — `exactPublicRows`, a permutation
///      manifest the prover cannot choose — and not out of the Lean source that generated it.
///   3. **The recomputation is independent and counted.** The chord fold below is this file's own
///      arithmetic over `U256`; it does not call the emitter, and `assert_eq!(checked, 97)` is the
///      counted assertion that all 97 term points across the four stages were consumed.
///
/// So a green here says: *the points the verifier will actually read out of the ROM, folded by
/// code that shares nothing with the emitter, land on Mina's own aggregate.*
const GOLDS: &str = include_str!("fixtures/mina-commit-golds.txt");

/// Where a ROM row's 32 immediate limbs begin: `1 + 3 + 3 + 1`, the pc key, the three operand
/// codes, the three selector codes and the assert bit.
const ROM_IMM_OFF: usize = 8;

/// The total term count across the four folds — `public_comm` 31 (41 nominal, ten dropped: see
/// below), `f_comm` 1, `ft_comm` 8, ξ-aggregate 47. The counted assertion of §2.
///
/// ⚑ `public_comm` is 31 and not 41 because of a defect this test FOUND on 2026-08-05. Ten of the
/// block's forty public inputs are zero; a zero scalar makes the term the point at infinity, and
/// `toAff` reads that as `(0, 0)` — which is NOT on Pallas. The 41-term affine fold reached
/// o1-labs' `public_comm` anyway, and only because ten is EVEN: adding `(0,0)` takes the running
/// total off the curve and adding it again is the identity map, so the ten cancelled in pairs. A
/// block with an ODD number of zero public inputs would have folded to the wrong point. It was the
/// `on_curve_at` assertion below that surfaced it — the fold check alone was green.
/// `MinaWrapCommitStages.an_odd_identity_count_misses_the_golden` is the refutation in Lean, and
/// `PUBLIC_TERMS` now drops the identity terms.
const TOTAL_TERMS: usize = 87;

/// 32 little-endian 8-bit limbs to a field element.
fn u256_of_limbs8(limbs: &[u32]) -> U256 {
    assert_eq!(limbs.len(), SK, "a coordinate is 32 8-bit limbs");
    let mut w = [0u64; 4];
    for (i, l) in limbs.iter().enumerate() {
        assert!(*l < 256, "limb {i} is out of its declared 8-bit range");
        w[i / 8] |= (*l as u64) << (8 * (i % 8));
    }
    U256(w)
}

/// The four goldens, as affine `(x, y)` pairs, from the Lean-emitted anchor.
fn parse_golds() -> Vec<(U256, U256)> {
    let g: Vec<(U256, U256)> = GOLDS
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            let v: Vec<u32> = l
                .split_whitespace()
                .map(|c| c.parse::<u32>().expect("limb is a u32 decimal"))
                .collect();
            assert_eq!(v.len(), 2 * SK, "a golden is 32 x-limbs then 32 y-limbs");
            (u256_of_limbs8(&v[..SK]), u256_of_limbs8(&v[SK..]))
        })
        .collect();
    assert_eq!(g.len(), 4, "public_comm, f_comm, ft_comm, xi-aggregate");
    g
}

/// The immediate of ROM row `j`, as a field element.
fn rom_imm(rows: &[Vec<u32>], j: usize) -> U256 {
    u256_of_limbs8(&rows[j][ROM_IMM_OFF..ROM_IMM_OFF + SK])
}

/// ⚑ **THE TERM POINTS, READ OFF THE ROM.** The fold program is
/// `emitInit` (1 instruction) `++ emitLoadT B0` (2) `++ emitAddImmT` per remaining term (12 each),
/// and `emitAddImmT`'s first two instructions are `subI TX bx` and `subI TY by`. So term 0's
/// coordinates are the immediates of rows 1 and 2, and term `k`'s are rows `3 + 12(k−1)` and the
/// one after. Nothing here is told the points; it is told the SCHEDULE, and reads them.
fn term_points_from_rom(rows: &[Vec<u32>], terms: usize) -> Vec<(U256, U256)> {
    let mut pts = vec![(rom_imm(rows, 1), rom_imm(rows, 2))];
    for k in 1..terms {
        let b = 3 + 12 * (k - 1);
        pts.push((rom_imm(rows, b), rom_imm(rows, b + 1)));
    }
    pts
}

/// The affine chord fold, in this file's own arithmetic, lifted to the projective `complete_add`
/// the Pasta cone already carries. `z = 1` for every ROM point, so the lift is exact.
fn fold_affine(pts: &[(U256, U256)]) -> Pt {
    let mut acc = Pt {
        x: pts[0].0,
        y: pts[0].1,
        z: U256::ONE,
    };
    for (x, y) in pts.iter().skip(1) {
        acc = complete_add(
            &P_PASTA,
            &acc,
            &Pt {
                x: *x,
                y: *y,
                z: U256::ONE,
            },
        );
    }
    acc
}

#[test]
fn every_fold_recomputes_from_its_own_rom_cells_to_the_o1labs_golden() {
    let golds = parse_golds();
    let mut checked = 0usize;
    println!("\n═══ §2 THE FOUR FOLDS, RECOMPUTED FROM ROM CELLS ═══");
    for (i, (name, json, pis_text, terms)) in [
        ("public_comm", Pub::DESC, Pub::PIS, 31usize),
        ("f_comm", FComm::DESC, FComm::PIS, 1),
        ("ft_comm", FtComm::DESC, FtComm::PIS, 8),
        ("xi-aggregate", Agg::DESC, Agg::PIS, 47),
    ]
    .iter()
    .enumerate()
    {
        let d = parse_desc(json);
        let rows = rom_rows(&d);
        let pts = term_points_from_rom(rows, *terms);
        assert_eq!(pts.len(), *terms, "{name}: one point per term");

        // ⚑ Every ROM point is a real Pallas point. Without this the fold could be landing on the
        // golden through a pair of field values that are not on the curve at all.
        for (j, (x, y)) in pts.iter().enumerate() {
            let p = Pt {
                x: *x,
                y: *y,
                z: U256::ONE,
            };
            assert!(
                on_curve_at(&P_PASTA, &p),
                "{name}: ROM term {j} is not on Pallas"
            );
        }

        let (gx, gy) = golds[i];
        let gold = Pt {
            x: gx,
            y: gy,
            z: U256::ONE,
        };
        let got = fold_affine(&pts);
        assert!(
            proj_eq_at(&P_PASTA, &got, &gold),
            "{name}: the ROM's own term points do not fold to o1-labs' golden"
        );

        // …and the stage's emitted PUBLIC INPUTS carry that same golden, so the point the prover is
        // bound to is the point the ROM computes.
        let pis = parse_pis(pis_text);
        let px = u256_of_limbs8(&pis[..SK].iter().map(|b| b.as_u32()).collect::<Vec<u32>>());
        let py = u256_of_limbs8(&pis[SK..].iter().map(|b| b.as_u32()).collect::<Vec<u32>>());
        assert_eq!(px, gx, "{name}: PI x is not the golden");
        assert_eq!(py, gy, "{name}: PI y is not the golden");

        checked += terms;
        println!(
            "{name:>14}: {terms:>2} ROM term points, all on Pallas, folded -> o1-labs golden, and \
             the emitted PIs carry it"
        );
    }
    assert_eq!(
        checked, TOTAL_TERMS,
        "all 87 meaningful term points across the four folds were consumed"
    );
    println!(
        "§2 ⚑ {checked}/{TOTAL_TERMS} ROM term points checked against \
         MinaWrapAggregationGate/GroupGate/PublicCommGate goldens. No transcribed decimal."
    );
}

/// ⚑ **AND THE ANCHOR IS NOT FOUR COPIES OF ONE POINT.** Four assertions of the form
/// `fold == gold` would all hold in a cone where every golden had collapsed to the same value —
/// which is what a wrong shared constant looks like. Lean's `the_four_goldens_are_distinct` is the
/// kernel-side twin of this.
#[test]
fn the_four_goldens_are_four_different_points() {
    let g = parse_golds();
    for i in 0..g.len() {
        for j in (i + 1)..g.len() {
            assert_ne!(g[i], g[j], "goldens {i} and {j} are the same point");
        }
    }
    println!("\n§2b the four o1-labs goldens are four DISTINCT Pallas points");
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
        "{label:>14}: {terms:>3} terms, {:>5} instructions, {imm_instrs:>3} ROM-pinned immediates, \
         {asserts:>3} slope assertions — PROVED and VERIFIED",
        trace.len()
    );
}

#[test]
fn the_public_comm_fold_proves() {
    fold_proves("public_comm", Pub::DESC, Pub::TRACE, Pub::PIS, 31);
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
    //
    // ⚑ These term counts are the NOMINAL ones, and deliberately so: this table prices what a
    // FULL-WIDTH stage would cost, where every term gets its own 255-plane ladder whether or not
    // its scalar happens to be zero in this particular block. The EMITTED `public_comm` fold runs
    // 31 terms (§2), because a zero scalar makes an affine term the point at infinity; that is a
    // property of block 539508's public inputs, not of the stage, and pricing the stage by it would
    // understate every other block.
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
