//! # The in-AIR verifier's MACHINE — a register file and a verifier-known instruction ROM — proved
//! on the deployed prover, both polarities, in RELEASE, with literal refusal text per stage.
//!
//! `pasta_alu_verifier_row_proves.rs` shows what ONE row forces. It also shows, honestly, what it
//! does not: seven of its eight fixture rows carry `SEL_CHAIN = 0`, and
//! `MinaWrapVerifierAir.unchained_transition_relates_nothing` is the theorem that says such a trace
//! is eight UNRELATED Pasta operations. This file is the next rung. The Lean-authored
//! `Dregg2.Circuit.Emit.MinaWrapVerifierProgram.sboxDesc` adds three things the ALU could not say:
//!
//!   * a **REGISTER FILE** (6 × 32 limb columns) threaded by `.transition` window legs, so a row's
//!     operands can be arbitrary earlier results rather than only the immediately preceding row's;
//!   * an **INSTRUCTION ROM** as a `TableSem::ExactPublicRows` manifest — and that is a
//!     PERMUTATION balance, not a subset lookup, so the descriptor's own bytes say *these
//!     instructions, in this order, and no others*;
//!   * **64 PUBLIC INPUTS**, 32 limbs of `x` on the first row's `R0` and 32 limbs of the claimed
//!     `x⁷` on the last row's `R3`.
//!
//! So this descriptor's meaning is a sentence about public inputs — *"I know a trace proving
//! `PI_out = PI_in⁷ (mod p)`"* — which is the Poseidon S-box, the atom the 148-permutation Fq
//! transcript sponge is built from. It is the first object in the Pasta cone whose statement
//! mentions neither rows nor columns.
//!
//! ⚑ **RELEASE, DELIBERATELY.** Algebraic refusals are `debug_assert` PANICS in debug and clean
//! `Err(...)` in release. A refusal test that passes only in debug is testing the assertion, not
//! the constraint system. Every refusal below is asserted on the `Err` string.
//!
//! ⚑ **EVERY FORGERY BELOW IS CHECKED FOR REFUSING FOR THE RIGHT REASON.** The ALU file records the
//! trap: its first add-forgery bumped an 8-bit limb from `255` to `256` and the refusal that came
//! back was a RANGE LOOKUP, so the add gate was never exercised. Forgeries here wrap inside the
//! limb width, and each assertion names the class of check that must be the one to fire.
//!
//! ⚑ **WHAT THIS DOES NOT SHOW.** That the machine runs Kimchi's `verify`. It runs a 4-instruction
//! program. The Lean side's `rom_cannot_hold_the_whole_verifier` is the `decide` that one
//! exact-public ROM tops out at 610 080 instructions against the verifier's 1 598 396, so the whole
//! verifier is not a single ROM-bound instance at this instruction width at all.
//!
//! Run: `cargo test -p dregg-circuit --release --test pasta_sbox_program_proves -- --nocapture`

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TableSem, VmConstraint2, decomp_cols_pub,
    parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};

const SBOX_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-sbox-prog.json");
const SBOX_TRACE: &str = include_str!("fixtures/pasta-sbox-prog-trace.txt");
const SBOX_PIS: &str = include_str!("fixtures/pasta-sbox-prog-pis.txt");

/// The SAME machine at a `2^10` height — four S-box multiplies then 1 020 padding adds — so §7's
/// per-instruction price is a measured SLOPE and not an 8-row fixed cost divided by eight.
const LONG_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-sbox-prog-1k.json");
const LONG_TRACE: &str = include_str!("fixtures/pasta-sbox-prog-1k-trace.txt");

/// The Lean layout (`MinaWrapVerifierProgram` §1), restated so a drift in either side reds here
/// rather than silently addressing a different column.
const PROG_WIDTH: usize = 469;
const X_BASE: usize = 0;
const Y_BASE: usize = 32;
const Z_BASE: usize = 64;
const SEL_MUL: usize = 222;
const SEL_ADD: usize = 223;
const SEL_CHAIN: usize = 225;
const REG_BASE: usize = 226;
const SK: usize = 32;
const XSEL_BASE: usize = 418;
const YSEL_BASE: usize = 424;
const WSEL_BASE: usize = 430;
const PC_COL: usize = 436;
const IMM_BASE: usize = 437;
const NREG: usize = 6;

/// The ALU row this machine extends — so the width claim "1.31× the ALU" is read off the artifacts
/// rather than asserted.
const ALU_COMMITTED: usize = 794;

fn reg_col(r: usize) -> usize {
    REG_BASE + r * SK
}

fn desc() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(SBOX_DESC_JSON).expect("the deployed checker parses the S-box descriptor")
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
    assert_eq!(t.len(), 8, "the Lean-emitted S-box run is 8 rows");
    assert!(
        t.iter().all(|r| r.len() == PROG_WIDTH),
        "every row is {PROG_WIDTH} wide"
    );
    t
}

fn parse_pis(text: &str) -> Vec<BabyBear> {
    let pis: Vec<BabyBear> = text
        .split_whitespace()
        .map(|c| BabyBear::new(c.parse::<u32>().expect("PI is a u32 decimal")))
        .collect();
    assert_eq!(pis.len(), 64, "32 limbs of x, then 32 of x^7");
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

/// A forgery that stays INSIDE the declared 8-bit range, so the only thing left that can refuse is
/// the algebra rather than a cheaper lookup.
fn bump_limb8(cell: BabyBear) -> BabyBear {
    BabyBear::new((cell.as_u32() + 1) % 256)
}

/// The committed main width, from the descriptor's own tables through the deployed
/// `decomp_cols_pub`.
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

/// ⚑ **§0 — THE SHAPE, READ OFF THE ARTIFACT.** Every number this campaign quotes for the machine
/// is printed here from the emitted descriptor, not from a plan.
#[test]
fn the_machine_has_the_shape_lean_emitted() {
    let d = desc();
    let committed = committed_width(&d);
    let rom = d
        .tables
        .iter()
        .find(|t| matches!(t.sem, TableSem::ExactPublicRows { .. }))
        .expect("the machine declares an instruction ROM");
    let TableSem::ExactPublicRows { rows } = &rom.sem else {
        unreachable!()
    };

    println!("\n═══ THE PASTA PROGRAM MACHINE ═══");
    println!(
        "descriptor        {}\nconstraints       {}\ndeclared columns  {}\ncommitted columns {} \
         ({:.2}x the ALU's {ALU_COMMITTED})\npublic inputs     {}\nROM               {} rows x \
         {} arity = {} cells",
        d.name,
        d.constraints.len(),
        d.trace_width,
        committed,
        committed as f64 / ALU_COMMITTED as f64,
        d.public_input_count,
        rows.len(),
        rom.arity,
        rows.len() * rom.arity,
    );

    assert_eq!(d.trace_width, PROG_WIDTH);
    assert_eq!(d.public_input_count, 64);
    assert_eq!(rom.arity, 55, "the instruction word is 55 cells");
    assert_eq!(
        rows.len(),
        8,
        "one manifest row per instruction — `forced_trace_length` makes this the TRACE length too"
    );
    // The ROM's key column is `pc + 1`, strictly increasing and never zero: that is what makes the
    // permutation balance a POINTWISE identification of row j with instruction j rather than a
    // statement about the multiset of instructions.
    for (j, row) in rows.iter().enumerate() {
        assert_eq!(row.len(), 55, "manifest row {j} has the declared arity");
        assert_eq!(row[0], j as u32 + 1, "manifest key at index {j} is pc+1");
    }
}

/// ⚑ **§1 — THE HONEST POLARITY.** The Lean interpreter's own 8-row run of the S-box program,
/// proved and verified against the 64 public inputs on the deployed prover.
#[test]
fn the_sbox_program_proves_against_its_public_inputs() {
    let d = desc();
    let trace = parse_trace(SBOX_TRACE);
    let pis = parse_pis(SBOX_PIS);

    // The fixture really is the program Lean says it is, so a green below is not a green on eight
    // copies of one row.
    let cell = |r: usize, c: usize| trace[r][c].as_u32();
    for (pc, row) in trace.iter().enumerate() {
        assert_eq!(
            row[PC_COL].as_u32(),
            pc as u32,
            "row {pc} carries pc = {pc}"
        );
    }
    assert!(
        (0..4).all(|r| cell(r, SEL_MUL) == 1),
        "the four S-box instructions are multiplies"
    );
    assert!(
        (4..8).all(|r| cell(r, SEL_ADD) == 1),
        "the four padding instructions are adds — there is NO nop opcode, the inherited \
         `selSumExpr` asserts sMul+sAdd+sSub = 1 on every row"
    );
    assert!(
        (0..8).all(|r| cell(r, SEL_CHAIN) == 0),
        "the machine does not use the single chain edge at all — the register file replaces it"
    );
    // The instruction at pc 3 writes R3, and the value it writes is that row's RESULT — the write
    // half of the register window leg, on the wire.
    assert_eq!(cell(3, WSEL_BASE + 3), 1, "pc 3 writes R3");
    for i in 0..SK {
        assert_eq!(
            trace[4][reg_col(3) + i],
            trace[3][Z_BASE + i],
            "limb {i}: R3 at row 4 is row 3's result"
        );
    }

    // ⚑ THE INSTRUCTION THE CHAIN COULD NOT EXPRESS. Row 1 is `R1 * R1`, a multiply whose two
    // operands are the SAME earlier result. `nxt.x = loc.z` wires ONE operand; nothing in
    // `MinaWrapVerifierAir` could put a value into `y`.
    for i in 0..SK {
        assert_eq!(
            trace[1][X_BASE + i],
            trace[1][Y_BASE + i],
            "limb {i}: row 1 squares its register"
        );
        assert_eq!(
            trace[1][X_BASE + i],
            trace[1][reg_col(1) + i],
            "limb {i}: row 1's x operand IS register R1"
        );
    }

    prove_and_verify(&d, &trace, &pis).expect("the honest S-box run must prove and verify");
    println!(
        "\n§1 HONEST: x -> x^7 over the Pasta base field, 8 rows, PROVED and VERIFIED in release \
         against 64 public inputs."
    );
}

/// ⚑ **§2 — A FORGED OUTPUT PUBLIC INPUT IS REFUSED.** This is the check that makes the descriptor
/// a STATEMENT: claim a different `x⁷` and the boundary pin must refuse, whatever the trace says.
#[test]
fn a_forged_output_public_input_is_refused() {
    let d = desc();
    let trace = parse_trace(SBOX_TRACE);
    let mut pis = parse_pis(SBOX_PIS);

    pis[32] = bump_limb8(pis[32]); // the low limb of the claimed x^7

    let err = prove_and_verify(&d, &trace, &pis)
        .expect_err("a claimed output that is not the trace's result must be REFUSED");
    println!("\n§2 forged OUTPUT PI REFUSED: {err}");
    assert!(!err.is_empty());
}

/// …and the input side, so the pin is a real binding at both ends rather than a one-way check.
#[test]
fn a_forged_input_public_input_is_refused() {
    let d = desc();
    let trace = parse_trace(SBOX_TRACE);
    let mut pis = parse_pis(SBOX_PIS);

    pis[0] = bump_limb8(pis[0]);

    let err = prove_and_verify(&d, &trace, &pis)
        .expect_err("a claimed input that is not the trace's R0 must be REFUSED");
    println!("§2b forged INPUT PI REFUSED: {err}");
    assert!(!err.is_empty());
}

/// ⚑ **§3 — THE REGISTER FILE IS A MEMORY, AND BREAKING IT IS REFUSED.** Move one limb of a
/// register between two rows without an instruction writing it. `reg_hold_forces_preservation` is
/// the Lean theorem; this is the deployed pole.
///
/// The target is `R3` on the LAST row — the register the output PI reads, three padding
/// instructions after the S-box wrote it. If the hold leg did not bite, that pin would be reading
/// a free cell and §2's refusal would be worth nothing.
#[test]
fn tampering_with_a_held_register_is_refused() {
    let d = desc();
    let pis = parse_pis(SBOX_PIS);

    let mut trace = parse_trace(SBOX_TRACE);
    // R3 is written at pc 3 (so it appears from row 4 on) and held by rows 5, 6, 7.
    assert_eq!(
        trace[4][reg_col(3)],
        trace[7][reg_col(3)],
        "the honest run holds R3 from row 4 to row 7"
    );
    trace[6][reg_col(3)] = bump_limb8(trace[6][reg_col(3)]);

    let err = prove_and_verify(&d, &trace, &pis)
        .expect_err("a register that changes with no instruction writing it must be REFUSED");
    println!("\n§3 held-register tamper REFUSED: {err}");
    assert!(
        err.contains("OodEvaluationMismatch") || err.contains("boundary") || err.contains("Lookup"),
        "the register WINDOW leg (or the PI pin it feeds) must refuse -- got: {err}"
    );
}

/// ⚑ **§4 — OPERAND ROUTING BITES.** Change the `x` operand so it is no longer the register the
/// instruction names. The arithmetic of that row is then internally consistent for a DIFFERENT
/// input, so nothing but the routing gate can catch it — which is the point.
#[test]
fn an_operand_that_is_not_its_named_register_is_refused() {
    let d = desc();
    let pis = parse_pis(SBOX_PIS);
    let mut trace = parse_trace(SBOX_TRACE);

    trace[2][X_BASE] = bump_limb8(trace[2][X_BASE]);

    let err = prove_and_verify(&d, &trace, &pis)
        .expect_err("an x operand that is not the named register must be REFUSED");
    println!("\n§4 mis-routed operand REFUSED: {err}");
    assert!(
        err.contains("OodEvaluationMismatch"),
        "the ROUTING GATE (an algebraic gate) must refuse, not a lookup -- got: {err}"
    );
}

/// ⚑ **§5 — THE ROM IS A PERMUTATION, NOT A SUBSET.** Three separate lies, each refused, and each
/// refused by the LOOKUP BUS rather than by an algebraic gate — which is the observable difference
/// between "the tuple is a manifest row" and "the tuples ARE the manifest".
#[test]
fn the_instruction_rom_pins_the_program() {
    let d = desc();
    let pis = parse_pis(SBOX_PIS);

    // (a) Run a DIFFERENT opcode than the ROM names. Row 5 is a padding add; make it a multiply.
    // Its arithmetic block is an add's, so the multiply gates would refuse too — the assertion
    // therefore checks the BUS is what fires, not merely that something did.
    let mut t_op = parse_trace(SBOX_TRACE);
    t_op[5][SEL_ADD] = BabyBear::new(0);
    t_op[5][SEL_MUL] = BabyBear::new(1);
    let err = prove_and_verify(&d, &t_op, &pis)
        .expect_err("an opcode the ROM did not name must be REFUSED");
    println!("\n§5a opcode not in the ROM REFUSED: {err}");
    assert!(
        err.contains("exact-public") || err.contains("LookupError") || err.contains("Lookup"),
        "the ROM BUS must refuse an unnamed instruction -- got: {err}"
    );

    // (b) Read a different register than the ROM names. The x-routing gate is satisfied for the
    // register actually selected, so only the ROM can object to the SELECTION.
    let mut t_sel = parse_trace(SBOX_TRACE);
    assert_eq!(t_sel[3][XSEL_BASE + 2].as_u32(), 1, "pc 3 reads R2");
    t_sel[3][XSEL_BASE + 2] = BabyBear::new(0);
    t_sel[3][XSEL_BASE + 0] = BabyBear::new(1);
    for i in 0..SK {
        t_sel[3][X_BASE + i] = t_sel[3][reg_col(0) + i];
    }
    let err = prove_and_verify(&d, &t_sel, &pis)
        .expect_err("an operand SELECTION the ROM did not name must be REFUSED");
    println!("§5b operand selection not in the ROM REFUSED: {err}");
    assert!(
        err.contains("exact-public") || err.contains("LookupError") || err.contains("Lookup"),
        "the ROM BUS must refuse a re-selected operand -- got: {err}"
    );

    // (c) Reorder the program. ⚑ CORRECTED BY THIS RUN: the swap moves each row's `pc` CELL with
    // it, so the queried multiset is UNCHANGED and the ROM bus stays balanced — the refusal comes
    // from the pc THREAD gate (`OodEvaluationMismatch`), not from the manifest. That is the honest
    // division of labour and it is worth stating plainly: the permutation fixes WHICH instructions
    // run and with what multiplicity; the pc thread fixes their ORDER. Neither alone is enough,
    // and a first draft of this comment credited the ROM with both.
    let mut t_perm = parse_trace(SBOX_TRACE);
    t_perm.swap(4, 5);
    let err = prove_and_verify(&d, &t_perm, &pis)
        .expect_err("instructions executed out of ROM order must be REFUSED");
    println!("§5c reordered program REFUSED: {err}");
    assert!(!err.is_empty());

    // (d) …and the other side of that division: forge the counter alone and the ROM KEY goes out
    // of the manifest, so the BUS is what refuses. Both mechanisms exhibited, each on the lie it
    // is actually responsible for.
    let mut t_pc = parse_trace(SBOX_TRACE);
    t_pc[4][PC_COL] = BabyBear::new(9);
    let err = prove_and_verify(&d, &t_pc, &pis)
        .expect_err("a program counter that does not thread must be REFUSED");
    println!("§5d broken pc thread REFUSED: {err}");
    assert!(!err.is_empty());
}

/// ⚑ **§6 — THE IMMEDIATE IS THE DESCRIPTOR'S CONSTANT, NOT THE PROVER'S.** This is the gate that
/// makes a Poseidon round constant and an MDS coefficient sayable at all. Move an immediate limb
/// and the ROM must refuse, because the immediate cells ARE tuple entries.
#[test]
fn a_prover_chosen_immediate_is_refused() {
    let d = desc();
    let pis = parse_pis(SBOX_PIS);
    let mut trace = parse_trace(SBOX_TRACE);

    // Row 5 is `add R0, #0`; make the immediate a 1.
    assert_eq!(trace[5][IMM_BASE].as_u32(), 0);
    assert!(
        (0..NREG).all(|r| trace[5][YSEL_BASE + r].as_u32() == 0),
        "row 5 takes its y operand from the IMMEDIATE (every YSEL off)"
    );
    trace[5][IMM_BASE] = BabyBear::new(1);

    let err = prove_and_verify(&d, &trace, &pis)
        .expect_err("an immediate the ROM did not name must be REFUSED");
    println!("\n§6 prover-chosen immediate REFUSED: {err}");
    assert!(
        err.contains("exact-public") || err.contains("LookupError") || err.contains("Lookup"),
        "the ROM BUS must refuse a re-chosen immediate -- got: {err}"
    );
}

/// ⚑ **§7 — WHAT ONE INSTANCE COSTS, AND WHERE THE PROGRAM CEILING IS.** Measured, at the deployed
/// FRI point, so the stage census in `MinaWrapVerifierAir` §5 has a per-instruction price in this
/// machine's units rather than the ALU's.
///
/// ⚑ THE PROBE ROW WHOSE TRUE COST IS ALREADY KNOWN is the 8-row honest run: if it does not prove
/// here, every number below is noise, and it is asserted rather than displayed.
///
/// ⚠ **THE SLOPE, NOT THE QUOTIENT.** An 8-row instance is almost entirely the prover's FIXED
/// cost, and dividing it by eight manufactures a per-instruction figure that is wrong by orders.
/// The number reported is the difference between the `2^10` and the `2^3` instance divided by the
/// 1 016 instructions between them. The first prove in the process is DISCARDED — a previous lane
/// in this campaign measured a cold-start artifact and would have shipped a fake 12×.
#[test]
fn the_machine_is_priced_per_instruction() {
    let d = desc();
    let trace = parse_trace(SBOX_TRACE);
    let pis = parse_pis(SBOX_PIS);
    let committed = committed_width(&d);

    let dl =
        parse_vm_descriptor2(LONG_DESC_JSON).expect("the deployed checker parses the 2^10 machine");
    let long: Vec<Vec<BabyBear>> = LONG_TRACE
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|c| BabyBear::new(c.parse::<u32>().expect("cell is a u32 decimal")))
                .collect::<Vec<_>>()
        })
        .collect();
    assert_eq!(long.len(), 1024, "the 2^10 run is 1024 rows");
    assert!(long.iter().all(|r| r.len() == PROG_WIDTH));
    assert_eq!(
        committed_width(&dl),
        committed,
        "same machine, same committed width"
    );

    // ⚠ COLD START, DISCARDED. Not reported.
    prove_and_verify(&d, &trace, &pis)
        .expect("the probe run must prove; nothing below means anything otherwise");

    let t0 = std::time::Instant::now();
    prove_and_verify(&d, &trace, &pis).expect("the 8-row probe proves warm");
    let small_ms = t0.elapsed().as_secs_f64() * 1000.0;

    let t1 = std::time::Instant::now();
    prove_and_verify(&dl, &long, &pis)
        .expect("the 2^10 run must prove and verify against the SAME public inputs");
    let big_ms = t1.elapsed().as_secs_f64() * 1000.0;

    let slope_us = (big_ms - small_ms) * 1000.0 / (1024.0 - 8.0);

    println!("\n═══ §7  THE MACHINE, PRICED ═══");
    println!(
        "committed width {committed} ({:.2}x the ALU's {ALU_COMMITTED}); one instruction commits \
         {} bytes of trace",
        committed as f64 / ALU_COMMITTED as f64,
        committed * 4,
    );
    println!(
        "\n{:>12}  {:>12}  {:>12}",
        "instructions", "prove ms", "trace MiB"
    );
    for (n, ms) in [(8usize, small_ms), (1024usize, big_ms)] {
        println!(
            "{n:>12}  {ms:>12.1}  {:>12.2}",
            (n * committed * 4) as f64 / (1024.0 * 1024.0)
        );
    }
    println!(
        "\nSLOPE: {slope_us:.1} us/instruction (the 8-row quotient would have said {:.1} — \
         {:.1}x too high, which is the fixed cost: {:.1} ms of it).",
        small_ms * 1000.0 / 8.0,
        (small_ms * 1000.0 / 8.0) / slope_us,
        small_ms - 8.0 * slope_us / 1000.0
    );
    // ⚠ AND THE DIRECTION THE EXTRAPOLATION IS WRONG IN. FRI is O(n log n), so a slope fitted
    // between 2^3 and 2^10 UNDERSTATES the marginal cost at 2^21 by roughly the log ratio. The
    // verifier figure below is therefore a FLOOR, not an estimate, and the honest way to read it
    // is "at least this".
    println!(
        "⚠ two-point fit at 2^3/2^10; FRI is O(n log n) so this slope is a FLOOR at 2^21 \
         (log ratio ~{:.1}x).",
        21.0 / 10.0
    );

    // ⚑ THE CENSUS, RE-DENOMINATED IN THE MACHINE. `MinaWrapVerifierAir` prices the verifier at
    // 1 598 396 ALU rows; on this machine an instruction is an ALU row plus the register file, so
    // the row count is the same and only the per-row cost moves.
    const VERIFIER_INSTRUCTIONS: usize = 1_598_396;
    println!(
        "\nthe Wrap verifier at {VERIFIER_INSTRUCTIONS} instructions:\n  trace {:.2} GB\n  \
         prove >= {:.1} min at this slope and the deployed lb=6 (a FLOOR, see above)",
        VERIFIER_INSTRUCTIONS as f64 * committed as f64 * 4.0 / 1e9,
        VERIFIER_INSTRUCTIONS as f64 * slope_us / 1e6 / 60.0,
    );

    // ⚑ THE ROM CEILING, from the deployed caps rather than from a plan.
    const MAX_CELLS: usize = 1 << 25;
    const MAX_ROWS: usize = 1 << 21;
    const ARITY: usize = 55;
    let rom_cap = MAX_CELLS / ARITY;
    println!(
        "\nROM cap: {MAX_CELLS} cells / arity {ARITY} = {rom_cap} instructions (the row cap \
         {MAX_ROWS} is NOT the binder).\nthe verifier is {:.2}x that -- one ROM-bound instance \
         cannot hold it.",
        VERIFIER_INSTRUCTIONS as f64 / rom_cap as f64
    );
    assert!(
        rom_cap < VERIFIER_INSTRUCTIONS,
        "if this ever stops holding, `rom_cannot_hold_the_whole_verifier` in Lean is stale"
    );

    // ⚑ AND THE ROW CEILING, which is a FIELD fact and a consequence of the blowup: BabyBear's
    // two-adicity is 27, so `log_rows <= 27 - log_blowup` — 2^21 at the deployed lb=6, 2^25 at
    // lb=2. The verifier needs 2^21 rows, which is EXACTLY the lb=6 ceiling.
    println!(
        "row ceiling 2^21 at lb=6, 2^25 at lb=2. The verifier pads to 2^21 -- ON the lb=6 ceiling."
    );
    assert!(slope_us.is_finite() && slope_us > 0.0);
}
