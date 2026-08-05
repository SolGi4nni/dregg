//! # The Fq transcript sponge ON the machine — a full Kimchi round over the REAL `fq_kimchi`
//! constants, and a two-element ABSORPTION whose output public input is the digest o1-labs' own
//! `ArithmeticSponge` returns. Both polarities, in RELEASE, with literal refusal text.
//!
//! `pasta_sbox_program_proves.rs` proved `x ↦ x⁷` over the Pasta BASE field — the S-box, the atom.
//! It named what was missing: *"the register allocation for a full round (three S-boxes and the 3×3
//! MDS over the real `fq_kimchi` constants) and the `qLimb` instantiation."* Both are here, and the
//! Lean-authored `Dregg2.Circuit.Emit.MinaWrapVerifierSponge` adds three things the S-box could not
//! say:
//!
//!   * a **FULL ROUND** — 21 multiplies and 9 additions — at a register allocation that cycles with
//!     period three and spends **zero move instructions** (`the_allocation_hands_off`);
//!   * the **`qLimb` INSTANTIATION**, with `alu_add_forces_fq` / `alu_sub_forces_fq` closing the gap
//!     that an ADD row at the Vesta-base modulus forced nothing at all;
//!   * a **55-ROUND PERMUTATION AND AN ABSORPTION**, whose squeeze is
//!     `PastaPoseidonFq.Core.hash fqParams [1,2]` by proof — not by a re-checked constant.
//!
//! ⚑ **THE SPEC IS NOT NEW.** `PastaPoseidonFq` already carried the `fq_kimchi` MDS and 55×3 round
//! constants dumped from `mina_poseidon::pasta::fq_kimchi::static_params()`, a parametric sponge
//! whose Fp instantiation is `PastaPoseidon.Ref` *by proof*, and twelve Fq digests produced by
//! driving the UPSTREAM `ArithmeticSponge` state machine. The Lean side of this rung proves the
//! emitted PROGRAM computes that object; §7 below pins its BYTES.
//!
//! ⚑ **RELEASE, DELIBERATELY.** Algebraic refusals are `debug_assert` PANICS in debug and clean
//! `Err(...)` in release. A refusal test that passes only in debug is testing the assertion, not the
//! constraint system. Every refusal below is asserted on the `Err` string.
//!
//! ⚑ **EVERY FORGERY WRAPS INSIDE THE LIMB WIDTH.** The ALU file records the trap: a forgery that
//! bumped an 8-bit limb from `255` to `256` was refused by a RANGE LOOKUP, so the gate under test
//! was never exercised. `bump_limb8` wraps mod 256, so only the algebra (or the bus, or a pin) can
//! object — and each assertion names which of those must be the one to fire.
//!
//! ⚑ **WHAT THIS DOES NOT SHOW.** That the machine runs Kimchi's `verify`. It runs one stage of
//! six, the field stage; the five MSM stages need curve arithmetic that is not programmed. And it
//! does not show the absorbed values came from a Kimchi transcript — see §4c, which is the theorem
//! about which lie each mechanism is responsible for.
//!
//! Run: `cargo test -p dregg-circuit --release --test pasta_fq_sponge_proves -- --nocapture`

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TableSem, VmConstraint2, decomp_cols_pub,
    parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};

const ROUND_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-fq-round.json");
const ROUND_TRACE: &str = include_str!("fixtures/pasta-fq-round-trace.txt");
const ROUND_PIS: &str = include_str!("fixtures/pasta-fq-round-pis.txt");

const ABSORB_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-fq-absorb.json");
const ABSORB_TRACE: &str = include_str!("fixtures/pasta-fq-absorb-trace.txt");
const ABSORB_PIS: &str = include_str!("fixtures/pasta-fq-absorb-pis.txt");

/// The Lean layout (`MinaWrapVerifierProgram` §1, unmoved), restated so a drift in either side reds
/// here rather than silently addressing a different column.
const PROG_WIDTH: usize = 469;
const X_BASE: usize = 0;
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

/// `MinaWrapVerifierSponge.ROWS_PER_ROUND` — 21 multiplies + 9 additions.
const ROWS_PER_ROUND: usize = 30;
/// `PlonkSpongeConstantsKimchi::PERM_ROUNDS_FULL`.
const FULL_ROUNDS: usize = 55;
/// The machine this extends, so "same committed width" is read off the artifacts.
const SBOX_MACHINE_COMMITTED: usize = 1037;

/// ⚑ **THE UPSTREAM DIGEST.** `PastaPoseidonFq` §4 pins
/// `Core.hash fqParams [1,2]` to this value, and that number was produced by
/// `ArithmeticSponge::<Fq, PlonkSpongeConstantsKimchi, 55>::new(fq_kimchi::static_params())`
/// absorbing `[1,2]` and squeezing once — the o1-labs implementation itself, not a
/// re-transcription. The Lean side proves the emitted program's squeeze IS `Core.hash fqParams
/// [1,2]`; this constant is what makes that a claim about a NUMBER rather than about a name.
const KIMCHI_FQ_HASH_1_2: &str =
    "18721052396410244253982636774728806624181288577958764574163425862396352099420";

fn reg_col(r: usize) -> usize {
    REG_BASE + r * SK
}

fn parse_trace(text: &str, rows: usize) -> Vec<Vec<BabyBear>> {
    let t: Vec<Vec<BabyBear>> = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|c| BabyBear::new(c.parse::<u32>().expect("cell is a u32 decimal")))
                .collect()
        })
        .collect();
    assert_eq!(t.len(), rows, "the Lean-emitted run is {rows} rows");
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
    assert_eq!(
        pis.len(),
        192,
        "three state lanes in, three out, 32 limbs each"
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

/// A forgery that stays INSIDE the declared 8-bit range, so the only thing left that can refuse is
/// the algebra, the lookup bus, or a boundary pin — never a range check.
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

/// Decompose a decimal string into little-endian 8-bit limbs, by repeated division of the DECIMAL
/// representation — so the expected limbs are derived from the upstream digest's own digits and no
/// bignum dependency (and no chance to transcribe a limb wrong) enters the check.
fn decimal_to_limbs(s: &str, n: usize) -> Vec<u32> {
    let mut digits: Vec<u32> = s.bytes().map(|b| u32::from(b - b'0')).collect();
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        let mut rem = 0u32;
        let mut q: Vec<u32> = Vec::with_capacity(digits.len());
        for d in &digits {
            let cur = rem * 10 + d;
            q.push(cur / 256);
            rem = cur % 256;
        }
        while q.len() > 1 && q[0] == 0 {
            q.remove(0);
        }
        out.push(rem);
        digits = q;
    }
    assert_eq!(digits, vec![0], "the value fits in {n} limbs");
    out
}

fn round_desc() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(ROUND_DESC_JSON).expect("the deployed checker parses the round descriptor")
}

fn absorb_desc() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(ABSORB_DESC_JSON)
        .expect("the deployed checker parses the absorption descriptor")
}

fn rom_rows(d: &EffectVmDescriptor2) -> Vec<Vec<u32>> {
    let rom = d
        .tables
        .iter()
        .find(|t| matches!(t.sem, TableSem::ExactPublicRows { .. }))
        .expect("the machine declares an instruction ROM");
    let TableSem::ExactPublicRows { rows } = &rom.sem else {
        unreachable!()
    };
    rows.clone()
}

/// ⚑ **§0 — THE SHAPE, READ OFF THE ARTIFACTS.** Every number this rung quotes is printed from the
/// emitted descriptors, not from a plan.
#[test]
fn the_sponge_has_the_shape_lean_emitted() {
    let dr = round_desc();
    let da = absorb_desc();
    let cr = committed_width(&dr);
    let ca = committed_width(&da);
    let rom_r = rom_rows(&dr);
    let rom_a = rom_rows(&da);

    println!("\n═══ THE Fq TRANSCRIPT SPONGE, ON THE MACHINE ═══");
    for (d, rom, w) in [(&dr, &rom_r, cr), (&da, &rom_a, ca)] {
        println!(
            "{:<28} constraints {:>5}  declared {:>4}  committed {:>5}  PIs {:>4}  ROM {:>5} x 55 \
             = {:>7} cells",
            d.name,
            d.constraints.len(),
            d.trace_width,
            w,
            d.public_input_count,
            rom.len(),
            rom.len() * 55,
        );
    }

    assert_eq!(dr.trace_width, PROG_WIDTH);
    assert_eq!(da.trace_width, PROG_WIDTH);
    assert_eq!(dr.public_input_count, 192);
    assert_eq!(da.public_input_count, 192);
    assert_eq!(
        cr, ca,
        "same machine at two heights, so the slope in §8 is a slope and not two machines"
    );
    assert_eq!(
        cr, SBOX_MACHINE_COMMITTED,
        "and it is the SAME committed width as the S-box machine — the sponge costs no new columns, \
         only instructions"
    );
    assert_eq!(rom_r.len(), 32, "one round + 2 padding, padded to 2^5");
    assert_eq!(
        rom_a.len(),
        2048,
        "2 absorbs + {FULL_ROUNDS} rounds + padding, padded to 2^11"
    );
    // The ROM's key column is `pc + 1`: injective, never zero. That is what makes the permutation
    // balance a POINTWISE identification of trace row j with instruction j.
    for (j, row) in rom_a.iter().enumerate() {
        assert_eq!(row.len(), 55, "manifest row {j} has the declared arity");
        assert_eq!(row[0], j as u32 + 1, "manifest key at index {j} is pc+1");
    }
    println!(
        "\na full round is {ROWS_PER_ROUND} instructions (21 mul / 9 add); {FULL_ROUNDS} of them is \
         {} , plus 2 absorbs = {}",
        FULL_ROUNDS * ROWS_PER_ROUND,
        2 + FULL_ROUNDS * ROWS_PER_ROUND
    );
}

/// ⚑ **§1 — THE HONEST POLARITY OF THE ROUND.** The Lean interpreter's own 32-row run, proved and
/// verified against 192 public inputs on the deployed prover.
#[test]
fn the_full_round_proves_against_its_public_inputs() {
    let d = round_desc();
    let trace = parse_trace(ROUND_TRACE, 32);
    let pis = parse_pis(ROUND_PIS);
    let cell = |r: usize, c: usize| trace[r][c].as_u32();

    // The fixture really is the program Lean says it is: 21 multiplies then 9 additions then
    // padding, and the register file — not the chain edge — carries every value.
    for (pc, row) in trace.iter().enumerate() {
        assert_eq!(
            row[PC_COL].as_u32(),
            pc as u32,
            "row {pc} carries pc = {pc}"
        );
    }
    let muls = (0..ROWS_PER_ROUND)
        .filter(|&r| cell(r, SEL_MUL) == 1)
        .count();
    let adds = (0..ROWS_PER_ROUND)
        .filter(|&r| cell(r, SEL_ADD) == 1)
        .count();
    assert_eq!(
        (muls, adds),
        (21, 9),
        "the round is 21 multiplies and 9 additions — the nine the stage census omitted"
    );
    assert!(
        (0..32).all(|r| cell(r, SEL_CHAIN) == 0),
        "the machine uses no chain edge at all; the register file replaces it"
    );

    // ⚑ THE S-BOX SCHEDULE IS KIMCHI'S OWN, AND IT USES ONE SCRATCH REGISTER. Row 0 squares R0 into
    // R3; row 1 multiplies R0 by R3. `MinaWrapVerifierProgram`'s x²·x⁴·x⁶·x⁷ walk needed two.
    assert_eq!(cell(0, XSEL_BASE), 1, "row 0 reads R0");
    assert_eq!(cell(0, YSEL_BASE), 1, "…times R0");
    assert_eq!(cell(0, WSEL_BASE + 3), 1, "…into the scratch R3");
    assert_eq!(cell(1, XSEL_BASE), 1, "row 1 reads R0");
    assert_eq!(cell(1, YSEL_BASE + 3), 1, "…times the scratch R3");
    assert_eq!(cell(1, WSEL_BASE), 1, "…back into R0, in place");

    // ⚑ AND THE MDS COEFFICIENTS ARE IMMEDIATES — the descriptor's constants, not the prover's.
    // Row 12 is the first MDS multiply: every YSEL off means the y operand is the ROM-pinned
    // immediate.
    assert!(
        (0..NREG).all(|r| cell(12, YSEL_BASE + r) == 0),
        "the first MDS multiply takes its coefficient from the IMMEDIATE"
    );
    assert!(
        (0..SK).any(|i| cell(12, IMM_BASE + i) != 0),
        "and that immediate is a real 254-bit MDS coefficient, not zero"
    );

    // ⚑ THE HAND-OFF: the round's outputs land in R4, R5 and R0 — `the_allocation_hands_off`, on
    // the wire. The last row holds them, three padding instructions after the round finished.
    assert_eq!(
        cell(29, WSEL_BASE),
        1,
        "the last real instruction writes R0"
    );
    for i in 0..SK {
        assert_eq!(
            trace[30][reg_col(0) + i],
            trace[29][Z_BASE + i],
            "limb {i}: R0 at row 30 is row 29's result"
        );
        assert_eq!(
            trace[31][reg_col(0) + i],
            trace[30][reg_col(0) + i],
            "limb {i}: and the padding row HOLDS it — which is what the output pin reads"
        );
    }

    prove_and_verify(&d, &trace, &pis).expect("the honest full round must prove and verify");
    println!(
        "\n§1 HONEST ROUND: one Kimchi full round over the real fq_kimchi constants at qLimb, \
         {ROWS_PER_ROUND} instructions, PROVED and VERIFIED in release against 192 public inputs."
    );
}

/// ⚑ **§2 — THE STATEMENT BINDS AT BOTH ENDS.** Claim a different output state, or a different
/// input state, and the boundary pin must refuse — otherwise the descriptor is a sentence about
/// nothing.
#[test]
fn a_forged_round_state_public_input_is_refused() {
    let d = round_desc();
    let trace = parse_trace(ROUND_TRACE, 32);

    let mut pis = parse_pis(ROUND_PIS);
    pis[96] = bump_limb8(pis[96]); // low limb of the claimed output lane 0
    let err = prove_and_verify(&d, &trace, &pis)
        .expect_err("a claimed output state that is not the round's result must be REFUSED");
    println!("\n§2 forged OUTPUT state PI REFUSED: {err}");
    assert!(!err.is_empty());

    let mut pis = parse_pis(ROUND_PIS);
    pis[0] = bump_limb8(pis[0]);
    let err = prove_and_verify(&d, &trace, &pis)
        .expect_err("a claimed input state that is not the trace's R0 must be REFUSED");
    println!("§2b forged INPUT state PI REFUSED: {err}");
    assert!(!err.is_empty());
}

/// ⚑ **§3 — THE ROUND'S CONSTANTS ARE THE DESCRIPTOR'S.** Move one limb of an MDS coefficient and
/// the ROM must refuse, because the immediate cells ARE tuple entries. This is the gate that makes
/// "multiply by `m₀₁`" a statement the descriptor makes rather than one the witness makes.
#[test]
fn a_prover_chosen_mds_coefficient_is_refused() {
    let d = round_desc();
    let pis = parse_pis(ROUND_PIS);
    let mut trace = parse_trace(ROUND_TRACE, 32);

    // Row 12 is the first MDS multiply; its immediate is the coefficient m₀₀.
    assert!(
        (0..NREG).all(|r| trace[12][YSEL_BASE + r].as_u32() == 0),
        "row 12 takes its y operand from the IMMEDIATE"
    );
    trace[12][IMM_BASE] = bump_limb8(trace[12][IMM_BASE]);

    let err = prove_and_verify(&d, &trace, &pis)
        .expect_err("an MDS coefficient the ROM did not name must be REFUSED");
    println!("\n§3 prover-chosen MDS COEFFICIENT REFUSED: {err}");
    assert!(
        err.contains("exact-public") || err.contains("LookupError") || err.contains("Lookup"),
        "the ROM BUS must refuse a re-chosen coefficient -- got: {err}"
    );
}

/// ⚑ **§4 — ORDER vs SET, AND THE THREE LIES EACH MECHANISM IS RESPONSIBLE FOR.**
///
/// `pasta_sbox_program_proves.rs` established the division on the instruction stream: the ROM
/// permutation fixes WHICH instructions run, the `pc` thread fixes their ORDER. On a sponge the
/// same two poles land on different lies, and the absorb INVERTS them. All three measured here, and
/// each assertion names the mechanism that must be the one to fire.
#[test]
fn the_order_and_the_set_are_fixed_by_different_things() {
    let d = absorb_desc();
    let pis = parse_pis(ABSORB_PIS);

    // ── (a) THE ROUND-CONSTANT SCHEDULE IS THE ROM'S, POINTWISE. Give round 3 the round constant
    // of round 7. Both constants are in the manifest — but not at those keys, so the queried
    // MULTISET changes and the bus refuses. This is the ROM doing sponge-specific work: it pins
    // WHICH constant is used at WHICH round.
    let rom = rom_rows(&d);
    // instruction index of round r's first round-constant add: 2 absorbs + 30r + 17
    let rc_instr = |r: usize| 2 + ROWS_PER_ROUND * r + 17;
    let (i3, i7) = (rc_instr(3), rc_instr(7));
    // the immediate occupies the last 32 cells of the 55-cell instruction word
    assert_ne!(
        rom[i3][23..55],
        rom[i7][23..55],
        "round 3 and round 7 carry different constants, so the swap below is a real lie"
    );

    let mut t = parse_trace(ABSORB_TRACE, 2048);
    for i in 0..SK {
        let a = t[i3][IMM_BASE + i];
        t[i3][IMM_BASE + i] = t[i7][IMM_BASE + i];
        t[i7][IMM_BASE + i] = a;
    }
    let err = prove_and_verify(&d, &t, &pis)
        .expect_err("round 3 using round 7's constant must be REFUSED");
    println!("\n§4a SWAPPED ROUND CONSTANTS REFUSED: {err}");
    assert!(
        err.contains("exact-public") || err.contains("LookupError") || err.contains("Lookup"),
        "the ROM BUS must refuse a round constant used at the wrong round -- got: {err}"
    );

    // ── (b) BUT THE ORDER IS THE pc THREAD'S. Swap two whole rows: each carries its own `pc` cell
    // with it, so the queried multiset is UNCHANGED and the bus stays balanced. The refusal is the
    // pc thread's, an algebraic gate. Same correction `pasta_sbox_program_proves.rs` had to make in
    // flight, re-measured here rather than inherited.
    let mut t = parse_trace(ABSORB_TRACE, 2048);
    t.swap(500, 501);
    let err = prove_and_verify(&d, &t, &pis)
        .expect_err("instructions executed out of ROM order must be REFUSED");
    println!("§4b REORDERED INSTRUCTIONS REFUSED: {err}");
    assert!(
        err.contains("OodEvaluationMismatch"),
        "the pc THREAD (an algebraic gate) must refuse a reorder, not the bus -- got: {err}"
    );

    // ── (c) ⚑ AND ON THE ABSORB THE POLES INVERT. The absorbed values are NOT immediates; they
    // enter through PI-pinned register cells. Swap the two absorbed values in the trace and the ROM
    // is SILENT — every instruction word is unchanged. What refuses is the boundary PIN.
    //
    // So: the ROM fixes the absorb ORDER (which lane each value is added into), and the PUBLIC
    // INPUTS fix the absorb SET (which values those are). That is the exact inverse of the division
    // on the instruction stream, and it is why "the sponge absorbed the transcript" is NOT
    // something this descriptor can say — see the module docblock.
    let mut t = parse_trace(ABSORB_TRACE, 2048);
    for i in 0..SK {
        let a = t[0][reg_col(3) + i];
        t[0][reg_col(3) + i] = t[0][reg_col(4) + i];
        t[0][reg_col(4) + i] = a;
    }
    let err = prove_and_verify(&d, &t, &pis)
        .expect_err("absorbing the two values into the other lanes must be REFUSED");
    println!("§4c SWAPPED ABSORBED VALUES REFUSED: {err}");
    assert!(
        !err.contains("exact-public"),
        "the ROM must be SILENT about the absorbed VALUE -- the pin is what refuses; got: {err}"
    );
    println!(
        "\n⚑ THE DIVISION OF LABOUR, MEASURED:\n  \
         the ROM fixes WHICH round constant runs at WHICH round (a, bus)\n  \
         the pc thread fixes the ORDER the instructions run in (b, gate)\n  \
         the PI pins fix WHICH VALUES are absorbed (c, boundary) -- the ROM says nothing about them"
    );
}

/// ⚑ **§5 — THE REGISTER FILE IS A MEMORY ACROSS 1 650 INSTRUCTIONS.** Move one limb of a register
/// between two rows with no instruction writing it. `reg_hold_forces_preservation` is the Lean
/// theorem; this is the deployed pole, at a distance the S-box instance could not exercise.
#[test]
fn tampering_with_a_held_register_across_the_permutation_is_refused() {
    let d = absorb_desc();
    let pis = parse_pis(ABSORB_PIS);
    let mut trace = parse_trace(ABSORB_TRACE, 2048);

    // The squeeze lane is R4 on the last row (`allocAt 55 0 = 4`), written by the final round and
    // then HELD through 396 padding instructions. If the hold leg did not bite, the output pin
    // would be reading a free cell and §2's refusal would be worth nothing.
    assert_eq!(
        trace[1652][reg_col(4)],
        trace[2047][reg_col(4)],
        "the honest run holds the squeeze lane from row 1652 to row 2047"
    );
    trace[1900][reg_col(4)] = bump_limb8(trace[1900][reg_col(4)]);

    let err = prove_and_verify(&d, &trace, &pis)
        .expect_err("a register that changes with no instruction writing it must be REFUSED");
    println!("\n§5 held-register tamper across 396 padding rows REFUSED: {err}");
    assert!(
        err.contains("OodEvaluationMismatch") || err.contains("boundary") || err.contains("Lookup"),
        "the register WINDOW leg (or the PI pin it feeds) must refuse -- got: {err}"
    );
}

/// ⚑ **§6 — OPERAND ROUTING BITES INSIDE A ROUND.** Change the `x` operand of an MDS multiply so it
/// is no longer the register the instruction names. That row's arithmetic is then internally
/// consistent for a DIFFERENT input, so nothing but the routing gate can catch it.
#[test]
fn an_operand_that_is_not_its_named_register_is_refused() {
    let d = round_desc();
    let pis = parse_pis(ROUND_PIS);
    let mut trace = parse_trace(ROUND_TRACE, 32);

    trace[13][X_BASE] = bump_limb8(trace[13][X_BASE]);

    let err = prove_and_verify(&d, &trace, &pis)
        .expect_err("an x operand that is not the named register must be REFUSED");
    println!("\n§6 mis-routed operand REFUSED: {err}");
    assert!(
        err.contains("OodEvaluationMismatch"),
        "the ROUTING GATE (an algebraic gate) must refuse, not a lookup -- got: {err}"
    );
}

/// ⚑ **§7 — THE ABSORPTION, AND ITS OUTPUT IS THE DIGEST o1-labs' OWN SPONGE RETURNS.**
///
/// This is the one that answers "does one AIR instance prove a Kimchi sponge absorption". The
/// honest 2 048-row run proves and verifies; and the 32 public inputs it claims for the squeeze
/// recompose to `18721052396410244253982636774728806624181288577958764574163425862396352099420`,
/// which is `ArithmeticSponge::<Fq, PlonkSpongeConstantsKimchi, 55>::new(fq_kimchi::static_params())`
/// absorbing `[1,2]` and squeezing once.
///
/// ⚠ The BYTE pin lives here and the SHAPE pin lives in Lean, which is the split this repo already
/// uses: `the_absorb_program_squeezes_the_kimchi_hash` proves the emitted program's squeeze is
/// `Core.hash fqParams [1,2]` for EVERY input pair, and the constant below is what makes that a
/// claim about a number.
#[test]
fn the_absorption_proves_and_its_squeeze_is_the_upstream_kimchi_digest() {
    let d = absorb_desc();
    let trace = parse_trace(ABSORB_TRACE, 2048);
    let pis = parse_pis(ABSORB_PIS);

    // The sponge starts FRESH: the three initial state lanes are pinned to zero. Without this the
    // descriptor's statement would be about a sponge somebody else had already absorbed into.
    assert!(
        (0..3 * SK).all(|i| pis[i].as_u32() == 0),
        "the first 96 public inputs are the zero state of a fresh Kimchi sponge"
    );
    // …and the two absorbed values are 1 and 2, the pair `PastaPoseidonFq` measured upstream on.
    assert_eq!(pis[3 * SK].as_u32(), 1, "x0 = 1");
    assert!((1..SK).all(|i| pis[3 * SK + i].as_u32() == 0));
    assert_eq!(pis[4 * SK].as_u32(), 2, "x1 = 2");
    assert!((1..SK).all(|i| pis[4 * SK + i].as_u32() == 0));

    // ⚑ THE DIGEST, RECOMPOSED FROM THE UPSTREAM DECIMAL rather than transcribed as limbs.
    let expected = decimal_to_limbs(KIMCHI_FQ_HASH_1_2, SK);
    let got: Vec<u32> = (0..SK).map(|i| pis[5 * SK + i].as_u32()).collect();
    assert_eq!(
        got, expected,
        "the emitted squeeze public inputs must be the limbs of the upstream Kimchi Fq digest"
    );

    prove_and_verify(&d, &trace, &pis)
        .expect("the honest absorption must prove and verify against its 192 public inputs");
    println!(
        "\n§7 ⚑ ONE AIR INSTANCE PROVES A KIMCHI SPONGE ABSORPTION.\n  \
         fresh state (0,0,0) -> absorb [1,2] -> {FULL_ROUNDS} full rounds -> squeeze lane 0\n  \
         = {KIMCHI_FQ_HASH_1_2}\n  \
         2048 rows, 192 public inputs, PROVED and VERIFIED in release."
    );
}

/// ⚑ **§8 — WHAT A ROUND COSTS, AS A SLOPE.**
///
/// ⚠ **THE SLOPE, NOT THE QUOTIENT.** A 32-row instance is almost entirely the prover's FIXED cost;
/// dividing it by 32 manufactures a per-instruction figure wrong by orders. The number reported is
/// the difference between the 2^11 and the 2^5 instance over the 2 016 instructions between them.
///
/// ⚑ **THE PROBE ROW WHOSE TRUE COST IS ALREADY KNOWN** is the 32-row honest run: if it does not
/// prove here, every number below is noise, and it is asserted rather than displayed. The first
/// prove in the process is DISCARDED — a lane in this campaign once measured a cold start and would
/// have shipped a fake 12×.
#[test]
fn the_sponge_is_priced_per_instruction() {
    let dr = round_desc();
    let da = absorb_desc();
    let tr = parse_trace(ROUND_TRACE, 32);
    let ta = parse_trace(ABSORB_TRACE, 2048);
    let pr = parse_pis(ROUND_PIS);
    let pa = parse_pis(ABSORB_PIS);
    let committed = committed_width(&dr);

    // ⚠ COLD START, DISCARDED. Not reported.
    prove_and_verify(&dr, &tr, &pr)
        .expect("the probe run must prove; nothing below means anything otherwise");

    let t0 = std::time::Instant::now();
    prove_and_verify(&dr, &tr, &pr).expect("the 32-row probe proves warm");
    let small_ms = t0.elapsed().as_secs_f64() * 1000.0;

    let t1 = std::time::Instant::now();
    prove_and_verify(&da, &ta, &pa).expect("the 2^11 absorption proves");
    let big_ms = t1.elapsed().as_secs_f64() * 1000.0;

    let slope_us = (big_ms - small_ms) * 1000.0 / (2048.0 - 32.0);

    println!("\n═══ §8  THE SPONGE, PRICED ═══");
    println!(
        "committed width {committed}; one instruction commits {} bytes of trace",
        committed * 4
    );
    println!(
        "\n{:>12}  {:>12}  {:>12}",
        "instructions", "prove ms", "trace MiB"
    );
    for (n, ms) in [(32usize, small_ms), (2048usize, big_ms)] {
        println!(
            "{n:>12}  {ms:>12.1}  {:>12.2}",
            (n * committed * 4) as f64 / (1024.0 * 1024.0)
        );
    }
    println!(
        "\nSLOPE: {slope_us:.1} us/instruction (the 32-row quotient would have said {:.1} -- \
         {:.1}x too high; the fixed cost is {:.1} ms of it).",
        small_ms * 1000.0 / 32.0,
        (small_ms * 1000.0 / 32.0) / slope_us,
        small_ms - 32.0 * slope_us / 1000.0
    );
    println!("⚠ two-point fit at 2^5/2^11; FRI is O(n log n), so this slope is a FLOOR at 2^19.");

    // ⚑ THE STAGE, RE-PRICED IN THE UNITS A ROUND ACTUALLY COSTS. The census
    // (`MinaWrapVerifierAir.ROWS_PER_POSEIDON_PERM`) counted 21 multiplies per round and omitted
    // the nine additions the MDS sums and the round constants need. `the_census_underprices_the_round`
    // is the Lean `decide`; this is what it costs.
    const CENSUS_PER_PERM: usize = 1155;
    let measured_per_perm = FULL_ROUNDS * ROWS_PER_ROUND;
    let stage = 148 * measured_per_perm;
    println!(
        "\nA PERMUTATION: census {CENSUS_PER_PERM} rows, MEASURED {measured_per_perm} -- the census \
         is low by {:.1}%, because it counted 21 multiplies and no additions.",
        100.0 * (measured_per_perm as f64 / CENSUS_PER_PERM as f64 - 1.0)
    );
    println!(
        "THE TRANSCRIPT STAGE (148 permutations): {stage} instructions, {:.1}% of the 610 080-\
         instruction ROM cap (the census said 28.0%).",
        100.0 * stage as f64 / 610_080.0
    );
    println!(
        "  trace {:.2} GB, pads to 2^{}; prove >= {:.1} min at this slope and the deployed lb=6.",
        stage as f64 * committed as f64 * 4.0 / 1e9,
        stage.next_power_of_two().trailing_zeros(),
        stage as f64 * slope_us / 1e6 / 60.0,
    );
    assert!(
        stage < 610_080,
        "if the re-priced transcript stage ever stops fitting one ROM, \
         `the_repriced_transcript_stage_still_fits` in Lean is stale"
    );
    assert!(slope_us.is_finite() && slope_us > 0.0);
}
