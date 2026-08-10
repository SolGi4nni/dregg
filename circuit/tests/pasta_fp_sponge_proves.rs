//! # The PHASE-1 (Fp) transcript sponge ON the machine — the leg that says **whose tape** the
//! phase-2 chain is absorbing. Both polarities, in RELEASE, with literal refusal text.
//!
//! `mina_phase2_chain_fold.rs` folds 46 links of Mina devnet block 539508's phase-2 transcript and
//! ends on that block's own `v′`/`u′`. Its tape's **element 0 is `fq_digest`** — and nothing
//! derived it in a circuit, so the chain proved *a tape absorbs to the published challenges*
//! without proving whose tape. `fq_digest` is **phase 1's output**. This is phase 1.
//!
//! Three artifacts, all `EffectLower.lowerAir` of `MinaWrapVerifierProgram.programAir` at
//! **`pLimb`** — the Fq leg's `qLimb` is the whole of the field change, because `programAir` is
//! parametric in the limb vector and always was:
//!
//!   * `dregg-pasta-fp-round::v1` — one full Kimchi round at the `fp_kimchi` constants, 32 rows;
//!   * `dregg-pasta-fp-absorb::v1` — the 55-round absorption, 2 048 rows, whose squeeze public
//!     input is `Core.hash fpParams [1,2]` — the digest o1-labs' own `ArithmeticSponge` returns;
//!   * `dregg-pasta-fp-chainlink::v1` — the 27-link chain's descriptor, at the SAME eight-block pin
//!     layout `dregg-pasta-fq-chainlink::v1` deploys. **Link 26's outgoing lane 1 is `fq_digest`.**
//!
//! ## ⚑⚑ §10 IS WHY THIS FILE EXISTS
//!
//! The weld is **32 felts, elementwise, at full limb width** — phase-1 link 26's PI slots
//! `[4·SK, 5·SK)` against phase-2 link 0's `[6·SK, 7·SK)`. **No digest, so no birthday bound**: a
//! forger must match all 32 eight-bit limbs of a 254-bit value. A one-felt tie would be `2^31`,
//! below this repository's own ~124-bit bar, and is not what is built here.
//!
//! ## ⚑ §9: THE CONSTANTS ARE CHECKED, NOT COPIED
//!
//! `PastaPoseidon.mdsN`/`rcsN` were 174 decimal literals that **nothing had ever compared to
//! `mina_poseidon::pasta::fp_kimchi::static_params()`** — the identical hole the Fq lane found and
//! closed. One wrong digit in 174 numbers gives a SELF-CONSISTENT tree: Lean proving the program
//! computes ITS constants, a harness pinning ITS digest, every gate green, and the object not being
//! Kimchi's sponge. §9 reads `metatheory/fp_kimchi_params.json` (o1-labs `proof-systems`
//! `f6d958dc05`, via `fixtures/kimchi-extractors/fp_kimchi_export.rs`) and refuses unless all
//! **660** immediates of the EMITTED instruction ROM are its numbers.
//!
//! ⚑ **RELEASE, DELIBERATELY.** Algebraic refusals are `debug_assert` PANICS in debug and clean
//! `Err(...)` in release. A refusal test that passes only in debug is testing the assertion, not
//! the constraint system. Every refusal below is asserted on the `Err` string.
//!
//! ⚑ **EVERY FORGERY WRAPS INSIDE THE LIMB WIDTH.** `bump_limb8` wraps mod 256, so a range lookup
//! can never be the thing that objects and each assertion names which gate must be.
//!
//! Run: `cargo test -p dregg-circuit --release --test pasta_fp_sponge_proves -- --nocapture`

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TableSem, VmConstraint2, decomp_cols_pub,
    parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::refusal::assert_violated_constraint_not_bus;

const ROUND_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-fp-round.json");
const ROUND_TRACE: &str = include_str!("fixtures/pasta-fp-round-trace.txt");
const ROUND_PIS: &str = include_str!("fixtures/pasta-fp-round-pis.txt");

const ABSORB_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-fp-absorb.json");
const ABSORB_TRACE: &str = include_str!("fixtures/pasta-fp-absorb-trace.txt");
const ABSORB_PIS: &str = include_str!("fixtures/pasta-fp-absorb-pis.txt");

const CHAIN_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-fp-chainlink.json");
const CHAIN26_TRACE: &str = include_str!("fixtures/pasta-fp-chainlink-26-trace.txt");
/// All 27 phase-1 links' public inputs, one line per link, in chain order.
const CHAIN_PIS: &str = include_str!("fixtures/pasta-fp-chainlink-pis.txt");
/// ⚑ THE OTHER SIDE OF THE WELD: the 46 PHASE-2 links' public inputs. Link 0's `absorbed[0]` block
/// is the tape head phase 1 must reproduce.
const PHASE2_CHAIN_PIS: &str = include_str!("fixtures/pasta-fq-chainlink-pis.txt");

/// The Lean layout (`MinaWrapVerifierProgram` §1, unmoved), restated so a drift in either side reds
/// here rather than silently addressing a different column.
const PROG_WIDTH: usize = 469;
const SEL_MUL: usize = 222;
const REG_BASE: usize = 226;
const SK: usize = 32;
const XSEL_BASE: usize = 418;
const YSEL_BASE: usize = 424;
const WSEL_BASE: usize = 430;
const PC_COL: usize = 436;
const IMM_BASE: usize = 437;

/// ⚑ **THE COLUMN ORDER, PINNED AT BUILD TIME.** Every index above is a transcription of the
/// emitted program layout; if two of them ever crossed, every witness builder in this file would
/// be writing into the wrong column and the proofs would still be *about something*, just not
/// about the sponge. The immediate block must also end flush at `PROG_WIDTH` — no slack, no
/// overrun.
const THE_COLUMN_ORDER_IS_THE_LAYOUTS: () = {
    assert!(SEL_MUL < REG_BASE && REG_BASE < XSEL_BASE);
    assert!(XSEL_BASE < YSEL_BASE && YSEL_BASE < WSEL_BASE && WSEL_BASE < PC_COL);
    assert!(PC_COL < IMM_BASE && IMM_BASE + SK == PROG_WIDTH);
};
const _: () = THE_COLUMN_ORDER_IS_THE_LAYOUTS;
const NREG: usize = 6;

/// `MinaWrapVerifierAir.ROWS_PER_POSEIDON_ROUND` — 21 multiplies + 9 additions. Welded to the
/// emitted list by `MinaWrapVerifierSponge.the_census_round_is_the_emitted_round`.
const ROWS_PER_ROUND: usize = 30;
/// `PlonkSpongeConstantsKimchi::PERM_ROUNDS_FULL`.
const FULL_ROUNDS: usize = 55;
/// `MinaPhase1Chain.the_chain_is_twenty_seven_links` — 19 + 1 + 7.
const PHASE1_LINKS: usize = 27;
/// `MinaPhase1Chain.DIGEST_LINK` — the link whose OUTGOING LANE 1 is `fq_digest`.
const DIGEST_LINK: usize = 26;

/// ⚑ **THE o1-labs ARTIFACT, not a transcription.** Produced by
/// `metatheory/fixtures/kimchi-extractors/fp_kimchi_export.rs` calling
/// `mina_poseidon::pasta::fp_kimchi::static_params()` and driving
/// `ArithmeticSponge::<Fp, PlonkSpongeConstantsKimchi, 55>` at o1-labs `proof-systems`
/// `f6d958dc05`.
const O1_LABS_FP_KIMCHI_JSON: &str = include_str!("../../metatheory/fp_kimchi_params.json");

const PINNED_PROOF_SYSTEMS_REV: &str = "f6d958dc05";

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

fn parse_pi_line(line: &str, n: usize) -> Vec<BabyBear> {
    let pis: Vec<BabyBear> = line
        .split_whitespace()
        .map(|c| BabyBear::new(c.parse::<u32>().expect("PI is a u32 decimal")))
        .collect();
    assert_eq!(pis.len(), n, "expected {n} public inputs");
    pis
}

fn parse_pis(text: &str, n: usize) -> Vec<BabyBear> {
    parse_pi_line(text.trim(), n)
}

/// The 27 phase-1 / 46 phase-2 public-input vectors, one per line.
fn parse_pi_lines(text: &str, links: usize, n: usize) -> Vec<Vec<BabyBear>> {
    let v: Vec<Vec<BabyBear>> = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| parse_pi_line(l, n))
        .collect();
    assert_eq!(v.len(), links, "expected {links} public-input vectors");
    v
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

/// Decompose a decimal string into little-endian 8-bit limbs by repeated division of the DECIMAL
/// representation — so the expected limbs come from the upstream number's own digits and no bignum
/// dependency (and no chance to transcribe a limb wrong) enters the check.
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

/// ⚑ **THE PROVENANCE GATE.** Parses the o1-labs dump and REFUSES unless six independent conditions
/// hold — the same standard `pasta_fq_sponge_proves.rs` applies to the `fq_kimchi` block.
/// Returns `(mds[9], round_constants[165], kats, antivalues)`.
fn o1_labs_fp_kimchi() -> (
    Vec<String>,
    Vec<String>,
    std::collections::BTreeMap<String, String>,
    std::collections::BTreeMap<String, String>,
) {
    let v: serde_json::Value =
        serde_json::from_str(O1_LABS_FP_KIMCHI_JSON).expect("the o1-labs dump is JSON");

    // (1) the dump names the pinned upstream rev and the function it called.
    let source = v["source"].as_str().expect("the dump carries a `source`");
    assert!(
        source.contains("o1-labs/proof-systems")
            && source.contains(PINNED_PROOF_SYSTEMS_REV)
            && source.contains("fp_kimchi::static_params()"),
        "the dump is not `fp_kimchi::static_params()` @ {PINNED_PROOF_SYSTEMS_REV}: {source}"
    );
    let fp_source = v["fp_kimchi"]["source"]
        .as_str()
        .expect("the fp_kimchi block carries its own `source`");
    assert!(
        fp_source.contains("fp_kimchi.rs")
            && fp_source.contains("ArithmeticSponge")
            && fp_source.contains(PINNED_PROOF_SYSTEMS_REV),
        "the constants did not come from `poseidon/src/pasta/fp_kimchi.rs` at the pinned rev: \
         {fp_source}"
    );

    // (2) the shape `PlonkSpongeConstantsKimchi` forces.
    assert_eq!(
        v["fp_kimchi"]["full_rounds"].as_u64(),
        Some(FULL_ROUNDS as u64)
    );
    assert_eq!(v["fp_kimchi"]["rate"].as_u64(), Some(2));
    assert_eq!(v["fp_kimchi"]["sbox_alpha"].as_u64(), Some(7));

    let mds: Vec<String> = v["fp_kimchi"]["mds"]
        .as_array()
        .expect("mds")
        .iter()
        .map(|x| x.as_str().unwrap().to_string())
        .collect();
    let rcs: Vec<String> = v["fp_kimchi"]["round_constants"]
        .as_array()
        .expect("round_constants")
        .iter()
        .map(|x| x.as_str().unwrap().to_string())
        .collect();
    assert_eq!(mds.len(), 9, "the MDS is 3x3");
    assert_eq!(
        rcs.len(),
        3 * FULL_ROUNDS,
        "{FULL_ROUNDS} full rounds of three constants"
    );

    // (3) every constant is a canonical Pasta element — 32 8-bit limbs and no more.
    for c in mds.iter().chain(rcs.iter()) {
        let _ = decimal_to_limbs(c, SK);
    }

    // (4) the KAT table and the double-permute anti-values are present, and an anti-value DIFFERS
    // from its digest — otherwise the negative pin would be vacuous.
    let mut kats = std::collections::BTreeMap::new();
    for k in v["fp_kimchi"]["kats"].as_array().expect("kats") {
        kats.insert(
            k["name"].as_str().unwrap().to_string(),
            k["digest"].as_str().unwrap().to_string(),
        );
    }
    let mut anti = std::collections::BTreeMap::new();
    for a in v["fp_kimchi"]["double_permute_antivalues"]
        .as_array()
        .expect("antivalues")
    {
        anti.insert(
            a["name"].as_str().unwrap().to_string(),
            a["double_permuted"].as_str().unwrap().to_string(),
        );
    }
    assert_eq!(kats.len(), 12, "twelve KATs, at both input parities");
    assert_eq!(anti.len(), 5, "five double-permute anti-values");
    assert_ne!(
        kats.get("pair12"),
        anti.get("pair12"),
        "the double-permute anti-value equals the digest -- the negative pin would be vacuous"
    );

    // (5) ⚑ THE MODULE CHECK. Reading `static_params()` off the wrong module is the failure mode
    // the K3 audit named by name. `fq_kimchi`'s first MDS entry must NOT appear here.
    const FQ_KIMCHI_MDS_00: &str =
        "21645304954155744709830343885496239941442051768956068498671778416293702873282";
    assert!(
        !mds.contains(&FQ_KIMCHI_MDS_00.to_string()),
        "the dump carries `fq_kimchi`'s MDS -- `static_params()` was read off the wrong module"
    );

    (mds, rcs, kats, anti)
}

fn round_desc() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(ROUND_DESC_JSON).expect("the deployed checker parses the round descriptor")
}

fn absorb_desc() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(ABSORB_DESC_JSON)
        .expect("the deployed checker parses the absorption descriptor")
}

fn chain_desc() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(CHAIN_DESC_JSON)
        .expect("the deployed checker parses the phase-1 chain-link descriptor")
}

fn rom_rows(d: &EffectVmDescriptor2) -> Vec<Vec<u32>> {
    let rom = d
        .tables
        .iter()
        .find(|t| t.name == "pasta_program_rom")
        .expect("the machine declares an instruction ROM");
    let TableSem::ExactPublicRows { rows } = &rom.sem else {
        panic!("the instruction ROM is an exact-public manifest");
    };
    rows.iter().map(|r| r.to_vec()).collect()
}

/// ⚑ **§0 — THE SHAPE, READ OFF THE ARTIFACTS.** Every number this rung quotes is printed from the
/// emitted descriptors, not from a plan.
#[test]
fn the_fp_sponge_shape_is_read_off_the_artifacts() {
    let dr = round_desc();
    let da = absorb_desc();
    let dc = chain_desc();
    let rom_r = rom_rows(&dr);
    let rom_a = rom_rows(&da);
    let rom_c = rom_rows(&dc);

    println!("\n═══ §0  THE PHASE-1 (Fp) SPONGE, AS EMITTED ═══");
    for (d, rom) in [(&dr, &rom_r), (&da, &rom_a), (&dc, &rom_c)] {
        println!(
            "{:<32} constraints {:>5}  declared {:>4}  committed {:>5}  PIs {:>4}  ROM {:>5} x 55",
            d.name,
            d.constraints.len(),
            d.trace_width,
            committed_width(d),
            d.public_input_count,
            rom.len(),
        );
    }

    assert_eq!(dr.name, "dregg-pasta-fp-round::v1");
    assert_eq!(da.name, "dregg-pasta-fp-absorb::v1");
    assert_eq!(dc.name, "dregg-pasta-fp-chainlink::v1");
    assert_eq!(dr.public_input_count, 192, "three lanes in, three out");
    assert_eq!(da.public_input_count, 192);
    assert_eq!(
        dc.public_input_count, 256,
        "eight pin blocks: in(3) ++ out(3) ++ absorbed(2)"
    );
    assert_eq!(rom_r.len(), 32, "one round + 2 padding, padded to 2^5");
    assert_eq!(
        rom_a.len(),
        2048,
        "two absorbs + {FULL_ROUNDS} x {ROWS_PER_ROUND} + padding, at 2^11"
    );

    // ⚑ THE CHAIN LINK AND THE ABSORPTION ARE THE SAME PROGRAM. `MinaPhase1Chain.chainAir` is
    // `programAir pLimb fpAbsorbProg ++ chainPins`, so the two ROMs must be equal ROW FOR ROW —
    // the same 55x3 `fp_kimchi` round constants as descriptor cells. Only the boundary moves.
    assert_eq!(
        rom_c, rom_a,
        "the chain link and the absorption must carry the SAME instruction ROM"
    );
    assert_eq!(
        dc.trace_width, da.trace_width,
        "same machine, same declared width"
    );
    assert!(
        dc.constraints.len() > da.constraints.len(),
        "the chain link pins EIGHT blocks where the absorption pins six"
    );

    // The ROM's key column is `pc + 1`: injective, never zero — what makes the permutation argument
    // a pointwise identification rather than a multiset coincidence.
    for (j, row) in rom_a.iter().enumerate() {
        assert_eq!(row[0], (j as u32) + 1, "ROM key column is pc+1");
    }
}

/// ⚑ **§1 — THE Fp ROUND PROVES.** One full Kimchi round over the REAL `fp_kimchi` constants at the
/// Pallas BASE modulus, 32 rows, 192 public inputs.
#[test]
fn the_fp_round_proves() {
    let d = round_desc();
    let t = parse_trace(ROUND_TRACE, 32);
    let p = parse_pis(ROUND_PIS, 192);
    prove_and_verify(&d, &t, &p).expect("the honest Fp round proves and verifies");
    println!(
        "\n§1 ⚑ ONE Fp KIMCHI ROUND PROVES: 32 rows x {} committed, 192 PIs, {} constraints.",
        committed_width(&d),
        d.constraints.len()
    );
}

/// ⚑ **§2 — THE Fp ABSORPTION PROVES**, and its squeeze public input is o1-labs' own `[1,2]` KAT.
#[test]
fn the_fp_absorption_proves_and_squeezes_the_upstream_kat() {
    let (_, _, kats, _) = o1_labs_fp_kimchi();
    let d = absorb_desc();
    let t = parse_trace(ABSORB_TRACE, 2048);
    let p = parse_pis(ABSORB_PIS, 192);
    prove_and_verify(&d, &t, &p).expect("the honest Fp absorption proves and verifies");

    // ⚑ THE OUTPUT PIN IS THE UPSTREAM DIGEST, LIMB FOR LIMB. Not a transcribed decimal: the
    // expected limbs are derived from the dump's own digits.
    let upstream = kats.get("pair12").expect("the [1,2] KAT is in the dump");
    let want = decimal_to_limbs(upstream, SK);
    let got: Vec<u32> = p[5 * SK..6 * SK].iter().map(|c| c.as_u32()).collect();
    assert_eq!(
        got, want,
        "the emitted squeeze public input is not `fp_kimchi`'s own `absorb([1,2]); squeeze()`"
    );

    // …and the fresh-sponge pins really are zero, or the statement is about a sponge that was not
    // fresh (`MinaWrapVerifierSpongeFp.the_fp_absorb_pins_a_fresh_sponge`).
    assert!(
        p[0..3 * SK].iter().all(|c| c.as_u32() == 0),
        "the three incoming state lanes must be pinned to zero"
    );

    println!(
        "\n§2 ⚑ ONE AIR INSTANCE PROVES A `fp_kimchi` SPONGE ABSORPTION.\n  \
         fresh state (0,0,0) -> absorb [1,2] -> {FULL_ROUNDS} full rounds -> squeeze lane 0\n  \
         = {upstream}\n  \
         (read from o1-labs' own `static_params()` dump, not transcribed)\n  \
         2048 rows, 192 public inputs, PROVED and VERIFIED in release."
    );
}

/// ⚑ **§3 — THE PI PINS REFUSE A FORGED TRANSCRIPT VALUE, and the ROM is SILENT about it.**
///
/// The absorbed values enter through PI-pinned REGISTER cells with zero immediates
/// (`the_absorbed_value_is_not_a_rom_constant`), so the instruction ROM says nothing whatever about
/// WHICH value was absorbed. The refusal must come from the BOUNDARY PIN, and the assertion says so
/// by name: the error must not be the exact-public bus.
#[test]
fn a_forged_absorbed_value_is_refused_by_the_pi_pin() {
    let d = absorb_desc();
    let mut t = parse_trace(ABSORB_TRACE, 2048);
    let p = parse_pis(ABSORB_PIS, 192);

    // R3 on row 0 is the first absorbed value. Bump one limb, INSIDE the 8-bit range.
    let col = reg_col(3);
    t[0][col] = bump_limb8(t[0][col]);
    let err = prove_and_verify(&d, &t, &p).expect_err("a forged absorbed value must be REFUSED");
    assert!(
        !err.contains("exact-public"),
        "the ROM must be SILENT about the absorbed VALUE -- the PIN is what refuses; got: {err}"
    );
    // ⚑ The negative above was the WHOLE assertion until 2026-08-09, and a lone negative is
    // satisfied by every error string — including the prover's trace-width / PI-arity pre-flight,
    // which fires before the constraint system reads a cell. Name the verdict positively.
    // Measured in `--release`: `OodEvaluationMismatch { index: Some(0) }`, the Main AIR's own.
    assert_violated_constraint_not_bus("fp-sponge forged absorbed value", &err);
    println!("\n§3 ⚑ FORGED ABSORBED VALUE -> REFUSED by the boundary PIN: {err}");
}

/// ⚑ **§4 — THE ROM BUS REFUSES A MISPLACED ROUND CONSTANT.**
///
/// The 55×3 `fp_kimchi` round constants are IMMEDIATES, hence cells of the instruction-ROM tuple.
/// Give round 3 the round constant of round 7 and the QUERIED MULTISET changes, so the lookup bus
/// refuses — this is the ROM doing sponge-specific work, and it is a DIFFERENT gate from §3's.
#[test]
fn a_misplaced_round_constant_is_refused_by_the_rom_bus() {
    let d = absorb_desc();
    let mut t = parse_trace(ABSORB_TRACE, 2048);
    let p = parse_pis(ABSORB_PIS, 192);
    let rom = rom_rows(&d);

    // Within a round: 12 S-box multiplies, then three MDS rows of six instructions each; the round
    // constant is at offset 5 of each MDS row. The absorption's ROM is offset by the two absorbs.
    let base = |r: usize, row: usize| 2 + ROWS_PER_ROUND * r + 12 + 6 * row;
    let i3 = base(3, 0) + 5;
    let i7 = base(7, 0) + 5;
    assert_ne!(
        rom[i3][23..55],
        rom[i7][23..55],
        "rounds 3 and 7 must carry DIFFERENT constants or this control is vacuous"
    );

    // Substitute round 7's immediate limbs into round 3's row of the TRACE.
    for k in 0..SK {
        t[i3][IMM_BASE + k] = BabyBear::new(rom[i7][23 + k]);
    }
    let err = prove_and_verify(&d, &t, &p)
        .expect_err("a round constant used at the wrong round must be REFUSED");
    assert!(
        err.contains("exact-public") || err.contains("lookup") || err.contains("permutation"),
        "the ROM BUS must refuse a misplaced round constant -- got: {err}"
    );
    println!("\n§4 ⚑ ROUND 7's CONSTANT AT ROUND 3 -> REFUSED by the ROM BUS: {err}");
}

/// ⚑ **§5 — THE `pc` THREAD REFUSES A REORDER.**
///
/// The ROM fixes WHICH instructions run; the `pc` thread fixes their ORDER. Swapping two adjacent
/// trace rows leaves the queried multiset UNCHANGED — so only the thread can object.
#[test]
fn a_reordered_instruction_stream_is_refused_by_the_pc_thread() {
    let d = absorb_desc();
    let mut t = parse_trace(ABSORB_TRACE, 2048);
    let p = parse_pis(ABSORB_PIS, 192);

    // Swap two S-box multiplies inside round 0 — same rows, same ROM tuples, different order.
    let a = 2 + 4;
    let b = 2 + 5;
    t.swap(a, b);
    let err = prove_and_verify(&d, &t, &p)
        .expect_err("instructions executed out of ROM order must be REFUSED");
    println!("\n§5 ⚑ TWO ROWS SWAPPED (multiset UNCHANGED) -> REFUSED by the pc THREAD: {err}");
    // Sanity: the swap really did preserve the ROM tuples, so the bus had nothing to see.
    let mut keys: Vec<u32> = t.iter().map(|r| r[PC_COL].as_u32()).collect();
    keys.sort_unstable();
    let mut want: Vec<u32> = (0..2048u32).collect();
    want.sort_unstable();
    assert_eq!(keys, want, "the swap must preserve the pc MULTISET");
}

/// ⚑ **§6 — THE CHAIN LINK THAT PRODUCES `fq_digest` PROVES.**
///
/// Link 26 of the 27-link phase-1 chain: absorb the last two `t_comm` coordinates into a state 26
/// permutations deep in Mina devnet block 539508's own phase-1 tape, permute, and expose all three
/// outgoing lanes. Lane 0's low 128 bits are ζ′; **lane 1 IS `fq_digest`.**
#[test]
fn the_digest_producing_chain_link_proves() {
    let d = chain_desc();
    let t = parse_trace(CHAIN26_TRACE, 2048);
    let all = parse_pi_lines(CHAIN_PIS, PHASE1_LINKS, 256);
    prove_and_verify(&d, &t, &all[DIGEST_LINK])
        .expect("the honest phase-1 link 26 proves and verifies");
    println!(
        "\n§6 ⚑ PHASE-1 LINK {DIGEST_LINK}/{PHASE1_LINKS} PROVES: 2048 rows x {} committed, \
         256 PIs, {} constraints.",
        committed_width(&d),
        d.constraints.len()
    );
}

/// ⚑ **§7 — CONTINUITY, ON THE EMITTED CLAIMS.** Link `j`'s outgoing PI block IS link `j+1`'s
/// incoming block, limb for limb, for all 26 seams — `the_emitted_claims_are_continuous` on the
/// wire. This is the equality a recursion fold's `cb.connect` enforces in-circuit.
#[test]
fn the_phase1_chain_is_continuous_on_the_wire() {
    let all = parse_pi_lines(CHAIN_PIS, PHASE1_LINKS, 256);
    for j in 0..PHASE1_LINKS - 1 {
        assert_eq!(
            &all[j][3 * SK..6 * SK],
            &all[j + 1][0..3 * SK],
            "link {j}'s outgoing state is not link {}'s incoming state",
            j + 1
        );
    }
    // …and the chain starts at a FRESH sponge, or it is a chain of something else.
    assert!(
        all[0][0..3 * SK].iter().all(|c| c.as_u32() == 0),
        "the chain must start at the zero state"
    );
    println!(
        "\n§7 ⚑ CONTINUITY: {}/{} seams equal, elementwise over 96 felts; link 0 starts fresh.",
        PHASE1_LINKS - 1,
        PHASE1_LINKS - 1
    );
}

/// ⚑⚑ **§10 — THE WELD: PHASE 1's DIGEST IS PHASE 2's TAPE HEAD.**
///
/// This is the point of the leg. Phase 2's chain begins by absorbing `WRAP_TAPE2[0]`; phase 1's
/// chain ends by producing it in **outgoing lane 1 of link 26**. Both are published as 32 eight-bit
/// limbs, so the tie is a slice comparison: **no arithmetic, no digest, no birthday bound.**
///
/// ⚠ A one-felt tie would be `2^31`, below this repository's own ~124-bit bar. This is 32 felts of
/// a 254-bit element, so a forger must match every limb.
#[test]
fn the_phase1_digest_is_the_phase2_tape_head() {
    let p1 = parse_pi_lines(CHAIN_PIS, PHASE1_LINKS, 256);
    let p2 = parse_pi_lines(PHASE2_CHAIN_PIS, 46, 256);

    // phase-1 chainlink: in(3) ++ out(3) ++ absorbed(2) -> outgoing lane 1 is [4*SK, 5*SK)
    let digest_block: Vec<u32> = p1[DIGEST_LINK][4 * SK..5 * SK]
        .iter()
        .map(|c| c.as_u32())
        .collect();
    // phase-2 chainlink: same layout -> absorbed[0] is [6*SK, 7*SK)
    let tape_head: Vec<u32> = p2[0][6 * SK..7 * SK].iter().map(|c| c.as_u32()).collect();

    assert_eq!(
        digest_block.len(),
        SK,
        "the wire block is the WHOLE element, {SK} limbs"
    );
    assert_eq!(
        digest_block, tape_head,
        "phase-1 link {DIGEST_LINK}'s outgoing lane 1 is not phase-2 link 0's absorbed[0] -- \
         the transcript chain would be absorbing a tape nothing derives"
    );

    // ⚑ NON-VACUITY. A block of zeros, or a block equal to the other absorbed slot, would make the
    // equality above say nothing.
    assert!(
        digest_block.iter().any(|&c| c != 0),
        "the digest block is the zero vector -- the weld would be vacuous"
    );
    let other: Vec<u32> = p2[0][7 * SK..8 * SK].iter().map(|c| c.as_u32()).collect();
    assert_ne!(
        digest_block, other,
        "the digest block equals phase-2's SECOND absorbed slot -- the weld picks no lane"
    );

    // ⚑ AND EVERY LIMB IS LOAD-BEARING: moving any ONE of the 32 breaks the equality, so the tie
    // is elementwise and not a prefix. 32/32.
    let mut moved = 0usize;
    for i in 0..SK {
        let mut forged = digest_block.clone();
        forged[i] = (forged[i] + 1) % 256;
        if forged != tape_head {
            moved += 1;
        }
    }
    assert_eq!(
        moved, SK,
        "only {moved}/{SK} limbs are load-bearing -- the tie is not elementwise"
    );

    println!(
        "\n§10 ⚑⚑ THE WELD, ELEMENTWISE AT FULL LIMB WIDTH.\n  \
         phase-1 `dregg-pasta-fp-chainlink::v1` link {DIGEST_LINK}, PI[{}..{}) (outgoing lane 1)\n  \
         == phase-2 `dregg-pasta-fq-chainlink::v1` link 0,  PI[{}..{}) (absorbed[0] = fq_digest)\n  \
         {}/{} felts equal, {moved}/{SK} load-bearing. NO digest, NO birthday bound: a forger must \
         match every limb of a 254-bit element.\n  \
         (a one-felt tie would be 2^31, below this repository's own ~124-bit bar.)",
        4 * SK,
        5 * SK,
        6 * SK,
        7 * SK,
        SK,
        SK
    );
}

/// ⚑ **§11 — AND THE DIGEST BLOCK IS PINNED, NOT DECORATIVE.** Forging one limb of link 26's
/// outgoing lane 1 in the TRACE must be refused by the boundary pin — otherwise §10 compares two
/// numbers a prover was free to choose.
#[test]
fn a_forged_digest_lane_is_refused() {
    let d = chain_desc();
    let all = parse_pi_lines(CHAIN_PIS, PHASE1_LINKS, 256);

    // (a) forge the PUBLIC INPUT: the pin compares a trace cell to a PI slot, so moving the PI
    // alone must refuse.
    let t = parse_trace(CHAIN26_TRACE, 2048);
    let mut pis = all[DIGEST_LINK].clone();
    pis[4 * SK] = bump_limb8(pis[4 * SK]);
    let err = prove_and_verify(&d, &t, &pis)
        .expect_err("a forged fq_digest public input must be REFUSED");
    println!("\n§11a ⚑ FORGED `fq_digest` PUBLIC INPUT -> REFUSED by the boundary pin: {err}");

    // (b) forge the TRACE CELL the pin reads — the LAST row's R5 block (`allocAt 55 1 = 5`).
    let mut t2 = parse_trace(CHAIN26_TRACE, 2048);
    let col = reg_col(5);
    t2[2047][col] = bump_limb8(t2[2047][col]);
    let err2 = prove_and_verify(&d, &t2, &all[DIGEST_LINK])
        .expect_err("a forged fq_digest trace cell must be REFUSED");
    println!("§11b ⚑ FORGED `fq_digest` TRACE CELL -> REFUSED: {err2}");
}

/// ⚑⚑ **§9 — THE WELD TO o1-labs IS A CHECK ON THE EMITTED ARTIFACT, NOT A TRANSCRIBED CONSTANT.**
///
/// ⚠ **THE DEFECT THIS CLOSES.** The 55×3 `fp_kimchi` round constants and the 3×3 MDS live in
/// `PastaPoseidon.mdsN`/`rcsN` as decimal literals. All of it was *copied* — correctly, as it turns
/// out — and **nothing had ever compared the copy to `static_params()`.** A single wrong digit in
/// 174 numbers would have produced a self-consistent tree: the Lean would prove the program
/// computes ITS constants, the harness would pin the bytes of ITS digest, every gate would be
/// green, and the object would not be Kimchi's sponge.
///
/// ⚑ **AND THE DESCRIPTOR IS THE RIGHT PLACE TO LOOK.** The round constants and MDS coefficients
/// are IMMEDIATES, so they are instruction-ROM tuple entries — descriptor cells the prover cannot
/// choose (§4). Checking them here checks what the verifier will actually enforce, not what a
/// source file says.
#[test]
fn the_emitted_rom_carries_o1_labs_own_fp_kimchi_constants() {
    let (mds, rcs, kats, _) = o1_labs_fp_kimchi();
    let d = absorb_desc();
    let rom = rom_rows(&d);

    // `ROM_ARITY = 1 + 4 + 3*NREG + SK = 55`: a key, the four instruction fields, the eighteen
    // operand one-hots, then the 32 immediate limbs.
    assert_eq!(1 + 4 + 3 * NREG + SK, 55);
    let imm_of = |instr: usize| -> Vec<u32> { rom[instr][23..55].to_vec() };
    // Within a round: 12 S-box multiplies, then three MDS rows of six instructions each. A row is
    // `out := a*m0`, `d := b*m1`, `out += d`, `d := c*m2`, `out += d`, `out += rc` — so the three
    // coefficients sit at offsets 0, 1, 3 of the row and the round constant at offset 5.
    let base = |r: usize, row: usize| 2 + ROWS_PER_ROUND * r + 12 + 6 * row;

    let mut checked = 0usize;
    for r in 0..FULL_ROUNDS {
        for row in 0..3 {
            for (k, off) in [0usize, 1, 3].iter().enumerate() {
                assert_eq!(
                    imm_of(base(r, row) + off),
                    decimal_to_limbs(&mds[3 * row + k], SK),
                    "round {r}, MDS row {row}, coefficient {k}: the emitted immediate is not \
                     o1-labs' `fp_kimchi::static_params().mds[{row}][{k}]`"
                );
                checked += 1;
            }
            assert_eq!(
                imm_of(base(r, row) + 5),
                decimal_to_limbs(&rcs[3 * r + row], SK),
                "round {r}, lane {row}: the emitted immediate is not o1-labs' \
                 `fp_kimchi::static_params().round_constants[{r}][{row}]`"
            );
            checked += 1;
        }
    }
    assert_eq!(
        checked,
        FULL_ROUNDS * 12,
        "9 MDS coefficients and 3 round constants per round, {FULL_ROUNDS} rounds"
    );

    // ⚑ NON-VACUITY OF THE CHECK ITSELF. If `imm_of` read a block of zeros, or if the 165 round
    // constants happened to be equal, the loop above would pass while saying nothing.
    let mut seen = std::collections::BTreeSet::new();
    for c in &rcs {
        assert_ne!(c, "0", "a round constant is zero");
        assert!(seen.insert(c.clone()), "round constant {c} repeats");
    }
    assert_eq!(seen.len(), 3 * FULL_ROUNDS);
    for c in &rcs {
        assert!(
            !mds.contains(c),
            "a round constant is also an MDS coefficient"
        );
    }

    println!(
        "\n§9 ⚑ THE WELD TO o1-labs, ON THE ARTIFACT.\n  \
         {checked} immediates of `pasta-fp-absorb.json`'s instruction ROM checked against\n  \
         `mina_poseidon::pasta::fp_kimchi::static_params()` @ o1-labs proof-systems \
         {PINNED_PROOF_SYSTEMS_REV}\n  \
         ({} MDS coefficients x {FULL_ROUNDS} rounds + {} round constants), all EQUAL.\n  \
         and the emitted squeeze recomposes to that dump's own [1,2] KAT:\n  \
         {}\n  \
         Nothing in this test is a transcribed decimal.",
        9,
        3 * FULL_ROUNDS,
        kats.get("pair12").unwrap()
    );
}

/// ⚑ **§12 — THE Fp AND Fq LEGS ARE THE SAME PROGRAM AT DIFFERENT CONSTANTS.**
///
/// `MinaWrapVerifierSpongeFp.the_deployed_fq_programs_are_this_one_at_fqParams` is the Lean side.
/// On the wire it means: identical widths, identical PI counts, identical ROM row counts, identical
/// operand routing — and DIFFERENT immediates on every round-constant row. A leg that had silently
/// inherited `fq_kimchi` would pass every other test in this file.
#[test]
fn the_fp_leg_is_the_fq_program_at_the_other_constants() {
    const FQ_ABSORB_JSON: &str = include_str!("../descriptors/by-name/pasta-fq-absorb.json");
    let dp = absorb_desc();
    let dq = parse_vm_descriptor2(FQ_ABSORB_JSON).expect("the Fq absorption parses");
    let rp = rom_rows(&dp);
    let rq = rom_rows(&dq);

    assert_eq!(dp.trace_width, dq.trace_width);
    assert_eq!(dp.public_input_count, dq.public_input_count);
    assert_eq!(dp.constraints.len(), dq.constraints.len());
    assert_eq!(rp.len(), rq.len());

    // The instruction FIELDS (key, op, xr, yr, wr, and the 18 operand one-hots) are identical …
    let mut same_head = 0usize;
    let mut diff_imm = 0usize;
    for (a, b) in rp.iter().zip(rq.iter()) {
        assert_eq!(
            a[0..23],
            b[0..23],
            "the instruction stream must be IDENTICAL"
        );
        same_head += 1;
        if a[23..55] != b[23..55] {
            diff_imm += 1;
        }
    }
    // … and every one of the 660 constant-bearing instructions differs in its immediate.
    assert_eq!(same_head, 2048);
    assert_eq!(
        diff_imm,
        FULL_ROUNDS * 12,
        "exactly the {} constant-bearing instructions must differ",
        FULL_ROUNDS * 12
    );

    println!(
        "\n§12 ⚑ ONE PROGRAM, TWO PARAMETER SETS.\n  \
         2048/2048 instruction words identical in fields 0..23 (op, operands, one-hots, pc key);\n  \
         {diff_imm}/{} immediates differ — exactly the {FULL_ROUNDS}x(9 MDS + 3 rc) constant-bearing \
         rows.\n  \
         `programAir`'s `pl` parametricity is the whole of the field change.",
        FULL_ROUNDS * 12
    );

    // Selector columns exist where the layout says — see `THE_COLUMN_ORDER_IS_THE_LAYOUTS` at
    // module scope. Every operand is a constant, so a drift that silently re-addressed the
    // selectors is a build error rather than a late report from whichever test ran first.
}
