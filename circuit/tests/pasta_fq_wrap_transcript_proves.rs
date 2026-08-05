//! # ⚑⚑ THE IN-AIR Fq SPONGE, FED A REAL MINA BLOCK'S TRANSCRIPT.
//!
//! `pasta_fq_sponge_proves.rs` proved a Kimchi sponge absorption: `(0,0,0) → absorb [1,2] → 55
//! rounds → squeeze`. Its own docblock named what it did NOT show — *"it does not show the absorbed
//! values came from a Kimchi transcript"* — and `MinaWrapVerifierSponge` §9 named the same thing:
//! *"neither fixes that the values came from a Kimchi transcript. That is the generator gap."*
//!
//! **The values here were not chosen.** They are a link of the phase-2 (`fq_kimchi`) absorption tape
//! of the Wrap proof of
//!
//!   * network **mina devnet**, state hash `3NLmVB6Fs3dm4kXNkgwheHXzJXNpCCwEDe76RpTVeBTNujm12zNk`,
//!     blockchain length **539508**;
//!   * ground truth asserted in Rust by `metatheory/fixtures/pickles-extractors` before a number was
//!     emitted: openmina's own devnet `BlockVerifier`, `accumulator_check = true`, and
//!     **`kimchi::verifier::verify::<Pallas, …> = Ok(())`** — o1-labs' own verifier.
//!
//! ⚑ **WHY OUR Fq SPONGE IS A BLOCK'S SPONGE.** A Mina block's proof is the **Wrap** proof, which is
//! Pallas-committed, so its phase-1 sponge is `fp_kimchi` and its **phase-2 sponge is `fq_kimchi`
//! over `ZMod qN` — this machine's constants.** Its two outputs are `v′` (polyscale) and `u′`
//! (evalscale), and `u′` costs no permutation because it is lane 1 of `v′`'s state.
//!
//! ⚑ **WHAT IS IN THE AIR — stated before the result, not after it.** The tape is 91 elements, which
//! at rate 2 is **46 permutations** = 75 900 rows ≈ 207 MB of witness, against a repository whose
//! largest tracked file is 10 MB. **ONE** of the 46 is emitted: the closing squeeze, together with
//! the absorb that feeds it. The other 45 are carried by the Lean reference the AIR program is
//! PROVED to compute at every state (`the_permutation_program_computes_the_kimchi_permutation`), so
//! what is missing is 45 more WITNESSES, not an algebra. `the_link_input_is_the_real_tape_prefix` is
//! the join, and §2 below is what makes it checkable: a wrong incoming state cannot produce the
//! right `v′`.
//!
//! ⚑ **WHICH GATE REFUSES WHAT.** `MinaWrapVerifierSponge` §9's pole inversion decides this and it
//! is the whole point: the 55x3 round constants are IMMEDIATES, so the ROM bus refuses a wrong one;
//! the absorbed value is a register operand with a zero immediate, so **the ROM is silent about the
//! transcript and the BOUNDARY PIN is what refuses it.** §3–§6 fire each one and assert which.
//!
//! ⚑ **RELEASE, DELIBERATELY** — algebraic refusals are `debug_assert` panics in debug and clean
//! `Err(...)` in release, so a refusal test that passes only in debug tests the assertion.
//!
//! Run: `cargo test -p dregg-circuit --release --test pasta_fq_wrap_transcript_proves -- --nocapture`

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TableSem, VmConstraint2, decomp_cols_pub,
    parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};

const LINK_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-fq-wraplink.json");
const LINK_TRACE: &str = include_str!("fixtures/pasta-fq-wraplink-trace.txt");
const LINK_PIS: &str = include_str!("fixtures/pasta-fq-wraplink-pis.txt");

/// The `[1,2]` absorption, whose ROM this instance must reuse cell for cell — same program, same
/// `fq_kimchi` constants.
const ABSORB_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-fq-absorb.json");

/// ⚑ **THE BLOCK, from the extractor that ran Mina's own verifier over it.** Nothing in this file
/// types a challenge; every expected number is read out of here.
const MINA_BLOCK_JSON: &str = include_str!("../../metatheory/mina_real_block_proof.json");

const PROG_WIDTH: usize = 469;
const SK: usize = 32;
const REG_BASE: usize = 226;
const IMM_BASE: usize = 437;
const NREG: usize = 6;
const YSEL_BASE: usize = 424;
const ROWS_PER_ROUND: usize = 30;
const FULL_ROUNDS: usize = 55;
/// The two high-entropy limbs `challenge()` keeps: `CHALLENGE_LENGTH_IN_LIMBS = 2` at 64 bits each,
/// so a challenge is the low 128 bits of the raw squeeze — 16 of our 8-bit limbs.
const CHALLENGE_LIMBS: usize = 16;
/// 7 pin blocks: three incoming state lanes, the absorbed element, the zero second slot, and BOTH
/// squeezed lanes.
const LINK_PI_COUNT: usize = 7 * SK;

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
    assert_eq!(pis.len(), LINK_PI_COUNT, "seven pinned register blocks");
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

/// A forgery that stays INSIDE the declared 8-bit range, so a RANGE LOOKUP can never be the thing
/// that refuses and the assertion about WHICH gate fires means something.
fn bump_limb8(cell: BabyBear) -> BabyBear {
    BabyBear::new((cell.as_u32() + 1) % 256)
}

/// Little-endian 8-bit limbs of a DECIMAL string, by repeated division of the decimal digits — so
/// no bignum dependency and no chance to transcribe a limb wrong. Returns the limbs and whatever
/// remains ABOVE them, so a caller taking a prefix says so and a caller taking the whole value can
/// refuse a value that did not fit.
fn decimal_to_limbs_and_rest(s: &str, n: usize) -> (Vec<u32>, Vec<u32>) {
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
    (out, digits)
}

/// The WHOLE value, refusing anything that does not fit in `n` limbs.
fn decimal_to_limbs(s: &str, n: usize) -> Vec<u32> {
    let (out, rest) = decimal_to_limbs_and_rest(s, n);
    assert_eq!(rest, vec![0], "the value {s} does not fit in {n} limbs");
    out
}

/// The low `n` limbs, deliberately — used for the two-limb `challenge()` truncation, where the
/// value above the prefix is the part Kimchi throws away.
fn decimal_low_limbs(s: &str, n: usize) -> Vec<u32> {
    decimal_to_limbs_and_rest(s, n).0
}

fn link_desc() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(LINK_DESC_JSON)
        .expect("the deployed checker parses the wrap-link descriptor")
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

/// ⚑ **THE GROUND TRUTH, refused unless the extractor asserted it.** Returns
/// `(v_chal, u_chal, tape[90], tape_len)` — every one read from the block dump.
fn the_block() -> (String, String, String, usize) {
    let v: serde_json::Value =
        serde_json::from_str(MINA_BLOCK_JSON).expect("the block dump is JSON");

    assert_eq!(
        v["_network"].as_str(),
        Some("mina devnet"),
        "this is not the devnet dump"
    );
    assert_eq!(
        v["_state_hash"].as_str(),
        Some("3NLmVB6Fs3dm4kXNkgwheHXzJXNpCCwEDe76RpTVeBTNujm12zNk"),
        "a different block would make every number below a different (still true) sentence"
    );
    let gt = v["_ground_truth"].as_str().expect("_ground_truth");
    assert!(
        gt.contains("BlockVerifier")
            && gt.contains("accumulator_check=true")
            && gt.contains("kimchi::verifier::verify=Ok"),
        "the dump does not assert Mina's own verifier accepted this proof: {gt}"
    );

    let wt = &v["wrap_transcript"];
    // ⚑ THE ONE THAT MAKES THIS OUR SPONGE. A Wrap proof's phase-2 sponge is `fq_kimchi` over the
    // Pallas SCALAR field. If the extractor ever relabels this, the emitted instance is about the
    // other Pasta field and every equality below would be an accident.
    assert_eq!(
        wt["_phase2_params"].as_str(),
        Some("fq_kimchi over Fq (Pallas scalar field)"),
        "the block's phase-2 sponge is not the `fq_kimchi` one this machine implements"
    );
    let tape_len = wt["phase2_tape_len"].as_u64().expect("phase2_tape_len") as usize;
    assert_eq!(
        tape_len, 91,
        "the tape length the link's arithmetic assumes"
    );

    // tape = [fq_digest, prev_challenge_digest, ft_eval1] ++ public_evals[0] ++ public_evals[1]
    //        ++ evals_tape   (pickles-extractors/src/main.rs:1083-1087)
    let evals = wt["phase2_evals_tape"]
        .as_array()
        .expect("phase2_evals_tape");
    assert_eq!(evals.len(), 86, "5 header elements + 86 evaluations = 91");
    let last = evals[85].as_str().unwrap().to_string();

    (
        wt["v_chal"].as_str().expect("v_chal").to_string(),
        wt["u_chal"].as_str().expect("u_chal").to_string(),
        last,
        tape_len,
    )
}

/// ⚑ **§0 — THE SHAPE, READ OFF THE ARTIFACT.**
#[test]
fn the_wrap_link_has_the_shape_lean_emitted() {
    let d = link_desc();
    let rom = rom_rows(&d);

    assert_eq!(d.trace_width, PROG_WIDTH);
    assert_eq!(
        d.public_input_count, LINK_PI_COUNT,
        "seven pinned blocks: 3 state lanes in, the absorbed element, the zero slot, v' and u'"
    );
    assert_eq!(
        rom.len(),
        2048,
        "the same 2^11 program the [1,2] absorption runs"
    );
    for (j, row) in rom.iter().enumerate() {
        assert_eq!(row.len(), 55, "manifest row {j} has the declared arity");
        assert_eq!(row[0], j as u32 + 1, "manifest key at index {j} is pc+1");
    }

    // ⚑ THE ROM IS THE ABSORPTION'S, ROW FOR ROW. Same program, therefore the same 55x3 `fq_kimchi`
    // round constants as descriptor cells — so `pasta_fq_sponge_proves.rs` §9's check of those
    // constants against o1-labs' own `static_params()` dump is a check of THIS instance too. Two
    // descriptors that merely shared a Lean source file would not give that.
    let da = parse_vm_descriptor2(ABSORB_DESC_JSON).expect("the absorption descriptor parses");
    assert_eq!(
        rom,
        rom_rows(&da),
        "the wrap link must run the SAME instruction ROM as the [1,2] absorption"
    );
    assert_eq!(
        committed_width(&d),
        committed_width(&da),
        "and the same committed width -- the transcript costs no new columns"
    );

    println!("\n═══ THE Fq TRANSCRIPT SPONGE, ON A REAL MINA BLOCK ═══");
    println!(
        "{:<30} constraints {:>5}  declared {:>4}  committed {:>5}  PIs {:>4}  ROM {:>5} x 55",
        d.name,
        d.constraints.len(),
        d.trace_width,
        committed_width(&d),
        d.public_input_count,
        rom.len(),
    );
    println!(
        "instruction ROM IDENTICAL to pasta-fq-absorb::v1 -- the same {} `fq_kimchi` round \
         constants, as descriptor cells.",
        3 * FULL_ROUNDS
    );
}

/// ⚑⚑ **§1 — THE HONEST LINK PROVES, AND ITS SQUEEZE IS THE BLOCK'S OWN `v′` AND `u′`.**
///
/// This is the test the campaign was for. The 2 048-row Lean-emitted witness proves and verifies
/// against 224 public inputs, and those public inputs are: an incoming sponge state 45 permutations
/// deep in a real Mina block's phase-2 tape, that tape's 91st element, and the two raw squeezes
/// whose low 128 bits are the `v_chal` / `u_chal` `proof.oracles(...)` returned on that block.
#[test]
fn the_wrap_link_squeezes_the_blocks_own_challenges() {
    let (v_chal, u_chal, tape90, tape_len) = the_block();
    let d = link_desc();
    let trace = parse_trace(LINK_TRACE, 2048);
    let pis = parse_pis(LINK_PIS);

    // ── THE ABSORBED ELEMENT IS THE TAPE'S 91st. Pin block 3 is first-row R3.
    assert_eq!(
        (0..SK)
            .map(|i| pis[3 * SK + i].as_u32())
            .collect::<Vec<_>>(),
        decimal_to_limbs(&tape90, SK),
        "the absorbed element is not the block's {tape_len}th phase-2 tape element"
    );
    // ── AND EXACTLY ONE ELEMENT IS ABSORBED: the second slot is pinned to zero, so the descriptor
    // cannot be a sentence about a link that absorbed something else alongside it.
    assert!(
        (0..SK).all(|i| pis[4 * SK + i].as_u32() == 0),
        "the second absorb slot must be pinned to zero"
    );
    // ── AND THE INCOMING STATE IS NOT A FRESH SPONGE. The [1,2] instance pinned (0,0,0); this one
    // is mid-transcript, which is the whole difference.
    assert!(
        (0..3 * SK).any(|i| pis[i].as_u32() != 0),
        "a fresh (0,0,0) state here would mean the link is not mid-transcript"
    );

    // ── ⚑ THE TWO CHALLENGES. `challenge()` keeps two 64-bit limbs, so the challenge is the low
    // 128 bits of the raw squeeze — the first 16 of our 8-bit limbs.
    assert_eq!(
        (0..CHALLENGE_LIMBS)
            .map(|i| pis[5 * SK + i].as_u32())
            .collect::<Vec<_>>(),
        decimal_low_limbs(&v_chal, CHALLENGE_LIMBS),
        "the emitted lane-0 squeeze does not truncate to the block's v' (polyscale)"
    );
    assert_eq!(
        (0..CHALLENGE_LIMBS)
            .map(|i| pis[6 * SK + i].as_u32())
            .collect::<Vec<_>>(),
        decimal_low_limbs(&u_chal, CHALLENGE_LIMBS),
        "the emitted lane-1 squeeze does not truncate to the block's u' (evalscale)"
    );
    // Non-vacuity of the truncation: the raw squeezes have HIGH limbs, so the 16 above are a
    // genuine prefix of a 254-bit value and not a 128-bit number padded out.
    assert!(
        (CHALLENGE_LIMBS..SK).any(|i| pis[5 * SK + i].as_u32() != 0),
        "the raw v' squeeze is only 128 bits wide -- the truncation is checking nothing"
    );

    prove_and_verify(&d, &trace, &pis)
        .expect("the honest wrap link must prove and verify against its 224 public inputs");

    println!(
        "\n§1 ⚑⚑ ONE AIR INSTANCE RECOMPUTES A LINK OF A REAL MINA BLOCK'S KIMCHI TRANSCRIPT.\n  \
         devnet block 539508, Wrap proof, phase-2 (`fq_kimchi`) sponge, {tape_len}-element tape\n  \
         state after 45 permutations -> absorb tape[90] -> {FULL_ROUNDS} full rounds -> lanes 0,1\n  \
         v' = {v_chal}\n  \
         u' = {u_chal}\n  \
         both read from `mina_real_block_proof.json`, which openmina's BlockVerifier and\n  \
         o1-labs' `kimchi::verifier::verify` accepted before it was written.\n  \
         2048 rows, 224 public inputs, PROVED and VERIFIED in release."
    );
}

/// ⚑ **§2 — THE INCOMING STATE IS BOUND.** The AIR carries one of the tape's 46 permutations; the
/// other 45 reach it through the pinned incoming state. If that state could be anything, the
/// instance would be a permutation of three arbitrary 254-bit numbers wearing a block's name.
///
/// ⚑ **AND THE PIN IS WHAT REFUSES.** The state lanes are register cells, not immediates, so the ROM
/// is silent — exactly the pole inversion `MinaWrapVerifierSponge` §9 names.
#[test]
fn a_forged_incoming_transcript_state_is_refused() {
    let d = link_desc();
    let trace = parse_trace(LINK_TRACE, 2048);

    let mut pis = parse_pis(LINK_PIS);
    pis[0] = bump_limb8(pis[0]); // low limb of the incoming lane 0
    let err = prove_and_verify(&d, &trace, &pis)
        .expect_err("an incoming state that is not the block's must be REFUSED");
    println!("\n§2 forged INCOMING TRANSCRIPT STATE REFUSED: {err}");
    assert!(
        !err.contains("exact-public"),
        "the ROM must be SILENT about the transcript state -- the PIN is what refuses; got: {err}"
    );
}

/// ⚑ **§3 — THE ABSORBED ELEMENT IS BOUND, AND ONLY BY THE PIN.** Claim the sponge absorbed
/// something other than the block's 91st tape element. Every instruction word is unchanged, so the
/// bus stays balanced; the boundary pin is the whole of the transcript binding.
#[test]
fn a_forged_absorbed_transcript_element_is_refused() {
    let d = link_desc();
    let trace = parse_trace(LINK_TRACE, 2048);

    let mut pis = parse_pis(LINK_PIS);
    pis[3 * SK] = bump_limb8(pis[3 * SK]);
    let err = prove_and_verify(&d, &trace, &pis)
        .expect_err("an absorbed element that is not the tape's must be REFUSED");
    println!("\n§3 forged ABSORBED TAPE ELEMENT REFUSED (PI): {err}");
    assert!(
        !err.contains("exact-public"),
        "the ROM must be SILENT about WHICH value is absorbed; got: {err}"
    );

    // …and the same lie told in the TRACE instead of the claim. Row 0's R3 is the register the
    // first absorb instruction reads.
    let pis = parse_pis(LINK_PIS);
    let mut t = parse_trace(LINK_TRACE, 2048);
    t[0][reg_col(3)] = bump_limb8(t[0][reg_col(3)]);
    let err = prove_and_verify(&d, &t, &pis)
        .expect_err("a trace that absorbs a different element must be REFUSED");
    println!("§3b forged ABSORBED TAPE ELEMENT REFUSED (trace): {err}");
    assert!(!err.is_empty());
}

/// ⚑ **§4 — AND THE SQUEEZE IS BOUND AT BOTH LANES.** Claim a different `v′`, then a different `u′`.
/// `u′` is the one a single-output pin would have left free: it is lane 1 of the same permutation
/// and no instruction reads it after the last round.
#[test]
fn a_forged_challenge_is_refused_at_both_lanes() {
    let d = link_desc();
    let trace = parse_trace(LINK_TRACE, 2048);

    let mut pis = parse_pis(LINK_PIS);
    pis[5 * SK] = bump_limb8(pis[5 * SK]);
    let err = prove_and_verify(&d, &trace, &pis)
        .expect_err("a claimed v' that is not the link's squeeze must be REFUSED");
    println!("\n§4 forged v' (polyscale) REFUSED: {err}");
    assert!(!err.is_empty());

    let mut pis = parse_pis(LINK_PIS);
    pis[6 * SK] = bump_limb8(pis[6 * SK]);
    let err = prove_and_verify(&d, &trace, &pis)
        .expect_err("a claimed u' that is not the link's squeeze must be REFUSED");
    println!("§4b forged u' (evalscale) REFUSED: {err}");
    assert!(!err.is_empty());
}

/// ⚑ **§5 — THE `fq_kimchi` CONSTANTS ARE THE DESCRIPTOR'S, ON THIS INSTANCE TOO.** Give round 3 the
/// round constant of round 7. Both are in the manifest, but not at those keys, so the queried
/// MULTISET changes — and here the refusal MUST be the ROM bus, because the transcript binding
/// above rests on the pin and this one must not.
#[test]
fn a_prover_chosen_round_constant_is_refused_by_the_rom() {
    let d = link_desc();
    let pis = parse_pis(LINK_PIS);
    let rom = rom_rows(&d);

    // instruction index of round r's first round-constant add: 2 absorbs + 30r + 17
    let rc_instr = |r: usize| 2 + ROWS_PER_ROUND * r + 17;
    let (i3, i7) = (rc_instr(3), rc_instr(7));
    assert_ne!(
        rom[i3][23..55],
        rom[i7][23..55],
        "round 3 and round 7 carry different constants, so the swap is a real lie"
    );

    let mut t = parse_trace(LINK_TRACE, 2048);
    // both are IMMEDIATE-operand instructions, which is what makes them the ROM's business
    assert!((0..NREG).all(|r| t[i3][YSEL_BASE + r].as_u32() == 0));
    for i in 0..SK {
        let a = t[i3][IMM_BASE + i];
        t[i3][IMM_BASE + i] = t[i7][IMM_BASE + i];
        t[i7][IMM_BASE + i] = a;
    }
    let err = prove_and_verify(&d, &t, &pis)
        .expect_err("round 3 using round 7's constant must be REFUSED");
    println!("\n§5 SWAPPED fq_kimchi ROUND CONSTANTS REFUSED: {err}");
    assert!(
        err.contains("exact-public") || err.contains("LookupError") || err.contains("Lookup"),
        "the ROM BUS must refuse a constant used at the wrong round -- got: {err}"
    );
}

/// ⚑ **§6 — AND THE ORDER IS THE `pc` THREAD'S.** Swap two whole rows: each carries its own `pc`
/// cell, so the queried multiset is unchanged and the bus stays balanced. An algebraic gate refuses.
///
/// Together with §2–§5 this is the whole division of labour, measured on a real transcript:
/// **bus → which constant at which round · pc thread → order · pins → the transcript itself.**
#[test]
fn a_reordered_permutation_is_refused_by_the_pc_thread() {
    let d = link_desc();
    let pis = parse_pis(LINK_PIS);
    let mut t = parse_trace(LINK_TRACE, 2048);
    t.swap(500, 501);

    let err = prove_and_verify(&d, &t, &pis)
        .expect_err("instructions executed out of ROM order must be REFUSED");
    println!("\n§6 REORDERED INSTRUCTIONS REFUSED: {err}");
    assert!(
        err.contains("OodEvaluationMismatch"),
        "the pc THREAD (an algebraic gate) must refuse a reorder, not the bus -- got: {err}"
    );
    println!(
        "\n⚑ THE DIVISION OF LABOUR ON A REAL TRANSCRIPT:\n  \
         the ROM bus fixes WHICH fq_kimchi constant runs at WHICH round (§5)\n  \
         the pc thread fixes the ORDER the 1 652 instructions run in (§6)\n  \
         the PI pins fix THE TRANSCRIPT -- the incoming state, the absorbed element and both\n  \
         squeezed challenges (§2, §3, §4). The ROM is silent about every one of those."
    );
}

/// ⚑ **§7 — THE RESIDUAL, MEASURED RATHER THAN ASSERTED.** One of the block's 46 phase-2
/// permutations is in the AIR. This prints what the other 45 would cost, so the residual in the
/// docblock is a number a reader can check rather than a hedge.
#[test]
fn the_rest_of_the_tape_is_priced() {
    let d = link_desc();
    let committed = committed_width(&d);
    let per_perm = FULL_ROUNDS * ROWS_PER_ROUND;
    let (_, _, _, tape_len) = the_block();
    // rate 2: elements 3, 5, …, 91 each trigger one arrival permutation, plus the closing squeeze.
    let perms = (tape_len - 1) / 2 + 1;
    let rows = perms * per_perm + tape_len;
    let bytes_per_row = LINK_TRACE.len() / 2048;

    println!("\n═══ §7  WHAT THE WHOLE TAPE WOULD COST ═══");
    println!(
        "tape {tape_len} elements at rate 2 = {perms} permutations x {per_perm} rows = {rows} \
         instructions"
    );
    println!(
        "  committed {:.2} GB; emitted witness TEXT ~{:.0} MB at the measured {bytes_per_row} \
         bytes/row",
        rows as f64 * committed as f64 * 4.0 / 1e9,
        rows as f64 * bytes_per_row as f64 / 1e6,
    );
    println!(
        "  EMITTED HERE: 1 permutation of {perms} (the closing squeeze + its absorb), 2048 rows, \
         {:.1} MB.",
        LINK_TRACE.len() as f64 / 1e6
    );
    println!(
        "  the other {} are `PastaPoseidonFq.Core` -- the reference \
         `the_permutation_program_computes_the_kimchi_permutation` proves this program computes at \
         EVERY state. The residual is {} WITNESSES, not an algebra.",
        perms - 1,
        perms - 1
    );
    assert_eq!(perms, 46, "the arithmetic the docblock quotes");
}
