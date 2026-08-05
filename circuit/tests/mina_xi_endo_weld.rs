//! # ξ IS COMPUTED: the endomorphism lift PROVED on the deployed prover, and WELDED to the ξ chain
//! by a 32-felt public-input equality — both polarities, in RELEASE, with the refusing gate named.
//!
//! ## Substrate, said out loud
//!
//! **The AIR is Lean-authored.** The descriptor is
//! `Dregg2.Circuit.Emit.MinaWrapXiEndoLift.endoDesc` — `EffectLower.lowerAir` of an
//! `EffectAirIR.EffectAir` built from `MinaWrapCommitMachine.commitAir`, the same machine
//! `MinaWrapCommitStages` emits its four stages on. Nothing in this file and nothing in
//! `dregg-circuit` authors a constraint, a gadget or an `air_accepts` predicate. Rust parses the
//! emitted JSON, fills trace CELLS from a Lean-emitted fixture, and runs `prove_vm_descriptor2`.
//! House Law #1.
//!
//! ## What this closes
//!
//! `MinaWrapXiAggregateMsm` §4, its author's own closing sentence:
//!
//! > **`ξ` ITSELF.** `SCAL` is the 47 powers as descriptor constants. […] the aggregate's scalar
//! > multiplication is now the trace's work; the aggregate's scalars are still the verifier's to be
//! > told.
//!
//! The cone behind ξ is a sponge, and the whole of it is now emitted:
//! `MinaPhase2Chain.the_whole_phase2_transcript_folds_into_one_claim` proves **46 links** of
//! `dregg-pasta-fq-chainlink::v1` over Mina devnet block **539508**'s real 91-element phase-2 tape,
//! ending on that block's own `v′` and `u′`. The step from `v′` to ξ is
//! `ScalarChallenge::to_field(endo_r)` (`sponge.rs:190-226`), and **this file's descriptor is that
//! step as an AIR**: 64 rounds of double-and-conditional-±1, a 128-place in-circuit bit
//! decomposition, and a closing `SC = v′` assertion that makes the bits the bits OF the published
//! prechallenge.
//!
//! ⚠ **§4 WELDS TO THE 46th CHAIN LINK, NOT TO `dregg-pasta-fq-wraplink::v1`.** The seven-block
//! wraplink descriptor exposes only TWO of a Poseidon state's THREE outgoing lanes
//! (`MinaPhase2Chain`: *"the successor's third lane would be a free prover scalar"*). Welding to it
//! would inherit that seam; it is kept here only as a corroboration.
//!
//! ## ⚑ THE WELD, AND ITS WIDTH
//!
//! Two separately emitted descriptors share a boundary:
//!
//! | | first-row pin | last-row pin |
//! |---|---|---|
//! | `dregg-mina-xi-endo-lift::v1` | `v′`, 32 limbs | **ξ, 32 limbs** |
//! | `dregg-mina-xi-scalar-vector::v1` | **ξ, 32 limbs** | `ξ⁴⁶`, 32 limbs |
//!
//! `the_endo_output_pi_block_is_the_chain_input_pi_block` checks those 32 felts **elementwise**.
//! It is not a digest and it has no birthday bound: 255 bits of agreement, one felt at a time.
//! ⚠ That distinction is the whole point — the `proof_bind` seam's `commit`/`vk`/`bound` are ONE
//! felt each against an eight-lane object, which is `2^31` and below this repo's ~124-bit bar. A
//! PI equality between two descriptors is exactly where that mistake is free to make.
//!
//! ## ⚠ WHAT IS STILL TOLD — read before reading any green
//!
//! The ξ-AGGREGATE's 47 scalars are **still descriptor constants.** `PastaMsmBucketed` §7.4:
//! *"This descriptor's `piCount = 27` publishes only the output `C`; `u⃗` enters through `T_COVER`'s
//! declared digits and is therefore a DESCRIPTOR PARAMETER, not a wire value."* There is no PI slot
//! on the aggregate for this file's output to equal, so the aggregate side is joined by a
//! **descriptor-to-descriptor** equality instead (§3 here, `MinaWrapXiScalarWeld` in Lean): the
//! emitted `pasta_msm_cover` manifest, recomposed in THIS FILE's own arithmetic keyed by each row's
//! own generator index, against the orbit of the ξ that crosses the wire. 47 scalars × 255 bits,
//! elementwise. It is checked once per (block, VK) by whoever reads the artifacts — **not** by a
//! batch, and it costs the reader the 46 multiplies the chain circuit exists to remove.
//!
//! ⚑ **AND THE `fpMulCore` DOWNGRADE IS NOT LIFTED.** The aggregate's rows are the unsound
//! multiply; this descriptor and every `MinaWrapCommitStages` one are `PastaFieldSound`. Nothing
//! here repairs that and nothing here spreads it.
//!
//! ⚑ **RELEASE, DELIBERATELY.** Algebraic refusals are `debug_assert` PANICS in debug and clean
//! `Err(...)` in release; a refusal test that passes only in debug is testing the assertion.
//!
//! Run: `cargo test -p dregg-circuit --release --test mina_xi_endo_weld -- --nocapture`

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TableSem, parse_vm_descriptor2,
    parse_vm_descriptor2_unsound_oversized, prove_vm_descriptor2, verify_vm_descriptor2,
};

const CM_WIDTH: usize = 687;
const SK: usize = 32;

const ENDO_DESC: &str = include_str!("../descriptors/by-name/mina-xi-endo-lift.json");
const ENDO_TRACE: &str = include_str!("fixtures/mina-xi-endo-lift-trace.txt");
const ENDO_PIS: &str = include_str!("fixtures/mina-xi-endo-lift-pis.txt");
const CHAIN_DESC: &str = include_str!("../descriptors/by-name/mina-commit-xi.json");
const CHAIN_PIS: &str = include_str!("fixtures/mina-commit-xi-pis.txt");
const AGG_DESC: &str = include_str!("../descriptors/by-name/mina-xi-aggregate-msm.json");
/// ⚑ **THE 46th AND LAST LINK OF `dregg-pasta-fq-chainlink::v1`** — the descriptor
/// `the_whole_phase2_transcript_folds_into_one_claim` folds 46 of, over Mina devnet block 539508's
/// real 91-element phase-2 tape. Its outgoing state is the block's terminal squeeze.
///
/// ⚠ **THIS IS DELIBERATELY NOT `pasta-fq-wraplink-pis.txt`.** `MinaPhase2Chain` §"WHY THE OLD
/// DESCRIPTOR COULD NOT BE CHAINED": `MinaBlockFqTranscript.linkPins` pins SEVEN blocks and exposes
/// only TWO of a Poseidon state's THREE outgoing lanes — *"the successor's third lane would be a
/// free prover scalar and the chain would prove nothing about the transcript."* `chainPins` pins
/// EIGHT (`in(3) ++ out(3) ++ absorbed(2)`, 256 PIs). A weld to the seven-block descriptor would
/// inherit that seam, so this file welds to the eight-block one.
///
/// ⚠ **READ OUT OF THE TRACKED AGGREGATE, ONE LINE PER LINK — NOT out of the emit directory.**
/// `circuit/tests/fixtures/pasta-fq-chainlink/.gitignore` ignores `link-*-pis.txt`: those 46 files
/// are the ~150 MB emit's by-products and are regenerated, never committed. A committed
/// `include_str!` of one of them compiles for whoever ran the emit and REDS FOR EVERY FRESH CLONE,
/// which is what HEAD did between `f93e47090` and this line. The 46 public-input vectors are
/// tracked one directory up, exactly as that `.gitignore` says they are, and this reads link 45
/// from there — ONE source of these bytes, not two that agree today.
const CHAINLINK_ALL_PIS: &str = include_str!("fixtures/pasta-fq-chainlink-pis.txt");

/// The number of links the phase-2 chain folds — one tracked PI line each.
const CHAINLINK_LINKS: usize = 46;

/// Link 45's public inputs: the last line of [`CHAINLINK_ALL_PIS`]. Byte-identical to the emit's
/// `link-45-pis.txt`, which is why that file can stay untracked.
fn chainlink_pis() -> &'static str {
    let mut lines = CHAINLINK_ALL_PIS.lines();
    let n = CHAINLINK_ALL_PIS.lines().count();
    assert_eq!(
        n, CHAINLINK_LINKS,
        "the tracked chain-link PI aggregate carries {n} lines; the fold is {CHAINLINK_LINKS} links \
         — re-emit it rather than reading a truncated chain"
    );
    lines
        .nth(CHAINLINK_LINKS - 1)
        .expect("checked non-empty above")
}

/// The seven-block descriptor's PIs, kept ONLY as a corroboration that the two emissions agree on
/// the squeeze — never as the weld's own side.
const WRAPLINK_PIS: &str = include_str!("fixtures/pasta-fq-wraplink-pis.txt");

/// `chainPins`' layout is `in(3) ++ out(3) ++ absorbed(2)`, so outgoing lane 0 — the `v′` lane — is
/// block 3, at `[3·SK, 4·SK)`.
const CHAINLINK_V_BLOCK: usize = 3;

/// The PI block index at which the SEVEN-block wraplink descriptor publishes its raw lane-0 squeeze.
const WRAPLINK_V_BLOCK: usize = 5;

// ---------------------------------------------------------------------------------------------
// §0 — the fixtures, and the arithmetic this file does for itself.
// ---------------------------------------------------------------------------------------------

/// ⚑ **EVERY FIXTURE IS NON-EMPTY, CHECKED BEFORE ANYTHING READS ONE.** `include_str!` accepts a
/// 0-byte file and yields `""`; a sibling test in this cone reported success against nothing for
/// exactly that reason, because a MISSING fixture is a loud compile error and an EMPTY one is
/// silent.
#[test]
fn no_fixture_is_empty() {
    let mut n = 0usize;
    for (label, text) in [
        ("endo desc", ENDO_DESC),
        ("endo trace", ENDO_TRACE),
        ("endo pis", ENDO_PIS),
        ("chain desc", CHAIN_DESC),
        ("chain pis", CHAIN_PIS),
        ("aggregate desc", AGG_DESC),
        ("chainlink link-45 pis", chainlink_pis()),
        ("wraplink pis", WRAPLINK_PIS),
    ] {
        assert!(
            !text.trim().is_empty(),
            "{label} is EMPTY -- include_str! accepted a 0-byte file and this test would have \
             reported success against nothing"
        );
        n += 1;
    }
    assert_eq!(n, 8);
    println!("\n§0 all {n} fixtures non-empty");
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
    text.split_whitespace()
        .map(|c| BabyBear::new(c.parse::<u32>().expect("PI is a u32 decimal")))
        .collect()
}

fn prove_and_verify(
    d: &EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    pis: &[BabyBear],
) -> Result<(), String> {
    let proof = prove_vm_descriptor2(d, trace, pis, &MemBoundaryWitness::default(), &[])?;
    verify_vm_descriptor2(d, &proof, pis)
}

/// A forgery that stays INSIDE the declared 8-bit range, so a RANGE lookup cannot be what refuses
/// and the gate under test is actually exercised.
fn bump_limb8(cell: BabyBear) -> BabyBear {
    BabyBear::new((cell.as_u32() + 1) % 256)
}

/// A 256-bit unsigned integer, little-endian in 32-bit words. This file does its own arithmetic
/// rather than trusting a decimal: a `Vec<u32>` limb pile with schoolbook mul and Barrett-free
/// reduction by repeated subtraction is enough for 47 modular multiplies.
type Big = Vec<u32>;

fn big_from_limbs8(limbs: &[BabyBear]) -> Big {
    let mut bytes = vec![0u8; limbs.len()];
    for (i, c) in limbs.iter().enumerate() {
        let v = c.as_u32();
        assert!(v < 256, "a limb pin carries an 8-bit value, got {v}");
        bytes[i] = v as u8;
    }
    big_from_le_bytes(&bytes)
}

fn big_from_le_bytes(bytes: &[u8]) -> Big {
    let mut w = vec![0u32; bytes.len().div_ceil(4)];
    for (i, b) in bytes.iter().enumerate() {
        w[i / 4] |= (*b as u32) << (8 * (i % 4));
    }
    big_trim(w)
}

fn big_trim(mut w: Big) -> Big {
    while w.len() > 1 && *w.last().unwrap() == 0 {
        w.pop();
    }
    w
}

fn big_cmp(a: &Big, b: &Big) -> std::cmp::Ordering {
    let (a, b) = (big_trim(a.clone()), big_trim(b.clone()));
    if a.len() != b.len() {
        return a.len().cmp(&b.len());
    }
    for i in (0..a.len()).rev() {
        if a[i] != b[i] {
            return a[i].cmp(&b[i]);
        }
    }
    std::cmp::Ordering::Equal
}

fn big_sub(a: &Big, b: &Big) -> Big {
    let mut out = vec![0u32; a.len()];
    let mut borrow = 0i64;
    for i in 0..a.len() {
        let bi = *b.get(i).unwrap_or(&0) as i64;
        let mut d = a[i] as i64 - bi - borrow;
        borrow = 0;
        if d < 0 {
            d += 1i64 << 32;
            borrow = 1;
        }
        out[i] = d as u32;
    }
    assert_eq!(borrow, 0, "big_sub underflow");
    big_trim(out)
}

fn big_mul(a: &Big, b: &Big) -> Big {
    let mut out = vec![0u64; a.len() + b.len() + 1];
    for (i, x) in a.iter().enumerate() {
        let mut carry = 0u64;
        for (j, y) in b.iter().enumerate() {
            let cur = out[i + j] + (*x as u64) * (*y as u64) + carry;
            out[i + j] = cur & 0xffff_ffff;
            carry = cur >> 32;
        }
        let mut k = i + b.len();
        while carry > 0 {
            let cur = out[k] + carry;
            out[k] = cur & 0xffff_ffff;
            carry = cur >> 32;
            k += 1;
        }
    }
    big_trim(out.into_iter().map(|v| v as u32).collect())
}

fn big_shl1(a: &Big) -> Big {
    let mut out = vec![0u32; a.len() + 1];
    let mut carry = 0u32;
    for i in 0..a.len() {
        out[i] = (a[i] << 1) | carry;
        carry = a[i] >> 31;
    }
    out[a.len()] = carry;
    big_trim(out)
}

fn big_bitlen(a: &Big) -> usize {
    let a = big_trim(a.clone());
    let top = *a.last().unwrap();
    if top == 0 {
        return 0;
    }
    (a.len() - 1) * 32 + (32 - top.leading_zeros() as usize)
}

/// `a mod m`, by shift-and-subtract. Slow and obvious on purpose: this file's job is to be an
/// INDEPENDENT arithmetic, not a fast one.
fn big_mod(a: &Big, m: &Big) -> Big {
    let mut r = big_trim(a.clone());
    if big_cmp(&r, m) == std::cmp::Ordering::Less {
        return r;
    }
    let mut shifted = vec![m.clone()];
    while big_bitlen(shifted.last().unwrap()) <= big_bitlen(&r) {
        let next = big_shl1(shifted.last().unwrap());
        shifted.push(next);
    }
    for s in shifted.iter().rev() {
        if big_cmp(&r, s) != std::cmp::Ordering::Less {
            r = big_sub(&r, s);
        }
    }
    r
}

fn big_mulmod(a: &Big, b: &Big, m: &Big) -> Big {
    big_mod(&big_mul(a, b), m)
}

fn big_dec(a: &Big) -> String {
    let mut digits: Vec<u8> = vec![0];
    for w in a.iter().rev() {
        for bit in (0..32).rev() {
            let mut carry = (w >> bit) & 1;
            for d in digits.iter_mut() {
                let v = (*d as u32) * 2 + carry;
                *d = (v % 10) as u8;
                carry = v / 10;
            }
            while carry > 0 {
                digits.push((carry % 10) as u8);
                carry /= 10;
            }
        }
    }
    while digits.len() > 1 && *digits.last().unwrap() == 0 {
        digits.pop();
    }
    digits.iter().rev().map(|d| (b'0' + d) as char).collect()
}

/// The Pallas SCALAR prime `q` (`PastaField.qN`) — `2^254 + 0x224698fc0994a8dd8c46eb2100000001`,
/// the field ξ and its powers live in. ⚑ **This is the ONLY typed constant in the file**, and it is
/// a curve parameter rather than a per-block value: every other number here is read out of an
/// emitted artifact. Reading the powers in the BASE field is the classic Pasta error and
/// `MinaWrapXiEndoLift.the_base_field_lift_is_a_different_scalar` is its refutation in Lean.
fn q_pasta() -> Big {
    big_from_le_bytes(&[
        0x01, 0x00, 0x00, 0x00, 0x21, 0xeb, 0x46, 0x8c, 0xdd, 0xa8, 0x94, 0x09, 0xfc, 0x98, 0x46,
        0x22, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x40,
    ])
}

// ---------------------------------------------------------------------------------------------
// §1 — the endo-lift descriptor PROVES and VERIFIES.
// ---------------------------------------------------------------------------------------------

#[test]
fn the_endo_lift_proves_and_verifies() {
    let d = parse_vm_descriptor2(ENDO_DESC).expect("the deployed checker parses the Lean artifact");
    let trace = parse_trace(ENDO_TRACE);
    let pis = parse_pis(ENDO_PIS);

    assert_eq!(d.name, "dregg-mina-xi-endo-lift::v1");
    assert_eq!(d.trace_width, CM_WIDTH);
    assert_eq!(d.public_input_count, 64, "32 limbs of v', 32 limbs of xi");
    assert_eq!(pis.len(), 64);
    assert_eq!(trace.len(), 2048, "the emitted height is 2^11");

    let t0 = std::time::Instant::now();
    prove_and_verify(&d, &trace, &pis).expect("the honest endo-lift trace proves and verifies");
    println!(
        "\n§1 dregg-mina-xi-endo-lift::v1 PROVED+VERIFIED  {}x{}  {:.1} ms",
        trace.len(),
        d.trace_width,
        t0.elapsed().as_secs_f64() * 1e3
    );
}

/// ⚑ **THE PIN REFUSES A DIFFERENT LIFTED SCALAR.** The output half of the public inputs moved by
/// one limb, inside the 8-bit range. The refusing gate is the LAST-ROW PI BINDING (`pinPair`'s
/// last-row limbs) — the descriptor's ROM says nothing about the lifted value, so this is the pin
/// and not the bus, and a `OodEvaluationMismatch` is what a PI pin's boundary constraint produces.
#[test]
fn a_forged_lift_output_is_refused() {
    let d = parse_vm_descriptor2(ENDO_DESC).expect("parses");
    let trace = parse_trace(ENDO_TRACE);
    let mut pis = parse_pis(ENDO_PIS);
    pis[SK] = bump_limb8(pis[SK]);

    let err = prove_and_verify(&d, &trace, &pis)
        .expect_err("a lifted scalar that is not the one the trace computed must be REFUSED");
    assert!(
        err.contains("OodEvaluationMismatch")
            || err.contains("constraints not satisfied")
            || err.contains("boundary"),
        "the LAST-ROW PI PIN must refuse a forged lift output -- got: {err}"
    );
    println!("§1b forged lift output REFUSED by the last-row PI pin: {err}");
}

/// ⚑ **AND THE PIN REFUSES A DIFFERENT PRECHALLENGE.** The input half moved by one limb. This is
/// the transcript binding: `MinaBlockFqTranscript` says the absorbed value is a register operand
/// with a zero immediate, so the ROM is SILENT about which challenge it is and the binding rests on
/// the FIRST-ROW pin. The same pole split holds here — and the closing `SC = v′` assertion is what
/// makes a moved input inconsistent with the 128 witnessed bits.
#[test]
fn a_forged_prechallenge_is_refused() {
    let d = parse_vm_descriptor2(ENDO_DESC).expect("parses");
    let trace = parse_trace(ENDO_TRACE);
    let mut pis = parse_pis(ENDO_PIS);
    pis[0] = bump_limb8(pis[0]);

    let err = prove_and_verify(&d, &trace, &pis)
        .expect_err("a prechallenge that is not the one the bits decompose must be REFUSED");
    assert!(
        err.contains("OodEvaluationMismatch")
            || err.contains("constraints not satisfied")
            || err.contains("boundary"),
        "the FIRST-ROW PI PIN must refuse a forged prechallenge -- got: {err}"
    );
    println!("§1c forged prechallenge REFUSED by the first-row PI pin: {err}");
}

/// ⚑ **AND THE ROM BUS REFUSES A MISPLACED CONSTANT.** `endo_r` enters as a ROM IMMEDIATE, so it is
/// a descriptor cell rather than a witness: a prover that wanted a different endomorphism scalar
/// would have to move the manifest, and `pasta_commit_rom` is `exactPublicRows`, whose lookup log
/// the deployed prover demands be a PERMUTATION of the Lean-emitted manifest. This forgery moves the
/// immediate limb in the TRACE, leaving the manifest alone — the bus is what must fire, not a gate.
#[test]
fn a_misplaced_rom_immediate_is_refused() {
    let d = parse_vm_descriptor2(ENDO_DESC).expect("parses");
    let pis = parse_pis(ENDO_PIS);
    let mut trace = parse_trace(ENDO_TRACE);

    // The `addI ZERO endo_r T0` instruction is the second of the four closing instructions.
    let imm_base = 655usize;
    let row = trace
        .iter()
        .position(|r| r[imm_base].as_u32() != 0 && r[imm_base + 31].as_u32() != 0)
        .expect("the endo_r immediate row is in the trace");
    trace[row][imm_base] = bump_limb8(trace[row][imm_base]);

    let err =
        prove_and_verify(&d, &trace, &pis).expect_err("a re-chosen ROM immediate must be REFUSED");
    assert!(
        err.contains("exact-public") || err.contains("LookupError") || err.contains("Lookup"),
        "the ROM BUS (pasta_commit_rom, exactPublicRows) must refuse a re-chosen immediate -- \
         got: {err}"
    );
    println!("§1d misplaced ROM immediate REFUSED by the exact-public ROM bus: {err}");
}

// ---------------------------------------------------------------------------------------------
// §2 — ⚑ THE WELD: the PI equality, at the real width.
// ---------------------------------------------------------------------------------------------

/// ⚑⚑ **THE ENDO LIFT'S OUTPUT PUBLIC INPUTS ARE THE ξ CHAIN'S INPUT PUBLIC INPUTS.**
///
/// Elementwise over all 32 felts. Two separately emitted descriptors, two separately generated
/// traces, one shared boundary — so a batch that verifies both proofs and compares these two slices
/// learns that the ξ whose powers the chain walks is the ξ the endo AIR derived from the block's own
/// sponge squeeze.
///
/// ⚠ **THE WIDTH IS THE POINT.** This assertion would be equally green over ONE felt, and a one-felt
/// tie between two descriptors is `2^31`. It is 32 felts / 255 bits, checked one at a time, with no
/// digest anywhere in it — so it has no birthday bound at all.
#[test]
fn the_endo_output_pi_block_is_the_chain_input_pi_block() {
    let endo = parse_vm_descriptor2(ENDO_DESC).expect("parses");
    let chain = parse_vm_descriptor2(CHAIN_DESC).expect("parses");
    let endo_pis = parse_pis(ENDO_PIS);
    let chain_pis = parse_pis(CHAIN_PIS);

    assert_ne!(
        endo.name, chain.name,
        "a weld between an artifact and itself is not a weld"
    );
    assert_eq!(endo.name, "dregg-mina-xi-endo-lift::v1");
    assert_eq!(chain.name, "dregg-mina-xi-scalar-vector::v1");
    assert_eq!(endo_pis.len(), 64);
    assert_eq!(chain_pis.len(), 64);

    let out_block = &endo_pis[SK..];
    let in_block = &chain_pis[..SK];
    let mut matched = 0usize;
    for i in 0..SK {
        assert_eq!(
            out_block[i], in_block[i],
            "shared boundary felt {i} disagrees: the endo lift publishes {:?}, the chain consumes \
             {:?}",
            out_block[i], in_block[i]
        );
        matched += 1;
    }
    assert_eq!(matched, 32, "the tie is 32 felts, not a digest");

    // ⚑ And the shared block carries a WHOLE field element, not a tag: 253 significant bits.
    let xi = big_from_limbs8(out_block);
    let q = q_pasta();
    assert_eq!(big_cmp(&xi, &q), std::cmp::Ordering::Less, "xi < q");
    assert!(
        big_bitlen(&xi) >= 252,
        "the shared block carries a full-width scalar, not a short tag -- {} bits",
        big_bitlen(&xi)
    );
    println!(
        "\n§2 WELD: 32/32 shared boundary felts equal; xi = {} ({} bits)",
        big_dec(&xi),
        big_bitlen(&xi)
    );
}

/// ⚑ **AND THE WELD IS REFUTABLE, ONE FELT AT A TIME.** The tie's strength is exactly this: change
/// any single felt of the shared boundary and the equality fails. A digest-shaped tie would survive
/// a change it collided on; this one cannot, because there is nothing to collide.
#[test]
fn any_single_moved_felt_breaks_the_weld() {
    let endo_pis = parse_pis(ENDO_PIS);
    let chain_pis = parse_pis(CHAIN_PIS);
    let mut broken = 0usize;
    for i in 0..SK {
        let mut forged = endo_pis[SK..].to_vec();
        forged[i] = bump_limb8(forged[i]);
        assert_ne!(
            forged.as_slice(),
            &chain_pis[..SK],
            "moving shared felt {i} must break the weld"
        );
        broken += 1;
    }
    assert_eq!(broken, 32);
    println!("§2b all 32/32 single-felt perturbations REFUSED by the weld");
}

/// ⚑ **AND THE CHAIN'S OTHER HALF IS A DIFFERENT VALUE.** The chain publishes `ξ⁴⁶` on its last
/// row; if its two halves agreed, the "weld" above would be satisfied by a chain that computed
/// nothing. This checks the pair overlaps on ξ and disagrees everywhere else.
#[test]
fn the_chain_publishes_a_different_value_at_its_other_end() {
    let chain_pis = parse_pis(CHAIN_PIS);
    assert_ne!(
        &chain_pis[..SK],
        &chain_pis[SK..],
        "the chain's input and output halves must differ -- 46 multiplies did something"
    );

    // ξ⁴⁶ recomputed HERE, from the shared boundary, in this file's own arithmetic.
    let q = q_pasta();
    let xi = big_from_limbs8(&chain_pis[..SK]);
    let mut acc = vec![1u32];
    for _ in 0..46 {
        acc = big_mulmod(&acc, &xi, &q);
    }
    let claimed = big_from_limbs8(&chain_pis[SK..]);
    assert_eq!(
        big_cmp(&acc, &claimed),
        std::cmp::Ordering::Equal,
        "the chain's published output is xi^46 of its published input: got {} want {}",
        big_dec(&claimed),
        big_dec(&acc)
    );
    println!("§2c chain output = xi^46 of the welded xi, recomputed in this file's arithmetic");
}

// ---------------------------------------------------------------------------------------------
// §3 — the AGGREGATE side: a descriptor-to-descriptor tie, at full width, priced honestly.
// ---------------------------------------------------------------------------------------------

/// Read `pasta_msm_cover`'s manifest out of the emitted aggregate descriptor and recompose the 59
/// declared scalars — routed by each row's OWN generator key, not by its position.
fn declared_scalars(d: &EffectVmDescriptor2, n_pad: usize, c: usize) -> Vec<Big> {
    let table = d
        .tables
        .iter()
        .find(|t| t.name == "pasta_msm_cover")
        .expect("the aggregate declares a pasta_msm_cover table");
    let rows = match &table.sem {
        TableSem::ExactPublicRows { rows } => rows,
        other => panic!("pasta_msm_cover must be exact-public, got {other:?}"),
    };
    let mut acc: Vec<Big> = vec![vec![0u32]; n_pad];
    let base = vec![1u32 << c];
    let mut absorbed = 0usize;
    for row in rows {
        assert_eq!(row.len(), 3, "a cover row is (window, generator, digit)");
        let i = row[1] as usize;
        if i == 0 {
            continue;
        }
        let digit = row[2] as u32;
        assert!(digit < (1u32 << c), "a declared digit is {c} bits");
        let slot = i - 1;
        acc[slot] = big_trim(add_small(&big_mul(&acc[slot], &base), digit));
        absorbed += 1;
    }
    assert_eq!(
        absorbed,
        128 * n_pad,
        "128 windows x {n_pad} generators of real term rows"
    );
    acc
}

fn add_small(a: &Big, k: u32) -> Big {
    let mut out = a.clone();
    let mut carry = k as u64;
    let mut i = 0;
    while carry > 0 {
        if i == out.len() {
            out.push(0);
        }
        let cur = out[i] as u64 + carry;
        out[i] = (cur & 0xffff_ffff) as u32;
        carry = cur >> 32;
        i += 1;
    }
    big_trim(out)
}

/// ⚑⚑ **THE AGGREGATE'S DECLARED DIGITS ARE THE ORBIT OF THE ξ ON THE WIRE.**
///
/// The emitted `pasta_msm_cover` manifest — 8 192 rows, 7 552 of them real — read as data, keyed by
/// each row's own generator index, recomposed base-4 over 128 windows in this file's own big-integer
/// arithmetic, and compared against `ξ⁰ … ξ⁴⁶` computed here from the 32 shared boundary felts.
/// **47 scalars × 255 bits, elementwise.** Nothing transcribed; the only decimal in this file is `q`.
///
/// ⚠ **AND THIS IS A DESCRIPTOR-TO-DESCRIPTOR TIE, NOT A WIRE ONE** — because the aggregate's
/// `public_input_count` is 27, which cannot hold even ONE 32-limb scalar. Asserted below so the
/// limit is measured rather than described.
#[test]
fn the_aggregate_declares_the_orbit_of_the_welded_xi() {
    let agg = parse_vm_descriptor2_unsound_oversized(AGG_DESC)
        .expect("the aggregate parses through the oversized path (495-bit gate coefficients)");
    let chain_pis = parse_pis(CHAIN_PIS);
    let q = q_pasta();
    let xi = big_from_limbs8(&chain_pis[..SK]);

    assert_eq!(
        agg.public_input_count, 27,
        "the aggregate publishes only its output point"
    );
    assert!(
        agg.public_input_count < SK,
        "27 felts cannot hold one 32-limb scalar, let alone 47 -- this is WHY the tie below is a \
         descriptor equality and not a public-input one"
    );

    let declared = declared_scalars(&agg, 59, 2);
    let mut want = vec![1u32];
    let mut checked = 0usize;
    for (i, item) in declared.iter().enumerate().take(47) {
        assert_eq!(
            big_cmp(item, &want),
            std::cmp::Ordering::Equal,
            "declared scalar {i} is {} but the orbit of the welded xi says {}",
            big_dec(item),
            big_dec(&want)
        );
        want = big_mulmod(&want, &xi, &q);
        checked += 1;
    }
    for (i, item) in declared.iter().enumerate().skip(47) {
        assert_eq!(
            big_trim(item.clone()),
            vec![0u32],
            "padding term {i} carries scalar 0"
        );
        checked += 1;
    }
    assert_eq!(checked, 59, "47 real terms and 12 inert padding terms");
    println!(
        "§3 47/47 declared scalars are the orbit of the welded xi; 12/12 padding terms are zero"
    );
}

/// ⚑ **AND THE ORBIT IS NOT CONSTANT.** If ξ were 0 or 1 the theorem above would be green over a
/// manifest that declared the same scalar 47 times, which is exactly what a silently-zeroed
/// boundary produces. 47 distinct values, counted.
#[test]
fn the_declared_orbit_is_forty_seven_distinct_scalars() {
    let agg = parse_vm_descriptor2_unsound_oversized(AGG_DESC).expect("parses");
    let declared = declared_scalars(&agg, 59, 2);
    let mut seen: Vec<String> = declared.iter().take(47).map(big_dec).collect();
    seen.sort();
    seen.dedup();
    assert_eq!(
        seen.len(),
        47,
        "the declared orbit must be 47 DIFFERENT scalars"
    );
    println!("§3b the declared orbit is 47 distinct scalars");
}

// ---------------------------------------------------------------------------------------------
// §4 — the third cone: ξ traced back to the squeeze the 46-link chain ends on.
// ---------------------------------------------------------------------------------------------

/// ⚑⚑ **THE ENDO LIFT'S INPUT IS THE CHAIN'S TERMINAL SQUEEZE, TRUNCATED.**
///
/// `dregg-pasta-fq-chainlink::v1`'s 46th link publishes its outgoing state IN FULL — three lanes,
/// `chainPins`' blocks 3/4/5 — and lane 0 is the block's terminal squeeze.
/// `challenge()` (`sponge.rs:265-277`) keeps the two least-significant 64-bit limbs, so `v′` is that
/// value's low 128 bits — and this file's endo descriptor consumes exactly those 16 felts, with its
/// remaining 16 input felts pinned to ZERO so a 255-bit value cannot be fed in as a challenge.
///
/// ⚠ **WHY THE 46th CHAIN LINK AND NOT THE WRAPLINK.** `MinaPhase2Chain` found that
/// `MinaBlockFqTranscript.linkPins` exposes only TWO of a Poseidon state's THREE outgoing lanes, so
/// *"the successor's third lane would be a free prover scalar and the chain would prove nothing
/// about the transcript."* Welding to that descriptor would inherit the seam. `the_two_emissions_
/// agree_on_the_squeeze` below keeps the seven-block artifact as a CORROBORATION and not as a side
/// of the weld.
///
/// **This is the last link.** With it, ξ is: the block's 91-element phase-2 tape → 46 emitted Fq
/// sponge links → `v′` → an emitted endo lift → ξ → an emitted 46-multiply chain → `ξ⁴⁶`, and the
/// aggregate's declared digits are that ξ's orbit. Every arrow but the last is a public-input
/// equality between two emitted artifacts.
#[test]
fn the_endo_input_is_the_chain_terminal_squeeze_truncated() {
    let endo_pis = parse_pis(ENDO_PIS);
    let link_pis = parse_pis(chainlink_pis());
    assert_eq!(
        link_pis.len(),
        8 * SK,
        "the chain link publishes 8 limb blocks -- in(3) ++ out(3) ++ absorbed(2)"
    );

    let raw = &link_pis[CHAINLINK_V_BLOCK * SK..(CHAINLINK_V_BLOCK + 1) * SK];
    let mut matched = 0usize;
    for i in 0..16 {
        assert_eq!(
            endo_pis[i], raw[i],
            "the endo lift's input felt {i} is the chain's terminal squeeze felt {i}"
        );
        matched += 1;
    }
    for i in 16..SK {
        assert_eq!(
            endo_pis[i].as_u32(),
            0,
            "the endo lift's input felt {i} is pinned to ZERO -- a ScalarChallenge is 128 bits, and \
             a 128-bit bit vector has exactly one field representative"
        );
    }
    assert_eq!(matched, 16, "128 bits of challenge, felt by felt");

    let v = big_from_limbs8(&endo_pis[..SK]);
    let raw_big = big_from_limbs8(raw);
    assert!(
        big_bitlen(&v) <= 128,
        "v' is below the truncation, {} bits",
        big_bitlen(&v)
    );
    assert!(
        big_bitlen(&raw_big) > 128,
        "the RAW squeeze is not below it -- so the truncation is load-bearing and not a no-op \
         ({} bits)",
        big_bitlen(&raw_big)
    );
    println!(
        "\n§4 endo input = chain link 45's terminal squeeze low-128: v' = {} ({} bits) out of raw \
         {} bits",
        big_dec(&v),
        big_bitlen(&v),
        big_bitlen(&raw_big)
    );
}

/// ⚑ **AND THE TWO EMISSIONS AGREE ON THE SQUEEZE.** The seven-block `dregg-pasta-fq-wraplink::v1`
/// and the eight-block `dregg-pasta-fq-chainlink::v1` are the same `programAir qLimb absorbProg`
/// with different boundary pins, so their published lane-0 squeezes must be the same 32 felts. This
/// is a CORROBORATION — the weld above stands on the chain link, which pins the third lane the
/// seven-block descriptor left free.
#[test]
fn the_two_emissions_agree_on_the_squeeze() {
    let link_pis = parse_pis(chainlink_pis());
    let wrap_pis = parse_pis(WRAPLINK_PIS);
    assert_eq!(
        wrap_pis.len(),
        7 * SK,
        "the wraplink publishes 7 limb blocks"
    );
    let chain_v = &link_pis[CHAINLINK_V_BLOCK * SK..(CHAINLINK_V_BLOCK + 1) * SK];
    let wrap_v = &wrap_pis[WRAPLINK_V_BLOCK * SK..(WRAPLINK_V_BLOCK + 1) * SK];
    assert_eq!(
        chain_v, wrap_v,
        "the two boundary emissions of the SAME program must publish the same squeeze"
    );
    println!(
        "§4b the 7-block and 8-block emissions agree on all {SK} squeeze felts (corroboration only)"
    );
}

/// The census this cone should be read at, printed so a report cannot round it up.
#[test]
fn the_census() {
    let endo = parse_vm_descriptor2(ENDO_DESC).expect("parses");
    let chain = parse_vm_descriptor2(CHAIN_DESC).expect("parses");
    let agg = parse_vm_descriptor2_unsound_oversized(AGG_DESC).expect("parses");
    println!("\n=== the xi cone, at CURRENT resolution ===");
    println!(
        "  {:<38} {:>6} rows  {:>5} cols  {:>4} PIs  {}",
        endo.name, 2048, endo.trace_width, endo.public_input_count, "PastaFieldSound"
    );
    println!(
        "  {:<38} {:>6} rows  {:>5} cols  {:>4} PIs  {}",
        chain.name, 64, chain.trace_width, chain.public_input_count, "PastaFieldSound"
    );
    println!(
        "  {:<38} {:>6} rows  {:>5} cols  {:>4} PIs  {}",
        agg.name, 8192, agg.trace_width, agg.public_input_count, "UNSOUND fpMulCore"
    );
    println!("  weld endo->chain : 32 felts / 255 bits, elementwise, no digest");
    println!(
        "  weld chain->endo : 16 felts / 128 bits, elementwise (the whole challenge), off the\n                     8-block chainlink whose THIRD outgoing lane is pinned"
    );
    println!("  weld chain->agg  : DESCRIPTOR-TO-DESCRIPTOR, 47 scalars x 255 bits");
    println!("                     (the aggregate has 27 PIs; there is no wire slot for a scalar)");
}
