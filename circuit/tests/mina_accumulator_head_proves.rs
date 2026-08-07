//! # `dregg-mina-accumulator-head::v1` — **the claim is tied to a head by a CONSTRAINT, and a
//! claim that discharges honestly but belongs to a different head is refused by the AIR.**
//!
//! ## What this file is the tooth for
//!
//! `mina_accumulator_srs_proves.rs` closed the rung below: the declared addends are `−s_r·G_r` over
//! the sha-pinned SRS, so no list of points occurs in the discharge theorem's statement. It left the
//! accumulator's SECOND trusted item exactly where `MinaAccumulatorAir` §8 named it — *"whether the
//! descriptor a node verified against is the one for the block in hand"* — and one half of that was
//! sharper than the rest:
//!
//! > **no gate ties the claim to a head.** `bridge/src/mina_accumulator_discharge.rs::
//! > root_entry_binds_claim` compares a verified root's `acc_in` block against a claim a caller
//! > holds, and its own docblock says what it is: *"a REFUSAL made by the consumer, not a gate"*,
//! > and *"nor does it relate the claim to a tracked head."*
//!
//! So a node that verifies an accumulator root and **forgets to call that function** accepts any
//! discharging claim. `MinaAccumulatorAir` §11 makes it a constraint: `-head` is `-srs`'s algebra
//! plus twelve constraints — a guard forced ON at `.first` and OFF on every successor, nine PI pins
//! publishing the head, and ONE `proof_bind` whose 105 `commit` lanes are `HEAD_STATE(9) ‖ ACC(96)`,
//! `bound` to the descriptor's declared pair and `vk`-pinned to
//! `dregg-mina-lightclient-verify::v1`'s semantic fingerprint. **105 lanes, elementwise, no digest,
//! therefore no birthday bound.**
//!
//! ## ⚑ THE PAIR, AND THE FORGERY IS THE ONE ITEM 2 ADMITTED YESTERDAY
//!
//! The forgery is the honest head chain with the devnet **GENESIS anchor's** nine lanes
//! substituted for block 539508's tip — built CONSTRUCTIVELY here, cell by cell, with the movement
//! asserted before any verdict is read. It is the sharpest forgery this rung can carry: every row is a genuine `rcbSoundRow`, every thread holds, the index column is
//! threaded, the addends ARE the descriptor's declared `−s_r·G_r`, the accumulator VANISHES, and
//! `PI[0..191]` is **byte-identical** to the honest trace's. The only thing wrong with it is that
//! the head it publishes is not the head the descriptor declares — which is precisely *a claim that
//! discharges honestly and belongs to a different head.*
//!
//! It is REFUSED under `-head`, and the isolation is MEASURED rather than asserted:
//! `dregg-mina-accumulator-head-genesis::v1` is a Lean-emitted negative control whose bytes differ
//! from `-head`'s in **exactly one constraint — the `proof_bind` — and within it in exactly the
//! nine head lanes**, and the same forged chain PROVES under it. Two further old-admits poles: the
//! forged chain narrowed to 3 049 columns proves under `-srs`, which carries no seam at all.
//!
//! ## ⚠ WHAT THIS DOES NOT ESTABLISH, and §11's docblock is where it is written at full resolution
//!
//! The seam's ROW-LOCAL half is a constraint and is what this file measures. Its OFF-ROW half —
//! `ProofBind.boundAt`'s *"∃ a verifying sub-proof of the pinned program whose `piCommit` is these
//! 105 lanes"* — names evidence **no program in this tree can produce today**: the head descriptor
//! publishes the tip's nine lanes and does not publish the block's challenge-polynomial commitment
//! at all. That is UNDONE WORK with a named shape, not a caveat, and the cheap version of it
//! (appending 96 free PI slots to the head) is refused in §11 as the same vacuity one layer down.
//!
//! And the PAIRING here is the demonstration's: the head lanes are block 539508's REAL state hash,
//! the claim is `Σ s_r·G_r` at three CHOSEN challenges. `MinaAccumulatorSrsDemo` says so in the
//! same words it says it about `demoChals`.
//!
//! Run: `cargo test -p dregg-circuit --release --test mina_accumulator_head_proves -- --nocapture`
//! ⚠ RELEASE. In debug a lookup refusal is a p3 `#[cfg(debug_assertions)]` panic rather than a
//! clean `Err`, and the release verdict carries the constraint name this file asserts on.

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TableSem, VmConstraint2, decomp_cols_pub,
    parse_vm_descriptor2, prove_vm_descriptor2, prove_vm_descriptor2_unchecked,
    verify_vm_descriptor2,
};
use dregg_circuit::descriptor_ir2_canonical::effect_vm_descriptor2_semantic_fingerprint;
use dregg_circuit::lean_descriptor_air::LeanExpr;
use dregg_circuit::refusal::{assert_violated_constraint_not_bus, must_refuse_or_unsat_panic};

// -------------------------------------------------------------------------------------------
// The artifacts. All Lean-emitted; nothing here is authored.
// -------------------------------------------------------------------------------------------

const HEAD_JSON: &str = include_str!("../descriptors/by-name/mina-accumulator-head.json");
const SRS_JSON: &str = include_str!("../descriptors/by-name/mina-accumulator-srs.json");
/// ⚑ The Lean-emitted NEGATIVE CONTROL: the same algebra, manifest and claim, declaring the devnet
/// GENESIS head instead of the block-539508 tip. Its whole job is to make the refusal isolating.
const HEAD_GENESIS_JSON: &str =
    include_str!("../descriptors/by-name/mina-accumulator-head-genesis.json");
/// ⚑ The program the seam's `vk_pin` NAMES — read as bytes, so the pin is a gate and not a literal.
const MINA_LC_JSON: &str =
    include_str!("../descriptors/by-name/dregg-mina-lightclient-verify-v1.json");

/// The honest head chain: `acc_0 = C = Σ s_r·G_r`, eight declared addends `−s_r·G_r`, terminal `O`,
/// the guard on at row 0 and off after, block 539508's nine tip lanes published.
const HEAD_TRACE: &str = include_str!("fixtures/mina-accumulator-head-trace.txt");

// -------------------------------------------------------------------------------------------
// Layout — every constant a mirror of a Lean name, none of them re-derived here.
// -------------------------------------------------------------------------------------------

const RCB_WIDTH: usize = 3048; // PastaCurveSound.RCB_WIDTH
const ROUTED_WIDTH: usize = RCB_WIDTH + 1; // MinaAccumulatorAir.ROUTED_WIDTH
const HEAD_OK: usize = ROUTED_WIDTH; // MinaAccumulatorAir.HEAD_OK           = 3049
const HEAD_STATE_0: usize = ROUTED_WIDTH + 1; // MinaAccumulatorAir.HEAD_STATE 0 = 3050
const HEAD_VK_0: usize = ROUTED_WIDTH + 10; // MinaAccumulatorAir.HEAD_VK 0     = 3059
const HEADED_WIDTH: usize = ROUTED_WIDTH + 19; // MinaAccumulatorAir.HEADED_WIDTH = 3068
const ROWS: usize = 8;
const SK: usize = 32; // PastaFieldSound.SK
const ACC: [usize; 3] = [0, SK, 2 * SK];
const OUT: [usize; 3] = [1024, 1120, 1216];
const HEAD_LANES: usize = 9;
const ACC_PI_COUNT: usize = 6 * SK; // 192
const HEAD_PI_COUNT: usize = ACC_PI_COUNT + HEAD_LANES; // 201
/// `-srs`'s 4 831 plus the twelve: guard-on, guard-off, nine pins, one `proof_bind`.
const HEAD_CONSTRAINTS: usize = 4476 + 96 + 192 + 64 + 3 + 12;

const HEAD_NAME: &str = "dregg-mina-accumulator-head::v1";
const SRS_NAME: &str = "dregg-mina-accumulator-srs::v1";
const MINA_LC_NAME: &str = "dregg-mina-lightclient-verify::v1";
const HEAD_GENESIS_NAME: &str = "dregg-mina-accumulator-head-genesis::v1";

/// `LightClientMinaAir.DEVNET_TIP_LANES` — devnet block **539508**'s state hash, the block whose
/// Wrap proof o1-labs' `kimchi::verifier::verify` accepts. This is the head the artifact declares.
const DEVNET_TIP_LANES: [u32; HEAD_LANES] = [
    148_400_356,
    2_288_994,
    332_868_807,
    237_767_070,
    530_455_789,
    507_531_490,
    336_317_945,
    425_818_875,
    3_793_778,
];

/// `LightClientMinaAir.GENESIS_ANCHOR_LANES` — devnet GENESIS's state hash. ⚑ A DIFFERENT REAL
/// Mina head, which is what the forgery substitutes. Using a real second head rather than an
/// invented number is what keeps the exhibit from being a falsifier that moved a magic constant.
const GENESIS_ANCHOR_LANES: [u32; HEAD_LANES] = [
    317_368_465,
    122_552_485,
    518_650_043,
    481_937_944,
    112_457_995,
    488_503_206,
    390_747_624,
    350_427_965,
    1_320_595,
];

// -------------------------------------------------------------------------------------------
// Readers.
// -------------------------------------------------------------------------------------------

fn descriptor(json: &str) -> EffectVmDescriptor2 {
    parse_vm_descriptor2(json).expect("the STRICT deployed checker parses the AIR")
}

fn trace(text: &str, width: usize) -> Vec<Vec<BabyBear>> {
    let rows: Vec<Vec<BabyBear>> = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            let cells: Vec<BabyBear> = l
                .split_whitespace()
                .map(|c| {
                    BabyBear::new(
                        u32::try_from(c.parse::<u64>().expect("decimal cell"))
                            .expect("cell inside BabyBear"),
                    )
                })
                .collect();
            assert_eq!(cells.len(), width, "every row is exactly {width} wide");
            cells
        })
        .collect();
    assert_eq!(rows.len(), ROWS, "the base trace is {ROWS} rows");
    rows
}

/// The 3 049-wide narrowing of a head trace — literally the `-srs` rail's row, since the head seam
/// APPENDS. This is what makes the old-admits pole the previous rung's own descriptor rather than a
/// second fixture.
fn narrow(t: &[Vec<BabyBear>]) -> Vec<Vec<BabyBear>> {
    t.iter().map(|r| r[..ROUTED_WIDTH].to_vec()).collect()
}

/// PIs are READ OFF the trace, never authored: row 0's three `ACC` blocks, row 7's three `OUT`
/// blocks, then row 0's nine head lanes.
fn public_inputs(t: &[Vec<BabyBear>], with_head: bool) -> Vec<BabyBear> {
    let mut pis = Vec::with_capacity(HEAD_PI_COUNT);
    for base in ACC {
        for i in 0..SK {
            pis.push(t[0][base + i]);
        }
    }
    for base in OUT {
        for i in 0..SK {
            pis.push(t[ROWS - 1][base + i]);
        }
    }
    assert_eq!(pis.len(), ACC_PI_COUNT);
    if with_head {
        for i in 0..HEAD_LANES {
            pis.push(t[0][HEAD_STATE_0 + i]);
        }
        assert_eq!(pis.len(), HEAD_PI_COUNT);
    }
    pis
}

/// `Faithful9::from_key_lanes9` — 32 bytes as one little-endian 256-bit number in NINE base-`2^29`
/// digits. Same decomposition `circuit/examples/conj_fingerprint.rs` prints and
/// `mina_head_verifier::check_subproof_program_pin` recomputes at verify time.
fn key_lanes9(bytes: &[u8; 32]) -> [i64; HEAD_LANES] {
    let mut acc = [0i64; HEAD_LANES];
    let mut cur: u128 = 0;
    let mut bits = 0u32;
    let mut out = 0usize;
    for b in bytes.iter() {
        cur |= u128::from(*b) << bits;
        bits += 8;
        while bits >= 29 && out < 8 {
            acc[out] = i64::try_from(cur & ((1u128 << 29) - 1)).unwrap();
            cur >>= 29;
            bits -= 29;
            out += 1;
        }
    }
    acc[8] = i64::try_from(cur).unwrap();
    acc
}

/// The descriptor's one `proof_bind`, resolved by SHAPE and refused if there is more than one —
/// `reference-a-display-name-is-not-a-key`, one rail down: "the seam" must not be ambiguous.
fn the_seam(d: &EffectVmDescriptor2) -> &dregg_circuit::descriptor_ir2::ProofBindSpec {
    let binds: Vec<_> = d
        .constraints
        .iter()
        .filter_map(|c| match c {
            VmConstraint2::ProofBind(m) => Some(m),
            _ => None,
        })
        .collect();
    assert_eq!(
        binds.len(),
        1,
        "the head descriptor must carry exactly one proof_bind; found {}",
        binds.len()
    );
    binds[0]
}

/// A `bound` lane, as the literal it must be. A `Var` here would mean the seam compares a column to
/// another column, which is the decoration `MinaAccumulatorAir` §11 argues against.
fn bound_const(e: &LeanExpr) -> i64 {
    match e {
        LeanExpr::Const(c) => *c,
        other => panic!("a bound lane is not a literal: {other:?}"),
    }
}

fn prove_and_verify_adversarial(
    d: &EffectVmDescriptor2,
    t: &[Vec<BabyBear>],
    pis: &[BabyBear],
) -> Result<(), String> {
    let proof = prove_vm_descriptor2_unchecked(d, t, pis, &MemBoundaryWitness::default(), &[])?;
    verify_vm_descriptor2(d, &proof, pis)
}

// -------------------------------------------------------------------------------------------
// §1 — SHAPE. What this file reads is what the artifact declares.
// -------------------------------------------------------------------------------------------

#[test]
fn the_head_artifact_declares_what_this_file_reads() {
    let d = descriptor(HEAD_JSON);
    assert_eq!(d.name, HEAD_NAME);
    assert_eq!(d.trace_width, HEADED_WIDTH);
    assert_eq!(d.public_input_count, HEAD_PI_COUNT);
    assert_eq!(d.constraints.len(), HEAD_CONSTRAINTS);

    let seam = the_seam(&d);
    assert_eq!(seam.commit.len(), HEAD_LANES + 3 * SK, "105 commit lanes");
    assert_eq!(seam.vk.len(), HEAD_LANES);
    assert!(!seam.is_declarative(), "the seam pins BOTH halves");
    assert!(seam.vk_pin.is_some() && seam.bound.is_some());
    seam.width_ok().expect("the seam clears both lane floors");
    println!(
        "-head: {HEADED_WIDTH} cols, {HEAD_CONSTRAINTS} constraints, {} commit lanes, {} vk lanes",
        seam.commit.len(),
        seam.vk.len()
    );
}

/// ⚑ **THE SEAM NAMES THE COLUMNS §11 SAYS IT NAMES.** `commit` is the nine head columns then the
/// ninety-six accumulator columns; `vk` is the nine program columns; the guard is `HEAD_OK`. Read
/// off the EMITTED bytes, so a column-index drift in Lean goes red here rather than producing a
/// descriptor that constrains the wrong cells while every count still matches.
#[test]
fn the_seam_names_the_head_columns_and_the_accumulator_columns() {
    let d = descriptor(HEAD_JSON);
    let seam = the_seam(&d);

    assert_eq!(seam.guard, LeanExpr::Var(HEAD_OK));
    for i in 0..HEAD_LANES {
        assert_eq!(seam.commit[i], LeanExpr::Var(HEAD_STATE_0 + i));
        assert_eq!(seam.vk[i], LeanExpr::Var(HEAD_VK_0 + i));
    }
    for j in 0..3 * SK {
        assert_eq!(
            seam.commit[HEAD_LANES + j],
            LeanExpr::Var(ACC[0] + j),
            "commit lane {} is not accumulator column {j}",
            HEAD_LANES + j
        );
    }
}

// -------------------------------------------------------------------------------------------
// §2 — ⚑⚑ THE PROGRAM PIN IS A GATE, NOT A LITERAL.
// -------------------------------------------------------------------------------------------

/// ⚑⚑ **THE PINNED PROGRAM IS THE SERVED HEAD DESCRIPTOR.** The nine `vk_pin` lanes are recomputed
/// here from `dregg-mina-lightclient-verify-v1.json`'s OWN bytes — blake3 semantic fingerprint,
/// then `Faithful9` key lanes — and compared against what Lean wrote.
///
/// ⚠ This test exists because `75df624cf` re-emitted a descriptor and left a `vkPin` naming a
/// program no descriptor in this tree had. A pin whose only reader is prose is a pin a re-emit
/// drifts past.
#[test]
fn the_pinned_head_program_is_the_served_head_descriptor() {
    let lc = descriptor(MINA_LC_JSON);
    assert_eq!(lc.name, MINA_LC_NAME);

    let fp = effect_vm_descriptor2_semantic_fingerprint(&lc)
        .expect("the head descriptor is fingerprint-representable");
    let want = key_lanes9(&fp);

    let d = descriptor(HEAD_JSON);
    let pin = the_seam(&d)
        .vk_pin
        .as_ref()
        .expect("the seam pins its program");
    assert_eq!(pin.len(), HEAD_LANES);
    assert_eq!(
        pin.as_slice(),
        want.as_slice(),
        "MINA_HEAD_VK_LANES does not name {MINA_LC_NAME}'s fingerprint — re-emitting that \
         descriptor moves this literal and re-VKs -head; run `cargo run -p dregg-circuit \
         --release --example conj_fingerprint -- circuit/descriptors/by-name/\
         dregg-mina-lightclient-verify-v1.json`"
    );
    println!(
        "vk_pin = fingerprint({MINA_LC_NAME}) = {}",
        fp.iter().map(|b| format!("{b:02x}")).collect::<String>()
    );
}

/// ⚑ **THE DECLARED HEAD IS THE LIGHT CLIENT'S DEVNET TIP** — the `bound` block's first nine lanes
/// are block 539508's state hash lanes, the same value `LightClientMinaAir.DEVNET_TIP_LANES`
/// carries and `honest_tip_lanes_decode_the_devnet_block` pins against the decimal. Two spellings,
/// one value; a drift in either goes red here.
#[test]
fn the_declared_head_is_the_light_clients_devnet_tip() {
    let d = descriptor(HEAD_JSON);
    let bound = the_seam(&d)
        .bound
        .as_ref()
        .expect("the seam bounds its commitment");
    assert_eq!(bound.len(), HEAD_LANES + 3 * SK);

    for i in 0..HEAD_LANES {
        assert_eq!(
            bound_const(&bound[i]),
            i64::from(DEVNET_TIP_LANES[i]),
            "declared head lane {i} is not block 539508's"
        );
    }
    assert_ne!(
        DEVNET_TIP_LANES, GENESIS_ANCHOR_LANES,
        "the two exhibited heads must differ or the falsifier moves nothing"
    );
}

/// ⚑ **AND THE DECLARED CLAIM IS THE TRACE'S ENTRY ACCUMULATOR** — the `bound` block's remaining 96
/// lanes are the honest chain's `acc_0` limbs, so the artifact and the fixture cannot drift into
/// two different claims while every count still matches.
#[test]
fn the_declared_claim_is_the_honest_chains_entry_accumulator() {
    let d = descriptor(HEAD_JSON);
    let bound = the_seam(&d).bound.as_ref().expect("bound");
    let t = trace(HEAD_TRACE, HEADED_WIDTH);

    let mut nonzero = 0usize;
    for j in 0..3 * SK {
        let declared = bound_const(&bound[HEAD_LANES + j]);
        let witnessed = i64::from(t[0][ACC[0] + j].as_u32());
        assert_eq!(
            declared, witnessed,
            "declared claim limb {j} is not the trace's"
        );
        assert!(
            (0..256).contains(&declared),
            "claim limb {j} is not an 8-bit digit"
        );
        if declared != 0 {
            nonzero += 1;
        }
    }
    assert!(
        nonzero > 0,
        "every declared claim limb is zero — the claim is the all-zero point"
    );
    println!("96 declared claim limbs match the trace, {nonzero} of them nonzero");
}

// -------------------------------------------------------------------------------------------
// §3 — ⚑ THE POLARITIES.
// -------------------------------------------------------------------------------------------

/// The honest head chain proves. Both rails: the adversarial one (so the teeth below are measured
/// against a prover that CAN emit a bad trace) and the checked one.
#[test]
fn the_head_chain_proves() {
    let d = descriptor(HEAD_JSON);
    let t = trace(HEAD_TRACE, HEADED_WIDTH);
    let pis = public_inputs(&t, true);

    prove_and_verify_adversarial(&d, &t, &pis).expect("the honest head chain proves and verifies");

    let proof = prove_vm_descriptor2(&d, &t, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the honest head chain passes the producer pre-flight");
    verify_vm_descriptor2(&d, &proof, &pis).expect("…and verifies");
}

/// ⚑⚑⚑ **THE TOOTH — A CLAIM THAT DISCHARGES HONESTLY AND BELONGS TO A DIFFERENT HEAD.**
///
/// The honest chain with the devnet GENESIS anchor's nine lanes in place of block 539508's tip.
/// Every row is a genuine sound RCB row; the threads hold; the index is threaded; the addends are
/// the descriptor's own declared `−s_r·G_r`; the accumulator vanishes; `PI[0..191]` is
/// byte-identical. **The only thing wrong with it is the head it says the claim belongs to.**
///
/// ⚠ It is refused by a CONSTRAINT, and the assertion says so: a bus verdict here would mean the
/// routing caught it and the seam was never exercised.
///
/// ⚠ And it is the AIR's refusal, not a producer assert: the trace goes in through
/// `prove_vm_descriptor2_unchecked`, which bypasses `build_traces`' replay entirely.
#[test]
fn the_wrong_head_claim_is_refused_by_the_air() {
    let d = descriptor(HEAD_JSON);
    let honest = trace(HEAD_TRACE, HEADED_WIDTH);
    let mut forged = honest.clone();

    // ⚑ CONSTRUCTIVE, and the mutation is asserted BEFORE the verdict is read.
    let mut moved = 0usize;
    for r in 0..ROWS {
        for i in 0..HEAD_LANES {
            let before = forged[r][HEAD_STATE_0 + i].as_u32();
            let after = GENESIS_ANCHOR_LANES[i];
            forged[r][HEAD_STATE_0 + i] = BabyBear::new(after);
            if before != after {
                assert!(
                    before != 0 && after != 0,
                    "a head lane moved a zero into a zero"
                );
                moved += 1;
            }
        }
    }
    assert!(
        moved > 0,
        "the substitution did not move a single head lane"
    );

    // The forged PIs are READ OFF the forged trace, so the pi_binding still holds and the seam is
    // the only thing that can refuse.
    let pis = public_inputs(&forged, true);
    let honest_pis = public_inputs(&honest, true);
    assert_eq!(
        pis[..ACC_PI_COUNT],
        honest_pis[..ACC_PI_COUNT],
        "the two traces must publish the SAME claim and the SAME discharge"
    );
    assert_ne!(pis[ACC_PI_COUNT..], honest_pis[ACC_PI_COUNT..]);

    let what = "a discharging claim published against a different head, under -head";
    let refusal =
        must_refuse_or_unsat_panic(what, || prove_and_verify_adversarial(&d, &forged, &pis));
    let reason = refusal.reason();
    assert_violated_constraint_not_bus(what, &reason);
    println!("{moved} head lanes moved; refused by: {reason}");
}

/// ⚑ **THE OLD-ADMITS POLE.** The SAME forged chain, narrowed to `-srs`'s 3 049 columns, PROVES —
/// because `-srs` has no head seam at all. A pair that cannot rot into agreement is the exhibit;
/// without this half the tooth above could be measuring a broken fixture.
#[test]
fn the_wrong_head_chain_still_proves_under_the_headless_descriptor() {
    let srs = descriptor(SRS_JSON);
    assert_eq!(srs.name, SRS_NAME);
    assert_eq!(srs.trace_width, ROUTED_WIDTH);

    let mut forged = trace(HEAD_TRACE, HEADED_WIDTH);
    for r in 0..ROWS {
        for i in 0..HEAD_LANES {
            forged[r][HEAD_STATE_0 + i] = BabyBear::new(GENESIS_ANCHOR_LANES[i]);
        }
    }
    let narrowed = narrow(&forged);
    let pis = public_inputs(&narrowed, false);
    assert_eq!(pis.len(), ACC_PI_COUNT);

    prove_and_verify_adversarial(&srs, &narrowed, &pis)
        .expect("the wrong-head chain proves under -srs, which does not carry the seam");
}

/// ⚑ **THE SEAM CANNOT BE SWITCHED OFF FOR ONE FELT.** `ProofBind.boundAt` is guarded, so a free
/// guard column would let a prover zero it and evaporate the whole obligation — the vacuity
/// `LightClientMinaLinkAir` names. `headOkOnLeg` forces `HEAD_OK = 1` on the first row, and this is
/// the exhibit that it is a real gate.
#[test]
fn the_unguarded_head_row_is_refused() {
    let d = descriptor(HEAD_JSON);
    let mut forged = trace(HEAD_TRACE, HEADED_WIDTH);

    let before = forged[0][HEAD_OK].as_u32();
    assert_eq!(before, 1, "the honest guard is on at the first row");
    forged[0][HEAD_OK] = BabyBear::new(0);
    let pis = public_inputs(&forged, true);

    let what = "the head seam switched off by zeroing its guard";
    let refusal =
        must_refuse_or_unsat_panic(what, || prove_and_verify_adversarial(&d, &forged, &pis));
    assert_violated_constraint_not_bus(what, &refusal.reason());
    println!("guard 1 -> 0 refused by: {}", refusal.reason());
}

/// ⚑ **A FORGED PROGRAM LANE IS REFUSED** — the `vkPin` congruence. This is what makes the head
/// descriptor's identity part of THESE bytes: a `-head` proof cannot attest to a sub-proof of some
/// other program. `forged_program_refused` one rail over is the same exhibit.
#[test]
fn the_forged_head_program_is_refused() {
    let d = descriptor(HEAD_JSON);
    let pin = the_seam(&d)
        .vk_pin
        .clone()
        .expect("the seam pins its program");
    let mut forged = trace(HEAD_TRACE, HEADED_WIDTH);

    let before = forged[0][HEAD_VK_0 + 3].as_u32();
    assert_eq!(
        i64::from(before),
        pin[3],
        "the honest trace carries the pinned program lane"
    );
    let after = before + 1;
    assert!(
        after != 0 && after < (1 << 29),
        "the bump stays a legal lane"
    );
    forged[0][HEAD_VK_0 + 3] = BabyBear::new(after);
    let pis = public_inputs(&forged, true);

    let what = "a head-program lane bumped by one";
    let refusal =
        must_refuse_or_unsat_panic(what, || prove_and_verify_adversarial(&d, &forged, &pis));
    assert_violated_constraint_not_bus(what, &refusal.reason());
}

// -------------------------------------------------------------------------------------------
// §4 — FALSIFIER HYGIENE. What moved, that it is nonzero, and that no range check can be it.
// -------------------------------------------------------------------------------------------

/// ⚑ The head lanes carry NO range lookup and need none: the seam's congruence pins each of them to
/// an exact declared value, which is strictly stronger than a width bound — *"a width bound is a
/// fact about a value's SHAPE; it is not a tie to the evidence."* This test is what makes
/// "no range lookup can be the refusal" a measurement rather than an assertion: no declared table
/// tuple mentions a head column at all.
#[test]
fn no_lookup_reads_a_head_column() {
    let d = descriptor(HEAD_JSON);
    let head_cols: Vec<usize> = (HEAD_OK..HEADED_WIDTH).collect();

    fn mentions(e: &LeanExpr, cols: &[usize]) -> bool {
        match e {
            LeanExpr::Var(c) => cols.contains(c),
            LeanExpr::Const(_) => false,
            LeanExpr::Add(a, b) | LeanExpr::Mul(a, b) => mentions(a, cols) || mentions(b, cols),
        }
    }

    for c in &d.constraints {
        if let VmConstraint2::Lookup(l) = c {
            for e in &l.tuple {
                assert!(
                    !mentions(e, &head_cols),
                    "a lookup tuple reads a head-seam column; a range refusal could then be \
                     mistaken for the seam's"
                );
            }
        }
    }
    println!("no declared lookup tuple mentions columns {HEAD_OK}..{HEADED_WIDTH}");
}

/// ⚑ The moved values are inside their declared BabyBear lane widths on BOTH sides — lanes 0..=7
/// below `2^29` and lane 8 below `2^24` — so the exhibit is not a falsifier that pushed a value out
/// of range and got refused for the wrong reason.
#[test]
fn both_exhibited_heads_are_legal_faithful9_lanes() {
    for (name, lanes) in [
        ("block 539508 tip", DEVNET_TIP_LANES),
        ("devnet genesis anchor", GENESIS_ANCHOR_LANES),
    ] {
        for (i, v) in lanes.iter().enumerate() {
            let bound = if i < 8 { 1u32 << 29 } else { 1u32 << 24 };
            assert!(
                *v < bound,
                "{name} lane {i} = {v} is not a legal Faithful9 lane"
            );
            assert!(*v != 0, "{name} lane {i} is zero");
        }
    }
}

/// ⚑ The guard is a bit and it is on exactly once: `1` at row 0 and `0` at every successor. That
/// shape is what makes the seam's off-row obligation the FIRST ROW's — one sentence, not eight.
#[test]
fn the_guard_is_on_exactly_at_the_first_row() {
    let t = trace(HEAD_TRACE, HEADED_WIDTH);
    assert_eq!(t[0][HEAD_OK].as_u32(), 1);
    for r in 1..ROWS {
        assert_eq!(
            t[r][HEAD_OK].as_u32(),
            0,
            "the guard is set at row {r}, which re-arms the per-row obligation"
        );
    }
}

/// ⚑ The head rail is `-srs` plus an APPENDIX: narrowing the honest head trace to 3 049 columns and
/// proving under `-srs` must succeed, which is what says the twelve constraints are additive and
/// that `-head` did not silently re-author the routing.
#[test]
fn the_honest_head_chain_narrows_to_the_srs_chain() {
    let srs = descriptor(SRS_JSON);
    let t = trace(HEAD_TRACE, HEADED_WIDTH);
    let narrowed = narrow(&t);
    let pis = public_inputs(&narrowed, false);
    prove_and_verify_adversarial(&srs, &narrowed, &pis)
        .expect("the honest head chain, narrowed, is an honest -srs chain");
}

// -------------------------------------------------------------------------------------------
// §5 — ⚑⚑ THE ISOLATION, MEASURED. "Refused by the proof_bind and by nothing else" is a claim,
// and this is where it stops being one.
// -------------------------------------------------------------------------------------------

/// ⚑⚑ **THE CONTROL DIFFERS FROM THE ARTIFACT IN ONE CONSTRAINT AND NINE LANES.** Both are
/// Lean-emitted from `MinaAccumulatorAir.accHeadDescNamed` at the SAME manifest and the SAME claim;
/// the only input that differs is the declared head. Measured on the bytes: same width, same PI
/// count, same constraint count, same tables — and exactly one differing constraint, which is the
/// `proof_bind`, differing in exactly the nine head `bound` lanes.
///
/// ⚠ Emitted, not assembled: editing a parsed descriptor's `bound` in Rust would be Rust authoring
/// AIR. Same reason `mina-wrap-conjunction-unthreaded.json` exists as an artifact.
#[test]
fn the_control_differs_from_the_artifact_in_nine_lanes() {
    let d = descriptor(HEAD_JSON);
    let c = descriptor(HEAD_GENESIS_JSON);

    assert_eq!(c.name, HEAD_GENESIS_NAME);
    assert_ne!(c.name, d.name);
    assert_eq!(c.trace_width, d.trace_width);
    assert_eq!(c.public_input_count, d.public_input_count);
    assert_eq!(c.constraints.len(), d.constraints.len());
    assert_eq!(
        c.tables.iter().map(|t| t.id).collect::<Vec<_>>(),
        d.tables.iter().map(|t| t.id).collect::<Vec<_>>()
    );

    let differing: Vec<usize> = d
        .constraints
        .iter()
        .zip(c.constraints.iter())
        .enumerate()
        .filter_map(|(i, (a, b))| if a == b { None } else { Some(i) })
        .collect();
    assert_eq!(
        differing.len(),
        1,
        "the control must differ in exactly one constraint; it differs in {differing:?}"
    );
    assert!(
        matches!(d.constraints[differing[0]], VmConstraint2::ProofBind(_)),
        "the one differing constraint is not the proof_bind"
    );

    let a = the_seam(&d);
    let b = the_seam(&c);
    assert_eq!(a.guard, b.guard);
    assert_eq!(a.commit, b.commit);
    assert_eq!(a.vk, b.vk);
    assert_eq!(a.vk_pin, b.vk_pin, "both name the SAME head program");

    let ab = a.bound.as_ref().expect("bound");
    let bb = b.bound.as_ref().expect("bound");
    assert_eq!(ab.len(), bb.len());
    let lanes: Vec<usize> = (0..ab.len()).filter(|&i| ab[i] != bb[i]).collect();
    assert_eq!(
        lanes,
        (0..HEAD_LANES).collect::<Vec<_>>(),
        "the two bound vectors must differ in exactly the nine HEAD lanes"
    );
    for i in 0..HEAD_LANES {
        assert_eq!(bound_const(&ab[i]), i64::from(DEVNET_TIP_LANES[i]));
        assert_eq!(bound_const(&bb[i]), i64::from(GENESIS_ANCHOR_LANES[i]));
    }
    println!(
        "control differs in constraint {} and in lanes {lanes:?}",
        differing[0]
    );
}

/// ⚑⚑⚑ **THE ISOLATING POLE.** The very trace the tooth above refuses PROVES under the descriptor
/// that DECLARES the head it publishes. Everything else about that trace — the routing, the
/// discharge, the threads, the PI pins, the guard, the program pin — is therefore fine, and the
/// nine head lanes of the seam's `bound` are the only thing that refused it.
#[test]
fn the_wrong_head_chain_proves_under_the_descriptor_that_declares_that_head() {
    let c = descriptor(HEAD_GENESIS_JSON);
    let mut forged = trace(HEAD_TRACE, HEADED_WIDTH);
    for r in 0..ROWS {
        for i in 0..HEAD_LANES {
            forged[r][HEAD_STATE_0 + i] = BabyBear::new(GENESIS_ANCHOR_LANES[i]);
        }
    }
    let pis = public_inputs(&forged, true);
    prove_and_verify_adversarial(&c, &forged, &pis)
        .expect("the genesis-head chain proves under the descriptor declaring the genesis head");
}

/// ⚑ …and the control is not accepting everything: the HONEST chain — block 539508's tip — is
/// REFUSED under it, by the same nine lanes in the other direction. A negative control that
/// accepted both poles would be measuring nothing.
#[test]
fn the_honest_chain_is_refused_under_the_control() {
    let c = descriptor(HEAD_GENESIS_JSON);
    let t = trace(HEAD_TRACE, HEADED_WIDTH);
    let pis = public_inputs(&t, true);

    let what = "the block-539508 head chain under the descriptor declaring the genesis head";
    let refusal = must_refuse_or_unsat_panic(what, || prove_and_verify_adversarial(&c, &t, &pis));
    assert_violated_constraint_not_bus(what, &refusal.reason());
}

/// ⚑ **THE COMMITTED WIDTH, NOT THE DECLARED ONE.** `MainLayout::build` extends the declared trace
/// with one aux block per declared RANGE lookup (`decomp_cols(bits)` columns each), so
/// `trace_width` is the shape a reader sees and the prover commits to something wider. Reported
/// here beside `-srs`'s, because the seam's cost is the DELTA and the delta is what a reader is
/// entitled to.
///
/// ⚑ The nineteen head columns carry NO range lookup (`no_lookup_reads_a_head_column`), so they
/// cost nineteen committed columns and not one aux block more.
#[test]
fn the_committed_width_is_reported_beside_the_declared_one() {
    fn committed(d: &EffectVmDescriptor2) -> usize {
        let range_bits = |tid: usize| -> Option<usize> {
            d.tables
                .iter()
                .find(|t| t.id == tid)
                .and_then(|t| match t.sem {
                    TableSem::Range { bits } => Some(bits),
                    _ => None,
                })
        };
        let mut w = d.trace_width;
        for c in &d.constraints {
            if let VmConstraint2::Lookup(l) = c {
                if let Some(bits) = range_bits(l.table) {
                    w += decomp_cols_pub(bits);
                }
            }
        }
        w
    }

    let head = descriptor(HEAD_JSON);
    let srs = descriptor(SRS_JSON);
    let (hc, sc) = (committed(&head), committed(&srs));

    assert_eq!(head.trace_width, HEADED_WIDTH);
    assert_eq!(srs.trace_width, ROUTED_WIDTH);
    assert_eq!(
        hc - sc,
        HEADED_WIDTH - ROUTED_WIDTH,
        "the seam's committed cost must be exactly its nineteen columns — a range lookup on a head \
         column would make this larger and would also make a range refusal indistinguishable from \
         the seam's"
    );
    println!(
        "-srs : declared {} / committed {sc}\n-head: declared {} / committed {hc}  (+{} columns, \
         +{:.3}%)",
        srs.trace_width,
        head.trace_width,
        hc - sc,
        100.0 * (hc - sc) as f64 / sc as f64
    );
}
