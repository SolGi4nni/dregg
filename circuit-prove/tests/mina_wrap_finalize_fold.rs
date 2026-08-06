//! ⚑⚑ **THE FINALIZE CONJUNCTION AND THE ENDOMORPHISM LIFT, FOLDED — ξ CARRIED INSIDE THE
//! RECURSION.**
//!
//! ## What was here before, and why it was not enough
//!
//! `circuit/tests/mina_xi_endo_weld.rs` proves both descriptors and then compares their published ξ
//! blocks **host-side**, elementwise, 32 felts. That is a real comparison and it is a comparison a
//! TEST makes: a prover who hands the conjunction some other ξ produces two proofs that both
//! verify, and only someone re-running that test notices. `MinaWrapXiEndoLift` §"THE WELD" says as
//! much — *"two separately emitted descriptors … one shared 32-felt boundary"*.
//!
//! This file folds them. `fold_endo_into_finalize` verifies both children in-circuit and
//! `cb.connect`s the 32 ξ limbs, so the boundary is a **constraint of a third proof**. A prover
//! whose conjunction reads a different ξ has no satisfying assignment in the aggregation circuit —
//! there is no root.
//!
//! ## ⚑ AND THIS IS WHAT MAKES `xiCorrect` MEAN ANYTHING AT ALL
//!
//! Read the conjunction AIR's ξ columns and the finding is sharp: `XI_SQ` and `XI_CL` appear in
//! **`eqBlock XI_SQ XI_CL`, in `globalThread`'s hold legs, and in the input range lookups — and
//! nowhere else.** No sound core consumes either. So `xiCorrect` on its own forces *"two free
//! columns of the prover's choosing agree"*, and a prover may run the entire b-polynomial fold at
//! any ξ whatsoever.
//!
//! The connect is what supplies the missing side: after the fold, `XI_CL` is the endo-lift's
//! OUTPUT, `xiCorrect` carries it to `XI_SQ`, and `xiCorrect` becomes *"the squeezed ξ is
//! `ScalarChallenge(v′).to_field(endo_r)`"*. That is not a decoration of the conjunction; it is the
//! conjunction's first conjunct acquiring content.
//!
//! ⚠ **Which is also why §3's falsifier is what it is.** Because ξ enters no gate, the honest trace
//! with BOTH ξ blocks moved to another value — in all sixteen rows, and in the PI vector — is a
//! fully satisfying, standalone-verifying conjunction leaf. §3 proves it standalone first, then
//! shows the FOLD refuses it. A falsifier that could not stand alone would leave the refusal
//! attributable to something else, and this campaign has shipped two of those.
//!
//! ## WHAT THE ROOT DOES **NOT** SAY — the four, named, not summarised
//!
//! 1. **Not that the Pickles proof is valid.** The IPA opening is not in circuit;
//!    `PastaIpaDeferral.opening_is_vacuous_when_sg_is_free` is a theorem that its closing check
//!    accepts at every value while `sg` is free.
//! 2. **Not finalize.** Upstream's is a FOUR-way AND with the opening; this is a **TWO-way** AND.
//!    `cipCorrect` and `plonkChecksPassed` are absent BY CONSTRUCTION (`MinaWrapConjunctionAir`
//!    §"WHAT THIS OBJECT FORCES"), because comparing `cip` against a ξ-fold with a free `ft_eval0`
//!    column forces nothing.
//! 3. **`v′` is published, not derived.** Tying it to the block's own Fq transcript is the 46-leaf
//!    chain fold's job (`mina_phase2_chain_fold.rs`, 1037 s); §4 exercises the seam's ARITHMETIC
//!    against the tracked link-45 vector and says plainly that it is not the in-circuit connect.
//! 4. **ζ, ζω and `r` are published and derived by nothing here.**
//!
//! ## ⚑ RELEASE, DELIBERATELY
//!
//! Algebraic refusals are `debug_assert` panics in debug and clean `Err(..)` in release. A refusal
//! test that passes only in debug is testing the assertion.
//!
//! ## ⚠ `--test-threads=1`, AND IT IS A MEASUREMENT, NOT A PRECAUTION
//!
//! Measured 2026-08-06 on a 96 GB box: wrapping a **2 536-column** leaf as a recursion layer peaks
//! around **15 GB RSS**, so §4's two folds run concurrently take ~30 GB — and with sibling lanes on
//! the same box the harness was **SIGKILL**ed (signal 9, an OOM kill, which reads as a test
//! *failure* and is an ENVIRONMENT fault). The six cheap tests are unaffected.
//!
//! ⚑ That number is also a real datum about in-AIR Pickles: the sound curve row is 3 048 columns,
//! *wider* than this conjunction, so a fold tower over it is memory-bound per node long before it is
//! row-bound.
//!
//! ## ⚠⚠ AND THE MEASURED TIMES CORRECT A PRICE I HAD JUST DERIVED — READ THIS BEFORE QUOTING CELLS
//!
//! Measured here, 2026-08-06: **endo-lift leaf 55.7 s (687 cols × 2 048 rows), conjunction leaf
//! 177.3 s (2 536 cols × 16 rows), fold node 48.0 s**, root verified. Against the phase-2 chain's
//! **9.5 s** for a 469-column × 2 048-row leaf.
//!
//! ⚑ **LEAF COST DOES NOT TRACK COMMITTED CELLS. IT TRACKS COLUMNS.** The conjunction leaf commits
//! `2 536 × 16 = 40 576` cells — **1/24th** of the chainlink leaf's `960 512` — and takes **18.7×
//! longer.** The recursion verifier opens every committed column at the out-of-domain point, so the
//! wrap circuit grows with the descriptor's WIDTH and barely notices its height.
//!
//! ⚠ So `MinaWrapVerifierAir` §5b's `WRAP_CELLS` is the right figure for WITNESS VOLUME and the
//! wrong one for wall clock, and an extrapolation from the chain fold's cells-per-second (which
//! would say ~45 min) is optimistic by roughly 3×. Extrapolating from THESE numbers instead — 17
//! curve leaves at 3 048 columns, 84 sponge leaves at 226, ~100 fold nodes — puts one in-AIR Wrap
//! verification at **a few hours on one box**, not minutes and not seasons. Both figures are
//! extrapolations; this one is at least extrapolating from the right variable, and it is stated so a
//! reader does not carry my cell-rate number forward.
//!
//! ```text
//! cargo test -p dregg-circuit-prove --release --test mina_wrap_finalize_fold -- --nocapture --test-threads=1
//! ```

use std::time::Instant;

use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::mina_wrap_finalize_fold::{
    CLAIM_B0, CLAIM_R, CLAIM_VPRIME, CLAIM_ZETA, CLAIM_ZETAW, CONJ_PI_B0, CONJ_PI_COUNT, CONJ_PI_R,
    CONJ_PI_XI, CONJ_PI_ZETA, CONJ_PI_ZETAW, CONJ_ROWS, ENDO_PI_COUNT, ENDO_PI_VPRIME, ENDO_PI_XI,
    FINALIZE_CLAIM_LEN, SK, V_PRIME_LIMBS, conjunction_descriptor, endo_lift_descriptor,
    finalize_config, fold_endo_into_finalize, prove_conjunction_leaf, prove_endo_lift_leaf,
    read_finalize_claim,
};
use dregg_circuit_prove::plonky3_recursion_impl::recursive::verify_recursive_batch_proof_with_config;

const ENDO_TRACE: &str = include_str!("../../circuit/tests/fixtures/mina-xi-endo-lift-trace.txt");
const ENDO_PIS: &str = include_str!("../../circuit/tests/fixtures/mina-xi-endo-lift-pis.txt");
const CONJ_TRACE: &str =
    include_str!("../../circuit/tests/fixtures/mina-wrap-conjunction-trace.txt");
const CONJ_PIS: &str = include_str!("../../circuit/tests/fixtures/mina-wrap-conjunction-pis.txt");

/// The two SOUND atoms the in-AIR Pickles price is denominated in. Served bytes, so the widths
/// `MinaWrapVerifierAir` §5b prices with have a source independent of its own layout arithmetic.
const RCB_THREAD_DESC: &str =
    include_str!("../../circuit/descriptors/by-name/pasta-pallas-rcb-thread.json");
const ALU_DESC: &str = include_str!("../../circuit/descriptors/by-name/pasta-alu-sound.json");

/// The 46 tracked chain-link PI vectors, one line per link, in chain order.
const CHAIN_PIS_ALL: &str = include_str!("../../circuit/tests/fixtures/pasta-fq-chainlink-pis.txt");
/// `MinaPhase2Chain.chainPins` is `in(3) ++ out(3) ++ absorbed(2)`, so outgoing lane 0 is block 3.
const CHAINLINK_OUT_LANE0_BLOCK: usize = 3;
const CHAINLINK_LINKS: usize = 46;

/// `MinaWrapOpeningGate.B0` — the `b0` `b0_is_the_b_polynomial` proves is
/// `bPoly CHAL ζ + r · bPoly CHAL ζω` on block 539508's own challenges.
const B0_DECIMAL: &str =
    "8959513835325565174995450957597499793792733131117505895288870852340268010913";
/// `MinaRealBlockGate.VV` — the block's polyscale ξ.
const XI_DECIMAL: &str =
    "8288233988205559029449525580974252420889527181759196726389788710191542809415";

// ────────────────────────────────────────────────────────────────────────────────────────────────
// fixtures
// ────────────────────────────────────────────────────────────────────────────────────────────────

fn parse_trace(text: &str, width: usize) -> Vec<Vec<BabyBear>> {
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
        t.iter().all(|r| r.len() == width),
        "every row is {width} wide"
    );
    t
}

fn parse_pis(text: &str) -> Vec<BabyBear> {
    text.split_whitespace()
        .map(|c| BabyBear::new(c.parse::<u32>().expect("PI is a u32 decimal")))
        .collect()
}

/// Recompose 32 little-endian base-`2^8` limbs into a decimal string, so a claim can be checked
/// against the block's own published scalar rather than against another fixture.
fn block_decimal(v: &[BabyBear], base: usize) -> String {
    let mut acc: Vec<u32> = vec![0];
    for i in (0..SK).rev() {
        let mut carry: u32 = v[base + i].as_u32();
        assert!(carry < 256, "a sound-encoded limb is a byte");
        for d in acc.iter_mut() {
            let x = *d * 256 + carry;
            *d = x % 10;
            carry = x / 10;
        }
        while carry > 0 {
            acc.push(carry % 10);
            carry /= 10;
        }
    }
    while acc.len() > 1 && *acc.last().unwrap() == 0 {
        acc.pop();
    }
    acc.iter()
        .rev()
        .map(|d| char::from(b'0' + *d as u8))
        .collect()
}

/// ⚑ **THE FALSIFIER.** The honest conjunction trace with BOTH ξ blocks (`XI_SQ` at column 0 and
/// `XI_CL` at column `SK`) moved to a different byte string, on EVERY row, and the PI vector moved
/// with them. Every gate of the descriptor still holds — `xiCorrect` compares the two blocks to
/// each other, the thread holds them, the range lookups see bytes — so this is an honest,
/// standalone-verifying leaf about a DIFFERENT ξ, which is exactly what the fold must refuse.
fn forge_xi(trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let bump = |c: BabyBear| BabyBear::new((c.as_u32() + 1) % 256);
    let mut t: Vec<Vec<BabyBear>> = trace.to_vec();
    for row in t.iter_mut() {
        for i in 0..SK {
            row[i] = bump(row[i]); // XI_SQ = blk 0
            row[SK + i] = bump(row[SK + i]); // XI_CL = blk 1
        }
    }
    let mut p: Vec<BabyBear> = pis.to_vec();
    for i in 0..SK {
        p[CONJ_PI_XI + i] = bump(p[CONJ_PI_XI + i]);
    }
    (t, p)
}

// ────────────────────────────────────────────────────────────────────────────────────────────────
// §0 — the shapes, and the fixtures are not empty.
// ────────────────────────────────────────────────────────────────────────────────────────────────

/// `include_str!` accepts a 0-byte file and yields `""`; a sibling in this cone reported success
/// against nothing for exactly that reason.
#[test]
fn no_fixture_is_empty_and_the_layouts_are_the_lean_ones() {
    for (label, text) in [
        ("endo trace", ENDO_TRACE),
        ("endo pis", ENDO_PIS),
        ("conjunction trace", CONJ_TRACE),
        ("conjunction pis", CONJ_PIS),
        ("chainlink pis", CHAIN_PIS_ALL),
    ] {
        assert!(!text.trim().is_empty(), "{label} is EMPTY");
    }

    let e = endo_lift_descriptor().expect("endo-lift descriptor");
    let c = conjunction_descriptor().expect("conjunction descriptor");
    assert_eq!(e.public_input_count, ENDO_PI_COUNT);
    assert_eq!(c.public_input_count, CONJ_PI_COUNT);
    assert_eq!(parse_pis(ENDO_PIS).len(), ENDO_PI_COUNT);
    assert_eq!(parse_pis(CONJ_PIS).len(), CONJ_PI_COUNT);
    assert_eq!(parse_trace(CONJ_TRACE, c.trace_width).len(), CONJ_ROWS);
    println!(
        "\n§0 endo {} PIs, conjunction {} PIs, {} rows",
        ENDO_PI_COUNT, CONJ_PI_COUNT, CONJ_ROWS
    );
}

/// ⚑ **THE TWO PUBLISHED ξ BLOCKS ALREADY AGREE, AND THAT IS THE POINT.** Host-side this is what
/// `mina_xi_endo_weld.rs` asserts. The fold below is what makes it a CONSTRAINT; this test is here
/// so that a future drift shows up as "the fixtures disagree" rather than as "the fold is UNSAT",
/// which are two very different diagnoses.
#[test]
fn the_two_emitted_xi_blocks_are_one_value_host_side() {
    let e = parse_pis(ENDO_PIS);
    let c = parse_pis(CONJ_PIS);
    for i in 0..SK {
        assert_eq!(
            e[ENDO_PI_XI + i].as_u32(),
            c[CONJ_PI_XI + i].as_u32(),
            "xi limb {i}: the endo-lift's output and the conjunction's claim are one value"
        );
    }
    assert_eq!(
        block_decimal(&c, CONJ_PI_XI),
        XI_DECIMAL,
        "and it is the block's own polyscale"
    );
    assert_eq!(block_decimal(&c, CONJ_PI_B0), B0_DECIMAL);
    // v' is 128 bits: the top 16 limbs of its 32-limb slot are zero.
    for i in V_PRIME_LIMBS..SK {
        assert_eq!(
            e[ENDO_PI_VPRIME + i].as_u32(),
            0,
            "v' limb {i} is above 2^128"
        );
    }
    println!("§1 32/32 xi limbs agree; v' occupies {V_PRIME_LIMBS} of {SK} limbs");
}

/// The falsifier MOVES VALUES — a mutation that is a no-op is this repo's named failure mode
/// (`minted-a-falsifier-that-stopped-falsifying`), and it has happened here twice.
#[test]
fn the_falsifier_actually_moves_the_xi() {
    let c = conjunction_descriptor().expect("conjunction descriptor");
    let t = parse_trace(CONJ_TRACE, c.trace_width);
    let p = parse_pis(CONJ_PIS);
    let (ft, fp) = forge_xi(&t, &p);

    let moved_cells: usize = t
        .iter()
        .zip(ft.iter())
        .map(|(a, b)| a.iter().zip(b.iter()).filter(|(x, y)| x != y).count())
        .sum();
    let moved_pis = p.iter().zip(fp.iter()).filter(|(x, y)| x != y).count();
    assert_eq!(moved_cells, 2 * SK * CONJ_ROWS, "both xi blocks, every row");
    assert_eq!(moved_pis, SK, "and the published xi block");
    assert_ne!(block_decimal(&fp, CONJ_PI_XI), XI_DECIMAL);
    // Every forged cell is still a legal 8-bit limb, so no RANGE lookup can be the refusal.
    assert!(
        ft.iter()
            .all(|r| r[..2 * SK].iter().all(|c| c.as_u32() < 256))
    );
    // …and the four blocks the fold republishes are UNTOUCHED, so the refusal cannot be theirs.
    for base in [CONJ_PI_ZETA, CONJ_PI_ZETAW, CONJ_PI_R, CONJ_PI_B0] {
        for i in 0..SK {
            assert_eq!(p[base + i], fp[base + i]);
        }
    }
    println!("§2 falsifier moves {moved_cells} cells + {moved_pis} PIs, all inside the limb width");
}

/// ⚑ **AND THE FALSIFIER STANDS ALONE.** The forged leaf proves and verifies against the deployed
/// `prove_vm_descriptor2` — so when the fold refuses it below, the refusal is the CONNECT and
/// cannot be the conjunction's own gates.
#[test]
fn the_forged_xi_leaf_proves_and_verifies_on_its_own() {
    let d = conjunction_descriptor().expect("conjunction descriptor");
    let t = parse_trace(CONJ_TRACE, d.trace_width);
    let p = parse_pis(CONJ_PIS);
    let (ft, fp) = forge_xi(&t, &p);
    let proof = prove_vm_descriptor2(&d, &ft, &fp, &MemBoundaryWitness::default(), &[])
        .expect("a conjunction trace at ANY xi satisfies every gate — xi enters no sound core");
    verify_vm_descriptor2(&d, &proof, &fp).expect("and it verifies");
    println!("§3 the forged-xi conjunction leaf PROVES and VERIFIES standalone");
}

// ────────────────────────────────────────────────────────────────────────────────────────────────
// §4 — BOTH POLARITIES OF THE FOLD. Release.
// ────────────────────────────────────────────────────────────────────────────────────────────────

/// ⚑ **POLARITY 1 — THE FOLD LANDS, AND THE ROOT VERIFIES.**
#[test]
fn the_endo_and_the_conjunction_fold_into_one_claim() {
    let cfg = finalize_config();
    let ed = endo_lift_descriptor().expect("endo-lift descriptor");
    let cd = conjunction_descriptor().expect("conjunction descriptor");

    let t0 = Instant::now();
    let endo = prove_endo_lift_leaf(
        &parse_trace(ENDO_TRACE, ed.trace_width),
        &parse_pis(ENDO_PIS),
        &cfg,
    )
    .expect("the endo-lift leaf");
    let t_endo = t0.elapsed();

    let t1 = Instant::now();
    let conj = prove_conjunction_leaf(
        &parse_trace(CONJ_TRACE, cd.trace_width),
        &parse_pis(CONJ_PIS),
        &cfg,
    )
    .expect("the conjunction leaf");
    let t_conj = t1.elapsed();

    let t2 = Instant::now();
    let root = fold_endo_into_finalize(&endo, &conj, &cfg).expect("the honest fold lands");
    let t_fold = t2.elapsed();

    verify_recursive_batch_proof_with_config(&root.0, &cfg).expect("the fold root verifies");

    let claim = read_finalize_claim(&root).expect("the root publishes the finalize claim");
    assert_eq!(claim.len(), FINALIZE_CLAIM_LEN);

    // The root's `b0` is the block's own, and its `v'` is the endo-lift's published prechallenge.
    assert_eq!(block_decimal(&claim, CLAIM_B0), B0_DECIMAL);
    let e = parse_pis(ENDO_PIS);
    for i in 0..SK {
        assert_eq!(
            claim[CLAIM_VPRIME + i].as_u32(),
            e[ENDO_PI_VPRIME + i].as_u32()
        );
    }
    // …and the three published evaluation scalars are the conjunction's own.
    let c = parse_pis(CONJ_PIS);
    for (cl, cj) in [
        (CLAIM_ZETA, CONJ_PI_ZETA),
        (CLAIM_ZETAW, CONJ_PI_ZETAW),
        (CLAIM_R, CONJ_PI_R),
    ] {
        for i in 0..SK {
            assert_eq!(claim[cl + i].as_u32(), c[cj + i].as_u32());
        }
    }
    // ⚑ xi is NOT republished — it is an internal wire of the aggregation now.
    println!(
        "\n§4 POLARITY 1 — endo leaf {:.1}s + conjunction leaf {:.1}s + fold {:.1}s, root VERIFIED, \
         {FINALIZE_CLAIM_LEN} claim lanes",
        t_endo.as_secs_f64(),
        t_conj.as_secs_f64(),
        t_fold.as_secs_f64()
    );
}

/// ⚑⚑ **POLARITY 2 — AND A CONJUNCTION AT ANOTHER ξ HAS NO ROOT.**
///
/// **The refusing gate, named:** the 32 `CircuitBuilder::connect(endo.xi[i], conj.xi[i])` calls in
/// `mina_wrap_finalize_fold::fold_endo_into_finalize`. Nothing else can refuse this pair — both
/// leaves prove and verify on their own (`the_forged_xi_leaf_proves_and_verifies_on_its_own`), the
/// forged cells are legal limbs, and the four republished blocks are untouched.
#[test]
fn a_conjunction_at_another_xi_cannot_be_folded() {
    let cfg = finalize_config();
    let ed = endo_lift_descriptor().expect("endo-lift descriptor");
    let cd = conjunction_descriptor().expect("conjunction descriptor");

    let endo = prove_endo_lift_leaf(
        &parse_trace(ENDO_TRACE, ed.trace_width),
        &parse_pis(ENDO_PIS),
        &cfg,
    )
    .expect("the endo-lift leaf");

    let (ft, fp) = forge_xi(
        &parse_trace(CONJ_TRACE, cd.trace_width),
        &parse_pis(CONJ_PIS),
    );
    let conj = prove_conjunction_leaf(&ft, &fp, &cfg)
        .expect("the forged leaf is honest in its own right and wraps as a leaf");

    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        fold_endo_into_finalize(&endo, &conj, &cfg)
    }));
    let refused = match r {
        Err(_) => true,
        Ok(Ok(_)) => false,
        Ok(Err(_)) => true,
    };
    assert!(
        refused,
        "an endo-lift publishing xi and a conjunction reading a DIFFERENT xi must have no \
         satisfying assignment in the aggregation circuit — the 32 `connect`s are what refuse them"
    );
    println!("§4 POLARITY 2 — the forged-xi pair is REFUSED by the 32 xi connects");
}

// ────────────────────────────────────────────────────────────────────────────────────────────────
// §5 — the third leg, stated at the resolution it actually has.
// ────────────────────────────────────────────────────────────────────────────────────────────────

/// ⚑ **THE `v′` SEAM IS ARITHMETICALLY AVAILABLE AND IT IS NOT YET A CONNECT.**
///
/// `MinaPhase2Chain.the_chain_ends_at_the_blocks_challenges`: the 46-link fold root's outgoing lane
/// 0, low 128 bits, IS the block's `v′`. This asserts that against the TRACKED link-45 PI vector —
/// the same bytes `mina_xi_endo_weld.rs` welds — so the seam's arithmetic is checked and its
/// absence from the circuit is stated rather than implied.
///
/// ⚠ **This is a HOST assertion.** Making it a constraint is `connect_chain_root_v_prime`, and it
/// needs a chain-fold ROOT, which is 46 leaves and 45 folds (measured 1037 s in
/// `mina_phase2_chain_fold.rs` §5). Until a caller runs that fold and passes its root here, the
/// finalize root's `v′` is a prover-chosen 128-bit value.
#[test]
fn the_chain_roots_v_prime_is_the_endo_lifts_input_but_only_host_side() {
    let lines: Vec<&str> = CHAIN_PIS_ALL
        .lines()
        .filter(|l| !l.trim().is_empty())
        .collect();
    assert_eq!(
        lines.len(),
        CHAINLINK_LINKS,
        "the tracked chain-link PI aggregate is {CHAINLINK_LINKS} lines; re-emit it rather than \
         reading a truncated chain"
    );
    let last = parse_pis(lines[CHAINLINK_LINKS - 1]);
    let out_lane0 = CHAINLINK_OUT_LANE0_BLOCK * SK;
    let e = parse_pis(ENDO_PIS);

    for i in 0..V_PRIME_LIMBS {
        assert_eq!(
            last[out_lane0 + i].as_u32(),
            e[ENDO_PI_VPRIME + i].as_u32(),
            "v' limb {i}: the chain's terminal squeeze is the endo-lift's input"
        );
    }
    // …and the seam's SECOND half, without which "low 128 bits" is not what a connect would say.
    for i in V_PRIME_LIMBS..SK {
        assert_eq!(e[ENDO_PI_VPRIME + i].as_u32(), 0);
    }
    println!(
        "§5 v' seam checked HOST-SIDE over {V_PRIME_LIMBS} limbs + {} zero limbs — NOT a connect",
        SK - V_PRIME_LIMBS
    );
}

// ────────────────────────────────────────────────────────────────────────────────────────────────
// §6 — the atom widths the RE-DERIVED price is denominated in, from the SERVED bytes.
// ────────────────────────────────────────────────────────────────────────────────────────────────

/// ⚑ **THE PRICE'S TWO ATOMS, MEASURED ON THE ARTIFACTS.**
///
/// `MinaWrapVerifierAir` §5b re-prices one in-AIR Wrap verification at **144 751 608 committed
/// cells** — `34 816` sound complete additions at `3 048` columns plus `170 940` sound ALU rows at
/// `226`. Those two widths are the whole re-derivation, and in Lean they come from the AIRs' own
/// allocators. This asserts them against the SERVED descriptors, which is the other source.
///
/// ⚠ What this does NOT establish: that any trace of these descriptors IS a Wrap verification. §5b
/// says the same thing about itself — these are PRICES, and the operation counts are read at
/// o1-labs source, not proved here.
#[test]
fn the_repriced_atoms_are_the_served_widths() {
    use dregg_circuit::descriptor_ir2::parse_vm_descriptor2;
    let rcb = parse_vm_descriptor2(RCB_THREAD_DESC).expect("the served sound curve row");
    let alu = parse_vm_descriptor2(ALU_DESC).expect("the served sound ALU row");
    assert_eq!(rcb.name, "dregg-pasta-pallas-rcb-thread::v1");
    assert_eq!(alu.name, "dregg-pasta-alu-sound::v1");
    assert_eq!(rcb.trace_width, 3048, "MinaWrapVerifierAir.RCB_ROW_COLS");
    assert_eq!(alu.trace_width, 226, "MinaWrapVerifierAir.ALU_ROW_COLS");

    // …and the cell price those two widths give, recomputed here rather than quoted.
    const COMPLETE_ADDS: usize = 256 * (41 + 2 + 10 + 48 + 35);
    const TRANSCRIPT_ALU_ROWS: usize = 148 * (55 * (3 * 4 + 9));
    assert_eq!(COMPLETE_ADDS, 34_816);
    assert_eq!(TRANSCRIPT_ALU_ROWS, 170_940);
    let cells = COMPLETE_ADDS * rcb.trace_width + TRANSCRIPT_ALU_ROWS * alu.trace_width;
    assert_eq!(cells, 144_751_608, "MinaWrapVerifierAir.wrap_cells_eq");

    // ⚑ The row count against the measured `lb = 2` ceiling — the number the standing ≈10⁹ estimate
    // got wrong in SHAPE, by assuming ~100 constraints packed per row.
    let rows = COMPLETE_ADDS + TRANSCRIPT_ALU_ROWS;
    assert_eq!(rows, 205_756);
    assert!(rows < 1 << 18, "four powers of two under the 2^25 ceiling");

    println!(
        "\n§6 in-AIR Wrap verify (excl. SRS leg) = {cells} cells over {rows} rows \
         ({} + {} at widths {} / {})",
        COMPLETE_ADDS, TRANSCRIPT_ALU_ROWS, rcb.trace_width, alu.trace_width
    );
}
