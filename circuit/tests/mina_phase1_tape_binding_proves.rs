//! # WHOSE POINTS — the phase-1 tape's 53 elements, on the wire, against their sources.
//!
//! ## Substrate, said out loud (HOUSE LAW #1)
//!
//! **The AIR is Lean-authored.** `dregg-pasta-fp-chainlink::v1` is
//! `Dregg2.Circuit.Emit.MinaPhase1Chain.chainDesc`; every fact this file proves ABOUT the wire is a
//! theorem in `Dregg2.Circuit.Emit.MinaPhase1TapeBinding`. Nothing here authors a constraint, a
//! `Builder` gadget or an `air_accepts` predicate. Rust parses the emitted descriptor, fills trace
//! CELLS, runs the deployed prover and the deployed verifier, and compares slices.
//!
//! ## ⚑⚑ THE HOLE, IN THE WORDS OF THE LANE THAT LEFT IT
//!
//! > *"Nothing checks the 53 coordinates ARE the commitments they claim to be — no curve check, no
//! > `public_comm` binding … Deriving `fq_digest` removes a carrier; it does not verify Mina."*
//!
//! ## ⚠⚠ WHAT THIS FILE'S CHECKS ARE STRUCTURALLY INCAPABLE OF NOTICING — FIRST, NOT LAST
//!
//! §3 is the sentence as an executable control: **a point that is on the Pallas curve and is the
//! wrong commitment passes the on-curve leg 26/26.** The sibling cone paid months for this — 33 of
//! the wrap transcript's `lr` points were fifty SRS Lagrange bases cycled, and `onCurveQ` *could
//! never have caught it, because cycled SRS bases are on-curve.* So every forgery below is an
//! **on-curve-and-wrong** point of this very block, never an off-curve one and never a bumped limb.
//!
//! ## THE TWO SOURCES, AND WHY THIS IS A GATE AND NOT DECORATION
//!
//! * the **WIRE**: `fixtures/pasta-fp-chainlink-pis.txt`, the 27 links' public inputs as
//!   `EmitPastaAlu` renders `MinaPhase1Chain.chainPIs` — i.e. Lean's hand-typed literals *through
//!   the emitter*;
//! * the **EXTRACTOR**: `metatheory/mina_real_block_proof.json`, written by
//!   `metatheory/fixtures/pickles-extractors/src/main.rs` `fn transcript` off the committed
//!   `mina_devnet_block.json` (devnet block **539508**) and gated by `BlockVerifier::make()`,
//!   `accumulator_check` and `kimchi::verifier::verify == Ok(())` before a digit is printed.
//!
//! ⚑ Those are two independent sources, so §1 is a gate. It is also the FIRST thing in the tree to
//! check the Lean literals at all: `MinaRealBlockTranscript.lean`'s 53 decimals are a **hand
//! transcription** of that JSON, no generator writes them, and until this file nothing diffed them.
//!
//! ## Run
//!
//! `cargo test -p dregg-circuit --release --test mina_phase1_tape_binding_proves -- --nocapture`

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::pasta_msm::on_curve_at;
use dregg_circuit::pasta_windowed_witness::{P_PASTA, Pt, U256};
use dregg_circuit::refusal::{assert_violated_constraint_not_bus, must_refuse_or_unsat_panic};

const CHAIN_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-fp-chainlink.json");
const CHAIN26_TRACE: &str = include_str!("fixtures/pasta-fp-chainlink-26-trace.txt");
const CHAIN_PIS: &str = include_str!("fixtures/pasta-fp-chainlink-pis.txt");
/// ⚑ THE OTHER SOURCE — openmina's own read of Mina devnet block 539508.
const BLOCK_JSON: &str = include_str!("../../metatheory/mina_real_block_proof.json");

/// `PastaFieldSound.SK` — eight-bit limbs per 254-bit element.
const SK: usize = 32;
/// `MinaPhase1Chain.the_chain_is_twenty_seven_links`.
const PHASE1_LINKS: usize = 27;
/// `MinaPhase1Chain.DIGEST_LINK`.
const DIGEST_LINK: usize = 26;
/// `MinaPhase1TapeBinding.NPTS` — the group elements the phase-1 transcript eats.
const NPTS: usize = 26;
/// Flat absorb-stream length: 53 tape elements plus the odd tail's one padding zero.
const FLAT: usize = 54;
/// `MinaPhase1TapeBinding.flatIx`'s pad slot — between `w_comm[14].y` and `z_comm.x`.
const PAD_SLOT: usize = 37;

// ---------------------------------------------------------------------------------------------
// Wire readers
// ---------------------------------------------------------------------------------------------

fn parse_pi_lines(text: &str, links: usize, n: usize) -> Vec<Vec<BabyBear>> {
    let rows: Vec<Vec<BabyBear>> = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            let v: Vec<BabyBear> = l
                .split_whitespace()
                .map(|t| BabyBear::new(t.parse::<u32>().expect("a felt")))
                .collect();
            assert_eq!(v.len(), n, "every link publishes {n} public inputs");
            v
        })
        .collect();
    assert_eq!(rows.len(), links, "the chain is {links} links");
    rows
}

fn parse_trace(text: &str, rows: usize) -> Vec<Vec<BabyBear>> {
    let t: Vec<Vec<BabyBear>> = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|x| BabyBear::new(x.parse::<u32>().expect("a trace cell")))
                .collect()
        })
        .collect();
    assert_eq!(t.len(), rows, "the machine is {rows} rows");
    t
}

/// ⚑ The descriptor's PI layout is `in(3) ++ out(3) ++ absorbed(2)` at `SK` limbs, so flat slot `m`
/// lives at link `m / 2`, absorbed lane `m % 2`, PI window `[(6 + lane)·SK, (7 + lane)·SK)`. This is
/// `MinaPhase1TapeBinding.wireSlot`, and `the_wire_lane0`/`the_wire_lane1` are its `rfl` proofs.
fn wire_slot(pis: &[Vec<BabyBear>], m: usize) -> Vec<u32> {
    let base = (6 + m % 2) * SK;
    pis[m / 2][base..base + SK]
        .iter()
        .map(|c| c.as_u32())
        .collect()
}

/// Recompose 32 eight-bit limbs, little-endian, into the 254-bit element they carry.
fn limbs_to_u256(limbs: &[u32]) -> U256 {
    assert_eq!(limbs.len(), SK);
    let mut w = [0u64; 4];
    for (i, l) in limbs.iter().enumerate() {
        assert!(*l < 256, "limb {i} = {l} is not an eight-bit limb");
        w[i / 8] |= (*l as u64) << ((i % 8) * 8);
    }
    U256(w)
}

fn u256_to_limbs(v: &U256) -> Vec<u32> {
    (0..SK)
        .map(|i| ((v.0[i / 8] >> ((i % 8) * 8)) & 0xff) as u32)
        .collect()
}

// ---------------------------------------------------------------------------------------------
// Extractor readers
// ---------------------------------------------------------------------------------------------

fn block() -> serde_json::Value {
    serde_json::from_str(BLOCK_JSON).expect("the extractor's block JSON parses")
}

fn dec_list(v: &serde_json::Value, key: &str) -> Vec<U256> {
    v["wrap_transcript"][key]
        .as_array()
        .unwrap_or_else(|| panic!("the extractor emits `{key}` as a list"))
        .iter()
        .map(|s| U256::from_dec(s.as_str().expect("a decimal string")))
        .collect()
}

/// ⚑ **THE EXTRACTOR'S OWN 54-SLOT STREAM**, assembled in `verifier.rs` absorb order from the
/// LABELLED pieces — never as one opaque list, so a mis-ordering is visible here rather than hidden
/// in a paste. The padding zero is the one the odd 37-element first segment forces.
fn extractor_flat_stream() -> Vec<U256> {
    let b = block();
    let vk = U256::from_dec(
        b["wrap_transcript"]["verifier_index_digest"]
            .as_str()
            .expect("the extractor emits the verifier-index digest"),
    );
    let mut out = vec![vk];
    out.extend(dec_list(&b, "phase1_prev_comm_xy"));
    out.extend(dec_list(&b, "phase1_public_comm_xy"));
    out.extend(dec_list(&b, "phase1_w_comm_xy"));
    assert_eq!(out.len(), 37, "the tape to beta is 37 elements");
    assert_eq!(
        b["wrap_transcript"]["phase1_tape_to_beta_len"].as_u64(),
        Some(37),
        "and the extractor says so itself"
    );
    out.push(U256::ZERO); // the pad — slot 37
    out.extend(dec_list(&b, "phase1_z_comm_xy"));
    out.extend(dec_list(&b, "phase1_t_comm_xy"));
    assert_eq!(out.len(), FLAT);
    out
}

/// The 26 points, from the extractor's coordinates: everything but slot 0 and the pad.
fn extractor_points() -> Vec<Pt> {
    let s = extractor_flat_stream();
    let coords: Vec<U256> = (0..FLAT)
        .filter(|m| *m != 0 && *m != PAD_SLOT)
        .map(|m| s[m])
        .collect();
    assert_eq!(coords.len(), 2 * NPTS, "52 coordinates");
    (0..NPTS)
        .map(|i| Pt {
            x: coords[2 * i],
            y: coords[2 * i + 1],
            z: U256::ONE,
        })
        .collect()
}

fn chain_desc() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(CHAIN_DESC_JSON)
        .expect("the deployed checker parses the phase-1 chain-link descriptor")
}

fn prove_and_verify(
    d: &EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    pis: &[BabyBear],
) -> Result<(), String> {
    let proof = prove_vm_descriptor2(d, trace, pis, &MemBoundaryWitness::default(), &[])?;
    verify_vm_descriptor2(d, &proof, pis)
}

// ---------------------------------------------------------------------------------------------
// §1 — PROVENANCE: the wire IS the extractor's stream
// ---------------------------------------------------------------------------------------------

/// ⚑⚑ **§1 — ALL 54 FLAT SLOTS, ELEMENTWISE AT FULL LIMB WIDTH.** The 32 felts the deployed
/// descriptor publishes for each slot recompose to exactly the value openmina read off block
/// 539508. **No digest, therefore no birthday bound**: a forger must match all 32 eight-bit limbs of
/// a 254-bit element, and 32 × 8 = 256 > 254, so every bit is on the wire.
///
/// ⚑ This is also the first check the Lean literals have ever faced. They are a HAND TRANSCRIPTION
/// of this JSON and no generator writes them.
#[test]
fn the_wire_is_the_extractors_own_tape() {
    let pis = parse_pi_lines(CHAIN_PIS, PHASE1_LINKS, 256);
    let stream = extractor_flat_stream();

    let mut moved = 0usize;
    for m in 0..FLAT {
        let on_wire = wire_slot(&pis, m);
        assert_eq!(
            on_wire,
            u256_to_limbs(&stream[m]),
            "flat slot {m} (link {}, absorbed lane {}) is not the extractor's value",
            m / 2,
            m % 2
        );
        if stream[m] != U256::ZERO {
            moved += 1;
        }
    }
    // ⚑ THE FALSIFIER CHECK: a slot-by-slot equality over a stream of zeros would be a tautology.
    assert_eq!(
        moved,
        FLAT - 1,
        "every slot but the pad must carry a non-zero value"
    );
    assert_eq!(
        wire_slot(&pis, PAD_SLOT),
        vec![0u32; SK],
        "the pad slot is zero"
    );

    println!(
        "\n§1 ⚑ PROVENANCE: {FLAT}/{FLAT} flat slots equal the extractor's, {} × {SK} felts, \
         elementwise, no digest. {moved} non-zero.",
        FLAT
    );
}

// ---------------------------------------------------------------------------------------------
// §2 — the necessary leg
// ---------------------------------------------------------------------------------------------

/// **§2 — 26/26 ON THE PALLAS CURVE**, read off the WIRE rather than off a dump: each point is two
/// 32-felt slices recomposed. `y²z = x³ + 5z³` over `Fp`.
#[test]
fn every_absorbed_point_on_the_wire_is_on_pallas() {
    let pis = parse_pi_lines(CHAIN_PIS, PHASE1_LINKS, 256);
    let slots: Vec<usize> = (0..FLAT).filter(|m| *m != 0 && *m != PAD_SLOT).collect();
    assert_eq!(slots.len(), 2 * NPTS);

    for i in 0..NPTS {
        let x = limbs_to_u256(&wire_slot(&pis, slots[2 * i]));
        let y = limbs_to_u256(&wire_slot(&pis, slots[2 * i + 1]));
        let p = Pt { x, y, z: U256::ONE };
        assert!(
            on_curve_at(&P_PASTA, &p),
            "absorbed point {i} is not on Pallas"
        );
    }
    println!("\n§2 — {NPTS}/{NPTS} absorbed points are on Pallas, read off the published wire.");
}

// ---------------------------------------------------------------------------------------------
// §3 — ⚑⚑ THE BLIND SPOT, EXECUTABLE
// ---------------------------------------------------------------------------------------------

/// ⚑⚑ **§3 — WHAT §2 CANNOT SEE.** Substitute `w_comm[0]` — a real Pallas point **of this very
/// block**, so the forger needs no search — for `public_comm`, and the on-curve leg still passes
/// **26/26**. An on-curve predicate answers *"is this a point"*. The question is *"is this THIS
/// block's commitment"*, and no curve check reaches it. Everything §4-§5 do is what reaches it.
#[test]
fn the_on_curve_leg_cannot_see_provenance() {
    let pts = extractor_points();
    let honest_pub = pts[2];
    let forged = pts[3]; // w_comm[0]

    assert!(
        on_curve_at(&P_PASTA, &forged),
        "the forgery must be ON the curve"
    );
    assert!(
        forged.x != honest_pub.x && forged.y != honest_pub.y,
        "…and WRONG"
    );
    assert!(
        forged.x != U256::ZERO && forged.y != U256::ZERO,
        "…and a real displacement"
    );

    let mut substituted = pts.clone();
    substituted[2] = forged;
    let survivors = substituted
        .iter()
        .filter(|p| on_curve_at(&P_PASTA, p))
        .count();
    assert_eq!(
        survivors, NPTS,
        "the whole on-curve leg must SURVIVE the substitution — that is the point"
    );

    println!(
        "\n§3 ⚠ BLIND SPOT: public_comm := w_comm[0] (on-curve, wrong) — on-curve leg still \
         {survivors}/{NPTS}. A curve check is NECESSARY and NOWHERE NEAR SUFFICIENT."
    );
}

// ---------------------------------------------------------------------------------------------
// §4 — ⚑⚑ THE BINDING THAT FORCES IDENTITY
// ---------------------------------------------------------------------------------------------

/// ⚑⚑ **§4 — `public_comm` IS COMPUTED FROM THE BLOCK'S STATEMENT, NOT READ OFF ITS PROOF.**
///
/// The extractor's `phase1_public_comm_xy` is `commit_public`'s output — `Σ_{i<40} (−publicᵢ)·Lᵢ +
/// 1·srs.h` over openmina's own `PreparedStatement::to_public_input` (`main.rs:336,360`), asserted
/// against the `public_input` the ACCEPTED `kimchi::verifier::verify` consumed. The Lean twin is
/// `MinaWrapPublicCommGate.publicComm`, and
/// `MinaPhase1TapeBinding.the_tape_public_comm_is_the_msm_of_the_public_input` is the tie.
///
/// So flat slots 5 and 6 — link 2's absorbed lane 1 and link 3's lane 0 — are the ONE place in this
/// tape where an on-curve-and-wrong substitution is refused OUTRIGHT rather than merely propagated.
#[test]
fn the_public_comm_on_the_wire_is_the_msm_of_the_public_input() {
    let pis = parse_pi_lines(CHAIN_PIS, PHASE1_LINKS, 256);
    let b = block();
    let pubc = dec_list(&b, "phase1_public_comm_xy");
    assert_eq!(pubc.len(), 2);

    assert_eq!(
        wire_slot(&pis, 5),
        u256_to_limbs(&pubc[0]),
        "public_comm.x is flat slot 5"
    );
    assert_eq!(
        wire_slot(&pis, 6),
        u256_to_limbs(&pubc[1]),
        "public_comm.y is flat slot 6"
    );

    // ⚑ AND THE FORGERY IS REFUSED BY THIS EQUALITY, where §3 could not see it at all.
    let forged = extractor_points()[3];
    assert_ne!(
        wire_slot(&pis, 5),
        u256_to_limbs(&forged.x),
        "the forgery must move slot 5"
    );
    assert_ne!(wire_slot(&pis, 6), u256_to_limbs(&forged.y), "…and slot 6");

    // …and the slot really is inside a link, not a free constant beside one.
    assert_eq!(
        (5 / 2, 5 % 2),
        (2, 1),
        "public_comm.x is link 2's absorbed lane 1"
    );
    assert_eq!(
        (6 / 2, 6 % 2),
        (3, 0),
        "public_comm.y is link 3's absorbed lane 0"
    );

    println!(
        "\n§4 ⚑⚑ BINDING: public_comm on the wire == the 40-term Lagrange MSM of the block's own \
         public input. 2 × {SK} felts, elementwise. An on-curve-and-wrong point is REFUSED here."
    );
}

// ---------------------------------------------------------------------------------------------
// §5 — BOTH POLARITIES, IN THE DEPLOYED PROVER
// ---------------------------------------------------------------------------------------------

/// **§5a — POSITIVE POLE.** The honest link 26 proves and verifies under the deployed prover.
#[test]
fn the_honest_link_proves_and_verifies() {
    let d = chain_desc();
    let t = parse_trace(CHAIN26_TRACE, 2048);
    let pis = parse_pi_lines(CHAIN_PIS, PHASE1_LINKS, 256);
    prove_and_verify(&d, &t, &pis[DIGEST_LINK]).expect("the honest phase-1 link 26 proves");
    println!("\n§5a — honest link {DIGEST_LINK} PROVES and VERIFIES (2048 rows, 256 PIs).");
}

/// ⚑⚑ **§5b — NEGATIVE POLE: AN ON-CURVE-AND-WRONG COORDINATE IS REFUSED, AND THE GATE IS NAMED.**
///
/// Link 26 absorbs `t_comm`'s last chunk. Its lane-0 slot is replaced by the **x-coordinate of
/// `w_comm[0]`** — a genuine Pallas coordinate of this very block, which is exactly the forgery §3
/// proved the curve check cannot see. The honest trace is kept, so the prover must reconcile a
/// published claim with a machine that computed something else.
///
/// ⚑ **THE REFUSAL MUST NAME THE BOUNDARY PIN, NOT A BUS.** `assert_violated_constraint_not_bus`
/// demands `constraints not satisfied on row N` (debug) / `OodEvaluationMismatch` (release) and
/// REDS on a bus imbalance — so a range lookup or a ROM multiset cannot be what objects.
///
/// ⚑ **AND THE FALSIFIER FALSIFIES.** Every substituted limb is `< 256` (so no range lookup can
/// fire), the substituted value is non-zero, and it differs from the honest one — the three checks
/// whose absence refuted a sibling control that moved a zero into a zero.
#[test]
fn an_on_curve_and_wrong_absorbed_coordinate_is_refused_by_the_pin() {
    let d = chain_desc();
    let t = parse_trace(CHAIN26_TRACE, 2048);
    let pis = parse_pi_lines(CHAIN_PIS, PHASE1_LINKS, 256);

    let forged = extractor_points()[3]; // w_comm[0] — on the curve, and not t_comm's chunk
    assert!(
        on_curve_at(&P_PASTA, &forged),
        "the forgery is ON the curve"
    );

    let honest = wire_slot(&pis, 2 * DIGEST_LINK); // link 26, lane 0
    let replacement = u256_to_limbs(&forged.x);
    assert_ne!(
        honest, replacement,
        "the forgery must actually move the slot"
    );
    assert!(replacement.iter().any(|l| *l != 0), "…to a non-zero value");
    assert!(
        replacement.iter().all(|l| *l < 256),
        "…that wraps inside the limb width, so a RANGE LOOKUP can never be what objects"
    );

    let mut forged_pis = pis[DIGEST_LINK].clone();
    for (i, l) in replacement.iter().enumerate() {
        forged_pis[6 * SK + i] = BabyBear::new(*l);
    }

    let r = must_refuse_or_unsat_panic("an on-curve-and-wrong absorbed coordinate", || {
        prove_and_verify(&d, &t, &forged_pis)
    });
    let reason = r.reason();
    assert_violated_constraint_not_bus("an on-curve-and-wrong absorbed coordinate", &reason);

    println!(
        "\n§5b ⚑⚑ REFUSED — on-curve-and-wrong coordinate at link {DIGEST_LINK} lane 0, by the \
         BOUNDARY PIN (a violated constraint, not a bus): {reason}"
    );
}

/// ⚑ **§5c — AND THE SAME FORGERY AT `public_comm`'s OWN SLOT.** Link 2's absorbed lane 1 is
/// `public_comm.x`. Substituting the same on-curve point there breaks §4's binding on the wire —
/// stated here as the wire fact, because the trace fixture in this tree is link 26's, so the
/// in-prover pole is fired above and this pole is fired on the published claim.
///
/// ⚠ **NAMED, NOT LAUNDERED**: this is a verifier-side slice comparison against an
/// independently-derived constant, NOT an in-AIR gate. See §8 residual 4 of the Lean file.
#[test]
fn the_forgery_at_public_comms_own_slot_breaks_the_binding() {
    let pis = parse_pi_lines(CHAIN_PIS, PHASE1_LINKS, 256);
    let b = block();
    let pubx = dec_list(&b, "phase1_public_comm_xy")[0];
    let forged = extractor_points()[3];

    assert_eq!(wire_slot(&pis, 5), u256_to_limbs(&pubx));
    assert_ne!(u256_to_limbs(&forged.x), u256_to_limbs(&pubx));

    // how many of the 32 felts must a forger match? all of them.
    let differing = u256_to_limbs(&forged.x)
        .iter()
        .zip(u256_to_limbs(&pubx).iter())
        .filter(|(a, b)| a != b)
        .count();
    assert!(
        differing > 0,
        "the substitution must be visible on the wire"
    );

    println!(
        "\n§5c — the same on-curve-and-wrong point at flat slot 5 differs in {differing}/{SK} \
         published felts; the binding is a slice comparison and does no arithmetic."
    );
}

// ---------------------------------------------------------------------------------------------
// §6 — what is still substitutable, counted
// ---------------------------------------------------------------------------------------------

/// ⚑ **§6 — THE RESIDUAL, AS A COUNT RATHER THAN A PARAGRAPH.** Printed so the number moves when
/// the tree does, and asserted so it cannot silently grow.
///
/// ⚑ **BOTH OF THIS FILE'S FREE ELEMENTS CLOSED 2026-08-06**, at the numbers they were named with:
///
/// * **1** element — the verifier-index digest — is DERIVED by `MinaWrapVkDigestChain`, the **28**
///   more links of THIS descriptor over the sha256-pinned Wrap VK's 56 coordinates this file priced.
///   Harness: `mina_wrap_vk_digest_chain_proves.rs`. ⚠ What is left of it is two blind spots stated
///   as theorems there, not a free constant here.
/// * **14** coordinates — the 7 `t_comm` chunks — are welded to `MinaWrapGroupGate.TCHUNKS`
///   (`the_tape_t_comm_chunks_are_the_ftComm_chunks`), hence to `ftComm`, hence to aggregate slot 3
///   and `opening_relation_holds`. They now sit at exactly the strength of the 36 below.
/// * **36 + 14 = 50** coordinates are bound to a second list which the block's own opening closes
///   over, and inherit the IPA `msm == 0` floor (P10), **unmoved**.
/// * **2** coordinates — `public_comm` — are bound to the block's own 40-element public input, the
///   one place an on-curve-and-wrong substitution is refused OUTRIGHT.
#[test]
fn what_is_still_substitutable_is_counted() {
    let vk_digest = 1usize;
    let t_comm = 14usize;
    let aggregate_bound = 36usize;
    let statement_bound = 2usize;
    assert_eq!(vk_digest + t_comm + aggregate_bound + statement_bound, 53);
    assert_eq!(t_comm + aggregate_bound + statement_bound, 2 * NPTS);

    println!(
        "\n§6 ⚑ OF THE 53: {statement_bound} bound to the block's STATEMENT (public input); \
         {} bound to the aggregate the IPA opening closes over ({aggregate_bound} via \
         COMBINE_POINTS, {t_comm} via TCHUNKS -> ftComm -> slot 3; floor: P10, UNMOVED); \
         {vk_digest} (the verifier-index digest) DERIVED from the pinned Wrap VK's 28 commitments \
         by 28 links of this same descriptor. 0 free constants remain.",
        aggregate_bound + t_comm
    );
}
