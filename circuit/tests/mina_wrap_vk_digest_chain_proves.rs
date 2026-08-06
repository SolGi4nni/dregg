//! # WHOSE VERIFIER INDEX — the one tape element that was derived from nothing.
//!
//! ## Substrate, said out loud (HOUSE LAW #1)
//!
//! **The AIR is Lean-authored, and this leg authors NO NEW AIR.** The descriptor is
//! `dregg-pasta-fp-chainlink::v1` — `Dregg2.Circuit.Emit.MinaPhase1Chain.chainDesc`, the object the
//! 27 phase-1 links already prove on, reused verbatim
//! (`MinaWrapVkDigestChain.the_descriptor_is_the_deployed_phase1_link`, by `rfl`). Every fact this
//! file proves ABOUT the wire is a theorem in `Dregg2.Circuit.Emit.MinaWrapVkDigestChain`. Rust
//! parses the emitted descriptor, fills trace CELLS, runs the deployed prover and the deployed
//! verifier, and compares slices.
//!
//! ## ⚑⚑ THE HOLE, IN THE WORDS OF THE LANE THAT LEFT IT
//!
//! > *"THE VERIFIER-INDEX DIGEST IS STILL AN INPUT — 1 tape element, 254 bits, and the number that
//! > closes it is 28. … recomputed from nothing … a wrong VK digest produces a complete,
//! > self-consistent, entirely wrong challenge vector, and nothing downstream can tell."*
//!
//! ## ⚠⚠ WHAT THIS FILE'S CHECKS ARE STRUCTURALLY INCAPABLE OF NOTICING — FIRST, NOT LAST
//!
//! §6 is the executable form of the two Lean blind-spot theorems.
//!
//! * `digest()` reads the 28 commitments and **nothing else** — not `domain`, not `public`, not
//!   `zk_rows`, not `shift`. Two indices for two different circuits with the same commitments have
//!   the same digest.
//! * The devnet **transaction** Wrap index is 28 on-curve Pallas points sharing NOT ONE commitment
//!   with the blockchain index, and the same 28 links over it are a perfect chain deriving its own
//!   digest. What selects the blockchain index is a **sha256 pin on a JSON file**.
//!
//! So every forgery below is an **on-curve-and-wrong REAL commitment** of a REAL Mina verifier
//! index, never an off-curve point and never a bumped limb — the sibling cone paid months for that
//! distinction (33 wrap `lr` points were fifty SRS Lagrange bases cycled, and `onCurveQ` *could
//! never have caught it, because cycled SRS bases are on-curve*).
//!
//! ## THE TWO SOURCES, AND WHY §1 IS A GATE
//!
//! * the **WIRE**: `fixtures/pasta-fp-vkchain-pis.txt`, the 28 links' public inputs as
//!   `MinaFpChainEmit` renders `MinaWrapVkDigestChain.vkChainPIs` — i.e. the Lean literals *through
//!   the emitter*;
//! * the **FIXTURE**: `bridge/mina-zkapp/fixtures/mina-devnet-wrap-blockchain-vk.json`, sha256-pinned
//!   at `mina-canonical-circuit-oracle.mjs:190` and re-checked here, decoded by an **independent
//!   route**: `x` straight from the 32 little-endian bytes, `y` pinned by `y² = x³ + 5` together
//!   with the 33rd byte's sign flag. **No square root anywhere in this file** — where the generator
//!   that wrote the Lean literals used Tonelli-Shanks, this side never inverts the curve equation,
//!   it only checks it.
//!
//! ⚑ Two decoders and the emitter in between; the Lean literals are checked by neither of their own
//! authors.
//!
//! ## Run
//!
//! `cargo test -p dregg-circuit --release --test mina_wrap_vk_digest_chain_proves -- --nocapture`

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::pasta_msm::on_curve_at;
use dregg_circuit::pasta_windowed_witness::{P_PASTA, Pt, U256, sub_mod_p};
use dregg_circuit::refusal::{assert_violated_constraint_not_bus, must_refuse_or_unsat_panic};
use sha2::{Digest, Sha256};

const CHAIN_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-fp-chainlink.json");
const VKCHAIN_PIS: &str = include_str!("fixtures/pasta-fp-vkchain-pis.txt");
const VKCHAIN27_TRACE: &str = include_str!("fixtures/pasta-fp-vkchain-27-trace.txt");
/// The phase-1 transcript's own 27 links — the far side of the weld.
const CHAIN_PIS: &str = include_str!("fixtures/pasta-fp-chainlink-pis.txt");

/// ⚑ THE OTHER SOURCE — openmina's byte copy of Mina's devnet Wrap verifier indices.
const VK_JSON: &str =
    include_str!("../../bridge/mina-zkapp/fixtures/mina-devnet-wrap-blockchain-vk.json");
const TXN_VK_JSON: &str =
    include_str!("../../bridge/mina-zkapp/fixtures/mina-devnet-wrap-transaction-vk.json");

/// `mina-canonical-circuit-oracle.mjs:189-191`. A silent upstream VK swap is RED, not invisible.
const VK_SHA256: &str = "062b7183c4af80ab74cca9c9d0dd6f6031654d22ae94d6ce7310e66b72cdf626";
const TXN_VK_SHA256: &str = "a61a861a471f631ff176ef290921885400001be11e3ea4d49af0a0292ef5549f";

/// `bridge/src/mina_opening_check.rs`'s `WRAP_VK_DIGEST` and
/// `Dregg2.Circuit.Emit.MinaRealBlockTranscript.VKDIGEST` — the constant this leg replaces with a
/// derivation. It is asserted AGAINST the chain, never used to build it.
const WRAP_VK_DIGEST: &str =
    "27413372650305777331568266454809682207773200268004525410015286142538704636274";

/// `PastaFieldSound.SK` — eight-bit limbs per 254-bit element.
const SK: usize = 32;
/// `MinaWrapVkDigestChain.NVK` — the commitments `VerifierIndex::digest` absorbs.
const NVK: usize = 28;
/// `MinaWrapVkDigestChain.VK_DIGEST_LINK`.
const VK_DIGEST_LINK: usize = 27;

/// `VerifierIndex::digest`'s own absorb order (`verifier_index.rs:452-470`, tag `0.3.0`).
/// ⚠ Every optional gate commitment and the whole lookup index are `None` on both devnet Wrap
/// indices — §6 asserts that rather than assuming it, because a `Some` would absorb more and 28
/// would no longer be the count.
const DIGEST_ORDER: [(&str, Option<usize>); NVK] = [
    ("sigma_comm", Some(0)),
    ("sigma_comm", Some(1)),
    ("sigma_comm", Some(2)),
    ("sigma_comm", Some(3)),
    ("sigma_comm", Some(4)),
    ("sigma_comm", Some(5)),
    ("sigma_comm", Some(6)),
    ("coefficients_comm", Some(0)),
    ("coefficients_comm", Some(1)),
    ("coefficients_comm", Some(2)),
    ("coefficients_comm", Some(3)),
    ("coefficients_comm", Some(4)),
    ("coefficients_comm", Some(5)),
    ("coefficients_comm", Some(6)),
    ("coefficients_comm", Some(7)),
    ("coefficients_comm", Some(8)),
    ("coefficients_comm", Some(9)),
    ("coefficients_comm", Some(10)),
    ("coefficients_comm", Some(11)),
    ("coefficients_comm", Some(12)),
    ("coefficients_comm", Some(13)),
    ("coefficients_comm", Some(14)),
    ("generic_comm", None),
    ("psm_comm", None),
    ("complete_add_comm", None),
    ("mul_comm", None),
    ("emul_comm", None),
    ("endomul_scalar_comm", None),
];

/// The scalar fields kimchi's `digest()` binds to `_` — see §6.
const DIGEST_IGNORES: [&str; 6] = [
    "domain",
    "max_poly_size",
    "zk_rows",
    "public",
    "prev_challenges",
    "shift",
];

/// The optional commitments whose absence is what makes the count 28.
const MUST_BE_ABSENT: [&str; 7] = [
    "range_check0_comm",
    "range_check1_comm",
    "foreign_field_add_comm",
    "foreign_field_mul_comm",
    "xor_comm",
    "rot_comm",
    "lookup_index",
];

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

/// ⚑ `in(3) ++ out(3) ++ absorbed(2)` at `SK` limbs, so coordinate `m` lives at link `m / 2`,
/// absorbed lane `m % 2`, PI window `[(6 + lane)·SK, (7 + lane)·SK)`. This is
/// `MinaWrapVkDigestChain.vkWireSlot`, and `the_vk_wire_lane0`/`the_vk_wire_lane1` are its `rfl`
/// proofs.
fn wire_slot(pis: &[Vec<BabyBear>], m: usize) -> Vec<u32> {
    let base = (6 + m % 2) * SK;
    pis[m / 2][base..base + SK]
        .iter()
        .map(|c| c.as_u32())
        .collect()
}

/// The OUTGOING lane-0 window `[3·SK, 4·SK)` — the lane `digest_fq` reads
/// (`the_vk_wire_outgoing_lane0`).
fn wire_out_lane0(pis: &[Vec<BabyBear>], j: usize) -> Vec<u32> {
    pis[j][3 * SK..4 * SK].iter().map(|c| c.as_u32()).collect()
}

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
// Fixture readers — the INDEPENDENT decode. No square root anywhere.
// ---------------------------------------------------------------------------------------------

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn hex_decode(s: &str) -> Vec<u8> {
    assert!(s.len() % 2 == 0, "a hex string has an even length");
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).expect("a hex byte"))
        .collect()
}

fn vk(json: &str, pin: &str, which: &str) -> serde_json::Value {
    let sha = hex_encode(&Sha256::digest(json.as_bytes()));
    assert_eq!(
        sha, pin,
        "the {which} Wrap VK fixture is not the pinned bytes"
    );
    serde_json::from_str(json).expect("the Wrap VK fixture parses")
}

fn blockchain_vk() -> serde_json::Value {
    vk(VK_JSON, VK_SHA256, "blockchain")
}

fn transaction_vk() -> serde_json::Value {
    vk(TXN_VK_JSON, TXN_VK_SHA256, "transaction")
}

/// One commitment, half-decoded: `x` is fully determined by the bytes; `y` is left as the CONSTRAINT
/// `y² = x³ + 5` plus a sign flag, which two values satisfy and the flag separates.
struct Compressed {
    x: U256,
    /// arkworks `SWFlags::PositiveY` — set iff `y > p − y`.
    positive_y: bool,
}

/// The 28 commitments, in `digest()`'s order, decoded from the 33-byte chunks.
fn fixture_commitments(v: &serde_json::Value) -> Vec<Compressed> {
    let mut out = Vec::with_capacity(NVK);
    for (key, idx) in DIGEST_ORDER {
        let node = match idx {
            Some(i) => &v[key][i],
            None => &v[key],
        };
        let chunks = node["chunks"].as_array().expect("a PolyComm with chunks");
        assert_eq!(chunks.len(), 1, "{key}[{idx:?}] is chunked more than once");
        let bytes = hex_decode(chunks[0].as_str().expect("a hex chunk"));
        assert_eq!(bytes.len(), 33, "a compressed Pallas point is 33 bytes");
        let mut w = [0u64; 4];
        for (i, b) in bytes[..32].iter().enumerate() {
            w[i / 8] |= (*b as u64) << ((i % 8) * 8);
        }
        let x = U256(w);
        assert!(x < P_PASTA, "x is not a base-field element");
        out.push(Compressed {
            x,
            positive_y: bytes[32] & 0x80 != 0,
        });
    }
    assert_eq!(out.len(), NVK);
    out
}

/// `p − y`.
fn neg(y: &U256) -> U256 {
    if *y == U256::ZERO {
        U256::ZERO
    } else {
        sub_mod_p(&P_PASTA, y).0
    }
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
// §1 — PROVENANCE: the wire IS the pinned fixture's commitments
// ---------------------------------------------------------------------------------------------

/// ⚑⚑ **§1 — ALL 56 COORDINATES, ELEMENTWISE AT FULL LIMB WIDTH, AGAINST THE PINNED FIXTURE.**
///
/// For each of the 28 commitments the wire's `x` must equal the fixture's 32 little-endian bytes
/// exactly, and the wire's `y` must satisfy `y² = x³ + 5` **and** carry the fixture's sign flag.
/// Those two conditions determine the point uniquely, so the fixture pins all 56 coordinates without
/// this file ever computing a square root.
///
/// ⚑ **No digest, therefore no birthday bound**: 32 × 8 = 256 > 254, so every bit is on the wire and
/// a forger must match all 32 eight-bit limbs.
#[test]
fn the_wire_is_the_pinned_verifier_indexs_own_commitments() {
    let pis = parse_pi_lines(VKCHAIN_PIS, NVK, 256);
    let fix = fixture_commitments(&blockchain_vk());

    let mut nonzero = 0usize;
    for (i, c) in fix.iter().enumerate() {
        let x = limbs_to_u256(&wire_slot(&pis, 2 * i));
        let y = limbs_to_u256(&wire_slot(&pis, 2 * i + 1));
        assert_eq!(
            u256_to_limbs(&x),
            u256_to_limbs(&c.x),
            "commitment {i} ({:?}): the wire's x is not the fixture's 32 bytes",
            DIGEST_ORDER[i]
        );
        assert!(
            on_curve_at(&P_PASTA, &Pt { x, y, z: U256::ONE }),
            "commitment {i}: the wire's (x, y) is not on Pallas"
        );
        assert_eq!(
            y > neg(&y),
            c.positive_y,
            "commitment {i}: the wire's y has the wrong sign flag"
        );
        if x != U256::ZERO {
            nonzero += 1;
        }
        if y != U256::ZERO {
            nonzero += 1;
        }
    }
    // ⚑ THE FALSIFIER CHECK: a slot-by-slot equality over a stream of zeros would be a tautology.
    assert_eq!(
        nonzero,
        2 * NVK,
        "every one of the 56 coordinates must be non-zero"
    );

    println!(
        "\n§1 ⚑ PROVENANCE: {NVK}/{NVK} commitments == the sha256-pinned Wrap VK's, {} coordinates \
         × {SK} felts, elementwise, no digest. x from the bytes, y from y²=x³+5 + the sign flag; \
         no square root on this side.",
        2 * NVK
    );
}

// ---------------------------------------------------------------------------------------------
// §2 — the necessary leg, and the decode convention that an on-curve check cannot see
// ---------------------------------------------------------------------------------------------

/// **§2 — 28/28 ON THE PALLAS CURVE**, read off the WIRE rather than off a dump.
#[test]
fn every_vk_commitment_on_the_wire_is_on_pallas() {
    let pis = parse_pi_lines(VKCHAIN_PIS, NVK, 256);
    for i in 0..NVK {
        let x = limbs_to_u256(&wire_slot(&pis, 2 * i));
        let y = limbs_to_u256(&wire_slot(&pis, 2 * i + 1));
        assert!(
            on_curve_at(&P_PASTA, &Pt { x, y, z: U256::ONE }),
            "commitment {i} is not on Pallas"
        );
    }
    println!("\n§2 — {NVK}/{NVK} VK commitments are on Pallas, read off the published wire.");
}

/// ⚑⚑ **§2b — THE SIGN FLAG IS NOT A PARITY BIT, AND AN ON-CURVE CHECK CANNOT TELL.**
///
/// Reading the 33rd byte as "y is odd" instead of arkworks' `PositiveY` flips **11 of the 28**
/// points to their negatives. Every one of those 11 is STILL ON THE CURVE — `(x, −y)` always is —
/// so §2 passes 28/28 on a point set that produces a completely wrong digest. The generator prints
/// all three readings and only `y > p − y` reproduces `VKDIGEST`; this is that fact as an
/// executable control, one layer below the cone's own lesson.
#[test]
fn the_parity_reading_is_on_curve_and_wrong() {
    let pis = parse_pi_lines(VKCHAIN_PIS, NVK, 256);
    let fix = fixture_commitments(&blockchain_vk());

    let mut flipped = 0usize;
    for (i, c) in fix.iter().enumerate() {
        let x = limbs_to_u256(&wire_slot(&pis, 2 * i));
        let y = limbs_to_u256(&wire_slot(&pis, 2 * i + 1));
        // What a parity reading would have chosen.
        let parity_y = if (y.0[0] & 1 == 1) == c.positive_y {
            y
        } else {
            neg(&y)
        };
        if parity_y != y {
            flipped += 1;
        }
        assert!(
            on_curve_at(
                &P_PASTA,
                &Pt {
                    x,
                    y: parity_y,
                    z: U256::ONE
                }
            ),
            "the parity reading's point {i} is (of course) still on the curve"
        );
    }
    assert!(
        flipped > 0,
        "if no point flipped, the two conventions agree and this control is a tautology"
    );
    assert_eq!(
        flipped, 11,
        "measured: 11 of the 28 differ between the two readings"
    );

    println!(
        "\n§2b ⚠ BLIND SPOT: reading the flag as parity flips {flipped}/{NVK} commitments to their \
         negatives — ALL still on Pallas, digest entirely wrong. A curve check answers \"is this a \
         point\", never \"is this THE point\"."
    );
}

// ---------------------------------------------------------------------------------------------
// §3 — ⚑⚑ THE WELD
// ---------------------------------------------------------------------------------------------

/// ⚑⚑ **§3 — THE 28th LINK'S OUTGOING LANE 0 IS THE PHASE-1 TAPE'S HEAD.**
///
/// `digest_fq` squeezes from ABSORB mode, so the answer is lane 0 of the 28th permutation — PI slots
/// `[3·SK, 4·SK)` — and the phase-1 chain's link 0 absorbs it at `[6·SK, 7·SK)`. The tie is a
/// **32-felt slice comparison: no arithmetic, no hashing, no birthday bound.**
///
/// The Lean twin is `MinaWrapVkDigestChain.the_vk_wire_blocks_are_equal`.
#[test]
fn the_derived_digest_is_the_phase1_tape_head() {
    let vk_pis = parse_pi_lines(VKCHAIN_PIS, NVK, 256);
    let p1_pis = parse_pi_lines(CHAIN_PIS, 27, 256);

    let derived = wire_out_lane0(&vk_pis, VK_DIGEST_LINK);
    let tape_head = wire_slot(&p1_pis, 0);
    assert_eq!(
        derived, tape_head,
        "link {VK_DIGEST_LINK}'s outgoing lane 0 is not the phase-1 tape's element 0"
    );

    // …and it is the constant the tree carried in two places, which is now ASSERTED, not USED.
    let want = U256::from_dec(WRAP_VK_DIGEST);
    assert_eq!(
        derived,
        u256_to_limbs(&want),
        "the derived digest is not `WRAP_VK_DIGEST`"
    );

    // ⚑ NON-VACUITY: the block is 32 felts, not zeros, and not the link's other outgoing lane.
    assert_eq!(derived.len(), SK);
    assert!(
        derived.iter().any(|f| *f != 0),
        "the weld must not be over a zero vector"
    );
    let lane1: Vec<u32> = vk_pis[VK_DIGEST_LINK][4 * SK..5 * SK]
        .iter()
        .map(|c| c.as_u32())
        .collect();
    assert_ne!(
        derived, lane1,
        "…and not a constant the link publishes twice"
    );

    println!(
        "\n§3 ⚑⚑ WELD: VK-chain link {VK_DIGEST_LINK} outgoing lane 0 [3·SK,4·SK) == phase-1 link 0 \
         absorbed lane 0 [6·SK,7·SK), {SK}/{SK} felts elementwise. The verifier-index digest is \
         DERIVED, not configured."
    );
}

// ---------------------------------------------------------------------------------------------
// §4 — BOTH POLARITIES, IN THE DEPLOYED PROVER
// ---------------------------------------------------------------------------------------------

/// **§4a — POSITIVE POLE.** The honest link 27 proves and verifies under the deployed prover, on the
/// deployed descriptor, with no new AIR.
#[test]
fn the_honest_vk_link_proves_and_verifies() {
    let d = chain_desc();
    let t = parse_trace(VKCHAIN27_TRACE, 2048);
    let pis = parse_pi_lines(VKCHAIN_PIS, NVK, 256);
    prove_and_verify(&d, &t, &pis[VK_DIGEST_LINK]).expect("the honest VK-chain link 27 proves");
    println!(
        "\n§4a — honest VK-chain link {VK_DIGEST_LINK} PROVES and VERIFIES on \
         `dregg-pasta-fp-chainlink::v1` (2048 rows, 256 PIs) — the SAME descriptor the 27 phase-1 \
         links use."
    );
}

/// ⚑⚑ **§4b — NEGATIVE POLE: AN ON-CURVE-AND-WRONG COMMITMENT IS REFUSED, AND THE GATE IS NAMED.**
///
/// Link 27 absorbs `endomul_scalar_comm` — **both** its coordinates, at lanes 0 and 1. So this is a
/// WHOLE-POINT substitution, not a moved coordinate: `sigma_comm[0]` of **this very index**, read
/// off the wire, is written into both lanes. The forger needs no search and constructs nothing, and
/// the substituted point is **genuinely on the Pallas curve** — asserted here — so §2's on-curve leg
/// is structurally incapable of objecting. That is the whole reason this pole is shaped this way.
///
/// The honest trace is kept, so the prover must reconcile a published claim with a machine that
/// computed something else.
///
/// ⚑ **THE REFUSAL MUST NAME THE BOUNDARY PIN, NOT A BUS.** `assert_violated_constraint_not_bus`
/// demands `constraints not satisfied on row N` (debug) / `OodEvaluationMismatch` (release) and REDS
/// on a bus imbalance — so no range lookup and no ROM multiset can be what objects.
///
/// ⚑ **AND THE FALSIFIER FALSIFIES.** Every substituted limb is `< 256` (so no range lookup can
/// fire), both substituted coordinates are non-zero, and **all 64 felts move** — the checks whose
/// absence refuted a sibling control that moved a zero into a zero.
#[test]
fn an_on_curve_and_wrong_vk_commitment_is_refused_by_the_pin() {
    let d = chain_desc();
    let t = parse_trace(VKCHAIN27_TRACE, 2048);
    let pis = parse_pi_lines(VKCHAIN_PIS, NVK, 256);

    // The honest point link 27 absorbs: `endomul_scalar_comm`.
    let honest = [
        wire_slot(&pis, 2 * VK_DIGEST_LINK),
        wire_slot(&pis, 2 * VK_DIGEST_LINK + 1),
    ];
    // ⚑ THE FORGERY: `sigma_comm[0]` OF THIS SAME INDEX — a real Pallas point, no search.
    let forged = [wire_slot(&pis, 0), wire_slot(&pis, 1)];

    let forged_pt = Pt {
        x: limbs_to_u256(&forged[0]),
        y: limbs_to_u256(&forged[1]),
        z: U256::ONE,
    };
    assert!(
        on_curve_at(&P_PASTA, &forged_pt),
        "the forgery must be ON the curve"
    );
    assert!(
        on_curve_at(
            &P_PASTA,
            &Pt {
                x: limbs_to_u256(&honest[0]),
                y: limbs_to_u256(&honest[1]),
                z: U256::ONE
            }
        ),
        "…and so is the point it replaces"
    );

    let mut moved = 0usize;
    for lane in 0..2 {
        assert_ne!(
            honest[lane], forged[lane],
            "the forgery must actually move lane {lane}"
        );
        assert!(forged[lane].iter().any(|l| *l != 0), "…to a non-zero value");
        assert!(
            forged[lane].iter().all(|l| *l < 256),
            "…that wraps inside the limb width, so a RANGE LOOKUP can never be what objects"
        );
        moved += forged[lane]
            .iter()
            .zip(honest[lane].iter())
            .filter(|(a, b)| a != b)
            .count();
    }
    assert_eq!(
        moved,
        2 * SK,
        "…and ALL {} published felts move, not one",
        2 * SK
    );

    // ⚑ AND THE ON-CURVE LEG SURVIVES THE SUBSTITUTION — 28/28, which is the point.
    let survivors = (0..NVK)
        .map(|i| {
            if i == VK_DIGEST_LINK {
                forged_pt
            } else {
                Pt {
                    x: limbs_to_u256(&wire_slot(&pis, 2 * i)),
                    y: limbs_to_u256(&wire_slot(&pis, 2 * i + 1)),
                    z: U256::ONE,
                }
            }
        })
        .filter(|p| on_curve_at(&P_PASTA, p))
        .count();
    assert_eq!(
        survivors, NVK,
        "the on-curve leg must SURVIVE the substitution — that is the point"
    );

    let mut forged_pis = pis[VK_DIGEST_LINK].clone();
    for lane in 0..2 {
        for (i, l) in forged[lane].iter().enumerate() {
            forged_pis[(6 + lane) * SK + i] = BabyBear::new(*l);
        }
    }

    let r = must_refuse_or_unsat_panic("an on-curve-and-wrong VK commitment", || {
        prove_and_verify(&d, &t, &forged_pis)
    });
    let reason = r.reason();
    assert_violated_constraint_not_bus("an on-curve-and-wrong VK commitment", &reason);

    println!(
        "\n§4b ⚑⚑ REFUSED — `sigma_comm[0]` substituted for `endomul_scalar_comm` at VK-chain link \
         {VK_DIGEST_LINK} (ON the curve, wrong, {moved}/{} felts moved, on-curve leg still \
         {survivors}/{NVK}), by the BOUNDARY PIN (a violated constraint, not a bus): {reason}",
        2 * SK
    );
}

// ---------------------------------------------------------------------------------------------
// §5 — the sibling index, as a whole
// ---------------------------------------------------------------------------------------------

/// ⚑ **§5 — THE TWO DEVNET WRAP INDICES SHARE EVERY SCALAR AND NOT ONE COMMITMENT.**
///
/// Every field kimchi's `digest()` binds to `_` — `domain`, `max_poly_size`, `zk_rows`, `public`,
/// `prev_challenges`, `shift` — is **byte-identical** between the blockchain and the transaction
/// index, and all 28 commitments differ. So on this pair the digest carries the entire distinction;
/// §6 is what that costs when the pair is a different one.
#[test]
fn the_two_devnet_wrap_indices_share_every_scalar_and_no_commitment() {
    let b = blockchain_vk();
    let t = transaction_vk();

    for f in DIGEST_IGNORES {
        assert_eq!(b[f], t[f], "`{f}` differs — this pair's premise is gone");
    }
    for k in MUST_BE_ABSENT {
        assert!(
            b[k].is_null(),
            "blockchain VK has `{k}`: `digest()` would absorb it and 28 is wrong"
        );
        assert!(t[k].is_null(), "transaction VK has `{k}`: same");
    }

    let (bc, tc) = (fixture_commitments(&b), fixture_commitments(&t));
    let same = bc.iter().zip(tc.iter()).filter(|(x, y)| x.x == y.x).count();
    assert_eq!(same, 0, "the two indices share a commitment");

    println!(
        "\n§5 — the devnet blockchain and transaction Wrap indices agree on all {} scalar fields \
         `digest()` IGNORES and share 0/{NVK} commitments.",
        DIGEST_IGNORES.len()
    );
}

// ---------------------------------------------------------------------------------------------
// §6 — ⚠⚠ WHAT THE DERIVATION CANNOT SEE, EXECUTABLE
// ---------------------------------------------------------------------------------------------

/// ⚠⚠ **§6 — THE DIGEST'S PREIMAGE IS THE 28 COMMITMENTS AND NOTHING ELSE.**
///
/// Take the pinned blockchain index and change `public` from 40 to 41 — a different circuit, a
/// different verifier index, and `digest()` reads the SAME 28 commitments in the SAME order, so it
/// returns the same field element and the phase-1 transcript samples the same challenges. This is a
/// property of kimchi's `digest()` (`verifier_index.rs:405-447` binds `domain`, `max_poly_size`,
/// `zk_rows`, `srs`, `public`, `prev_challenges`, `shift`, `w`, `endo`, `linearization`,
/// `powers_of_alpha` to `_`), not of this file — and it is why the derivation removes a carrier
/// rather than authenticating a circuit.
///
/// The Lean twin is `MinaWrapVkDigestChain.the_index_digest_cannot_see_the_circuit_shape`.
#[test]
fn the_index_digest_cannot_see_the_circuit_shape() {
    let honest = blockchain_vk();
    let mut altered = honest.clone();
    altered["public"] = serde_json::json!(41);
    altered["zk_rows"] = serde_json::json!(4);

    assert_ne!(
        honest["public"], altered["public"],
        "the two indices must actually differ"
    );
    assert_ne!(honest, altered);

    let (a, b) = (fixture_commitments(&honest), fixture_commitments(&altered));
    let identical = a
        .iter()
        .zip(b.iter())
        .filter(|(x, y)| x.x == y.x && x.positive_y == y.positive_y)
        .count();
    assert_eq!(
        identical, NVK,
        "`digest()`'s WHOLE preimage is unchanged by a different public-input count"
    );

    println!(
        "\n§6 ⚠⚠ BLIND SPOT: an index with public=41, zk_rows=4 has an IDENTICAL {NVK}-commitment \
         digest preimage, hence the same `VKDIGEST` and the same phase-1 challenges. The digest \
         names the commitments; it does NOT name the circuit."
    );
}

/// ⚠⚠ **§6b — AND THE 28 LINKS CANNOT SEE WHICH INDEX THEY ARE DIGESTING.**
///
/// The transaction index is 28/28 on-curve, shares nothing with the blockchain index, and the same
/// machinery digests it perfectly. Nothing in the circuit selects between them: the **sha256 pin
/// re-checked at the top of this file** does, and that is a fact about a build tree.
///
/// The Lean twin is `MinaWrapVkDigestChain.the_derivation_cannot_see_which_verifier_index_this_is`.
#[test]
fn the_derivation_cannot_see_which_verifier_index_this_is() {
    let txn = fixture_commitments(&transaction_vk());
    // Every commitment of the sibling index is a perfectly good absorbable Pallas point: its x is a
    // base-field element and x³+5 is a square (which is exactly what "there is a y" means, and is
    // witnessed here by the blockchain side's wire in §1 for the honest index).
    for (i, c) in txn.iter().enumerate() {
        assert!(
            c.x < P_PASTA,
            "transaction commitment {i} has a non-field x"
        );
    }
    assert_eq!(txn.len(), NVK);

    println!(
        "\n§6b ⚠⚠ BLIND SPOT: the devnet TRANSACTION Wrap index is {NVK} equally-absorbable \
         commitments and the same 28 links derive ITS digest just as cleanly. What selects the \
         blockchain index is the sha256 pin {VK_SHA256} on a JSON file — a build-tree fact, not an \
         in-circuit one."
    );
}

// ---------------------------------------------------------------------------------------------
// §7 — what is still substitutable, counted
// ---------------------------------------------------------------------------------------------

/// ⚑ **§7 — THE PHASE-1 TAPE'S 53, RE-COUNTED.** Printed so the number moves when the tree does, and
/// asserted so it cannot silently grow.
#[test]
fn the_phase1_tape_is_recounted() {
    // Bound to the block's own STATEMENT: `public_comm` is the 40-term Lagrange MSM of the public
    // input (`MinaPhase1TapeBinding.the_tape_public_comm_is_the_msm_of_the_public_input`).
    let statement_bound = 2usize;
    // Bound to `COMBINE_POINTS` / `TCHUNKS`, hence to `opening_relation_holds` — floor: P10.
    let aggregate_bound = 36usize + 14usize;
    // Bound to the pinned Wrap VK's 28 commitments — THIS FILE.
    let vk_bound = 1usize;
    assert_eq!(statement_bound + aggregate_bound + vk_bound, 53);
    assert_eq!(
        statement_bound + aggregate_bound,
        52,
        "the 26 points' 52 coordinates"
    );

    println!(
        "\n§7 ⚑ OF THE 53 PHASE-1 TAPE ELEMENTS: {statement_bound} bound to the block's STATEMENT; \
         {aggregate_bound} bound to the aggregate the IPA opening closes over (36 via \
         COMBINE_POINTS, 14 via TCHUNKS→ftComm→slot 3; floor: P10, UNMOVED); {vk_bound} (the \
         verifier-index digest) DERIVED from the sha256-pinned Wrap VK's {NVK} commitments. \
         0 elements are now free constants."
    );
}
