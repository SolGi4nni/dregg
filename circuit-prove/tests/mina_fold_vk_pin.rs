//! ⚑⚑ **THE CHILD-VK PIN, AND THE SAME-SHAPE/DIFFERENT-CONSTANTS CHILD IT REFUSES.**
//!
//! ⚠ **LABEL FIRST.** These are Rust **case-tests**. They are not translation validation, not
//! refinement and not verification — there is no formal semantics of Rust and a case-test says
//! nothing about all inputs. What they establish is behavioural: on this box, at this rev, the
//! pinned fold refuses a child proof of a different circuit and accepts the honest one. "It proves
//! on a box" is not verified and not sound; everything below inherits the undischarged FRI/STARK
//! floor.
//!
//! # WHAT WAS OPEN
//!
//! `RecursionOutput::into_recursion_input` passes `expected_preprocessed_commit: None`, and the
//! field's own docblock says a from-scratch prover could then fold a proof of a DIFFERENT circuit.
//! Every fold in the Mina tower took that path — `fold_chain_links`, `fold_endo_into_finalize`,
//! `fold_transcript_into_finalize` **and `fold_accumulator_segments`**, eight `into_recursion_input`
//! call sites across four folds. The parent circuit's SHAPE comes from each child's `CommonData`, so
//! a differently-shaped child moves the parent VK; what was not excluded is a child of **identical
//! shape and different preprocessed CONTENT.**
//!
//! # ⚑ THE ADVERSARY IS NOT SYNTHETIC — IT IS A DESCRIPTOR ALREADY IN THE TREE
//!
//! `dregg-pasta-fp-chainlink::v1` is `dregg-pasta-fq-chainlink::v1` with `fp_kimchi`'s Poseidon
//! constants where `fq_kimchi`'s should be. Same 469 trace columns, same 256 public inputs, same 922
//! constraints, same five tables at the same arities, the same `chainPins` layout, and therefore the
//! same 200-lane fold claim — so `fold_chain_links`' `require_chain_claim` lane-count gate passes it.
//! §0 asserts that structural identity and that numeric difference **constructively, before any
//! verdict is read**, because this repo has shipped an adversary that quietly became a no-op.
//!
//! # HOW THE REFUSAL IS ISOLATED
//!
//! §1 folds the Fp pair `(fp0, fp1)` twice with the SAME children:
//!
//! * with pins tracked off those children — a **CONTROL** that must LAND. It proves the Fp pair is
//!   internally chain-continuous, that its transcript fold is satisfiable, and that every other
//!   constraint in that parent circuit has a satisfying assignment.
//! * with pins naming the **Fq** leaf's commitment — which must be **REFUSED**. The children,
//!   the claim lanes, the state carry and the digest fold are byte-identical to the control run, so
//!   the only constraint that changed is the VK pin.
//!
//! ⚠ **The refusal is the CIRCUIT'S.** `fold_chain_links` runs no host comparison of `pins` against
//! the children's actual commitments — deliberately, so that a producer-side pre-flight cannot fire
//! first and leave the in-circuit constraint untested. The error arrives out of the aggregation
//! layer's witness solver.
//!
//! # MEASURED 2026-08-07, release — TWO runs, because one number here would be a lie
//!
//! ```text
//!   §0  660/2048 ROM rows and 52/922 constraints differ; every shape field agrees
//!   §1                                            run A (load ~40)   run B (quiet)
//!       Fq leaf wraps                             18 747 / 19 190     11 918 / 9 889 ms
//!       Fp leaf wraps                             15 858 / 20 046      9 402 / 8 274 ms
//!       CONTROL   (Fp children, Fp pins) LANDED   20 607 ms           10 454 ms
//!       ADVERSARY (Fp children, Fq pins) REFUSED     558 ms              452 ms
//!       HONEST    (Fq children, Fq pins) LANDED   19 515 ms            9 879 ms
//! ```
//!
//! ⚠ A factor of two between runs twenty minutes apart, on the same box, from co-tenancy alone.
//! Quote the band or re-measure.
//!
//! ⚑ The refusal reads `WitnessConflict { witness_id: WitnessId(472), … }` — the aggregation
//! layer's witness solver, which is what "the refusal is the circuit's" means concretely.
//!
//! ⚑ And a measurement that corrects the hole's statement: the two LEAF-wrap `RecursionVk`
//! fingerprints DIFFER (`705a99b1…` / `a4c22d13…`), because a leaf-wrap circuit compiles the inner
//! AIR's constants into its own op list. It is the FOLD's parent VK that does not separate them
//! unpinned — the child's commitment rides as a runtime public input, and `PublicAir`'s value
//! columns are main-trace only. A fold root is what a consumer anchors.
//!
//! Run: `cargo test -p dregg-circuit-prove --release --test mina_fold_vk_pin -- --nocapture`
//!
//! ## PREREQUISITE — the witnesses
//!
//! Links 0..1 of BOTH chains. Neither set is tracked (they are ~3 MB each). Emit with:
//!
//! ```text
//! cd metatheory && lake build mina_chain_emit mina_fp_chain_emit
//! ./.lake/build/bin/mina_chain_emit ../circuit/tests/fixtures/pasta-fq-chainlink 2
//! ./.lake/build/bin/mina_fp_chain_emit ../circuit/tests/fixtures 2
//! ```

use std::path::PathBuf;
use std::time::Instant;

use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::mina_fold_vk_pin::{FoldVkPins, VK_PIN_FELTS_PER_CHILD, child_vk_commit};
use dregg_circuit_prove::mina_phase2_chain_leaf::{
    CHAIN_PI_COUNT, chain_config, chain_link_descriptor, fold_chain_links,
    fp_chain_link_descriptor, prove_chain_link_leaf_with, read_chain_claim,
};
use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    recursion_vk_fingerprint, verify_recursive_batch_proof_with_config,
};

const FQ_DESC_JSON: &str =
    include_str!("../../circuit/descriptors/by-name/pasta-fq-chainlink.json");
const FP_DESC_JSON: &str =
    include_str!("../../circuit/descriptors/by-name/pasta-fp-chainlink.json");

// ============================================================================
// §0 — THE ADVERSARY IS SAME-SHAPE AND DIFFERENT-CONSTANTS. Cheap, unconditional,
//      and asserted BEFORE any proof is built.
// ============================================================================

/// Collapse every maximal run of ASCII digits to a single `#`, leaving all other bytes alone.
///
/// Two descriptor JSONs with the same skeleton have the same tables, the same constraint tree
/// shapes, the same operators and the same nesting — and differ ONLY in numeric literals. This is
/// the mechanical statement of "same shape, different constants", computed over the actual emitted
/// artifacts rather than asserted about them.
fn digit_skeleton(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut in_digits = false;
    for c in s.chars() {
        if c.is_ascii_digit() {
            if !in_digits {
                out.push('#');
                in_digits = true;
            }
        } else {
            in_digits = false;
            out.push(c);
        }
    }
    out
}

/// The two chain-link descriptors differ in FIELD, which is a difference of `p`/`q` in the name and
/// nowhere else structural. Normalising it is what lets the skeleton comparison be about constants.
fn field_normalised(s: &str) -> String {
    s.replace("pasta-fp-chainlink", "pasta-fX-chainlink")
        .replace("pasta-fq-chainlink", "pasta-fX-chainlink")
}

#[test]
fn the_fp_chainlink_is_the_fq_chainlink_with_different_constants() {
    let fq = chain_link_descriptor().expect("the Lean Fq chain-link descriptor parses");
    let fp = fp_chain_link_descriptor().expect("the Lean Fp chain-link descriptor parses");

    // They are DIFFERENT objects.
    assert_ne!(fq.name, fp.name);
    assert_eq!(fq.name, "dregg-pasta-fq-chainlink::v1");
    assert_eq!(fp.name, "dregg-pasta-fp-chainlink::v1");

    // …of IDENTICAL shape. Each of these is a dimension the parent aggregation circuit is derived
    // from, so agreeing on all of them is what makes the substitution invisible to a VK fingerprint
    // that does not pin preprocessed CONTENT.
    assert_eq!(fq.trace_width, fp.trace_width, "same trace width");
    assert_eq!(fq.trace_width, 469);
    assert_eq!(
        fq.public_input_count, fp.public_input_count,
        "same PI count — this is what `require_chain_claim` sees"
    );
    assert_eq!(fq.public_input_count, CHAIN_PI_COUNT);
    assert_eq!(
        fq.constraints.len(),
        fp.constraints.len(),
        "same constraint count"
    );
    assert_eq!(fq.constraints.len(), 922);

    // …and the whole emitted artifact agrees up to numeric literals.
    //
    // ⚠ `.trim()` covers exactly one measured byte: `pasta-fq-chainlink.json` ends with a newline
    // and `pasta-fp-chainlink.json` does not (`tail -c 40 … | xxd`, 2026-08-07). That is an emit
    // formatting difference, not a structural one, and it is named rather than absorbed silently —
    // a normalisation nobody can see is how an adversary quietly stops being one.
    let sk_fq = digit_skeleton(field_normalised(FQ_DESC_JSON).trim());
    let sk_fp = digit_skeleton(field_normalised(FP_DESC_JSON).trim());
    assert_eq!(
        sk_fq, sk_fp,
        "the two descriptors must agree on EVERYTHING except numeric literals — if they do not, \
         this test's adversary is a different-SHAPE child, which the parent VK already refuses, and \
         the pin would be tested against nothing"
    );

    // ⚑ AND THE CONSTANTS REALLY DIFFER, COUNTED OVER THE PARSED OBJECTS. Without this the
    // assertion above is satisfied by two copies of the same file and the whole adversary is a
    // no-op — the recorded failure this repo has already paid for once. Counted rather than
    // asserted `!=`, because "they are not equal" would also be true of a one-byte difference and
    // this test's whole claim is that the ROUND CONSTANTS are elsewhere.
    let differing_constraints = fq
        .constraints
        .iter()
        .zip(fp.constraints.iter())
        .filter(|(a, b)| a != b)
        .count();
    assert!(
        differing_constraints > 0,
        "the two descriptors' constraint lists are identical — the adversary would be the SAME \
         circuit and every verdict below would be vacuous"
    );

    let rom_rows = |d: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2| {
        d.tables
            .iter()
            .find(|t| t.name == "pasta_program_rom")
            .map(|t| match &t.sem {
                dregg_circuit::descriptor_ir2::TableSem::ExactPublicRows { rows } => rows.clone(),
                _ => panic!("the pasta program ROM is an `exact_public_rows` table"),
            })
            .expect("both chain-link descriptors declare a `pasta_program_rom`")
    };
    let (fq_rom, fp_rom) = (rom_rows(&fq), rom_rows(&fp));
    assert_eq!(
        fq_rom.len(),
        fp_rom.len(),
        "same ROM height — a different row count is a different SHAPE"
    );
    let differing_rom_rows = fq_rom
        .iter()
        .zip(fp_rom.iter())
        .filter(|(a, b)| a != b)
        .count();
    assert!(
        differing_rom_rows > 0,
        "⚑ THE ROUND CONSTANTS MUST ACTUALLY DIFFER. The ROM is where `ConstAir`-visible constants \
         live; if these rows agreed, the preprocessed commitments could agree and the pin would \
         have nothing to refuse."
    );

    println!(
        "\n§0 ⚑ SAME SHAPE, DIFFERENT CONSTANTS\n  \
         {} and {}\n  \
         trace_width {}  PIs {}  constraints {}  ROM rows {}  — identical\n  \
         JSON skeletons identical up to numeric literals.\n  \
         DIFFER: {differing_rom_rows}/{} ROM rows, {differing_constraints}/{} constraints.",
        fq.name,
        fp.name,
        fq.trace_width,
        fq.public_input_count,
        fq.constraints.len(),
        fq_rom.len(),
        fq_rom.len(),
        fq.constraints.len()
    );
}

// ============================================================================
// §1 — THE PIN BITES, AND THE REFUSAL IS THE CIRCUIT'S.
// ============================================================================

fn fq_dir() -> PathBuf {
    std::env::var("DREGG_CHAINLINK_WITNESS_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("../circuit/tests/fixtures/pasta-fq-chainlink")
        })
}

fn fp_dir() -> PathBuf {
    std::env::var("DREGG_FP_CHAINLINK_WITNESS_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("../circuit/tests/fixtures/pasta-fp-chainlink")
        })
}

fn felts(line: &str) -> Vec<BabyBear> {
    line.split_whitespace()
        .map(|c| BabyBear::new(c.parse::<u32>().expect("cell is a u32 decimal")))
        .collect()
}

/// Read link `j`'s Lean-emitted trace and public inputs. Fails LOUDLY with the emit command rather
/// than skipping: a test that quietly does nothing when its input is absent is not a gate.
fn link_witness(dir: &PathBuf, which: &str, j: usize) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let read = |name: String| {
        let path = dir.join(&name);
        std::fs::read_to_string(&path).unwrap_or_else(|e| {
            panic!(
                "{which} chain-link witness {} missing ({e}).\n\
                 Emit links 0..1 of BOTH chains first (COMPILED — the interpreter costs minutes \
                 per link):\n  \
                 cd metatheory && lake build mina_chain_emit mina_fp_chain_emit\n  \
                 ./.lake/build/bin/mina_chain_emit ../circuit/tests/fixtures/pasta-fq-chainlink 2\n  \
                 ./.lake/build/bin/mina_fp_chain_emit ../circuit/tests/fixtures 2",
                path.display()
            )
        })
    };
    let trace: Vec<Vec<BabyBear>> = read(format!("link-{j}-trace.txt"))
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(felts)
        .collect();
    let pis: Vec<BabyBear> = felts(
        read(format!("link-{j}-pis.txt"))
            .lines()
            .find(|l| !l.trim().is_empty())
            .expect("a link PI file has one non-empty line"),
    );
    assert_eq!(
        pis.len(),
        CHAIN_PI_COUNT,
        "{which} link {j} must carry {CHAIN_PI_COUNT} public inputs"
    );
    (trace, pis)
}

/// ⚑⚑ **A CHILD OF THE SAME SHAPE AND DIFFERENT CONSTANTS IS REFUSED BY THE FOLD ITSELF.**
///
/// The control and the adversary fold the SAME two children with the SAME expose hook; the only
/// difference between the two runs is which VK the pins name. So the refusal is the pin's and
/// nothing else's — stated this way because a theorem can be true about the wrong object.
#[test]
fn a_same_shape_different_constants_child_is_refused_by_the_vk_pin() {
    let config = chain_config();
    let fq_desc = chain_link_descriptor().expect("Fq chain-link descriptor");
    let fp_desc = fp_chain_link_descriptor().expect("Fp chain-link descriptor");

    // ── the four leaves ──────────────────────────────────────────────────────────────────────
    let t = Instant::now();
    let (fq0_t, fq0_p) = link_witness(&fq_dir(), "Fq", 0);
    let (fq1_t, fq1_p) = link_witness(&fq_dir(), "Fq", 1);
    let (fp0_t, fp0_p) = link_witness(&fp_dir(), "Fp", 0);
    let (fp1_t, fp1_p) = link_witness(&fp_dir(), "Fp", 1);
    println!("\n§1 witnesses read in {} ms", t.elapsed().as_millis());

    let wrap = |desc: &_, trace: &Vec<Vec<BabyBear>>, pis: &Vec<BabyBear>, label: &str| {
        let t = Instant::now();
        let out = prove_chain_link_leaf_with(desc, trace, pis, &config)
            .unwrap_or_else(|e| panic!("{label} leaf wrap: {e}"));
        println!("  {label:<10} leaf wrap {:>7} ms", t.elapsed().as_millis());
        out
    };
    let fq0 = wrap(&fq_desc, &fq0_t, &fq0_p, "Fq link 0");
    let fq1 = wrap(&fq_desc, &fq1_t, &fq1_p, "Fq link 1");
    let fp0 = wrap(&fp_desc, &fp0_t, &fp0_p, "Fp link 0");
    let fp1 = wrap(&fp_desc, &fp1_t, &fp1_p, "Fp link 1");

    // ── the substitution is invisible to every gate that is NOT the pin ───────────────────────
    // Both leaves publish a well-formed 200-lane chain claim, so `require_chain_claim` — the only
    // host gate `fold_chain_links` runs — cannot tell them apart.
    assert!(
        read_chain_claim(&fq0).is_some() && read_chain_claim(&fp0).is_some(),
        "both leaves publish a readable chain claim; the shape gate does not separate them"
    );
    // ⚑ MEASURED, not asserted from a guess: whether a LEAF-wrap `RecursionVk` separates the two
    // descriptors is a different question from whether a FOLD does, and this repo's rule is to
    // measure what reality decides. Printed here and reported; the pin's verdict below does not
    // depend on the answer either way.
    let fq_leaf_vk = recursion_vk_fingerprint(&fq0.0);
    let fp_leaf_vk = recursion_vk_fingerprint(&fp0.0);
    println!(
        "  leaf-wrap RecursionVk  Fq {}\n  leaf-wrap RecursionVk  Fp {}\n  → leaf fingerprints {}",
        fq_leaf_vk.to_hex(),
        fp_leaf_vk.to_hex(),
        if fq_leaf_vk == fp_leaf_vk {
            "AGREE (a leaf anchor cannot separate the two descriptors)"
        } else {
            "DIFFER (a leaf anchor separates them; the fold's parent VK is the layer at issue)"
        }
    );

    // ⚑ …and the thing the pin acts on DOES differ. Asserted BEFORE any verdict is read.
    let fq_commit =
        child_vk_commit(&fq0, "Fq leaf").expect("Fq leaf has a preprocessed commitment");
    let fq1_commit =
        child_vk_commit(&fq1, "Fq leaf 1").expect("Fq leaf 1 has a preprocessed commitment");
    let fp_commit =
        child_vk_commit(&fp0, "Fp leaf").expect("Fp leaf has a preprocessed commitment");
    assert_eq!(
        fq_commit, fq1_commit,
        "two leaves of the SAME descriptor share a preprocessed commitment — otherwise the pin \
         would be a per-witness value and could not name a circuit at all"
    );
    assert_ne!(
        fq_commit, fp_commit,
        "⚑ THE ADVERSARY MUST ACTUALLY DIFFER IN THE PINNED VALUE. If these were equal the pin \
         would have nothing to refuse and every verdict below would be vacuous."
    );
    println!("  ⚑ the two leaves' preprocessed commitments DIFFER — the pin has something to bite");

    // ── the CONTROL: the Fp pair folds when the pins name the Fp circuit ──────────────────────
    let t = Instant::now();
    let control = fold_chain_links(
        &fp0,
        &fp1,
        &FoldVkPins::tracked(&fp0, &fp1).expect("both children carry a preprocessed commitment"),
        &config,
    )
    .expect(
        "the CONTROL must land: the Fp pair is chain-continuous and every constraint of this \
         parent circuit other than the pin has a satisfying assignment",
    );
    let control_ms = t.elapsed().as_millis();
    verify_recursive_batch_proof_with_config(&control.0, &config)
        .expect("the control fold's root verifies");
    println!("  CONTROL  (Fp children, Fp pins)  LANDED   {control_ms:>7} ms");

    // ── the ADVERSARY: the same two children, pinned to the Fq circuit ────────────────────────
    let t = Instant::now();
    let adversary = fold_chain_links(
        &fp0,
        &fp1,
        &FoldVkPins::new(fq_commit.clone(), fq_commit.clone()),
        &config,
    );
    let adversary_ms = t.elapsed().as_millis();
    let err = match adversary {
        Ok(_) => panic!(
            "⚑ A FOLD PINNED TO THE Fq CHAIN-LINK CIRCUIT ACCEPTED TWO Fp CHILDREN. The pin is \
             not biting: the tower proves \"some circuit of this shape ran\", not \"our chain-link \
             descriptor ran\"."
        ),
        Err(e) => e,
    };
    println!("  ADVERSARY (Fp children, Fq pins) REFUSED  {adversary_ms:>7} ms\n    {err}");

    // ── and the honest Fq fold still lands, so the pin has not simply broken the fold ─────────
    let t = Instant::now();
    let honest = fold_chain_links(
        &fq0,
        &fq1,
        &FoldVkPins::new(fq_commit.clone(), fq_commit.clone()),
        &config,
    )
    .expect("the honest Fq fold, pinned to the RECORDED Fq leaf commitment, must land");
    let honest_ms = t.elapsed().as_millis();
    verify_recursive_batch_proof_with_config(&honest.0, &config)
        .expect("the honest pinned fold's root verifies");
    println!("  HONEST   (Fq children, Fq pins)  LANDED   {honest_ms:>7} ms");

    // ⚑ CONSEQUENCE (2), as far as it can be measured here. The control and the honest fold build
    // structurally identical parent circuits — same child table shapes, same expose hook, same
    // connects — and differ only in the VALUES the pin's `alloc_const`s carry. So a difference in
    // the parent `RecursionVk` is the pinned value reaching the fingerprint a consumer anchors.
    // ⚠ This is weaker than an isolation: the two runs also fold different children, and it is the
    // children's SHAPES agreeing (not their identity) that makes the attribution hold.
    let control_vk = recursion_vk_fingerprint(&control.0);
    let honest_vk = recursion_vk_fingerprint(&honest.0);
    assert_ne!(
        control_vk, honest_vk,
        "⚑ TWO FOLDS OVER DIFFERENT CHILD CIRCUITS MINTED THE SAME PARENT VK. That is the defect \
         in its original form: a consumer's fingerprint anchor cannot then tell an Fp-chain root \
         from an Fq-chain one, and the pin is not reaching the fingerprint."
    );
    println!(
        "  parent RecursionVk  Fp-fold {}\n  parent RecursionVk  Fq-fold {}\n  → parent \
         fingerprints DIFFER",
        control_vk.to_hex(),
        honest_vk.to_hex()
    );

    println!(
        "\n§1 ⚑ THE PIN IS THE REFUSING CONSTRAINT.\n  \
         Same children, same expose hook, same claim lanes, same state carry — the control landed \
         and the adversary did not.\n  \
         Cost: {VK_PIN_FELTS_PER_CHILD} `alloc_const` + {VK_PIN_FELTS_PER_CHILD} `connect` per \
         child, {} + {} per 2-to-1 fold.\n  \
         Fold wall clock: control {control_ms} ms · honest {honest_ms} ms · refusal \
         {adversary_ms} ms.",
        2 * VK_PIN_FELTS_PER_CHILD,
        2 * VK_PIN_FELTS_PER_CHILD
    );
}
