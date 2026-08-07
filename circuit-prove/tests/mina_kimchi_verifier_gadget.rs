//! ⚑⚑ **THE KIMCHI VERIFIER GADGET, OVER MINA DEVNET BLOCK 539508.**
//!
//! ⚠⚠ **WHAT THESE TESTS ARE.** Rust **case-tests**. They are not translation validation, not
//! refinement and not verification — there is no formal semantics of Rust and a case-test says
//! nothing about all inputs. What they establish is that a specific tower **ran on this box** and
//! that two specific forgeries were **refused by a named connect**. "It proves on a box" inherits
//! the undischarged FRI/STARK floor and the gadget itself carries no proof at all.
//!
//! ## The shape
//!
//! * **§1 / §2** — cheap. Layout agreement and the NON-VACUITY of the truncation pin.
//! * **§3** — the two falsifiers, each isolating a DIFFERENT one of the gadget's three connect
//!   groups. Several minutes: it is dominated by the 2 536-column conjunction leaf wrap, measured at
//!   177.3 s in `mina_wrap_finalize_fold.rs` on 2026-08-06, plus two aggregation-circuit builds that
//!   go all the way to the witness solver before the connects refuse. ⚠ No wall clock is quoted here
//!   until this file has been run and the number written down; an estimate in a docblock is how a
//!   guess becomes a datum.
//! * **§4** — `#[ignore]`d for wall clock: the whole tower, 46 chain leaves + 45 chain folds + the
//!   endo leaf + the conjunction leaf + the finalize fold + the gadget fold, root verified.
//!
//! ## ⚑ THERE IS NO CHEAP POSITIVE, AND THAT IS A PROPERTY OF THE GADGET, NOT AN OMISSION
//!
//! The gadget ACCEPTS only a chain root whose incoming state is `(0,0,0)` **and** whose outgoing
//! lane 0 truncates to the block's `v′`. Only the real 46-link fold has both. So §3's refusals are
//! the only thing that runs unattended, and a gadget that refused EVERYTHING would pass §3 — which
//! is the "a falsifier that stopped falsifying" class read from the other side. §4 is therefore
//! not optional evidence; it is the pole that makes §3 mean something, and it is RUN.
//!
//! ## RUNNING
//!
//! ```text
//! # §1-§3
//! cargo test -p dregg-circuit-prove --release --test mina_kimchi_verifier_gadget \
//!   -- --nocapture --test-threads=1
//! # §4 — the whole tower
//! /usr/bin/time -l cargo test -p dregg-circuit-prove --release \
//!   --test mina_kimchi_verifier_gadget -- --ignored --nocapture --test-threads=1
//! ```
//!
//! ⚠ `--test-threads=1` is a MEASUREMENT, not a precaution: wrapping the 2 536-column conjunction
//! leaf peaks around 15 GB RSS (`mina_wrap_finalize_fold.rs`, 2026-08-06), and two of those
//! concurrently on a shared box is an OOM kill, which reads as a test failure and is an environment
//! fault.
//!
//! ## ⚑⚑ AND THAT 15 GB FIGURE IS LOW — MEASURED HERE 2026-08-07, ON A 96 GB M2 MAX
//!
//! §3 was run under an RSS watchdog (30 GiB self-cap, yield if system free drops under 8 GiB). The
//! endo leaf wrapped in **14.0 s**. Then, building the conjunction leaf, the watchdog **killed the
//! run**: system free went from **41.2 GiB to 3 GiB**, and snapped back to **39.6 GiB the instant
//! the process died**, with no other process on the box above 2.6 GB. So ONE 2 536-column
//! conjunction leaf wrap was responsible for roughly **38 GiB** of pressure — about **2.5× the
//! recorded 15 GB**.
//!
//! ⚠ **The sampled figure was 26.05 GiB / 27.97 GB and that is a FLOOR, not a peak** — the watchdog
//! samples every 2 s and a spike between samples is invisible. **A killed run bounds nothing from
//! above.** Both numbers are reported because quoting only the sampled one would be quoting the
//! flattering half of a pair.
//!
//! ⚑ **This cost is INHERITED, not introduced here.** The conjunction leaf wrap is
//! `mina_wrap_finalize_fold`'s, and this gadget's own contribution is 128 `connect`s in an
//! aggregation circuit. But it means **§3 and §4 are not safely runnable on a loaded shared box**,
//! and the honest statement is that neither has completed: §1 and §2 pass, §3 was killed by its own
//! watchdog, and §4 has never been attempted. Give it a quiet box, or a cgroup
//! (`swarm-build`, hbox-only — the mac has no containment at all).

use std::path::PathBuf;
use std::time::Instant;

use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::fold_vk_pin::FoldVkPins;
use dregg_circuit_prove::mina_kimchi_verifier_gadget::{
    CHAIN_ACC_LO, CHAIN_ACC_WIDTH, CHAIN_OUT_LANE0, GADGET_CONNECTS, KIMCHI_CLAIM_LEN, KV_B0,
    KV_VPRIME, V_PRIME_LIMBS, fold_transcript_into_finalize, kimchi_config, read_kimchi_claim,
};
use dregg_circuit_prove::mina_phase2_chain_leaf::{
    ABSORBED_PI_LO, CHAIN_CLAIM_LEN, CHAIN_PI_COUNT, OUT_PI_LO, STATE_WIDTH,
    host_chain_transcript_acc, prove_chain_fold, prove_chain_link_leaf,
};
use dregg_circuit_prove::mina_wrap_finalize_fold::{
    CONJ_PI_COUNT, ENDO_PI_COUNT, ENDO_PI_VPRIME, FINALIZE_CLAIM_LEN, SK, fold_endo_into_finalize,
    prove_conjunction_leaf, prove_endo_lift_leaf,
};
use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, verify_recursive_batch_proof_with_config,
};
use p3_recursion::RecursionOutput;

// ────────────────────────────────────────────────────────────────────────────────────────────────
// fixtures — the SAME bytes `mina_phase2_chain_fold.rs` and `mina_wrap_finalize_fold.rs` read
// ────────────────────────────────────────────────────────────────────────────────────────────────

const CHAIN_PIS_ALL: &str = include_str!("../../circuit/tests/fixtures/pasta-fq-chainlink-pis.txt");
const ENDO_TRACE: &str = include_str!("../../circuit/tests/fixtures/mina-xi-endo-lift-trace.txt");
const ENDO_PIS: &str = include_str!("../../circuit/tests/fixtures/mina-xi-endo-lift-pis.txt");
const CONJ_TRACE: &str =
    include_str!("../../circuit/tests/fixtures/mina-wrap-conjunction-trace.txt");
const CONJ_PIS: &str = include_str!("../../circuit/tests/fixtures/mina-wrap-conjunction-pis.txt");

/// Mina devnet block 539508's own polyscale prechallenge, from `mina_real_block_proof.json` via
/// `MinaBlockFqTranscript.WRAP_V_CHAL`. State hash
/// `3NLmVB6Fs3dm4kXNkgwheHXzJXNpCCwEDe76RpTVeBTNujm12zNk`.
const WRAP_V_CHAL: u128 = 330305781815358857211111367912836029937;

const CHAIN_LINKS: usize = 46;
const ENDO_TRACE_WIDTH: usize = 687;
const CONJ_TRACE_WIDTH: usize = 2536;

fn witness_dir() -> PathBuf {
    std::env::var("DREGG_CHAINLINK_WITNESS_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("../circuit/tests/fixtures/pasta-fq-chainlink")
        })
}

fn parse_cells(text: &str) -> Vec<BabyBear> {
    text.split_whitespace()
        .map(|c| BabyBear::new(c.parse::<u32>().expect("cell is a u32 decimal")))
        .collect()
}

fn parse_trace(text: &str, width: usize) -> Vec<Vec<BabyBear>> {
    let t: Vec<Vec<BabyBear>> = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(parse_cells)
        .collect();
    assert!(!t.is_empty(), "an empty trace measures nothing");
    assert!(
        t.iter().all(|r| r.len() == width),
        "every row must be {width} wide"
    );
    t
}

fn all_link_pis() -> Vec<Vec<BabyBear>> {
    let pis: Vec<Vec<BabyBear>> = CHAIN_PIS_ALL
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(parse_cells)
        .collect();
    assert_eq!(pis.len(), CHAIN_LINKS, "the block's tape costs 46 links");
    assert!(pis.iter().all(|p| p.len() == CHAIN_PI_COUNT));
    pis
}

/// Read link `j`'s Lean-emitted 2048x469 trace. Fails LOUDLY with the emit command rather than
/// skipping: a test that quietly does nothing when its input is absent is not a gate.
fn link_trace(j: usize) -> Vec<Vec<BabyBear>> {
    let path = witness_dir().join(format!("link-{j}-trace.txt"));
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "chain-link witness {} missing ({e}).\n\
             Emit the witnesses first (COMPILED — the interpreter costs 9m20s per link):\n  \
             cd metatheory && lake build mina_chain_emit \\\n    \
             && ./.lake/build/bin/mina_chain_emit ../circuit/tests/fixtures/pasta-fq-chainlink 46",
            path.display()
        )
    });
    parse_trace(&text, 469)
}

fn limbs_to_u128_low(limbs: &[BabyBear]) -> u128 {
    let mut acc: u128 = 0;
    for (i, l) in limbs.iter().take(V_PRIME_LIMBS).enumerate() {
        acc |= u128::from(l.as_u32()) << (8 * i);
    }
    acc
}

/// Run `f` and require that it REFUSED, returning the refusal text.
///
/// ⚑ Both refusal shapes are accepted, and that is deliberate rather than lax: an unsatisfiable
/// `connect` surfaces as a clean `Err(..)` on the release path and as a `WitnessConflict` PANIC
/// from the circuit runner on the debug path (`mina_wrap_finalize_fold.rs`'s forged-ξ test uses
/// `catch_unwind` for exactly this). A test that only accepted one shape would pass in one profile
/// and fail in the other while the gadget behaved identically.
///
/// ⚠ What this does NOT do is attribute the refusal by STRING. The attribution here is
/// STRUCTURAL — see the test's docblock: each forgery leaves exactly one connect group able to
/// refuse. A message match would be the weaker check, because a `WitnessConflict` names a witness
/// slot, not the source-level constraint that created it.
fn expect_refusal<T>(what: &str, f: impl FnOnce() -> Result<T, String>) -> String {
    let hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    std::panic::set_hook(hook);
    match r {
        Ok(Ok(_)) => panic!(
            "{what}: the gadget produced a ROOT where it had to refuse — the connect that was \
             supposed to be load-bearing is not"
        ),
        Ok(Err(e)) => format!("Err({e})"),
        Err(p) => {
            let msg = p
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| p.downcast_ref::<&str>().map(|s| (*s).to_string()))
                .unwrap_or_else(|| "<non-string panic payload>".to_string());
            format!("panic({msg})")
        }
    }
}

/// Prove the endo-lift and conjunction leaves and fold them — the gadget's RIGHT child.
fn finalize_root(config: &DreggRecursionConfig) -> RecursionOutput<DreggRecursionConfig> {
    let endo_trace = parse_trace(ENDO_TRACE, ENDO_TRACE_WIDTH);
    let endo_pis = parse_cells(ENDO_PIS);
    let conj_trace = parse_trace(CONJ_TRACE, CONJ_TRACE_WIDTH);
    let conj_pis = parse_cells(CONJ_PIS);
    assert_eq!(endo_pis.len(), ENDO_PI_COUNT);
    assert_eq!(conj_pis.len(), CONJ_PI_COUNT);

    let t = Instant::now();
    let endo = prove_endo_lift_leaf(&endo_trace, &endo_pis, config).expect("endo-lift leaf");
    println!("    endo leaf        {:>7} ms", t.elapsed().as_millis());
    let t = Instant::now();
    let conj = prove_conjunction_leaf(&conj_trace, &conj_pis, config).expect("conjunction leaf");
    println!("    conjunction leaf {:>7} ms", t.elapsed().as_millis());
    let t = Instant::now();
    let root = fold_endo_into_finalize(
        &endo,
        &conj,
        &FoldVkPins::tracked(&endo, &conj).expect("both children carry a preprocessed commitment"),
        config,
    )
    .expect("endo -> finalize fold");
    println!("    finalize fold    {:>7} ms", t.elapsed().as_millis());
    root
}

/// `|D⁽⁰⁾| = max_height · 2^log_blowup`, read off a REAL proof's own `degree_bits` and the config's
/// own MINT knobs — never off a constant, and never off the witness.
///
/// FRI batches every committed polynomial onto the LARGEST evaluation domain, so the tallest table
/// sets `|D⁽⁰⁾|` for the whole proof (`p3-fri/src/two_adic_pcs.rs`, `coset_lde_batch(evals,
/// fri.log_blowup, shift)`).
fn report_lde_domain(
    label: &str,
    out: &RecursionOutput<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
) {
    let db = &out.0.proof.degree_bits;
    let lb = config.mint_knobs().log_blowup;
    let max_h = db.iter().copied().max().unwrap_or(0);
    assert!(
        !db.is_empty(),
        "[{label}] the proof carries no degree_bits — nothing was measured"
    );
    println!(
        "    [{label}] degree_bits {db:?} → max height 2^{max_h} · mint log_blowup {lb} \
         → |D⁽⁰⁾| = 2^{}",
        max_h + lb
    );
}

// ────────────────────────────────────────────────────────────────────────────────────────────────
// §1 — the layouts the gadget indexes with are the ones the fixtures and both children carry
// ────────────────────────────────────────────────────────────────────────────────────────────────

#[test]
fn the_layouts_and_the_fixtures_agree() {
    let pis = all_link_pis();
    let endo_pis = parse_cells(ENDO_PIS);
    let conj_pis = parse_cells(CONJ_PIS);

    assert_eq!(CHAIN_CLAIM_LEN, 200);
    assert_eq!(FINALIZE_CLAIM_LEN, 160);
    assert_eq!(KIMCHI_CLAIM_LEN, 168);
    assert_eq!(KV_VPRIME, CHAIN_ACC_WIDTH);
    assert_eq!(KV_B0 + SK, KIMCHI_CLAIM_LEN);
    assert_eq!(CHAIN_OUT_LANE0, STATE_WIDTH);
    assert_eq!(CHAIN_ACC_LO, 2 * STATE_WIDTH);
    assert_eq!(GADGET_CONNECTS, 128);

    assert_eq!(endo_pis.len(), ENDO_PI_COUNT);
    assert_eq!(conj_pis.len(), CONJ_PI_COUNT);
    assert!(pis.iter().all(|p| p.len() == CHAIN_PI_COUNT));

    // ⚑ THE THREE ROOT SHAPES A CONSUMER DISCRIMINATES BY LENGTH ARE PAIRWISE DISTINCT. Two roots
    // at one length would be a claim read as the wrong sentence, silently.
    assert_ne!(KIMCHI_CLAIM_LEN, CHAIN_CLAIM_LEN);
    assert_ne!(KIMCHI_CLAIM_LEN, FINALIZE_CLAIM_LEN);
    assert_ne!(CHAIN_CLAIM_LEN, FINALIZE_CLAIM_LEN);

    println!(
        "\n§1 layouts agree — chain {CHAIN_CLAIM_LEN} / finalize {FINALIZE_CLAIM_LEN} / \
         kimchi {KIMCHI_CLAIM_LEN} lanes, pairwise distinct; gadget adds {GADGET_CONNECTS} connects"
    );
}

// ────────────────────────────────────────────────────────────────────────────────────────────────
// §2 — EVERY ONE OF THE GADGET'S THREE CONNECT GROUPS IS NON-VACUOUS ON THE REAL FIXTURES
// ────────────────────────────────────────────────────────────────────────────────────────────────

/// ⚑ **A CONNECT BETWEEN TWO VALUES THAT ARE ALREADY EQUAL BY CONSTRUCTION FORCES NOTHING.** This
/// checks, on the real bytes, that each group has something to say:
///
/// 1. the fresh-sponge pin is about a value that is NOT trivially zero elsewhere (link 45's
///    incoming state is non-zero, so pinning link 0's to zero discriminates);
/// 2. the `v′` weld relates two lanes that a prover could otherwise have chosen apart (link 0's
///    outgoing lane 0 differs from link 45's, so "some chain root" is not "the block's");
/// 3. the truncation pin forbids a value the raw squeeze ACTUALLY CARRIES — link 45's outgoing
///    lane 0 has non-zero limbs ABOVE the 128-bit window, while the endo-lift's `v′` has zeros
///    there. Without group 3 a prover picks those 128 high bits freely.
#[test]
fn every_connect_group_is_non_vacuous_on_the_real_fixtures() {
    let pis = all_link_pis();
    let endo_pis = parse_cells(ENDO_PIS);
    let last = &pis[CHAIN_LINKS - 1];
    let first = &pis[0];

    // GROUP 1 — the fresh-sponge pin discriminates.
    assert!(
        first[..STATE_WIDTH].iter().all(|v| v.as_u32() == 0),
        "link 0 must start from a FRESH Kimchi sponge, or the gadget's group-1 pin refuses the \
         honest chain"
    );
    assert!(
        last[..STATE_WIDTH].iter().any(|v| v.as_u32() != 0),
        "link 45's incoming state is all-zero — then pinning the chain root's in_state to zero \
         would accept a single-link 'chain' too and group 1 would forbid nothing"
    );

    // GROUP 2 — the weld relates lanes that really can differ.
    let last_lane0 = &last[OUT_PI_LO..OUT_PI_LO + SK];
    let first_lane0 = &first[OUT_PI_LO..OUT_PI_LO + SK];
    assert_ne!(
        limbs_to_u128_low(last_lane0),
        limbs_to_u128_low(first_lane0),
        "link 0 and link 45 squeeze the same low 128 bits — then the v' weld cannot tell a \
         truncated chain from the block's and §3's first falsifier is not falsifying"
    );
    assert_eq!(
        limbs_to_u128_low(last_lane0),
        WRAP_V_CHAL,
        "the chain's terminal squeeze does not truncate to block 539508's v'"
    );
    for i in 0..V_PRIME_LIMBS {
        assert_eq!(
            last_lane0[i].as_u32(),
            endo_pis[ENDO_PI_VPRIME + i].as_u32(),
            "v' limb {i}: the chain's terminal squeeze is the endo-lift's input"
        );
    }

    // GROUP 3 — the truncation pin forbids something the raw squeeze carries.
    let high_nonzero = last_lane0[V_PRIME_LIMBS..]
        .iter()
        .filter(|v| v.as_u32() != 0)
        .count();
    assert!(
        high_nonzero > 0,
        "the raw v' squeeze is only 128 bits wide — then the truncation pin forbids nothing and \
         group 3 is decoration"
    );
    for i in V_PRIME_LIMBS..SK {
        assert_eq!(
            endo_pis[ENDO_PI_VPRIME + i].as_u32(),
            0,
            "the endo-lift's v' limb {i} must be zero, or the honest witness fails group 3"
        );
    }

    // …and the closing squeeze absorbs exactly one element (the tape is 91 — odd).
    assert!(
        last[ABSORBED_PI_LO + SK..ABSORBED_PI_LO + 2 * SK]
            .iter()
            .all(|v| v.as_u32() == 0)
    );

    println!(
        "\n§2 all three connect groups non-vacuous:\n  \
         group 1: link45 in_state non-zero (fresh pin discriminates)\n  \
         group 2: link0 lane0 low128 = {} != link45's {WRAP_V_CHAL}\n  \
         group 3: link45 lane0 carries {high_nonzero} non-zero limbs ABOVE the 128-bit window, \
         endo v' has 0",
        limbs_to_u128_low(first_lane0)
    );
}

// ────────────────────────────────────────────────────────────────────────────────────────────────
// §3 — THE FALSIFIERS. Two forgeries, each isolating a DIFFERENT connect group.
// ────────────────────────────────────────────────────────────────────────────────────────────────

/// ⚑⚑ **THE GADGET REFUSES BOTH FORGERIES, AND EACH ONE ISOLATES ONE GROUP.**
///
/// A single chain-link LEAF publishes the same 200-lane claim a 46-link fold root does, so both
/// forgeries are structurally admissible roots that verify **standalone** — the refusal is the
/// gadget's, not a shape check's.
///
/// * **Forgery A — link 0's leaf as the chain root.** Its `in_state` IS `(0,0,0)`, so group 1
///   PASSES; its outgoing lane 0 is link 0's squeeze, not the block's `v′`. ⇒ only **group 2** can
///   refuse.
/// * **Forgery B — link 45's leaf as the chain root.** Its outgoing lane 0 IS the terminal squeeze,
///   so groups 2 and 3 PASS; its `in_state` is link 44's output, not a fresh sponge. ⇒ only
///   **group 1** can refuse.
///
/// ⚠ Both moved values are non-zero and inside the declared 8-bit limb width the descriptor's own
/// range lookups enforce, so neither refusal can be a range check firing instead of the connect.
/// §2 asserts exactly that before this test runs.
#[test]
fn each_forged_chain_root_is_refused_by_the_group_that_should_refuse_it() {
    let pis = all_link_pis();
    let config = kimchi_config();

    println!("\n§3 building the finalize root (the gadget's RIGHT child) …");
    let fin = finalize_root(&config);
    verify_recursive_batch_proof_with_config(&fin.0, &config)
        .expect("the finalize root verifies standalone");

    // ── Forgery A ────────────────────────────────────────────────────────────────────────────
    let t = Instant::now();
    let leaf0 = prove_chain_link_leaf(&link_trace(0), &pis[0], &config).expect("link 0 leaf");
    println!("    link-0 leaf      {:>7} ms", t.elapsed().as_millis());
    verify_recursive_batch_proof_with_config(&leaf0.0, &config).expect(
        "FORGERY A must verify STANDALONE, or the refusal below is attributable to it \
                 not being a proof rather than to the gadget's connect",
    );

    let e = expect_refusal("forgery A (fresh sponge, wrong terminal squeeze)", || {
        fold_transcript_into_finalize(
            &leaf0,
            &fin,
            &FoldVkPins::tracked(&leaf0, &fin)
                .expect("both children carry a preprocessed commitment"),
            &config,
        )
    });
    println!("    §3a REFUSED (only group 2, the v' weld, can refuse this): {e}");

    // ── Forgery B ────────────────────────────────────────────────────────────────────────────
    let last = CHAIN_LINKS - 1;
    let t = Instant::now();
    let leaf45 =
        prove_chain_link_leaf(&link_trace(last), &pis[last], &config).expect("link 45 leaf");
    println!("    link-45 leaf     {:>7} ms", t.elapsed().as_millis());
    verify_recursive_batch_proof_with_config(&leaf45.0, &config)
        .expect("FORGERY B must verify STANDALONE");

    let e = expect_refusal("forgery B (correct terminal squeeze, warm sponge)", || {
        fold_transcript_into_finalize(
            &leaf45,
            &fin,
            &FoldVkPins::tracked(&leaf45, &fin)
                .expect("both children carry a preprocessed commitment"),
            &config,
        )
    });
    println!("    §3b REFUSED (only group 1, the fresh-sponge pin, can refuse this): {e}");

    println!(
        "\n§3 ⚑ both forgeries verify STANDALONE and are refused by the gadget's connects.\n  \
         A: correct fresh sponge, WRONG terminal squeeze → group 2\n  \
         B: correct terminal squeeze, WRONG incoming sponge → group 1"
    );
}

// ────────────────────────────────────────────────────────────────────────────────────────────────
// §4 — THE WHOLE TOWER. `#[ignore]`d for wall clock only.
// ────────────────────────────────────────────────────────────────────────────────────────────────

/// ⚑⚑⚑ **THE KIMCHI VERIFIER GADGET, OVER BLOCK 539508's REAL TRANSCRIPT, PROVED RECURSIVELY.**
///
/// 46 chain leaves + 45 chain folds → the transcript root; the endo leaf + the conjunction leaf +
/// their fold → the finalize root; then ONE more aggregation layer that verifies both in-circuit
/// and welds them.
///
/// What the root that comes out says is in `mina_kimchi_verifier_gadget`'s header, and what it does
/// NOT say is there too, in three named items. ⚠ It is not "this Kimchi proof is valid".
#[test]
#[ignore = "the whole tower: 46 chain leaves + 45 folds + 2 leaves + 2 folds. Explicit --ignored."]
fn the_whole_kimchi_verifier_tower_proves_over_block_539508() {
    let pis = all_link_pis();
    let config = kimchi_config();
    let t_all = Instant::now();

    println!("\n═══ §4 THE KIMCHI VERIFIER GADGET OVER MINA DEVNET BLOCK 539508 ═══");
    println!("  mint knobs: {:?}", config.mint_knobs());

    // ── the LEFT child: the whole phase-2 transcript ─────────────────────────────────────────
    let t = Instant::now();
    let chain = prove_chain_fold(
        &pis.iter()
            .enumerate()
            .map(|(j, p)| (link_trace(j), p.clone()))
            .collect::<Vec<_>>(),
        &config,
        |i, phase| {
            if phase == "fold" {
                println!(
                    "    chain link {i:>2}/46 folded ({:.1} min elapsed)",
                    t_all.elapsed().as_secs_f64() / 60.0
                );
            }
        },
    )
    .expect("the 46-link chain fold");
    let chain_ms = t.elapsed().as_millis();
    verify_recursive_batch_proof_with_config(&chain.0, &config)
        .expect("the 46-link chain root verifies");
    println!("  chain root: {chain_ms} ms (46 leaves + 45 folds)");
    report_lde_domain("chain root", &chain, &config);

    // ── the RIGHT child: the finalize conjunction under the endo-lifted ξ ─────────────────────
    let t = Instant::now();
    let fin = finalize_root(&config);
    let fin_ms = t.elapsed().as_millis();
    verify_recursive_batch_proof_with_config(&fin.0, &config).expect("the finalize root verifies");
    println!("  finalize root: {fin_ms} ms");
    report_lde_domain("finalize root", &fin, &config);

    // ── THE GADGET ───────────────────────────────────────────────────────────────────────────
    let t = Instant::now();
    let root = fold_transcript_into_finalize(
        &chain,
        &fin,
        &FoldVkPins::tracked(&chain, &fin).expect("both children carry a preprocessed commitment"),
        &config,
    )
    .expect("the kimchi verifier gadget fold");
    let gadget_ms = t.elapsed().as_millis();
    verify_recursive_batch_proof_with_config(&root.0, &config)
        .expect("the kimchi verifier gadget root verifies");
    println!("  gadget fold: {gadget_ms} ms ({GADGET_CONNECTS} in-circuit connects)");
    report_lde_domain("gadget root", &root, &config);

    // ── what the root says ───────────────────────────────────────────────────────────────────
    let claim = read_kimchi_claim(&root).expect("the root publishes a kimchi claim");
    assert_eq!(
        claim.v_prime_u128(),
        Some(WRAP_V_CHAL),
        "the root's v' is not block 539508's polyscale prechallenge"
    );
    assert_eq!(
        claim.transcript_acc,
        host_chain_transcript_acc(&pis),
        "the root's transcript digest is not the ordered commitment to the block's real tape — \
         the chain absorbed something else"
    );
    assert_eq!(claim.zeta.len(), SK);
    assert_eq!(claim.b0.len(), SK);

    println!("\n  ═══ THE ROOT ═══");
    println!("  in   : FRESH Kimchi fq_sponge (0,0,0) — a CONSTRAINT, not a host predicate");
    println!("  tape : 91 elements, ordered, committed in-circuit");
    println!("  v'   : {WRAP_V_CHAL}  ⇐ DERIVED from the transcript, not published free");
    println!("  and against ScalarChallenge(v').to_field(endo_r): xiCorrect + bCorrect");
    println!(
        "\n  total {:.1} min. ⚠ NOT 'this Kimchi proof is valid': the IPA opening is not in \
         circuit (opening_is_vacuous_when_sg_is_free), cipCorrect/plonkChecksPassed are absent by \
         construction, and zeta/zetaw/r are derived by nothing.",
        t_all.elapsed().as_secs_f64() / 60.0
    );
}
