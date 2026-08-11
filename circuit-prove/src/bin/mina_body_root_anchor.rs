//! ⚑⚑⚑ **THE `state_body_hash` ROOT CEREMONY — mint the root a node anchors, and print the
//! fingerprint it anchors it BY.**
//!
//! ```text
//!   cargo build -p dregg-circuit-prove --release --bin mina_body_root_anchor
//!   ./target/release/mina_body_root_anchor <fixtures-dir> [--plain] [--out root.bin]
//! ```
//!
//! `<fixtures-dir>` is `circuit/tests/fixtures` — it must hold `mina-body-preimage-bits-row.txt`,
//! `mina-body-preimage-bits-pis.txt`, `pasta-fp-bodyhash-pis.txt` and
//! `pasta-fp-bodyhash/link-{j}-trace.txt` for `j` in `0..25`. The 25 traces are ~80 MB and are NOT
//! tracked; re-emit them with
//! `cd metatheory && lake build mina_fp_chain_emit && ./.lake/build/bin/mina_fp_chain_emit ../circuit/tests/fixtures 25`.
//!
//! # ⚑ WHY THIS IS A BINARY AND NOT A TEST, WITH THE MEASUREMENT
//!
//! `node/src/mina_chain_root_backend.rs` told an operator that the body anchor *"is printed by
//! `circuit-prove/tests/mina_body_hash_chain_fold.rs`'s root section"*. **It is not, and never
//! was.** Measured 2026-08-11: that file calls `recursion_vk_fingerprint` in §3 only, over a
//! **two-leaf** fold, and its §4 root section prints the claim and no fingerprint at all. So the
//! documented ceremony for `DREGG_MINA_BODY_ROOT_VK` produced either nothing or a value that
//! refuses every real 25-link root. The anchor a node compares against had no reachable source.
//!
//! A ceremony whose output is a `println!` inside an `#[ignore]`d test is a ceremony nobody can
//! run without reading the test. This is the ceremony as an artifact.
//!
//! # ⚑⚑ THE TWO TOWERS, AND WHY THIS BINARY MINTS BOTH
//!
//! `--plain` folds twenty-five **plain** chain leaves; the default folds twenty-five **adapters**
//! ([`dregg_circuit_prove::mina_body_preimage_adapter::prove_welded_body_hash_chain_fold`]), each
//! welding that link's absorbed pair, limb for limb, to the gated body-preimage descriptor.
//!
//! **The two publish the IDENTICAL 200-lane claim.** That is the adapter's drop-in property and it
//! is also the hazard: nothing downstream — not the fold node, not `read_chain_claim`, not
//! `dregg-turn`'s REFUSAL 16 — can tell a welded root from an unwelded one. The **only**
//! discriminator is the `recursion_vk_fingerprint`, exactly as it is the only thing telling the Fq
//! phase-2 root from an Fp body root. So this binary prints both towers' fingerprints from one
//! build on one box, and an operator who anchors the welded value has a node that refuses the
//! unwelded tower at REFUSAL 16b.
//!
//! ⚠ **AND SAY THE RESIDUAL.** Anchoring is the operator's act. A node handed the PLAIN tower's
//! fingerprint verifies plain roots happily and every gate stays green — the seventeen body slots
//! are still welded (REFUSAL 16), but each link's absorbed pair is back to being whatever the
//! prover said. Nothing in the node can detect that; the flag-day rename of the env var is what
//! stops an old pin from being carried across silently, and it is not a proof that the pin is the
//! welded one.

use std::path::{Path, PathBuf};
use std::time::Instant;

use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::mina_body_preimage_adapter::{
    BODY_BITS_PI_COUNT, BODY_BITS_WIDTH, BODY_LINKS, body_preimage_descriptor,
    prove_welded_body_hash_chain_fold,
};
use dregg_circuit_prove::mina_phase2_chain_leaf::{
    CHAIN_PI_COUNT, OUT_PI_LO, SK, STATE_WIDTH, chain_inner_config, chain_root_config,
    fp_chain_link_descriptor, host_chain_transcript_acc, prove_chain_fold_with, read_chain_claim,
};
use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    recursion_vk_fingerprint, verify_recursive_batch_proof_with_config,
};

/// `MinaStateBodyHashChain.realBodyHash` — the `state_body_hash` of Mina devnet block **540221**,
/// which the honest root's outgoing lane 0 must recompose to. A ceremony that mints a root and
/// does not check WHAT it derived is a ceremony that will happily anchor a wrong circuit.
const REAL_BODY_HASH: &str =
    "5693930022757138716743408081919214747940268519364092084787368564557482288885";

fn decimals(path: &Path, want: usize, what: &str) -> Vec<BabyBear> {
    let text = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("cannot read the {what} at {}: {e}", path.display()));
    let v: Vec<BabyBear> = text
        .split_whitespace()
        .map(|c| {
            BabyBear::new(
                c.parse::<u32>()
                    .unwrap_or_else(|e| panic!("{what}: cell {c:?} is not a u32 decimal: {e}")),
            )
        })
        .collect();
    assert_eq!(
        v.len(),
        want,
        "the {what} at {} is {} cells; expected {want}",
        path.display(),
        v.len()
    );
    v
}

/// One link's trace: `469` columns per line, `2^k` lines.
fn link_trace(dir: &Path, j: usize) -> Vec<Vec<BabyBear>> {
    let path = dir.join(format!("link-{j}-trace.txt"));
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "cannot read link {j}'s trace at {}: {e}\nre-emit with: cd metatheory && lake build \
             mina_fp_chain_emit && ./.lake/build/bin/mina_fp_chain_emit ../circuit/tests/fixtures 25",
            path.display()
        )
    });
    text.lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|c| BabyBear::new(c.parse::<u32>().expect("trace cell is a u32 decimal")))
                .collect()
        })
        .collect()
}

/// Recompose 32 little-endian 8-bit limbs into a DECIMAL string by repeated multiply-add on the
/// decimal digits — no bignum dependency, no intermediate to transcribe wrong.
fn limbs_to_decimal(limbs: &[BabyBear]) -> String {
    let mut digits: Vec<u32> = vec![0];
    for limb in limbs.iter().rev() {
        let mut carry = u64::from(limb.as_u32());
        for d in digits.iter_mut() {
            let v = u64::from(*d) * 256 + carry;
            *d = (v % 10) as u32;
            carry = v / 10;
        }
        while carry > 0 {
            digits.push((carry % 10) as u32);
            carry /= 10;
        }
    }
    while digits.len() > 1 && *digits.last().unwrap() == 0 {
        digits.pop();
    }
    digits
        .iter()
        .rev()
        .map(|d| char::from(b'0' + *d as u8))
        .collect()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut fixtures: Option<PathBuf> = None;
    let mut plain = false;
    let mut out: Option<PathBuf> = None;
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--plain" => plain = true,
            "--out" => {
                i += 1;
                out = Some(PathBuf::from(args.get(i).expect("--out needs a path")));
            }
            other if other.starts_with("--") => panic!("unknown flag {other}"),
            other => fixtures = Some(PathBuf::from(other)),
        }
        i += 1;
    }
    let fixtures = fixtures.unwrap_or_else(|| {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../circuit/tests/fixtures")
    });
    let witness_dir = std::env::var("DREGG_BODYHASH_WITNESS_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| fixtures.join("pasta-fp-bodyhash"));

    let tower = if plain { "PLAIN (unwelded)" } else { "WELDED" };
    println!("═══ mina_body_root_anchor — {tower} state_body_hash tower, {BODY_LINKS} links ═══");
    println!("  fixtures : {}", fixtures.display());
    println!("  witnesses: {}", witness_dir.display());

    // ── The 25 links' public inputs, one line per link, in chain order.
    let pis_text = std::fs::read_to_string(fixtures.join("pasta-fp-bodyhash-pis.txt"))
        .expect("the 25 link PI vectors");
    let link_pis: Vec<Vec<BabyBear>> = pis_text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|c| BabyBear::new(c.parse::<u32>().expect("PI is a u32 decimal")))
                .collect()
        })
        .collect();
    assert_eq!(link_pis.len(), BODY_LINKS);
    assert!(link_pis.iter().all(|p| p.len() == CHAIN_PI_COUNT));

    let load = Instant::now();
    let witnesses: Vec<(Vec<Vec<BabyBear>>, Vec<BabyBear>)> = (0..BODY_LINKS)
        .map(|j| (link_trace(&witness_dir, j), link_pis[j].clone()))
        .collect();
    println!(
        "  {BODY_LINKS} link witnesses loaded in {} s",
        load.elapsed().as_secs()
    );

    let cdesc = fp_chain_link_descriptor().expect("the Lean Fp chain-link descriptor parses");
    let inner = chain_inner_config();
    let t0 = Instant::now();

    let root = if plain {
        prove_chain_fold_with(&cdesc, &witnesses, &inner, |j, phase| {
            if phase == "fold" {
                println!(
                    "  folded {}/{BODY_LINKS} ({} s)",
                    j + 1,
                    t0.elapsed().as_secs()
                );
            }
        })
        .expect("the plain 25-link body-hash fold")
    } else {
        let pdesc = body_preimage_descriptor().expect("the Lean preimage descriptor parses");
        let row = decimals(
            &fixtures.join("mina-body-preimage-bits-row.txt"),
            BODY_BITS_WIDTH,
            "preimage row",
        );
        let claim = decimals(
            &fixtures.join("mina-body-preimage-bits-pis.txt"),
            BODY_BITS_PI_COUNT,
            "preimage claim",
        );
        // ONE real row plus a zero pad row: a zero row satisfies every gate of this descriptor.
        let trace = vec![row, vec![BabyBear::new(0); BODY_BITS_WIDTH]];
        prove_welded_body_hash_chain_fold(
            &pdesc,
            &trace,
            &claim,
            &cdesc,
            &witnesses,
            &inner,
            |j, phase| {
                if phase == "fold" {
                    println!(
                        "  welded {}/{BODY_LINKS} ({} s)",
                        j + 1,
                        t0.elapsed().as_secs()
                    );
                }
            },
        )
        .expect("the welded 25-adapter body-hash fold")
    };
    let total_s = t0.elapsed().as_secs();

    // ── The root VERIFIES, at the engine a node verifies it at. Not the prover's word for it.
    let fold_cfg = chain_root_config();
    verify_recursive_batch_proof_with_config(&root.0, &fold_cfg)
        .expect("the minted root MUST verify under `chain_root_config` — the node's own engine");

    // ── …and it derives the value it is supposed to derive. A ceremony that skips this anchors
    // whatever it built.
    let claim = read_chain_claim(&root).expect("the root publishes a chain claim");
    assert_eq!(
        claim.in_state,
        link_pis[0][..STATE_WIDTH],
        "the root's incoming state must be the `MinaProtoStateBody` salt"
    );
    assert_eq!(
        claim.out_state,
        link_pis[BODY_LINKS - 1][OUT_PI_LO..OUT_PI_LO + STATE_WIDTH],
        "the root's outgoing state must be link 24's"
    );
    assert_eq!(
        claim.transcript_acc,
        host_chain_transcript_acc(&link_pis),
        "the root's transcript digest must be the ordered fold of the 49 absorbed elements"
    );
    let derived = limbs_to_decimal(&claim.out_state[..SK]);
    assert_eq!(
        derived, REAL_BODY_HASH,
        "the root's outgoing lane 0 must be block 540221's `state_body_hash`"
    );

    let vk = recursion_vk_fingerprint(&root.0);

    if let Some(path) = out {
        // ⚑ The wire's own encoding: `MinaHeadProofWire::body_chain_root_proof` is postcard bytes
        // of exactly this type, and `decode_recursive_batch_proof` is what a node reads them with.
        let bytes = postcard::to_allocvec(&root.0).expect("the root postcard-serialises");
        std::fs::write(&path, &bytes).expect("write the root");
        println!(
            "  root written to {} ({} bytes)",
            path.display(),
            bytes.len()
        );
    }

    println!("\n═══ {tower} ROOT MINTED in {total_s} s ═══");
    println!("  in_state : salt(\"MinaProtoStateBody\")");
    println!("  out lane0: {derived}");
    println!("  acc      : {:?}", claim.transcript_acc);
    println!("\n  recursion_vk_fingerprint = {}", vk.to_hex());
    if plain {
        println!(
            "\n  ⚠ THIS IS THE UNWELDED TOWER. Anchoring this value gives a node whose body root\n  \
             says nothing about WHICH preimage each link absorbed. It is printed so the two\n  \
             fingerprints can be compared from one build on one box, not so it can be pinned."
        );
    } else {
        println!(
            "\n  ⚑ export DREGG_MINA_BODY_WELDED_ROOT_VK={}",
            vk.to_hex()
        );
        println!(
            "  ⚠ and it names THIS build's welded circuit. Re-extract after any change to the\n  \
             preimage descriptor, the chain-link descriptor, the seams, the fold engine or the\n  \
             recursion fork — every one of those moves this value and an old pin refuses."
        );
    }
}
