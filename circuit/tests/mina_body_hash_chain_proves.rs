//! ⚑⚑ **`state_body_hash` ON THE DEPLOYED PROVER — and the refusal is the AIR's, not a pre-flight.**
//!
//! ⚑ SUBSTRATE, SAID OUT LOUD (House Law #1): every constraint under test is LEAN-AUTHORED and
//! LEAN-COMPILED (`Dregg2.Circuit.Emit.MinaStateBodyHashChain.bodyChainDesc` **is**
//! `MinaPhase1Chain.chainDesc` by `rfl` — `dregg-pasta-fp-chainlink::v1`, unchanged). This file
//! writes no AIR. It reads the emitted descriptor and the Lean-emitted witnesses and asks the
//! deployed prover/verifier for a verdict.
//!
//! ## What this rung is
//!
//! `LightClientMinaLinkAir` derived `OWNHASH` on 2026-08-06 over `Poseidon_{MinaProtoState}(PARENT,
//! BODYHASH)` and named the residual: *"what it can still choose is `BODYHASH`."* `BODYHASH` is
//! `Poseidon_{MinaProtoStateBody}(pack_input (Body.to_input body))` — **49 packed field elements at
//! rate 2, 25 permutations** (derived, not counted: `MinaStateBodyHashChain.pairsOf_length` at 49,
//! against a standing figure of 26 that double-counted the closing squeeze).
//!
//! ## ⚑ THE THREE THINGS THIS FILE CHECKS THAT NOTHING ELSE COULD
//!
//! 1. **The head is the SALT, checked against openmina's own regression constants.** With a free
//!    incoming state the chain is VACUOUS and not weakly so: `perm` is a permutation, so 25 links
//!    from a chosen head reach every field element. The head pin is the whole domain separation.
//! 2. **The honest link proves on the DEPLOYED rail** (`prove_vm_descriptor2` + `verify_vm_descriptor2`,
//!    `ir2_config`), not only inside a recursion wrapper.
//! 3. ⚑⚑ **The forgery is refused BY THE CIRCUIT.** `prove_vm_descriptor2` runs a producer-side
//!    replay that refuses eagerly — a falsifier that stops there has measured a Rust `assert`, not
//!    an AIR. §3 goes through `prove_vm_descriptor2_unchecked`, which puts the forged witness in
//!    front of the deployed verifier.
//!
//! ## PREREQUISITE — the witnesses
//!
//! `pasta-fp-bodyhash-pis.txt` is TRACKED, so §1 runs with no emit. The 2048x469 traces are not:
//!
//! ```text
//! cd metatheory && lake build mina_fp_chain_emit
//! ./.lake/build/bin/mina_fp_chain_emit ../circuit/tests/fixtures 25
//! ```
//!
//! Run: `cargo test -p dregg-circuit --release --test mina_body_hash_chain_proves -- --nocapture`

use std::path::PathBuf;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TableSem, parse_vm_descriptor2, prove_vm_descriptor2,
    prove_vm_descriptor2_unchecked, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;

const CHAIN_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-fp-chainlink.json");
const BODY_PIS_ALL: &str = include_str!("fixtures/pasta-fp-bodyhash-pis.txt");

/// `MinaStateBodyHashChain.BODY_LINKS` — `⌈49/2⌉`, derived.
const BODY_LINKS: usize = 25;
/// `PastaFieldSound.SK` — 32 eight-bit limbs an `Fp` element.
const SK: usize = 32;
/// Three sponge lanes.
const STATE_WIDTH: usize = 3 * SK;
const IN_PI_LO: usize = 0;
const OUT_PI_LO: usize = STATE_WIDTH;
const ABSORBED_PI_LO: usize = 2 * STATE_WIDTH;
const CHAIN_PI_COUNT: usize = ABSORBED_PI_LO + 2 * SK;

/// ⚑ **THE EXTERNAL ANCHOR — openmina's own `Random_oracle.salt "MinaProtoStateBody"`**
/// (`poseidon/tests/test_hash_params.rs:28-51`). Comparing the WIRE against these rather than
/// against the Lean file that emitted it is what keeps the head check from being a transcription of
/// a transcription.
const OPENMINA_SALT_PROTO_STATE_BODY: [&str; 3] = [
    "3548547909990922956559515810876765435326873020883079662683136168632773655275",
    "134182536761489093478066959027928272525080293912190881939140820794450385287",
    "18910449726094816833941350890285540874861148441082116020102338532207375519343",
];

/// The `state_body_hash` of Mina devnet block 540221, derived from that block's own protocol-state
/// bytes (`MinaStateBodyHashChain.realBodyHash`).
const REAL_BODY_HASH: &str =
    "5693930022757138716743408081919214747940268519364092084787368564557482288885";

/// The daemon's identity for the same block, off the CHILD's first 32 bytes. A NEGATIVE control:
/// the body hash and the state hash are different objects under different salts.
const CHILD_PREVIOUS_STATE_HASH: &str =
    "8394902380975589711861123145165826281573604591160422433563741797039332441420";

fn chain_desc() -> EffectVmDescriptor2 {
    let d = parse_vm_descriptor2(CHAIN_DESC_JSON).expect("the Lean chain-link descriptor parses");
    assert_eq!(d.name, "dregg-pasta-fp-chainlink::v1");
    assert_eq!(d.public_input_count, CHAIN_PI_COUNT);
    d
}

fn all_link_pis() -> Vec<Vec<BabyBear>> {
    let pis: Vec<Vec<BabyBear>> = BODY_PIS_ALL
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|c| BabyBear::new(c.parse::<u32>().expect("PI is a u32 decimal")))
                .collect()
        })
        .collect();
    assert_eq!(
        pis.len(),
        BODY_LINKS,
        "the packed preimage costs 25 permutations"
    );
    assert!(pis.iter().all(|p| p.len() == CHAIN_PI_COUNT));
    pis
}

fn witness_dir() -> PathBuf {
    std::env::var("DREGG_BODYHASH_WITNESS_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/pasta-fp-bodyhash")
        })
}

fn link_trace(j: usize) -> Vec<Vec<BabyBear>> {
    let path = witness_dir().join(format!("link-{j}-trace.txt"));
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "body-hash link witness {} missing ({e}).\n\
             Emit it first (COMPILED):\n  cd metatheory && lake build mina_fp_chain_emit \\\n    \
             && ./.lake/build/bin/mina_fp_chain_emit ../circuit/tests/fixtures 25",
            path.display()
        )
    });
    let t: Vec<Vec<BabyBear>> = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|c| BabyBear::new(c.parse::<u32>().expect("cell is a u32 decimal")))
                .collect()
        })
        .collect();
    assert_eq!(t.len(), 2048);
    assert!(t.iter().all(|r| r.len() == 469));
    t
}

/// Recompose 32 little-endian 8-bit limbs into a DECIMAL string, by multiply-add on the decimal
/// digits — no bignum dependency and no intermediate to transcribe wrong.
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

/// ⚑ **THE ADVERSARIAL RAIL.** `prove_vm_descriptor2_unchecked` bypasses `build_traces`'s
/// producer-side replay, so a forged witness reaches the CONSTRAINT SYSTEM and the verdict is the
/// circuit's; the proof is then handed to the deployed verifier.
fn prove_and_verify_adversarial(
    d: &EffectVmDescriptor2,
    t: &[Vec<BabyBear>],
    pis: &[BabyBear],
) -> Result<(), String> {
    let proof = prove_vm_descriptor2_unchecked(d, t, pis, &MemBoundaryWitness::default(), &[])?;
    verify_vm_descriptor2(d, &proof, pis)
}

// ────────────────────────────────────────────────────────────────────────────────────────────────
// §1 — THE WIRE. No proving, no witnesses beyond the tracked PI file.
// ────────────────────────────────────────────────────────────────────────────────────────────────

/// ⚑⚑ **THE 25 EMITTED CLAIMS ARE A CHAIN FROM THE SALT TO `state_body_hash`.**
#[test]
fn the_wire_is_the_blocks_body_hash_chain() {
    let pis = all_link_pis();

    for j in 0..BODY_LINKS - 1 {
        assert_eq!(
            &pis[j][OUT_PI_LO..OUT_PI_LO + STATE_WIDTH],
            &pis[j + 1][IN_PI_LO..IN_PI_LO + STATE_WIDTH],
            "link {j}'s outgoing state is not link {}'s incoming state",
            j + 1
        );
    }

    for (lane, expect) in OPENMINA_SALT_PROTO_STATE_BODY.iter().enumerate() {
        assert_eq!(
            &limbs_to_decimal(&pis[0][lane * SK..(lane + 1) * SK]),
            expect,
            "link 0's incoming lane {lane} is not `salt(\"MinaProtoStateBody\")` -- a chain from a \
             head nobody pinned proves nothing, because `perm` is a permutation and 25 links from \
             a FREE head reach every field element"
        );
    }
    assert!(
        pis[0][..STATE_WIDTH].iter().any(|v| v.as_u32() != 0),
        "the head must NOT be the fresh sponge"
    );

    let body_hash = limbs_to_decimal(&pis[BODY_LINKS - 1][OUT_PI_LO..OUT_PI_LO + SK]);
    assert_eq!(
        body_hash, REAL_BODY_HASH,
        "the chain's final lane 0 is not the body hash"
    );
    assert_ne!(
        body_hash, CHILD_PREVIOUS_STATE_HASH,
        "body hash != state hash"
    );

    println!("\n§1 ⚑ WIRE: salt(\"MinaProtoStateBody\") --25 links--> {REAL_BODY_HASH}");
}

/// ⚑ **NO NEW AIR.** The body-hash chain runs the descriptor the phase-1 transcript already runs.
#[test]
fn the_body_hash_chain_emits_nothing() {
    let d = chain_desc();
    let rom = d
        .tables
        .iter()
        .find_map(|t| match &t.sem {
            TableSem::ExactPublicRows { rows } => Some(rows.len()),
            _ => None,
        })
        .expect("the machine declares an instruction ROM");
    assert_eq!(rom, 2048, "the same 2048-instruction ROM");
    assert_eq!(d.trace_width, 469);
    println!("\n§1b ⚑ `dregg-pasta-fp-chainlink::v1` UNCHANGED — 25 witnesses, no new descriptor.");
}

// ────────────────────────────────────────────────────────────────────────────────────────────────
// §2 — THE HONEST LINK, ON THE DEPLOYED RAIL.
// ────────────────────────────────────────────────────────────────────────────────────────────────

/// ⚑ The FIRST link — the one whose incoming state is the salt — proves and verifies.
#[test]
fn the_honest_head_link_proves_and_verifies() {
    let d = chain_desc();
    let pis = all_link_pis();
    let t = link_trace(0);
    let proof = prove_vm_descriptor2(&d, &t, &pis[0], &MemBoundaryWitness::default(), &[])
        .expect("the honest head link MUST prove");
    verify_vm_descriptor2(&d, &proof, &pis[0]).expect("…and verify");
    println!("\n§2 ⚑ honest head link (salt -> state 1) proves and verifies on the deployed rail.");
}

// ────────────────────────────────────────────────────────────────────────────────────────────────
// §3 — ⚑⚑ THE FORGERY, AND THE REFUSAL IS THE AIR'S.
// ────────────────────────────────────────────────────────────────────────────────────────────────

/// ⚑⚑ **A BODY WHOSE HASH IS RIGHT AND WHICH IS NOT THIS BLOCK'S — REFUSED BY THE CIRCUIT.**
///
/// Link 0's absorbed pair carries the first two of the block body's 49 packed field elements. Move
/// ONE limb of the first and leave **the entire claim untouched** — the same incoming salt, the same
/// outgoing state, so the chain still ends on the same `state_body_hash`. That is the substitution
/// this rung exists to refuse.
///
/// Three properties of the falsifier, checked rather than asserted:
///
/// * it moves a **NON-ZERO** limb to a non-zero value — not the zero-into-zero mutation that
///   passes trivially;
/// * it stays **INSIDE the declared 8-bit range**, so no range lookup can be the refusal;
/// * **nothing else moves**, so the refusal cannot come from a pre-existing pin.
///
/// ⚑⚑ **AND IT GOES THROUGH `prove_vm_descriptor2_unchecked`.** The checked entry replays the
/// witness in Rust and refuses eagerly; an adversary does not run the producer. This puts the forged
/// witness in front of the DEPLOYED VERIFIER, so the verdict is the AIR's. Both rails are exercised
/// and the CHECKED one is asserted to refuse too — but the unchecked one is the gate.
#[test]
fn a_substituted_body_element_is_refused_by_the_air() {
    let d = chain_desc();
    let pis = all_link_pis();
    let t = link_trace(0);

    // The honest witness proves on the adversarial rail too, so the refusal below is about the
    // forgery and not about the rail.
    prove_and_verify_adversarial(&d, &t, &pis[0])
        .expect("the HONEST link must prove on the unchecked rail");

    let slot = ABSORBED_PI_LO;
    let before = pis[0][slot].as_u32();
    assert_ne!(before, 0, "the falsifier must move a NON-ZERO limb");
    let mut forged = pis[0].clone();
    forged[slot] = BabyBear::new((before + 1) % 256);
    assert_ne!(forged[slot].as_u32(), before, "the falsifier must MOVE");
    assert!(
        forged[slot].as_u32() < 256,
        "…and stay inside the 8-bit range"
    );
    assert_eq!(
        &forged[..2 * STATE_WIDTH],
        &pis[0][..2 * STATE_WIDTH],
        "the CLAIM must be untouched -- same salt in, same state out, same eventual body hash"
    );

    let err = prove_and_verify_adversarial(&d, &t, &forged)
        .expect_err("a body element that is not this block's must be REFUSED BY THE CIRCUIT");
    println!("\n§3 ⚑⚑ SUBSTITUTED BODY ELEMENT REFUSED BY THE AIR: {err}");
    assert!(
        !err.contains("exact-public"),
        "the ROM must be SILENT about WHICH value is absorbed -- the boundary PIN is the whole of \
         the preimage binding; got: {err}"
    );
    assert!(
        !err.to_lowercase().contains("pre-flight") && !err.to_lowercase().contains("replay"),
        "the refusal must be the CONSTRAINT SYSTEM's, not the producer replay's; got: {err}"
    );

    // …and the CHECKED rail refuses it as well, which is the producer doing its job.
    assert!(
        prove_vm_descriptor2(&d, &t, &forged, &MemBoundaryWitness::default(), &[]).is_err(),
        "the checked rail must refuse it too"
    );
}

/// ⚑⚑ **A FORGED HEAD IS REFUSED BY THE CIRCUIT.** Claim link 0 started somewhere other than the
/// `MinaProtoStateBody` salt. ⚠ This is the vacuity the head pin exists against: `perm` is a
/// permutation, so a prover free to choose the incoming state reaches any target.
#[test]
fn a_forged_head_state_is_refused_by_the_air() {
    let d = chain_desc();
    let pis = all_link_pis();
    let t = link_trace(0);

    let before = pis[0][0].as_u32();
    assert_ne!(
        before, 0,
        "the salt's first limb must be non-zero to move it"
    );
    let mut forged = pis[0].clone();
    forged[0] = BabyBear::new((before + 1) % 256);

    let err = prove_and_verify_adversarial(&d, &t, &forged)
        .expect_err("an incoming state that is not the pinned salt must be REFUSED BY THE CIRCUIT");
    println!("\n§3b ⚑ FORGED HEAD REFUSED BY THE AIR: {err}");
    assert!(
        !err.contains("exact-public"),
        "the ROM must be SILENT about the sponge state; got: {err}"
    );
}

/// ⚑ **AND A FORGED OUTGOING LANE 2 IS REFUSED** — the lane the seven-block descriptor never
/// pinned, and the reason `chainPins` publishes all three. Without it a third of the handed-on
/// state would be a free prover scalar and the chain would not be a chain.
#[test]
fn a_forged_third_outgoing_lane_is_refused_by_the_air() {
    let d = chain_desc();
    let pis = all_link_pis();
    let t = link_trace(0);

    let slot = OUT_PI_LO + 2 * SK;
    let before = pis[0][slot].as_u32();
    let mut forged = pis[0].clone();
    forged[slot] = BabyBear::new((before + 1) % 256);

    let err = prove_and_verify_adversarial(&d, &t, &forged)
        .expect_err("a third outgoing lane the machine did not compute must be REFUSED");
    println!("\n§3c ⚑ FORGED THIRD OUTGOING LANE REFUSED BY THE AIR: {err}");
}
