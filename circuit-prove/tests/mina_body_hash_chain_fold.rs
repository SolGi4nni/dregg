//! ⚑⚑ **`BODYHASH` DERIVED — THE 25-PERMUTATION `state_body_hash` OF A REAL MINA BLOCK, FOLDED.**
//!
//! `LightClientMinaLinkAir` derived `OWNHASH` on 2026-08-06 and named what was left in the same
//! breath:
//!
//! > *"**WHAT IT CAN STILL CHOOSE IS `BODYHASH`** … `state_body_hash`'s own preimage (~38 field
//! > elements under a second salt) is **the next rung**."*
//!
//! This is the Rust half of that rung. The Lean-authored `dregg-pasta-fp-chainlink::v1` descriptor
//! (`Dregg2.Circuit.Emit.MinaStateBodyHashChain`) proven as 25 recursion LEAVES and folded 24 times,
//! with the sponge state carried **inside the recursion circuit** by `cb.connect`. Not one AIR
//! constraint is authored in Rust: the descriptor, its pins, its ROM and its witnesses all come out
//! of Lean. House Law #1.
//!
//! ## ⚑ NO NEW DESCRIPTOR. THE PRICE WAS 25 WITNESSES.
//!
//! `bodyChainDesc = MinaPhase1Chain.chainDesc` by `rfl` — the SAME 2 048 instructions, the SAME 469
//! columns, the SAME `chainPins` layout the phase-1 transcript (27 links) and the VK-digest chain
//! (28 links) already ride. Nothing emits, no VK rotates, nothing re-genesises.
//!
//! ## ⚑ THE PRICE, RE-DERIVED — AND THE INHERITED FIGURE WAS 26
//!
//! `Body.to_input` on the real devnet block is 38 whole field elements + 819 packed chunks
//! (2 381 bits), packing to **49** field elements. The standing number was 26 permutations
//! (`MinaStateHashPackPrice.PERMS_FOR_BODY`, written `(49+1)/2 + 1`); the `+1` double-counted the
//! squeeze, which permutes the LAST partial block rather than adding one after a completed block.
//! It is **25**, and it is derived — `MinaStateBodyHashChain.pairsOf_length` (`⌈n/2⌉`, every list)
//! composed with `MinaPhase1Chain.the_pairs_are_the_absorb_schedule` (every `Params`, every
//! segment).
//!
//! ## ⚑ THE FOOTPRINT, IN THE UNIT THAT BINDS
//!
//! Leaf cost tracks **COMMITTED** width, not declared. This descriptor is **469 declared → 1,037
//! committed** (2.21×, `mina_accumulator_leaf_anatomy.rs`) — the same shape the Fq twin folds 46
//! leaves + 45 folds through in 1,037 s, which is the cheap end of this family. 25 links is under
//! it on every axis. ⚠ The wall clock below is the BOX, not the shape; they are two unit systems
//! and this file reports both without mixing them.
//!
//! **MEASURED 2026-08-07** (laptop, release, `--test-threads=1`): §4's 25 leaves + 24 folds ran in
//! **514 s**, root verified — one leaf **8.6 s**, one fold **8.2 s**. Whole file 709.7 s, 8/8.
//!
//! ## ⚑ WHAT MAKES THIS A CLAIM AND NOT 25 PROOFS
//!
//! Three things are carried, and each is read from a child's OWN FRI-bound public targets:
//!
//! 1. **The state carry.** [`fold_chain_links`] `connect`s the left child's 96 OUTGOING state limbs
//!    to the right child's 96 INCOMING limbs. A prover handing on a state the left link did not
//!    compute makes the aggregation UNSAT: there is no root.
//! 2. **The absorbed stream.** Each leaf commits in-circuit to its own absorbed pair; each fold
//!    folds the two children's commitments into an ORDERED parent digest. §0 is what that digest is
//!    compared against.
//! 3. ⚑ **The HEAD.** The root's `in_state` is the `MinaProtoStateBody` **salt**, not the fresh
//!    sponge every other chain in this cone starts from. ⚠ **This is the load-bearing part.** `perm`
//!    is a permutation, so with a free head 25 links reach every field element and the whole chain
//!    would be vacuous. §0 pins the head against **openmina's own regression constants**.
//!
//! ⇒ the root claim reads: *starting from `Random_oracle.salt "MinaProtoStateBody"`, absorbing
//! exactly this ordered stream, 25 emitted `fpAbsorbProg` executions chain to a state whose lane 0
//! is `state_body_hash`.*
//!
//! ## ⚠ WHAT THIS DOES NOT ESTABLISH — the residual, in the words that fit it
//!
//! **The value a prover chooses moved from `BODYHASH` — one felt — to its 2 381-bit preimage.** It
//! did not disappear. Nothing here says the 49 absorbed elements are a `Protocol_state.Body`'s
//! packing; what says so is Lean's reality gate
//! (`MinaStateHashRealBlock.the_derived_state_hash_is_the_one_the_chain_recorded`, blocks
//! 540221 → 540222), which is a fact about a fixture and not a gate on a witness. And **no
//! constraint in `dregg-mina-lightclient-link::v1` relates its `BODYHASH` nonet to this root** —
//! those nine columns are not PI-bound, so a fold cannot reach them
//! (`LightClientAnchorConnectivity.minaLink_body_hash_is_joined_but_not_published`). That flag day
//! is costed in `LightClientMinaLinkAir` §"WHAT THIS BREAKS".
//!
//! ## PREREQUISITE — the witnesses
//!
//! The 25 traces are ~80 MB and are NOT tracked. Emit them (COMPILED; the interpreter costs
//! minutes per link):
//!
//! ```text
//! cd metatheory && lake build mina_fp_chain_emit
//! ./.lake/build/bin/mina_fp_chain_emit ../circuit/tests/fixtures 25
//! ```
//!
//! The 25 PI vectors ARE tracked (`fixtures/pasta-fp-bodyhash-pis.txt`), so §0 — the claim that the
//! 25 emitted witnesses ARE the block's body-hash chain — runs with no emit at all.
//!
//! Run: `cargo test -p dregg-circuit-prove --release --test mina_body_hash_chain_fold -- --nocapture`

use std::path::PathBuf;
use std::time::Instant;

use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::mina_phase2_chain_leaf::{
    ABSORBED_PI_LO, ABSORBED_WIDTH, CHAIN_CLAIM_LEN, CHAIN_PI_COUNT, OUT_PI_LO, SK, STATE_WIDTH,
    chain_config, fold_chain_links, fp_chain_link_descriptor, host_chain_transcript_acc,
    prove_chain_link_leaf_with, read_chain_claim,
};
use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    recursion_vk_fingerprint, verify_recursive_batch_proof_with_config,
};

/// `MinaStateBodyHashChain.BODY_LINKS` — DERIVED from `⌈49/2⌉`, not counted.
const BODY_LINKS: usize = 25;

/// The 25 Lean-emitted public-input vectors, one line per link, in chain order. TRACKED — small,
/// and the object §0's continuity claim is about.
const BODY_PIS_ALL: &str = include_str!("../../circuit/tests/fixtures/pasta-fp-bodyhash-pis.txt");

/// ⚑ **THE EXTERNAL ANCHOR — openmina's own `Random_oracle.salt "MinaProtoStateBody"`.** These
/// three decimals are the regression constants at `poseidon/tests/test_hash_params.rs:28-51` in
/// o1-labs/openmina, which exist there for exactly this purpose. `Bridge/MinaStateHashDerive.lean`
/// §3 pins the same three; comparing the WIRE against them here rather than against that file is
/// what keeps the head check from being a transcription of a transcription.
const OPENMINA_SALT_PROTO_STATE_BODY: [&str; 3] = [
    "3548547909990922956559515810876765435326873020883079662683136168632773655275",
    "134182536761489093478066959027928272525080293912190881939140820794450385287",
    "18910449726094816833941350890285540874861148441082116020102338532207375519343",
];

/// `MinaStateBodyHashChain.realBodyHash` — the `state_body_hash` of Mina devnet block **540221**,
/// derived by `Bridge.MinaStateHashDerive` from that block's own 1 544 protocol-state bytes.
const REAL_BODY_HASH: &str =
    "5693930022757138716743408081919214747940268519364092084787368564557482288885";

/// The daemon's own identity for the same block, read off the CHILD's first 32 bytes
/// (`MinaStateHashRealBlock.childPreviousStateHash`). Used as a NEGATIVE control: the body hash and
/// the state hash are two different objects and the chain must land on the first.
const CHILD_PREVIOUS_STATE_HASH: &str =
    "8394902380975589711861123145165826281573604591160422433563741797039332441420";

fn witness_dir() -> PathBuf {
    std::env::var("DREGG_BODYHASH_WITNESS_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("../circuit/tests/fixtures/pasta-fp-bodyhash")
        })
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
        "the block body's packed preimage costs 25 permutations"
    );
    assert!(
        pis.iter().all(|p| p.len() == CHAIN_PI_COUNT),
        "every link carries {CHAIN_PI_COUNT} public inputs"
    );
    pis
}

/// Read link `j`'s Lean-emitted 2048x469 trace. Fails LOUDLY with the emit command rather than
/// skipping: a test that quietly does nothing when its input is absent is not a gate.
fn link_trace(j: usize) -> Vec<Vec<BabyBear>> {
    let path = witness_dir().join(format!("link-{j}-trace.txt"));
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "body-hash link witness {} missing ({e}).\n\
             Emit the witnesses first (COMPILED — the interpreter costs minutes per link):\n  \
             cd metatheory && lake build mina_fp_chain_emit \\\n    \
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
    assert_eq!(t.len(), 2048, "the Lean-emitted link is 2048 rows");
    assert!(t.iter().all(|r| r.len() == 469), "every row is 469 wide");
    t
}

/// `Result::expect_err` needs `T: Debug`, and a `RecursionOutput` is not.
fn expect_refusal<T>(r: Result<T, String>, must: &str) -> String {
    match r {
        Ok(_) => panic!("{must}"),
        Err(e) => e,
    }
}

/// Recompose 32 little-endian 8-bit limbs into a DECIMAL string, by repeated multiply-add on the
/// decimal digits — so no bignum dependency and no chance to transcribe an intermediate wrong.
fn limbs_to_decimal(limbs: &[BabyBear]) -> String {
    let mut digits: Vec<u32> = vec![0];
    for limb in limbs.iter().rev() {
        // digits := digits * 256 + limb
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

// ============================================================================
// §0 — THE EMITTED CLAIMS CHAIN. Cheap, unconditional, and what everything below is about.
// ============================================================================

/// ⚑⚑ **THE 25 EMITTED CLAIMS ARE A CHAIN, AND ITS TWO ENDS ARE THE ONES THAT MATTER.**
///
/// `MinaStateBodyHashChain.the_body_emitted_claims_are_continuous` on the wire (link `j`'s outgoing
/// state block IS link `j+1`'s incoming block, limb for limb), plus:
///
/// * ⚑ **the HEAD is the SALT** — checked against openmina's regression constants, not against the
///   Lean file that emitted the wire. With a free head the whole chain is vacuous;
/// * ⚑ **the TAIL is `state_body_hash`** — link 24's outgoing lane 0;
/// * and the closing squeeze's second absorb slot is the padding zero the ODD 49-element stream
///   forces, so the chain is not a sentence about a 50th element nobody checked.
#[test]
fn the_twenty_five_emitted_claims_are_the_blocks_body_hash_chain() {
    let pis = all_link_pis();

    for j in 0..BODY_LINKS - 1 {
        assert_eq!(
            &pis[j][OUT_PI_LO..OUT_PI_LO + STATE_WIDTH],
            &pis[j + 1][..STATE_WIDTH],
            "link {j}'s outgoing state is not link {}'s incoming state -- the emitted witnesses \
             are not a chain",
            j + 1
        );
    }

    // ⚑ THE HEAD. Three lanes of 32 limbs each, against openmina's own constants.
    for (lane, expect) in OPENMINA_SALT_PROTO_STATE_BODY.iter().enumerate() {
        let got = limbs_to_decimal(&pis[0][lane * SK..(lane + 1) * SK]);
        assert_eq!(
            &got, expect,
            "link 0's incoming lane {lane} is not `Random_oracle.salt \"MinaProtoStateBody\"` -- \
             a chain from a head nobody pinned proves nothing, because `perm` is a permutation and \
             25 links from a FREE head reach every field element"
        );
    }
    assert!(
        pis[0][..STATE_WIDTH].iter().any(|v| v.as_u32() != 0),
        "the head must NOT be the fresh sponge -- that is the copy-paste this pin exists to refuse"
    );

    // ⚑ THE TAIL.
    let last = &pis[BODY_LINKS - 1];
    let body_hash = limbs_to_decimal(&last[OUT_PI_LO..OUT_PI_LO + SK]);
    assert_eq!(
        body_hash, REAL_BODY_HASH,
        "the chain's final lane 0 is not block 540221's `state_body_hash`"
    );
    assert_ne!(
        body_hash, CHILD_PREVIOUS_STATE_HASH,
        "the body hash and the STATE hash are two different objects under two different salts; \
         landing on the second would mean the salt lanes are wrong"
    );

    // ⚑ THE ODD TAIL. 49 elements is odd, so the last link absorbs ONE.
    assert!(
        last[ABSORBED_PI_LO + SK..ABSORBED_PI_LO + ABSORBED_WIDTH]
            .iter()
            .all(|v| v.as_u32() == 0),
        "the closing squeeze's second absorb slot must be pinned to zero"
    );
    // ⚑ **AND THE ZERO SLOTS ARE A MEASUREMENT, NOT AN ACCIDENT — this is what a falsifier must
    // steer around.** Nine of the fifty absorbed slots are zero: the odd tail's pad, and TWO RUNS
    // OF FOUR at flat indices 9..12 and 19..22. Those are the `Local_state.to_input` blocks of the
    // SOURCE and TARGET `Registers` — an empty call stack, two zero transaction commitments and a
    // zero local ledger — ten elements apart, which is `registersI`'s own stride. ⚠ A control that
    // aimed at one of these would be moving a zero into a zero, which is how a sibling lane's first
    // falsifier died.
    let zero_slots: Vec<usize> = (0..2 * BODY_LINKS)
        .filter(|k| {
            let (j, h) = (k / 2, k % 2);
            pis[j][ABSORBED_PI_LO + h * SK..ABSORBED_PI_LO + (h + 1) * SK]
                .iter()
                .all(|v| v.as_u32() == 0)
        })
        .collect();
    assert_eq!(
        zero_slots,
        vec![9, 10, 11, 12, 19, 20, 21, 22, 49],
        "the zero elements of the packed preimage moved -- either the block changed or \
         `Body.to_input`'s field order did"
    );
    // The two falsifier targets §2 uses are NOT among them.
    for k in [0usize, 24] {
        let (j, h) = (k / 2, k % 2);
        assert!(
            pis[j][ABSORBED_PI_LO + h * SK..ABSORBED_PI_LO + (h + 1) * SK]
                .iter()
                .any(|v| v.as_u32() != 0),
            "falsifier target (element {k}) must be a NON-ZERO preimage element"
        );
    }

    println!("\n═══ §0  THE 25 EMITTED CLAIMS ARE THE BLOCK'S BODY-HASH CHAIN ═══");
    println!("  24 joints  : out(j) == in(j+1), limb for limb");
    println!("  link 0  in : salt(\"MinaProtoStateBody\") — openmina's own regression constants");
    println!("  link 24 out: state_body_hash = {REAL_BODY_HASH}");
    println!("  absorbed   : 49 packed field elements + 1 padding zero (49 is ODD)");
    println!("  zero slots : {zero_slots:?} — the two Local_state blocks and the pad");
}

/// The Fp chain-link descriptor is the DEPLOYED one — the same object the phase-1 transcript and
/// the VK-digest chain run on. ⚑ This rung emitted nothing.
#[test]
fn the_body_hash_chain_runs_the_deployed_fp_chainlink_descriptor() {
    use dregg_circuit::descriptor_ir2::{TableSem, parse_vm_descriptor2};

    let body = fp_chain_link_descriptor().expect("the Lean Fp chain-link descriptor parses");
    let phase1 = parse_vm_descriptor2(include_str!(
        "../../circuit/descriptors/by-name/pasta-fp-chainlink.json"
    ))
    .expect("the deployed phase-1 chain-link descriptor parses");

    let rom = |d: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2| {
        d.tables
            .iter()
            .find_map(|t| match &t.sem {
                TableSem::ExactPublicRows { rows } => Some(rows.clone()),
                _ => None,
            })
            .expect("the machine declares an instruction ROM")
    };

    assert_eq!(body.name, "dregg-pasta-fp-chainlink::v1");
    assert_eq!(rom(&body), rom(&phase1), "the SAME 2048-instruction ROM");
    assert_eq!(body.trace_width, 469);
    assert_eq!(body.public_input_count, CHAIN_PI_COUNT);
    println!(
        "\n§0b the body-hash chain runs `dregg-pasta-fp-chainlink::v1` UNCHANGED — 25 witnesses, \
         no new AIR, no VK rotation."
    );
}

// ============================================================================
// §1 — THE FOLD, SMALL FIRST.
// ============================================================================

/// ⚑⚑ **§1 — TWO LINKS FOLD, AND THE STATE IS CARRIED INSIDE THE RECURSION.**
///
/// The parent's incoming state is link 0's — the SALT — and its outgoing state is link 1's. That
/// equality is not compared host-side: `fold_chain_links` `connect`s 96 limbs in-circuit, so a
/// chain that does not join has no satisfying assignment.
#[test]
fn two_body_hash_links_fold_into_one_claim() {
    let pis = all_link_pis();
    let config = chain_config();
    let desc = fp_chain_link_descriptor().expect("descriptor");

    let t0 = Instant::now();
    let l0 = prove_chain_link_leaf_with(&desc, &link_trace(0), &pis[0], &config)
        .expect("body link 0 leaf");
    let l1 = prove_chain_link_leaf_with(&desc, &link_trace(1), &pis[1], &config)
        .expect("body link 1 leaf");
    let leaves_ms = t0.elapsed().as_millis();

    let t1 = Instant::now();
    let node = fold_chain_links(&l0, &l1, &config).expect("body links 0..1 fold");
    let fold_ms = t1.elapsed().as_millis();

    verify_recursive_batch_proof_with_config(&node.0, &config).expect("the folded node verifies");

    let claim = read_chain_claim(&node).expect("the node publishes a chain claim");
    assert_eq!(
        claim.in_state,
        pis[0][..STATE_WIDTH],
        "parent in == the SALT"
    );
    assert_eq!(
        claim.out_state,
        pis[1][OUT_PI_LO..OUT_PI_LO + STATE_WIDTH],
        "parent out == link 1 out"
    );
    assert_eq!(
        claim.transcript_acc,
        host_chain_transcript_acc(&pis[..2]),
        "the folded digest must be the host fold of the two links' absorbed pairs"
    );
    assert_eq!(
        claim.in_state.len() + claim.out_state.len() + 8,
        CHAIN_CLAIM_LEN
    );

    println!("\n§1 ⚑⚑ TWO BODY-HASH LINKS FOLDED. 2 leaves {leaves_ms} ms, 1 fold {fold_ms} ms.");
    println!("  the parent's incoming state IS the MinaProtoStateBody salt, and the join was");
    println!("  enforced by 96 in-circuit `connect`s, not a host comparison.");
}

// ============================================================================
// §2 — BOTH POLARITIES, IN RELEASE. The refusing gate is named.
// ============================================================================

/// ⚑⚑ **§2 — THE FORGERY: A BODY WHOSE HASH IS RIGHT AND WHICH IS NOT THIS BLOCK'S.**
///
/// Take link 12 — an honest link of the real preimage, whose leaf proves — and move ONE limb of the
/// absorbed body element while leaving **the entire claim untouched**: the same incoming state, the
/// same outgoing state, so the chain still ends on the same `state_body_hash`. That is exactly the
/// substitution this rung exists to refuse: *the hash is right, the body is not this block's.*
///
/// Three properties of the falsifier, each of which a sibling lane's first draft got wrong:
///
/// * the moved limb goes from a **NON-ZERO** value to a non-zero value — not the zero-into-zero
///   mutation `decide` cheerfully proves is not a tamper;
/// * it stays **INSIDE the declared 8-bit range**, so a range lookup cannot be what refuses it;
/// * **nothing else moves** — the in-state, the out-state and the other 63 absorbed limbs are the
///   honest link's, so the refusal cannot come from a pre-existing pin on those.
#[test]
fn a_substituted_body_element_is_refused_by_the_pin() {
    let pis = all_link_pis();
    let config = chain_config();
    let desc = fp_chain_link_descriptor().expect("descriptor");

    // The honest link proves — asserted FIRST, so the refusal below cannot be a leaf failing for
    // an unrelated reason.
    prove_chain_link_leaf_with(&desc, &link_trace(12), &pis[12], &config)
        .expect("link 12 is an honest link and its leaf MUST prove");

    let slot = ABSORBED_PI_LO;
    let before = pis[12][slot].as_u32();
    assert_ne!(
        before, 0,
        "the falsifier must move a NON-ZERO limb, or it is a tautology about an unchanged chain"
    );
    let mut forged = pis[12].clone();
    forged[slot] = BabyBear::new((before + 1) % 256);
    assert_ne!(forged[slot].as_u32(), before, "the falsifier must MOVE");
    assert_eq!(
        &forged[..2 * STATE_WIDTH],
        &pis[12][..2 * STATE_WIDTH],
        "the CLAIM must be untouched -- same in-state, same out-state, same eventual body hash"
    );

    let err = expect_refusal(
        prove_chain_link_leaf_with(&desc, &link_trace(12), &forged, &config),
        "a body element that is not this block's must be REFUSED even when the hash is unchanged",
    );
    println!("\n§2 ⚑⚑ SUBSTITUTED BODY ELEMENT REFUSED AT THE LEAF: {err}");
    assert!(
        !err.contains("exact-public"),
        "the ROM must be SILENT about WHICH value is absorbed -- the boundary PIN is the whole of \
         the preimage binding; got: {err}"
    );
}

/// ⚑ **§2b — A SKIPPED LINK IS REFUSED BY THE FOLD'S `connect`.** Fold link 0 with link 2. Both are
/// honest links of the real preimage and both leaves prove; what is false is only that link 2
/// continues link 0. The 96 `cb.connect`s are then a witness CONFLICT and there is no parent proof.
///
/// ⚑ This is the "state inside the recursion" property, exhibited: a fold that merely re-pinned
/// public inputs would accept this.
#[test]
fn a_skipped_body_link_is_refused_by_the_folds_connect() {
    let pis = all_link_pis();
    let config = chain_config();
    let desc = fp_chain_link_descriptor().expect("descriptor");

    let l0 = prove_chain_link_leaf_with(&desc, &link_trace(0), &pis[0], &config)
        .expect("link 0 is honest and its leaf MUST prove");
    let l2 = prove_chain_link_leaf_with(&desc, &link_trace(2), &pis[2], &config)
        .expect("link 2 is honest and its leaf MUST prove -- the lie is only the JOIN");

    let err = expect_refusal(
        fold_chain_links(&l0, &l2, &config),
        "a body-hash chain that skips link 1 must be REFUSED by the fold",
    );
    println!("\n§2b ⚑ BROKEN JOIN REFUSED BY THE FOLD: {err}");
    assert!(
        !err.contains("exact-public"),
        "the ROM must be SILENT about the sponge state; got: {err}"
    );

    let l1 =
        prove_chain_link_leaf_with(&desc, &link_trace(1), &pis[1], &config).expect("link 1 leaf");
    fold_chain_links(&l0, &l1, &config).expect("the HONEST join must still fold");
    println!("  …and the honest join (0,1) folds, so the refusal is the join and not the link.");
}

/// ⚑⚑ **§2c — A FORGED HEAD IS REFUSED.** Claim link 0 started from the FRESH SPONGE instead of the
/// `MinaProtoStateBody` salt — the copy-paste every other chain in this cone would invite. ⚠ This
/// is the vacuity the head pin exists against, and it is refused at the leaf: the trace computed
/// `perm(salt + [x₀,x₁,0])` and the claim says it started from zero.
#[test]
fn a_fresh_sponge_head_is_refused() {
    let pis = all_link_pis();
    let config = chain_config();
    let desc = fp_chain_link_descriptor().expect("descriptor");

    let mut forged = pis[0].clone();
    // Move ONE limb of the incoming state toward zero — inside the 8-bit range, so no range gate.
    let before = forged[0].as_u32();
    assert_ne!(
        before, 0,
        "the salt's first limb must be non-zero to move it"
    );
    forged[0] = BabyBear::new((before + 1) % 256);

    let err = expect_refusal(
        prove_chain_link_leaf_with(&desc, &link_trace(0), &forged, &config),
        "an incoming state that is not the pinned salt must be REFUSED",
    );
    println!("\n§2c ⚑ FORGED HEAD REFUSED AT THE LEAF: {err}");
}

// ============================================================================
// §3 — RecursionVk determinism: a shipped property this must not break.
// ============================================================================

/// ⚑ An honest re-fold of the same chain mints the SAME `RecursionVk` fingerprint.
/// `recursion_vk_determinism.rs` calls that fingerprint *"the light client's distributed trust
/// anchor"*.
#[test]
fn the_body_hash_folds_recursion_vk_is_deterministic() {
    let pis = all_link_pis();
    let config = chain_config();
    let desc = fp_chain_link_descriptor().expect("descriptor");

    let build = || {
        let l0 = prove_chain_link_leaf_with(&desc, &link_trace(0), &pis[0], &config).expect("l0");
        let l1 = prove_chain_link_leaf_with(&desc, &link_trace(1), &pis[1], &config).expect("l1");
        fold_chain_links(&l0, &l1, &config).expect("links 0..1 fold")
    };

    let a = build();
    let b = build();
    assert_eq!(
        recursion_vk_fingerprint(&a.0),
        recursion_vk_fingerprint(&b.0),
        "two honest folds of the SAME chain minted different RecursionVk fingerprints"
    );
    assert_eq!(
        read_chain_claim(&a).expect("a"),
        read_chain_claim(&b).expect("b")
    );
    println!(
        "\n§3 ⚑ RecursionVk fingerprint STABLE across two honest folds: {:?}",
        recursion_vk_fingerprint(&a.0)
    );
}

// ============================================================================
// §4 — THE WHOLE CHAIN.
// ============================================================================

/// ⚑⚑⚑ **§4 — ALL 25 LINKS, FOLDED INTO ONE ROOT: `BODYHASH` IS DERIVED.**
///
/// 25 leaves and 24 fold nodes. The root claim's `in_state` is the `MinaProtoStateBody` salt, its
/// `out_state`'s lane 0 is block 540221's `state_body_hash`, and its `transcript_acc` is the ordered
/// digest of the 49 absorbed packed elements — compared against the host mirror over the Lean
/// emitted public inputs.
///
/// `#[ignore]`d for wall clock only. Run:
/// `cargo test -p dregg-circuit-prove --release --test mina_body_hash_chain_fold -- --ignored --nocapture`
#[test]
#[ignore = "the whole 25-link body-hash fold; wall-clock only"]
fn the_whole_body_hash_chain_folds() {
    let pis = all_link_pis();
    let config = chain_config();
    let desc = fp_chain_link_descriptor().expect("descriptor");

    let t0 = Instant::now();
    let mut acc = prove_chain_link_leaf_with(&desc, &link_trace(0), &pis[0], &config)
        .expect("body link 0 leaf");
    for j in 1..BODY_LINKS {
        let leaf = prove_chain_link_leaf_with(&desc, &link_trace(j), &pis[j], &config)
            .unwrap_or_else(|e| panic!("body link {j} leaf: {e}"));
        acc = fold_chain_links(&acc, &leaf, &config)
            .unwrap_or_else(|e| panic!("fold at body link {j}: {e}"));
        println!(
            "  folded {}/{BODY_LINKS} ({} s)",
            j + 1,
            t0.elapsed().as_secs()
        );
    }
    let total_s = t0.elapsed().as_secs();

    verify_recursive_batch_proof_with_config(&acc.0, &config).expect("the 25-link root verifies");

    let claim = read_chain_claim(&acc).expect("the root publishes a chain claim");
    assert_eq!(
        claim.in_state,
        pis[0][..STATE_WIDTH],
        "the root's incoming state must be the MinaProtoStateBody SALT"
    );
    assert_eq!(
        claim.out_state,
        pis[BODY_LINKS - 1][OUT_PI_LO..OUT_PI_LO + STATE_WIDTH],
        "the root's outgoing state must be link 24's"
    );
    assert_eq!(
        claim.transcript_acc,
        host_chain_transcript_acc(&pis),
        "the root's transcript digest must be the ordered fold of the 49 absorbed elements"
    );
    assert_eq!(
        limbs_to_decimal(&claim.out_state[..SK]),
        REAL_BODY_HASH,
        "the root's outgoing lane 0 must be block 540221's `state_body_hash`"
    );

    println!("\n═══ §4 ⚑⚑⚑ THE WHOLE 25-LINK BODY-HASH CHAIN FOLDED in {total_s} s ═══");
    println!("  root in  : salt(\"MinaProtoStateBody\")");
    println!("  root out0: {REAL_BODY_HASH}");
    println!("  BODYHASH is DERIVED. ⚠ What a prover still chooses is its 2 381-bit PREIMAGE.");
}
