//! ⚑⚑⚑ **TIE 1 BECOMES A WELD — the leaf adapter, at the deployed prover, both polarities.**
//!
//! `MinaBodyPreimageSeams` §7.0 named the owed object and refused to round it up:
//!
//! > *"The two surfaces this seam welds are `air_public_targets.first()` of two DIFFERENT leaves,
//! > and every `apply_seam` call site in the tree welds two children's `expose_claim` instances
//! > instead. The owed object is a leaf adapter verifying the preimage STARK and a chain-link STARK
//! > in one circuit. ⚑ Until it exists the tie is **authored and proved but not applied** … The
//! > `WeldCover`/executor comparison it replaces is still what runs."*
//!
//! This file is that object running. `prove_body_preimage_link_adapter` verifies both STARKs in one
//! aggregation circuit and `apply_seam` issues the 64 merges the Lean artifact names.
//!
//! ## The polarities, and what each one is about
//!
//! * **§1 honest** — link 0's adapter proves and verifies, and its claim is **identical** to the
//!   claim a plain `prove_chain_link_leaf_with` publishes for the same link. That identity is what
//!   makes the adapter a DROP-IN: twenty-five of them fold with the same node into the same root.
//! * **§2 the forgery** — a preimage whose own AIR accepts it completely and which is **not the
//!   body this chain absorbed**. One whole-field limb moves by one, inside the eight-bit range, in
//!   the row AND the claim, so the range gate passes and the pin passes; the chain link is
//!   untouched and its leaf still proves. The ONLY false thing in the whole system is the seam, and
//!   the refusal must be the seam's own `cb.connect`.
//! * **§2b the wrong link** — link 0's seam applied to link 1's claim. Both leaves are honest; what
//!   is false is only WHICH link this preimage block belongs to.
//! * **§3 the drop-in** — two adapters fold with `fold_chain_links`, unmodified.
//!
//! ## PREREQUISITES — two Lean emits, neither of them a Rust re-derivation
//!
//! ```text
//! cd metatheory
//! lake env lean --run MinaBodyBitsEmit.lean ../circuit/tests/fixtures     # the preimage row + claim
//! lake build mina_fp_chain_emit && ./.lake/build/bin/mina_fp_chain_emit ../circuit/tests/fixtures 25
//! ```
//!
//! The 25 chain traces are ~80 MB and are NOT tracked; the preimage row, the preimage claim and the
//! 25 chain PI vectors ARE.
//!
//! Run (⚠ the workspace needs the Lean archive resolvable):
//! ```text
//! DREGG_METATHEORY_DIR=$PWD/metatheory DREGG_LEAN_SYSROOT=$(lean --print-prefix) \
//!   cargo test -p dregg-circuit-prove --release --test mina_body_preimage_adapter -- --nocapture
//! ```

use std::path::PathBuf;
use std::time::Instant;

use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::binding_tooth::{BINDING_CONNECT_MARKERS, binding_connect_marker};
use dregg_circuit_prove::fold_vk_pin::FoldVkPins;
use dregg_circuit_prove::mina_body_preimage_adapter::{
    BODY_BITS_PI_COUNT, BODY_BITS_WIDTH, BODY_LINKS, NBITS, NLIMB, body_preimage_descriptor,
    body_preimage_seam, claim_from_row, prove_body_preimage_link_adapter,
};
use dregg_circuit_prove::mina_phase2_chain_leaf::{
    ABSORBED_PI_LO, CHAIN_PI_COUNT, chain_inner_config, chain_root_config, fold_chain_links,
    fp_chain_link_descriptor, host_chain_transcript_acc, prove_chain_link_leaf_with,
    read_chain_claim,
};
use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    recursion_layer_over, verify_recursive_batch_proof_with_config,
};

const BODY_PIS_ALL: &str = include_str!("../../circuit/tests/fixtures/pasta-fp-bodyhash-pis.txt");
const PREIMAGE_ROW: &str =
    include_str!("../../circuit/tests/fixtures/mina-body-preimage-bits-row.txt");
const PREIMAGE_PIS: &str =
    include_str!("../../circuit/tests/fixtures/mina-body-preimage-bits-pis.txt");

fn decimals(text: &str, want: usize, what: &str) -> Vec<BabyBear> {
    let v: Vec<BabyBear> = text
        .split_whitespace()
        .map(|c| BabyBear::new(c.parse::<u32>().expect("cell is a u32 decimal")))
        .collect();
    assert_eq!(
        v.len(),
        want,
        "the Lean-emitted {what} is {want} cells; re-emit with \
         `cd metatheory && lake env lean --run MinaBodyBitsEmit.lean ../circuit/tests/fixtures`"
    );
    v
}

fn preimage_row() -> Vec<BabyBear> {
    decimals(PREIMAGE_ROW, BODY_BITS_WIDTH, "preimage row")
}

fn preimage_claim() -> Vec<BabyBear> {
    decimals(PREIMAGE_PIS, BODY_BITS_PI_COUNT, "preimage claim")
}

/// A power-of-two trace: the real row, then zero padding. A zero row satisfies every gate of this
/// descriptor — booleanity because `0·(0−1) = 0`, the limb legs because an all-zero byte composes
/// to zero, the range queries because `0` is in the table.
fn preimage_trace(row: Vec<BabyBear>) -> Vec<Vec<BabyBear>> {
    vec![row, vec![BabyBear::new(0); BODY_BITS_WIDTH]]
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
    assert_eq!(pis.len(), BODY_LINKS);
    assert!(pis.iter().all(|p| p.len() == CHAIN_PI_COUNT));
    pis
}

fn witness_dir() -> PathBuf {
    std::env::var("DREGG_BODYHASH_WITNESS_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("../circuit/tests/fixtures/pasta-fp-bodyhash")
        })
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

fn expect_refusal<T>(r: Result<T, String>, must: &str) -> String {
    dregg_circuit::refusal::must_refuse(must, || r)
}

// ============================================================================
// §0 — THE EMITTED CLAIM IS THE STREAM THE CHAIN ABSORBS. Cheap, unconditional.
// ============================================================================

/// ⚑⚑ **THE SEAM'S TWO ENDS AGREE ON THE REAL BLOCK, ON THE WIRE.** The Lean twin is
/// `MinaBodyPreimageSeams.the_preimage_seams_hold_on_the_real_block`; this is the same 1 518 pins
/// and 82 zero-pins checked against the two EMITTED fixtures rather than against Lean's own
/// functions, so a fixture that stopped being the block's is a red HERE.
///
/// ⚠ Asserted before anything proves: if this is false, every refusal below would be about the
/// witnesses rather than about the seam.
#[test]
fn the_emitted_preimage_claim_is_the_stream_the_chain_absorbs() {
    let lv = preimage_claim();
    let rv = all_link_pis();
    let mut welded = 0usize;
    let mut zeroed = 0usize;
    for j in 0..BODY_LINKS {
        let s = body_preimage_seam(j).unwrap_or_else(|e| panic!("seam {j}: {e}"));
        for &(l, r) in &s.pins {
            assert_eq!(
                lv[l], rv[j][r],
                "seam {j}: preimage claim slot {l} is not chain slot {r} — the two emitted \
                 fixtures are not about the same block"
            );
            welded += 1;
        }
        for &r in &s.zero_right {
            assert_eq!(
                rv[j][r].as_u32(),
                0,
                "seam {j}: chain slot {r} must be zero — the `32 − ⌈W_e/8⌉` high limbs and the odd \
                 tail's pad are what stop the chain absorbing `element + k·2^(8m)`"
            );
            zeroed += 1;
        }
    }
    assert_eq!(welded, BODY_BITS_PI_COUNT);
    assert_eq!(zeroed, 82);

    // ⚑ THE CONTROL, and it is NOT "every link welds a non-zero value" — that is FALSE and knowing
    // exactly where is the point. `Body.to_input` puts the SOURCE and TARGET `Local_state` blocks
    // at absorbed elements 9..12 and 19..22, so links 5 (elements 10, 11) and 10 (20, 21) weld two
    // genuinely-zero field elements. The Lean twin is
    // `the_real_welds_are_non_zero_except_at_the_two_local_state_links`.
    let all_zero: Vec<usize> = (0..BODY_LINKS)
        .filter(|&j| {
            let s = body_preimage_seam(j).unwrap();
            !s.pins.iter().any(|&(l, _)| lv[l].as_u32() != 0)
        })
        .collect();
    assert_eq!(
        all_zero,
        vec![5, 10],
        "the links whose welds are all-zero moved — either the block changed or `Body.to_input`'s \
         field order did. A seam family that welded zeros everywhere would move this list, not \
         satisfy it."
    );

    println!("\n═══ §0  THE SEAM HOLDS ON THE REAL BLOCK, ON THE WIRE ═══");
    println!("  {welded} welds + {zeroed} zero-pins across {BODY_LINKS} links");
    println!("  all-zero links: {all_zero:?} (the two Local_state blocks) — 23/25 weld a value");
}

/// The preimage claim the ADAPTER will hand in is the emitted one, and the row it is derived from
/// agrees with it. Two Lean functions, one layout.
#[test]
fn the_preimage_row_and_claim_agree() {
    let row = preimage_row();
    assert_eq!(claim_from_row(&row).expect("row is the right width"), preimage_claim());
    assert!(row[..NBITS].iter().all(|v| v.as_u32() <= 1));
    assert!(
        row[NBITS..NBITS + NLIMB].iter().all(|v| v.as_u32() < 256),
        "every packed limb is a byte"
    );
}

// ============================================================================
// §1 — THE HONEST ADAPTER. Asserted FIRST so every refusal below is about a forgery.
// ============================================================================

/// ⚑⚑⚑ **§1 — THE ADAPTER PROVES, AND ITS CLAIM IS THE CHAIN LEAF'S CLAIM.**
///
/// Both STARKs verified in ONE circuit, the 64 merges issued, and the published claim **identical**
/// to what `prove_chain_link_leaf_with` publishes for the same link — which is the whole drop-in
/// property: `fold_chain_links` cannot tell the two apart, so the 25-link root keeps its shape and
/// gains a sentence.
#[test]
fn the_body_preimage_adapter_proves_and_publishes_the_chain_leafs_claim() {
    let pis = all_link_pis();
    let inner = chain_inner_config();
    let pdesc = body_preimage_descriptor().expect("the Lean preimage descriptor parses");
    let cdesc = fp_chain_link_descriptor().expect("the Lean Fp chain-link descriptor parses");
    let seam = body_preimage_seam(0).expect("seam 0");
    let row = preimage_row();
    let claim = preimage_claim();

    let t0 = Instant::now();
    let adapter = prove_body_preimage_link_adapter(
        &pdesc,
        &preimage_trace(row),
        &claim,
        &cdesc,
        &link_trace(0),
        &pis[0],
        &seam,
        &inner,
    )
    .expect("the honest adapter MUST prove — both STARKs and the 64 welds");
    let adapter_ms = t0.elapsed().as_millis();

    // ⚑ It verifies at the engine a chain leaf's wrap mints at, which is what makes it foldable.
    let wrap_cfg = recursion_layer_over(&inner);
    verify_recursive_batch_proof_with_config(&adapter.0, &wrap_cfg)
        .expect("the adapter's own proof verifies");

    let t1 = Instant::now();
    let plain = prove_chain_link_leaf_with(&cdesc, &link_trace(0), &pis[0], &inner)
        .expect("the plain chain leaf proves");
    let plain_ms = t1.elapsed().as_millis();

    let a = read_chain_claim(&adapter).expect("the adapter publishes a chain claim");
    let p = read_chain_claim(&plain).expect("the plain leaf publishes a chain claim");
    assert_eq!(
        a, p,
        "the adapter must publish EXACTLY the chain leaf's claim, or it is not a drop-in and the \
         25-link root would change shape"
    );
    assert_eq!(a.transcript_acc, host_chain_transcript_acc(&pis[..1]));

    println!("\n═══ §1 ⚑⚑⚑ THE LEAF ADAPTER PROVES ═══");
    println!("  adapter (2 STARKs + {} welds): {adapter_ms} ms", seam.connect_count());
    println!("  plain chain leaf (1 STARK)   : {plain_ms} ms");
    println!("  claims IDENTICAL — the adapter is a drop-in for the chain leaf.");
}

// ============================================================================
// §2 — BOTH POLARITIES. The refusing gate is the SEAM's own `cb.connect`.
// ============================================================================

/// ⚑⚑⚑ **§2 — A BODY WHOSE OWN AIR ACCEPTS IT AND WHICH IS NOT THIS BLOCK'S.**
///
/// This is the substitution the whole tie exists to refuse, and until this adapter existed it was
/// refused by an executor comparison or by nothing at all.
///
/// Four properties of the falsifier, and the first three are what make the fourth mean something:
///
/// * the moved value is a whole-field limb going from a **NON-ZERO** byte to another byte — not the
///   zero-into-zero mutation that is a tautology about an unchanged row;
/// * it stays **INSIDE the eight-bit range**, so the `range_w8` query cannot be what refuses it;
/// * it moves in the ROW **and** in the CLAIM, so the pin leg is satisfied — and §2's first
///   assertion is that **the forged preimage STARK still proves on its own**, which is the whole
///   point: this body is internally perfect;
/// * the chain link is **untouched**, and its leaf proves.
///
/// So the only false statement anywhere is *"this preimage is the one this link absorbed"*, and the
/// refusal must be the seam's `cb.connect` — a witness CONFLICT, not a claim-layout guard, not an
/// FRI fault, not a range verdict.
#[test]
fn a_preimage_that_is_not_this_blocks_is_refused_by_the_seam() {
    let pis = all_link_pis();
    let inner = chain_inner_config();
    let pdesc = body_preimage_descriptor().expect("preimage descriptor");
    let cdesc = fp_chain_link_descriptor().expect("chain-link descriptor");
    let seam = body_preimage_seam(0).expect("seam 0");

    // The first whole-field limb column, `FLIMB 0 0` — welded by seam 0 to chain slot 192.
    let col = NBITS + NLIMB;
    let honest = preimage_row();
    let before = honest[col].as_u32();
    assert_ne!(
        before, 0,
        "the falsifier must move a NON-ZERO limb, or it is a tautology about an unchanged body"
    );
    let mut forged = honest.clone();
    forged[col] = BabyBear::new((before + 1) % 256);
    assert_ne!(forged[col].as_u32(), before, "the falsifier must MOVE");
    assert!(
        forged[col].as_u32() < 256,
        "the moved limb must stay INSIDE the eight-bit table, or the range gate refuses it and \
         this tooth measures the range gate instead of the seam"
    );
    assert_eq!(
        &forged[..col],
        &honest[..col],
        "not one bit and not one packed limb moves"
    );
    let forged_claim = claim_from_row(&forged).expect("the forged row is the right width");
    assert_ne!(forged_claim, preimage_claim(), "the CLAIM must move with it");
    // ⚑ And the welded chain slot is unchanged, so the seam is what disagrees.
    assert_eq!(
        pis[0][ABSORBED_PI_LO].as_u32(),
        before,
        "the chain absorbed the HONEST limb; the seam welds claim slot 0 to chain slot \
         {ABSORBED_PI_LO}"
    );

    // ⚑⚑ THE FORGED PREIMAGE IS INTERNALLY PERFECT — its own descriptor accepts it, asserted on
    // the CHECKED rail before the seam is asked anything. Without this, a red below could be the
    // preimage AIR refusing its own row and the tooth would prove nothing about the weld.
    {
        use dregg_circuit::descriptor_ir2::{
            MemBoundaryWitness, prove_vm_descriptor2, verify_vm_descriptor2,
        };
        let proof = prove_vm_descriptor2(
            &pdesc,
            &preimage_trace(forged.clone()),
            &forged_claim,
            &MemBoundaryWitness::default(),
            &[],
        )
        .expect("the FORGED body must prove against its own AIR — that is the whole hazard");
        verify_vm_descriptor2(&pdesc, &proof, &forged_claim)
            .expect("…and verify; this body is internally perfect and is not this block's");
    }
    // …and the chain link is honest and its own leaf proves.
    prove_chain_link_leaf_with(&cdesc, &link_trace(0), &pis[0], &inner)
        .expect("link 0 is honest and its leaf MUST prove");

    let err = expect_refusal(
        prove_body_preimage_link_adapter(
            &pdesc,
            &preimage_trace(forged),
            &forged_claim,
            &cdesc,
            &link_trace(0),
            &pis[0],
            &seam,
            &inner,
        ),
        "a body that is not this block's must be REFUSED by the seam even though both STARKs prove",
    );
    println!("\n§2 ⚑⚑⚑ A FOREIGN PREIMAGE REFUSED BY THE SEAM: {err}");

    // ⚑ THE POSITIVE POLE. This tooth's whole claim is that the 64 `cb.connect`s object, so the
    // refusal must BE a connect conflict. Anything else — a claim-layout guard, an FRI fault, an
    // OOM — means the connect was never built and this tooth would stay green with `apply_seam`
    // DELETED, which is the falsifier-that-stopped-falsifying class.
    assert!(
        binding_connect_marker(&err).is_some(),
        "the foreign preimage must be refused by the seam's own `cb.connect` — one of \
         {BINDING_CONNECT_MARKERS:?}; got: {err}"
    );
    assert!(
        !err.contains("is not the preimage descriptor") && !err.contains("claim"),
        "the adapter refused on SHAPE, before the seam existed; got: {err}"
    );
    assert!(
        !err.contains("exact-public"),
        "the ROM must be SILENT about which body this is — the SEAM is the whole binding; got: \
         {err}"
    );
}

/// ⚑⚑ **§2b — THE RIGHT BODY AT THE WRONG LINK.** Seam 0 welds absorbed elements 0 and 1; apply it
/// against link **1**, which absorbed elements 2 and 3. Both witnesses are honest, both STARKs
/// prove, and the false statement is only WHICH pair of the 49 this link took.
///
/// ⚠ This is the tooth that separates *"the preimage is welded"* from *"the preimage is welded in
/// ORDER"* — a family that welded the same block at every link would pass §2 and fail here.
#[test]
fn the_right_body_at_the_wrong_link_is_refused_by_the_seam() {
    let pis = all_link_pis();
    let inner = chain_inner_config();
    let pdesc = body_preimage_descriptor().expect("preimage descriptor");
    let cdesc = fp_chain_link_descriptor().expect("chain-link descriptor");
    let seam0 = body_preimage_seam(0).expect("seam 0");

    // The mutation is PRESENT: link 1's first absorbed element really is a different value from
    // link 0's, so the misapplication really does assert something false.
    assert_ne!(
        pis[0][ABSORBED_PI_LO], pis[1][ABSORBED_PI_LO],
        "links 0 and 1 must absorb different elements, or this tooth asserts nothing"
    );

    let err = expect_refusal(
        prove_body_preimage_link_adapter(
            &pdesc,
            &preimage_trace(preimage_row()),
            &preimage_claim(),
            &cdesc,
            &link_trace(1),
            &pis[1],
            &seam0,
            &inner,
        ),
        "the block's own preimage welded at the WRONG link must be REFUSED",
    );
    println!("\n§2b ⚑⚑ THE RIGHT BODY AT THE WRONG LINK REFUSED: {err}");
    assert!(
        binding_connect_marker(&err).is_some(),
        "the misordered weld must be refused by `cb.connect` — one of \
         {BINDING_CONNECT_MARKERS:?}; got: {err}"
    );

    // …and the CORRECT seam at the same link folds, so the refusal is the ORDER and not the link.
    let seam1 = body_preimage_seam(1).expect("seam 1");
    prove_body_preimage_link_adapter(
        &pdesc,
        &preimage_trace(preimage_row()),
        &preimage_claim(),
        &cdesc,
        &link_trace(1),
        &pis[1],
        &seam1,
        &inner,
    )
    .expect("seam 1 at link 1 MUST prove — the refusal above is the ORDER, not the link");
    println!("  …and seam 1 at link 1 proves, so the refusal is the order and not the link.");
}

// ============================================================================
// §3 — THE DROP-IN, EXHIBITED.
// ============================================================================

/// ⚑⚑⚑ **§3 — TWO ADAPTERS FOLD WITH THE UNMODIFIED `fold_chain_links`.**
///
/// The whole reason the adapter publishes the chain leaf's claim rather than a wider one: the fold
/// node, its VK pins, its 96-limb carry and its ordered transcript digest are untouched. The parent
/// claim here is the same object `mina_body_hash_chain_fold.rs` §1 asserts for two plain leaves —
/// with each link's absorbed pair now welded to a gated preimage.
///
/// `#[ignore]`d for wall clock only.
#[test]
#[ignore = "two adapters plus a fold; wall-clock only"]
fn two_adapters_fold_with_the_unmodified_chain_fold() {
    let pis = all_link_pis();
    let inner = chain_inner_config();
    let fold_cfg = chain_root_config();
    let pdesc = body_preimage_descriptor().expect("preimage descriptor");
    let cdesc = fp_chain_link_descriptor().expect("chain-link descriptor");

    let t0 = Instant::now();
    let mut leaves = Vec::new();
    for j in 0..2 {
        leaves.push(
            prove_body_preimage_link_adapter(
                &pdesc,
                &preimage_trace(preimage_row()),
                &preimage_claim(),
                &cdesc,
                &link_trace(j),
                &pis[j],
                &body_preimage_seam(j).expect("seam"),
                &inner,
            )
            .unwrap_or_else(|e| panic!("adapter at link {j}: {e}")),
        );
    }
    let leaves_ms = t0.elapsed().as_millis();

    let t1 = Instant::now();
    let node = fold_chain_links(
        &leaves[0],
        &leaves[1],
        &FoldVkPins::tracked(&leaves[0], &leaves[1]).expect("both children carry a commitment"),
        &fold_cfg,
    )
    .expect("two adapters MUST fold with the unmodified chain fold");
    let fold_ms = t1.elapsed().as_millis();

    verify_recursive_batch_proof_with_config(&node.0, &fold_cfg).expect("the folded node verifies");
    let claim = read_chain_claim(&node).expect("the node publishes a chain claim");
    assert_eq!(
        claim.transcript_acc,
        host_chain_transcript_acc(&pis[..2]),
        "the folded digest must be the host fold of the two links' absorbed pairs"
    );

    println!("\n═══ §3 ⚑⚑⚑ TWO ADAPTERS FOLDED, NODE UNMODIFIED ═══");
    println!("  2 adapters {leaves_ms} ms, 1 fold {fold_ms} ms");
    println!("  the 96-limb carry, the VK pins and the ordered digest are the chain fold's own.");
}

// ============================================================================
// §4 — THE WHOLE CHAIN, WELDED.
// ============================================================================

/// `MinaStateBodyHashChain.realBodyHash` — the `state_body_hash` of Mina devnet block **540221**.
const REAL_BODY_HASH: &str =
    "5693930022757138716743408081919214747940268519364092084787368564557482288885";

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

/// ⚑⚑⚑ **§4 — ALL 25 LINKS AS ADAPTERS: `BODYHASH` DERIVED WITH EVERY ABSORBED ELEMENT WELDED.**
///
/// The same root `mina_body_hash_chain_fold.rs` §4 derives — `in_state` the `MinaProtoStateBody`
/// salt, `out_state`'s lane 0 block 540221's `state_body_hash`, `transcript_acc` the ordered digest
/// of the 49 packed elements — but every one of the 25 leaves is an ADAPTER, so each link's
/// absorbed pair is welded, limb for limb, to a descriptor that gates those limbs as bytes and the
/// 2 381 chunk bits as bits.
///
/// ⚠ **THIS IS THE ROUTE, AND IT IS A TEST AND NOT A PRODUCTION PATH.** No node calls it: the
/// deployed 25-link fold still proves plain chain leaves, and
/// `turn::executor::mina_head_verifier`'s REFUSAL 16 is still what a node runs. What this test
/// establishes is that the route EXISTS and terminates on the same root value — not that anything
/// has been switched over.
///
/// `#[ignore]`d for wall clock only.
#[test]
#[ignore = "the whole 25-link welded body-hash fold; wall-clock only"]
fn the_whole_body_hash_chain_folds_with_every_link_welded() {
    let pis = all_link_pis();
    let inner = chain_inner_config();
    let fold_cfg = chain_root_config();
    let pdesc = body_preimage_descriptor().expect("preimage descriptor");
    let cdesc = fp_chain_link_descriptor().expect("chain-link descriptor");
    let row = preimage_row();
    let claim = preimage_claim();

    let adapter = |j: usize| {
        prove_body_preimage_link_adapter(
            &pdesc,
            &preimage_trace(row.clone()),
            &claim,
            &cdesc,
            &link_trace(j),
            &pis[j],
            &body_preimage_seam(j).expect("seam"),
            &inner,
        )
        .unwrap_or_else(|e| panic!("adapter at link {j}: {e}"))
    };

    let t0 = Instant::now();
    let mut acc = adapter(0);
    let mut welds = body_preimage_seam(0).unwrap().connect_count();
    for j in 1..BODY_LINKS {
        let leaf = adapter(j);
        welds += body_preimage_seam(j).unwrap().connect_count();
        acc = fold_chain_links(
            &acc,
            &leaf,
            &FoldVkPins::tracked(&acc, &leaf).expect("both children carry a commitment"),
            &fold_cfg,
        )
        .unwrap_or_else(|e| panic!("fold at link {j}: {e}"));
        println!("  welded {}/{BODY_LINKS} ({} s)", j + 1, t0.elapsed().as_secs());
    }
    let total_s = t0.elapsed().as_secs();

    verify_recursive_batch_proof_with_config(&acc.0, &fold_cfg).expect("the welded root verifies");

    let claim_out = read_chain_claim(&acc).expect("the root publishes a chain claim");
    assert_eq!(
        claim_out.in_state,
        pis[0][..96],
        "the root's incoming state must be the MinaProtoStateBody SALT"
    );
    assert_eq!(
        claim_out.transcript_acc,
        host_chain_transcript_acc(&pis),
        "the root's transcript digest must be the ordered fold of the 49 absorbed elements"
    );
    assert_eq!(
        limbs_to_decimal(&claim_out.out_state[..32]),
        REAL_BODY_HASH,
        "the root's outgoing lane 0 must be block 540221's `state_body_hash`"
    );
    assert_eq!(welds, BODY_LINKS * 2 * 32, "1 518 welds + 82 zero-pins");

    println!("\n═══ §4 ⚑⚑⚑ THE WHOLE 25-LINK CHAIN, WELDED, in {total_s} s ═══");
    println!("  root out0: {REAL_BODY_HASH}");
    println!("  {welds} in-circuit merges across 25 adapters — the preimage can no longer");
    println!("  disagree with the stream. ⚠ What a prover still chooses is the CONTENT.");
}
