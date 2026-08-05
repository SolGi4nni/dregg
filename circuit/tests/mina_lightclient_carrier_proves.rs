//! ⚑⚑ **THE MINA LIGHT CLIENT'S CARRIER, ON THE DEPLOYED PROVER — BOTH POLARITIES, IN RELEASE.**
//!
//! # What was missing
//!
//! Measured 2026-08-05: `dregg-mina-lightclient-verify::v1` had a Lean refinement, an emitted
//! descriptor, a served golden and a consumer that refuses a turn on it — and **no test anywhere
//! had ever handed it to `prove_vm_descriptor2`.** Eth, Tendermint, Solana and Midnight each have a
//! `*_lightclient_proves.rs`; Mina had `mina_link_segment_multirow.rs` for its multi-row companion
//! and nothing for the verify rung. A descriptor whose Lean says it discriminates but which no
//! prover has ever run is a descriptor whose refusals are `decide`s, not proofs.
//!
//! # What this file gates
//!
//! The rung that landed 2026-08-05: `PICKLES_OK` — a witnessed bit forced `= 1` with nothing
//! computing it — became two columns. `PICKLES_WITNESSED` is the residue and is still a bit, named
//! so. `WRAP_FS_PROVED` is not: its `= 1` guards **one nine-lane `proof_bind` constraint** pinning the row's
//! attested program, lane by lane, to the semantic fingerprint of `dregg-pasta-fq-chainlink::v1` —
//! an AIR that EXISTS, PROVES (proven here from the served descriptor, and folded 46 deep in
//! `circuit-prove/tests/mina_phase2_chain_fold.rs`) and whose fixture instance is Mina devnet block
//! 539508's own phase-2 `fq_kimchi` transcript.
//!
//! ⚑⚑ **RE-POINTED 2026-08-05, AND TWO THINGS WERE RED BEFORE IT.** This rung used to bind
//! `dregg-pasta-fq-wraplink::v1`, the SEVEN-block sibling that publishes two of a Poseidon state's
//! three outgoing lanes; the chainlink publishes all three, and it is the descriptor the 46-leaf
//! fold is built on. Separately, `adf5aa892` moved the head descriptor to 30 public inputs and this
//! file kept asserting 29 — so nine of its ten tests were failing with a SHAPE FAULT, which
//! `refusal::must_refuse` correctly reports as a panic rather than a refusal. Both are fixed here;
//! neither was fixed by the other.
//!
//! ⚠ **SCOPE — read before the results.** A verifying head proof does NOT mean a Pickles proof is
//! valid. It means: the row published a canonical anchor and tip, derived its height from the pinned
//! anchor plus the exhibited segment, met a floored Samasika depth, AND named a sub-proof of the
//! chainlink program whose public-input commitment it published. What that sub-proof establishes is
//! ONE absorption of an Fq transcript — the full statement and its three named residuals are in
//! `turn/src/executor/mina_head_verifier.rs`'s module docs and `LightClientMinaAir` §2b.
//!
//! ⚑ **RELEASE, DELIBERATELY** — plonky3's algebraic refusals are `debug_assert` panics in debug and
//! clean `Err(OodEvaluationMismatch)` in release. Every refusal here goes through
//! `dregg_circuit::refusal`, which catches both, but the RELEASE reading is the deployed one.
//!
//! Run: `cargo test -p dregg-circuit --release --test mina_lightclient_carrier_proves -- --nocapture`

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, VmConstraint2, parse_vm_descriptor2,
    prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::heap_root::HeapLeaf;
use dregg_circuit::refusal;

const MINA_LC_VERIFY_DESCRIPTOR: &str = "dregg-mina-lightclient-verify::v1";
const CHAINLINK_DESCRIPTOR: &str = "dregg-pasta-fq-chainlink::v1";

/// ⚑ **ONE TRACE, TWO DESCRIPTORS — and the proof below is what establishes it, not this comment.**
/// `pasta-fq-wraplink.json` and `pasta-fq-chainlink.json` are the same `programAir qLimb absorbProg`
/// (`MinaPhase2Chain.the_chain_air_extends_the_program_air`), and this fixture is block 539508's
/// 46th and last phase-2 permutation — which is both the wraplink's fixture instance and the chain's
/// link 45 (`the_chain_meets_the_emitted_link`). So this ONE tracked witness satisfies the
/// eight-block chain-link descriptor at link 45's public inputs, and
/// `the_named_sub_proof_proves_from_the_served_descriptor` is exactly that claim, discharged by the
/// deployed prover.
///
/// That is why no second 3.1 MB fixture is tracked: the emit directory's 46 traces stay gitignored
/// (~150 MB) and nothing here depends on them. (Measured 2026-08-05: this file and the emitted
/// `fixtures/pasta-fq-chainlink/link-45-trace.txt` are byte-identical, md5
/// `c1c1df266dfe7d1881ec510898eb6b72` — a measurement, stated as one; the TEST is the gate.)
const LINK_TRACE: &str = include_str!("fixtures/pasta-fq-wraplink-trace.txt");
/// ⚑ The 46 chain links' public-input vectors, one line each — the TRACKED aggregate. Link 45's line
/// is the sub-proof the honest head names. Read from here rather than from the gitignored emit
/// directory, which compiles for whoever ran the emit and REDS for every fresh clone.
const CHAINLINK_ALL_PIS: &str = include_str!("fixtures/pasta-fq-chainlink-pis.txt");
/// The number of links the phase-2 chain folds — one tracked PI line each.
const CHAINLINK_LINKS: usize = 46;
/// `chainPins`' layout is `in(3) ++ out(3) ++ absorbed(2)`, so the first absorbed element is block 6.
const ABSORBED_BLOCK: usize = 6;

// ── The Lean column layout (`LightClientMinaAir` §1). ────────────────────────────────────────────
const SEG_LEN: usize = 0;
const ANCHOR_H: usize = 1;
const SUBMIT_H: usize = 2;
const WIT_DEPTH: usize = 3;
const REQ_DEPTH: usize = 4;
const SEG_SLACK: usize = 5;
const ANCH_SLACK: usize = 6;
const DEPTH_SLACK: usize = 7;
const LINK_OK: usize = 8;
const PICKLES_WITNESSED: usize = 9;
const CANON_OK: usize = 10;
const BLOCK_LEN: usize = 11;
const ANCHOR_STATE_0: usize = 12;
const TIP_STATE_0: usize = 21;
/// ⚑ The recursion carrier — the first column of this descriptor a prover cannot simply write down.
const WRAP_FS_PROVED: usize = 30;
const SUB_VK_0: usize = 31;
const SUB_PI_0: usize = 40;
const MINA_LC_WIDTH: usize = 49;
const MINA_PI_COUNT: usize = 30;
const STATE_LANES: usize = 9;
const PI_SUB_COMMIT_BASE: usize = 20;
/// ⚑ PI slot 29 — the weak-subjectivity anchor's `blockchain_length` (`LightClientMinaAir.PI_ANCHOR_H`).
/// Added by `adf5aa892`; this file asserted 29 PIs for hours afterwards and every prove in it was a
/// SHAPE FAULT rather than a refusal, so all nine polarity tests were red and reporting a panic.
const PI_ANCHOR_H: usize = 29;

const TRACE_ROWS: usize = 8;

/// Devnet **genesis** `3NL93SipJfAMNDBRfQ8Uo8LPovC74mnJZfZYB5SK7mTtkL72dsPx`, as nine base-`2^29`
/// lanes — `LightClientMinaAir.GENESIS_ANCHOR_LANES`, itself pinned against the Base58Check decode.
const GENESIS_ANCHOR_LANES: [u32; 9] = [
    317368465, 122552485, 518650043, 481937944, 112457995, 488503206, 390747624, 350427965, 1320595,
];
/// Devnet block **539508** — the block whose Wrap proof o1-labs' `kimchi::verifier::verify` accepts.
const DEVNET_TIP_LANES: [u32; 9] = [
    148400356, 2288994, 332868807, 237767070, 530455789, 507531490, 336317945, 425818875, 3793778,
];
/// `LightClientMinaAir.CHAINLINK_VK_LANES` — the nine `Faithful9` lanes of the CHAINLINK descriptor's
/// semantic fingerprint. `mina_transcript_carrier_binding.rs` recomputes these from that
/// descriptor's own bytes; here they are the row a prover must fill.
const CHAINLINK_VK_LANES: [u32; 9] = [
    40589529, 494773874, 527776693, 373808410, 118028044, 372824034, 512521559, 25478361, 4577485,
];
/// `LightClientMinaAir.CHAINLINK_PI_LANES` — the nine lanes of the digest of the chainlink
/// sub-proof's 256 public inputs on the block-539508 instance's 46th and last link.
const CHAINLINK_PI_LANES: [u32; 9] = [
    76470648, 44150818, 361910605, 443692671, 242143308, 490185822, 240590146, 360276303, 4019771,
];

fn desc() -> EffectVmDescriptor2 {
    descriptor_by_name(MINA_LC_VERIFY_DESCRIPTOR)
        .expect("the served Mina anchored-head verify descriptor must dispatch")
}

fn felt(v: i64) -> BabyBear {
    BabyBear::new(v.rem_euclid(2_013_265_921) as u32)
}

/// ⚑ **THE HONEST ROW** — the same values `LightClientMinaAir.honestRow` carries, so the Lean
/// `decide` and the deployed prover are looking at ONE object. Anchor pinned at height 1000, 300
/// exhibited blocks, settlement submitted at 1010, Samasika `k = 290` met exactly.
fn honest_cells() -> Vec<i64> {
    let mut c = vec![0i64; MINA_LC_WIDTH];
    c[SEG_LEN] = 300;
    c[ANCHOR_H] = 1000;
    c[SUBMIT_H] = 1010;
    c[WIT_DEPTH] = 290;
    c[REQ_DEPTH] = 290;
    c[SEG_SLACK] = 299;
    c[ANCH_SLACK] = 10;
    c[DEPTH_SLACK] = 0;
    c[LINK_OK] = 1;
    c[PICKLES_WITNESSED] = 1;
    c[CANON_OK] = 1;
    c[BLOCK_LEN] = 1300;
    for i in 0..STATE_LANES {
        c[ANCHOR_STATE_0 + i] = i64::from(GENESIS_ANCHOR_LANES[i]);
        c[TIP_STATE_0 + i] = i64::from(DEVNET_TIP_LANES[i]);
        c[SUB_VK_0 + i] = i64::from(CHAINLINK_VK_LANES[i]);
        c[SUB_PI_0 + i] = i64::from(CHAINLINK_PI_LANES[i]);
    }
    c[WRAP_FS_PROVED] = 1;
    c
}

/// The public inputs the row's thirty pins publish, read OFF THE ROW so a tampered column and
/// its publication cannot silently disagree.
fn pis_of(cells: &[i64]) -> Vec<BabyBear> {
    let mut pis = vec![BabyBear::new(0); MINA_PI_COUNT];
    for i in 0..STATE_LANES {
        pis[i] = felt(cells[ANCHOR_STATE_0 + i]);
        pis[STATE_LANES + i] = felt(cells[TIP_STATE_0 + i]);
        pis[PI_SUB_COMMIT_BASE + i] = felt(cells[SUB_PI_0 + i]);
    }
    pis[2 * STATE_LANES] = felt(cells[BLOCK_LEN]);
    pis[2 * STATE_LANES + 1] = felt(cells[REQ_DEPTH]);
    // ⚑ The anchor height, PUBLISHED since `adf5aa892`. Read off the row like every other pin, so a
    // tampered `ANCHOR_H` and its publication cannot silently disagree.
    pis[PI_ANCHOR_H] = felt(cells[ANCHOR_H]);
    pis
}

fn trace_of(cells: &[i64]) -> Vec<Vec<BabyBear>> {
    let row: Vec<BabyBear> = cells.iter().map(|&v| felt(v)).collect();
    vec![row; TRACE_ROWS]
}

fn prove_and_verify(
    d: &EffectVmDescriptor2,
    cells: &[i64],
    pis: &[BabyBear],
) -> Result<(), String> {
    let trace = trace_of(cells);
    refusal::assert_committed_shape("mina lightclient carrier", d, &trace, pis);
    let proof = prove_vm_descriptor2(d, &trace, pis, &MemBoundaryWitness::default(), &[])
        .map_err(|e| format!("prover refused: {e}"))?;
    verify_vm_descriptor2(d, &proof, pis).map_err(|e| format!("verifier refused: {e:?}"))
}

// ═══ §1 — THE SHAPE THE LEAN EMITTED ════════════════════════════════════════════════════════════

/// The served descriptor is the one Lean emitted, at the shape the rung declares.
#[test]
fn the_served_descriptor_has_the_recursion_shape() {
    let d = desc();
    assert_eq!(d.trace_width, MINA_LC_WIDTH);
    assert_eq!(d.public_input_count, MINA_PI_COUNT);
    // ⚑ 2026-08-05, the `ProofBind` widening: NINE one-felt binds collapsed into ONE nine-lane
    // bind, so the constraint count drops by eight and the bind count is 1.
    assert_eq!(
        d.constraints.len(),
        62,
        "50 + the carrier gate + 1 nine-lane bind + 9 commitment pins + the ANCHOR_H pin"
    );
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
        "one proof_bind, carrying every program lane"
    );
    assert_eq!(
        binds[0].vk.len(),
        STATE_LANES,
        "the seam ties all nine program lanes — a prefix pin is refused at admission"
    );
    assert_eq!(binds[0].commit.len(), STATE_LANES);
    assert_eq!(
        binds[0].vk_pin.as_ref().map(Vec::len),
        Some(STATE_LANES),
        "the program pin names every lane"
    );

    // ⚑ AND THE SUB-PROOF DESCRIPTOR IT NAMES IS ACTUALLY SERVED. A recursion bind to a program
    // this node cannot load would make the consumer's refusal unreachable — the fail-open shape.
    let link = descriptor_by_name(CHAINLINK_DESCRIPTOR)
        .expect("the Fq-transcript sub-proof descriptor must dispatch (fail-closed otherwise)");
    assert_eq!(
        link.public_input_count, 256,
        "eight 32-limb pin blocks: in(3) ++ out(3) ++ absorbed(2)"
    );

    // ⚑⚑ AND THE SEVEN-BLOCK WRAPLINK IS NO LONGER SERVED. It pinned two of a Poseidon state's
    // three outgoing lanes, so a consumer welding a fold root to it compared 64 of 96 limbs. Both
    // names cannot be resolvable at once without the next reader picking the wrong one.
    assert!(
        descriptor_by_name("dregg-pasta-fq-wraplink::v1").is_none(),
        "the seven-block wraplink must NOT dispatch: a pre-flag-day proof identity is answered \
         None and REFUSED, never reinterpreted under a program that pins one fewer sponge lane"
    );
}

// ═══ §2 — POLARITY ONE: THE HONEST HEAD PROVES ══════════════════════════════════════════════════

/// ⚑⚑ **THE MINA ANCHORED-HEAD VERIFY DESCRIPTOR PROVES AND VERIFIES — for the first time on the
/// deployed prover**, on the REAL devnet genesis anchor and the REAL block-539508 tip, carrying the
/// recursion binds to the real chainlink fingerprint.
#[test]
fn the_honest_anchored_head_proves() {
    let cells = honest_cells();
    let pis = pis_of(&cells);
    refusal::must_accept(
        "honest Mina anchored head with the recursion carrier",
        || prove_and_verify(&desc(), &cells, &pis),
    );
}

// ═══ §3 — POLARITY TWO: THE CARRIER IS NOT A BIT ════════════════════════════════════════════════

/// ⚑⚑ **A ROW THAT NAMES A DIFFERENT PROGRAM IS REFUSED BY A GATE.** One lane of the nine, bumped
/// by ONE — still a canonical `Faithful9` digit, so no range lookup can be what refuses it. This is
/// the forgery the witnessed `PICKLES_OK = 1` waved through for its entire life: a prover asserting
/// "someone verified the Mina proof" with nothing behind it.
#[test]
fn a_row_naming_a_different_program_is_refused() {
    let mut cells = honest_cells();
    cells[SUB_VK_0] += 1;
    let pis = pis_of(&cells);
    let e = refusal::must_refuse(
        "a head row attesting a program that is not the chainlink AIR",
        || prove_and_verify(&desc(), &cells, &pis),
    );
    refusal::assert_violated_constraint_not_bus("forged program lane", &e);
}

/// ⚑ …and the LAST lane too, so the refusal is not an artifact of lane 0 being special.
#[test]
fn a_forged_top_program_lane_is_refused() {
    let mut cells = honest_cells();
    cells[SUB_VK_0 + 8] += 1;
    let pis = pis_of(&cells);
    refusal::must_refuse("a head row whose top program lane is forged", || {
        prove_and_verify(&desc(), &cells, &pis)
    });
}

/// ⚑⚑ **THE GUARD CANNOT BE SWITCHED OFF.** A prover who would rather not name a sub-proof at all
/// sets `WRAP_FS_PROVED = 0` — which makes all nine `guard·(vk − vk_pin)` congruences hold
/// vacuously. G9 (`WRAP_FS_PROVED = 1`) is what stops that, and without it the whole rung would be
/// an opt-in. This is the theorem `mina_bind_guard_cannot_be_disarmed` on the prover.
#[test]
fn disarming_the_recursion_guard_is_refused() {
    let mut cells = honest_cells();
    cells[WRAP_FS_PROVED] = 0;
    // A prover disarming the guard would also blank the program lanes it no longer has to fill.
    for i in 0..STATE_LANES {
        cells[SUB_VK_0 + i] = 0;
    }
    let pis = pis_of(&cells);
    refusal::must_refuse("a head row with the recursion guard disarmed", || {
        prove_and_verify(&desc(), &cells, &pis)
    });
}

/// ⚑ **THE PUBLISHED COMMITMENT IS PINNED TO THE ROW.** A prover that keeps the honest row but
/// publishes a different sub-proof commitment (so it can hand over some OTHER verifying chainlink
/// proof) is refused by the PI binding.
#[test]
fn publishing_a_commitment_the_row_does_not_hold_is_refused() {
    let cells = honest_cells();
    let mut pis = pis_of(&cells);
    pis[PI_SUB_COMMIT_BASE] = felt(i64::from(CHAINLINK_PI_LANES[0]) + 1);
    refusal::must_refuse(
        "a head proof publishing a commitment its row does not carry",
        || prove_and_verify(&desc(), &cells, &pis),
    );
}

/// The pre-existing teeth still bite with the widened row — a regression guard on the rung, since a
/// width change that broke the height derivation would be invisible to the new tests alone.
#[test]
fn the_forged_blockchain_length_is_still_refused() {
    let mut cells = honest_cells();
    cells[SEG_LEN] = 5;
    cells[SEG_SLACK] = 4;
    let pis = pis_of(&cells);
    refusal::must_refuse("the free-`blockchain_length` liar", || {
        prove_and_verify(&desc(), &cells, &pis)
    });
}

// ═══ §4 — THE SUB-PROOF IS REAL, AND A TAMPERED TRANSCRIPT IS REFUSED ═══════════════════════════

fn link_trace() -> Vec<Vec<BabyBear>> {
    LINK_TRACE
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|c| BabyBear::new(c.parse::<u32>().expect("cell is a u32 decimal")))
                .collect()
        })
        .collect()
}

/// Link 45's raw public inputs: the LAST line of the tracked 46-line aggregate.
fn link_pis_raw() -> Vec<u32> {
    let n = CHAINLINK_ALL_PIS.lines().count();
    assert_eq!(
        n, CHAINLINK_LINKS,
        "the tracked chain-link PI aggregate carries {n} lines; the fold is {CHAINLINK_LINKS} links \
         — re-emit it rather than reading a truncated chain"
    );
    CHAINLINK_ALL_PIS
        .lines()
        .nth(CHAINLINK_LINKS - 1)
        .expect("checked non-empty above")
        .split_whitespace()
        .map(|c| c.parse::<u32>().expect("PI is a u32 decimal"))
        .collect()
}

fn link_pis() -> Vec<BabyBear> {
    link_pis_raw().into_iter().map(BabyBear::new).collect()
}

/// ⚑⚑ **THE PROGRAM THE CARRIER PINS IS ONE A PROVER CAN ACTUALLY DISCHARGE.** A pin to a program
/// nobody can prove would be a carrier nobody can set — completeness would be zero and the rung
/// would be a ban. This proves the sub-proof the honest head names, from the committed Lean-emitted
/// fixture, through the same `descriptor_by_name` dispatch the consumer uses.
#[test]
fn the_named_sub_proof_proves_from_the_served_descriptor() {
    let d = descriptor_by_name(CHAINLINK_DESCRIPTOR).expect("served");
    let trace = link_trace();
    let pis = link_pis();
    assert_eq!(pis.len(), d.public_input_count);
    refusal::must_accept("the Fq-transcript sub-proof the Mina head names", || {
        let proof = prove_vm_descriptor2(&d, &trace, &pis, &MemBoundaryWitness::default(), &[])
            .map_err(|e| format!("prover refused: {e}"))?;
        verify_vm_descriptor2(&d, &proof, &pis).map_err(|e| format!("verifier refused: {e:?}"))
    });
}

/// ⚑⚑ **A TAMPERED TRANSCRIPT IS REFUSED BY A GATE.** The absorbed element is a register operand
/// with a ZERO immediate, so the instruction ROM says nothing about it — the BOUNDARY PIN is what
/// refuses it, which is exactly where `MinaBlockFqTranscript` §"which gate refuses what" says the
/// transcript binding rests. One limb of the 91st tape element, moved.
#[test]
fn a_tampered_transcript_element_is_refused_by_the_pin() {
    let d = descriptor_by_name(CHAINLINK_DESCRIPTOR).expect("served");
    let trace = link_trace();
    let mut pis = link_pis();
    // ⚑ `chainPins` is `in(3) ++ out(3) ++ absorbed(2)`, so the first absorbed element is PI BLOCK
    // SIX (limbs 192..223) — NOT block 3, which is the outgoing `v'` lane under this layout.
    let sk = 32usize;
    pis[ABSORBED_BLOCK * sk] = BabyBear::new((pis[ABSORBED_BLOCK * sk].as_u32() + 1) % 256);
    refusal::must_refuse(
        "a chainlink proof whose absorbed transcript element was moved",
        || {
            let proof = prove_vm_descriptor2(&d, &trace, &pis, &MemBoundaryWitness::default(), &[])
                .map_err(|e| format!("prover refused: {e}"))?;
            verify_vm_descriptor2(&d, &proof, &pis).map_err(|e| format!("verifier refused: {e:?}"))
        },
    );
}

/// ⚑⚑ **AND A TAMPERED TRANSCRIPT CANNOT REUSE THE HEAD PROOF.** The head row publishes the digest
/// of the sub-proof's public inputs; moving one of them moves the digest, so the nine lanes the
/// honest head carries no longer describe the tampered sub-proof. Stated on the digest so the
/// coupling is arithmetic rather than a claim about the consumer's code.
#[test]
fn a_tampered_transcript_moves_the_published_commitment() {
    let mut raw: Vec<u32> = link_pis_raw();
    let honest = chainlink_pi_commitment(&raw);
    raw[ABSORBED_BLOCK * 32] = (raw[ABSORBED_BLOCK * 32] + 1) % 256;
    let tampered = chainlink_pi_commitment(&raw);
    assert_ne!(
        honest, tampered,
        "a moved transcript element must move the commitment the head row publishes"
    );
    assert_eq!(
        key_lanes9(&honest).map(|v| v as u32),
        CHAINLINK_PI_LANES,
        "and the HONEST digest is the one the honest head row carries"
    );
}

/// blake3 derive-key over the consumer's context; kept byte-identical to
/// `dregg_turn::executor::mina_head_verifier::chainlink_pi_commitment`, which
/// `mina_transcript_carrier_binding.rs` gates against the Lean literal.
fn chainlink_pi_commitment(pis: &[u32]) -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key(
        "dregg.mina-lightclient.chainlink-subproof-pi-commitment.v1",
    );
    h.update(&(pis.len() as u64).to_le_bytes());
    for v in pis {
        h.update(&v.to_le_bytes());
    }
    *h.finalize().as_bytes()
}

fn key_lanes9(bytes: &[u8; 32]) -> [u64; 9] {
    let mut v = [0u64; 9];
    let mut acc: u128 = 0;
    let mut bits = 0usize;
    let mut out = 0usize;
    for b in bytes.iter() {
        acc |= (*b as u128) << bits;
        bits += 8;
        while bits >= 29 && out < 8 {
            v[out] = (acc & ((1u128 << 29) - 1)) as u64;
            acc >>= 29;
            bits -= 29;
            out += 1;
        }
    }
    v[8] = acc as u64;
    v
}

/// Silence the unused-import lint when `HeapLeaf` is only needed by the shape helper above.
#[allow(dead_code)]
fn _heaps() -> Vec<Vec<HeapLeaf>> {
    vec![]
}
