//! # THE A/−A TOOTH — a deployed sovereign key and its NEGATION must publish different teeth.
//!
//! ## SUBSTRATE, SAID OUT LOUD
//!
//! Lean-authored AIR. The gate under test (`Emit.CarrierOctetGates.keyCommitConstraints` /
//! `withSovereignKeyCommit`) is emitted from Lean into
//! `circuit/descriptors/rotation-wide-registry-staged.tsv`; this file writes no constraint. What it
//! adds is the EXHIBIT — the concrete pair the gate must separate, driven through the deployed
//! dispatcher and the deployed prover.
//!
//! ## The wound, and why the cheap fix was forbidden
//!
//! `canonical_32_to_felts_8` and every eight-lane successor packed a 32-byte key into eight
//! BabyBear lanes. Nine is the minimum (`p^8 < 2^256`), so the key-nonet flag day (`6441705e8`)
//! replaced the encoder — but the KEY_COMMIT teeth gate kept reading the EIGHT committed octet
//! columns and never the ninth lane. RFC 8032 puts an Ed25519 point's x-sign in bit 7 of byte 31 =
//! source bit 255 = bit 23 of nonet lane 8, and lane 8 is the ONLY committed column that carries
//! it. So `A` and `−A` — a keypair whose private half is `-a mod L`, which an attacker HOLDS —
//! produced bit-identical KEY_COMMIT teeth, and the sovereign teeth could not tell one from the
//! other.
//!
//! Independently, `6441705e8` re-pointed `TurnExecutor::pubkey_to_witness_key_commit` at a
//! DIFFERENT fold (one arity-16 absorb over the nonet), so from that commit the executor and the
//! AIR checked different functions and every honest `makeSovereign` diverged in the transcript. The
//! single-file repair — point the executor back at the octet recipe — would have made the member
//! green while re-opening the A/−A blindness, which is the containment `CLAUDE.md` forbids.
//!
//! The repair does both: `quadIdx` row 2 moved `[0,4,2,6] → [8,0,4,2]` (full nine-lane cover at
//! UNCHANGED arity, UNCHANGED `KEY_COMMIT_SPAN = 32`, UNCHANGED trace width and PI count), and the
//! executor, the producer rider and the Lean spec now name ONE denotation whose interleave matrix
//! is EMITTED from the AIR (`layout_generated::KEY_COMMIT_QUAD_IDX`).
//!
//! ## What each tooth here bites
//!
//! * `a_key_and_its_negation_publish_different_teeth` — the value-level exhibit on a REAL
//!   curve25519 pair, plus the assertion that exactly ONE tooth moves (quad 2, the only quad that
//!   reads lane 8).
//! * `the_retired_octet_matrix_merged_the_pair` — the REFUTATION OBJECT. The retired
//!   `[0,4,2,6]`-over-the-octet recipe is kept HERE, with no call site anywhere in the tree, and it
//!   is shown to merge the very pair the tooth above separates. Without it the tooth cannot
//!   distinguish "the fix works" from "these two keys were never going to collide anyway".
//! * `the_deployed_row_reads_the_ninth_lane` — the COMMITTED BYTES. The emitted makeSovereign row's
//!   four key-commit chip lookups must, between them, name all nine nonet columns; the ninth-lane
//!   column must appear in exactly one.
//! * `deployed_prover_refuses_a_negated_owner_key` — the pair at the DEPLOYED PROVER: a leg minted
//!   for owner `−A` carrying `A`'s teeth is UNSAT, by a violated CONSTRAINT and not a bus
//!   imbalance. This is the pole that was ACCEPTED before the repair.
//! * `deployed_prover_accepts_the_honest_owner_key` — the honest pole, so the refusal above is not
//!   "it rejects everything".

mod binding_tooth;

use dregg_cell::{CellMode, Ledger};
use dregg_circuit::descriptor_ir2::WindowExpr;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, UMemBoundaryWitness, VmConstraint2, chip_absorb_all_lanes,
    parse_vm_descriptor2, prove_vm_descriptor2_for_config,
};
use dregg_circuit::effect_vm::layout_generated::{
    B_PUBKEY_NINTH_LANE, B_PUBKEY_OCTET, KEY_COMMIT_QUAD_IDX,
};
use dregg_circuit::effect_vm::trace_rotated::{
    BEFORE_BASE, RotatedBlockWitness, empty_caveat_manifest,
    generate_rotated_effect_vm_descriptor_and_trace_wide,
};
use dregg_circuit::effect_vm::{CellState, Effect, PUBKEY_NONET_LANE_COL, key_limbs9};
use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};
use dregg_circuit::refusal::{
    assert_violated_constraint_not_bus, must_accept, must_refuse_or_unsat_panic,
};
use dregg_circuit_prove::ivc_turn_chain::{SOVEREIGN_KEY_COMMIT_PI_LO, ir2_leaf_wrap_config};
use dregg_circuit_prove::sovereign_leaf_adapter::KEY_COMMIT_LEN;
use dregg_turn::rotation_witness as rw;

/// SCOPE — printed by every test in this file.
fn scope() {
    println!(
        "ANSWERS:         do a deployed sovereign owner key and its curve NEGATION publish different KEY_COMMIT teeth, does the committed makeSovereign row's key-commit gate read the ninth nonet lane, and does the deployed prover REFUSE a leg whose committed owner nonet is the negation of the key its published teeth digest?"
    );
    println!(
        "DOES NOT ANSWER: whether possession of the private half is checked anywhere. Nothing here signs. What is bound is that the committed nonet DETERMINES the published teeth over all nine lanes — a key-substitution tooth, not an authentication one. It also does not answer whether the teeth are collision-resistant: that rests on the Poseidon2 chip's soundness, which this test assumes and does not measure."
    );
}

/// The live registry key of the deployed keyed sovereign member.
const SOVEREIGN_KEY: &str = "makeSovereignVmDescriptor2R24";

// ============================================================================
// The pair
// ============================================================================

/// A genuine curve25519 keypair's public half and the public half of its NEGATION.
///
/// `A = a·B` and `−A = (−a mod L)·B` are both honest public keys, and an attacker who holds `a`
/// holds `−a`. Their compressed encodings differ in exactly one bit — bit 7 of byte 31, the x-sign
/// (RFC 8032 §5.1.2) — which is source bit 255 and therefore bit 23 of nonet lane 8 and of NO other
/// lane. That is the whole reason the eight-lane cover was blind to this pair.
fn key_and_its_negation() -> ([u8; 32], [u8; 32]) {
    use curve25519_dalek::constants::ED25519_BASEPOINT_TABLE;
    use curve25519_dalek::scalar::Scalar;

    // A fixed, reduced secret scalar — the test is deterministic on purpose.
    let mut seed = [0u8; 32];
    for (i, b) in seed.iter_mut().enumerate() {
        *b = (i as u8).wrapping_mul(7).wrapping_add(11);
    }
    let a = Scalar::from_bytes_mod_order(seed);
    let point = &a * ED25519_BASEPOINT_TABLE;
    let neg_point = -point;
    // `-a mod L` really does produce the negated point: the attacker's key is a KEY.
    let neg_a = -a;
    assert_eq!(
        (&neg_a * ED25519_BASEPOINT_TABLE).compress().to_bytes(),
        neg_point.compress().to_bytes(),
        "the negated point must be the public half of the negated scalar"
    );
    (point.compress().to_bytes(), neg_point.compress().to_bytes())
}

/// ⚑ **THE REFUTATION OBJECT — the RETIRED eight-lane key-commit recipe.**
///
/// Four `chip_absorb_all_lanes(4, ..)` folds over the interleave `[0,1,2,3] · [4,5,6,7] ·
/// [0,4,2,6] · [1,5,3,7]` applied to nonet lanes 0..7 ONLY — exactly what
/// `trace_rotated::append_sovereign_key_commit_rider` computed and what
/// `CarrierOctetGates.quadIdx` emitted until 2026-08-08.
///
/// It has NO call site anywhere in the tree. It lives here so
/// `the_retired_octet_matrix_merged_the_pair` has an object to refute: a separation tooth whose
/// "before" picture is prose cannot tell a repair from a coincidence.
fn retired_octet_key_commit(pubkey: &[u8; 32]) -> [BabyBear; 4] {
    const RETIRED_QUAD_IDX: [[usize; 4]; 4] =
        [[0, 1, 2, 3], [4, 5, 6, 7], [0, 4, 2, 6], [1, 5, 3, 7]];
    let nonet = key_limbs9(pubkey);
    std::array::from_fn(|q| {
        let inputs: [BabyBear; 4] = std::array::from_fn(|j| nonet[RETIRED_QUAD_IDX[q][j]]);
        chip_absorb_all_lanes(4, &inputs)[0]
    })
}

// ============================================================================
// TOOTH 1 — the value-level separation, and the refutation it needs
// ============================================================================

#[test]
fn a_key_and_its_negation_publish_different_teeth() {
    scope();
    let (a, neg_a) = key_and_its_negation();

    // The pair really is a bit-255 flip and nothing else — otherwise the tooth would be separating
    // two unrelated keys and proving nothing about the x-sign.
    assert_eq!(a[..31], neg_a[..31], "the pair must agree on bytes 0..31");
    assert_eq!(
        a[31] ^ neg_a[31],
        0x80,
        "the pair must differ in exactly bit 7 of byte 31 — the RFC 8032 x-sign"
    );

    // …and that flip lands in lane 8 of the committed nonet, and nowhere else.
    let (la, ln) = (key_limbs9(&a), key_limbs9(&neg_a));
    for lane in 0..8 {
        assert_eq!(
            la[lane], ln[lane],
            "lanes 0..7 must be IDENTICAL — this is why an eight-lane cover was blind"
        );
    }
    assert_ne!(la[8], ln[8], "lane 8 must carry the x-sign");

    // THE EXHIBIT.
    let teeth_a = dregg_turn::executor::TurnExecutor::pubkey_to_witness_key_commit(&a);
    let teeth_n = dregg_turn::executor::TurnExecutor::pubkey_to_witness_key_commit(&neg_a);
    assert_ne!(
        teeth_a, teeth_n,
        "A KEY AND ITS NEGATION MUST PUBLISH DIFFERENT KEY_COMMIT TEETH"
    );

    // …and EXACTLY the quad that reads lane 8 moves. This pins WHERE the separation comes from, so
    // a future matrix edit that separates the pair by accident (through some other lane) still
    // fails here rather than passing as the same guarantee.
    let moved: Vec<usize> = (0..KEY_COMMIT_LEN)
        .filter(|&q| teeth_a[q] != teeth_n[q])
        .collect();
    let expect: Vec<usize> = (0..KEY_COMMIT_LEN)
        .filter(|&q| KEY_COMMIT_QUAD_IDX[q].contains(&8))
        .collect();
    assert_eq!(
        moved, expect,
        "exactly the quads that read lane 8 may move; the emitted matrix says {expect:?}"
    );
    assert_eq!(
        expect,
        vec![2],
        "the emitted matrix must read lane 8 in exactly one quad (Lean \
         `quadIdx_row2_reads_the_ninth_lane`)"
    );
}

#[test]
fn the_retired_octet_matrix_merged_the_pair() {
    scope();
    let (a, neg_a) = key_and_its_negation();
    assert_eq!(
        retired_octet_key_commit(&a),
        retired_octet_key_commit(&neg_a),
        "the retired eight-lane recipe MUST merge the pair — if it does not, this file's \
         refutation object has rotted and the separation tooth above is unanchored"
    );
    // …and the live recipe must not BE the retired one (the mutation is live, not a no-op).
    assert_ne!(
        dregg_turn::executor::TurnExecutor::pubkey_to_witness_key_commit(&a),
        retired_octet_key_commit(&a),
        "the deployed teeth function must differ from the retired one on the honest key too — \
         otherwise the 'repair' is the same object under a new name"
    );
}

// ============================================================================
// TOOTH 2 — the committed bytes read the ninth lane
// ============================================================================

fn deployed_sovereign_descriptor() -> EffectVmDescriptor2 {
    let json = WIDE_REGISTRY_STAGED_TSV
        .lines()
        .find_map(|line| {
            let mut it = line.splitn(3, '\t');
            if it.next() == Some(SOVEREIGN_KEY) {
                let _display = it.next();
                it.next()
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("{SOVEREIGN_KEY} not in WIDE_REGISTRY_STAGED_TSV"));
    parse_vm_descriptor2(json).expect("deployed wide descriptor parses")
}

/// The four teeth columns as the DEPLOYED DESCRIPTOR pins them (post-E1-compaction frame), read off
/// its own `pi_binding` constraints rather than from a Rust constant.
fn committed_teeth_col(desc: &EffectVmDescriptor2) -> usize {
    let cols: Vec<usize> = (0..KEY_COMMIT_LEN)
        .map(|q| {
            desc.constraints
                .iter()
                .find_map(|c| match c {
                    VmConstraint2::Base(VmConstraint::PiBinding {
                        row: VmRow::First,
                        col,
                        pi_index,
                    }) if *pi_index == SOVEREIGN_KEY_COMMIT_PI_LO + q => Some(*col),
                    _ => None,
                })
                .unwrap_or_else(|| panic!("teeth {q} must be row-0-pinned"))
        })
        .collect();
    let base = cols[0];
    assert_eq!(
        cols,
        (0..KEY_COMMIT_LEN).map(|q| base + q).collect::<Vec<_>>()
    );
    base
}

/// The columns a `WindowExpr` reads on the CURRENT row.
fn window_cols(e: &WindowExpr, out: &mut Vec<usize>) {
    match e {
        WindowExpr::Loc(c) => out.push(*c),
        WindowExpr::Nxt(_) | WindowExpr::Const(_) => {}
        WindowExpr::Add(a, b) | WindowExpr::Mul(a, b) => {
            window_cols(a, out);
            window_cols(b, out);
        }
    }
}

#[test]
fn the_deployed_row_reads_the_ninth_lane() {
    scope();
    let desc = deployed_sovereign_descriptor();
    let teeth = committed_teeth_col(&desc);

    // ⚑ FOLLOW THE DESCRIPTOR'S OWN WIRING, never a shift this test computes. Each published tooth
    // is welded by a `window_gate` to lane 0 of one chip lookup's digest group; that lookup is the
    // quad. Anything else here would be a second opinion about the compacted geometry, which is the
    // class of drift this whole flag day is about.
    let mut quads: Vec<Vec<usize>> = Vec::new();
    for q in 0..KEY_COMMIT_LEN {
        let tooth = teeth + q;
        let digest_lane0 = desc
            .constraints
            .iter()
            .find_map(|c| match c {
                VmConstraint2::WindowGate(g) => {
                    let mut cols = Vec::new();
                    window_cols(&g.body, &mut cols);
                    if cols.len() == 2 && cols.contains(&tooth) {
                        cols.into_iter().find(|c| *c != tooth)
                    } else {
                        None
                    }
                }
                _ => None,
            })
            .unwrap_or_else(|| panic!("tooth {q} (col {tooth}) must be welded to a digest lane"));
        let inputs = desc
            .constraints
            .iter()
            .find_map(|c| match c {
                VmConstraint2::Lookup(l) => {
                    let cols: Vec<usize> = l.tuple.iter().filter_map(expr_col).collect();
                    // The arity-4 chip row: 4 input vars then 8 output vars (the arity tag and the
                    // 12 zero pads are consts and drop out).
                    if cols.len() == 12 && cols[4] == digest_lane0 {
                        Some(cols[0..4].to_vec())
                    } else {
                        None
                    }
                }
                _ => None,
            })
            .unwrap_or_else(|| {
                panic!("tooth {q}'s digest lane {digest_lane0} must be a chip lookup output")
            });
        assert_eq!(
            inputs.len(),
            4,
            "the arity must stay 4 — no chip-shape move"
        );
        quads.push(inputs);
    }

    // ⚑ THE CLAIM — full nine-lane cover. Eight would mean a key and its negation publish
    // identical teeth, which is the wound.
    let mut covered: Vec<usize> = quads.iter().flatten().copied().collect();
    covered.sort_unstable();
    covered.dedup();
    assert_eq!(
        covered.len(),
        9,
        "the four key-commit quads must cover NINE committed columns between them, not eight — \
         they cover {covered:?}"
    );

    // …and the ninth is the NON-CONTIGUOUS one: eight consecutive octet columns plus a lane sitting
    // well past them. This is what distinguishes the owner-key NONET from any eight-plus-one window
    // a compaction might have produced by accident.
    let octet: Vec<usize> = covered[0..8].to_vec();
    assert_eq!(
        octet,
        (covered[0]..covered[0] + 8).collect::<Vec<_>>(),
        "lanes 0..7 must be the contiguous committed octet"
    );
    let ninth = covered[8];
    assert!(
        ninth > covered[0] + 8,
        "the ninth lane must sit PAST the octet, never flush against it ({ninth} vs octet base {})",
        covered[0]
    );
    // The authoring-frame offset survives the E1/S2 compaction: lane 8 is `B_PUBKEY_NINTH_LANE -
    // B_PUBKEY_OCTET` columns past lane 0, read from the emitted layout rather than transcribed.
    assert_eq!(
        ninth - covered[0],
        B_PUBKEY_NINTH_LANE - B_PUBKEY_OCTET,
        "the compacted ninth-lane offset must equal the emitted authoring offset"
    );
    // …and exactly ONE quad reads it (Lean `quadIdx_row2_reads_the_ninth_lane`), matching the
    // emitted matrix.
    let hits = quads.iter().filter(|q| q.contains(&ninth)).count();
    assert_eq!(hits, 1, "exactly one quad may read the ninth lane");
    assert_eq!(
        hits,
        KEY_COMMIT_QUAD_IDX
            .iter()
            .filter(|r| r.contains(&8))
            .count(),
        "the committed row and the emitted matrix must agree on how many quads read lane 8"
    );
    // The BEFORE-block nonet is what is read (the OPERATED cell's owner key), in the authoring
    // frame `BEFORE_BASE + PUBKEY_NONET_LANE_COL` shifted down by the compaction.
    let shift = (BEFORE_BASE + B_PUBKEY_OCTET) - covered[0];
    let authored: Vec<usize> = PUBKEY_NONET_LANE_COL
        .iter()
        .map(|c| BEFORE_BASE + c - shift)
        .collect();
    let mut authored_sorted = authored.clone();
    authored_sorted.sort_unstable();
    assert_eq!(
        covered, authored_sorted,
        "the covered columns must BE the BEFORE-block owner nonet"
    );
}

fn expr_col(e: &LeanExpr) -> Option<usize> {
    match e {
        LeanExpr::Var(c) => Some(*c),
        _ => None,
    }
}

// ============================================================================
// TOOTH 3 — the pair at the DEPLOYED PROVER
// ============================================================================

fn open_permissions() -> dregg_cell::Permissions {
    use dregg_cell::AuthRequired;
    dregg_cell::Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn producer_cell(owner: [u8; 32], balance: i64, nonce: u64, mode: CellMode) -> dregg_cell::Cell {
    let mut cell = dregg_cell::Cell::with_balance(owner, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell.mode = mode;
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("pre-iroot limbs")
}

struct MintedLeg {
    desc: EffectVmDescriptor2,
    trace: Vec<Vec<BabyBear>>,
    dpis: Vec<BabyBear>,
    map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>>,
    mb: dregg_circuit::descriptor_ir2::MemBoundaryWitness,
}

/// Mint the deployed keyed-wide `MakeSovereign` leg for a cell OWNED BY `owner`, through the
/// deployed dispatcher — the same spine the live SDK wide prover rides. The rider derives the four
/// KEY_COMMIT teeth from the committed nonet in the trace.
fn mint_leg(owner: [u8; 32]) -> MintedLeg {
    let balance = 1000i64;
    let st = CellState::new(balance as u64, 0);
    let effects = vec![Effect::MakeSovereign];
    let before_cell = producer_cell(owner, balance, 0, CellMode::Hosted);
    let after_cell = producer_cell(owner, balance, 1, CellMode::Sovereign);

    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).expect("ledger seed");
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];
    let empty8 = dregg_circuit::heap_root::empty_heap_root_8();
    let revoked = dregg_turn::rotation_witness::empty_revoked_root_8();
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &empty8,
        &empty8,
        &revoked,
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &empty8,
        &empty8,
        &revoked,
        &receipt_log,
        &Default::default(),
    );

    let (desc, trace, dpis, map_heaps, mb) = generate_rotated_effect_vm_descriptor_and_trace_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &empty_caveat_manifest(),
        None,
        None,
        None,
        None,
    )
    .expect("deployed makeSovereign wide dispatch");

    // The dispatcher must resolve the COMMITTED row byte-for-byte, or this tooth is testing a
    // descriptor nothing serves.
    assert_eq!(
        desc,
        deployed_sovereign_descriptor(),
        "the dispatcher must resolve the committed wide makeSovereign row"
    );

    // The rider's teeth ARE the executor's teeth for this owner — the third edge, on the producer
    // side, asserted at BOTH the published claim PIs and the committed teeth columns.
    let kc = dregg_turn::executor::TurnExecutor::pubkey_to_witness_key_commit(&owner);
    assert_eq!(
        &dpis[SOVEREIGN_KEY_COMMIT_PI_LO..SOVEREIGN_KEY_COMMIT_PI_LO + KEY_COMMIT_LEN],
        &kc[..],
        "the leg must publish the executor KEY_COMMIT at the tail claim PIs"
    );
    let teeth_col = committed_teeth_col(&desc);
    assert_eq!(
        &trace[0][teeth_col..teeth_col + KEY_COMMIT_LEN],
        &kc[..],
        "the executor KEY_COMMIT must sit at the committed teeth columns"
    );

    MintedLeg {
        desc,
        trace,
        dpis,
        map_heaps,
        mb,
    }
}

fn prove(leg: &MintedLeg) -> Result<impl Sized, String> {
    prove_vm_descriptor2_for_config(
        &leg.desc,
        &leg.trace,
        &leg.dpis,
        &leg.mb,
        &leg.map_heaps,
        &UMemBoundaryWitness::default(),
        &ir2_leaf_wrap_config(),
    )
}

/// THE HONEST POLE. Without it the refusal below is worthless.
#[test]
fn deployed_prover_accepts_the_honest_owner_key() {
    scope();
    let (a, _) = key_and_its_negation();
    let leg = mint_leg(a);
    must_accept("the honest sovereign owner key", || prove(&leg));
}

/// ⚑⚑ **THE POLE THAT WAS ACCEPTED BEFORE THE REPAIR.**
///
/// The leg is minted for a cell owned by `−A`, so the committed nonet is `−A`'s: lanes 0..7 are
/// BYTE-IDENTICAL to `A`'s and only lane 8 differs. The published teeth are then overwritten with
/// `A`'s — a claim that the committed owner is `A` over a committed key that is `−A`.
///
/// Under the retired eight-lane matrix this trace SATISFIED the gate: every quad's inputs were
/// unchanged, so the AIR recomputed exactly `A`'s teeth from `−A`'s committed columns. Under the
/// nine-lane cover quad 2 absorbs lane 8, its digest moves, and the tooth weld cannot hold.
#[test]
fn deployed_prover_refuses_a_negated_owner_key() {
    scope();
    let (a, neg_a) = key_and_its_negation();
    let mut leg = mint_leg(neg_a);

    let honest_teeth = dregg_turn::executor::TurnExecutor::pubkey_to_witness_key_commit(&a);
    let negated_teeth = dregg_turn::executor::TurnExecutor::pubkey_to_witness_key_commit(&neg_a);
    // ⚑ ASSERT THE MUTATION HAPPENED. A substitution that is a no-op is a falsifier that stopped
    // falsifying, and this one is a no-op under the retired matrix BY CONSTRUCTION.
    assert_ne!(
        honest_teeth, negated_teeth,
        "the substitution must actually move the teeth, or this tooth proves nothing"
    );

    let teeth_col = committed_teeth_col(&leg.desc);
    for row in leg.trace.iter_mut() {
        for (q, v) in honest_teeth.iter().enumerate() {
            row[teeth_col + q] = *v;
        }
    }
    for (q, v) in honest_teeth.iter().enumerate() {
        leg.dpis[SOVEREIGN_KEY_COMMIT_PI_LO + q] = *v;
    }

    let what = "a sovereign leg whose committed owner nonet is the NEGATION of the key its \
                published teeth digest";
    let refusal = must_refuse_or_unsat_panic(what, || prove(&leg));
    assert_violated_constraint_not_bus(what, &refusal.reason());
}
