//! THE DSL rc-EMIT satisfiability + tooth (`withDfaRcPins` — the `Witnessed{Dfa}`
//! route-commitment PI exposure, the named BIG-BANG piece of `dsl_leaf_adapter.rs`).
//!
//! Every deployed rotated cohort member now publishes the caveat-region 4-felt DFA
//! ROUTE-COMMITMENT carrier (`C_DFA_RC_OFF`, filled from `RotatedCaveatManifest::dfa_rc`)
//! as its LAST 4 member PIs. This file proves the emit is REAL both ways on the live
//! transfer member:
//!
//!   1. a turn WITHOUT a Dfa caveat proves + verifies with the ZERO sentinel (the wrap is
//!      selector-free — plain PI bindings over the uniformly-filled carrier — so the whole
//!      live fleet keeps proving);
//!   2. an honest Dfa-GATED turn (manifest carrying
//!      `dfa_route_commitment(DfaProofWire.public_inputs)`) proves + verifies, publishing
//!      the rc at the TAIL slots the fold's binding node will `connect` to;
//!   3. THE TOOTH: a verifier-side rc CLAIM that differs from the trace's bound carrier
//!      (a forged / omitted route commitment) is REFUSED — **and so is the adversary that moves
//!      the carrier AND every PI the rc pins publish, together**, because the rc FOLD absorbs the
//!      carrier into the caveat commitment a verifier reconstructs from the turn's own witnessed
//!      predicates. The pin-only emit admitted that adversary; the fold is what refuses it.

use dregg_circuit::CellState;
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::Effect;
use dregg_circuit::effect_vm::trace_rotated::{
    C_DFA_RC_OFF, CAVEAT_BASE, DFA_RC_LEN, ROT_PI_COUNT, RotatedBlockWitness, V1_PI_COUNT,
    avail_pad_for_descriptor_name, dfa_route_commitment, generate_rotated_effect_vm_trace_avail,
    transfer_caveat_manifest,
};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::refusal::{assert_violated_constraint_not_bus, must_refuse_or_unsat_panic};
use dregg_turn::rotation_witness as rw;

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};

fn open_permissions() -> Permissions {
    Permissions {
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

fn producer_cell(balance: i64, nonce: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn transfer_desc_json() -> &'static str {
    for line in V3_STAGED_REGISTRY_TSV.lines() {
        let mut parts = line.splitn(3, '\t');
        if parts.next() == Some("transferVmDescriptor2R24") {
            let _name = parts.next();
            return parts.next().expect("registry line has a json column");
        }
    }
    panic!("transferVmDescriptor2R24 not in V3_STAGED_REGISTRY_TSV");
}

/// Build one honest rotated transfer (the flip file's recipe) with the given caveat manifest.
///
/// The deployed `transferVmDescriptor2R24` is the AVAILABILITY-HARDENED member
/// (`dregg-effectvm-transfer-v1-avail-…`, pad 10): the 15-bit weld-witness columns ride
/// `[V1_WIDTH, V1_WIDTH + pad)` (wire 188 = `BEF0`, the low 15-bit limb of `before.bal_lo`) and every
/// rotated appendix base shifts up by the pad. The producer MUST match — derive the pad from the
/// descriptor name (`avail_pad_for_descriptor_name`) and use the avail-aware generator, or the bare
/// producer lays a ~30-bit block limb at wire 188 and the descriptor's 15-bit range refuses it.
fn honest_transfer(
    pad: usize,
    caveat: &dregg_circuit::effect_vm::trace_rotated::RotatedCaveatManifest,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let before_balance: i64 = 100_000;
    let amount: u64 = 50;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance - amount as i64, 0);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let bridge = |w: &rw::RotationWitness| {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("pre-iroot limbs")
    };
    generate_rotated_effect_vm_trace_avail(
        pad,
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        caveat,
    )
    .expect("live rotated generator (avail-aware)")
}

#[test]
fn dsl_rc_pins_prove_with_and_without_a_dfa_caveat_and_the_tooth_bites() {
    let desc = parse_vm_descriptor2(transfer_desc_json()).expect("rotated transfer parses");
    // The deployed transfer member is AVAILABILITY-HARDENED (`…-v1-avail`, pad 10): derive the
    // producer's weld pad from the descriptor name so the trace geometry matches the 15-bit range
    // on wire 188 (`BEF0`) + the pad-shifted appendix bases.
    let pad = avail_pad_for_descriptor_name(&desc.name);
    assert!(
        pad > 0,
        "the deployed transfer member is the hardened `-v1-avail` face (nonzero pad); got {pad} \
         from name {}",
        desc.name
    );
    // The deployed member is the `withDfaRcPins` wrap: 42 v1 + 4 rotated + 4 dsl rc.
    assert_eq!(
        desc.public_input_count,
        ROT_PI_COUNT + DFA_RC_LEN,
        "the deployed transfer member carries the 4 dsl rc TAIL PIs (regen the descriptors if \
         this is the pre-rc corpus)"
    );

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    // ── 1. WITHOUT a Dfa caveat: the ZERO sentinel proves (the live fleet keeps proving). ──
    let caveat = transfer_caveat_manifest();
    let (trace, dpis) = honest_transfer(pad, &caveat);
    assert_eq!(dpis.len(), ROT_PI_COUNT + DFA_RC_LEN);
    for k in 0..DFA_RC_LEN {
        assert_eq!(
            dpis[ROT_PI_COUNT + k],
            BabyBear::ZERO,
            "no-Dfa turn publishes the zero rc sentinel at tail slot {k}"
        );
    }
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
        .expect("no-Dfa rotated transfer must prove (the rc wrap is honest-satisfiable at zero)");
    verify_vm_descriptor2(&desc, &proof, &dpis).expect("no-Dfa proof verifies");

    // ── 2. WITH a Dfa caveat: the real rc proves and rides the TAIL PIs. ──
    // The `DfaProofWire.public_inputs` shape of the production router
    // (`dregg-dfa-routing-v1`): [initial_state, final_state, table_commitment, route_commitment].
    let wire_pis: Vec<BabyBear> = [3u32, 0, 913_211, 77_004]
        .iter()
        .map(|v| BabyBear::new(*v))
        .collect();
    let rc = dfa_route_commitment(&wire_pis);
    assert_ne!(rc, [BabyBear::ZERO; DFA_RC_LEN], "a real rc is non-zero");
    let mut caveat_dfa = transfer_caveat_manifest();
    caveat_dfa.dfa_rc = rc;
    let (trace_dfa, dpis_dfa) = honest_transfer(pad, &caveat_dfa);
    for k in 0..DFA_RC_LEN {
        assert_eq!(
            dpis_dfa[ROT_PI_COUNT + k],
            rc[k],
            "the Dfa-gated turn publishes rc[{k}] at its tail slot"
        );
        assert_eq!(
            trace_dfa[0][CAVEAT_BASE + pad + C_DFA_RC_OFF + k],
            rc[k],
            "the carrier column holds rc[{k}] (uniform fill)"
        );
    }
    let proof_dfa = prove_vm_descriptor2(&desc, &trace_dfa, &dpis_dfa, &mem_boundary, &map_heaps)
        .expect("the Dfa-gated rotated transfer must prove (SAT with the real rc)");
    verify_vm_descriptor2(&desc, &proof_dfa, &dpis_dfa).expect("Dfa-gated proof verifies");

    // ── 3. THE TOOTH, RESTORED AS A REAL ONE — the rc carrier is FOLDED into the published
    //       caveat commitment, so the pins bind and the move-both adversary is refused. ──
    //
    // History, because the shape of the hole is the lesson. `withDfaRcPins` appends ONLY
    // `.piBinding`s, and until 2026-07-31 the rc carrier columns (caveat-region offsets 39..=42)
    // were read by no gate, lookup, hash site or range tooth. So each pin was `local[c] == pi[k]`
    // with the prover choosing BOTH sides: `UnforcedPiPins.unforcedPins` condemned all four on
    // every member and the convergence re-emit deleted them — correctly. The half of this step
    // that "tested the pin" then had to be inverted to a MEASUREMENT that the AIR admits a
    // carrier/claim mismatch, and `ivc_turn_chain::dsl_rc_claim_pi_lo` (which locates the fold's rc
    // slot BY that pin) started refusing every deployed leg.
    //
    // ⚠ AND THE OLD TOOTH WAS ROUTABLE-AROUND EVEN WHEN IT PASSED: it moved the carrier and left
    // the PI alone; a real adversary moves BOTH. That is why the repair is the FOLD, not a
    // restored pin — see (c).
    {
        // (a) forging the PUBLISHED vector against an honest proof is refused — but note WHAT by.
        // Public values are absorbed into the Fiat–Shamir transcript, so ANY edit to the PI vector
        // breaks verification, including edits to slots no constraint mentions. This would pass
        // against a descriptor with no rc pin at all; it is transcript binding, not the pin.
        let mut forged = dpis_dfa.clone();
        forged[ROT_PI_COUNT] += BabyBear::ONE;
        assert!(
            verify_vm_descriptor2(&desc, &proof_dfa, &forged).is_err(),
            "any edit to the published vector breaks the transcript this proof was bound to. NOTE \
             this is transcript binding, NOT the rc pin — it would hold for an unpinned slot too."
        );

        // (b) THE PIN, back and biting: forge the TRACE carrier, keep the honest PI vector. The
        // `withDfaRcPins` pin `local[rc lane 0] == pi[46]` now fails — and it is a real pin again
        // only because the fold made the column FORCED, so `dropUnforcedPins` keeps it.
        let mut forged_trace = trace_dfa.clone();
        for row in forged_trace.iter_mut() {
            row[CAVEAT_BASE + pad + C_DFA_RC_OFF] += BabyBear::ONE;
        }
        let refused = must_refuse_or_unsat_panic(
            "a trace whose rc carrier disagrees with the published rc",
            || {
                prove_vm_descriptor2(&desc, &forged_trace, &dpis_dfa, &mem_boundary, &map_heaps)
                    .and_then(|proof| verify_vm_descriptor2(&desc, &proof, &dpis_dfa))
            },
        );
        // ...and it is the PIN that bites, not a bus imbalance. The distinction is the whole
        // tooth: a LogUp mismatch would mean the caveat-chain lookups disagreed, which is a
        // different statement from "the published rc is not the one the trace carries".
        assert_violated_constraint_not_bus("the rc carrier/claim mismatch", &refused.reason());

        // (c) ⚑ THE MOVE-BOTH ADVERSARY — the one (b) could never catch. Mint a FULLY CONSISTENT
        // forged world: a different route commitment, its carrier columns, the two chip carriers
        // the fold derives from them, and the four published rc PIs, all agreeing. The ONLY felt it
        // does not get to choose is the caveat commit at PI 45, which a verifier reconstructs from
        // the turn's own witnessed predicates (`proof_verify.rs`: PI `V1_PI_COUNT + 3` is
        // witness-INDEPENDENT and re-derived, with `caveat.dfa_rc` recomputed from the turn's Dfa
        // blobs). Because the carrier is now ABSORBED into that commitment, the forged world moves
        // it — and the leg is UNSAT against the honest one.
        let mut forged_rc = rc;
        forged_rc[0] += BabyBear::ONE;
        assert_ne!(forged_rc, rc);
        let mut caveat_forged = transfer_caveat_manifest();
        caveat_forged.dfa_rc = forged_rc;
        let (trace_moved, dpis_moved) = honest_transfer(pad, &caveat_forged);

        // S1 — THE HONEST POLE FIRST, in this same step: the forged world is internally consistent
        // and proves on its own terms. Without this, (c)'s refusal would be satisfied just as well
        // by an arm that refuses every chain of this shape.
        let consistent =
            prove_vm_descriptor2(&desc, &trace_moved, &dpis_moved, &mem_boundary, &map_heaps)
                .and_then(|proof| verify_vm_descriptor2(&desc, &proof, &dpis_moved));
        assert!(
            consistent.is_ok(),
            "the move-both world is a well-formed turn on its OWN caveat commit; the refusal below \
             must come from the anchor, not from the shape: {consistent:?}"
        );

        // The fold really did move the published caveat commit — the whole point of the repair.
        assert_ne!(
            dpis_moved[V1_PI_COUNT + 3],
            dpis_dfa[V1_PI_COUNT + 3],
            "moving the rc carrier must move the PUBLISHED caveat commit (PI 45). If these are \
             EQUAL the rc carrier is outside the commitment fold again and the pins bind nothing."
        );

        // ...and now the adversary: everything moved EXCEPT the anchor the verifier supplies.
        let mut moved_both = dpis_moved.clone();
        moved_both[V1_PI_COUNT + 3] = dpis_dfa[V1_PI_COUNT + 3];
        for k in 0..DFA_RC_LEN {
            assert_eq!(moved_both[ROT_PI_COUNT + k], forged_rc[k]);
            assert_eq!(
                trace_moved[0][CAVEAT_BASE + pad + C_DFA_RC_OFF + k],
                forged_rc[k],
                "carrier and PI moved TOGETHER — the adversary the pin-only emit admitted"
            );
        }
        let move_both = must_refuse_or_unsat_panic(
            "MOVE-BOTH: a forged route commitment published consistently at its own pins",
            || {
                prove_vm_descriptor2(&desc, &trace_moved, &moved_both, &mem_boundary, &map_heaps)
                    .and_then(|proof| verify_vm_descriptor2(&desc, &proof, &moved_both))
            },
        );
        assert_violated_constraint_not_bus("the move-both adversary", &move_both.reason());
        eprintln!(
            "rc FOLD: carrier/claim mismatch REFUSED, and the move-both adversary (carrier + all \
             four rc PIs moved together) REFUSED against the verifier-anchored caveat commit."
        );
    }

    // ⚑ AND THE PINS ARE BACK ON THEIR OWN MERITS. `dropUnforcedPins` is UNCHANGED and still drops
    // every pin whose column no non-pin constraint reads; these survive it because the fold made
    // their columns read. Measured here on the committed bytes, not asserted in prose.
    {
        use dregg_circuit::descriptor_ir2::VmConstraint2;
        use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};
        let rc_col0 = CAVEAT_BASE + pad + C_DFA_RC_OFF;
        let rc_pins: Vec<usize> = desc
            .constraints
            .iter()
            .filter_map(|c| match c {
                VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index })
                    if *row == VmRow::Last && (rc_col0..rc_col0 + DFA_RC_LEN).contains(col) =>
                {
                    Some(*pi_index)
                }
                _ => None,
            })
            .collect();
        assert_eq!(
            rc_pins,
            (0..DFA_RC_LEN)
                .map(|k| ROT_PI_COUNT + k)
                .collect::<Vec<_>>(),
            "the committed transfer member must carry all four rc pins, contiguous at the tail \
             slots — this is what `ivc_turn_chain::dsl_rc_claim_pi_lo` searches for"
        );

        // ⚑ AND THE FORCING IS A READ, NOT A DECLARATION. This is the discrimination
        // `unforced_pi_pin_census::proof_bind_is_the_only_reader_of_the_custom_exposure_columns`
        // exists to make: `forcedCols` counts a `proof_bind`'s commit/vk references even though the
        // deployed `Ir2Air::eval` `continue`s on that kind and Lean's `holdsAt` is `trivial` for it,
        // so a column can be "forced" on the strength of a declaration and still be prover-chosen.
        // The rc columns are not in that class — each is read by a CHIP LOOKUP, the constraint kind
        // the caveat chain graduates to, which has a row denotation in both models.
        let mut readers = vec![0usize; DFA_RC_LEN];
        for c in &desc.constraints {
            if let VmConstraint2::Lookup(l) = c {
                for e in &l.tuple {
                    if let dregg_circuit::lean_descriptor_air::LeanExpr::Var(v) = e {
                        if (rc_col0..rc_col0 + DFA_RC_LEN).contains(v) {
                            readers[v - rc_col0] += 1;
                        }
                    }
                }
            }
        }
        assert!(
            readers.iter().all(|n| *n > 0),
            "every rc carrier column must be READ by a chip lookup (the caveat fold's two new \
             absorption sites), not merely pinned or declared: readers per lane = {readers:?}"
        );
        // ...and nothing about this is a `proof_bind`: the custom member is the only one with one,
        // and this member carries none at all.
        assert!(
            !desc
                .constraints
                .iter()
                .any(|c| matches!(c, VmConstraint2::ProofBind(_))),
            "the transfer member carries no proof_bind, so no rc column can be forced by a \
             declaration here even in principle"
        );
    }

    // ── 4. THE AVAIL-WELD RANGE STILL BITES: wire 188 (`BEF0`) carries the 15-bit range lookup that
    //     closes the GAP #4 over-debit forgery. An over-15-bit value there (the forgery shape: a
    //     ~30-bit felt masquerading as the low limb) is REFUSED — the geometry fix did not weaken
    //     the check, it aligned the honest producer to it. ──
    use dregg_circuit::effect_vm::EFFECT_VM_WIDTH; // wire 188 = AVAIL_BASE = BEF0
    let mut over_range = trace.clone();
    for row in over_range.iter_mut() {
        row[EFFECT_VM_WIDTH] = BabyBear::new(40_000); // ≥ 2^15 = 32768
    }
    assert!(
        prove_vm_descriptor2(&desc, &over_range, &dpis, &mem_boundary, &map_heaps).is_err(),
        "an over-15-bit value at wire 188 (BEF0) must be refused — the avail-weld range still bites"
    );

    // The slot contract for the fold lane: rc = the LAST 4 member PIs, i.e.
    // `public_input_count - 4 ..` on the non-wide member (46..49 for transfer).
    assert_eq!(ROT_PI_COUNT, 46);
    assert_eq!(desc.public_input_count - DFA_RC_LEN, ROT_PI_COUNT);
}

/// The rc derivation is the custom proof-bind commitment, term-for-term (the fold's DSL leaf
/// exposes `custom_proof_pi_commitment` in-circuit; the deployed leg must publish the SAME
/// value or the binding node's `connect` would never close). Cross-pin the duplicated
/// derivation against a golden: recompute via the same WideHash call the doc names.
#[test]
fn dfa_route_commitment_is_the_custom_proof_pi_commitment() {
    use dregg_circuit::binding::WideHash;
    let pis: Vec<BabyBear> = (1u32..=7).map(BabyBear::new).collect();
    let rc = dfa_route_commitment(&pis);
    let felts = WideHash::from_poseidon2("dregg-custom-proof-bind-pi-v1", &pis).to_felts();
    assert_eq!(rc, [felts[0], felts[1], felts[2], felts[3]]);
}
