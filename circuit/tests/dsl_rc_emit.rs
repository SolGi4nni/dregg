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
//!      (a forged / omitted route commitment) is REFUSED.

use dregg_circuit::CellState;
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::Effect;
use dregg_circuit::effect_vm::trace_rotated::{
    C_DFA_RC_OFF, CAVEAT_BASE, DFA_RC_LEN, ROT_PI_COUNT, RotatedBlockWitness,
    avail_pad_for_descriptor_name, dfa_route_commitment, generate_rotated_effect_vm_trace_avail,
    transfer_caveat_manifest,
};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
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

    // ── 3. ⚑ THE "TOOTH" WAS NEVER A TOOTH, AND `dropUnforcedPins` REMOVED THE PIN THAT
    //       IMPERSONATED ONE. ──
    //
    // This step used to assert, in two halves, that "a claimed rc ≠ the bound carrier is REFUSED".
    // Half (a) still passes and half (b) now fails, and the SPLIT is the diagnosis:
    //
    //   (a) forging the PUBLISHED vector against an honest proof is refused — but not by the rc
    //       pin. Public values are absorbed into the Fiat–Shamir transcript, so ANY edit to the PI
    //       vector breaks verification, including edits to slots no constraint mentions. (a) would
    //       pass against a descriptor with no rc pin at all, which is exactly the situation now.
    //
    //   (b) forging the TRACE carrier and keeping the honest PI vector was the half that tested the
    //       pin — and the pin is gone. `withDfaRcPins` appends ONLY `.piBinding`s
    //       (`withDfaRcPins_constraints` / `memOpsOf_withDfaRcPins` / `mapOpsOf_withDfaRcPins`), and
    //       the rc carrier columns (caveat-region offsets 39..=42) are read by no gate, lookup, hash
    //       site or range tooth. So the pin was `local[c] == pi[k]` with the prover choosing both
    //       sides, `UnforcedPiPins.unforcedPins` condemned all four, and the convergence re-emit
    //       deleted them.
    //
    // ⚠ AND (b) WAS ALWAYS ROUTABLE-AROUND EVEN WHEN IT PASSED. It moved the carrier and left the
    // PI alone; a real adversary moves BOTH and is accepted, publishing whatever route commitment
    // it likes. `withDfaRcPins`'s own doc has said so all along: "the pins are plain PI bindings,
    // satisfiable at any uniformly-filled value — the executor/verifier anchors the published
    // value, real-or-zero, off the turn's own witnessed predicates." The AIR never bound the route
    // commitment. This step is therefore replaced by the MEASUREMENT, not renumbered.
    {
        // (a) is kept, with its claim corrected to what it actually demonstrates.
        let mut forged = dpis_dfa.clone();
        forged[ROT_PI_COUNT] += BabyBear::ONE;
        assert!(
            verify_vm_descriptor2(&desc, &proof_dfa, &forged).is_err(),
            "any edit to the published vector breaks the transcript this proof was bound to. NOTE \
             this is transcript binding, NOT the rc pin — it would hold for an unpinned slot too."
        );

        // (b) INVERTED: the AIR ADMITS a trace whose rc carrier disagrees with the published rc.
        let mut forged_trace = trace_dfa.clone();
        for row in forged_trace.iter_mut() {
            row[CAVEAT_BASE + pad + C_DFA_RC_OFF] += BabyBear::ONE;
        }
        let admitted =
            prove_vm_descriptor2(&desc, &forged_trace, &dpis_dfa, &mem_boundary, &map_heaps)
                .and_then(|proof| verify_vm_descriptor2(&desc, &proof, &dpis_dfa));
        assert!(
            admitted.is_ok(),
            "MEASURED: with the unforced rc pins deleted, the AIR must ADMIT a carrier/claim \
             mismatch — nothing relates the rc carrier column to PI {ROT_PI_COUNT}. If this \
             REFUSES, a real binding arrived (see the note below) and this assertion should be \
             flipped back to a refusal, not deleted: {admitted:?}"
        );
        eprintln!(
            "MEASURED — the rc route commitment is NOT bound in-AIR: a trace whose carrier \
             disagrees with the published rc proves and verifies."
        );
    }

    // ⚑ AND THE REMOVAL BROKE A REAL CONSUMER — the one place the rc binding was ever enforced.
    //
    // `circuit-prove/src/ivc_turn_chain.rs::dsl_rc_claim_pi_lo` LOCATES the fold's rc slot BY
    // searching for the `PiBinding` on the rc lane-0 column, and errors fail-closed ("dsl: leg
    // descriptor carries NO rc pin … refusing to fold") when it is absent. `carrier_claim_pins_admitted`
    // then requires a pin per claim slot. No member of any deployed registry carries an rc pin now,
    // so the `CarrierWitness::Dsl` fold arm refuses every deployed leg.
    //
    // ⚠ THE REPAIR IS TO MAKE THE BINDING REAL, NOT TO TEACH THE FOLD TO ACCEPT AN UNPINNED SLOT.
    // Fold the rc carrier into `caveatCommit` (move it inside the commit fold, so the columns enter
    // `forcedCols`); the next emit then KEEPS the pins because they bind, `dsl_rc_claim_pi_lo` finds
    // them again, and step 3(b) above flips back to a refusal that an adversary cannot route around
    // by moving the column. Teaching the fold to accept an unpinned slot would restore the green
    // and keep the hole — and would be the second time this route's binding was assumed rather
    // than checked. Detection lives here and in
    // `effect_vm_descriptors::v3_staged_registry_parses_and_covers`.

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
