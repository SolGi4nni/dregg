//! # THE DEPLOYED DECO-BINDING LIGHT-CLIENT TOOTH (the 8th carrier's deployed-path tooth —
//! the fiat/Stripe money-in twin of `bridge_binding_deployed_tooth.rs`).
//!
//! This is the NON-VACUITY WITNESS that the DECO carrier is LIVE (`docs/deos/DECO-CARRIER-PLAN.md`).
//! It builds a REAL 2-turn chain whose FIRST turn is a **Stripe money-in mint** on the COMMITTED
//! deployed, PI-46-pinned mint row (`mintVmDescriptor2R24` wide = Lean `mintV3BridgeHash`) —
//! produced by [`generate_rotated_stripe_mint_wide`], which fills the mint row's `param0`
//! (PI 46) with the FELT-DOMAIN `deco_payment_hash_felt(PaymentFacts)` (the SAME felt the
//! executor writes to `VerifiedPayment::payment_hash`, `bridge/src/stripe_mirror.rs`) — PLUS the
//! prover-side `DecoWitnessBundle` (the DECO commitment witness: the felt PaymentFacts + salt).
//! It folds through the DEPLOYED chain prover's **Deco arm** (`ivc_turn_chain.rs`: dual-expose at
//! PI 46 → re-prove the Poseidon2 DECO commitment leaf → the payment-hash binding node's
//! in-circuit `connect`) and verifies through the light-client verifier.
//!
//! ## SHARED DEPLOYED ROW (the carrier is the witness, not the descriptor)
//!
//! DECO rides the SAME committed pinned mint row as bridge: `DECO_PAYMENT_HASH_PI ==
//! BRIDGE_MINT_HASH_PI == 46` (a mint row publishes ONE mint-identity PI; the deployed row
//! ALREADY pins `param0` at PI 46 on the FIRST row, NON-VK). The DECO fold arm dispatches on
//! `CarrierWitness::Deco`, so the DECO commitment leaf — NOT the note-spend leaf — recomputes
//! the published felt IN-AIR from its OWN PI-pinned `(amountCents, currency, recipient,
//! paymentIntentId)` and exposes it at claim lane `DECO_LEAF_PAYMENT_HASH_PI`. Under
//! Poseidon2-CR the folded identity IS the identity of exactly that verified payment (which
//! paymentIntentId — the double-mint linkage: the executor's `note_nullifiers` set-uniqueness
//! ranges over the SAME payment identity's replay nonce).
//!
//! THE TWO POLES: honest identity (leg's published PI 46 == the leaf's recomputed lane) folds +
//! verifies; a FORGED published payment identity (a value no genuine DECO commitment produces)
//! ⇒ in-circuit `connect` conflict ⇒ UNSAT ⇒ REJECTED.
//!
//! Both slow poles are `#[ignore]` (real recursion, minutes). Run with:
//!   cargo test -p dregg-circuit-prove --test deco_binding_deployed_tooth -- --ignored --nocapture

use dregg_cell::Ledger;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, UMemBoundaryWitness, VmConstraint2,
    parse_vm_descriptor2, prove_vm_descriptor2_for_config,
};
use dregg_circuit::dsl::deco_payment::{deco_payment_hash_felt, stripe_payment_facts_felts};
use dregg_circuit::effect_vm::columns::{PARAM_BASE, param};
use dregg_circuit::effect_vm::trace_rotated::{
    ROT_PI_COUNT, RotatedBlockWitness, empty_caveat_manifest, generate_rotated_stripe_mint_wide,
    generate_rotated_transfer_shape_wide, transfer_caveat_manifest,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};
use dregg_circuit_prove::deco_leaf_adapter::DecoLeafWitness;
use dregg_circuit_prove::ivc_turn_chain::{
    DECO_PAYMENT_HASH_PI, FinalizedTurn, ir2_leaf_wrap_config, prove_turn_chain_recursive,
    verify_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::{
    CarrierWitness, DecoWitnessBundle, DescriptorParticipant, RotatedParticipantLeg,
};
use dregg_turn::rotation_witness as rw;

// ============================================================================
// Fixtures
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

fn producer_cell(balance: i64, nonce: u64) -> dregg_cell::Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("pre-iroot limbs")
}

/// A REAL Stripe payment's felt witness: the `PaymentFacts` decomposed through the ONE
/// canonical encoder (`stripe_payment_facts_felts`) — the SAME encoder the executor's
/// `VerifiedPayment::payment_hash` and the deployed producer decompose through — plus a
/// transcript-commitment opening `salt`. `amountCents` (2500 = $25.00) drives both the
/// leaf's amount range gate and the minted value.
fn stripe_witness(amount_cents: u64, payment_intent_id: &str) -> DecoLeafWitness {
    let recipient = [0xCDu8; 32]; // the dregg cell in `metadata.dregg_recipient`
    let [amount, currency, recipient_f, pi_f] =
        stripe_payment_facts_felts(amount_cents, "usd", &recipient, payment_intent_id);
    DecoLeafWitness {
        amount_cents: amount,
        currency,
        recipient: recipient_f,
        payment_intent: pi_f,
        salt: BabyBear::new(0x0DEC0),
    }
}

fn deployed_wide_descriptor(wire: &str) -> EffectVmDescriptor2 {
    let json = WIDE_REGISTRY_STAGED_TSV
        .lines()
        .find_map(|line| {
            let mut it = line.splitn(3, '\t');
            if it.next() == Some(wire) {
                let _display = it.next();
                it.next()
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("{wire} not in WIDE_REGISTRY_STAGED_TSV"));
    parse_vm_descriptor2(json).expect("deployed wide descriptor parses")
}

/// Mint the deployed Stripe money-in leg: the mint row credits `value_lo` and publishes
/// `payment_hash` (the leg's CLAIMED felt payment identity) at PI 46 (`param0`, the native
/// pin) via [`generate_rotated_stripe_mint_wide`].
fn mint_stripe_leg(
    before_balance: i64,
    value_full: u64,
    nonce: u64,
    payment_hash: BabyBear,
    witness: Option<CarrierWitness>,
) -> RotatedParticipantLeg {
    let value_lo_u = value_full & ((1u64 << 30) - 1);
    let st = CellState::new(before_balance as u64, nonce as u32);
    let before_cell = producer_cell(before_balance, nonce);
    let after_cell = producer_cell(before_balance + value_lo_u as i64, nonce);

    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).expect("ledger seed");
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &receipt_log,
        &Default::default(),
    );

    let (trace, dpis) = generate_rotated_stripe_mint_wide(
        &st,
        value_full,
        payment_hash,
        &bridge(&before_w),
        &bridge(&after_w),
        &empty_caveat_manifest(),
    )
    .expect("deployed Stripe money-in wide trace generates");

    let desc = deployed_wide_descriptor("mintVmDescriptor2R24");
    assert_eq!(
        dpis.len(),
        desc.public_input_count,
        "the NATIVE mint row's PI count matches the producer (46 + payment_hash + 4 rc + 16 anchors)"
    );
    assert_eq!(
        dpis[DECO_PAYMENT_HASH_PI], payment_hash,
        "the producer publishes the mint row's param0 (the claimed felt payment identity) at PI 46"
    );

    let config = ir2_leaf_wrap_config();
    let proof = prove_vm_descriptor2_for_config(
        &desc,
        &trace,
        &dpis,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &config,
    )
    .expect("the deployed Stripe money-in wide leg proves under the leaf-wrap config");

    RotatedParticipantLeg {
        proof,
        descriptor: desc,
        public_inputs: dpis,
        carrier_witness: witness,
    }
}

/// A plain transfer leg (the chain's second turn), linking off the Stripe-mint turn's post-state.
fn mint_plain_transfer_leg(before_balance: i64, amount: u64, nonce: u64) -> RotatedParticipantLeg {
    let st = CellState::new(before_balance as u64, nonce as u32);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let before_cell = producer_cell(before_balance, nonce);
    let after_cell = producer_cell(before_balance - amount as i64, nonce);

    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).expect("ledger seed");
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &receipt_log,
        &Default::default(),
    );

    let (trace, dpis) = generate_rotated_transfer_shape_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &transfer_caveat_manifest(),
    )
    .expect("plain transfer wide trace generates");

    let desc = deployed_wide_descriptor("transferVmDescriptor2R24");
    // The committed transfer row carries the 2 membership claim PIs (50..51) the bare transfer
    // producer does not fill; splice zero teeth exactly as the bridge/membership teeth do.
    let (desc, dpis, trace) = if dpis.len() == desc.public_input_count {
        (desc, dpis, trace)
    } else {
        let mut trace = trace;
        // The gentian capacity-floor refuse (transfer is a bare cohort member) appends 48 aux cols
        // PAST the teeth, widening the wide member 2495->2543; derive the teeth base from the
        // pre-refuse width (`trace_width - 48 - 2`), then grow + fill the refuse aux (floor=0).
        let refuse_w: usize = if desc.name.ends_with("-gentian-deployed-bare-refuse") {
            48
        } else {
            0
        };
        let teeth_col = desc.trace_width - refuse_w - 2;
        for row in trace.iter_mut() {
            debug_assert_eq!(row.len(), teeth_col);
            row.push(BabyBear::ZERO);
            row.push(BabyBear::ZERO);
            if desc.trace_width > row.len() {
                row.resize(desc.trace_width, BabyBear::ZERO);
                dregg_circuit::effect_vm::bare_floor_refuse_weld::fill_refuse_aux(&desc, row);
            }
        }
        let dpis = dregg_circuit_prove::carrier_pin_twin::splice_pi_values(
            &dpis,
            dregg_circuit_prove::ivc_turn_chain::MEMBERSHIP_CLAIM_PI_LO,
            &[BabyBear::ZERO, BabyBear::ZERO],
        );
        assert_eq!(dpis.len(), desc.public_input_count);
        (desc, dpis, trace)
    };

    let config = ir2_leaf_wrap_config();
    let proof = prove_vm_descriptor2_for_config(
        &desc,
        &trace,
        &dpis,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &config,
    )
    .expect("the plain transfer wide leg proves under the leaf-wrap config");

    RotatedParticipantLeg {
        proof,
        descriptor: desc,
        public_inputs: dpis,
        carrier_witness: None,
    }
}

/// Build the 2-turn chain: turn 0 = the witnessed Stripe money-in mint publishing
/// `leg_payment_hash`, turn 1 = a plain transfer linking off turn 0's post-state.
fn build_chain(leg_payment_hash: BabyBear, bundle: DecoWitnessBundle) -> Vec<FinalizedTurn> {
    let value_full: u64 = 2500; // $25.00 credited
    let value_lo = (value_full & ((1u64 << 30) - 1)) as i64;
    let t0_leg = mint_stripe_leg(
        1000,
        value_full,
        0,
        leg_payment_hash,
        Some(CarrierWitness::Deco(bundle)),
    );
    let t0 = FinalizedTurn::new(DescriptorParticipant::rotated(t0_leg));
    // The rotated generator TICKS the AFTER-block nonce on a mint turn, so t1's BEFORE state
    // carries nonce 1 and the credited balance for the 8-felt anchors to chain.
    let t1_leg = mint_plain_transfer_leg(1000 + value_lo, 7, 1);
    let t1 = FinalizedTurn::new(DescriptorParticipant::rotated(t1_leg));
    assert_eq!(
        t0.new_root(),
        t1.old_root(),
        "Stripe-mint turn 0's post-state must link to turn 1's pre-state"
    );
    vec![t0, t1]
}

// ============================================================================
// THE CHEAP TEETH (geometry + identity binding; run in normal CI)
// ============================================================================

/// THE REGEN-TIE GEOMETRY TOOTH: the COMMITTED wide mint row DECO rides carries the felt
/// payment-identity pin — a genuine `PiBinding{First}` welding PI 46 (`DECO_PAYMENT_HASH_PI`)
/// to the mint row's `param0` column (`PARAM_BASE + param::MINT_HASH`) — exactly the FIRST-row
/// prmCol-0 pin the DECO fold arm's admission requires (never a free column). This is the SAME
/// committed row bridge rides; DECO is distinguished by the witness/leaf, not the descriptor.
#[test]
fn committed_mint_row_carries_the_first_row_payment_hash_pin() {
    let desc = deployed_wide_descriptor("mintVmDescriptor2R24");
    assert_eq!(
        desc.public_input_count,
        ROT_PI_COUNT + 1 + 4 + 16,
        "the committed mint row is the felt-mint-identity member (67 PIs)"
    );
    let pin = desc.constraints.iter().find_map(|c| match c {
        VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index })
            if *pi_index == DECO_PAYMENT_HASH_PI =>
        {
            Some((*row, *col))
        }
        _ => None,
    });
    assert_eq!(
        pin,
        Some((VmRow::First, PARAM_BASE + param::MINT_HASH)),
        "PI 46 is pinned to the FIRST-row param0 column (the third-edge tie DECO shares with bridge)"
    );
}

/// THE PRODUCER ANTI-VACUITY TOOTH (cheap): the deployed Stripe-mint producer publishes at PI 46
/// EXACTLY the felt-domain payment identity the DECO leaf recomputes — `deco_payment_hash_felt`
/// over the witness facts — so the leg's published PI is not a free-floating scalar but the
/// executor-derivable, leaf-recomputable payment identity.
#[test]
fn stripe_producer_publishes_the_felt_payment_identity_at_pi46() {
    let w = stripe_witness(2500, "pi_deco_cheap");
    let expected =
        deco_payment_hash_felt(w.amount_cents, w.currency, w.recipient, w.payment_intent);
    assert_eq!(w.payment_hash(), expected);

    let leg = mint_stripe_leg(1000, 2500, 0, w.payment_hash(), None);
    assert_eq!(
        leg.public_inputs[DECO_PAYMENT_HASH_PI],
        w.payment_hash(),
        "the deployed Stripe-mint leg publishes the felt payment identity at PI 46"
    );
}

/// THE DOUBLE-MINT LINKAGE TOOTH (cheap): the published payment identity BINDS the
/// paymentIntentId — two payments differing ONLY in their paymentIntentId produce DIFFERENT
/// identities, so a leg's published identity can only connect to the DECO commitment leaf of
/// exactly its own payment. Set-uniqueness over that replay nonce is the executor's committed
/// `note_nullifiers` set; the fold makes WHICH paymentIntentId was minted against
/// light-client-visible through the identity.
#[test]
fn payment_identity_binds_the_payment_intent() {
    let a = stripe_witness(2500, "pi_intent_A");
    let b = stripe_witness(2500, "pi_intent_B"); // same amount/currency/recipient, different PI
    assert_ne!(
        a.payment_hash(),
        b.payment_hash(),
        "two payments differing only in paymentIntentId must carry distinct payment identities"
    );
}

// ============================================================================
// THE SLOW POLES (real deployed recursion)
// ============================================================================

/// POSITIVE POLE — an honest Stripe money-in mint (the leg's published payment identity at PI 46
/// == the DECO commitment leaf's in-AIR-recomputed lane) folds through the DEPLOYED chain
/// prover's Deco arm and the LIGHT CLIENT ACCEPTS.
#[test]
#[ignore = "SLOW: real deployed DECO-binding recursion fold (~minutes); run with --ignored"]
fn deployed_stripe_mint_honest_accepts() {
    let w = stripe_witness(2500, "pi_deco_honest");
    let bundle = DecoWitnessBundle::from_leaf_witness(&w);
    let honest_identity = w.payment_hash();
    let turns = build_chain(honest_identity, bundle);
    let whole = prove_turn_chain_recursive(&turns)
        .expect("the honest Stripe money-in chain must fold through the deployed prover");
    let vk = whole.root_vk_fingerprint();
    verify_turn_chain_recursive(&whole, &vk)
        .expect("the light client must ACCEPT the honest DECO-bound whole-chain artifact");
    eprintln!(
        "DEPLOYED DECO binding: honest Stripe money-in mint FOLDED + light-client VERIFIED (the \
         felt payment identity bound to the re-proven DECO commitment in the recursion tree)."
    );
}

/// THE TOOTH — a FORGED published payment identity: the leg publishes `payment_hash + 1` (a value
/// no genuine DECO commitment produces; the leg's own trace is self-consistent — the forged value
/// rides param0 + effects_hash + PI 46, exactly a prover minting against a Stripe payment that
/// never cleared). The binding `connect` conflicts with the leaf's in-AIR-recomputed identity ⇒
/// UNSAT ⇒ no root ⇒ REJECTED.
#[test]
#[ignore = "SLOW: real deployed DECO-binding recursion fold (~minutes); run with --ignored"]
fn deployed_stripe_mint_forged_identity_rejected() {
    let w = stripe_witness(2500, "pi_deco_forged");
    let bundle = DecoWitnessBundle::from_leaf_witness(&w);
    let forged_identity = w.payment_hash() + BabyBear::ONE;
    let turns = build_chain(forged_identity, bundle);

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_turn_chain_recursive(&turns)
    }));
    match result {
        Err(_) => {}
        Ok(Err(_)) => {}
        Ok(Ok(_)) => panic!(
            "a FORGED payment identity (no verifying DECO commitment backs it) folded into a \
             verifying deployed whole-chain artifact — the deployed DECO binding is OPEN"
        ),
    }
    eprintln!(
        "DEPLOYED DECO binding: forged payment identity REJECTED by the deployed fold (no root)."
    );
}
