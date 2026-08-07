//! Both-polarity gate for the full-u64 shielded value/asset binding.
//!
//! The AIR is AUTHORED IN LEAN (`metatheory/Dregg2/Circuit/Emit/WideValueBindingEmit.lean`,
//! byte-pinned there; semantics in `WideValueBindingRefine.lean`). These are Rust harness checks
//! over the DEPLOYED sidecar path — they are shape and behaviour tests, not refinement, not
//! translation validation, and not verification.
//!
//! Turn carries one proof and all sixteen public lanes per input, and the live no-mint transcript
//! absorbs the carrier. The remaining migration seam is earlier: note creation/tree membership must
//! precommit the same wide value before the compatibility C7 join can be retired completely.

use dregg_cell::{ShieldedNoteCommitment, ShieldedNoteSet, felt_to_bytes32};
use dregg_circuit::cap_root::cap_node8;
use dregg_circuit::descriptor_ir2::{MemBoundaryWitness, UMemBoundaryWitness, VmConstraint2};
use dregg_circuit::descriptor_proof_backend::{
    DescriptorProofProver, DescriptorStatement, Plonky3HidingFriReference, Plonky3HidingFriWitness,
};
use dregg_circuit::exact_nullifier_aafi::TaggedKeyWire;
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::lean_descriptor_air::VmConstraint;
use dregg_circuit::poseidon2::hash_fact;
use dregg_circuit_prove::shielded::wide_value_binding::{DOMAIN_A, DOMAIN_B, col};
use dregg_circuit_prove::shielded::{
    BINDING_BLIND_LANES, ShieldedSpendCompleteWitness, ShieldedSpendMembership,
    ShieldedTransferWitness, TREE_DEPTH, WideValueBindingError, WideValueBindingProof,
    WideValueBindingWitness, generate_wide_value_binding_trace, prove_shielded_transfer,
    prove_wide_value_binding, verify_same_opening, verify_wide_sidecar_proof,
    wide_value_binding_descriptor,
};

/// A COMPLETE-spend witness over a REAL committed `ShieldedNoteSet`, carrying the same
/// `(value, asset, randomness, blind)` as the sidecar under test — so the spend proof's PI-pinned
/// sixteen-lane carrier IS the ring binding the sidecar must join.
///
/// ⚑ This is the point of the flag day, in the harness: the ring binding used to be a value this
/// test SYNTHESIZED (`honest_witness.wide_binding()`), which is exactly the vacuous-identity shape
/// `ShieldedWideJoinPin.join_still_decouples` names. It now comes off a separate, verified proof.
fn spend_in_set(
    value: u64,
    asset: u64,
    randomness: BabyBear,
) -> (ShieldedSpendCompleteWitness, ShieldedNoteSet) {
    let probe = ShieldedSpendCompleteWitness {
        value,
        asset_type: asset,
        randomness,
        spending_key: [
            BabyBear::new(11),
            BabyBear::new(13),
            BabyBear::new(17),
            BabyBear::new(19),
        ],
        binding_blind: blind(),
        membership: ShieldedSpendMembership {
            positions: [0; TREE_DEPTH],
            siblings: [[[BabyBear::ZERO; 8]; 3]; TREE_DEPTH],
            next_addr: TaggedKeyWire::top(),
        },
    };
    let commitment = ShieldedNoteCommitment(felt_to_bytes32(probe.note_commitment_felt()));
    let mut set = ShieldedNoteSet::new();
    set.insert(ShieldedNoteCommitment(felt_to_bytes32(BabyBear::new(
        0x0A0A_0001,
    ))))
    .expect("decoy inserts");
    set.insert(commitment).expect("the spent note is committed");
    let path = set
        .membership_path(&commitment)
        .expect("the committed note has a membership path");
    let witness = ShieldedSpendCompleteWitness {
        membership: ShieldedSpendMembership {
            positions: path.path.positions,
            siblings: path.path.siblings,
            next_addr: path.leaf.next_addr().wire(),
        },
        ..probe
    };
    (witness, set)
}

fn blind() -> [BabyBear; BINDING_BLIND_LANES] {
    core::array::from_fn(|i| BabyBear::new(0x1000 + (i as u32) * 0x111))
}

/// The relation the DEPLOYED sidecar proves against is the Lean-emitted one, and the felt-width
/// repair (128 boolean limb pins) is present in it. `wide_value_binding_lean_route.rs` checks the
/// same object straight out of the Lean source; this checks what `prove_wide_value_binding` and
/// `prove_wide_value_binding` / `verify_wide_sidecar_proof` actually load.
#[test]
fn the_deployed_relation_is_the_lean_emitted_one() {
    let desc = wide_value_binding_descriptor();
    assert_eq!(
        desc.name,
        "dregg-shielded-wide-value-binding-v1::poseidon2-node8"
    );
    assert_eq!(desc.trace_width, col::WIDTH);
    assert_eq!(desc.trace_width, 162);
    assert_eq!(desc.public_input_count, 17);
    assert_eq!(desc.constraints.len(), 158);

    // 128 boolean limb pins + 8 limb recompositions + 2 compatibility reductions, all as IR-v2
    // base gates; plus the 17 first-row PI pins.
    let gates = desc
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::Gate(_))))
        .count();
    assert_eq!(gates, 2 * 4 * 16 + 2 * 4 + 2);
    let pins = desc
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
        .count();
    assert_eq!(pins, 17);

    // The two domain-separated `node8` carriers and the one compatibility `hash_fact` join.
    let wide_sites = desc
        .constraints
        .iter()
        .filter(|c| {
            matches!(c, VmConstraint2::Lookup(l)
                if l.table == dregg_circuit::descriptor_ir2::TID_P2)
        })
        .count();
    assert_eq!(wide_sites, 2);
    let fact_sites = desc
        .constraints
        .iter()
        .filter(|c| {
            matches!(c, VmConstraint2::Lookup(l)
                if l.table == dregg_circuit::descriptor_ir2::TID_P2_NARROW)
        })
        .count();
    assert_eq!(fact_sites, 1);
}

#[test]
fn hostile_turn_wire_decode_is_canonical_and_exact() {
    let witness = WideValueBindingWitness {
        value: 0x1234_5678_9abc_def0,
        asset_type: 0xfedc_ba98_7654_3210,
        legacy_randomness: BabyBear::new(77),
        binding_blind: blind(),
    };
    let proof = prove_wide_value_binding(&witness).expect("wide value proof");
    let proof_bytes = proof.proof_bytes();
    let legacy = proof.claim.legacy_binding.as_u32();
    let wide = proof.claim.wide_binding.map(BabyBear::as_u32);

    let decoded = WideValueBindingProof::from_serialized_parts(legacy, wide, &proof_bytes)
        .expect("canonical Turn wire should decode");
    // Same-opening join: the ring's exposed wide carrier IS this opening's, so the
    // sidecar opens the ring's value — accepted.
    verify_same_opening(&proof.claim.wide_binding, &decoded.claim.wide_binding)
        .expect("the decoded claim is the same opening");
    verify_wide_sidecar_proof(&decoded).expect("decoded proof must retain the exact public claim");

    let mut noncanonical = wide;
    noncanonical[7] = BABYBEAR_P;
    assert!(matches!(
        WideValueBindingProof::from_serialized_parts(legacy, noncanonical, &proof_bytes),
        Err(WideValueBindingError::NonCanonicalPublicField {
            lane: 8,
            value: BABYBEAR_P
        })
    ));

    assert!(matches!(
        WideValueBindingProof::from_serialized_parts(
            legacy,
            wide,
            &proof_bytes[..proof_bytes.len() / 2],
        ),
        Err(WideValueBindingError::ProofDecode { .. })
    ));
}

/// Recompute every hash/output cell after a malicious trace edit, so a failed
/// proof isolates the canonical-limb range gate rather than an incidental hash
/// mismatch.
///
/// Indexing is by the Lean column layout (`col`, the mirror of
/// `WideValueBindingEmit.lean` §2). The v1 descriptor's per-column `ColumnDef` name/kind metadata
/// — which the old `column(descriptor, "…")` helper looked names up in — has no IR-v2 counterpart
/// and is gone with the Rust descriptor; `domain_a`/`domain_b`/`zero` are no longer columns at all
/// (Lean pins them as literal constants inside the chip tuples).
fn refill_public_hashes(row: &mut [BabyBear]) -> [BabyBear; 17] {
    let left = |row: &[BabyBear], domain: u32| {
        [
            BabyBear::new(domain),
            row[col::limb(0, 0)],
            row[col::limb(0, 1)],
            row[col::limb(0, 2)],
            row[col::limb(0, 3)],
            row[col::limb(1, 0)],
            row[col::limb(1, 1)],
            row[col::limb(1, 2)],
        ]
    };
    let right = [
        row[col::limb(1, 3)],
        row[col::RANDOMNESS],
        row[col::BLIND],
        row[col::BLIND + 1],
        row[col::BLIND + 2],
        row[col::BLIND + 3],
        row[col::BLIND + 4],
        row[col::BLIND + 5],
    ];
    let a = cap_node8(left(row, DOMAIN_A), right);
    let b = cap_node8(left(row, DOMAIN_B), right);
    for i in 0..8 {
        row[col::WIDE_A + i] = a[i];
        row[col::WIDE_B + i] = b[i];
    }
    let legacy = hash_fact(
        row[col::VALUE_MOD_P],
        &[row[col::ASSET_MOD_P], row[col::RANDOMNESS], BabyBear::ZERO],
    );
    row[col::LEGACY_BINDING] = legacy;
    let mut pis = [BabyBear::ZERO; 17];
    pis[0] = legacy;
    pis[1..9].copy_from_slice(&a);
    pis[9..17].copy_from_slice(&b);
    pis
}

#[test]
fn a_seventeenth_limb_bit_has_no_satisfying_trace() {
    let witness = WideValueBindingWitness {
        value: 0,
        asset_type: 0,
        legacy_randomness: BabyBear::new(77),
        binding_blind: blind(),
    };
    let (mut trace, _) = generate_wide_value_binding_trace(&witness);

    // Forge limb 0 to 2^16 while leaving its sixteen binary cells all zero.
    // Update value_mod_p, BOTH wide hashes, the compatibility hash, and every
    // public input to match the forgery. Thus only the exact 16-bit limb
    // recomposition is violated.
    let mut forged_pis = [BabyBear::ZERO; 17];
    for row in &mut trace {
        row[col::limb(0, 0)] = BabyBear::new(1 << 16);
        row[col::VALUE_MOD_P] = BabyBear::new(1 << 16);
        forged_pis = refill_public_hashes(row);
    }

    let statement = DescriptorStatement::try_new(
        wide_value_binding_descriptor().clone(),
        forged_pis.iter().map(|f| f.as_u32()).collect(),
    )
    .expect("the forged claim is still canonical and correctly sized");
    let mem = MemBoundaryWitness::default();
    let umem = UMemBoundaryWitness::default();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        Plonky3HidingFriReference::prove(
            &statement,
            Plonky3HidingFriWitness {
                base_trace: &trace,
                mem_boundary: &mem,
                map_heaps: &[],
                umem_boundary: &umem,
            },
        )
    }));
    assert!(
        !matches!(result, Ok(Ok(_))),
        "a 17-bit limb must not produce a verifying hiding proof"
    );
}

#[test]
fn full_u64_alias_is_distinguished_and_each_join_lane_is_load_bearing() {
    // Keep every high limb live. `alias = value + p` is a DIFFERENT u64 that
    // has exactly the same current one-felt representation.
    let value = 0x1234_5678_9abc_def0u64;
    let alias = value + BABYBEAR_P as u64;
    let asset = 0xfedc_ba98_7654_3210u64;
    let randomness = BabyBear::new(0x13579);

    let honest_witness = WideValueBindingWitness {
        value,
        asset_type: asset,
        legacy_randomness: randomness,
        binding_blind: blind(),
    };
    let alias_witness = WideValueBindingWitness {
        value: alias,
        ..honest_witness.clone()
    };

    assert_eq!(
        honest_witness.legacy_binding(),
        alias_witness.legacy_binding(),
        "the migration starts from a real modulo-p alias in the v1 C7 felt"
    );
    assert_ne!(
        honest_witness.wide_binding(),
        alias_witness.wide_binding(),
        "canonical 16-bit limbs must distinguish value from value+p"
    );

    // Build the COMPLETE hidden spend over a real committed accumulator, then join the full-u64
    // sidecar to that accepting proof's own PI-pinned carrier.
    //
    // ⚑ FLAG DAY (value link): the sidecar is no longer the shielded TRANSFER's value gate — the
    // Lean-emitted `dregg-shielded-transfer-value-link::v1` is, and it proves everything the
    // sidecar proves about an input carrier PLUS the tie to the minted note. So this file now
    // tests the sidecar RELATION and the same-opening comparison as standalone objects; the
    // transfer-path teeth moved to `shielded_transfer_value_link.rs` and
    // `turn-prover/tests/shielded_executor.rs`.
    let (spend, set) = spend_in_set(value, asset, randomness);
    let committed_root = set.root8().limbs();
    let transfer = prove_shielded_transfer(&ShieldedTransferWitness {
        spend,
        out_owner: BabyBear::new(0x0777),
        out_randomness: BabyBear::new(0x0888),
    })
    .expect("the complete shielded spend plus its value link should prove");
    transfer
        .verify(committed_root)
        .expect("the honest transfer verifies under its own committed root");

    let mut honest = prove_wide_value_binding(&honest_witness)
        .expect("full-u64 wide binding should prove through the hiding IR-v2 backend");
    // ⚑ THE RING BINDING, FROM THE PROOF. This is `transfer.inputs[0].spend_wide_binding` — a
    // PUBLIC INPUT of the complete-spend proof, pinned by the Lean `carrierPins`. The assertion
    // below is the non-vacuity guard: the two carriers agree because the two relations opened the
    // same note, not because one was copied from the other.
    let ring_wide_binding = transfer.inputs[0].spend_wide_binding;
    assert_eq!(
        ring_wide_binding,
        honest_witness.wide_binding(),
        "the complete-spend proof's PI-pinned carrier must equal the sidecar relation's carrier \
         over the same (value, asset, randomness, blind) — this is what makes the join comparable"
    );

    // SATISFIABLE: the honest sidecar opens the ring's value, and its own proof verifies.
    verify_same_opening(&ring_wide_binding, &honest.claim.wide_binding)
        .expect("the same-opening join accepts two proofs of the SAME opening");
    verify_wide_sidecar_proof(&honest).expect("the honest sidecar proof verifies");

    // ── THE FALSIFIER. The alias (`value + p`) is a DIFFERENT full-`u64` opening that shares the
    // honest opening's ~31-bit `legacy_binding` felt but NOT the sixteen lanes, so the join
    // separates what the one-felt binding cannot.
    let alias_proof = prove_wide_value_binding(&alias_witness)
        .expect("the alias sidecar proves its own relation");
    assert_eq!(
        alias_proof.claim.legacy_binding, honest.claim.legacy_binding,
        "the one-felt surface is BLIND to the alias — that is the wound the wide carrier closes"
    );
    assert!(
        verify_same_opening(&ring_wide_binding, &alias_proof.claim.wide_binding).is_err(),
        "an x+p sidecar must NOT join an x ring carrier"
    );

    // FALSE polarity 1: splice a different public wide lane onto the genuine sidecar proof. The
    // HidingFri verifier must reject; every public carrier lane is bound by a real Poseidon2
    // permutation output constraint.
    let saved = honest.claim;
    honest.claim.wide_binding[15] += BabyBear::ONE;
    assert!(
        verify_wide_sidecar_proof(&honest).is_err(),
        "a forged wide public lane must reject"
    );

    // FALSE polarity 2: retain the genuine wide lanes/proof but join it to a different ring
    // opening. The same-opening join rejects.
    honest.claim = saved;
    let mut other_ring = ring_wide_binding;
    other_ring[0] += BabyBear::ONE;
    assert!(
        verify_same_opening(&other_ring, &honest.claim.wide_binding).is_err(),
        "a wide sidecar must not join a different ring opening"
    );

    // ⚑ AND THE #15 CANARY, at this layer: the same accepting transfer, judged under a root that
    // is not the tree it folded to, REFUSES. The committed root is not decoration.
    assert!(
        transfer
            .verify(ShieldedNoteSet::new().root8().limbs())
            .is_err(),
        "a spend judged under a foreign committed root must reject"
    );
}
