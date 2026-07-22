//! UMEM-V2 faithful-codec and complete-boundary hostility teeth.
//!
//! V1 remains callable for the deployed protocol epoch, but its one-felt
//! address/value images admit deterministic `+ BabyBear::ORDER` aliases. V2
//! must keep those raw sources distinct, keep value variants distinct, bound
//! exact blob material, and reject duplicate boundary addresses.

use std::collections::{BTreeMap, BTreeSet};

use dregg_cell::CellId;
use dregg_circuit::field::BABYBEAR_P;
use dregg_turn::umem::{
    UAddrV2, UKey, UMEM_V2_ADDR_LIMBS, UMEM_V2_MAX_BLOB_BYTES, UProjection, UVal, UValV2,
    UmemBoundaryEntryV2, UmemBoundaryV2, UmemKind, UmemOp, UmemTraceV2, UmemTurnWitness,
    UmemV2Error, fold, umem_key_addr_v1, umem_proving_inputs_from_v1, umem_val_felt_v1,
};

fn zero_and_plus_p() -> ([u8; 32], [u8; 32]) {
    let zero = [0u8; 32];
    let mut plus_p = [0u8; 32];
    plus_p[..4].copy_from_slice(&BABYBEAR_P.to_le_bytes());
    (zero, plus_p)
}

fn write(key: UKey, value: UVal) -> UmemOp {
    UmemOp {
        kind: UmemKind::Write,
        key,
        val: Some(value),
        prev_val: None,
        prev_serial: 0,
    }
}

#[test]
fn v2_address_is_fixed_raw_source_and_named_v1_collisions_separate() {
    let (zero, plus_p) = zero_and_plus_p();
    let cell_zero = CellId(zero);
    let cell_plus_p = CellId(plus_p);

    // Cell identity: V1 first folds CellId to one felt, so +p in one raw u32
    // limb is invisible. V2 carries all 16 raw u16 limbs.
    let cell_a = UKey::Balance(cell_zero);
    let cell_b = UKey::Balance(cell_plus_p);
    assert_eq!(umem_key_addr_v1(&cell_a), umem_key_addr_v1(&cell_b));
    assert_ne!(UAddrV2::from_key(&cell_a), UAddrV2::from_key(&cell_b));

    // Nullifier source: the same deterministic v1 alias, directly at the key.
    let nullifier_a = UKey::NoteNullifier(zero);
    let nullifier_b = UKey::NoteNullifier(plus_p);
    assert_eq!(
        umem_key_addr_v1(&nullifier_a),
        umem_key_addr_v1(&nullifier_b)
    );
    assert_ne!(
        UAddrV2::from_key(&nullifier_a),
        UAddrV2::from_key(&nullifier_b)
    );

    // u64 slot source: V1 explicitly reduces modulo p. V2 carries four exact
    // big-endian u16 limbs, so raw-source lexicographic order is numeric here.
    let slot_a = UKey::Field {
        cell: cell_zero,
        slot: 0,
    };
    let slot_b = UKey::Field {
        cell: cell_zero,
        slot: BABYBEAR_P as u64,
    };
    assert_eq!(umem_key_addr_v1(&slot_a), umem_key_addr_v1(&slot_b));
    let slot_a_v2 = UAddrV2::from_key(&slot_a);
    let slot_b_v2 = UAddrV2::from_key(&slot_b);
    assert!(slot_a_v2 < slot_b_v2);
    assert_ne!(slot_a_v2.limbs(), slot_b_v2.limbs());

    assert_eq!(std::mem::size_of::<UAddrV2>(), 44);
    assert_eq!(slot_a_v2.limbs().len(), UMEM_V2_ADDR_LIMBS);
}

#[test]
fn every_v2_key_constructor_has_a_distinct_stable_tag() {
    let cell = CellId([0x31; 32]);
    let keys = vec![
        UKey::Exist(cell),
        UKey::Field { cell, slot: 7 },
        UKey::Balance(cell),
        UKey::Nonce(cell),
        UKey::ProvedState(cell),
        UKey::Lifecycle(cell),
        UKey::Mode(cell),
        UKey::Identity(cell),
        UKey::FieldVisibility { cell, slot: 7 },
        UKey::FieldCommitment { cell, slot: 7 },
        UKey::SwissTableRoot(cell),
        UKey::RefcountTableRoot(cell),
        UKey::SystemRoot { cell, index: 7 },
        UKey::HeapRoot(cell),
        UKey::Heap {
            cell,
            collection: 7,
            key: 8,
        },
        UKey::SovereignCommitment(cell),
        UKey::CapSlot { cell, slot: 7 },
        UKey::Delegate(cell),
        UKey::DelegationSnapshot(cell),
        UKey::DelegationEpoch(cell),
        UKey::CommittedHeight(cell),
        UKey::Permissions(cell),
        UKey::VerificationKey(cell),
        UKey::Program(cell),
        UKey::Factory([0x32; 32]),
        UKey::NoteNullifier([0x33; 32]),
        UKey::BridgedNullifier([0x34; 32]),
        UKey::Receipt(7),
        UKey::Working {
            service: cell,
            collection: 7,
            key: 8,
        },
        UKey::CapTombstone { cell, slot: 7 },
    ];
    let addrs: BTreeSet<_> = keys.iter().map(UAddrV2::from_key).collect();
    let variants: BTreeSet<_> = addrs.iter().map(|addr| addr.variant()).collect();
    assert_eq!(addrs.len(), keys.len());
    assert_eq!(variants, (1u16..=30).collect());
}

#[test]
fn v2_values_preserve_plus_p_bytes_and_bytes32_umemref_type() {
    let (zero, plus_p) = zero_and_plus_p();
    let zero_bytes = UVal::Bytes32(zero);
    let plus_p_bytes = UVal::Bytes32(plus_p);

    // V1 reduces each 4-byte chunk before its Poseidon fold.
    assert_eq!(
        umem_val_felt_v1(Some(&zero_bytes)),
        umem_val_felt_v1(Some(&plus_p_bytes))
    );
    let zero_v2 = UValV2::try_from_value(Some(&zero_bytes)).unwrap();
    let plus_p_v2 = UValV2::try_from_value(Some(&plus_p_bytes)).unwrap();
    assert_ne!(zero_v2, plus_p_v2);
    assert_eq!(zero_v2.source_bytes(), zero);
    assert_eq!(plus_p_v2.source_bytes(), plus_p);

    // V1 intentionally used the same scalar branch for raw Bytes32 and a
    // compositional UmemRef. V2's variant tag makes their meanings distinct.
    let umem_ref = UVal::UmemRef(zero);
    assert_eq!(
        umem_val_felt_v1(Some(&zero_bytes)),
        umem_val_felt_v1(Some(&umem_ref))
    );
    let ref_v2 = UValV2::try_from_value(Some(&umem_ref)).unwrap();
    assert_ne!(zero_v2, ref_v2);
    assert_ne!(zero_v2.variant(), ref_v2.variant());

    let absent = UValV2::try_from_value(None).unwrap();
    let present = UValV2::try_from_value(Some(&UVal::Present)).unwrap();
    assert_eq!(absent.presence(), 0);
    assert_eq!(present.presence(), 1);
    assert_ne!(absent.canonical_limbs(), present.canonical_limbs());
}

#[test]
fn blob_packing_is_exact_canonical_and_bounded() {
    let odd = UVal::Blob(vec![0x01, 0x02, 0x03]);
    let encoded = UValV2::try_from_value(Some(&odd)).unwrap();
    assert_eq!(encoded.source_byte_len(), 3);
    assert_eq!(encoded.payload(), &[0x0102, 0x0300]);
    assert_eq!(encoded.source_bytes(), vec![0x01, 0x02, 0x03]);
    assert_eq!(encoded.canonical_limbs()[4..], [0x0102, 0x0300]);

    let at_bound = UVal::Blob(vec![0x5a; UMEM_V2_MAX_BLOB_BYTES]);
    let at_bound = UValV2::try_from_value(Some(&at_bound)).expect("bound is inclusive");
    assert_eq!(at_bound.source_byte_len() as usize, UMEM_V2_MAX_BLOB_BYTES);
    assert_eq!(at_bound.payload().len(), UMEM_V2_MAX_BLOB_BYTES / 2);

    let oversized = UVal::Blob(vec![0; UMEM_V2_MAX_BLOB_BYTES + 1]);
    assert!(matches!(
        UValV2::try_from_value(Some(&oversized)),
        Err(UmemV2Error::BlobTooLarge { len, max })
            if len == UMEM_V2_MAX_BLOB_BYTES + 1 && max == UMEM_V2_MAX_BLOB_BYTES
    ));
}

#[test]
fn full_v2_boundary_accepts_v1_colliders_and_keeps_untouched_image() {
    let (zero, plus_p) = zero_and_plus_p();
    let untouched = UKey::Nonce(CellId([0x44; 32]));
    let mut pre: UProjection = BTreeMap::new();
    pre.insert(untouched.clone(), UVal::U64(9));

    let ops = vec![
        write(UKey::NoteNullifier(zero), UVal::Present),
        write(UKey::NoteNullifier(plus_p), UVal::Present),
    ];

    // The V1 producer does fail closed when both aliases are co-located. That
    // refusal is useful but is not an injective wire representation.
    let v1 = umem_proving_inputs_from_v1(&pre, &ops).unwrap_err();
    assert!(v1.contains("address codec collision"));

    let post = fold(&pre, &ops);
    let witness = UmemTurnWitness {
        pre,
        ops,
        post,
        synthesized: 0,
    };
    let boundary = UmemBoundaryV2::from_witness(&witness).expect("faithful V2 image");
    assert_eq!(boundary.entries().len(), 3);
    assert!(
        boundary
            .entries()
            .windows(2)
            .all(|pair| pair[0].addr < pair[1].addr)
    );
    assert!(boundary.entries().iter().any(
        |entry| entry.addr == UAddrV2::from_key(&untouched) && entry.init == entry.final_value
    ));
    let trace = UmemTraceV2::from_witness(&witness).expect("exact V2 trace");
    assert_eq!(trace.ops().len(), 2);
    assert_eq!(trace.ops()[0].serial_limbs(), [0, 0, 0, 1]);
    assert_eq!(trace.ops()[1].serial_limbs(), [0, 0, 0, 2]);
    assert_eq!(trace.ops()[0].prev_serial_limbs(), [0; 4]);
    assert_eq!(trace.boundary(), &boundary);
}

#[test]
fn duplicate_boundary_and_false_replay_claims_refuse() {
    let key = UKey::Receipt(7);
    let value = UValV2::try_from_value(Some(&UVal::Bytes32([0x77; 32]))).unwrap();
    let entry = UmemBoundaryEntryV2 {
        addr: UAddrV2::from_key(&key),
        init: UValV2::try_from_value(None).unwrap(),
        final_value: value,
    };
    assert!(matches!(
        UmemBoundaryV2::try_from_entries(vec![entry.clone(), entry]),
        Err(UmemV2Error::DuplicateAddress(_))
    ));

    let mut bad = write(key.clone(), UVal::Bytes32([0x77; 32]));
    bad.prev_val = Some(UVal::Bytes32([0x66; 32]));
    assert!(matches!(
        UmemBoundaryV2::from_full_image(&BTreeMap::new(), &[bad]),
        Err(UmemV2Error::PreviousValueMismatch { index: 0, key: k }) if k == key
    ));

    let mut wrong_serial = write(key.clone(), UVal::Bytes32([0x77; 32]));
    wrong_serial.prev_serial = 1;
    assert!(matches!(
        UmemBoundaryV2::from_full_image(&BTreeMap::new(), &[wrong_serial]),
        Err(UmemV2Error::PreviousSerialMismatch {
            index: 0,
            key: k,
            expected: 0,
            actual: 1,
        }) if k == key
    ));

    // A freshness/non-membership read is absent at BOTH endpoints, but its
    // address still belongs to the complete declared boundary image.
    let absent_read = UmemOp {
        kind: UmemKind::Read,
        key: UKey::NoteNullifier([0x88; 32]),
        val: None,
        prev_val: None,
        prev_serial: 0,
    };
    let absent_boundary =
        UmemBoundaryV2::from_full_image(&BTreeMap::new(), &[absent_read]).unwrap();
    assert_eq!(absent_boundary.entries().len(), 1);
    assert_eq!(absent_boundary.entries()[0].init.presence(), 0);
    assert_eq!(absent_boundary.entries()[0].final_value.presence(), 0);

    let false_read = UmemOp {
        kind: UmemKind::Read,
        key: UKey::Receipt(8),
        val: Some(UVal::U64(1)),
        prev_val: None,
        prev_serial: 0,
    };
    assert!(matches!(
        UmemBoundaryV2::from_full_image(&BTreeMap::new(), &[false_read]),
        Err(UmemV2Error::ReadValueMismatch { index: 0, .. })
    ));

    let op = write(UKey::Receipt(9), UVal::U64(2));
    let false_post = UmemTurnWitness {
        pre: BTreeMap::new(),
        ops: vec![op],
        post: BTreeMap::new(),
        synthesized: 0,
    };
    assert_eq!(
        UmemBoundaryV2::from_witness(&false_post),
        Err(UmemV2Error::PostReplayMismatch)
    );
}

#[test]
fn full_image_size_and_host_cost_smoke() {
    const CELLS: u64 = 4_096;
    let mut pre = UProjection::new();
    for position in 0..CELLS {
        pre.insert(UKey::Receipt(position), UVal::U64(position));
    }
    let op = UmemOp {
        kind: UmemKind::Write,
        key: UKey::Receipt(CELLS - 1),
        val: Some(UVal::U64(CELLS)),
        prev_val: Some(UVal::U64(CELLS - 1)),
        prev_serial: 0,
    };
    let started = std::time::Instant::now();
    let boundary = UmemBoundaryV2::from_full_image(&pre, &[op]).unwrap();
    let elapsed = started.elapsed();
    assert_eq!(boundary.entries().len(), CELLS as usize);
    eprintln!(
        "UMEM-V2 host model: addr={}B value-header={}B 4096-cell-full-image={elapsed:?}",
        std::mem::size_of::<UAddrV2>(),
        std::mem::size_of::<UValV2>(),
    );
}
