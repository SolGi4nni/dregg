//! # The umem producer gated its ADDRESS codec and never its VALUE codec — OLD-ADMITS / NEW-REJECTS
//!
//! `dregg_turn::umem::umem_proving_inputs_from_v1` is the ONE function both deployed universal-
//! memory cohort generators call (`umem_cohort_proving_inputs_from` and
//! `umem_cohort_multidomain_proving_inputs_from`), i.e. every umem leg the deployed
//! `prove_vm_descriptor2_umem` is ever handed comes through it. Since it was written it has
//! refused a trace whose distinct `UKey`s lower to one `(domain, key)` felt, with the reason
//! stated at the site: *"else the boundary's strict-increasing requirement (and the multiset
//! balance) is unsound."*
//!
//! The identical argument applies to the OTHER coordinate of the same row and **was not gated at
//! all**. `umem_val_felt_v1` lowers a typed `Option<&UVal>` to `(present, value)` — two felts —
//! and it is many-to-one on the source along three independent axes. This file exhibits all
//! three, each built into a WELL-FORMED trace that the retired derivation ACCEPTS and whose
//! emitted rows and boundary are BYTE-IDENTICAL to the honest trace's.
//!
//! ## What an accepted alias buys, concretely
//!
//! The umem AIR decides a fact about FELT ROWS: that they form a consistent offline-checked
//! memory over `(domain, key)`. The host reads those rows back as TYPED SOURCES, and
//! `dregg_turn::umem::reify_cell` genuinely dispatches on the variant (`expect_bytes32`,
//! `expected Int`, `expected U64`). So where the lowering is not injective on the sources a trace
//! contains, a read-after-write the AIR certifies as consistent can be a `Bytes32` write answered
//! by a `UmemRef` read — and `UVal::UmemRef`'s own doc says its bytes are "the child's
//! sorted-Poseidon2 root", consumed by `open_through_umem_ref` as a CHILD UMEM'S COMMITTED ROOT.
//! A writer who may write an arbitrary 32-byte field element may therefore have it read back as a
//! committed child-umem root that they chose.
//!
//! ⚠ **This is a PRODUCER-side refusal, so it is an honesty gate, not a soundness one** — and the
//! address half it mirrors has exactly the same character. A prover who declines to call the
//! producer is not stopped by it. What it buys is that no trace the deployed cohort generators
//! hand to the prover can carry an alias the committed row cannot express. Closing it on the
//! VERIFYING side is the V2 wire widening, which is a Lean-authored emit epoch and is priced in
//! `turn/src/umem.rs`'s UMEM-V2 section.
//!
//! ## The three axes and their costs — COLLISION, not second preimage
//!
//! The producer of a trace chooses BOTH sides of every pair below, so the governing figure is a
//! collision throughout. Quoting the second-preimage number (`2^30.91` for axis 3) would be the
//! flattering half of the pair.
//!
//! 1. **Variant erasure — cost 0, no search.** `Some(Bytes32(b))` and `Some(UmemRef(b))` share a
//!    single match arm in `umem_val_felt_v1`: `(ONE, fold_bytes32(b))`.
//! 2. **The `+p` chunk alias — cost 0, one addition.** `fold_bytes32` is
//!    `hash_many(bytes32_to_8_limbs(b))`, and `bytes32_to_8_limbs` is a per-4-byte-chunk `u32 % p`
//!    projection with `2p < 2^32`, so `v` and `v + p` are different bytes with an identical limb.
//! 3. **The one-felt squeeze — `2^15.4534`, and this one is genuinely SEARCHED.**
//!    `log2 p = log2 2013265921 = 30.906891`, so a birthday collision over the image costs
//!    `2^(30.906891 / 2) = 2^15.4534 ≈ 44,900` evaluations. `find_squeeze_collision` below runs
//!    that search deterministically and reports the measured count. Its candidates all carry
//!    DISTINCT limb vectors by construction (the varied chunk stays below `p`, so no candidate is
//!    an axis-2 alias of another) — so what it finds is a collision of the SQUEEZE, not of the
//!    encoder, and the `2^15.4534` figure is the one that applies to it.

use std::collections::HashMap;

use dregg_cell::CellId;
use dregg_circuit::cap_root::fold_bytes32;
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, prove_vm_descriptor2_umem, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::bytes32_to_8_limbs;
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_turn::umem::{
    UKey, UMEM_V2_MAX_BLOB_BYTES, UProjection, UVal, UValV2, UmemKind, UmemOp, umem_key_addr_v1,
    umem_proving_inputs_from_v1, umem_val_felt_v1,
};

// ---------------------------------------------------------------------------
// The RETIRED derivation, reconstructed from the SAME public lowering the live producer calls.
// ---------------------------------------------------------------------------

/// The rows + boundary the producer emitted BEFORE the value gate: the address gate, then the
/// row/boundary derivation, and nothing between them.
///
/// This is built out of the live public `umem_key_addr_v1` / `umem_val_felt_v1`, not a private
/// copy of them, so it cannot drift into a strawman — and
/// [`the_retired_reconstruction_agrees_with_the_live_producer_on_an_honest_trace`] pins it against
/// the real function on a trace both accept.
type RetiredOutput = (
    Vec<Vec<BabyBear>>,
    Vec<(u32, BabyBear)>,
    Vec<Option<BabyBear>>,
);

fn retired_derivation(pre: &UProjection, ops: &[UmemOp]) -> Result<RetiredOutput, String> {
    use std::collections::BTreeMap;

    if ops.is_empty() {
        return Err("umem producer: empty op trace (no boundary to derive)".into());
    }
    // The ADDRESS gate — the half that always existed.
    let mut by_addr: BTreeMap<(u32, u32), UKey> = BTreeMap::new();
    let mut touched: BTreeMap<UKey, (u32, BabyBear)> = BTreeMap::new();
    for op in ops {
        let (d, key) = umem_key_addr_v1(&op.key);
        match by_addr.get(&(d, key.as_u32())) {
            Some(prev) if prev != &op.key => {
                return Err(format!(
                    "umem producer: address codec collision at domain {d}"
                ));
            }
            _ => {
                by_addr.insert((d, key.as_u32()), op.key.clone());
            }
        }
        touched.entry(op.key.clone()).or_insert((d, key));
    }
    // ...and straight on to the rows. There was no value gate here.
    let mut domains: Vec<u32> = touched.values().map(|(d, _)| *d).collect();
    domains.sort_unstable();
    domains.dedup();
    let guard_col: BTreeMap<u32, usize> = domains
        .iter()
        .enumerate()
        .map(|(i, d)| (*d, 6 + i))
        .collect();
    let width = 6 + domains.len();

    let mut rows: Vec<Vec<BabyBear>> = Vec::with_capacity(ops.len());
    for op in ops {
        let (d, key) = umem_key_addr_v1(&op.key);
        let (present, value) = umem_val_felt_v1(op.val.as_ref());
        let (prev_present, prev_value) = umem_val_felt_v1(op.prev_val.as_ref());
        let mut row = vec![BabyBear::ZERO; width];
        row[0] = key;
        row[1] = present;
        row[2] = value;
        row[3] = prev_present;
        row[4] = prev_value;
        row[5] = BabyBear::new(op.prev_serial as u32);
        row[guard_col[&d]] = BabyBear::ONE;
        rows.push(row);
    }
    let height = rows.len().next_power_of_two().max(4);
    while rows.len() < height {
        rows.push(vec![BabyBear::ZERO; width]);
    }

    let mut addrs: Vec<(u32, BabyBear, Option<BabyBear>)> = touched
        .iter()
        .map(|(k, (d, key))| {
            let (present, value) = umem_val_felt_v1(pre.get(k));
            let init = if present == BabyBear::ONE {
                Some(value)
            } else {
                None
            };
            (*d, *key, init)
        })
        .collect();
    addrs.sort_by_key(|(d, k, _)| (*d, k.as_u32()));
    Ok((
        rows,
        addrs.iter().map(|(d, k, _)| (*d, *k)).collect(),
        addrs.iter().map(|(_, _, v)| *v).collect(),
    ))
}

// ---------------------------------------------------------------------------
// Trace scaffolding — ONE address, touched twice, so the ADDRESS gate is satisfied and the only
// thing on trial is the VALUE coordinate.
// ---------------------------------------------------------------------------

fn cell() -> CellId {
    let mut raw = [0u8; 32];
    raw[0] = 0xC0;
    raw[31] = 0x1D;
    CellId(raw)
}

fn addr() -> UKey {
    UKey::Field {
        cell: cell(),
        slot: 0,
    }
}

/// A well-formed two-op trace at ONE address: install `written`, then a second write whose
/// claimed prior value is `claimed_prev`. Setting `claimed_prev != written` while the two lower
/// to the same felt cell is exactly the alias under test.
fn trace(written: UVal, claimed_prev: UVal) -> (UProjection, Vec<UmemOp>) {
    let pre = UProjection::new();
    let ops = vec![
        UmemOp {
            kind: UmemKind::Write,
            key: addr(),
            val: Some(written),
            prev_val: None,
            prev_serial: 0,
        },
        UmemOp {
            kind: UmemKind::Write,
            key: addr(),
            val: Some(UVal::U64(7)),
            prev_val: Some(claimed_prev),
            prev_serial: 1,
        },
    ];
    (pre, ops)
}

/// The deterministic birthday search of axis 3, over candidates that are pairwise NON-aliasing in
/// the encoder — every candidate varies only chunk 0, and stays strictly below `p`, so
/// `bytes32_to_8_limbs` reduces nothing and all limb vectors are distinct. A hit is therefore a
/// collision of the SQUEEZE.
///
/// Returns `(a, b, evaluations)`.
fn find_squeeze_collision() -> ([u8; 32], [u8; 32], u64) {
    // Cached: three tests consume the same pair and the search is the file's whole cost.
    static FOUND: std::sync::OnceLock<([u8; 32], [u8; 32], u64)> = std::sync::OnceLock::new();
    *FOUND.get_or_init(search_squeeze_collision)
}

fn search_squeeze_collision() -> ([u8; 32], [u8; 32], u64) {
    let mut seen: HashMap<u32, u32> = HashMap::new();
    let mk = |i: u32| {
        let mut raw = [0u8; 32];
        raw[..4].copy_from_slice(&i.to_le_bytes());
        raw[31] = 0xA5; // a fixed tail so this corpus is not the `zero_and_plus_p` one
        raw
    };
    let mut evaluations = 0u64;
    for i in 0..BABYBEAR_P {
        let candidate = mk(i);
        evaluations += 1;
        let image = fold_bytes32(&candidate).as_u32();
        if let Some(&j) = seen.get(&image) {
            return (mk(j), candidate, evaluations);
        }
        seen.insert(image, i);
    }
    panic!("no squeeze collision inside the field — impossible by pigeonhole");
}

// ===========================================================================
// ANTI-VACUITY — the retired reconstruction is the real thing, and V2 round-trips.
// ===========================================================================

#[test]
fn the_retired_reconstruction_agrees_with_the_live_producer_on_an_honest_trace() {
    let value = UVal::Bytes32([0x11; 32]);
    let (pre, ops) = trace(value.clone(), value);
    let live = umem_proving_inputs_from_v1(&pre, &ops).expect("honest trace still admitted");
    let (rows, addrs, init_vals) = retired_derivation(&pre, &ops).expect("retired derivation");
    assert_eq!(
        live.rows, rows,
        "the retired reconstruction must emit the live producer's rows, or this file is testing a \
         strawman rather than the construction that was retired"
    );
    assert_eq!(
        live.boundary.addrs, addrs,
        "and the same boundary addresses"
    );
    assert_eq!(
        live.boundary.init_vals, init_vals,
        "and the same init image"
    );
}

#[test]
fn the_v2_encoding_round_trips_every_source_this_file_aliases() {
    let (a, b, _) = find_squeeze_collision();
    let sources = [
        UVal::Bytes32(a),
        UVal::Bytes32(b),
        UVal::UmemRef(a),
        UVal::U64(7),
        UVal::Int(-3),
        UVal::Bool(true),
        UVal::Blob(vec![9, 8, 7]),
    ];
    for source in &sources {
        let encoded = UValV2::try_from_value(Some(source)).expect("in-bound source encodes");
        let expected: Vec<u8> = match source {
            UVal::Bytes32(v) | UVal::UmemRef(v) => v.to_vec(),
            UVal::U64(v) => v.to_be_bytes().to_vec(),
            UVal::Int(v) => v.to_be_bytes().to_vec(),
            UVal::Bool(v) => vec![u8::from(*v)],
            UVal::Blob(v) => v.clone(),
            UVal::Present => Vec::new(),
        };
        assert_eq!(
            encoded.source_bytes(),
            expected,
            "V2 must recover the exact source bytes — a codec that cannot round-trip separates \
             nothing"
        );
        assert_eq!(encoded.presence(), 1, "a present source has presence 1");
    }
    // And absence is its own thing, not a zero-length present value.
    let absent = UValV2::try_from_value(None).expect("absence encodes");
    let empty_present = UValV2::try_from_value(Some(&UVal::Present)).expect("Present encodes");
    assert_ne!(
        absent, empty_present,
        "absence must not alias a zero-payload present value"
    );
}

// ===========================================================================
// AXIS 1 — VARIANT ERASURE, cost 0.
// ===========================================================================

#[test]
fn old_admits_a_bytes32_write_read_back_as_a_umem_ref_and_the_rows_are_identical() {
    let raw = [0x5C; 32];

    // HONEST: write Bytes32(raw), claim Bytes32(raw).
    let (honest_pre, honest_ops) = trace(UVal::Bytes32(raw), UVal::Bytes32(raw));
    // ALIASED: write Bytes32(raw), claim UmemRef(raw) — a DIFFERENT typed value.
    let (alias_pre, alias_ops) = trace(UVal::Bytes32(raw), UVal::UmemRef(raw));

    assert_ne!(
        UVal::Bytes32(raw),
        UVal::UmemRef(raw),
        "the two sources must genuinely differ, or there is nothing to exhibit"
    );

    let honest = retired_derivation(&honest_pre, &honest_ops).expect("retired admits the honest");
    let aliased = retired_derivation(&alias_pre, &alias_ops)
        .expect("⚑ OLD ADMITS: the retired derivation accepts the type-confused trace");

    // Not "the digests differ" — the far stronger statement: the committed trace is the SAME
    // object. A proof over one is a proof over the other.
    assert_eq!(
        honest, aliased,
        "the retired rows + boundary must be byte-identical, which is what makes the confusion \
         invisible to the AIR"
    );

    // And the felt cell really is shared.
    assert_eq!(
        umem_val_felt_v1(Some(&UVal::Bytes32(raw))),
        umem_val_felt_v1(Some(&UVal::UmemRef(raw))),
        "the one-felt lowering must genuinely erase the variant"
    );
}

#[test]
fn new_rejects_the_variant_erasure_and_names_the_value_gate() {
    let raw = [0x5C; 32];
    let (pre, ops) = trace(UVal::Bytes32(raw), UVal::UmemRef(raw));
    let err = umem_proving_inputs_from_v1(&pre, &ops)
        .expect_err("⚑ NEW REJECTS: the value gate must refuse the type-confused trace");
    assert!(
        err.contains("VALUE codec collision"),
        "the refusal must name the value gate, got: {err}"
    );
    assert!(
        err.contains("V2 variant"),
        "the refusal must name the V2 variants it separated, got: {err}"
    );
}

// ===========================================================================
// AXIS 2 — THE `+p` CHUNK ALIAS, cost 0 (one addition).
// ===========================================================================

#[test]
fn old_admits_the_plus_p_chunk_alias_at_zero_cost_and_new_rejects_it() {
    let zero = [0u8; 32];
    let mut plus_p = [0u8; 32];
    plus_p[..4].copy_from_slice(&BABYBEAR_P.to_le_bytes());

    assert_ne!(zero, plus_p, "the two byte strings differ");
    assert_eq!(
        bytes32_to_8_limbs(&zero),
        bytes32_to_8_limbs(&plus_p),
        "and they share a limb vector — the alias is in the ENCODER, constructed by one addition, \
         with no search at any price"
    );

    let (honest_pre, honest_ops) = trace(UVal::Bytes32(zero), UVal::Bytes32(zero));
    let (alias_pre, alias_ops) = trace(UVal::Bytes32(zero), UVal::Bytes32(plus_p));

    let honest = retired_derivation(&honest_pre, &honest_ops).expect("retired admits the honest");
    let aliased = retired_derivation(&alias_pre, &alias_ops)
        .expect("⚑ OLD ADMITS: the retired derivation accepts the +p sibling");
    assert_eq!(
        honest, aliased,
        "the retired rows + boundary are byte-identical for the +p sibling"
    );

    let err = umem_proving_inputs_from_v1(&alias_pre, &alias_ops)
        .expect_err("⚑ NEW REJECTS: the value gate must refuse the +p sibling");
    assert!(
        err.contains("VALUE codec collision"),
        "the refusal must name the value gate, got: {err}"
    );
}

// ===========================================================================
// AXIS 3 — THE ONE-FELT SQUEEZE, SEARCHED. 2^15.4534.
// ===========================================================================

#[test]
fn old_admits_a_searched_squeeze_collision_and_new_rejects_it() {
    let started = std::time::Instant::now();
    let (a, b, evaluations) = find_squeeze_collision();
    let elapsed = started.elapsed();
    eprintln!(
        "umem V1 value squeeze collision: {evaluations} evaluations in {elapsed:?} \
         (derived birthday bound 2^(30.906891/2) = 2^15.4534 ≈ 44,900; expected draws \
         sqrt(pi*p/2) ≈ 56,235 — ONE trial, so this count is a draw, not a check of the bound)"
    );

    assert_ne!(a, b, "the search must return two DISTINCT 32-byte sources");
    assert_ne!(
        bytes32_to_8_limbs(&a),
        bytes32_to_8_limbs(&b),
        "the pair must carry DISTINCT limb vectors, so what collided is the SQUEEZE and not the \
         encoder — otherwise this test would be re-exhibiting axis 2 and the 2^15.4534 figure \
         would not be the one that applies"
    );
    assert_eq!(
        fold_bytes32(&a),
        fold_bytes32(&b),
        "...and they must genuinely share the one-felt image"
    );

    let (honest_pre, honest_ops) = trace(UVal::Bytes32(a), UVal::Bytes32(a));
    let (alias_pre, alias_ops) = trace(UVal::Bytes32(a), UVal::Bytes32(b));

    let honest = retired_derivation(&honest_pre, &honest_ops).expect("retired admits the honest");
    let aliased = retired_derivation(&alias_pre, &alias_ops)
        .expect("⚑ OLD ADMITS: the retired derivation accepts the searched collision");
    assert_eq!(
        honest, aliased,
        "the retired rows + boundary are byte-identical for the searched pair"
    );

    let err = umem_proving_inputs_from_v1(&alias_pre, &alias_ops)
        .expect_err("⚑ NEW REJECTS: the value gate must refuse the searched pair");
    assert!(
        err.contains("VALUE codec collision"),
        "the refusal must name the value gate, got: {err}"
    );
}

// ===========================================================================
// COMPLETENESS — the gate refuses aliases and nothing else, and the honest leg still PROVES.
// ===========================================================================

#[test]
fn completeness_the_same_value_at_one_address_many_times_is_still_admitted() {
    let value = UVal::Bytes32([0x77; 32]);
    let mut pre = UProjection::new();
    pre.insert(addr(), value.clone());
    let ops: Vec<UmemOp> = (0..4)
        .map(|i| UmemOp {
            kind: UmemKind::Write,
            key: addr(),
            val: Some(value.clone()),
            prev_val: Some(value.clone()),
            prev_serial: i,
        })
        .collect();
    umem_proving_inputs_from_v1(&pre, &ops)
        .expect("repeating one source at one address is not a collision");
}

#[test]
fn completeness_one_felt_cell_shared_across_different_addresses_is_still_admitted() {
    // The gate is keyed per-address, because the address is what separates the rows. Two distinct
    // addresses holding sources with the same felt image is ordinary and must stay admitted.
    let raw = [0x31; 32];
    let mut other = cell().0;
    other[1] = 0xEE;
    let pre = UProjection::new();
    let ops = vec![
        UmemOp {
            kind: UmemKind::Write,
            key: addr(),
            val: Some(UVal::Bytes32(raw)),
            prev_val: None,
            prev_serial: 0,
        },
        UmemOp {
            kind: UmemKind::Write,
            key: UKey::Field {
                cell: CellId(other),
                slot: 0,
            },
            val: Some(UVal::UmemRef(raw)),
            prev_val: None,
            prev_serial: 0,
        },
    ];
    assert_eq!(
        umem_val_felt_v1(Some(&UVal::Bytes32(raw))),
        umem_val_felt_v1(Some(&UVal::UmemRef(raw))),
        "the two sources share a felt cell..."
    );
    umem_proving_inputs_from_v1(&pre, &ops)
        .expect("...but at DIFFERENT addresses, which the rows separate — must stay admitted");
}

#[test]
fn completeness_the_gate_does_not_inherit_v2s_64_kib_blob_ceiling() {
    // `UMEM_V2_MAX_BLOB_BYTES` is a replay ceiling for `UmemBoundaryV2::from_full_image`, not a
    // canonicity property, and `project_cell` stores a cell's `Program` / `VerificationKey` planes
    // as unbounded `json(...)` blobs. If the value gate had been routed through
    // `UValV2::try_from_value` it would refuse those honest turns — a collision fix creating an
    // availability cliff. It goes through `UValV2::encode_canonical` instead; this pins that.
    let big = UVal::Blob(vec![0x5a; UMEM_V2_MAX_BLOB_BYTES + 1024]);
    assert!(
        UValV2::try_from_value(Some(&big)).is_err(),
        "the oracle path still enforces its ceiling..."
    );
    let (pre, ops) = trace(big.clone(), big);
    umem_proving_inputs_from_v1(&pre, &ops).expect(
        "...and the producer's value gate must NOT, or a large program plane stops proving",
    );
}

#[test]
fn completeness_the_honest_leg_still_proves_and_verifies_at_the_deployed_umem_prover() {
    let value = UVal::Bytes32([0x42; 32]);
    let (pre, ops) = trace(value.clone(), value);
    let inputs =
        umem_proving_inputs_from_v1(&pre, &ops).expect("the honest trace survives the value gate");
    let proof = prove_vm_descriptor2_umem(
        &inputs.descriptor,
        &inputs.rows,
        &[],
        &MemBoundaryWitness::default(),
        &[],
        &inputs.boundary,
    )
    .expect("the deployed universal-memory prover still proves the gated honest leg");
    verify_vm_descriptor2(&inputs.descriptor, &proof, &[])
        .expect("and the independent verifier still accepts it");
}
