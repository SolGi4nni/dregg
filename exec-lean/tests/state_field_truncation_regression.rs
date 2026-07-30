//! state_field_truncation_regression.rs — GUARDS the state-field truncation fix and pins the
//! FULL-WIDTH carrier that closed its residual (docs/FINDING-state-field-truncation.md; acute fix
//! `76f7a6603`, carrier widening 2026-07-30).
//!
//! # The bug the FINDING reported (CLOSED)
//!
//! A cell state field holds a full 32-byte value (`FieldElement = [u8; 32]` — e.g. an
//! execution-lease's `PROVIDER_SLOT` seeded with `cell_tag(provider)`, a full cell id). The Lean
//! state producer reconstitutes each committed cell from a `WireState` whose fields WERE u64 lanes
//! (`lean_shadow::field_to_i128` read only `bytes[24..32]`). Pre-fix, `wire_state_to_ledger` wrote
//! EVERY named field back through `i128_to_field` UNCONDITIONALLY (`out[24..32] = v; out[0..24] =
//! 0`), so any producer turn that merely RE-EMITTED a cell — a `GrantCapability{to: c}` moves `c`'s
//! `cap_root`, an `IncrementNonce` moves its nonce — shredded every full-width field it never
//! touched to its low 8 bytes, on the executing node only. The lease's 32-byte provider id became
//! `0000…d68064` and the rent rail silently stopped.
//!
//! # The residual it left (now CLOSED TOO)
//!
//! The acute fix could only FENCE the residual: a turn that GENUINELY `SetField`ed a slot to a new
//! full-width value still had no wire image, so `field_fits_wire_carrier` failed the whole turn
//! CLOSED onto the unverified Rust executor. The carrier is now the full 256 bits a `FieldElement`
//! occupies (`marshal::WideInt`), which is exactly as wide as the Lean `Int` it always crossed as —
//! so the value goes whole, and the refusal moves to the only place a value can still fail to have
//! a field image: a produced NEGATIVE `Int`.
//!
//! These are PURE `wire_state_to_ledger` reconstitution tests — no Lean FFI, so they run everywhere
//! (no `lean_available()` self-skip). The end-to-end pole (a wide `SetField` turn actually EXECUTED
//! by the verified Lean producer, with the LEAN result asserted as installed) is
//! `lean_producer_wide_field.rs`.

use std::collections::HashMap;

use dregg_cell::{Cell, CellId, Ledger};
use dregg_exec_lean::lean_apply::wire_state_to_ledger;
use dregg_lean_ffi::marshal::{WideInt, WireState, WireValue};

/// The `fields[]` slot the wire names `"target"` — the execution-lease PROVIDER slot from the
/// FINDING (`field_index_to_name(6) == "target"`).
const PROVIDER_SLOT: usize = 6;

/// The FINDING's exact 32-byte provider cell id (`934e47f2…ad7a7da327d68064`). Its high 24 bytes are
/// non-zero, so any u64-lane round-trip is OBSERVABLE as the loss of `bytes[0..24]`.
fn pinned_provider_id() -> [u8; 32] {
    [
        0x93, 0x4e, 0x47, 0xf2, 0x22, 0x21, 0x69, 0x76, 0xec, 0xab, 0xcd, 0x76, 0xf8, 0xbe, 0x42,
        0xed, 0x45, 0x9e, 0x23, 0xb1, 0x2e, 0x98, 0x8a, 0xb7, 0xad, 0x7a, 0x7d, 0xa3, 0x27, 0xd6,
        0x80, 0x64,
    ]
}

/// The wire image of a 32-byte field — now the WHOLE word (`lean_shadow::field_to_wire`).
fn wire_of(v: &[u8; 32]) -> WideInt {
    WideInt::from_be_bytes32(*v)
}

/// A one-cell template ledger whose `PROVIDER_SLOT` carries the full 32-byte provider id — exactly
/// as `starbridge-apps/execution-lease` seeds it via `st.set_field(n, cell_tag(terms.provider))`.
/// The template is the pre-state the extractor clones; it holds the intact bytes.
fn template_with_pinned_provider() -> (Ledger, CellId, HashMap<u64, CellId>) {
    let mut pk = [0u8; 32];
    pk[0] = 1;
    pk[31] = 37;
    let mut cell = Cell::with_balance(pk, [0u8; 32], 100);
    assert!(
        cell.state.set_field(PROVIDER_SLOT, pinned_provider_id()),
        "seed the full 32-byte provider id into the PROVIDER slot"
    );
    let id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();
    let inv = HashMap::from([(0u64, id)]);
    (ledger, id, inv)
}

fn reconstitute(ws: &WireState, inv: &HashMap<u64, CellId>, template: &Ledger) -> Ledger {
    wire_state_to_ledger(ws, inv, template, &[], &[], true).expect("reconstitution must succeed")
}

/// REGRESSION GUARD (fix `76f7a6603`). A 32-byte field pinned in the template SURVIVES a producer
/// turn that touches the cell (bumps its nonce) but never `SetField`s that slot.
///
/// `ledger_to_wire_state` re-emits EVERY non-zero field, so the wire record carries the `"target"`
/// value even though the field did not move. On the PRE-FIX code (`set_field(idx,
/// i128_to_field(*i))` unconditional over a low-8 lane) this assertion FAILS — the field is
/// shredded to `0000…d68064`.
#[test]
fn pinned_32byte_field_survives_a_touching_turn() {
    let (template, id, inv) = template_with_pinned_provider();
    let full = pinned_provider_id();

    // A committed turn that TOUCHES the cell (nonce 0 -> 1) but performs NO SetField on slot 6.
    let record = WireValue::Record(vec![
        ("balance".into(), WireValue::int(100)),
        ("nonce".into(), WireValue::int(1)),
        ("target".into(), WireValue::Int(wire_of(&full))),
    ]);
    let ws = WireState {
        cells: vec![(0, record)],
        ..Default::default()
    };

    let out = reconstitute(&ws, &inv, &template);
    let cell = out.get(&id).unwrap();

    assert_eq!(
        cell.state.fields[PROVIDER_SLOT], full,
        "REGRESSION (76f7a6603): a 32-byte field pinned in the template must survive a turn that \
         only bumps the nonce"
    );
    assert_eq!(
        cell.state.nonce(),
        1,
        "the turn really TOUCHED the cell (nonce moved), so the survival is non-vacuous"
    );
}

/// ⚑ THE RESIDUAL, CLOSED. A turn that GENUINELY `SetField`s slot 6 to a NEW full-width value now
/// round-trips EXACTLY — every one of the 32 bytes, not the low-8 lane.
///
/// This assertion is the inverse of the one that stood here until 2026-07-30
/// (`genuine_setfield_to_a_new_32byte_value_truncates_the_residual`, which asserted the high 24
/// bytes were ZEROED and instructed the next reader to flip it when the widening landed).
#[test]
fn a_genuine_setfield_to_a_new_32byte_value_crosses_whole() {
    let (template, id, inv) = template_with_pinned_provider();

    // A NEW 32-byte value with non-zero high bytes — the shape that had no wire image at all.
    let mut new_val = [0xEEu8; 32];
    new_val[24..32].copy_from_slice(&0x1122_3344_5566_7788u64.to_be_bytes());
    assert_ne!(
        new_val,
        pinned_provider_id(),
        "the write must be a real move"
    );

    let record = WireValue::Record(vec![
        ("balance".into(), WireValue::int(100)),
        ("nonce".into(), WireValue::int(1)),
        ("target".into(), WireValue::Int(wire_of(&new_val))),
    ]);
    let ws = WireState {
        cells: vec![(0, record)],
        ..Default::default()
    };

    let got = reconstitute(&ws, &inv, &template)
        .get(&id)
        .unwrap()
        .state
        .fields[PROVIDER_SLOT];

    assert_eq!(
        got, new_val,
        "the FULL 32 bytes of a genuinely-moved field must round-trip — this is the residual the \
         acute fix could only fence, closed by the WideInt carrier"
    );
    let mut low8_only = [0u8; 32];
    low8_only[24..32].copy_from_slice(&new_val[24..32]);
    assert_ne!(
        got, low8_only,
        "and it is NOT the old low-8 projection — a non-vacuous statement of what changed"
    );
}

/// ⚑ THE LANE-COMPARISON BLIND SPOT, closed with the same change. The acute fix compared the
/// produced LOW-8 LANE against the template's lane and skipped an "unchanged" one. A write whose
/// low 64 bits COINCIDE with a wide template's low 64 bits therefore read as unchanged — so the
/// executor's write was silently DROPPED and the old wide value kept, on the producer path where
/// the Lean verdict is authoritative. The comparison is now over the whole 32-byte word.
#[test]
fn a_low64_colliding_write_over_a_wide_template_is_not_laundered() {
    let (template, id, inv) = template_with_pinned_provider();

    // Same low 8 bytes as the template's pinned provider id; high 24 bytes CLEARED. Under the lane
    // comparison this looked identical to the template and was skipped.
    let mut narrowed = [0u8; 32];
    narrowed[24..32].copy_from_slice(&pinned_provider_id()[24..32]);
    assert_eq!(
        narrowed[24..32],
        pinned_provider_id()[24..32],
        "the fixture must actually collide on the low-8 lane"
    );
    assert_ne!(
        narrowed,
        pinned_provider_id(),
        "…while differing in the high 24 bytes — that gap is the blind spot"
    );

    let record = WireValue::Record(vec![
        ("balance".into(), WireValue::int(100)),
        ("nonce".into(), WireValue::int(1)),
        ("target".into(), WireValue::Int(wire_of(&narrowed))),
    ]);
    let ws = WireState {
        cells: vec![(0, record)],
        ..Default::default()
    };

    let got = reconstitute(&ws, &inv, &template)
        .get(&id)
        .unwrap()
        .state
        .fields[PROVIDER_SLOT];

    assert_eq!(
        got, narrowed,
        "a write that only clears the HIGH bytes must be installed — the lane comparison read it \
         as a no-op and kept the stale wide value"
    );
}

/// ⚑ THE SURVIVING REFUSAL (the other pole). A widened carrier must be lossless OR still refuse —
/// it must never start silently reinterpreting. A cell field is an UNSIGNED 256-bit word, so a
/// produced NEGATIVE `Int` has no field image: the extractor REFUSES (fencing the turn onto the
/// Rust producer) rather than installing its magnitude or two's-complement.
#[test]
fn a_produced_negative_field_value_refuses_rather_than_wrapping() {
    let (template, _id, inv) = template_with_pinned_provider();

    let record = WireValue::Record(vec![
        ("balance".into(), WireValue::int(100)),
        ("nonce".into(), WireValue::int(1)),
        ("target".into(), WireValue::int(-5i128)),
    ]);
    let ws = WireState {
        cells: vec![(0, record)],
        ..Default::default()
    };

    let err = wire_state_to_ledger(&ws, &inv, &template, &[], &[], true)
        .expect_err("a negative state-field value has no 256-bit unsigned image and must REFUSE");
    let msg = err.to_string();
    assert!(
        msg.contains("state field"),
        "the refusal must name the state field it refused, got: {msg}"
    );
}

/// The carrier is exactly as wide as the domain: 2^256 - 1 (every bit set) round-trips, which is
/// what makes the `SetField` projection TOTAL and therefore fallback-free.
#[test]
fn the_carrier_covers_the_whole_field_domain() {
    let all_ones = [0xFFu8; 32];
    let w = WideInt::from_be_bytes32(all_ones);
    assert_eq!(
        w.to_be_bytes32(),
        Some(all_ones),
        "2^256-1 must survive the carrier — the top of the field domain"
    );
    assert_eq!(
        WideInt::parse_decimal(&w.to_decimal()),
        Some(w),
        "and its DECIMAL wire form (the Lean `toString : Int → String` shape) must round-trip"
    );
    assert_eq!(
        w.to_i128(),
        None,
        "…while being far outside the i128 the old carrier used — the widening is not cosmetic"
    );
    // One past the top REFUSES rather than wrapping (the honest boundary that replaced the low-64 one).
    let two_pow_256 =
        "115792089237316195423570985008687907853269984665640564039457584007913129639936";
    assert_eq!(
        WideInt::parse_decimal(two_pow_256),
        None,
        "a magnitude >= 2^256 must be REFUSED at the wire, never truncated into the carrier"
    );
}
