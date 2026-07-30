//! # The setField ENCODER WINDOW gate — where a u64 is allowed to land in a 32-byte field value.
//!
//! The deployed `setFieldVmDescriptor2-{slot}R24` ships the freeze-ALL wrap (`v3OfFrozen
//! (setFieldTickFace slot)`): all 7 of the written slot's COMPLETION lanes are pinned BEFORE↔AFTER.
//! Combined with the lane split in [`dregg_circuit::effect_vm::field_limbs8`]
//! (`circuit/src/effect_vm/helpers.rs:133`):
//!
//! | lane | source | on a setField turn |
//! |------|--------|--------------------|
//! | 0    | `be(b[28..32]) % p` | **FREE** (the welded u64-lane lo32) |
//! | 1    | `be(b[24..28]) % p` | FROZEN (under the historical freeze-ALL wrap) |
//! | 2..7 | a Poseidon2 image over ALL 32 bytes | FROZEN (ditto) |
//!
//! ⇒ **only bytes 28..32 of a 32-byte field value are writable on a setField turn.** An encoder that
//! puts a scalar anywhere in bytes 0..28 does not "silently truncate" — it makes the turn UNSAT.
//!
//! ⚠ **BOTH HALVES OF THAT TABLE HAVE SINCE MOVED, IN OPPOSITE DIRECTIONS, AND THE FILE'S TOOTH
//! SURVIVED BOTH.** The VALUE8 epoch FREED the written slot's completion lanes (they are published
//! as PIs 46..=52, not frozen), so the prover stopped refusing wrong-lane encoders — see
//! `canonical_and_le_prefix_encodings_both_prove_but_only_one_round_trips`. And lanes 2..7 stopped
//! being `u32 % p` chunks over bytes `0..24`: they are now the leading six felts of a Poseidon2
//! image over an injective 16 × u16-LE preimage of the whole value, because the chunk form collided
//! in `O(1)`. Consequence for this file: an honest small value no longer has a zero completion
//! octet, so "the frozen lanes really are 0 after" is not the non-vacuity check any more.
//!
//! `dregg_cell::field_from_u64` is the canonical encoder and writes big-endian into 24..32, so it is
//! provable exactly for `v < 2^32` (at `v ≥ 2^32` byte 24..28 lights frozen lane 1 — that ceiling is
//! the value8 epoch's business, not this gate's). The zoo of hand-rolled `pack_u64` copies wrote
//! LITTLE-endian into bytes `0..8` — the opposite end of the value — so `pack_u64(1)` is UNSAT.
//!
//! The teeth:
//!   * `canonical_be_encoding_proves_where_le_prefix_encoding_is_unsat` — THE REPRODUCTION. The same
//!     logical value `1` proves under the canonical big-endian-into-24..32 encoding and is REFUSED
//!     under the `pack_u64`-style little-endian-into-0..8 encoding, on the real deployed descriptor.
//!   * `the_canonical_pair_round_trips_through_the_writable_window` — encode/decode is identity for
//!     every value the window admits, so moving a call site cannot lose data; and the `2^32`
//!     ceiling is pinned, so widening it must be deliberate.
//!   * `the_repaired_casualties_now_prove` — the exact values the repaired production encoders now
//!     emit (the HTTP decimal path, factory-birth, the bridge ledger, a packed board coord) each
//!     prove against the deployed descriptor.
//!   * `every_setfield_encoder_writes_inside_the_u64_lane` — the TOOTH, and it is TYPE-directed
//!     rather than name-directed: it walks the tree for functions that take a `u64`/`i64` and
//!     return a 32-byte field element, and fails any that write below byte 24. A new encoder is
//!     caught by its SHAPE whatever it is named; landing one means using the canonical pair or
//!     registering it in `REGISTERED_NON_SETFIELD_ENCODERS` with the reason its value never
//!     reaches a `fields[]` slot (the HEAP codecs are registered there — `set_field_ext` rides a
//!     different descriptor and is NOT completion-frozen).

use dregg_cell::{Cell, Ledger, field_from_u64};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::{
    AFTER_BASE, empty_caveat_manifest, generate_rotated_effect_vm_trace,
    rotated_descriptor_name_for_effect,
};
use dregg_circuit::effect_vm::{CellState, Effect, fold_bytes32_to_bb};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::refusal::{Outcome, classify};
use dregg_turn::rotation_witness as rw;

/// The written slot under test.
const SLOT: usize = 3;
/// The written slot's 7 frozen completion lanes, first pre-limb offset (`113 + 7·slot`).
/// The authority for the base is `cell/src/commitment.rs` (the REVOKED-ROOT flag-day shifted the
/// `fields[0..7]` completion octet `112..=167 → 113..=168`).
const COMPLETION_BASE: usize = 113 + 7 * SLOT;

fn rotated_descriptor_json(name: &str) -> &'static str {
    V3_STAGED_REGISTRY_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some(name) {
                let _ = it.next();
                it.next()
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("{name} not in the deployed V3 staged registry"))
}

fn producer_cell(balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    Cell::with_balance(pk, [0u8; 32], balance)
}

fn bridge(w: &rw::RotationWitness) -> dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness {
    dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot)
        .expect("pre-iroot limbs")
}

struct Built {
    trace: Vec<Vec<BabyBear>>,
    dpis: Vec<BabyBear>,
    desc: dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
}

/// Build an honest single-effect `setField(SLOT, field_bytes)` against the DEPLOYED descriptor.
/// The only thing that varies between the teeth is WHERE in `field_bytes` the scalar was written.
fn build_setfield(field_bytes: [u8; 32]) -> Built {
    let before: i64 = 50_000;
    let value = fold_bytes32_to_bb(&field_bytes);
    let effect = Effect::SetField {
        field_idx: SLOT as u32,
        value,
    };
    let name = rotated_descriptor_name_for_effect(&effect).expect("setField is a cohort member");
    assert_eq!(
        name, "setFieldVmDescriptor2-3R24",
        "this gate must exercise the DEPLOYED setField member, not a staged twin"
    );
    let desc = parse_vm_descriptor2(rotated_descriptor_json(name)).expect("descriptor parses");

    let mut after_cell = producer_cell(before);
    assert!(after_cell.state.set_field(SLOT, field_bytes), "set_field");

    let st = CellState::new(before as u64, 0);
    let effects = vec![effect];
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let z8 = dregg_circuit::heap_root::empty_heap_root_8();
    let rvk = rw::empty_revoked_root_8();
    let rlog: Vec<[u8; 32]> = vec![[3u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &z8,
        &z8,
        &rvk,
        &rlog,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &z8,
        &z8,
        &rvk,
        &rlog,
        &Default::default(),
    );
    let (trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &empty_caveat_manifest(),
    )
    .expect("live rotated generator must produce a setField trace + PIs");
    Built { trace, dpis, desc }
}

/// Prove+verify through the real prover. `true` = ACCEPTED.
fn accepts(b: &Built) -> bool {
    match classify("setfield-encoder-window", || {
        let proof = prove_vm_descriptor2(
            &b.desc,
            &b.trace,
            &b.dpis,
            &MemBoundaryWitness::default(),
            &[],
        )?;
        verify_vm_descriptor2(&b.desc, &proof, &b.dpis)
    }) {
        // The p3 debug prover's DOCUMENTED unsat verdict, and any hard error, are refusals.
        Outcome::UnsatPanic(_) | Outcome::Err(_) => false,
        Outcome::Accepted(_) => true,
    }
}

/// How the hand-rolled `pack_u64` zoo encoded a scalar: LITTLE-endian into bytes `0..8`.
/// Reproduced here (not imported) precisely because the point of this gate is that NO shipping
/// crate may contain this shape any more — see `every_setfield_encoder_writes_inside_the_u64_lane`,
/// which is why this file is the one path that walk skips.
fn le_prefix_encoding(v: u64) -> [u8; 32] {
    let mut fe = [0u8; 32];
    fe[..8].copy_from_slice(&v.to_le_bytes());
    fe
}

/// **⚑ CONVERTED BY THE VALUE8 EPOCH, AND IT COST THIS FILE A DETECTOR.** This was
/// `canonical_be_encoding_proves_where_le_prefix_encoding_is_unsat`, and its (b) half asserted that a
/// `pack_u64`-style LITTLE-endian-into-`0..8` encoding was **UNSAT** — because the deployed
/// freeze-ALL wrap pinned the written slot's completion lanes, so lighting one made the turn
/// unprovable. That is how the LE-prefix encoder zoo was originally caught: the PROVER was
/// accidentally acting as a lane-discipline gate.
///
/// The deployed member is now freeze-EXCEPT + the 7 published completion pins, so the whole 32-byte
/// value is writable and the LE-prefix encoding **PROVES**. Say it plainly: **the prover no longer
/// refuses an encoder that writes on the wrong lane.** It is now purely a codec bug — `pack_u64`
/// LE-into-`0..8` paired with `unpack_u64` BE-from-`24..32` still reads back garbage — and the only
/// remaining detectors are the round-trip tooth
/// (`the_canonical_pair_round_trips_through_the_writable_window`) and the type-directed walk
/// (`every_setfield_encoder_writes_inside_the_u64_lane`), which is therefore now LOAD-BEARING rather
/// than belt-and-suspenders.
#[test]
fn canonical_and_le_prefix_encodings_both_prove_but_only_one_round_trips() {
    // The SAME logical value, encoded two ways.
    const V: u64 = 1;

    // ---- (a) the canonical encoder: big-endian into 24..32, so `1` lands in byte 31 = free lane 0.
    let canon = field_from_u64(V);
    assert_eq!(canon[31], 1, "canonical encoding puts the low byte at 31");
    assert!(
        canon[..28].iter().all(|&b| b == 0),
        "canonical encoding of a small value must leave the frozen prefix 0..28 clear"
    );
    let good = build_setfield(canon);
    // ⚑ THIS CHECK USED TO BE "every written-slot completion lane is 0 after". That was true only
    // while lanes 2..7 were `u32 % p` chunks over the (all-zero) bytes `0..24` — the O(1)-aliasable
    // shape. They are a Poseidon2 image over the whole value now, so the canonical small write
    // lights all seven, and what the generator must get right is that they are the HONEST octet.
    let canon8 = dregg_circuit::effect_vm::field_limbs8(&canon);
    for row in &good.trace {
        for k in 0..7 {
            assert_eq!(
                row[AFTER_BASE + COMPLETION_BASE + k],
                canon8[1 + k],
                "canonical small value: written-slot completion lane {k} must be the honest \
                 field_limbs8 lane {}",
                1 + k
            );
        }
    }
    assert!(
        accepts(&good),
        "BASELINE BROKEN: the canonical big-endian setField({V}) must prove against the deployed \
         descriptor. If this fails the fixture is wrong, not the encoder."
    );

    // ---- (b) the `pack_u64` zoo's encoding: little-endian into 0..8, so `1` lands in byte 0 = a
    //          HIGH completion lane. Under the VALUE8 epoch this is a perfectly provable 32-byte
    //          write: the lane is FREED and PUBLISHED (PIs 46..=52), not frozen.
    let le = le_prefix_encoding(V);
    assert_eq!(le[0], 1, "LE-prefix encoding puts the low byte at 0");
    let bad = build_setfield(le);
    // Non-vacuity. "≥1 completion lane is off zero" is satisfied by EVERY value now, so it is a
    // check that cannot go red. The discriminating property is that the two encodings of the SAME
    // logical value land on DIFFERENT lanes: identical lane 0 would mean the LE write reached the
    // u64 window, and an identical completion octet would mean it reached nothing at all.
    let le8 = dregg_circuit::effect_vm::field_limbs8(&le);
    assert_ne!(
        le8[0], canon8[0],
        "the LE-prefix encoding must NOT land in the u64 lane — that is the bug it exhibits"
    );
    assert!(
        (1..8).any(|k| le8[k] != canon8[k]),
        "the LE-prefix encoding must reach the completion octet (else this tooth proves nothing)"
    );
    for k in 0..7 {
        assert_eq!(
            bad.trace[0][AFTER_BASE + COMPLETION_BASE + k],
            le8[1 + k],
            "the generator must publish the LE-prefix value's honest completion lane {k}"
        );
    }
    assert!(
        accepts(&bad),
        "the VALUE8 epoch makes the WHOLE 32-byte value writable, so a high-lane encoding must \
         PROVE. If this is refused, the deployed member reverted to freeze-ALL."
    );

    // ⚑ AND THIS IS WHY THE PROVER IS NO LONGER THE GATE: both encodings prove, but only the
    // canonical one round-trips. `unpack_u64`/`field_to_u64` reads BE from `24..32`, so the
    // LE-prefix write reads back as a different number — silently, at every call site.
    assert_eq!(
        dregg_cell::field_to_u64(&canon),
        V,
        "the canonical pair round-trips"
    );
    assert_ne!(
        dregg_cell::field_to_u64(&le),
        V,
        "the LE-prefix write does NOT round-trip through the canonical decoder — still a bug, just \
         no longer one the prover refuses"
    );

    eprintln!(
        "VALUE8: setField({V}) proves under BOTH canonical BE→24..32 and pack_u64-style LE→0..8; \
         only the canonical pair round-trips. The lane gate is now STATIC, not proof-enforced."
    );
}

#[test]
fn the_canonical_pair_round_trips_through_the_writable_window() {
    // Every value the window admits must survive encode→decode, so rewiring a call site from the
    // LE-prefix pair to the canonical pair cannot lose data.
    for v in [
        0u64,
        1,
        2,
        0xC0,
        1_000,
        0xFFFF,
        0x1234_5678,
        u32::MAX as u64,
    ] {
        let f = field_from_u64(v);
        assert!(
            f[..28].iter().all(|&b| b == 0),
            "field_from_u64({v}) must write only inside the writable window 28..32"
        );
        assert_eq!(
            dregg_cell::field_to_u64(&f),
            v,
            "canonical encode/decode must round-trip {v}"
        );
    }
    // At 2^32 the canonical encoder reaches byte 24..28 = completion lane 1. Under the VALUE8 epoch
    // that lane is writable and PUBLISHED, so this is no longer a PROVABILITY ceiling — only a
    // statement about where `field_from_u64` puts its bytes. Pinned so a layout move is deliberate.
    let over = field_from_u64(1u64 << 32);
    assert!(
        over[..28].iter().any(|&b| b != 0),
        "at 2^32 the canonical encoder necessarily leaves the low lane (VALUE8 publishes it)"
    );
    assert_eq!(
        dregg_cell::field_to_u64(&over),
        1u64 << 32,
        "and it still round-trips — the u64 lane is bytes 24..32, both halves"
    );
}

#[test]
fn the_repaired_casualties_now_prove() {
    // Each case is the value a REPAIRED production encoder now emits. `field_from_u64` here is the
    // REAL `dregg_cell` function those sites call, not a copy — so proving it proves their lane.
    let cases: [(&str, [u8; 32]); 4] = [
        (
            // node/src/api.rs::parse_field_element — `{"kind":"set_field","value":"42"}`.
            "http decimal path: value=\"42\"",
            field_from_u64(42),
        ),
        (
            // turn/src/executor/apply.rs — factory-birth `initial_fields` lowering.
            "factory-birth initial_fields: (slot, 7)",
            field_from_u64(7),
        ),
        (
            // turn/src/executor/bridge_ledger.rs::encode_u64 — a committed supply quantity.
            "bridge-ledger supply: 50_000",
            field_from_u64(50_000),
        ),
        (
            // starbridge-web-surface/src/game.rs::pack_coord — `0x00C0_RRCC` in the low lane.
            // Shape-only (that crate is a separate workspace circuit cannot import); the
            // source-walk tooth is what pins the real site to this lane.
            "starbridge packed coord (row 3, col 4)",
            field_from_u64(0x00C0_0304),
        ),
    ];
    for (what, bytes) in cases {
        assert!(
            bytes[..28].iter().all(|&b| b == 0),
            "{what}: the repaired encoding must sit inside the writable window"
        );
        let b = build_setfield(bytes);
        assert!(
            accepts(&b),
            "{what}: the REPAIRED encoding must prove against the deployed setField descriptor"
        );
        eprintln!("CASUALTY CLEARED: {what} proves.");
    }
}

// ─────────────────────────────────────────────────────────────────────────────────────────────
// THE TOOTH: every field-element encoder in the tree writes inside the u64 lane.
//
// The rule it enforces is TYPE-DIRECTED, not name-directed: a function whose return type is a
// 32-byte field element and which writes a SCALAR into the value it returns may only write the
// u64 lane (bytes `24..32`). Anything below byte 24 lands in a lane the deployed setField
// descriptor freezes.
//
// A new hand-rolled encoder is therefore caught by its SHAPE, not by being named `pack_u64` — so
// it cannot slip in under a new name. To land one you must either use the canonical pair or add a
// row to [`REGISTERED_NON_SETFIELD_ENCODERS`] saying why the value never reaches a `fields[]`
// slot. That is the decision this test forces.
// ─────────────────────────────────────────────────────────────────────────────────────────────

/// Functions that build a 32-byte buffer with a sub-24 scalar write but are NOT setField value
/// encoders. Each row must say WHY the value never lands in a cell `fields[]` slot.
///
/// WILDCARD-FREE: matched on exact `path::function`, so a rename or a new encoder fails the gate.
const REGISTERED_NON_SETFIELD_ENCODERS: &[(&str, &str, &str)] = &[
    (
        "cell/src/blueprint.rs",
        "dkg_params_field",
        "packs TWO u64s (`n` at bytes 8..16, `t` at 24..32), so it CANNOT fit the u64 lane. ⚑ THE \
         VALUE8 EPOCH CLOSED THE PROVABILITY HALF OF THIS ROW: the deployed setField member no \
         longer freezes the written slot's high lanes (it publishes them as PIs 46..=52), so this \
         write PROVES now — the row used to end 'closing it is value8-epoch work' and that work is \
         done. It stays registered because the residual is REAL and different: `dkg_params_field` \
         has no `field_to_u64` inverse, so it is a bespoke two-u64 codec that the canonical pair \
         cannot round-trip. It IS a written setField value (node/src/dkg_service.rs:641, the live \
         `dkg_open` route); the two INCIDENTAL wiring properties that used to keep it off the \
         prover (`run_signed_turn` never enqueues the prove pool; the write is CROSS-CELL and \
         `sdk/src/cipherclerk.rs:6868` drops it from the actor projection) are no longer \
         load-bearing for provability.",
    ),
    (
        "bridge/src/mina_observer.rs",
        "mock_fe",
        "⚠ RED AT HEAD BEFORE THIS EPOCH, NOT CAUSED BY IT — `mock_fe` landed 2026-07-29 \
         (`7fd896f22`) and this gate has been failing on it since. It builds a PASTA field element \
         for the Mina observer's test fixtures (little-endian scalar + a `< 2^254` clamp byte); it \
         is a foreign-curve scalar and never reaches a cell `fields[]` slot, so it is registered \
         rather than rewritten. The type-directed walk caught it by SHAPE, which is the walk \
         working — and now that the prover no longer refuses wrong-lane writes, that walk is the \
         only detector left, so it must be green to be useful.",
    ),
    (
        "cell/src/state.rs",
        "encode_i64",
        "the HEAP value codec (`set_field_ext`, key >= STATE_SLOTS — the openable sorted-map \
         spine), not the fixed fields octet. Heap values ride a different descriptor and are NOT \
         completion-frozen. Paired with `decode_i64` in the same file.",
    ),
    (
        "cell/src/derived.rs",
        "encode_value_into_field",
        "heap value codec (see cell/src/state.rs::encode_i64), paired with decode_value_from_field.",
    ),
    (
        "cell/src/escrow_sealed.rs",
        "encode_i64",
        "heap value codec (see cell/src/state.rs::encode_i64), paired with decode_i64.",
    ),
    (
        "cell/src/obligation_standing.rs",
        "encode_i64",
        "heap value codec (see cell/src/state.rs::encode_i64), paired with decode_i64.",
    ),
    (
        "cell/src/prepaid_lease.rs",
        "encode_i64",
        "heap value codec (see cell/src/state.rs::encode_i64), paired with decode_i64.",
    ),
    (
        "cell/src/vault.rs",
        "encode_i64",
        "heap value codec (see cell/src/state.rs::encode_i64), paired with decode_i64.",
    ),
    (
        "entity-compose/src/lib.rs",
        "u64_to_fe",
        "the WIDE-PLANE (heap) codec: installed via `set_field_ext` and read via \
         `fields_root_membership`, never a fixed `fields[0..7]` slot. Paired with read_u64_fe.",
    ),
    (
        "entity-compose/src/lib.rs",
        "param_to_fe",
        "wide-plane (heap) codec, two's-complement — see u64_to_fe above. Paired with read_i64_fe.",
    ),
    (
        "eth-lightclient/src/ssz.rs",
        "htr_u64",
        "an SSZ `hash_tree_root` chunk, not a cell field. The SSZ spec MANDATES little-endian \
         right-padded serialization; moving it would break Ethereum consensus-root agreement.",
    ),
    (
        "coord/src/coord_diff.rs",
        "h",
        "a `mod tests` digest helper minting synthetic 32-byte DAG node ids, not a field value.",
    ),
    (
        "pg-dregg/src/turn_proofs.rs",
        "root",
        "a `mod tests` helper minting a synthetic 32-byte ROOT (a digest), not a field value.",
    ),
    (
        "pg-dregg/src/workflow.rs",
        "ledger_root",
        "a `mod tests` helper minting a synthetic 32-byte ledger ROOT (a digest), not a field value.",
    ),
    (
        "deos-view/src/mount.rs",
        "len_header",
        "a `mod tests` blob LENGTH header for the mount codec's own framing, not a cell field \
         value; the mount reader parses the same low-8 framing.",
    ),
    (
        "cell/tests/zzz_apply_delta_bench.rs",
        "pk",
        "a bench helper minting a synthetic 32-byte PUBKEY, not a field value.",
    ),
];

/// A 32-byte field element return type, in the spellings the tree actually uses.
fn returns_field_element(sig: &str) -> bool {
    for pat in [
        "-> FieldElement",
        "-> [u8; 32]",
        "-> dregg_cell::state::FieldElement",
        "-> dregg_cell::FieldElement",
        "-> state::FieldElement",
    ] {
        if sig.contains(pat) {
            return true;
        }
    }
    // `Result<[u8; 32], _>` / `Result<FieldElement, _>` — the HTTP ingress shape.
    sig.contains("-> Result<[u8; 32]") || sig.contains("-> Result<FieldElement")
}

/// Does the signature take a `u64`/`i64` SCALAR parameter?
///
/// This is the discriminator that makes the gate precise. `[u8; 32]` is an overloaded type in this
/// tree — it is both a cell field VALUE and a digest/commitment — so "returns 32 bytes and writes
/// a scalar low" alone flags every `felt_to_bytes32` / `bb_to_bytes` / hash-preimage builder.
/// A field-VALUE encoder is the one that takes an integer and places it in the value; a digest
/// converter takes a felt, a hash, or a byte slice. Requiring a `u64`/`i64` parameter separates
/// them without a name allowlist, so a new encoder is caught by shape whatever it is called.
fn takes_u64_scalar(sig: &str) -> bool {
    let Some(args) = sig.split_once('(').map(|(_, a)| a) else {
        return false;
    };
    let args = args.split_once("->").map(|(a, _)| a).unwrap_or(args);
    for ty in [": u64", ": i64", ":u64", ":i64"] {
        if args.contains(ty) {
            return true;
        }
    }
    false
}

/// The byte offset a write targets, if the line writes into an indexed buffer.
/// `None` when the line is not an indexed write.
fn write_offset(line: &str) -> Option<usize> {
    let l = line.trim();
    // `buf[a..b].copy_from_slice(` / `buf[..b].copy_from_slice(`
    if let Some(open) = l.find('[') {
        let rest = &l[open + 1..];
        if let Some(close) = rest.find(']') {
            let idx = &rest[..close];
            let after = rest[close + 1..].trim_start();
            let is_write = after.starts_with(".copy_from_slice(")
                || after.starts_with('=') && !after.starts_with("==");
            if !is_write {
                return None;
            }
            if let Some(dots) = idx.find("..") {
                let lo = idx[..dots].trim();
                return Some(if lo.is_empty() { 0 } else { lo.parse().ok()? });
            }
            return idx.trim().parse().ok();
        }
    }
    None
}

fn walk_rs(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
    let Ok(rd) = std::fs::read_dir(dir) else {
        return;
    };
    for e in rd.flatten() {
        let p = e.path();
        let name = e.file_name();
        let name = name.to_string_lossy();
        if p.is_dir() {
            // Skip build products, vendored trees, and every HIDDEN directory — `.claude/worktrees/`
            // holds sibling agents' full checkouts of this same repo, and scanning them makes this
            // gate report another worktree's staleness as this tree's offence.
            if name.starts_with('.')
                || matches!(
                    name.as_ref(),
                    "target" | "node_modules" | "vendor" | "dist" | "build"
                )
            {
                continue;
            }
            walk_rs(&p, out);
        } else if name.ends_with(".rs") {
            out.push(p);
        }
    }
}

/// The lowest byte a setField value encoder may write: the u64 lane starts at 24.
const U64_LANE_START: usize = 24;

#[test]
fn every_setfield_encoder_writes_inside_the_u64_lane() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("workspace root")
        .to_path_buf();
    let mut files = Vec::new();
    walk_rs(&root, &mut files);
    // NON-VACUITY: if the walk stops reaching the tree this gate silently passes forever.
    assert!(
        files.len() > 500,
        "the source walk found only {} .rs files — it is not reaching the tree, so this gate \
         cannot go red",
        files.len()
    );

    let mut scanned_encoders = 0usize;
    let mut offenders: Vec<String> = Vec::new();

    for f in &files {
        let rel = f
            .strip_prefix(&root)
            .unwrap_or(f)
            .to_string_lossy()
            .replace('\\', "/");
        // This gate's own `le_prefix_encoding` fixture is the counterexample the repro needs.
        if rel == "circuit/tests/setfield_encoder_window_gate.rs" {
            continue;
        }
        let Ok(src) = std::fs::read_to_string(f) else {
            continue;
        };
        if !src.contains("32]") && !src.contains("FieldElement") {
            continue;
        }

        let lines: Vec<&str> = src.lines().collect();
        let mut i = 0usize;
        while i < lines.len() {
            let sig = lines[i];
            let t = sig.trim_start();
            if !(t.starts_with("fn ")
                || t.starts_with("pub fn ")
                || t.starts_with("pub(crate) fn "))
            {
                i += 1;
                continue;
            }
            // Take the signature (possibly wrapped) up to the opening brace.
            let mut sig_buf = String::new();
            let mut j = i;
            while j < lines.len() && j < i + 6 {
                sig_buf.push_str(lines[j]);
                if lines[j].contains('{') {
                    break;
                }
                j += 1;
            }
            if !(returns_field_element(&sig_buf) && takes_u64_scalar(&sig_buf)) {
                i += 1;
                continue;
            }
            let name = sig_buf
                .split("fn ")
                .nth(1)
                .and_then(|s| s.split(['(', '<']).next())
                .unwrap_or("?")
                .trim()
                .to_string();

            // Brace-match the body.
            let mut depth = 0i32;
            let mut body: Vec<(usize, &str)> = Vec::new();
            let mut k = j;
            let mut started = false;
            while k < lines.len() {
                for c in lines[k].chars() {
                    if c == '{' {
                        depth += 1;
                        started = true;
                    } else if c == '}' {
                        depth -= 1;
                    }
                }
                if started && k > j {
                    body.push((k + 1, lines[k]));
                }
                if started && depth <= 0 {
                    break;
                }
                k += 1;
            }
            scanned_encoders += 1;

            let registered = REGISTERED_NON_SETFIELD_ENCODERS
                .iter()
                .any(|(p, fname, _)| *p == rel && *fname == name);

            if !registered {
                for (lineno, l) in &body {
                    let lt = l.trim();
                    if lt.starts_with("//") || lt.starts_with("/*") || lt.starts_with('*') {
                        continue;
                    }
                    // Only a SCALAR encoding is in scope: copying a 32-byte digest through, or
                    // hashing, is not a u64 value encoding.
                    if !(lt.contains("to_le_bytes()") || lt.contains("to_be_bytes()")) {
                        continue;
                    }
                    if let Some(off) = write_offset(lt) {
                        if off < U64_LANE_START {
                            offenders.push(format!("{rel}:{lineno} fn {name}: {lt}"));
                        }
                    }
                }
            }
            i = k.max(i + 1);
        }
    }

    // NON-VACUITY: the scan must actually be finding encoders to inspect.
    assert!(
        scanned_encoders >= 20,
        "the scan classified only {scanned_encoders} u64->field-element encoders — the signature \
         matcher has drifted and this gate cannot go red"
    );

    assert!(
        offenders.is_empty(),
        "{} field-element encoder(s) write BELOW byte {U64_LANE_START}. A cell `fields[]` slot is \
         definitionally a u64 lane (big-endian bytes 24..32), and the paired decoder \
         (`field_to_u64`) reads exactly that lane — so a scalar placed below byte 24 reads back as \
         a DIFFERENT NUMBER. ⚑ This gate is now the ONLY detector: before the setField VALUE8 epoch \
         the deployed `setFieldVmDescriptor2-*R24` FROZE the written slot's completion lanes, so a \
         low-byte write could not prove at all and the prover caught the whole class for free. The \
         lanes are freed and published now; a wrong-lane encoder proves happily and corrupts \
         silently. Use `dregg_cell::field_from_u64` / `dregg_cell::field_to_u64` (and move the \
         paired DECODER with it), or add a row to REGISTERED_NON_SETFIELD_ENCODERS explaining why \
         this value never reaches a `fields[]` slot:\n  {}",
        offenders.len(),
        offenders.join("\n  ")
    );
    eprintln!(
        "TOOTH: {scanned_encoders} field-element-returning functions scanned; every scalar write \
         is inside the u64 lane (bytes {U64_LANE_START}..32)."
    );
}
