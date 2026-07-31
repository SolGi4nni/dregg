//! # R1 FORGE PROBE — the setField written-slot VALUE8 completion-lane seam (audit §6 R1 / S1).
//!
//! The TRUST-BASE-CENSUS §6 R1 claims a LIVE ledgerless soundness gap: on a `setField(idx<8)` WRITE
//! turn the written field's completion lanes 1..7 (the high 224 bits of the 32-byte value) are
//! EXCEPTED from the freeze (`v3OfFrozenSetField` / `fieldsCompletionFreezesExcept slot`) AND not
//! forced to the declared value — so a ledgerless `verify_vm_descriptor2` client would accept an
//! arbitrary high-224-bit field value.
//!
//! THIS PROBE ATTACKS THAT CLAIM against the ACTUAL DEPLOYED descriptor
//! (`setFieldVmDescriptor2-{slot}R24` in `V3_STAGED_REGISTRY_TSV`).
//!
//! ⚑ THE VERDICT SURVIVED THE VALUE8 EPOCH BUT THE GATE THAT DELIVERS IT CHANGED. The deployed
//! member USED to be `withSelectorGate SEL_SET_FIELD (v3OfFrozen (setFieldTickFace slot))` —
//! freeze-ALL, all 56 completion lanes pinned BEFORE↔AFTER. That refused the census R1 forge, but it
//! ALSO refused every honest 32-byte write whose value had a nonzero byte outside `28..32`. The Lean
//! `v3RegistryBare` now emits `withSetFieldCompletionPins slot (withSelectorGate SEL_SET_FIELD
//! (setFieldV3 slot))` — freeze-EXCEPT (the written slot's 7 lanes are FREED) plus 7 `.piBinding
//! .last` PINS publishing exactly those lanes as PIs 46..=52. The high 224 bits are now bound BY
//! PUBLICATION rather than by being frozen shut: the light client reads them, and a lane moved off
//! its published PI has no satisfying assignment.
//!
//! Three teeth:
//!   * `honest_small_value_setfield_proves_and_verifies` — a lane-0-only value proves + verifies.
//!   * `honest_large_value_setfield_proves_on_the_deployed_member` — ⚑ CONVERTED (see its doc): it
//!     used to assert the REFUSAL, and its whole job was to document the wound.
//!   * `forged_written_slot_completion_lanes_is_unsat` — a forge that sets the written slot's
//!     completion lanes 1..7 to arbitrary nonzero (≠ the honest/pre-state 0) while keeping lane 0
//!     honest, recomputes the downstream commitment so NEW_COMMIT genuinely absorbs the forged high
//!     bytes (the wire view), and patches the post-state dpis — is UNSAT through prove/verify ALONE.
//!     If it ACCEPTS, the census R1 forge is LIVE.

use dregg_cell::{Cell, Ledger};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::{
    AFTER_BASE, B_CHAIN_BASE, B_IROOT, B_STATE_COMMIT, NUM_PRE_LIMBS, V1_PI_COUNT,
    empty_caveat_manifest, generate_rotated_effect_vm_trace, rotated_descriptor_name_for_effect,
};
use dregg_circuit::effect_vm::{CellState, Effect, fold_bytes32_to_bb};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_many;
use dregg_circuit::refusal::{Outcome, classify};
use dregg_turn::rotation_witness as rw;

/// The written slot under test.
const SLOT: usize = 3;
/// The first completion-lane pre-limb offset for `SLOT` (lanes 1..7 → `113 + 7·slot .. +6`).
///
/// ⚠ WAS `112 + 7·slot`, one limb LOW. The REVOKED-ROOT flag-day shifted the
/// `fields[0..7]` completion octet `112..=167 → 113..=168` (`cell/src/commitment.rs:1144`
/// is the authority; `setfield_value8_epoch_flip.rs:43` already used the correct base).
/// At `SLOT = 3` the stale constant aimed the forge at `fields[2]` lane 7 plus `fields[3]`
/// lanes 1..6 — every one of which the deployed freeze-ALL member also pins, so the UNSAT
/// verdict was right by accident. This test is the pin on the thing that RESCUES the
/// deployed SetField from the census R1 silent-forge; a rescue-pin aimed one lane off its
/// stated target is not a pin.
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
        .unwrap_or_else(|| panic!("{name} not in V3_STAGED_REGISTRY_TSV"))
}

fn producer_cell(balance: i64, nonce: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn bridge(w: &rw::RotationWitness) -> dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness {
    dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot)
        .expect("pre-iroot limbs")
}

/// Re-run the AFTER block's chained absorption on one row so `B_STATE_COMMIT` reflects the row's
/// current pre-limbs (incl. any forged completion lanes). Byte-identical to `fill_block`.
fn recompute_after_chain(row: &mut [BabyBear]) {
    let base = AFTER_BASE;
    let mut d = hash_many(&[row[base], row[base + 1], row[base + 2], row[base + 3]]);
    let mut chain = 0usize;
    row[base + B_CHAIN_BASE + chain] = d;
    chain += 1;
    let mut col = 4usize;
    while col < NUM_PRE_LIMBS {
        let remaining = NUM_PRE_LIMBS - col;
        if remaining >= 3 {
            d = hash_many(&[d, row[base + col], row[base + col + 1], row[base + col + 2]]);
            col += 3;
        } else {
            d = hash_many(&[d, row[base + col]]);
            col += 1;
        }
        row[base + B_CHAIN_BASE + chain] = d;
        chain += 1;
    }
    row[base + B_STATE_COMMIT] = hash_many(&[d, row[base + B_IROOT]]);
}

struct Honest {
    desc: dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    trace: Vec<Vec<BabyBear>>,
    dpis: Vec<BabyBear>,
    mem_boundary: MemBoundaryWitness,
    map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>>,
}

/// Build an honest single-effect setField trace whose written value sits entirely inside the kernel
/// u64 lane (bytes `28..32`) — the smallest honest write there is.
///
/// ⚑ Its completion lanes are NOT zero any more. They used to be, because `field_limbs8` lanes 2..7
/// were `u32 % p` chunks over the (all-zero) bytes `0..24`; they now carry a Poseidon2 image over
/// the whole 32-byte value, so an honest small write moves all seven freed lanes off zero. The
/// deployed member frees and PUBLISHES exactly those lanes (PIs 46..=52), so this is provable —
/// which is what `honest_small_value_setfield_proves_and_verifies` measures.
fn build_honest_small() -> (Honest, BabyBear) {
    let before: i64 = 50_000;
    let mut field_bytes = [0u8; 32];
    field_bytes[28..32].copy_from_slice(&1_000u32.to_be_bytes());
    let new_value = fold_bytes32_to_bb(&field_bytes);

    let effect = Effect::SetField {
        field_idx: SLOT as u32,
        value: new_value,
    };
    let name = rotated_descriptor_name_for_effect(&effect).expect("setField is a cohort member");
    assert_eq!(name, "setFieldVmDescriptor2-3R24");
    let desc = parse_vm_descriptor2(rotated_descriptor_json(name)).expect("descriptor parses");

    let mut after_cell = producer_cell(before, 0);
    assert!(after_cell.state.set_field(SLOT, field_bytes), "set_field");

    let st = CellState::new(before as u64, 0);
    let effects = vec![effect];
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before, 0);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let caveat = empty_caveat_manifest();
    let (trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("live rotated generator must produce a setField trace + PIs");

    (
        Honest {
            desc,
            trace,
            dpis,
            mem_boundary: MemBoundaryWitness::default(),
            map_heaps: vec![],
        },
        new_value,
    )
}

fn refused(h: &Honest, trace: &[Vec<BabyBear>], dpis: &[BabyBear]) -> bool {
    match classify("refused", || {
        let proof = prove_vm_descriptor2(&h.desc, trace, dpis, &h.mem_boundary, &h.map_heaps)?;
        verify_vm_descriptor2(&h.desc, &proof, dpis)
    }) {
        // The p3 debug prover's DOCUMENTED unsat verdict — a real refusal.
        // `classify` REDs on any other panic (a stray unwrap, a trace-assembly
        // debug_assert), which used to land here and read as "rejected".
        Outcome::UnsatPanic(_) => true,
        Outcome::Err(_) => true,
        Outcome::Accepted(_) => false,
    }
}

/// ⚑ **THE SELF-CHECK WAS INVERTED HERE AND THAT IS THE WHOLE MEASUREMENT.** It read
/// "written-slot completion lane {k} must be zero" on every row, which held only while
/// `field_limbs8` lanes 2..7 were `u32 % p` chunks over bytes `0..24` — the shape that collided in
/// `O(1)` on the one octet with no byte-exact companion. Those lanes are a hash of the whole value
/// now, so an honest SMALL write lights all seven, and the question this test answers changed with
/// them: not "does a zero completion octet prove" but **"does a NONZERO one"**.
///
/// It must, because the deployed member frees the written slot's lanes and publishes them as PIs
/// 46..=52 (`withSetFieldCompletionPins`). If this ever refuses, the freeze-ALL wrap is back and the
/// encoding change made honest field writes unprovable — which is the specific failure the fields
/// octet repair had to avoid.
#[test]
fn honest_small_value_setfield_proves_and_verifies() {
    let (h, _v) = build_honest_small();

    // The honest value8 the producer projected, recomputed from the encoder.
    let mut field_bytes = [0u8; 32];
    field_bytes[28..32].copy_from_slice(&1_000u32.to_be_bytes());
    let honest = dregg_circuit::effect_vm::field_limbs8(&field_bytes);

    // Self-check: every row's written-slot completion lanes carry EXACTLY the honest lanes 1..7.
    for (r, row) in h.trace.iter().enumerate() {
        for k in 0..7 {
            assert_eq!(
                row[AFTER_BASE + COMPLETION_BASE + k],
                honest[1 + k],
                "row {r}: written-slot completion lane {k} must be the honest field_limbs8 lane \
                 {}",
                1 + k
            );
        }
    }
    // NON-VACUITY: a zero octet would make this test the OLD one wearing a new assertion.
    assert!(
        (0..7).any(|k| h.trace[0][AFTER_BASE + COMPLETION_BASE + k] != BabyBear::ZERO),
        "the honest small-value completion octet must be NONZERO — if every lane is zero, the \
         `u32 % p` chunk encoding is back and this test proves nothing about the repair"
    );

    let proof = prove_vm_descriptor2(&h.desc, &h.trace, &h.dpis, &h.mem_boundary, &h.map_heaps)
        .expect("HONEST small-value setField must prove against the deployed descriptor");
    verify_vm_descriptor2(&h.desc, &proof, &h.dpis)
        .expect("HONEST small-value setField proof must verify");
    eprintln!(
        "R1 PROBE: honest small-value setField proves+verifies on the deployed descriptor with a \
         NONZERO published completion octet."
    );
}

/// Build an honest single-effect setField whose written value has NONZERO high bytes (so the
/// deployed completion freeze `before(0) == after(≠0)` is VIOLATED — the completeness seam).
fn build_honest_large() -> Honest {
    let before: i64 = 50_000;
    let mut field_bytes = [0u8; 32];
    field_bytes[0] = 0xAB; // a high byte → nonzero completion lane
    field_bytes[1] = 0xCD;
    field_bytes[28..32].copy_from_slice(&1_000u32.to_be_bytes());
    let new_value = fold_bytes32_to_bb(&field_bytes);
    let effect = Effect::SetField {
        field_idx: SLOT as u32,
        value: new_value,
    };
    let name = rotated_descriptor_name_for_effect(&effect).expect("setField cohort member");
    let desc = parse_vm_descriptor2(rotated_descriptor_json(name)).expect("descriptor parses");
    let mut after_cell = producer_cell(before, 0);
    assert!(after_cell.state.set_field(SLOT, field_bytes), "set_field");
    let st = CellState::new(before as u64, 0);
    let effects = vec![effect];
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before, 0);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &vec![[3u8; 32]],
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &vec![[3u8; 32]],
        &Default::default(),
    );
    let caveat = empty_caveat_manifest();
    let (trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("live rotated generator must produce a large-value setField trace + PIs");
    Honest {
        desc,
        trace,
        dpis,
        mem_boundary: MemBoundaryWitness::default(),
        map_heaps: vec![],
    }
}

/// **⚑ THIS TEST WAS CONVERTED, AND ITS OLD JOB WAS TO DOCUMENT A LIMITATION.** It used to be
/// `honest_large_value_setfield_fails_the_deployed_freeze` and it ASSERTED THE REFUSAL: an honest
/// `setField` whose 32-byte value had any nonzero byte outside `28..32` could not prove, because the
/// deployed freeze-ALL wrap pinned the written slot's 7 completion lanes BEFORE↔AFTER. That is the
/// whole of "the protocol cannot express an honest 32-byte field write", and it was a *passing test*
/// — a green tooth whose green meant the wound was intact.
///
/// The deployed members are now the VALUE8 shape (Lean `v3RegistryBare`: freeze-EXCEPT +
/// `withSetFieldCompletionPins slot`), so the assertion is INVERTED: the honest large write must
/// PROVE and VERIFY, with its high 224 bits published as PIs 46..=52. A refusal here is the wound
/// returning.
#[test]
fn honest_large_value_setfield_proves_on_the_deployed_member() {
    let h = build_honest_large();
    // NON-VACUITY. This used to read "≥1 completion lane is nonzero", which every value satisfies
    // once the lanes carry a hash — a gate that cannot go red. The property that still discriminates
    // is that the LARGE value's completion octet differs from the SMALL value's: the high bytes
    // (0xAB, 0xCD at positions 0/1) are outside the u64 lane, so ONLY the completion lanes can
    // carry them, and if they did not this test would be about a value lanes 0/1 already bound.
    let mut small_bytes = [0u8; 32];
    small_bytes[28..32].copy_from_slice(&1_000u32.to_be_bytes());
    let mut large_bytes = small_bytes;
    large_bytes[0] = 0xAB;
    large_bytes[1] = 0xCD;
    let small8 = dregg_circuit::effect_vm::field_limbs8(&small_bytes);
    let large8 = dregg_circuit::effect_vm::field_limbs8(&large_bytes);
    assert_eq!(
        small8[0], large8[0],
        "the pair must agree on lane 0 — the high bytes are invisible to the u64 lane"
    );
    assert_eq!(small8[1], large8[1], "and on lane 1");
    assert!(
        (1..8).any(|k| small8[k] != large8[k]),
        "the high bytes must reach the completion octet, else this test measures nothing"
    );
    for k in 0..7 {
        assert_eq!(
            h.trace[0][AFTER_BASE + COMPLETION_BASE + k],
            large8[1 + k],
            "the generator must publish the honest large-value completion lane {k}"
        );
    }
    // The generator publishes the 7 freed lanes as PIs 46..=52, ahead of the 4 rc pins.
    // ⚑ 57 → 58: the NINE-LANE epoch (`e662ade32`). DERIVED, not re-pinned to what the file says:
    // the emitted descriptor carries pi_binding indices 46..=53 on columns [569..575, 614] — seven
    // contiguous lanes plus the ninth at 614, which is `fieldLaneCol`'s documented NON-CONTIGUOUS
    // shape. So the count is 46 prefix + 8 value8 + 4 rc.
    assert_eq!(
        h.dpis.len(),
        58,
        "the deployed setField member is 58 PIs (46 prefix + 8 value8 + 4 rc)"
    );
    let last = h.trace.last().expect("non-empty trace");
    for k in 0..7 {
        assert_eq!(
            h.dpis[46 + k],
            last[AFTER_BASE + COMPLETION_BASE + k],
            "PI {} must publish the written slot's completion lane {k}",
            46 + k
        );
    }
    assert!(
        !refused(&h, &h.trace, &h.dpis),
        "an HONEST large-value setField (a real 32-byte FieldElement with nonzero high bytes) MUST \
         prove + verify against the DEPLOYED descriptor — the high 224 bits ride the freed \
         completion lanes and are PUBLISHED as PIs 46..=52. If this is refused, the freeze-ALL wrap \
         is back and the protocol cannot express an honest 32-byte field write."
    );
    eprintln!(
        "R1 CLOSED: an honest large-value setField PROVES on the deployed member; its high 224 bits \
         are published, not frozen."
    );
}

#[test]
fn forged_written_slot_completion_lanes_is_unsat() {
    let (h, _v) = build_honest_small();

    // Sanity: honest proves (so a reject below is the FORGE, not a broken fixture).
    let proof = prove_vm_descriptor2(&h.desc, &h.trace, &h.dpis, &h.mem_boundary, &h.map_heaps)
        .expect("honest baseline must prove");
    verify_vm_descriptor2(&h.desc, &proof, &h.dpis).expect("honest baseline must verify");

    // THE FORGE: on the active row (row 0), set the written slot's completion lanes 1..7 to
    // arbitrary values that are NOT the honest published value8 (the honest lanes are now a
    // Poseidon2 image, not zeros — see `build_honest_small`), keeping lane 0 (the welded limb)
    // honest.
    // Recompute the AFTER chain so NEW_COMMIT genuinely absorbs the forged high bytes — the exact
    // wire view a ledgerless client would accept. BEFORE stays honest (pre-state completion 0), so
    // the ONLY thing that can bite is the completion freeze `before == after`.
    let mut ftrace = h.trace.clone();
    let n = ftrace.len();
    let forged_lanes: [u32; 7] = [0xDEAD, 0xBEEF, 0x1234, 0x5678, 0x9ABC, 0xCAFE, 0xF00D];
    for k in 0..7 {
        ftrace[0][AFTER_BASE + COMPLETION_BASE + k] = BabyBear::new(forged_lanes[k]);
    }
    recompute_after_chain(&mut ftrace[0]);

    // Patch the rotated NEW_COMMIT PI (PI 43) to the forged active row's AFTER commit — the wire
    // view (the light client is handed this NEW_COMMIT). NOTE: for a single-effect trace the last
    // row's AFTER commit is the published one; here the active row IS row 0 and the padding rows
    // fold forward, so patch to whatever the last row now carries after the chain. To keep the
    // published commit consistent with the forged high bytes we mirror the forged completion lanes
    // onto every row's AFTER block and rebuild each chain, then pin PI 43 to the last row.
    for r in 1..n {
        for k in 0..7 {
            ftrace[r][AFTER_BASE + COMPLETION_BASE + k] = BabyBear::new(forged_lanes[k]);
        }
        recompute_after_chain(&mut ftrace[r]);
    }
    let mut fdpis = h.dpis.clone();
    fdpis[V1_PI_COUNT + 1] = ftrace[n - 1][AFTER_BASE + B_STATE_COMMIT];

    // Self-check (non-vacuity): the forged published commit DIFFERS from the honest one — the wire
    // genuinely carries the forged high bytes.
    assert_ne!(
        ftrace[n - 1][AFTER_BASE + B_STATE_COMMIT],
        h.trace[n - 1][AFTER_BASE + B_STATE_COMMIT],
        "the forged completion lanes must publish a DIFFERENT commit (else the forge is vacuous)"
    );

    let unsat = refused(&h, &ftrace, &fdpis);
    // Report the verdict either way — this is the R1 attack, so the truth matters, not the pass.
    if unsat {
        eprintln!(
            "R1 VERDICT: the written-slot completion-lane forge is UNSAT on the deployed descriptor \
             — under the VALUE8 epoch the binding gate is the PIN (`.piBinding .last` on each freed \
             lane, PIs 46..=52) rather than the old BEFORE↔AFTER freeze: the forged lanes differ \
             from the honest published value8, so there is no satisfying assignment."
        );
    } else {
        eprintln!(
            "R1 VERDICT: the written-slot completion-lane forge PROVES+VERIFIES — the census R1 \
             silent-forge is LIVE on the deployed wire (the high 224 bits are unconstrained)."
        );
    }
    assert!(
        unsat,
        "R1 FORGE LIVE: a setField post-cell forged to differ ONLY in the written slot's completion \
         lanes 1..7 (high 224 bits) proves+verifies — a ledgerless client accepts an arbitrary \
         high-224-bit field value (census §6 R1 confirmed live)."
    );
}
