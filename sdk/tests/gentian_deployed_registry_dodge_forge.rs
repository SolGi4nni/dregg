//! # GENTIAN deployed-registry VERIFY — the FORGE (the decider), CLOSED.
//!
//! The meta-review flagged a registry mismatch: the flag-day capacity-floor REFUSE
//! (`gentianDeployedBareRefuse`, `EffectVmEmitRotationV3Refused.v3RegistryRefused`) was welded onto the
//! **V3 1-felt** cohort ONLY. But the DEPLOYED light-client verify path — the SDK wire verifier
//! [`dregg_sdk::full_turn_proof::verify_effect_vm_rotated_with_cutover`] and the executor
//! `verify_one_cohort_run` — resolves the **WIDE / WELDED** registries
//! (`WIDE_REGISTRY_STAGED_TSV` + `WIDE_UMEM_WELD_REGISTRY_TSV`), so a declared-capacity cell settling via
//! a plain BARE wide leg bound the (refuse-free) WIDE bare member and was ACCEPTED — the open dodge.
//!
//! THE FIX (option a — the wide VK epoch): the capacity-floor refuse is now lifted to ride the WIDE /
//! WELDED bare cohort too (`Dregg2.Deos.BareCohortFloorRefuseWide.gentianWideBareRefuse`, aux blocks PAST
//! the wide member width; `declared_capacity_unsat_wide`), emitted onto exactly the 36 bare cohort
//! members and regenerated into `WIDE_REGISTRY_STAGED_TSV` / `WIDE_UMEM_WELD_REGISTRY_TSV`. The Rust
//! `fill_refuse_aux` fills the wide aux base (`trace_width − 3·REFUSE_STRIDE`).
//!
//! THIS FORGE now DECIDES the flip: a cell whose caveat manifest DECLARES the escrow capacity (tag 17,
//! folded into caveatCommit PI 45) and settles via a plain bare-cohort `Burn` is REJECTED by the deployed
//! entry `verify_effect_vm_rotated_with_cutover` — the honest producer path is UNSAT under the
//! refuse-welded member (floor=1 → the floor==0 gate), and a genuine PRE-FLIP bare-dodge STARK binds NO
//! deployed cohort descriptor. A NON-declaring normal turn still verifies (completeness/liveness). If the
//! deployed LC ever ACCEPTS the declared-capacity bare dodge again, the refuse regressed off the deployed
//! WIDE/WELDED registries.
//!
//! Requires `prover`; self-skips under `not(prover)`. SLOW (real batch STARK).

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::columns::rotation::caveat as cav;
use dregg_circuit::effect_vm::pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW;
use dregg_circuit::effect_vm::trace_rotated::{
    DFA_RC_LEN, ROT_PI_COUNT, RotatedBlockWitness, RotatedCaveatEntry, RotatedCaveatManifest,
    generate_rotated_effect_vm_descriptor_and_trace_wide,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::{WIDE_REGISTRY_STAGED_TSV, WIDE_UMEM_WELD_REGISTRY_TSV};
use dregg_circuit::field::BabyBear;
use dregg_turn::rotation_witness as rw;

const WIDE_BARE_MEMBER: &str = "burnVmDescriptor2R24";

fn registry_json(registry: &'static str, name: &str) -> Option<&'static str> {
    registry.lines().find_map(|l| {
        let mut it = l.splitn(3, '\t');
        if it.next() == Some(name) {
            let _ = it.next();
            it.next()
        } else {
            None
        }
    })
}

fn wide_desc(name: &str) -> EffectVmDescriptor2 {
    let json = registry_json(WIDE_REGISTRY_STAGED_TSV, name)
        .unwrap_or_else(|| panic!("{name} not in WIDE_REGISTRY_STAGED_TSV"));
    parse_vm_descriptor2(json).unwrap_or_else(|e| panic!("{name} wide parses: {e}"))
}

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

fn producer_cell(balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("pre-iroot limbs")
}

/// **THE DEPLOYED WIDE LEG, THROUGH THE DEPLOYED PRODUCER.** This file used to call
/// `generate_rotated_transfer_shape_wide` directly — the per-family helper — and hand the result to
/// the committed member. That helper lays the base + the 16 wide carriers and STOPS: it does not run
/// the Epoch-1 `compact_s2_columns ∘ compact_e1_columns` deletion, and it does not lay the
/// post-regen registry tail (the refuse aux blocks + the teeth columns). Both of those live in
/// `generate_rotated_effect_vm_descriptor_and_trace_wide`, which is the route the SDK's own wide
/// prover takes. So the hand-rolled call produced a 2607-wide OLD-geometry row against a 1606-wide
/// committed descriptor and BOTH poles of this forge died in the pre-flight arity check — the dodge
/// was neither demonstrated nor closed, it was never exercised. Go through the deployed producer.
fn deployed_wide_leg(
    st: &CellState,
    effects: &[Effect],
    before_w: &rw::RotationWitness,
    after_w: &rw::RotationWitness,
    caveat: &RotatedCaveatManifest,
) -> (
    EffectVmDescriptor2,
    Vec<Vec<BabyBear>>,
    Vec<BabyBear>,
    Vec<Vec<dregg_circuit::heap_root::HeapLeaf>>,
    MemBoundaryWitness,
) {
    generate_rotated_effect_vm_descriptor_and_trace_wide(
        st,
        effects,
        &bridge(before_w),
        &bridge(after_w),
        caveat,
        None,
        None,
        None,
        None,
    )
    .expect("the DEPLOYED wide producer mints the bare burn leg at the committed geometry")
}

/// A caveat manifest that DECLARES the escrow capacity obligation (tag 17) on slot 0 — exactly the
/// gentian pattern: the capacity is committed into the caveat-commit fold (PI 45), so the proof's own
/// public inputs carry the declaration. The refuse gate (V3-only) reads the floor derived from this
/// declared tag; the WIDE bare member carries no such gate.
fn escrow_declaring_manifest() -> RotatedCaveatManifest {
    let mut m = RotatedCaveatManifest::default();
    m.entries[0] = RotatedCaveatEntry {
        type_tag: SLOT_CAVEAT_TAG_SETTLE_ESCROW,
        domain_tag: cav::DOMAIN_REGISTERS,
        key: BabyBear::ZERO,
        params: [BabyBear::ZERO; 4],
    };
    m
}

/// A non-declaring caveat manifest (all zero — NO capacity tag). The completeness pole: the refuse
/// decodes `floor = 0`, is inert, and an honest normal turn still verifies (no false reject).
fn non_declaring_manifest() -> RotatedCaveatManifest {
    RotatedCaveatManifest::default()
}

/// The pre-flip (NON-refuse) wide bare member: the deployed refuse-welded member with the three refuse
/// blocks stripped (the last 39 gates) and the trace narrowed to the pre-refuse width. This is EXACTLY
/// what an old (pre-flag-day) producer — or a forger who ignores the declaration-keyed routing — would
/// emit for a bare burn leg: a genuine wide STARK with NO capacity-floor refuse. Driving its proof
/// through the CURRENT deployed verify is the decider (it must bind NO deployed cohort descriptor).
/// The flag-day widening the three refuse aux blocks add PAST the member — **PER-MEMBER, DERIVED**.
/// It is NOT a constant 48: the two avail-hardened members (transfer/burn) ride the refuse block at
/// the very top of the trace (widen 45) while the other 34 carry a 3-column dead stride-tail above it
/// (widen 48), which is exactly why `generate_rotated_effect_vm_descriptor_and_trace_wide` derives it
/// from the descriptor's own committed floor-refuse gates. A hardcoded 48 here narrowed the burn
/// member by three columns too many.
fn refuse_width(welded: &EffectVmDescriptor2) -> usize {
    dregg_circuit::effect_vm::bare_floor_refuse_weld::refuse_weld_widen(welded)
}

fn preflip_bare_member(welded: &EffectVmDescriptor2) -> EffectVmDescriptor2 {
    const REFUSE_GATE_COUNT: usize = 39; // 3 blocks × 13 gates (Lean `wideRefuseGates`).
    let refuse_width = refuse_width(welded);
    let mut d = welded.clone();
    d.name = d
        .name
        .trim_end_matches("-gentian-deployed-bare-refuse")
        .to_string();
    d.trace_width -= refuse_width;
    let keep = d.constraints.len() - REFUSE_GATE_COUNT;
    d.constraints.truncate(keep);
    d
}

/// ====================================================================================================
/// THE DECIDER (post-flip): the capacity-floor refuse now rides the DEPLOYED WIDE / WELDED bare cohort,
/// so a cell that DECLARES a capacity obligation and settles via a plain bare-cohort leg is REJECTED by
/// the deployed light-client entry `verify_effect_vm_rotated_with_cutover` — while a NON-declaring
/// normal turn still verifies (completeness/liveness preserved).
/// ====================================================================================================
#[test]
fn declared_capacity_dodge_verifies_through_deployed_lightclient() {
    // ---- 0. GROUND: the flip landed — the DEPLOYED WIDE + WELDED bare burn members now carry the
    // capacity-floor refuse (the registries the deployed LC actually resolves), not only V3. ----
    let wide_json = registry_json(WIDE_REGISTRY_STAGED_TSV, WIDE_BARE_MEMBER).unwrap();
    let welded_json = registry_json(WIDE_UMEM_WELD_REGISTRY_TSV, WIDE_BARE_MEMBER).unwrap();
    assert!(
        wide_json.contains("gentian-deployed-bare-refuse"),
        "the deployed WIDE bare burn now carries the capacity-floor refuse (the flip is on the \
         deployed default registry)"
    );
    assert!(
        welded_json.contains("gentian-deployed-bare-refuse"),
        "the deployed WELDED bare burn carries the refuse too (the require_welded route is closed)"
    );
    let wide_bare = wide_desc(WIDE_BARE_MEMBER); // the refuse-welded deployed member
    // ⚑ DERIVED, NOT HARDCODED. This read `== 2541` — the PRE-Epoch-1 width. The S2 (dead 1-felt
    // chains) and E1 (dead v1-face bands) deletions moved every wide member, so an absolute width
    // here is a number that rots on the next compaction and says nothing about the refuse. What the
    // flag day actually asserts is the RELATION: the deployed member is the pre-flip bare member
    // PLUS the three refuse aux blocks.
    assert_eq!(
        wide_bare.trace_width,
        preflip_bare_member(&wide_bare).trace_width + refuse_width(&wide_bare),
        "the WIDE bare burn is the pre-flip member widened by the three-block refuse aux"
    );
    let vk_hash = *blake3::hash(wide_json.as_bytes()).as_bytes();

    // Shared witness scaffolding.
    let before_balance: i64 = 80_000;
    let amount: u64 = 30;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::Burn {
        target_hash: [BabyBear::ZERO; 8],
        amount_lo: BabyBear::new(amount as u32),
        amount_full: amount,
    }];
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance);
    let after_cell = producer_cell(before_balance - amount as i64);
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
    // ---- 1. COMPLETENESS (liveness preserved): a NON-declaring wide burn still verifies through the
    // deployed LC. The refuse decodes `floor = 0` on every block, is inert, and the honest normal turn
    // proves + verifies — no false reject. ----
    let (_d, honest_trace, honest_dpis, heaps, mem) = deployed_wide_leg(
        &st,
        &effects,
        &before_w,
        &after_w,
        &non_declaring_manifest(),
    );
    // The producer mints the committed geometry MINUS the refuse aux band: those columns are the
    // floor-refuse GATE's own witnesses, resized + filled at prove time by
    // `descriptor_ir2`'s `fill_refuse_aux`, never producer-emitted.
    assert_eq!(
        honest_trace[0].len(),
        wide_bare.trace_width - refuse_width(&wide_bare),
        "the deployed producer mints the committed member's geometry (less the refuse aux band)"
    );
    let honest_proof = prove_vm_descriptor2(&wide_bare, &honest_trace, &honest_dpis, &mem, &heaps)
        .expect("a NON-declaring wide bare burn proves under the refuse-welded member (floor=0)");
    verify_vm_descriptor2(&wide_bare, &honest_proof, &honest_dpis)
        .expect("non-declaring bare burn verifies at the descriptor level");
    let honest_bytes = postcard::to_allocvec(&honest_proof).expect("serialize honest proof");
    dregg_sdk::full_turn_proof::verify_effect_vm_rotated_with_cutover(
        &honest_bytes,
        &honest_dpis,
        &vk_hash,
    )
    .expect(
        "LIVENESS: a non-declaring normal turn must still verify through the deployed LC after the \
         flip (the refuse is inert for a cell that declares no capacity)",
    );

    // ---- 2. THE DODGE: a cell that DECLARES the escrow capacity (tag 17, folded into caveatCommit
    // PI 45) and settles via a plain bare-cohort burn. ----
    let manifest = escrow_declaring_manifest();
    let (_d2, trace, dpis, _h2, _m2) =
        deployed_wide_leg(&st, &effects, &before_w, &after_w, &manifest);
    assert_eq!(
        dpis.len(),
        ROT_PI_COUNT + DFA_RC_LEN + 16,
        "wide bare-cohort PI count (base 50 + 16 wide anchors)"
    );

    // ---- 2a. The declared-capacity bare leg is UNSAT under the DEPLOYED refuse-welded member: the
    // honest producer path fills `floor = 1` (escrow declared) and the `floor == 0`-refuse gate has no
    // satisfying assignment, so the STARK does not prove. There is NO deployed bare-dodge artifact. ----
    // The prover trips a debug constraint-check on the unsatisfiable refuse gate (an EXPECTED abort);
    // silence its panic hook so the run is not noisy, then restore it.
    let prev_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let declared_prove = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_vm_descriptor2(&wide_bare, &trace, &dpis, &mem, &heaps)
    }));
    std::panic::set_hook(prev_hook);
    match declared_prove {
        Err(_) => { /* the prover aborted on the unsatisfiable refuse gate — UNSAT, dodge closed */
        }
        Ok(Err(_)) => { /* the prover returned an error on the unsatisfiable trace — UNSAT */ }
        Ok(Ok(proof)) => {
            // If a proof was somehow produced, the deployed LC must still REJECT it.
            let bytes = postcard::to_allocvec(&proof).expect("serialize");
            let v = dregg_sdk::full_turn_proof::verify_effect_vm_rotated_with_cutover(
                &bytes, &dpis, &vk_hash,
            );
            assert!(
                v.is_err(),
                "a declared-capacity bare leg must NOT verify through the deployed LC"
            );
        }
    }

    // ---- 2b. THE DECIDER — through `verify_effect_vm_rotated_with_cutover`: even a genuine PRE-FLIP
    // bare-dodge STARK (the exact artifact an old producer, or a forger ignoring the declaration-keyed
    // routing, would emit — a wide bare burn with NO refuse) is REJECTED by the deployed LC. The
    // deployed registry now carries ONLY the refuse-welded member, so the pre-flip proof binds NO
    // deployed cohort descriptor. ----
    let preflip = preflip_bare_member(&wide_bare);
    assert_eq!(
        preflip.trace_width,
        wide_bare.trace_width - refuse_width(&wide_bare),
        "pre-flip member is the un-widened wide bare burn (derived, not a pre-Epoch-1 constant)"
    );
    assert!(
        !preflip.name.contains("gentian-deployed-bare-refuse"),
        "pre-flip member carries NO refuse"
    );
    // The pre-flip artifact is the SAME producer row — which already carries NO refuse aux band, so
    // it IS the exact row an old (pre-flag-day) producer emitted, at the pre-flip member's width.
    assert_eq!(
        trace[0].len(),
        preflip.trace_width,
        "the producer row IS the pre-flip member's geometry (the refuse aux is gate-internal)"
    );
    let dodge_proof = prove_vm_descriptor2(&preflip, &trace, &dpis, &mem, &heaps).expect(
        "the pre-flip bare-dodge STARK proves (the reconstructed pre-flag-day member has no refuse)",
    );
    verify_vm_descriptor2(&preflip, &dodge_proof, &dpis).expect(
        "the pre-flip bare-dodge verifies at ITS OWN descriptor level (a real, valid STARK)",
    );
    let dodge_bytes = postcard::to_allocvec(&dodge_proof).expect("serialize dodge proof");
    let verdict = dregg_sdk::full_turn_proof::verify_effect_vm_rotated_with_cutover(
        &dodge_bytes,
        &dpis,
        &vk_hash,
    );
    match verdict {
        Err(e) => {
            eprintln!(
                "GENTIAN DEPLOYED VERIFY — DODGE CLOSED: a declared-escrow cell settled via a plain \
                 bare-cohort burn was REJECTED by the deployed light-client entry \
                 `verify_effect_vm_rotated_with_cutover`. The deployed WIDE/WELDED bare burn now carries \
                 the capacity-floor refuse; the pre-flip bare-dodge proof binds NO deployed \
                 cohort descriptor. Reject: {e}"
            );
        }
        Ok(()) => {
            panic!(
                "HOLE STILL OPEN: the deployed LC ACCEPTED a declared-escrow bare-cohort dodge through \
                 `verify_effect_vm_rotated_with_cutover` — the capacity-floor refuse is NOT live on the \
                 deployed WIDE/WELDED registries."
            );
        }
    }
}

/// ====================================================================================================
/// GATE B — the INDEPENDENT arm: the verifier-side declared-capacity DISCRIMINATOR rejects a
/// declaring-but-bare route ALONE, with the refuse weld INERT.
///
/// Gate A (the refuse weld) rejects the dodge by making the declared-capacity bare leg UNSAT under the
/// refuse-welded member — a GEOMETRY property of the committed VK bytes. Gate B is a SECOND, orthogonal
/// gate: given the acting cell's COMMITTED declaration (re-derived required tags), a declared-capacity
/// turn MUST bind its satisfaction member; a bare cohort member is rejected regardless of geometry.
///
/// This arm ISOLATES gate B. We prove a NON-declaring bare burn — which passes gate A cleanly (the
/// refuse decodes `floor = 0`, is inert, the STARK proves + verifies through the deployed refuse-welded
/// member). The SAME proof, SAME PIs:
///   * through `verify_effect_vm_rotated_with_cutover` (no declaration) → ACCEPTED (gate A inert, so the
///     ONLY gate that could reject is off);
///   * through `verify_effect_vm_rotated_declaring(.., &[escrow tag])` → REJECTED by gate B alone.
/// So with gate A demonstrably NOT the rejector (it accepts the same bytes), gate B is the load-bearing
/// discriminator: a cell that declares the escrow capacity cannot settle via a bare cohort member.
#[test]
fn gate_b_discriminator_alone_rejects_declared_bare_route() {
    // Pure discriminator (no proof): the declared-escrow route MUST name the satisfaction member; the
    // bare cohort member is refused, geometry-free.
    assert_eq!(
        dregg_sdk::full_turn_proof::required_satisfaction_member(&[SLOT_CAVEAT_TAG_SETTLE_ESCROW]),
        Some("settleEscrowSatVmDescriptor2R24"),
        "gate B: a declared-escrow cell requires the settleEscrow satisfaction member"
    );
    assert_eq!(
        dregg_sdk::full_turn_proof::required_satisfaction_member(&[]),
        None,
        "gate B is inert for a non-declaring cell"
    );

    // Build a genuine NON-declaring wide bare burn (gate A inert: refuse floor = 0).
    let wide_json = registry_json(WIDE_REGISTRY_STAGED_TSV, WIDE_BARE_MEMBER).unwrap();
    let wide_bare = wide_desc(WIDE_BARE_MEMBER);
    let vk_hash = *blake3::hash(wide_json.as_bytes()).as_bytes();

    let before_balance: i64 = 80_000;
    let amount: u64 = 30;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::Burn {
        target_hash: [BabyBear::ZERO; 8],
        amount_lo: BabyBear::new(amount as u32),
        amount_full: amount,
    }];
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance);
    let after_cell = producer_cell(before_balance - amount as i64);
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
    let (_d, trace, dpis, heaps, mem) = deployed_wide_leg(
        &st,
        &effects,
        &before_w,
        &after_w,
        &non_declaring_manifest(),
    );
    let proof = prove_vm_descriptor2(&wide_bare, &trace, &dpis, &mem, &heaps)
        .expect("a NON-declaring wide bare burn proves under the refuse-welded member (floor=0)");
    let bytes = postcard::to_allocvec(&proof).expect("serialize");

    // ---- Gate A is INERT on these bytes: the pure LC entry ACCEPTS them. ----
    dregg_sdk::full_turn_proof::verify_effect_vm_rotated_with_cutover(&bytes, &dpis, &vk_hash).expect(
        "gate A inert: a non-declaring bare burn verifies through the deployed LC (the refuse is off)",
    );

    // ---- Gate B ALONE rejects the SAME bytes when the acting cell DECLARES the escrow capacity: a
    // declared-capacity turn cannot ride a bare cohort member. This is independent of the refuse weld —
    // the same STARK that gate A accepted is refused purely by the declaration/route mismatch. ----
    let verdict = dregg_sdk::full_turn_proof::verify_effect_vm_rotated_declaring(
        &bytes,
        &dpis,
        &vk_hash,
        &[SLOT_CAVEAT_TAG_SETTLE_ESCROW],
    );
    match verdict {
        Err(e) => eprintln!(
            "GATE B (declared-capacity discriminator) — LOAD-BEARING: a cell declaring the escrow \
             capacity that settled via a plain bare-cohort burn was REJECTED by the discriminator \
             ALONE (the refuse weld was inert — the identical bytes verified through the pure LC \
             entry). Reject: {e}"
        ),
        Ok(()) => panic!(
            "GATE B FAILED: the declaring verify ACCEPTED a declared-escrow cell settled via a bare \
             cohort burn — the verifier-side discriminator is NOT load-bearing."
        ),
    }
}
