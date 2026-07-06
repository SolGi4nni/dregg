//! # GENTIAN deployed-registry VERIFY — the FORGE (the decider).
//!
//! The meta-review flagged a registry mismatch: the flag-day capacity-floor REFUSE
//! (`gentianDeployedBareRefuse`, `EffectVmEmitRotationV3Refused.v3RegistryRefused`) is welded onto the
//! **V3 1-felt** cohort (`rotation-v3-staged-registry.tsv`, bare members widened 1581→1626 + 39 refuse
//! gates). But the DEPLOYED light-client verify path — the SDK wire verifier
//! [`dregg_sdk::full_turn_proof::verify_effect_vm_rotated_with_cutover`] and the executor
//! `verify_one_cohort_run` — resolves the **WIDE / WELDED** registries
//! (`WIDE_REGISTRY_STAGED_TSV` + `WIDE_UMEM_WELD_REGISTRY_TSV`), FALLING BACK to V3 only for cap-open
//! members that lack a wide twin (`name.contains("CapOpen")`, and only when the wide set is empty).
//!
//! The three capacity-satisfaction members (`settleEscrowSat` / `dischargeSat` / `vaultSat`) AND the
//! refuse-welded bare members live ONLY in the V3 registry. They are NOT cap-open names, so the V3
//! fallback filter EXCLUDES them, and the wide set is never empty for a bare-cohort proof. So the
//! deployed LC binds the WIDE bare member — which carries NEITHER the refuse NOR the satisfaction gate.
//!
//! THE FORGE: a cell whose caveat manifest DECLARES a capacity obligation (escrow, tag 17) settles via a
//! plain bare-cohort effect (here a value-draining `Burn`, a bare-46-PI cohort member — the refuse
//! theorem `declared_capacity_unsat_deployed` is stated for ANY bare member). The producer emits the
//! WIDE bare leg (the deployed default). We drive that real STARK through the ACTUAL deployed entry
//! `verify_effect_vm_rotated_with_cutover`. If it ACCEPTS, the bare-descriptor dodge is OPEN on the
//! deployed path (the refuse only bites on the V3 registry the deployed LC never verifies a bare leg
//! against) — the gentian flip is NOT live on the deployed light-client path.
//!
//! Requires `prover`; self-skips under `not(prover)`. SLOW (real batch STARK).
#![cfg(feature = "prover")]

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::columns::rotation::caveat as cav;
use dregg_circuit::effect_vm::pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW;
use dregg_circuit::effect_vm::trace_rotated::{
    DFA_RC_LEN, ROT_PI_COUNT, RotatedBlockWitness, RotatedCaveatEntry, RotatedCaveatManifest,
    generate_rotated_transfer_shape_wide,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::{
    V3_STAGED_REGISTRY_TSV, WIDE_REGISTRY_STAGED_TSV, WIDE_UMEM_WELD_REGISTRY_TSV,
};
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

/// ====================================================================================================
/// THE DECIDER: an honest-looking WIDE bare-cohort proof over a cell that DECLARES a capacity
/// obligation verifies through the DEPLOYED light-client entry — no refuse bites.
/// ====================================================================================================
#[test]
fn declared_capacity_dodge_verifies_through_deployed_lightclient() {
    // ---- 0. GROUND the registry split (the mismatch the meta-review flagged). ----
    // The refuse + the satisfaction members live ONLY on the V3 1-felt registry.
    let v3_bare = parse_vm_descriptor2(
        registry_json(V3_STAGED_REGISTRY_TSV, WIDE_BARE_MEMBER).expect("v3 bare member"),
    )
    .expect("v3 bare parses");
    let wide_bare = wide_desc(WIDE_BARE_MEMBER);
    assert_eq!(
        v3_bare.trace_width, 1626,
        "the V3 bare member IS refuse-welded (1581 base + the capacity-floor refuse widening)"
    );
    assert_ne!(
        wide_bare.trace_width, 1626,
        "the WIDE bare member is a DIFFERENT emit — it does NOT carry the 1626 refuse widening"
    );
    // The flag-day refuse marker (`gentian-deployed-bare-refuse`, the emit's `ir` suffix) is on the V3
    // bare member ONLY — NOT on the WIDE/WELDED bare members the deployed LC verifies against.
    let v3_json = registry_json(V3_STAGED_REGISTRY_TSV, WIDE_BARE_MEMBER).unwrap();
    let wide_json = registry_json(WIDE_REGISTRY_STAGED_TSV, WIDE_BARE_MEMBER).unwrap();
    let welded_json = registry_json(WIDE_UMEM_WELD_REGISTRY_TSV, WIDE_BARE_MEMBER).unwrap();
    assert!(
        v3_json.contains("gentian-deployed-bare-refuse"),
        "the V3 bare member carries the flag-day capacity-floor refuse weld"
    );
    assert!(
        !wide_json.contains("gentian-deployed-bare-refuse") && !wide_json.contains("refuse"),
        "the WIDE bare member carries NO refuse weld — the refuse is not on the deployed registry"
    );
    assert!(
        !welded_json.contains("gentian-deployed-bare-refuse") && !welded_json.contains("refuse"),
        "the WELDED bare member carries NO refuse weld either"
    );
    // The three satisfaction members are V3-only and are NOT cap-open names, so the deployed V3
    // fallback filter (`name.contains(\"CapOpen\")`) can never surface them.
    for sat in [
        "settleEscrowSatVmDescriptor2R24",
        "dischargeSatVmDescriptor2R24",
        "vaultSatVmDescriptor2R24",
    ] {
        assert!(
            registry_json(V3_STAGED_REGISTRY_TSV, sat).is_some(),
            "{sat} is a committed V3 member"
        );
        assert!(
            registry_json(WIDE_REGISTRY_STAGED_TSV, sat).is_none()
                && registry_json(WIDE_UMEM_WELD_REGISTRY_TSV, sat).is_none(),
            "{sat} is ABSENT from the deployed WIDE/WELDED registries the LC verifies against"
        );
        assert!(
            !sat.contains("CapOpen"),
            "{sat} is not a cap-open name, so the deployed V3 fallback filter excludes it"
        );
    }

    // ---- 1. Build the dodge: a capacity-DECLARING cell settled via a plain bare-cohort effect. ----
    let before_balance: i64 = 80_000;
    let amount: u64 = 30; // drain 30 out of the escrow-obligated cell
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::Burn {
        target_hash: BabyBear::new(0),
        amount_lo: BabyBear::new(amount as u32),
        amount_full: amount,
    }];

    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance);
    let after_cell = producer_cell(before_balance - amount as i64);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        &Default::default(),
    );

    // The caveat manifest DECLARES the escrow capacity obligation — the declaration is folded into the
    // committed caveatCommit PI, so the proof itself carries the capacity claim.
    let manifest = escrow_declaring_manifest();
    let (trace, dpis) = generate_rotated_transfer_shape_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &manifest,
    )
    .expect("wide bare producer (declared-capacity cell)");
    assert_eq!(
        dpis.len(),
        ROT_PI_COUNT + DFA_RC_LEN + 16,
        "wide bare-cohort PI count (base 50 + 16 wide anchors)"
    );
    assert_eq!(
        wide_bare.trace_width,
        trace[0].len(),
        "descriptor width == trace"
    );

    // ---- 2. Prove the real STARK, exactly as the deployed producer would emit it. ----
    let mem = MemBoundaryWitness::default();
    let heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];
    let proof = prove_vm_descriptor2(&wide_bare, &trace, &dpis, &mem, &heaps)
        .expect("the wide bare leg proves (the deployed producer's default emit)");
    // Sanity: it verifies at the descriptor level.
    verify_vm_descriptor2(&wide_bare, &proof, &dpis).expect("wide bare leg verifies");

    // ---- 3. THE DECIDER: drive it through the ACTUAL deployed light-client entry. ----
    let proof_bytes = postcard::to_allocvec(&proof).expect("serialize proof");
    let vk_hash = *blake3::hash(wide_json.as_bytes()).as_bytes();
    let verdict = dregg_sdk::full_turn_proof::verify_effect_vm_rotated_with_cutover(
        &proof_bytes,
        &dpis,
        &vk_hash,
    );

    // If the deployed LC ACCEPTS this leg, the declared-capacity dodge is OPEN on the deployed path:
    // the LC bound the WIDE bare member (no refuse), never the V3 refuse member nor a satisfaction
    // member. That is the hole the meta-review suspected.
    match verdict {
        Ok(()) => {
            eprintln!(
                "GENTIAN DEPLOYED VERIFY — HOLE CONFIRMED: a cell DECLARING the escrow capacity \
                 obligation (tag 17) settled via a plain bare-cohort leg was ACCEPTED by the deployed \
                 light-client entry `verify_effect_vm_rotated_with_cutover`. The LC bound the WIDE \
                 `{WIDE_BARE_MEMBER}` (width {}, no capacity-floor refuse); the refuse-welded V3 member \
                 (width 1626) and the V3 satisfaction members are UNREACHABLE on the deployed path. The \
                 gentian flip is NOT live on the deployed light-client path.",
                wide_bare.trace_width
            );
        }
        Err(e) => {
            panic!(
                "the deployed LC REJECTED the declared-capacity bare leg: {e}\n\
                 (if this rejects, the refuse reaches the deployed path after all — re-examine the \
                 resolution, the flip may be live)"
            );
        }
    }
}
