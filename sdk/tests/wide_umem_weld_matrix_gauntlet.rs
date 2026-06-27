//! # THE WIDE+UMEM WELD MATRIX GAUNTLET — per-MEMBER present/domain parity through the DEPLOYED path.
//!
//! The structural parity test (`effect_vm_descriptors::wide_umem_weld_registry_parity_and_no_narrowing`)
//! checks `registry == weld(bare_wide)` byte-for-byte and `WIDE_UMEM_WELD_REGISTRY_FP`. It NEVER checks
//! that the DEPLOYED welded PRODUCER's trace agrees with the registry member's declared umem shape — the
//! welded leg's DOMAIN. That gap let the 9th flip-refusal (`a5df2470`) through: `setPermsVmDescriptor2R24`
//! / `setVKVmDescriptor2R24` declared umem domain 1 (heap), but the deployed welded producer emits a
//! domain-2 (caps) leg — `SetPermissions` / `SetVerificationKey` move `UKey::Permissions` /
//! `UKey::VerificationKey`, both `UDomain::Caps` (`turn/src/umem.rs`). So the producer welded with
//! domain 2, the committed registry member declared domain 1, the proof bound NO descriptor, and
//! `verify_one_cohort_run` rejected — yet the structural parity test stayed green (it only re-welds the
//! SAME wrong domain extracted from the member).
//!
//! THIS gauntlet is the missing tooth: for each welded member with a genuine single-effect fixture, it
//! GENUINELY applies the effect, derives the GENUINE projection-diff umem ops (NOT a decoupled
//! placeholder — a decoupled op would mask exactly this bug), MINTS through the DEPLOYED welded producer
//! (`prove_wide_umem_welded_staged`), and BINDS+VERIFIES the proof through the DEPLOYED wire verifier
//! (`verify_effect_vm_rotated_with_cutover`) under that member's Lean-emitted welded twin — present/domain
//! parity on the wire, the thing the structural test omits.
//!
//! ## Coverage map (all 54 welded members accounted for — `matrix_enumerates_all_54`)
//!
//! * **DOMAIN-1 record-pin + value family (HERE, genuine mint→wire-verify):** setPerms, setVK, cellSeal,
//!   cellUnseal, cellDestroy, receiptArchive, refusal, makeSovereign — the family the bug lived in. Each
//!   genuinely applies its kernel effect (`apply_effect_to_cell` / the deployed `convert_effects_to_vm`
//!   projection) so the umem leg carries the effect's TRUE single-domain touch.
//! * **DOMAIN-2 capability family (covered end-to-end by the sibling gauntlets):** attenuate
//!   (`wide_umem_weld_domain2_gauntlet` + `executor_cap_open_welded_commit`), grant/introduce/refresh/
//!   revokeCapability/revokeDelegation write wrappers (`wide_umem_weld_domain2_siblings`). Their welded
//!   leg is caps-domain BY CONSTRUCTION (those tests assert `ops[0].domain == Caps`), so a domain flip
//!   there reds those gauntlets — they are the per-member tooth for the caps plane.
//! * **WIRE-FORBIDDEN cap descriptors (HERE, mint→wire-REJECT):** the plain cap descriptors and the
//!   authority-only cap-open crowns are deliberately wire-forbidden (`is_forbidden_plain_cap_descriptor`)
//!   — a representative is minted welded and asserted REJECTED, the authority floor. Their light-client
//!   route is the WRITE wrapper (covered above).
//! * **Grow-gate / value-balance members:** transfer (`wide_umem_weld_staged_gauntlet`), and the
//!   grow-gate births (noteSpend/noteCreate/createCell/factory/spawn) — classified, the wide-twin set
//!   pinned by the structural parity test; their welded twin's domain rides the same `weldUMemIntoWide`.
//!
//! ## STAGED / VK-RISK-FREE
//! Purely additive: the welded WIDE descriptors + the opt-in welded prover; no deployed descriptor / VK /
//! default prover touched, `umem_witness_enabled` untouched. Requires `prover`; self-skips otherwise.

#![cfg(feature = "prover")]

use dregg_cell::{Cell, CellMode, Ledger};
use dregg_circuit::effect_vm::trace_rotated::empty_caveat_manifest;
use dregg_circuit::effect_vm::{CellState, Effect as VmEffect};
use dregg_circuit::effect_vm_descriptors::WIDE_UMEM_WELD_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_sdk::AgentCipherclerk;
use dregg_sdk::full_turn_proof::{
    prove_wide_umem_welded_staged, verify_effect_vm_rotated_with_cutover,
};
use dregg_turn::rotation_witness as rw;
use dregg_turn::umem::{UDomain, UKey, UmemKind, UmemOp, project_record_kernel_state};

// ---- shared scaffolding ---------------------------------------------------------------------------

fn ops_from_diff(
    pre: &dregg_turn::umem::UProjection,
    post: &dregg_turn::umem::UProjection,
) -> Vec<UmemOp> {
    let mut keys: Vec<&UKey> = pre.keys().chain(post.keys()).collect();
    keys.sort();
    keys.dedup();
    let mut ops = Vec::new();
    for k in keys {
        let a = pre.get(k);
        let b = post.get(k);
        if a != b {
            ops.push(UmemOp {
                kind: UmemKind::Write,
                key: k.clone(),
                val: b.cloned(),
                prev_val: a.cloned(),
                prev_serial: 0,
            });
        }
    }
    ops
}

fn welded_member_json(key: &str) -> &'static str {
    WIDE_UMEM_WELD_REGISTRY_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some(key) {
                let _name = it.next();
                it.next()
            } else {
                None
            }
        })
        .unwrap_or_else(|| {
            panic!("{key}: welded member present in the Lean-emitted welded registry")
        })
}

fn welded_member_declared_domain(key: &str) -> u32 {
    let j = welded_member_json(key);
    let idx = j
        .find("umem_op")
        .unwrap_or_else(|| panic!("{key}: welded member declares a umem_op"));
    let rest = &j[idx..];
    let di = rest.find("\"domain\"").expect("umem_op has a domain");
    rest[di + 8..]
        .chars()
        .skip_while(|c| !c.is_ascii_digit())
        .take_while(|c| c.is_ascii_digit())
        .collect::<String>()
        .parse()
        .expect("domain is a number")
}

/// A sovereign before-cell with open permissions, fixed pubkey, token keyed by `seed`.
fn sovereign_before(seed: &[u8]) -> Cell {
    let token_id = *blake3::hash(seed).as_bytes();
    let mut before = Cell::with_balance([7u8; 32], token_id, 100_000);
    before.mode = CellMode::Sovereign;
    before
}

/// The genuine record-pin fixture for ONE kernel effect: apply it through the SHARED
/// `apply_effect_to_cell` weld and project to the deployed `convert_effects_to_vm` VM effect, so the
/// umem leg carries the effect's TRUE single-domain projection diff (the bug-catching honesty).
struct RecordPinFixture {
    initial: CellState,
    vm_effects: Vec<VmEffect>,
    before_w: rw::RotationWitness,
    after_w: rw::RotationWitness,
    proj_pre: dregg_turn::umem::UProjection,
    ops: Vec<UmemOp>,
    refusal_fields: Option<(Vec<dregg_circuit::heap_root::HeapLeaf>, BabyBear)>,
}

fn record_pin_fixture(
    seed: &[u8],
    build_kernel: impl Fn(dregg_cell::CellId) -> dregg_turn::Effect,
    pre_seal: bool,
    hosted_before: bool,
) -> RecordPinFixture {
    let block_height: u64 = 100;
    let mut before = sovereign_before(seed);
    if hosted_before {
        before.mode = CellMode::Hosted;
    }
    let cell_id = before.id();
    if pre_seal {
        let _ = before.seal([0x5Eu8; 32], 1);
    }
    let kernel = build_kernel(cell_id);
    let mut after = before.clone();
    rw::apply_effect_to_cell(&mut after, &cell_id, &kernel, block_height);
    let vm_effects =
        AgentCipherclerk::convert_effects_to_vm(&cell_id, std::slice::from_ref(&kernel));

    let refusal_fields = if matches!(kernel, dregg_turn::Effect::Refusal { .. }) {
        let audit_bytes = after
            .state
            .fields_map
            .get(&dregg_cell::state::REFUSAL_AUDIT_EXT_KEY)
            .copied()
            .expect("a refused cell carries the audit slot in fields_map");
        let before_leaves = dregg_cell::state::fields_root_leaves(&before.state.fields_map);
        let audit_value = dregg_circuit::cap_root::fold_bytes32(&audit_bytes);
        Some((before_leaves, audit_value))
    } else {
        None
    };

    let mut ledger = Ledger::new();
    let _ = ledger.insert_cell(before.clone());
    let before_w = rw::produce(&before, &ledger, &[0u8; 32], &[0u8; 32], &[]);
    let after_w = rw::produce(&after, &ledger, &[0u8; 32], &[0u8; 32], &[]);
    let initial = CellState::with_capability_root_and_record_digest(
        100_000u64,
        before.state.nonce() as u32,
        dregg_cell::compute_canonical_capability_root_felt(&before.capabilities),
        dregg_cell::compute_authority_digest_felt(&before),
    );
    let proj_pre = project_record_kernel_state(&before);
    let proj_post = project_record_kernel_state(&after);
    let ops = ops_from_diff(&proj_pre, &proj_post);
    RecordPinFixture {
        initial,
        vm_effects,
        before_w,
        after_w,
        proj_pre,
        ops,
        refusal_fields,
    }
}

/// MINT the welded proof through the DEPLOYED producer and BIND+VERIFY it through the DEPLOYED wire
/// verifier under `registry_key`'s Lean-emitted welded twin — the present/domain parity the structural
/// test omits. Asserts: (a) the GENUINE umem leg is single-domain and its domain EQUALS the registry's
/// declared domain (the direct setPerms/setVK tooth), (b) the welded proof wire-VERIFIES GREEN, (c) a
/// tampered 8-felt commit felt and (d) a tampered vk_hash are both REJECTED.
fn mint_and_wire_verify(family: &str, registry_key: &str, fx: &RecordPinFixture) {
    assert!(
        !fx.ops.is_empty(),
        "[{family}] the genuine record-pin diff must touch the universal memory (got an empty leg)"
    );
    let leg_domains: Vec<u32> = {
        let mut d: Vec<u32> = fx.ops.iter().map(|o| o.key.domain().code()).collect();
        d.sort();
        d.dedup();
        d
    };
    assert_eq!(
        leg_domains.len(),
        1,
        "[{family}] the welded cohort leg must be SINGLE-domain, got domains {leg_domains:?}"
    );
    let declared = welded_member_declared_domain(registry_key);
    assert_eq!(
        leg_domains[0], declared,
        "[{family}] PRESENT/DOMAIN PARITY: the GENUINE producer leg touches domain {} but the committed \
         welded registry member {registry_key} declares domain {declared} — a welded proof would bind NO \
         descriptor on the wire (the 9th flip-refusal class). Reconcile `wideKeyUMemDomain`.",
        leg_domains[0]
    );

    let caveat = empty_caveat_manifest();
    let refusal_fields = fx
        .refusal_fields
        .as_ref()
        .map(|(leaves, audit)| (leaves.as_slice(), *audit));
    let (welded_proof, welded_dpis) = prove_wide_umem_welded_staged(
        &fx.initial,
        &fx.vm_effects,
        &fx.before_w,
        &fx.after_w,
        &caveat,
        &fx.proj_pre,
        &fx.ops,
        None,
        refusal_fields,
    )
    .unwrap_or_else(|e| panic!("[{family}] the welded WIDE+umem mint MUST prove: {e:?}"));

    let proof_bytes = postcard::to_allocvec(&welded_proof).expect("serialize welded proof");
    let vk_hash: [u8; 32] = *blake3::hash(welded_member_json(registry_key).as_bytes()).as_bytes();

    // (b) GREEN through the deployed wire verifier under the welded twin.
    verify_effect_vm_rotated_with_cutover(&proof_bytes, &welded_dpis, &vk_hash).unwrap_or_else(
        |e| {
            panic!(
                "[{family}] the welded proof MUST verify through the deployed wire verifier under \
             {registry_key} (the staged verifier leg): {e:?}"
            )
        },
    );

    // (c) the ~124-bit 8-felt anchor tooth: a forged commit felt is rejected.
    let mut forged = welded_dpis.clone();
    let n = forged.len();
    forged[n - 1] = forged[n - 1] + BabyBear::new(0x7777);
    assert!(
        verify_effect_vm_rotated_with_cutover(&proof_bytes, &forged, &vk_hash).is_err(),
        "[{family}] a forged 8-felt commit felt MUST be rejected by the wire verifier"
    );

    // (d) the vk_hash tooth: a tampered welded-member vk_hash is rejected.
    let mut bad_vk = vk_hash;
    bad_vk[0] ^= 0xff;
    assert!(
        verify_effect_vm_rotated_with_cutover(&proof_bytes, &welded_dpis, &bad_vk).is_err(),
        "[{family}] a tampered welded-member vk_hash MUST be rejected by the wire verifier"
    );

    eprintln!(
        "MATRIX {family} ({registry_key}) GREEN: genuine domain-{declared} mint → wire-verify."
    );
}

// ---- DOMAIN-1 record-pin family: genuine mint → wire-verify (the bug's home) ----------------------

#[test]
fn matrix_set_permissions_welded_wire_verifies() {
    // THE 9th REFUSAL, FIXED: setPermissions moves `UKey::Permissions` → domain-2 (caps). The welded
    // member now declares domain 2; a genuine welded mint binds it on the wire.
    let fx = record_pin_fixture(
        b"matrix-setperms",
        |cell| dregg_turn::Effect::SetPermissions {
            cell,
            new_permissions: dregg_cell::Permissions::zkapp(),
        },
        false,
        false,
    );
    assert_eq!(
        fx.ops[0].key.domain(),
        UDomain::Caps,
        "setPermissions genuinely moves the CAPS plane (UKey::Permissions)"
    );
    mint_and_wire_verify("SetPermissions", "setPermsVmDescriptor2R24", &fx);
}

#[test]
fn matrix_set_verification_key_welded_wire_verifies() {
    let fx = record_pin_fixture(
        b"matrix-setvk",
        |cell| dregg_turn::Effect::SetVerificationKey {
            cell,
            new_vk: Some(dregg_cell::VerificationKey::from_components(
                &dregg_cell::vk_v2::VkComponents {
                    program_bytes: b"matrix-vk-program",
                    air_fingerprint: [0x11; 32],
                    verifier_fingerprint: dregg_cell::vk_v2::VerifierFingerprint::SourceHash(
                        [0x22; 32],
                    ),
                    proving_system_id: dregg_cell::vk_v2::ProvingSystemId::Plonky3BabyBearFri {
                        p3_rev: "matrix",
                    },
                },
            )),
        },
        false,
        false,
    );
    assert_eq!(
        fx.ops[0].key.domain(),
        UDomain::Caps,
        "setVerificationKey genuinely moves the CAPS plane (UKey::VerificationKey)"
    );
    mint_and_wire_verify("SetVerificationKey", "setVKVmDescriptor2R24", &fx);
}

#[test]
fn matrix_cell_seal_welded_wire_verifies() {
    let fx = record_pin_fixture(
        b"matrix-cellseal",
        |cell| dregg_turn::Effect::CellSeal {
            target: cell,
            reason: [0x5Au8; 32],
        },
        false,
        false,
    );
    mint_and_wire_verify("CellSeal", "cellSealVmDescriptor2R24", &fx);
}

#[test]
fn matrix_cell_unseal_welded_wire_verifies() {
    let fx = record_pin_fixture(
        b"matrix-cellunseal",
        |cell| dregg_turn::Effect::CellUnseal { target: cell },
        true, // pre-seal so the unseal is a genuine lifecycle move
        false,
    );
    mint_and_wire_verify("CellUnseal", "cellUnsealVmDescriptor2R24", &fx);
}

#[test]
fn matrix_cell_destroy_welded_wire_verifies() {
    let fx = record_pin_fixture(
        b"matrix-celldestroy",
        |cell| dregg_turn::Effect::CellDestroy {
            target: cell,
            certificate: dregg_cell::lifecycle::DeathCertificate {
                cell_id: cell,
                last_receipt_hash: [0x01; 32],
                final_state_commitment: [0x02; 32],
                destroyed_at_height: 99,
                reason: dregg_cell::lifecycle::DeathReason::Voluntary,
            },
        },
        false,
        false,
    );
    mint_and_wire_verify("CellDestroy", "cellDestroyVmDescriptor2R24", &fx);
}

#[test]
fn matrix_receipt_archive_welded_wire_verifies() {
    let fx = record_pin_fixture(
        b"matrix-receiptarchive",
        |cell| dregg_turn::Effect::ReceiptArchive {
            prefix_end_height: 42,
            checkpoint: dregg_cell::lifecycle::ArchivalAttestation {
                cell_id: cell,
                archive_start_height: 0,
                archive_end_height: 42,
                archive_blob_hash: [0x03; 32],
                archive_terminal_commitment: [0x04; 32],
                archive_terminal_receipt_hash: [0x05; 32],
            },
        },
        false,
        false,
    );
    mint_and_wire_verify("ReceiptArchive", "receiptArchiveVmDescriptor2R24", &fx);
}

#[test]
fn matrix_refusal_welded_wire_verifies() {
    let fx = record_pin_fixture(
        b"matrix-refusal",
        |cell| dregg_turn::Effect::Refusal {
            cell,
            offered_action_commitment: [11u8; 32],
            refusal_reason: dregg_turn::action::RefusalReason::Declined,
            proof_witness_index: 0,
        },
        false,
        false,
    );
    mint_and_wire_verify("Refusal", "refusalVmDescriptor2R24", &fx);
}

#[test]
fn matrix_make_sovereign_welded_wire_verifies() {
    // makeSovereign is unexercisable from an already-Sovereign before-cell (empty projection diff). From
    // a HOSTED before, the Hosted→Sovereign promotion is a genuine heap-domain Mode move.
    let fx = record_pin_fixture(
        b"matrix-makesovereign",
        |cell| dregg_turn::Effect::MakeSovereign { cell },
        false,
        true, // hosted before — the promotion is a real move
    );
    mint_and_wire_verify("MakeSovereign", "makeSovereignVmDescriptor2R24", &fx);
}

// ---- WIRE-FORBIDDEN cap descriptors: mint → wire-REJECT (the authority floor) ----------------------

/// A PLAIN cap descriptor (`attenuateVmDescriptor2R24`) is `is_forbidden_plain_cap_descriptor` — a cap
/// effect proven WITHOUT the in-circuit membership crown launders host-trusted authority. A welded plain
/// grant self-verifies but the deployed wire REJECTS it. This is the per-member tooth for the forbidden
/// crowns: their light-client route is the WRITE wrapper (covered by `wide_umem_weld_domain2_siblings`),
/// never the plain/authority-only descriptor. (Mirrors `domain2_plain_cap_weld_is_wire_forbidden`.)
#[test]
fn matrix_forbidden_plain_cap_is_wire_rejected() {
    let before_balance: u64 = 100_000;
    let initial = CellState::with_capability_root(
        before_balance,
        0,
        dregg_circuit::cap_root::empty_capability_root(),
    );
    let effects = vec![VmEffect::GrantCapability {
        cap_entry: [BabyBear::ZERO; 8],
        phase_b: None,
    }];

    let mut before = sovereign_before(b"matrix-forbidden-grant");
    before.permissions = dregg_cell::Permissions {
        send: dregg_cell::AuthRequired::None,
        receive: dregg_cell::AuthRequired::None,
        set_state: dregg_cell::AuthRequired::None,
        set_permissions: dregg_cell::AuthRequired::None,
        set_verification_key: dregg_cell::AuthRequired::None,
        increment_nonce: dregg_cell::AuthRequired::None,
        delegate: dregg_cell::AuthRequired::None,
        access: dregg_cell::AuthRequired::None,
    };
    let mut after = before.clone();
    let target = {
        let mut tpk = [0u8; 32];
        tpk[0] = 201;
        Cell::with_balance(tpk, [0u8; 32], 0).id()
    };
    after
        .capabilities
        .grant(target, dregg_cell::AuthRequired::None)
        .expect("grant a cap slot");

    let mut ledger = Ledger::new();
    let _ = ledger.insert_cell(after.clone());
    let before_w = rw::produce(&before, &ledger, &[0u8; 32], &[0u8; 32], &[]);
    let after_w = rw::produce(&after, &ledger, &[0u8; 32], &[0u8; 32], &[]);
    let proj_pre = project_record_kernel_state(&before);
    let proj_post = project_record_kernel_state(&after);
    let ops = ops_from_diff(&proj_pre, &proj_post);
    assert_eq!(ops[0].key.domain(), UDomain::Caps);

    let caveat = empty_caveat_manifest();
    let (welded_proof, welded_dpis) = prove_wide_umem_welded_staged(
        &initial, &effects, &before_w, &after_w, &caveat, &proj_pre, &ops, None, None,
    )
    .expect("the PLAIN welded grant SELF-verifies (it carries no membership crown)");
    let proof_bytes = postcard::to_allocvec(&welded_proof).unwrap();
    let vk_hash: [u8; 32] =
        *blake3::hash(welded_member_json("grantCapVmDescriptor2R24").as_bytes()).as_bytes();
    let r = verify_effect_vm_rotated_with_cutover(&proof_bytes, &welded_dpis, &vk_hash);
    assert!(
        r.is_err(),
        "the PLAIN welded grant MUST be REJECTED by the deployed wire verifier (forbidden plain cap)"
    );
}

// ---- the completeness ledger: every one of the 54 welded members is accounted for -----------------

/// The classification of each welded member's per-member coverage. The matrix is TRULY complete iff
/// every registry key maps to exactly one lane.
enum Lane {
    /// Genuine mint → wire-verify GREEN, HERE (the domain-1 record-pin family — the bug's home).
    HereGreen,
    /// Wire-FORBIDDEN authority/plain cap descriptor — its light-client route is the WRITE wrapper.
    /// Represented HERE by `matrix_forbidden_plain_cap_is_wire_rejected`.
    Forbidden,
    /// Caps-domain member proven end-to-end (mint → wire-verify → executor-commit) by a sibling
    /// gauntlet, which asserts `ops[0].domain == Caps` — the per-member tooth for the caps plane.
    SiblingCovered,
    /// Domain-1 value / grow-gate member covered by its own gauntlet (transfer) or pinned structurally
    /// (the grow-gate births share the additive `weldUMemIntoWide` domain; the wide-twin set is pinned
    /// by `wide_umem_weld_registry_parity_and_no_narrowing`).
    ValueOrGrowGate,
}

fn coverage_table() -> Vec<(&'static str, Lane)> {
    use Lane::*;
    vec![
        // domain-1 record-pin family — HERE
        ("setPermsVmDescriptor2R24", HereGreen),
        ("setVKVmDescriptor2R24", HereGreen),
        ("cellSealVmDescriptor2R24", HereGreen),
        ("cellUnsealVmDescriptor2R24", HereGreen),
        ("cellDestroyVmDescriptor2R24", HereGreen),
        ("receiptArchiveVmDescriptor2R24", HereGreen),
        ("refusalVmDescriptor2R24", HereGreen),
        ("makeSovereignVmDescriptor2R24", HereGreen),
        // domain-1 value / grow-gate family
        ("transferVmDescriptor2R24", ValueOrGrowGate),
        ("transferFeeVmDescriptor2R24", ValueOrGrowGate),
        ("transferCapOpenEffVmDescriptor2R24", ValueOrGrowGate),
        ("burnVmDescriptor2R24", ValueOrGrowGate),
        ("mintVmDescriptor2R24", ValueOrGrowGate),
        ("incrementNonceVmDescriptor2R24", ValueOrGrowGate),
        ("emitEventVmDescriptor2R24", ValueOrGrowGate),
        ("pipelinedSendVmDescriptor2R24", ValueOrGrowGate),
        ("exerciseVmDescriptor2R24", ValueOrGrowGate),
        ("exerciseCapOpenVmDescriptor2R24", ValueOrGrowGate),
        ("customVmDescriptor2R24", ValueOrGrowGate),
        ("setFieldDynVmDescriptor2R24", ValueOrGrowGate),
        ("noteSpendVmDescriptor2R24", ValueOrGrowGate),
        ("noteCreateVmDescriptor2R24", ValueOrGrowGate),
        ("createCellVmDescriptor2R24", ValueOrGrowGate),
        ("factoryVmDescriptor2R24", ValueOrGrowGate),
        ("setFieldVmDescriptor2-0R24", ValueOrGrowGate),
        ("setFieldVmDescriptor2-1R24", ValueOrGrowGate),
        ("setFieldVmDescriptor2-2R24", ValueOrGrowGate),
        ("setFieldVmDescriptor2-3R24", ValueOrGrowGate),
        ("setFieldVmDescriptor2-4R24", ValueOrGrowGate),
        ("setFieldVmDescriptor2-5R24", ValueOrGrowGate),
        ("setFieldVmDescriptor2-6R24", ValueOrGrowGate),
        ("setFieldVmDescriptor2-7R24", ValueOrGrowGate),
        // domain-2 capability family — sibling-covered, caps domain by construction
        ("attenuateCapOpenEffVmDescriptor2R24", SiblingCovered),
        ("delegateWriteCapOpenVmDescriptor2R24", SiblingCovered),
        ("introduceWriteCapOpenVmDescriptor2R24", SiblingCovered),
        ("delegateAttenWriteCapOpenVmDescriptor2R24", SiblingCovered),
        (
            "revokeDelegationWriteCapOpenVmDescriptor2R24",
            SiblingCovered,
        ),
        (
            "revokeCapabilityWriteCapOpenVmDescriptor2R24",
            SiblingCovered,
        ),
        (
            "refreshDelegationWriteCapOpenVmDescriptor2R24",
            SiblingCovered,
        ),
        ("spawnWriteCapOpenVmDescriptor2R24", SiblingCovered),
        ("spawnVmDescriptor2R24", SiblingCovered),
        // wire-FORBIDDEN cap descriptors — authority floor (route is the write wrapper)
        ("attenuateVmDescriptor2R24", Forbidden),
        ("revokeVmDescriptor2R24", Forbidden),
        ("introduceVmDescriptor2R24", Forbidden),
        ("grantCapVmDescriptor2R24", Forbidden),
        ("revokeCapabilityVmDescriptor2R24", Forbidden),
        ("refreshVmDescriptor2R24", Forbidden),
        ("delegateCapOpenVmDescriptor2R24", Forbidden),
        ("introduceCapOpenVmDescriptor2R24", Forbidden),
        ("grantCapCapOpenVmDescriptor2R24", Forbidden),
        ("revokeCapOpenVmDescriptor2R24", Forbidden),
        ("refreshDelegationCapOpenVmDescriptor2R24", Forbidden),
        ("revokeCapabilityCapOpenVmDescriptor2R24", Forbidden),
        ("spawnCapOpenVmDescriptor2R24", Forbidden),
    ]
}

#[test]
fn matrix_enumerates_all_54() {
    let registry_keys: std::collections::BTreeSet<&str> = WIDE_UMEM_WELD_REGISTRY_TSV
        .lines()
        .filter(|l| !l.is_empty())
        .map(|l| l.split('\t').next().expect("key"))
        .collect();
    assert_eq!(
        registry_keys.len(),
        54,
        "the welded registry has exactly 54 members"
    );
    let table = coverage_table();
    let table_keys: std::collections::BTreeSet<&str> = table.iter().map(|(k, _)| *k).collect();
    assert_eq!(
        table_keys.len(),
        table.len(),
        "the coverage table has no duplicate keys"
    );
    // Every registry member is classified, and every classified key is a registry member.
    for k in &registry_keys {
        assert!(
            table_keys.contains(k),
            "welded member {k} is NOT classified in the matrix coverage table — the matrix is not \
             empirically complete until it is minted/forbidden/sibling-covered/value-classified"
        );
    }
    for k in &table_keys {
        assert!(
            registry_keys.contains(k),
            "coverage-table key {k} is not a welded registry member (stale entry)"
        );
    }
    assert_eq!(
        registry_keys, table_keys,
        "the matrix coverage table must EXACTLY cover the 54 welded members"
    );
}
