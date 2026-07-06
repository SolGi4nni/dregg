//! # KERNEL-EFFECT-ENUM ≡ DESCRIPTOR-OR-NAMED-RESIDUAL GATE (the enum→circuit-witness blind spot).
//!
//! `producer_descriptor_coverage_gate` classifies every DEPLOYED registry member (descriptor →
//! coverage). This file closes the DUAL direction: every KERNEL `dregg_turn::Effect` variant must
//! either name a deployed light-client descriptor member that witnesses it, or carry a NAMED
//! circuit-witness residual — so a kernel verb can never silently ride the executor with NO rung
//! and NO named residual (the `effect_vm_bridge` catch-all `_ => {}` silently skips unmapped
//! variants; without this gate a new verb's missing circuit witness would be invisible).
//!
//! Two teeth:
//!   1. **Compile-time completeness** — `circuit_witness_ledger!` expands to a `match` over
//!      `dregg_turn::Effect` with NO wildcard arm. A NEW kernel Effect variant FAILS THIS BUILD
//!      until it is classified here as `Descriptor(registry key)` or `NamedResidual(reason)`.
//!   2. **Runtime grounding** — every `Descriptor` key must exist in the committed
//!      `V3_STAGED_REGISTRY_TSV` (no phantom rungs); every `NamedResidual` must carry a non-empty
//!      reason; and the residual set is pinned EXACTLY (a residual can only leave this list by
//!      gaining a descriptor rung, and can only enter it here, by name).
//!
//! The named-residual set at HEAD (all VK-affecting follow-ups, gated — see the in-enum notes in
//! `turn/src/action.rs` for `SetProgram` / `ShieldedTransfer`):
//!   * `SetProgram` — the program write is executor-applied; binding it into the turn commitment
//!     is the owed in-circuit witness (in-enum "CIRCUIT WITNESS (FOLLOW-UP)", ember-gated).
//!   * `Promise` / `Notify` — the promise-hole deposit mutates the cell's reactive registry with
//!     no descriptor rung; the hole is un-witnessed on the light-client wire.
//!   * `React` — the hole-nullifier spend is executor-enforced (double-spend gate); no descriptor
//!     rung binds the react on the light-client wire.
//!   * `ShieldedTransfer` — the executor verifies the shielded proof; binding that verification
//!     into the effect_vm descriptor is the in-enum "CIRCUIT WITNESS (named residual)" (M2 weld).
//!
//! Run: `cargo test -p dregg-circuit --test effect_enum_descriptor_residual_gate`.

use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_turn::Effect;

/// The circuit-witness status of one kernel Effect variant.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Witness {
    /// A deployed V3 registry member witnesses this verb on the light-client wire. The `&str` is
    /// a REPRESENTATIVE committed registry key (families like setField-0..7 / the cap-open routes
    /// name one member; the per-member coverage quality lives in
    /// `producer_descriptor_coverage_gate`).
    Descriptor(&'static str),
    /// NO descriptor rung exists for this verb — the executor applies it un-witnessed by a pure
    /// light client. The `&str` names the residual + its closure route (never a silent gap).
    NamedResidual(&'static str),
}

/// ONE source of truth: expands to BOTH the wildcard-free compile-time match (the build-breaking
/// tooth for a new kernel variant) AND the runtime ledger the grounding test checks.
macro_rules! circuit_witness_ledger {
    ( $( $variant:ident => $class:expr ),+ $(,)? ) => {
        /// COMPILE-TIME TOOTH: no wildcard arm. Adding a kernel `Effect` variant reds this build
        /// until the variant is classified in the ledger below.
        fn circuit_witness(e: &Effect) -> Witness {
            match e {
                $( Effect::$variant { .. } => $class, )+
            }
        }

        /// The same classification as data, for the runtime grounding checks.
        fn ledger() -> Vec<(&'static str, Witness)> {
            vec![ $( (stringify!($variant), $class), )+ ]
        }
    };
}

circuit_witness_ledger! {
    SetField              => Witness::Descriptor("setFieldVmDescriptor2-0R24"),
    Transfer              => Witness::Descriptor("transferVmDescriptor2R24"),
    GrantCapability       => Witness::Descriptor("grantCapVmDescriptor2R24"),
    RevokeCapability      => Witness::Descriptor("revokeCapabilityVmDescriptor2R24"),
    EmitEvent             => Witness::Descriptor("emitEventVmDescriptor2R24"),
    IncrementNonce        => Witness::Descriptor("incrementNonceVmDescriptor2R24"),
    CreateCell            => Witness::Descriptor("createCellVmDescriptor2R24"),
    SetPermissions        => Witness::Descriptor("setPermsVmDescriptor2R24"),
    SetVerificationKey    => Witness::Descriptor("setVKVmDescriptor2R24"),
    SetProgram            => Witness::NamedResidual(
        "in-enum CIRCUIT WITNESS follow-up (turn/src/action.rs): the program write is not bound \
         into the turn commitment; VK-affecting, ember-gated",
    ),
    NoteSpend             => Witness::Descriptor("noteSpendVmDescriptor2R24"),
    NoteCreate            => Witness::Descriptor("noteCreateVmDescriptor2R24"),
    SpawnWithDelegation   => Witness::Descriptor("spawnVmDescriptor2R24"),
    RefreshDelegation     => Witness::Descriptor("refreshVmDescriptor2R24"),
    RevokeDelegation      => Witness::Descriptor("revokeVmDescriptor2R24"),
    BridgeMint            => Witness::Descriptor("mintVmDescriptor2R24"),
    Introduce             => Witness::Descriptor("introduceVmDescriptor2R24"),
    PipelinedSend         => Witness::Descriptor("pipelinedSendVmDescriptor2R24"),
    ExerciseViaCapability => Witness::Descriptor("exerciseVmDescriptor2R24"),
    MakeSovereign         => Witness::Descriptor("makeSovereignVmDescriptor2R24"),
    CreateCellFromFactory => Witness::Descriptor("factoryVmDescriptor2R24"),
    Refusal               => Witness::Descriptor("refusalVmDescriptor2R24"),
    CellSeal              => Witness::Descriptor("cellSealVmDescriptor2R24"),
    CellUnseal            => Witness::Descriptor("cellUnsealVmDescriptor2R24"),
    CellDestroy           => Witness::Descriptor("cellDestroyVmDescriptor2R24"),
    Burn                  => Witness::Descriptor("burnVmDescriptor2R24"),
    AttenuateCapability   => Witness::Descriptor("attenuateVmDescriptor2R24"),
    ReceiptArchive        => Witness::Descriptor("receiptArchiveVmDescriptor2R24"),
    Promise               => Witness::NamedResidual(
        "promise-hole deposit mutates the reactive registry with NO descriptor rung; un-witnessed \
         on the light-client wire (VK-affecting follow-up, same family as SetProgram)",
    ),
    Notify                => Witness::NamedResidual(
        "notify deposits a promise-hole in the recipient's registry with NO descriptor rung; \
         un-witnessed on the light-client wire (VK-affecting follow-up)",
    ),
    React                 => Witness::NamedResidual(
        "react's hole-nullifier spend is executor-enforced only; NO descriptor rung binds it on \
         the light-client wire (VK-affecting follow-up)",
    ),
    Mint                  => Witness::Descriptor("supplyMintVmDescriptor2R24"),
    ShieldedTransfer      => Witness::NamedResidual(
        "in-enum CIRCUIT WITNESS named residual (turn/src/action.rs): the shielded-proof \
         verification is executor-side; binding it into the effect_vm descriptor is the \
         VK-affecting M2 weld follow-up",
    ),
}

/// The EXACT pinned residual set. A verb leaves ONLY by gaining a rung; enters ONLY by name here.
const EXPECTED_RESIDUALS: [&str; 5] = [
    "SetProgram",
    "Promise",
    "Notify",
    "React",
    "ShieldedTransfer",
];

/// The member keys of the committed V3 registry TSV (column 0).
fn registry_keys(tsv: &str) -> std::collections::BTreeSet<&str> {
    tsv.lines()
        .filter(|l| !l.is_empty())
        .map(|l| l.split('\t').next().expect("key column"))
        .collect()
}

#[test]
fn every_kernel_effect_variant_has_descriptor_or_named_residual() {
    // Fire the compile-time match on a cheap live instance so it is genuinely executed code.
    let cell = dregg_cell::Cell::with_balance([7u8; 32], [0u8; 32], 1);
    assert_eq!(
        circuit_witness(&Effect::IncrementNonce { cell: cell.id() }),
        Witness::Descriptor("incrementNonceVmDescriptor2R24"),
    );

    let rows = ledger();
    let names: std::collections::BTreeSet<&str> = rows.iter().map(|(n, _)| *n).collect();
    assert_eq!(
        names.len(),
        rows.len(),
        "duplicate variant rows in the ledger"
    );

    let keys = registry_keys(V3_STAGED_REGISTRY_TSV);
    let mut residuals: Vec<&str> = Vec::new();
    let (mut witnessed, mut named) = (0usize, 0usize);
    for (variant, w) in &rows {
        match w {
            Witness::Descriptor(key) => {
                witnessed += 1;
                assert!(
                    keys.contains(key),
                    "`{variant}` names `{key}` as its witnessing rung, but that key is NOT a \
                     committed V3 registry member — a phantom rung. Point at a real deployed \
                     member or reclassify as NamedResidual."
                );
            }
            Witness::NamedResidual(reason) => {
                named += 1;
                assert!(
                    !reason.is_empty(),
                    "`{variant}`: a named residual needs a non-empty reason"
                );
                residuals.push(variant);
            }
        }
    }

    let expected: std::collections::BTreeSet<&str> = EXPECTED_RESIDUALS.into_iter().collect();
    let actual: std::collections::BTreeSet<&str> = residuals.iter().copied().collect();
    assert_eq!(
        actual, expected,
        "the un-witnessed kernel-verb set drifted. A verb leaves this set ONLY by gaining a \
         deployed descriptor rung (then move it to Descriptor(key) here); a verb enters ONLY \
         with a named reason. Never silently."
    );

    eprintln!(
        "=== kernel Effect → circuit-witness gate: {} variants, {witnessed} descriptor-witnessed, \
         {named} NAMED residuals ({:?}) ===",
        rows.len(),
        residuals,
    );
}
