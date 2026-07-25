//! # KERNEL-EFFECT-ENUM ≡ DESCRIPTOR-OR-NAMED-RESIDUAL GATE (the enum→circuit-witness blind spot).
//!
//! `producer_descriptor_coverage_gate` classifies every DEPLOYED registry member (descriptor →
//! coverage). This file closes the DUAL direction: every KERNEL `dregg_turn::Effect` variant must
//! either name a deployed light-client descriptor member that witnesses it, or carry a NAMED
//! circuit-witness residual — so a kernel verb can never silently ride the executor with NO rung
//! and NO named residual (the `effect_vm_bridge` catch-all `_ => {}` silently skips unmapped
//! variants; without this gate a new verb's missing circuit witness would be invisible).
//!
//! Four teeth:
//!   1. **Compile-time completeness** — `circuit_witness_ledger!` expands to a `match` over
//!      `dregg_turn::Effect` with NO wildcard arm. A NEW kernel Effect variant FAILS THIS BUILD
//!      until it is classified here as `Descriptor(registry key)` / `NamedResidual(reason)` /
//!      `RefusedResidual(reason)`.
//!   2. **Runtime grounding** — every `Descriptor` key must exist in the committed
//!      `V3_STAGED_REGISTRY_TSV` (no phantom rungs); every residual must carry a non-empty
//!      reason; and both residual sets are pinned EXACTLY (a residual can only leave its list by
//!      gaining a descriptor rung, and can only enter it here, by name).
//!   3. **Rung injectivity** — two kernel verbs may NOT claim the SAME registry key. Aliasing a
//!      sibling's rung is how a verb gets misfiled as witnessed: `CreateHybridCell` looks exactly
//!      like `CreateCell` plus a field, and pointing it at `createCellVmDescriptor2R24` would have
//!      been a one-word lie in a security-relevant table (that descriptor's create_hash models the
//!      classical birth; it says nothing about a PQ anchor).
//!   4. **The refusal is EXECUTED, not asserted** —
//!      `refused_residuals_are_refused_by_the_live_projection` runs the production
//!      `try_convert_turn_effects_to_vm` over a turn carrying each `RefusedResidual` verb
//!      (top-level AND nested inside `ExerciseViaCapability`) and requires a by-name `Err`; and it
//!      requires a `NamedResidual` and a `Descriptor` control to project `Ok`. So "fail-closed" is
//!      a checked fact here, not prose.
//!
//! ## The two residual KINDS (they are not the same posture, and must not read as if they were)
//!
//! * `NamedResidual` — no rung, and the checked projection ACCEPTS the turn: the verb is simply
//!   dropped on the floor by the bridge's `_ => {}`. It rides a real, verifying cohort proof that
//!   says nothing about it. This is the worse posture: the proof is issued and is silent.
//! * `RefusedResidual` — no rung, and the checked projection REFUSES the turn BY NAME
//!   (`EffectVmProjectionError::PqIdentityEffect`). No proof-carrying turn can contain the verb at
//!   all. The verb is executor-only, but a verifier is never handed a proof that pretends
//!   otherwise. Fail-closed, and it is the correct posture for a verb whose whole authority plane
//!   has no AIR row.
//!
//! The `NamedResidual` (silent-on-the-wire) set at HEAD (all VK-affecting follow-ups, gated — see the in-enum notes in
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
//! ## ⚠ WOUND — the PQ identity authority plane has NO AIR row (coverage, not narrowing)
//!
//! `CreateHybridCell` and `RotatePqIdentity` are the two verbs that install and advance a cell's
//! POST-QUANTUM authority anchor (`CellPqIdentity { key_epoch, ml_dsa_key_commitment }`). Neither
//! has a descriptor. Stated plainly, because this is a security-relevant claim:
//!
//! **What the executor does.** `apply_create_hybrid_cell` / `apply_rotate_pq_identity`
//! (`turn/src/executor/apply.rs`) verify an ML-DSA-65 possession signature over
//! `pq::cell_pq_{creation,rotation}_message`, then call `Cell::{install,rotate}_pq_identity`
//! (`cell/src/cell.rs:656` / `:674`), which enforce epoch-zero-at-birth, `expected_epoch` equality,
//! new-key-differs, and exactly-+1 with overflow refusal. Every one of those checks is TRUSTED
//! RUST. None of them is a constraint.
//!
//! **What the anchor is bound into.** The anchor IS committed state: it is absorbed by
//! `compute_canonical_state_commitment` (`cell/src/commitment.rs:223`) and by the 8-felt
//! `authority_residue_bytes` (`:978`) that the rotated descriptors' authority digest folds. So it
//! cannot be omitted or substituted without moving the committed root. **Binding is not
//! constraining**: the root moves, and no circuit says the move was a LEGAL rotation.
//!
//! **What a light client learns about such a turn: nothing, and it is told so.** Because the
//! checked projection refuses these verbs, no EffectVM cohort proof over such a turn exists. A
//! verifier does not learn that the possession signature verified, that the epoch advanced by
//! exactly one, that `expected_epoch` matched the committed epoch, or that the new key differs
//! from the retired one. It learns only what the executor asserts. The claims the turn machinery
//! does make — descriptor refinement, the per-turn fold, cohort-run verification — quantify over
//! the projected VM effect rows, and there is no row here to quantify over.
//!
//! **Why that matters more here than for a missing rung elsewhere.** The committed ML-DSA key is
//! the root of post-quantum authority: under `require_pq` (ON by default at node admission —
//! `docs/ASSESS-require-pq-enforcement.md`) possession of the key committed in `pq_identity` is
//! what authorizes a turn at all. An executor that installs or rotates an anchor to a key of its
//! choosing yields state that every downstream proof then builds on faithfully. So the PQ half's
//! authority is exactly as strong as trust in the executor — it buys no verifier-checkable
//! authority beyond the classical trust boundary until this plane is in-circuit.
//!
//! **What already exists toward closing it.** A Lean-authored, Lean-PROVEN rotation authority
//! descriptor — `dregg-pq-identity-rotation::v1`
//! (`metatheory/Dregg2/Circuit/Emit/PqIdentityAuthorityEmit.lean`, semantics
//! `satisfied_implies_exact_rotation`; trace_width 127 / 108 PIs / 120 constraints, parsed by the
//! production IR2 parser in `circuit/tests/pq_identity_authority_descriptor.rs`). It is NOT a
//! member of `V3_STAGED_REGISTRY_TSV`, has no producer and no committed VK, and its own header
//! says parsing it "does not make the row deployable and does not discharge either ML-DSA premise".
//! So `RotatePqIdentity` is a residual WITH a proven-but-undeployed rung; `CreateHybridCell` has no
//! rung at all, not even staged. Deploying the rotation row (registry membership + producer + VK
//! epoch) and authoring the birth row is what moves either verb out of this set.
//!
//! **Where this wound is catalogued.** NOT `docs/WOUND-felt-width-boundaries-2026-07-19.md` — that
//! catalogues 32-byte digests NARROWED to ~31 bits at a security boundary, and nothing here is
//! narrowed (the anchor rides its full 32-byte key commitment into the 8-felt authority digest).
//! This is a COVERAGE gap: a kernel verb with no AIR row. Its live record is the pinned
//! `EXPECTED_REFUSED_RESIDUALS` set below (which cannot drift silently) plus
//! `docs/ASSESS-require-pq-enforcement.md` §6, the PQ posture doc — which previously assessed PQ
//! admission enforcement without noting that neither PQ verb is in-circuit.
//!
//! ## Scope of this gate (what it does NOT catch)
//!
//! This is an integration test in `circuit/tests/`, not a `#[cfg(test)] mod tests` inside the
//! crate, so it is not skippable by the lib's own test config — but it still cannot fire if
//! `dregg-circuit` or `dregg-turn` fails to build. Compile-breakage of those crates masks every
//! tooth here; the umbrella build is the thing that catches that, not this file.
//!
//! A `Descriptor(key)` claim here is grounded (the key is a committed registry member, and no two
//! verbs share one) but this file does NOT check that the bridge still EMITS a row for that verb —
//! a `Descriptor`-classified verb whose bridge arm was removed or narrowed would go silent while
//! this table still claimed a rung. That direction is
//! `tests/src/every_variant_roundtrip.rs::every_effect_variant_round_trips_through_projection`
//! (every variant projects to a non-NoOp sequence, or is refused BY NAME as an explicitly listed
//! out-of-AIR-domain variant — its `VM_DOMAIN_EXCLUSIONS` is the same two verbs as
//! `EXPECTED_REFUSED_RESIDUALS` here, over the SDK producer-side twin).
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
    /// NO descriptor rung exists for this verb AND the checked projection accepts the turn: the
    /// executor applies it while a verifying cohort proof stays silent about it. The `&str` names
    /// the residual + its closure route (never a silent gap in the LEDGER, even though the verb is
    /// silent on the wire).
    NamedResidual(&'static str),
    /// NO descriptor rung exists AND the production checked projection
    /// (`dregg_turn::executor::try_convert_turn_effects_to_vm`) REFUSES the turn BY NAME, so no
    /// proof-carrying turn can contain the verb. Executor-only, fail-closed. Checked live by
    /// `refused_residuals_are_refused_by_the_live_projection`.
    RefusedResidual(&'static str),
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
    // Custom (added 2026-07-16): the turn lane's "THE DOOR" commit made `Effect::Custom` REACHABLE and
    // welded it — before it, `dregg_turn::action::Effect` had NO Custom variant, so
    // `convert_turn_effects_to_vm` could never emit a `VmEffect::Custom` row and
    // `enforce_custom_proof_count_committed` computed committed=0 for EVERY turn (any turn carrying
    // custom_program_proofs was rejected `CustomProofCountMismatch{wire:n,committed:0}`). The carrier was
    // real and general but had no door. It is a DESCRIPTOR, not a residual: the Custom row publishes
    // `custom_proof_pi_commitment(public_inputs)` and the per-turn fold binds it to the sub-proof leaf —
    // a lie there is caught by the fold (no backing sub-proof => no aggregate root) or by the sub-proof's
    // own registry verify; a custom transition with no proof/weld/store is REFUSED
    // (`RequiresProofCarryingTurn`), never a silent no-op. Deployed as `dregg-effectvm-custom-v1`
    // (`descriptor_by_name.rs:144`).
    Custom                => Witness::Descriptor("customVmDescriptor2R24"),
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
    // ── The PQ identity authority plane (classified 2026-07-25; the verbs landed at
    //    `turn/src/action.rs:1569,1582` without this decision being made, which is exactly what
    //    tooth 1 exists to stop). See this file's WOUND section for the full statement of what a
    //    verifier does and does not learn. In brief, per verb:
    //
    // CreateHybridCell commits an epoch-zero `CellPqIdentity` at cell birth
    // (`apply.rs::apply_create_hybrid_cell` → `Cell::with_hybrid_balance` → `install_pq_identity`,
    // `cell/src/cell.rs:656`) after verifying an ML-DSA-65 possession signature. NOT a Descriptor:
    // its sibling `CreateCell` has `createCellVmDescriptor2R24`, but that rung models the CLASSICAL
    // birth — its create_hash carries no PQ anchor — so claiming it here would be a false entry,
    // not a shortcut (tooth 3 now also blocks the aliasing mechanically). There is no staged PQ
    // birth descriptor either.
    CreateHybridCell      => Witness::RefusedResidual(
        "PQ identity authority plane has NO AIR row: the epoch-zero ML-DSA anchor install is \
         executor-only (ML-DSA-65 possession verified in trusted Rust, `apply.rs`). `CreateCell`'s \
         rung models the classical birth and does NOT cover the anchor. FAIL-CLOSED: the checked \
         EffectVM projection refuses the turn by name, so no proof-carrying turn can contain it. \
         Closure = a PQ birth descriptor (none exists, not even staged) + registry membership + VK",
    ),
    // RotatePqIdentity advances the committed anchor exactly one epoch
    // (`apply.rs::apply_rotate_pq_identity` → `Cell::rotate_pq_identity`, `cell/src/cell.rs:674`):
    // action-target equality, live target, `expected_epoch` match, new-key-differs, +1 with
    // overflow refusal, and an ML-DSA-65 possession signature by the NEW key — all trusted Rust.
    // A Lean-PROVEN authority descriptor EXISTS (`dregg-pq-identity-rotation::v1`,
    // `PqIdentityAuthorityEmit.satisfied_implies_exact_rotation`) but is NOT a V3 registry member,
    // has no producer and no committed VK — a rung on paper, not on the wire. `turn/src/umem.rs`
    // says the same thing from the memory side: the anchor is "outside the current
    // universal-memory key planes", and the bridge "refuses to claim a proved RotatePqIdentity row
    // until that authority plane exists".
    RotatePqIdentity      => Witness::RefusedResidual(
        "PQ identity authority plane has NO DEPLOYED AIR row: the epoch ratchet + possession check \
         are executor-only. A Lean-proven rotation descriptor exists staged \
         (`dregg-pq-identity-rotation::v1`, satisfied_implies_exact_rotation) but is NOT in \
         V3_STAGED_REGISTRY_TSV, has no producer and no committed VK. FAIL-CLOSED: the checked \
         EffectVM projection refuses the turn by name. Closure = deploy that row (registry + \
         producer + VK epoch) and discharge the ML-DSA premises",
    ),
}

/// The EXACT pinned SILENT-residual set: no rung, and the projection accepts the turn anyway.
/// A verb leaves ONLY by gaining a rung; enters ONLY by name here.
const EXPECTED_RESIDUALS: [&str; 5] = [
    "SetProgram",
    "Promise",
    "Notify",
    "React",
    "ShieldedTransfer",
];

/// The EXACT pinned REFUSED-residual set: no rung, and the checked projection refuses by name.
/// A verb leaves ONLY by gaining a deployed rung (at which point the projection must stop refusing
/// it and `refused_residuals_are_refused_by_the_live_projection` reds until this list is updated).
const EXPECTED_REFUSED_RESIDUALS: [&str; 2] = ["CreateHybridCell", "RotatePqIdentity"];

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
    let mut silent: Vec<&str> = Vec::new();
    let mut refused: Vec<&str> = Vec::new();
    // key -> the verb that already claimed it (rung injectivity).
    let mut claimed: std::collections::BTreeMap<&str, &str> = std::collections::BTreeMap::new();
    let mut witnessed = 0usize;
    for (variant, w) in &rows {
        match w {
            Witness::Descriptor(key) => {
                witnessed += 1;
                assert!(
                    keys.contains(key),
                    "`{variant}` names `{key}` as its witnessing rung, but that key is NOT a \
                     committed V3 registry member — a phantom rung. Point at a real deployed \
                     member or reclassify as a residual."
                );
                if let Some(other) = claimed.insert(key, variant) {
                    panic!(
                        "`{variant}` and `{other}` BOTH claim rung `{key}`. Two kernel verbs \
                         cannot be witnessed by one registry member: whichever verb the rung was \
                         not authored for is unconstrained by it, and this table would be \
                         asserting a circuit that does not exist for it. Point at that verb's own \
                         deployed member, or classify it as a residual."
                    );
                }
            }
            Witness::NamedResidual(reason) => {
                assert!(
                    !reason.is_empty(),
                    "`{variant}`: a named residual needs a non-empty reason"
                );
                silent.push(variant);
            }
            Witness::RefusedResidual(reason) => {
                assert!(
                    !reason.is_empty(),
                    "`{variant}`: a named residual needs a non-empty reason"
                );
                refused.push(variant);
            }
        }
    }

    let expected_silent: std::collections::BTreeSet<&str> =
        EXPECTED_RESIDUALS.into_iter().collect();
    let actual_silent: std::collections::BTreeSet<&str> = silent.iter().copied().collect();
    assert_eq!(
        actual_silent, expected_silent,
        "the SILENTLY un-witnessed kernel-verb set drifted. A verb leaves this set ONLY by gaining \
         a deployed descriptor rung (then move it to Descriptor(key) here) or by becoming \
         fail-closed (RefusedResidual); a verb enters ONLY with a named reason. Never silently."
    );

    let expected_refused: std::collections::BTreeSet<&str> =
        EXPECTED_REFUSED_RESIDUALS.into_iter().collect();
    let actual_refused: std::collections::BTreeSet<&str> = refused.iter().copied().collect();
    assert_eq!(
        actual_refused, expected_refused,
        "the FAIL-CLOSED (projection-refused) kernel-verb set drifted. A verb enters ONLY with a \
         named reason AND a live refusal (see the projection test below); it leaves ONLY by \
         gaining a deployed rung."
    );

    eprintln!(
        "=== kernel Effect → circuit-witness gate: {} variants, {witnessed} descriptor-witnessed, \
         {} SILENT residuals ({:?}), {} REFUSED residuals ({:?}) ===",
        rows.len(),
        silent.len(),
        silent,
        refused.len(),
        refused,
    );
}

// ---------------------------------------------------------------------------
// Tooth 4: the classification's own evidence, EXECUTED.
// ---------------------------------------------------------------------------

/// Wrap one effect in a minimal single-action turn owned by `cell`.
fn turn_with(cell: dregg_cell::CellId, effect: Effect) -> dregg_turn::turn::Turn {
    let mut forest = dregg_turn::CallForest::new();
    forest.add_root(dregg_turn::Action {
        target: cell,
        method: [0u8; 32],
        args: vec![],
        authorization: dregg_turn::Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![effect],
        may_delegate: dregg_turn::DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    dregg_turn::turn::Turn {
        agent: cell,
        nonce: 0,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

/// The two PQ verbs, as the projection sees them. The payloads are never inspected — the refusal
/// is structural and fires before any crypto — so a well-formed-length key with an empty signature
/// is the honest minimal sample.
fn refused_effect_samples(cell: dregg_cell::CellId) -> Vec<(&'static str, Effect)> {
    vec![
        (
            "CreateHybridCell",
            Effect::CreateHybridCell {
                public_key: [0x11; 32],
                token_id: [0x22; 32],
                balance: 0,
                ml_dsa_public_key: vec![0u8; dregg_cell::ML_DSA_65_PUBLIC_KEY_LEN],
                pq_possession_signature: Vec::new(),
            },
        ),
        (
            "RotatePqIdentity",
            Effect::RotatePqIdentity {
                cell,
                expected_epoch: 0,
                new_ml_dsa_public_key: vec![0u8; dregg_cell::ML_DSA_65_PUBLIC_KEY_LEN],
                new_key_possession_signature: Vec::new(),
            },
        ),
    ]
}

/// TOOTH: `RefusedResidual` is a claim about the PRODUCTION projection, so execute it.
///
/// Three things are checked, and each is a different way this table could go quietly wrong:
///   1. every `RefusedResidual` verb IS refused, and the refusal NAMES it (an anonymous refusal
///      leaves a verifier unable to say which verb went unconstrained);
///   2. it is refused when NESTED inside `ExerciseViaCapability` too —
///      `apply_exercise_via_capability` dispatches inner effects through the same `apply_effect`,
///      while the projection only hash-folds them into `exercise_hash`, so a nesting bypass would
///      let a PQ identity mutation ride an `exerciseVmDescriptor2R24` proof that constrains nothing
///      about it. `EFFECT_ROTATE_PQ_IDENTITY` (`cell/src/facet.rs:113`) is a grantable
///      `allowed_effects` facet bit, so this is reachable, not theoretical;
///   3. the refusal set is not BROADER than the table says — a `NamedResidual` and a `Descriptor`
///      control must both project `Ok`. If a verb starts being refused, it must be reclassified
///      here rather than quietly changing posture.
#[test]
fn refused_residuals_are_refused_by_the_live_projection() {
    use dregg_turn::executor::try_convert_turn_effects_to_vm;

    let cell = dregg_cell::Cell::with_balance([0x5b; 32], [0u8; 32], 1).id();
    let table: std::collections::BTreeMap<&str, Witness> = ledger().into_iter().collect();

    for (name, effect) in refused_effect_samples(cell) {
        assert!(
            matches!(table.get(name), Some(Witness::RefusedResidual(_))),
            "`{name}` is exercised here as a fail-closed verb but the ledger does not classify it \
             as RefusedResidual"
        );

        // (1) top-level.
        let turn = turn_with(cell, effect.clone());
        let err = try_convert_turn_effects_to_vm(&cell, &turn).expect_err(
            "a RefusedResidual verb must be REFUSED by the checked projection: if this now \
             projects, the verb gained a row and its ledger entry is a stale lie",
        );
        assert!(
            err.to_string().contains(name),
            "the refusal must NAME the verb it cannot prove; got `{err}` for `{name}`"
        );

        // (2) nested one and two exercises deep.
        let nested = Effect::ExerciseViaCapability {
            cap_slot: 0,
            inner_effects: vec![effect.clone()],
        };
        let deep = Effect::ExerciseViaCapability {
            cap_slot: 1,
            inner_effects: vec![nested.clone()],
        };
        for (depth, wrapped) in [(1usize, nested), (2, deep)] {
            let turn = turn_with(cell, wrapped);
            let err = try_convert_turn_effects_to_vm(&cell, &turn).expect_err(
                "a PQ identity verb nested under ExerciseViaCapability is APPLIED by the executor \
                 and only hash-bound by the projection — it must be refused exactly as at top \
                 level, or the fail-closed posture is bypassable by nesting",
            );
            assert!(
                err.to_string().contains(name),
                "nested (depth {depth}) refusal must NAME `{name}`; got `{err}`"
            );
        }
    }

    // (3) the refusal set is not broader than the table claims.
    let silent_control = turn_with(
        cell,
        Effect::SetProgram {
            cell,
            program: dregg_cell::CellProgram::None,
        },
    );
    assert!(
        try_convert_turn_effects_to_vm(&cell, &silent_control).is_ok(),
        "`SetProgram` is classified NamedResidual — it must PROJECT (silently, to no row). If it \
         is now refused, it became fail-closed and belongs in EXPECTED_REFUSED_RESIDUALS."
    );
    let descriptor_control = turn_with(cell, Effect::IncrementNonce { cell });
    assert!(
        try_convert_turn_effects_to_vm(&cell, &descriptor_control).is_ok(),
        "`IncrementNonce` is descriptor-witnessed — it must project"
    );
}
