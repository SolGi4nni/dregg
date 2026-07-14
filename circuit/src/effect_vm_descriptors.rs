//! # `effect_vm_descriptors` — the Lean-emitted EffectVM descriptor REGISTRY.
//!
//! This is the foundation for the EffectVM circuit cutover: a registry of every
//! verified-by-construction `EffectVmDescriptor` that Lean's `emitVmJson` renders,
//! embedded here as committed JSON and keyed by the running prover's per-effect
//! **selector index** (`effect_vm::columns::sel`). The descriptor interpreter
//! (`lean_descriptor_air::parse_vm_descriptor` + `EffectVmDescriptorAir`) ingests
//! the selected JSON to drive the verified circuit for that effect.
//!
//! ## Provenance (the descriptor is a Lean-emitted cache)
//!
//! Each `*.json` under `circuit/descriptors/` is the output of the Lean
//! executable `Dregg2/Circuit/Emit/EmitAllJson.lean` (run via
//! `lake env lean --run`), which imports every `EffectVmEmit<Effect>.lean` module
//! and prints `<def>\t<name>\t<emitVmJson desc>`. The JSON is NOT hand-written —
//! Lean is the source of truth and the checked-in JSON is a CACHE of its emission.
//!
//! The actual Lean↔JSON drift gate is GENERATE-FRESH: `scripts/check-descriptor-drift.sh`
//! re-runs the Lean emitters and diffs the result against the checked-in artifacts.
//! That is the only check that can catch a re-emit changing a gate, because it
//! re-derives from Lean. The `*_FP` SHA-256 constants are cache-freshness pins the
//! emit script (re)writes alongside the JSON — `sha256(bytes) == FP` proves only
//! that a file matches the hash committed next to it (self-consistency), NOT that
//! the bytes still equal the current Lean emission. The tests below verify the real
//! property — that each descriptor PARSES through `parse_vm_descriptor` into the
//! structure the prover consumes — not the FP tautology.
//!
//! ## Coverage (HONEST)
//!
//! 26 UNIQUE descriptors are registered (VERB-LOCKSTEP: the 22 descriptors of
//! the factory-dissolved families — escrow/obligation-adjacent legs, the queue
//! family, seal/unseal/seal-pair, the swiss/sturdyref/handoff family, bridge
//! lock/finalize/cancel — died with their `Effect` variants; their semantics
//! are the factory-cell story). The `attenuateA` cap-root-move object is
//! SHARED by attenuate / delegate (ATTENUATE_CAPABILITY=48, GRANT_CAP=3);
//! `revokeDelegation-v2` / `introduce-v2` carry their OWN frozen-frame +
//! nonce-TICK descriptors, and the cap-table semantics are bound OFF-row via
//! each module's universe-A connector.
//!
//!   * `SELECTOR_DESCRIPTORS`: 25 of the 29 LIVE EffectVM selectors carry a
//!     descriptor (the 4 others — NOOP, SET_FIELD, CUSTOM, CELL_UNSEAL — have no
//!     emit module yet; REVOKE_CAPABILITY (24) GRADUATED via the cap-crown v1
//!     face `dregg-effectvm-revokecapability-v1`). Two selectors (3/48 cap moves)
//!     point at the shared `attenuateA` JSON.
//!
//!   * `NAME_ONLY_DESCRIPTORS`: 1 verified descriptor (`mint`) whose effect has
//!     NO dedicated Rust selector (supply mint, distinct from BRIDGE_MINT).
//!     (The RECORD-LAYER STAGE 2 `record` descriptor is registered in
//!     `ALL_DESCRIPTORS` directly — it is the transfer descriptor's `fields_root`-
//!     binding variant, selected by name on a map-write row, not a new selector.)
//!
//! ## PARTIAL / IR-BLOCKED descriptors (registered honestly)
//!
//! Several descriptors are the **economic-leg only** projection of an effect whose
//! full semantics touch an off-trace surface the per-row EffectVM IR can't yet
//! re-derive (the Lean module headers flag this as "IR-BLOCKED" / "the per-row IR
//! STOPS here"). They are registered because the leg they DO emit is verified, and
//! the registry is honest about the gap. Known-partial: the cap-root-move family
//! (`attenuateA` — `cap_root` is a scalar digest of the cap-table FUNCTION the IR
//! can't unfold) and the passthrough-with-hash effects (`setPermissionsA`/`setVK`/
//! `refreshDelegation`/`emitEvent` — state passthrough + an `effects_hash` binding
//! whose preimage lives off-trace). The transfer/burn/mint/note descriptors are
//! FULL economic-state descriptors (balance limb move + frame freeze + GROUP-4
//! commit).
//!
//! ## DO NOT hand-edit
//!
//! The const block and the tables below are generated from the Lean emit. To
//! refresh, run the ONE command:
//!
//!   scripts/emit-descriptors.sh
//!
//! It runs every Lean emitter, rewrites `circuit/descriptors/*.json`, and re-pins
//! the `*_FP` cache-freshness SHA-256 constants — idempotent (a no-op on a clean
//! tree). The CI gate `scripts/check-descriptor-drift.sh` (the `descriptor-drift`
//! job) is the real Lean↔JSON guard: it regenerates from Lean and diffs. See
//! `docs/DESCRIPTOR-EMIT.md`.

// ==== include_str! consts + sha256 cache-freshness pins (auto-generated; do not hand-edit) ====
pub const DREGG_EFFECTVM_ATTENUATEA_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-attenuateA-v1.json");
pub const DREGG_EFFECTVM_ATTENUATEA_V1_FP: &str =
    "d5d570ec30a918c2f3eca57964d62c481d0027ebd75be5958a6780f2bc98df5d";
pub const DREGG_EFFECTVM_BRIDGEMINT_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-bridgemint-v1.json");
pub const DREGG_EFFECTVM_BRIDGEMINT_V1_FP: &str =
    "7fd4ed0d7021982a771030a86d53fa5b3539b0c75a88fbdb25bc33b370853db8";
pub const DREGG_EFFECTVM_BURN_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-burn-v1.json");
pub const DREGG_EFFECTVM_BURN_V1_FP: &str =
    "2230c3d206be35268c199a38c3318a63f250e5542c55c0be9e2e47a73e1734f3";
// GRADUATED (cap-crown): RevokeCapability (sel 24) v1 FACE — the cap-root MOVE + frame freeze (the
// SAME row shape as the attenuate template, only the AIR name differs). The in-circuit sorted-tree
// slot DELETION is the v2 leg (`DREGG_EFFECTVM_REVOKE_CAP_IR2_*`). Lean source
// `EffectVmEmitRevokeCapability.revokeCapabilityVmDescriptor`.
pub const DREGG_EFFECTVM_REVOKECAPABILITY_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-revokecapability-v1.json");
pub const DREGG_EFFECTVM_REVOKECAPABILITY_V1_FP: &str =
    "2555ae492b1d18ff17b6ec5495b7c33d42cf5d3f6adf5173ba071917a10767a4";
// GRADUATED (nonce-tick reconcile, v2): frozen-balance + ticked-nonce effect; the Lean descriptor
// now ticks the runtime nonce (`gNonce`) AND carries the full last-row balance PI binding
// (`boundaryLastPins`), so the descriptor decides IDENTICALLY to the hand-AIR on the real witness
// (honest accept + forged-balance/forged-state-commit reject). Body STRUCTURALLY IDENTICAL to the
// validated `createsealpair-v2` (only the `name` differs). Name bumped `-v1`→`-v2`; FP updated.
pub const DREGG_EFFECTVM_CELLDESTROY_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-celldestroy-v2.json");
pub const DREGG_EFFECTVM_CELLDESTROY_V2_FP: &str =
    "b7fe5ea26cf63a8c90b0a997cdb3729157b9ec60df034581b1875795115201f8";
pub const DREGG_EFFECTVM_CELLSEAL_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-cellseal-v2.json");
pub const DREGG_EFFECTVM_CELLSEAL_V2_FP: &str =
    "0b0a9f6750f5d2d782c52771ba522f1f2d851571e16b384115dd63d441a5ceb1";
// GRADUATED (lifecycle Sealed→Live, v2): the runtime row is the SAME frozen-frame + nonce-tick
// passthrough as cellSeal (the trace arm ticks the nonce, freezes the economic block; the single
// CELL_UNSEAL_TARGET param binds the cell). The lifecycle flip is the off-row face, verified in
// `EffectVmEmitCellUnseal` (`cellUnsealA_full_sound`). Body structurally identical to cellseal-v2
// with `selectorGates 50`.
pub const DREGG_EFFECTVM_CELLUNSEAL_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-cellunseal-v2.json");
pub const DREGG_EFFECTVM_CELLUNSEAL_V2_FP: &str =
    "7a77f53e702e1711baed73c76c0c14231fe3d9fcb58c27079e030473a05ef165";
// GRADUATED (lifecycle/birth reconcile, v2): the WIRE descriptor is now the RUNTIME ACTOR row
// (frozen-frame + nonce-tick + last-row PI pins, body structurally identical to the validated
// `revokeDelegation-v2` template). The pre-v2 JSON pinned the BORN-EMPTY CHILD cell, which the
// runtime row (the acting cell's Stage-3 passthrough) cannot satisfy; the child face stays verified
// in the Lean module (`EffectVmEmitCreateCell`, off-row via `createCellA_full_sound`).
pub const DREGG_EFFECTVM_CREATECELL_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-createcell-v2.json");
pub const DREGG_EFFECTVM_CREATECELL_V2_FP: &str =
    "1b3effd8e83a1b829bb59e508769bf5deb70bc8dd86b0e8e357fbd7c559261e7";
// GRADUATED (lifecycle/birth reconcile, v2): same actor-row reconcile as createcell-v2; the minted
// cell's born-empty face stays in `EffectVmEmitCreateCellFromFactory`.
pub const DREGG_EFFECTVM_CREATECELLFROMFACTORY_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-createcellfromfactory-v2.json");
pub const DREGG_EFFECTVM_CREATECELLFROMFACTORY_V2_FP: &str =
    "704c0693d68323d9a969cb97a28de9d7388d5ff438b1b4fba8ec2dd2b4748d57";
// emitEvent GRADUATED into the cutover (passthrough+tick reconcile): the Lean emit module
// `EffectVmEmitEmitEvent` now ticks the runtime nonce (`gNonce`), freezes the economic block (NOT the
// commit), and carries the selector-binding gate (`selectorGates 25`). The prior JSON froze the nonce +
// the commit (made the honest TICKED trace UNSAT). Name unchanged (`-v1`); body + fingerprint updated.
pub const DREGG_EFFECTVM_EMITEVENT_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-emitEvent-v1.json");
pub const DREGG_EFFECTVM_EMITEVENT_V1_FP: &str =
    "35bc0e51263d232edcb971b4694771c05c37fb0af080e6ee215abffcb0d0c917";
// GRADUATED (nonce-tick + last-row PI pins, v2): the Lean emit module was reconciled onto the runtime
// Stage-3 passthrough batch (whole economic block frozen, nonce ticks via `gNonce`) AND grew the
// `boundaryLastPins` last-row balance PI binding. Body STRUCTURALLY IDENTICAL to the validated
// `createsealpair-v2`; the JSON had not been re-emitted. Name `-v1`→`-v2`; FP updated.
pub const DREGG_EFFECTVM_EXERCISEA_HOLDLAYER_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-exerciseA-holdlayer-v2.json");
pub const DREGG_EFFECTVM_EXERCISEA_HOLDLAYER_V2_FP: &str =
    "394ff8e9351e62d09daea76dfcd614f02a9901ad517f1d3c808eae47ca1433f2";
// GRADUATED (nonce-tick + last-row PI pins, v2): the explicit nonce-only effect. The Lean module was
// reconciled to the runtime TICK (`new_state.nonce += 1`) via `gNonce` and grew `boundaryLastPins`,
// dropping the prior param-bound nonce gate; body STRUCTURALLY IDENTICAL to `createsealpair-v2`. The
// committed JSON was the stale param-bound v1. Name `-v1`→`-v2`; FP updated.
pub const DREGG_EFFECTVM_INCREMENTNONCE_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-incrementNonce-v2.json");
pub const DREGG_EFFECTVM_INCREMENTNONCE_V2_FP: &str =
    "6bed86647d2f2d9558f5b16694e0930ffbf520e1c07926a53700340ca5e0ada8";
// GRADUATED (sovereign mode-bit reconcile, v2): the WIRE descriptor is the RUNTIME row — frame
// freeze + `reserved += 256` (the packed mode_flag bit the hand-AIR enforces) + nonce tick + last-row
// PI pins. The pre-v2 JSON pinned the executor's REBIND-TO-ZERO face (readable record dropped behind
// `stateCommitment`), which the runtime row cannot satisfy; that face stays verified in
// `EffectVmEmitMakeSovereign`. WHICH sovereignty semantics is canonical (rebind-zero vs mode-bit)
// remains an open protocol decision — the cutover models what the runtime proves today.
pub const DREGG_EFFECTVM_MAKESOVEREIGN_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-makesovereign-v2.json");
pub const DREGG_EFFECTVM_MAKESOVEREIGN_V2_FP: &str =
    "3da3f6c6afd7c6c63c60592b74870f0210e17600031cc5895755deb7bec2f505";
pub const DREGG_EFFECTVM_MINT_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-mint-v1.json");
pub const DREGG_EFFECTVM_MINT_V1_FP: &str =
    "c367cb5d2f38c321a73927cca3c92a42fcd1ab3b654074411767dae8da0490da";
pub const DREGG_EFFECTVM_NOTECREATE_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-notecreate-v1.json");
pub const DREGG_EFFECTVM_NOTECREATE_V1_FP: &str =
    "f887d7e0c131bb3b89522fc3f176309d9ec3cec4522748d4f547c072fa2914ad";
pub const DREGG_EFFECTVM_NOTESPEND_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-notespend-v1.json");
pub const DREGG_EFFECTVM_NOTESPEND_V1_FP: &str =
    "92c6a5b820c96a04fab65457566eec019ff3cdc202f5d7af83d46bda5a350f6b";
// GRADUATED (nonce-tick + last-row PI pins, v2): see exercise note. Body STRUCTURALLY IDENTICAL to
// `createsealpair-v2`. Name `-v1`→`-v2`; FP updated.
pub const DREGG_EFFECTVM_PIPELINEDSENDA_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-pipelinedSendA-v2.json");
pub const DREGG_EFFECTVM_PIPELINEDSENDA_V2_FP: &str =
    "97c76897b1c3520b5354022aaff924e2a11ebf9c57f6979e4bf623c6e83efcb4";
// GRADUATED (lifecycle-SET reconcile, v2): the WIRE descriptor is the RUNTIME row — pure
// frozen-frame + nonce-tick (the hand-AIR freezes field[1] and ticks the nonce; the archive
// lifecycle write lives off-row via effects_hash). The pre-v2 JSON SET field[1] := 1 and froze the
// nonce (the executor face), UNSAT on the runtime trace; that face stays verified in
// `EffectVmEmitReceiptArchive`.
pub const DREGG_EFFECTVM_RECEIPTARCHIVEA_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-receiptArchiveA-v2.json");
pub const DREGG_EFFECTVM_RECEIPTARCHIVEA_V2_FP: &str =
    "3f011561e0c29dce2191c76bc060eaea302f33b5647723633a49d3d463e6f77f";
// GRADUATED (nonce-tick + last-row PI pins, v2): refreshDelegation already ticked the runtime nonce
// (`gNonce`) but the committed JSON carried only `boundaryFirstPins` (anti-ghost WEAK: the forged
// last-row balance tooth did not bite). The Lean module grew `boundaryLastPins` + the 2 balance ranges.
// Name `-v1`→`-v2`; FP updated.
pub const DREGG_EFFECTVM_REFRESHDELEGATION_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-refreshDelegation-v2.json");
pub const DREGG_EFFECTVM_REFRESHDELEGATION_V2_FP: &str =
    "336426deea39fa5ade19666d40018ea97dea546efcf7a4a9887028491245049b";
// GRADUATED (nonce-tick + last-row PI pins, v2): revokeDelegation was PRE-v2 pointed at the
// `attenuateA` cap-root-MOVE descriptor, which the runtime hand-AIR does NOT enforce on a revoke row
// (it FREEZES `cap_root`); it "passed" only by fixture accident (cap_root = param2 = 0). The v2 Lean
// module emits the runtime frozen-frame + nonce-TICK directly; the cap-table edge removal is bound
// OFF-row via the universe-A connector. Body STRUCTURALLY IDENTICAL to `createsealpair-v2`.
pub const DREGG_EFFECTVM_REVOKEDELEGATION_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-revokeDelegation-v2.json");
pub const DREGG_EFFECTVM_REVOKEDELEGATION_V2_FP: &str =
    "5f8a55a5774afad4593b12840e7b31c626eaa53656c4065e0eccf2e2b7b2b26f";
// GRADUATED (nonce-tick + last-row PI pins, v2): introduce, same reconcile as revokeDelegation (was
// PRE-v2 pointed at `attenuateA`). The cap-table grant is bound OFF-row via the universe-A connector.
pub const DREGG_EFFECTVM_INTRODUCE_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-introduce-v2.json");
pub const DREGG_EFFECTVM_INTRODUCE_V2_FP: &str =
    "1dfe05b9ccdee704bf94dd2259a6acd4a53ce1fb7aeade387bc2d42b2beae8d2";
// GRADUATED (nonce-tick reconcile, v2): see celldestroy/cellseal note. Body STRUCTURALLY IDENTICAL
// to `createsealpair-v2`. Name bumped `-v1`→`-v2`; FP updated.
pub const DREGG_EFFECTVM_REFUSAL_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-refusal-v2.json");
pub const DREGG_EFFECTVM_REFUSAL_V2_FP: &str =
    "a54e4467a6e38f9bb1eb0dccea0d5476d5e64340d3118cba45b1a434cf291579";
// GRADUATED (nonce-tick + last-row PI pins, v2): see exercise note. Body STRUCTURALLY IDENTICAL to
// `createsealpair-v2`. Name `-v1`→`-v2`; FP updated.
pub const DREGG_EFFECTVM_SETPERMISSIONSA_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-setPermissionsA-v2.json");
pub const DREGG_EFFECTVM_SETPERMISSIONSA_V2_FP: &str =
    "6a70f63aa078f0178edaa0c956ab6568fd1167b43e521e8047f12309b6be0cb4";
pub const DREGG_EFFECTVM_SETVK_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-setVK-v2.json");
pub const DREGG_EFFECTVM_SETVK_V2_FP: &str =
    "a8a557e0c6570dae253c6115ef1e603d60b8ec600c55fcad6e0ac7d3d16320c2";
// GRADUATED (lifecycle/birth reconcile, v3): the WIRE descriptor is the RUNTIME ACTOR (parent) row
// (frozen-frame + nonce-tick). The pre-v3 `v2quint-childcell` JSON pinned the born-empty + cap-handoff
// CHILD cell, which the runtime row cannot satisfy; the child face stays verified in
// `EffectVmEmitSpawn` (off-row via `spawnA_full_sound`).
pub const DREGG_EFFECTVM_SPAWNA_V3_ACTORROW_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-spawnA-v3-actorrow.json");
pub const DREGG_EFFECTVM_SPAWNA_V3_ACTORROW_FP: &str =
    "71e462aa96641c82f4a2d7a830d81581c95716524cc09e52f61e1745ce6c933a";
pub const DREGG_EFFECTVM_TRANSFER_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-transfer-v1.json");
pub const DREGG_EFFECTVM_TRANSFER_V1_FP: &str =
    "b56667151f2c531aadc17cc7d9f46c7813716df25302c78f9274069dd2a63166";
// RECORD-LAYER STAGE 2 (`_RECORD-LAYER-UPGRADE.md` §B.5/§E Stage 2): the transfer descriptor with
// GROUP-4 site 3's previously-spare 4th input ({"t":"zero"}) replaced by the `fields_root` carrier
// cell (col 89 = state_after.FIELDS_ROOT = the RESERVED slot), absorbing the user-field-map root into
// `state_commit`. Width-neutral (186); constraints/ranges/sites 0..2 byte-identical to transfer.
// Verified by construction in `Dregg2.Circuit.Emit.EffectVmEmitRecordRoot` (anti-ghost:
// `recordDescriptor_commit_binds_fieldsRoot`).
pub const DREGG_EFFECTVM_RECORD_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-record-v1.json");
// Re-emitted: the committed JSON had gone STALE behind the Lean source (the transfer selector-binding
// gate landed in `EffectVmEmitTransfer`, and `recordVmDescriptor.constraints =
// transferVmDescriptor.constraints` holds by `rfl` in `EffectVmEmitRecordRoot`, but record-v1 was
// never re-emitted — it was one gate short). Bytes match the `EmitAllJson` output again.
pub const DREGG_EFFECTVM_RECORD_V1_FP: &str =
    "a1d0b1e1290ef23fbea5bb22001f0172eefc8696292677b5eccb0465ec48d169";

// ==== IR-v2 descriptor consts (EPOCH flag-day; ADDITIVE — the v1 consts above stay LIVE) ====
//
// These are the byte-exact output of the Lean executable `EmitAllJsonV2.lean`
// (`lake env lean --run`, which wires `EffectVmEmitV2.v2Registry` through
// `DescriptorIR2.emitVmJson2`). Each is a VERSIONED v2 wire string (`"ir":2`) carrying the five
// EPOCH tables (main / poseidon2_chip / range / memory / map_ops) + the lookup/mem_op/map_op
// constraint grammar that `descriptor_ir2::parse_vm_descriptor2` interprets. They sit ALONGSIDE
// the v1 JSONs during the transition: the live prover still routes through the v1 path
// (`lean_descriptor_air::prove_vm_descriptor`); these are wired+fingerprinted ahead of the
// cutover lane. The registry key is the UNIQUE Lean def-name (the 8 setField slots share the wire
// `name` `dregg-effectvm-setfield-v1`, so name-keying would collide — def-name does not).
pub const DREGG_EFFECTVM_TRANSFER_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-transfer-ir2.json");
pub const DREGG_EFFECTVM_TRANSFER_IR2_FP: &str =
    "7e1ab68576f7a54785dae752085035528753eb567addafcc455074cbcb7c8c3f";
pub const DREGG_EFFECTVM_BURN_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-burn-ir2.json");
pub const DREGG_EFFECTVM_BURN_IR2_FP: &str =
    "f732611fccdbe342987fec08e87ffd576ab8b3d8dd9d7aee67d7b9df8f5c70eb";
pub const DREGG_EFFECTVM_MINT_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-mint-ir2.json");
pub const DREGG_EFFECTVM_MINT_IR2_FP: &str =
    "1deaa7c97b373bffa9333586b5249df71c1b070935955d074e8160281b97bbca";
pub const DREGG_EFFECTVM_NOTE_SPEND_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-note-spend-ir2.json");
pub const DREGG_EFFECTVM_NOTE_SPEND_IR2_FP: &str =
    "a42ad7545f9eb65914cbec22b9355528284315be385a680a18004fd1900e20c2";
pub const DREGG_EFFECTVM_NOTE_CREATE_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-note-create-ir2.json");
pub const DREGG_EFFECTVM_NOTE_CREATE_IR2_FP: &str =
    "38b7187bba3542c531f70d0d00163b90e142bce9110721f24db403d214656cbf";
pub const DREGG_EFFECTVM_CELL_SEAL_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-cell-seal-ir2.json");
pub const DREGG_EFFECTVM_CELL_SEAL_IR2_FP: &str =
    "9096de2f8f2b829b10c461eacede288bfdd85b0fd509555cbb206b6fd3451bea";
pub const DREGG_EFFECTVM_CELL_DESTROY_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-cell-destroy-ir2.json");
pub const DREGG_EFFECTVM_CELL_DESTROY_IR2_FP: &str =
    "ea1dec2287e522594fea348fb523e83faba968c22c96e25f6ee8f62ce82c05fa";
pub const DREGG_EFFECTVM_REFUSAL_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-refusal-ir2.json");
pub const DREGG_EFFECTVM_REFUSAL_IR2_FP: &str =
    "18a3512df5094d494811f2d26fc306c25bfa3f876d9d14e59e3ba209edcd3f32";
pub const DREGG_EFFECTVM_SET_PERMS_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-perms-ir2.json");
pub const DREGG_EFFECTVM_SET_PERMS_IR2_FP: &str =
    "5fec17684e790c1c422b1bc200895f89b18ea1bb07074158842e5953cc64080c";
pub const DREGG_EFFECTVM_SET_VK_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-vk-ir2.json");
pub const DREGG_EFFECTVM_SET_VK_IR2_FP: &str =
    "9621c65a2e16d9c28823e333efc1eef8ab3d6ed55904451098ace2584e8d86a3";
pub const DREGG_EFFECTVM_EXERCISE_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-exercise-ir2.json");
pub const DREGG_EFFECTVM_EXERCISE_IR2_FP: &str =
    "c47e9add936777bfb6bd39df85a24ae960be520235afff6440e24e421240eb32";
pub const DREGG_EFFECTVM_PIPELINED_SEND_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-pipelined-send-ir2.json");
pub const DREGG_EFFECTVM_PIPELINED_SEND_IR2_FP: &str =
    "904f9c773aca65497a68348aa22224a1a16837ec511fe54519337ab657f30e3a";
pub const DREGG_EFFECTVM_REFRESH_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-refresh-ir2.json");
pub const DREGG_EFFECTVM_REFRESH_IR2_FP: &str =
    "aede347d2fe74a278cb609fe33f69dfdeb09151a905c110fd92cb9370d1ab005";
pub const DREGG_EFFECTVM_INCREMENT_NONCE_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-increment-nonce-ir2.json");
pub const DREGG_EFFECTVM_INCREMENT_NONCE_IR2_FP: &str =
    "7f5470169de5cc1d17c9ea90a251aabbbe558c8392a861103cca81305f65e7c3";
pub const DREGG_EFFECTVM_REVOKE_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-revoke-ir2.json");
pub const DREGG_EFFECTVM_REVOKE_IR2_FP: &str =
    "d69b2ad8d1e9b13c84e909c36891f59d47a43b452e55859bdcf6fc9308a0affa";
pub const DREGG_EFFECTVM_INTRODUCE_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-introduce-ir2.json");
pub const DREGG_EFFECTVM_INTRODUCE_IR2_FP: &str =
    "190521abaa1967847e23cbb8a2a332d6257ecc8d8ac05dbf52022d619f3fac34";
pub const DREGG_EFFECTVM_ATTENUATE_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-attenuate-ir2.json");
pub const DREGG_EFFECTVM_ATTENUATE_IR2_FP: &str =
    "52d6d6f1c76ce3f8814cbb0f3c41e325cfb645bfc45ed1ef763b40131ba5f6fe";
// GRADUATED (cap-crown): RevokeCapability (sel 24). The v2 leg of the cap-REMOVAL effect — a
// held-membership map-read authenticated against the before cap_root + a ZERO-value remove-write
// (the slot's rights deleted), NO submask (revoke deletes a slot, it does not narrow rights). Lean
// source `EffectVmEmitV2.revokeCapabilityVmDescriptor2`; keystones `revokeV2_removes` /
// `revokeV2_held_determined` / `revokeV2_post_determined`.
pub const DREGG_EFFECTVM_REVOKE_CAP_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-revoke-cap-ir2.json");
pub const DREGG_EFFECTVM_REVOKE_CAP_IR2_FP: &str =
    "ddd66b7acb3003e5e26eaf38743c67462824c6a8cd975796c08a805fa54d4d53";
// GRADUATED (Custom recursive-proof binding, sel 8): the runtime passthrough face graduated onto
// IR-v2 PLUS the `proof_bind` op (`customProofBind`) that ties the row's `custom_proof_commitment`
// to a VERIFYING external sub-proof of the recursion engine — the accumulator constraint the
// per-row IR gained (`DescriptorIR2.ProofBind`). Lean source
// `EffectVmEmitV2.customVmDescriptor2`. THE LAST rotation-cutover residue closed.
pub const DREGG_EFFECTVM_CUSTOM_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-custom-ir2.json");
pub const DREGG_EFFECTVM_CUSTOM_IR2_FP: &str =
    "e2d296687d88761ccc2977ac95a9a3ea693313d94cef66bd0810af13cb347033";
pub const DREGG_EFFECTVM_SET_FIELD_DYN_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-field-dyn-ir2.json");
pub const DREGG_EFFECTVM_SET_FIELD_DYN_IR2_FP: &str =
    "d2aa3dd677765b4d2bba2c628651b9c6ba37dcdd86c9da00da44f3aa5a3260fa";
pub const DREGG_EFFECTVM_SET_FIELD_0_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-field-0-ir2.json");
pub const DREGG_EFFECTVM_SET_FIELD_0_IR2_FP: &str =
    "e024ad19f58922252b7cdc70c274a4f6ed6f5f391adb77b08f46c2847f1cf0d8";
pub const DREGG_EFFECTVM_SET_FIELD_1_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-field-1-ir2.json");
pub const DREGG_EFFECTVM_SET_FIELD_1_IR2_FP: &str =
    "cf45df10a15ff2d7c49650da9040e78e534dd07fe4cf21f09d5f6b7069e89d8b";
pub const DREGG_EFFECTVM_SET_FIELD_2_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-field-2-ir2.json");
pub const DREGG_EFFECTVM_SET_FIELD_2_IR2_FP: &str =
    "719752cb08ec7e181b94a8a766703fdec344fa75b03e6817145a2e54cebf491e";
pub const DREGG_EFFECTVM_SET_FIELD_3_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-field-3-ir2.json");
pub const DREGG_EFFECTVM_SET_FIELD_3_IR2_FP: &str =
    "bc42b993f8f40325eedb94d3d33989534b2445a37c80f2d496f6c756ef524007";
pub const DREGG_EFFECTVM_SET_FIELD_4_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-field-4-ir2.json");
pub const DREGG_EFFECTVM_SET_FIELD_4_IR2_FP: &str =
    "c24af7e38efb2241ba402ba72b13f02fffbb70a0ad951ef8b481e1fcf6b97cb3";
pub const DREGG_EFFECTVM_SET_FIELD_5_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-field-5-ir2.json");
pub const DREGG_EFFECTVM_SET_FIELD_5_IR2_FP: &str =
    "5859dd8b048d1d89e30b10fa3e7c726c4f92126ef23464741d7ddf5b06002bfc";
pub const DREGG_EFFECTVM_SET_FIELD_6_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-field-6-ir2.json");
pub const DREGG_EFFECTVM_SET_FIELD_6_IR2_FP: &str =
    "02671895e187cc6dee172d0baf9372332b1041f81b3d8da68d9b2053fa28c351";
pub const DREGG_EFFECTVM_SET_FIELD_7_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-field-7-ir2.json");
pub const DREGG_EFFECTVM_SET_FIELD_7_IR2_FP: &str =
    "e26003660a1bbc0072eac64296230c5fbe8afbecafb140f059ae7f6d082402c2";

// ==== selector index -> (descriptor name, const json, fingerprint) ====
pub const SELECTOR_DESCRIPTORS: &[(usize, &str, &str, &str)] = &[
    (
        1,
        "dregg-effectvm-transfer-v1",
        DREGG_EFFECTVM_TRANSFER_V1_JSON,
        DREGG_EFFECTVM_TRANSFER_V1_FP,
    ), // TRANSFER: transferVmDescriptor
    (
        3,
        "dregg-effectvm-attenuateA-v1",
        DREGG_EFFECTVM_ATTENUATEA_V1_JSON,
        DREGG_EFFECTVM_ATTENUATEA_V1_FP,
    ), // GRANT_CAP: delegateVmDescriptor (unattenuated cap-root grant = attenuate template)
    (
        4,
        "dregg-effectvm-notespend-v1",
        DREGG_EFFECTVM_NOTESPEND_V1_JSON,
        DREGG_EFFECTVM_NOTESPEND_V1_FP,
    ), // NOTE_SPEND: noteSpendVmDescriptor
    (
        5,
        "dregg-effectvm-notecreate-v1",
        DREGG_EFFECTVM_NOTECREATE_V1_JSON,
        DREGG_EFFECTVM_NOTECREATE_V1_FP,
    ), // NOTE_CREATE: noteCreateVmDescriptor
    (
        12,
        "dregg-effectvm-makesovereign-v2",
        DREGG_EFFECTVM_MAKESOVEREIGN_V2_JSON,
        DREGG_EFFECTVM_MAKESOVEREIGN_V2_FP,
    ), // MAKE_SOVEREIGN: makeSovereignRuntimeVmDescriptor (GRADUATED: mode-bit +256 + nonce-tick; rebind face off-row)
    (
        13,
        "dregg-effectvm-createcellfromfactory-v2",
        DREGG_EFFECTVM_CREATECELLFROMFACTORY_V2_JSON,
        DREGG_EFFECTVM_CREATECELLFROMFACTORY_V2_FP,
    ), // CREATE_CELL_FROM_FACTORY: factoryActorVmDescriptor (GRADUATED: actor frozen-frame + nonce-tick; child face off-row)
    (
        24,
        "dregg-effectvm-revokecapability-v1",
        DREGG_EFFECTVM_REVOKECAPABILITY_V1_JSON,
        DREGG_EFFECTVM_REVOKECAPABILITY_V1_FP,
    ), // REVOKE_CAPABILITY: revokeCapabilityVmDescriptor (GRADUATED cap-crown v1 FACE; in-circuit slot DELETION = the v2 leg)
    (
        25,
        "dregg-effectvm-emitEvent-v1",
        DREGG_EFFECTVM_EMITEVENT_V1_JSON,
        DREGG_EFFECTVM_EMITEVENT_V1_FP,
    ), // EMIT_EVENT: emitEventVmDescriptor
    (
        26,
        "dregg-effectvm-setPermissionsA-v2",
        DREGG_EFFECTVM_SETPERMISSIONSA_V2_JSON,
        DREGG_EFFECTVM_SETPERMISSIONSA_V2_FP,
    ), // SET_PERMISSIONS: setPermsVmDescriptor (GRADUATED: nonce-tick + last-row PI pins)
    (
        27,
        "dregg-effectvm-setVK-v2",
        DREGG_EFFECTVM_SETVK_V2_JSON,
        DREGG_EFFECTVM_SETVK_V2_FP,
    ), // SET_VERIFICATION_KEY: setVKVmDescriptor (GRADUATED: nonce-tick + last-row PI pins)
    (
        29,
        "dregg-effectvm-refreshDelegation-v2",
        DREGG_EFFECTVM_REFRESHDELEGATION_V2_JSON,
        DREGG_EFFECTVM_REFRESHDELEGATION_V2_FP,
    ), // REFRESH_DELEGATION: refreshVmDescriptor (GRADUATED: nonce-tick + last-row PI pins)
    (
        30,
        "dregg-effectvm-revokeDelegation-v2",
        DREGG_EFFECTVM_REVOKEDELEGATION_V2_JSON,
        DREGG_EFFECTVM_REVOKEDELEGATION_V2_FP,
    ), // REVOKE_DELEGATION: revokeVmDescriptor (GRADUATED: frozen-frame + nonce-tick; cap-table move OFF-row)
    (
        31,
        "dregg-effectvm-createcell-v2",
        DREGG_EFFECTVM_CREATECELL_V2_JSON,
        DREGG_EFFECTVM_CREATECELL_V2_FP,
    ), // CREATE_CELL: createCellActorVmDescriptor (GRADUATED: actor frozen-frame + nonce-tick; child face off-row)
    (
        32,
        "dregg-effectvm-spawnA-v3-actorrow",
        DREGG_EFFECTVM_SPAWNA_V3_ACTORROW_JSON,
        DREGG_EFFECTVM_SPAWNA_V3_ACTORROW_FP,
    ), // SPAWN_WITH_DELEGATION: spawnActorVmDescriptor (GRADUATED: actor frozen-frame + nonce-tick; child face off-row)
    (
        34,
        "dregg-effectvm-exerciseA-holdlayer-v2",
        DREGG_EFFECTVM_EXERCISEA_HOLDLAYER_V2_JSON,
        DREGG_EFFECTVM_EXERCISEA_HOLDLAYER_V2_FP,
    ), // EXERCISE_VIA_CAPABILITY: exerciseVmDescriptor (GRADUATED: nonce-tick + last-row PI pins)
    (
        35,
        "dregg-effectvm-introduce-v2",
        DREGG_EFFECTVM_INTRODUCE_V2_JSON,
        DREGG_EFFECTVM_INTRODUCE_V2_FP,
    ), // INTRODUCE: introduceVmDescriptor (GRADUATED: frozen-frame + nonce-tick; cap-table grant OFF-row)
    (
        36,
        "dregg-effectvm-pipelinedSendA-v2",
        DREGG_EFFECTVM_PIPELINEDSENDA_V2_JSON,
        DREGG_EFFECTVM_PIPELINEDSENDA_V2_FP,
    ), // PIPELINED_SEND: pipelinedSendVmDescriptor (GRADUATED: nonce-tick + last-row PI pins)
    (
        40,
        "dregg-effectvm-bridgemint-v1",
        DREGG_EFFECTVM_BRIDGEMINT_V1_JSON,
        DREGG_EFFECTVM_BRIDGEMINT_V1_FP,
    ), // BRIDGE_MINT: bridgeMintVmDescriptor
    (
        46,
        "dregg-effectvm-burn-v1",
        DREGG_EFFECTVM_BURN_V1_JSON,
        DREGG_EFFECTVM_BURN_V1_FP,
    ), // BURN: burnVmDescriptor
    (
        47,
        "dregg-effectvm-celldestroy-v2",
        DREGG_EFFECTVM_CELLDESTROY_V2_JSON,
        DREGG_EFFECTVM_CELLDESTROY_V2_FP,
    ), // CELL_DESTROY: cellDestroyVmDescriptor (GRADUATED: nonce-tick + last-row PI pins)
    (
        48,
        "dregg-effectvm-attenuateA-v1",
        DREGG_EFFECTVM_ATTENUATEA_V1_JSON,
        DREGG_EFFECTVM_ATTENUATEA_V1_FP,
    ), // ATTENUATE_CAPABILITY: attenuateVmDescriptor (canonical cap-root move)
    (
        49,
        "dregg-effectvm-cellseal-v2",
        DREGG_EFFECTVM_CELLSEAL_V2_JSON,
        DREGG_EFFECTVM_CELLSEAL_V2_FP,
    ), // CELL_SEAL: cellSealVmDescriptor (GRADUATED: nonce-tick + last-row PI pins)
    (
        50,
        "dregg-effectvm-cellunseal-v2",
        DREGG_EFFECTVM_CELLUNSEAL_V2_JSON,
        DREGG_EFFECTVM_CELLUNSEAL_V2_FP,
    ), // CELL_UNSEAL: cellUnsealVmDescriptor (GRADUATED: frozen-frame + nonce-tick; lifecycle flip off-row)
    (
        51,
        "dregg-effectvm-receiptArchiveA-v2",
        DREGG_EFFECTVM_RECEIPTARCHIVEA_V2_JSON,
        DREGG_EFFECTVM_RECEIPTARCHIVEA_V2_FP,
    ), // RECEIPT_ARCHIVE: receiptArchiveActorVmDescriptor (GRADUATED: frozen-frame + nonce-tick; lifecycle write off-row)
    (
        52,
        "dregg-effectvm-refusal-v2",
        DREGG_EFFECTVM_REFUSAL_V2_JSON,
        DREGG_EFFECTVM_REFUSAL_V2_FP,
    ), // REFUSAL: refusalVmDescriptor (GRADUATED: nonce-tick + last-row PI pins)
    (
        53,
        "dregg-effectvm-incrementNonce-v2",
        DREGG_EFFECTVM_INCREMENTNONCE_V2_JSON,
        DREGG_EFFECTVM_INCREMENTNONCE_V2_FP,
    ), // INCREMENT_NONCE: incrementNonceVmDescriptor (GRADUATED: nonce-tick + last-row PI pins)
];

// ==== name-only descriptors (verified, but no dedicated Rust selector slot yet) ====
pub const NAME_ONLY_DESCRIPTORS: &[(&str, &str, &str)] = &[
    (
        "dregg-effectvm-mint-v1",
        DREGG_EFFECTVM_MINT_V1_JSON,
        DREGG_EFFECTVM_MINT_V1_FP,
    ), // mintVmDescriptor: supply MINT (balance credit); no dedicated EffectVM sel (distinct from BRIDGE_MINT)
];

// ==== IR-v2 descriptor registry (EPOCH; ADDITIVE — keyed by UNIQUE Lean def-name) ====
//
// The `EffectVmEmitV2.v2Registry` entries, byte-exact from `EmitAllJsonV2.lean`, fingerprinted.
// These prove+verify through `descriptor_ir2::{parse_vm_descriptor2, prove_vm_descriptor2,
// verify_vm_descriptor2}` (the multi-table batch STARK). The live prover does NOT route through
// these yet — they are wired ahead of the cutover lane so the flag-day flips a registry pointer,
// not an emission. Key = the Lean def-name (`transferVmDescriptor2`, `setFieldVmDescriptor2-3`, …)
// since the wire `name` collides across graduated/per-slot descriptors.
pub const V2_DESCRIPTORS: &[(&str, &str, &str)] = &[
    (
        "transferVmDescriptor2",
        DREGG_EFFECTVM_TRANSFER_IR2_JSON,
        DREGG_EFFECTVM_TRANSFER_IR2_FP,
    ),
    (
        "burnVmDescriptor2",
        DREGG_EFFECTVM_BURN_IR2_JSON,
        DREGG_EFFECTVM_BURN_IR2_FP,
    ),
    (
        "mintVmDescriptor2",
        DREGG_EFFECTVM_MINT_IR2_JSON,
        DREGG_EFFECTVM_MINT_IR2_FP,
    ),
    (
        "noteSpendVmDescriptor2",
        DREGG_EFFECTVM_NOTE_SPEND_IR2_JSON,
        DREGG_EFFECTVM_NOTE_SPEND_IR2_FP,
    ),
    (
        "noteCreateVmDescriptor2",
        DREGG_EFFECTVM_NOTE_CREATE_IR2_JSON,
        DREGG_EFFECTVM_NOTE_CREATE_IR2_FP,
    ),
    (
        "cellSealVmDescriptor2",
        DREGG_EFFECTVM_CELL_SEAL_IR2_JSON,
        DREGG_EFFECTVM_CELL_SEAL_IR2_FP,
    ),
    (
        "cellDestroyVmDescriptor2",
        DREGG_EFFECTVM_CELL_DESTROY_IR2_JSON,
        DREGG_EFFECTVM_CELL_DESTROY_IR2_FP,
    ),
    (
        "refusalVmDescriptor2",
        DREGG_EFFECTVM_REFUSAL_IR2_JSON,
        DREGG_EFFECTVM_REFUSAL_IR2_FP,
    ),
    (
        "setPermsVmDescriptor2",
        DREGG_EFFECTVM_SET_PERMS_IR2_JSON,
        DREGG_EFFECTVM_SET_PERMS_IR2_FP,
    ),
    (
        "setVKVmDescriptor2",
        DREGG_EFFECTVM_SET_VK_IR2_JSON,
        DREGG_EFFECTVM_SET_VK_IR2_FP,
    ),
    (
        "exerciseVmDescriptor2",
        DREGG_EFFECTVM_EXERCISE_IR2_JSON,
        DREGG_EFFECTVM_EXERCISE_IR2_FP,
    ),
    (
        "pipelinedSendVmDescriptor2",
        DREGG_EFFECTVM_PIPELINED_SEND_IR2_JSON,
        DREGG_EFFECTVM_PIPELINED_SEND_IR2_FP,
    ),
    (
        "refreshVmDescriptor2",
        DREGG_EFFECTVM_REFRESH_IR2_JSON,
        DREGG_EFFECTVM_REFRESH_IR2_FP,
    ),
    (
        "incrementNonceVmDescriptor2",
        DREGG_EFFECTVM_INCREMENT_NONCE_IR2_JSON,
        DREGG_EFFECTVM_INCREMENT_NONCE_IR2_FP,
    ),
    (
        "revokeVmDescriptor2",
        DREGG_EFFECTVM_REVOKE_IR2_JSON,
        DREGG_EFFECTVM_REVOKE_IR2_FP,
    ),
    (
        "introduceVmDescriptor2",
        DREGG_EFFECTVM_INTRODUCE_IR2_JSON,
        DREGG_EFFECTVM_INTRODUCE_IR2_FP,
    ),
    (
        "attenuateVmDescriptor2",
        DREGG_EFFECTVM_ATTENUATE_IR2_JSON,
        DREGG_EFFECTVM_ATTENUATE_IR2_FP,
    ),
    (
        "revokeCapabilityVmDescriptor2",
        DREGG_EFFECTVM_REVOKE_CAP_IR2_JSON,
        DREGG_EFFECTVM_REVOKE_CAP_IR2_FP,
    ),
    (
        "customVmDescriptor2",
        DREGG_EFFECTVM_CUSTOM_IR2_JSON,
        DREGG_EFFECTVM_CUSTOM_IR2_FP,
    ),
    (
        "setFieldDynVmDescriptor2",
        DREGG_EFFECTVM_SET_FIELD_DYN_IR2_JSON,
        DREGG_EFFECTVM_SET_FIELD_DYN_IR2_FP,
    ),
    (
        "setFieldVmDescriptor2-0",
        DREGG_EFFECTVM_SET_FIELD_0_IR2_JSON,
        DREGG_EFFECTVM_SET_FIELD_0_IR2_FP,
    ),
    (
        "setFieldVmDescriptor2-1",
        DREGG_EFFECTVM_SET_FIELD_1_IR2_JSON,
        DREGG_EFFECTVM_SET_FIELD_1_IR2_FP,
    ),
    (
        "setFieldVmDescriptor2-2",
        DREGG_EFFECTVM_SET_FIELD_2_IR2_JSON,
        DREGG_EFFECTVM_SET_FIELD_2_IR2_FP,
    ),
    (
        "setFieldVmDescriptor2-3",
        DREGG_EFFECTVM_SET_FIELD_3_IR2_JSON,
        DREGG_EFFECTVM_SET_FIELD_3_IR2_FP,
    ),
    (
        "setFieldVmDescriptor2-4",
        DREGG_EFFECTVM_SET_FIELD_4_IR2_JSON,
        DREGG_EFFECTVM_SET_FIELD_4_IR2_FP,
    ),
    (
        "setFieldVmDescriptor2-5",
        DREGG_EFFECTVM_SET_FIELD_5_IR2_JSON,
        DREGG_EFFECTVM_SET_FIELD_5_IR2_FP,
    ),
    (
        "setFieldVmDescriptor2-6",
        DREGG_EFFECTVM_SET_FIELD_6_IR2_JSON,
        DREGG_EFFECTVM_SET_FIELD_6_IR2_FP,
    ),
    (
        "setFieldVmDescriptor2-7",
        DREGG_EFFECTVM_SET_FIELD_7_IR2_JSON,
        DREGG_EFFECTVM_SET_FIELD_7_IR2_FP,
    ),
];

// ==== ROTATION v3-STAGED artifacts (THE ROTATION — `docs/ROTATION-CUTOVER.md`) ====
//
// Byte-exact from `EmitRotationV3.lean` (the verified emission is
// `Dregg2/Circuit/Emit/EffectVmEmitRotation.lean`). STAGED: nothing on the live wire
// reads these — they ride the recursion-gated IR-v2 path only (the staged probe proves
// through `prove_vm_descriptor2`, tests in `descriptor_ir2.rs`). NOT part of
// `V2_DESCRIPTORS` (its 26-entry pin is the graduation cohort) nor `ALL_DESCRIPTORS`
// (the live v1 registry stays byte-identical).

/// The Lean-pinned rotation layout manifest (`rotationLayoutManifest`, `#guard`-byte-pinned
/// in Lean; the Rust twin test `rotation_layout_matches_lean` rebuilds it from
/// `effect_vm::columns::rotation` + `pi::v3` and compares — both sides pin, neither parses).
pub const ROTATION_LAYOUT_V3_STAGED_JSON: &str =
    include_str!("../descriptors/rotation-layout-v3-staged.json");
pub const ROTATION_LAYOUT_V3_STAGED_FP: &str =
    "17d4d1097a020bc389fb8e3b584e44ffc4eb5a7438d47b810db1e7ad1954a7b4";

/// The staged rotation-state probe descriptor (`rotationProbeVmDescriptor2` =
/// `graduateV1` of the 8-site chained absorption + the two PI pins; Lean keystones
/// `rotationProbeV2_pins_commit` / `rotationProbe_commit_binds_published`).
pub const DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-rotation-state-v3-staged.json");
pub const DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_FP: &str =
    "615b2ff7419634d7f4527009d8de88d73cc2f321b789aec6fc5586d7ade36891";

/// The REGISTER-COUNT MEASUREMENT probes (`docs/ROTATION-CUTOVER.md` pre-gates): the same
/// staged rotation probe emitted at R=24 and R=32 registers from the PARAMETRIC Lean
/// emission (`Dregg2/Circuit/Emit/EffectVmEmitRotationR.lean`, driver `EmitRotationV3.lean`;
/// keystone `wireCommitR_binds` holds parametrically in R — no per-R axiom). The R=16
/// probe above is the deployed reference and its bytes DO NOT move (Lean `#guard`s the
/// graduated R=16 wire JSON byte-identical to the pinned emission). These exist to be
/// MEASURED (`descriptor_ir2.rs::rotation_probe_register_count_measurement`): registers
/// are ALWAYS-PAID commitment limbs in every turn proof; heap fields are METERED umem rows.
pub const DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_R24_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-rotation-state-v3-staged-r24.json");
pub const DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_R24_FP: &str =
    "92bba2b7f1dca932e0cf06f78ad155b2afccc8f7b4e8740a31e803000a4e8c6a";
pub const DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_R32_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-rotation-state-v3-staged-r32.json");
pub const DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_R32_FP: &str =
    "3afc1492e22949ed41f87a07f99e638a1d7f8684d6cc73a2bf7e4991231a8f82";

/// The v3-staged registry (keyed by Lean def-name, the `V2_DESCRIPTORS` pattern). Entry 0
/// is the deployed R=16 reference; entries 1-2 are the register-count measurement probes.
pub const V3_STAGED_DESCRIPTORS: &[(&str, &str, &str)] = &[
    (
        "rotationProbeVmDescriptor2",
        DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_JSON,
        DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_FP,
    ),
    (
        "rotationProbeVmDescriptorR24",
        DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_R24_JSON,
        DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_R24_FP,
    ),
    (
        "rotationProbeVmDescriptorR32",
        DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_R32_JSON,
        DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_R32_FP,
    ),
];

/// THE WIDENED CAVEAT OPERAND artifacts (staged — the second rotation wire-shape
/// pre-gate). The layout manifest is byte-pinned BOTH sides (Lean `#guard` in
/// `EffectVmEmitRotationCaveat.lean`; Rust twin `rotation_caveat_layout_matches_lean`
/// rebuilds from `columns::rotation::caveat` — both pin, neither parses); the probe
/// descriptor is the R=24 rotated block + the 29-felt caveat manifest block + its
/// chained commitment, three PI pins (state commit · height · caveat commit). Lean
/// keystones: `caveat_operand_no_aliasing` (slot/heap domain separation as a theorem),
/// `caveatCommit_binds` (a forged domain tag / tampered heap key moves the commit),
/// `rotationCaveatProbe_binds_published` (end-to-end, wire form).
pub const ROTATION_CAVEAT_LAYOUT_V3_STAGED_JSON: &str =
    include_str!("../descriptors/rotation-caveat-layout-v3-staged.json");
pub const ROTATION_CAVEAT_LAYOUT_V3_STAGED_FP: &str =
    "8cfcaf978f7123f9f159f9ae05ab85ef9a245c93d9d9e1b6e2ce7b9500c890a8";

pub const DREGG_EFFECTVM_ROTATION_CAVEAT_V3_STAGED_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-rotation-caveat-v3-staged-r24.json");
pub const DREGG_EFFECTVM_ROTATION_CAVEAT_V3_STAGED_FP: &str =
    "39d84d4af032e31380bf909b560d1924d2754ec023da0fb2dfee03de727f5112";

/// The caveat-operand staged registry (kept SEPARATE from `V3_STAGED_DESCRIPTORS`
/// so the three rotation-probe pins stay byte-frozen and their coverage walker
/// unchanged).
pub const V3_STAGED_CAVEAT_DESCRIPTORS: &[(&str, &str, &str)] = &[(
    "rotationCaveatProbeVmDescriptor2",
    DREGG_EFFECTVM_ROTATION_CAVEAT_V3_STAGED_JSON,
    DREGG_EFFECTVM_ROTATION_CAVEAT_V3_STAGED_FP,
)];

/// THE FULL-COHORT REGEN at the rotated R=24 block (`ROTATION-CUTOVER.md` §5 item 1):
/// all 36 cohort descriptors re-emitted past their v1 layout with the rotated
/// BEFORE/AFTER blocks + the widened-caveat region (Lean `rotateV3` /
/// `EffectVmEmitRotationV3.lean`; `v3Registry` is the source) — the 28 v2-graduated members
/// (the 17 graduated cohort + attenuate WITH its phase-B map-ops/submask lookup + revoke, plus
/// the cap-crown `revokeCapability`) PLUS the 8 LIVE-path effects the STEP 1 widening
/// added (grantCap · makeSovereign ·
/// createCell · factory · spawn · receiptArchive · cellUnseal · emitEvent). The TSV is
/// `key\tname\tjson` per line, structurally covered by `v3_staged_registry_parses_and_covers`.
/// ⚠ DEPLOYED, NOT staged — the "-staged" name + "no VK bump / live wire untouched" note are STALE.
/// The HARDSWAP VK-epoch landed this as the DEFAULT registry and RETIRED the v1 effect-VM fallback
/// (`prove_full_turn` fails closed without a rotation witness). This constant is the sole live
/// per-turn effect-VM source, read by `prove_effect_vm_rotated_ir2_with_caveat`.
/// Widths reflect the CURRENT geometry (revoked-root 178 flag-day + the 8-felt ProofBind flag-day
/// `36f04de71`), NOT the retired `409 = 188 + 221` v10 formula: narrow rotated members run
/// `trace_width` up to ≈1668 with 62 PIs (transfer-class), the graduated chip-lane columns included.
/// The commitment is the faithful 8-felt ~124-bit binding (state + ProofBind both 8-felt), not the
/// old four-appended-PI / ~31-bit form.
pub const V3_STAGED_REGISTRY_TSV: &str =
    include_str!("../descriptors/rotation-v3-staged-registry.tsv");
pub const V3_STAGED_REGISTRY_FP: &str =
    "609bf2698679e648d5c9a0359e5748706901f5f42ed9789436f2bec6e44f45cb";

/// **THE UMEM-FORM COHORT REGISTRY (STAGED, VK-RISK-FREE).** The 9 per-effect FIXED-cohort umem
/// descriptors — `setFieldUMem` · `setHeapUMem` · `grantUMem` · `attenuateUMem` ·
/// `transferBalanceUMem` · `mintBalanceUMem` · `burnBalanceUMem` · `revokeUMem` ·
/// `nullifierFreshUMem` — emitted from the verified Lean
/// `Dregg2.Circuit.Emit.EffectVmEmitUMemCohort.umemCohortRegistry` (`#assert_axioms`-clean,
/// byte-pinned). Each is single-domain, width-7, ONE `umem_op` guarded at column 6 — the FIXED
/// shape a committed VK can back (the producer's per-turn `umem-turn-boundary` form is
/// variable-width `6 + #domains` and cannot). `key\tname\tjson` per line (key = the lean def
/// name, e.g. `setFieldUMem`; name = the wire descriptor name; json = the parseable descriptor).
///
/// ADDITIVE / STAGED: a NEW set BESIDE the deployed per-map / rotated registries, NO VK bump,
/// nothing on the live wire. The deployed prover keeps using the per-map V3 registry until the
/// gated VK epoch; this is the per-effect → umem-descriptor routing the flip rides through.
pub const UMEM_COHORT_V1_STAGED_REGISTRY_TSV: &str =
    include_str!("../descriptors/umem-cohort-v1-staged-registry.tsv");

/// Resolve the umem-form COHORT lean-key (the [`UMEM_COHORT_V1_STAGED_REGISTRY_TSV`] first
/// column) for an [`Effect`](crate::effect_vm::Effect) — the per-effect FIXED-cohort
/// descriptor this effect's universal-memory touch proves against. `None` = the effect is not
/// (yet) a umem-cohort member (it stays on the per-map path; e.g. multi-domain or
/// state-passthrough effects). STAGED: this is the effect→umem-descriptor resolver the gated
/// flip routes through; the deployed default never calls it.
///
/// The domain each member touches mirrors `turn/src/umem.rs` (`UKey::domain`): Field / Balance →
/// `heap`(1), Cap planes → `caps`(2), nullifiers → `nullifiers`(3).
pub fn umem_cohort_lean_key_for_effect(effect: &crate::effect_vm::Effect) -> Option<&'static str> {
    use crate::effect_vm::Effect;
    Some(match effect {
        Effect::SetField { .. } => "setFieldUMem",
        Effect::Transfer { .. } => "transferBalanceUMem",
        Effect::GrantCapability { .. } => "grantUMem",
        Effect::AttenuateCapability { .. } => "attenuateUMem",
        Effect::RevokeCapability { .. } => "revokeUMem",
        Effect::Mint { .. } | Effect::BridgeMint { .. } => "mintBalanceUMem",
        Effect::Burn { .. } => "burnBalanceUMem",
        Effect::NoteSpend { .. } => "nullifierFreshUMem",
        _ => return None,
    })
}

/// The parseable descriptor JSON (third column) for a umem-cohort lean-key in
/// [`UMEM_COHORT_V1_STAGED_REGISTRY_TSV`]. `None` if the key is absent.
pub fn umem_cohort_descriptor_json(lean_key: &str) -> Option<&'static str> {
    UMEM_COHORT_V1_STAGED_REGISTRY_TSV.lines().find_map(|line| {
        let mut it = line.splitn(3, '\t');
        if it.next() == Some(lean_key) {
            let _wire_name = it.next();
            it.next()
        } else {
            None
        }
    })
}

/// The byte-pinned staged registry of the MULTI-DOMAIN umem-form COHORT descriptors (the verified
/// Lean `EffectVmEmitUMemCohortMulti.umemCohortMultiRegistry`, `EmitUMemCohortMulti.lean`-emitted +
/// `#guard` byte-pinned). Each is width-8, TWO `umem_op`s — one per touched domain, guarded at
/// column 6 (`heap`, the balance credit) and column 7 (`nullifiers`, the freshness insert) — the
/// FIXED twin of the producer's sorted-domain two-domain form (`turn/src/umem.rs`), the shape a
/// committed VK can back. This COMPLETES the umem cohort to the effects whose state touch spans more
/// than one domain in one effect (the NOTE/BRIDGE economic verbs), on which the single-domain cohort
/// fails closed. `key\tname\tjson` per line.
///
/// ADDITIVE / STAGED: a NEW set BESIDE the single-domain [`UMEM_COHORT_V1_STAGED_REGISTRY_TSV`] and
/// the deployed per-map / rotated registries, NO VK bump, nothing on the live wire.
pub const UMEM_COHORT_MULTIDOMAIN_V1_STAGED_REGISTRY_TSV: &str =
    include_str!("../descriptors/umem-cohort-multidomain-v1-staged-registry.tsv");

/// Resolve the MULTI-DOMAIN umem-form COHORT lean-key for an [`Effect`](crate::effect_vm::Effect)
/// whose state touch spans MORE THAN ONE domain in a single effect — the per-effect FIXED-cohort
/// descriptor (`UMEM_COHORT_MULTIDOMAIN_V1_STAGED_REGISTRY_TSV`) this effect's universal-memory
/// touch proves against. `None` = the effect is single-domain (resolve it through
/// [`umem_cohort_lean_key_for_effect`]) or a non-member (stays per-map). STAGED: the deployed default
/// never calls it.
///
/// The deployed multi-domain effects are the NOTE/BRIDGE economic verbs: each reveals/inserts a
/// `nullifiers`-domain freshness cell AND writes the `heap`-domain balance — domains `{heap (1),
/// nullifiers (3)}`, the producer's sorted-code order placing `heap` at guard column 6 and
/// `nullifiers` at guard column 7.
pub fn umem_cohort_multidomain_lean_key_for_effect(
    effect: &crate::effect_vm::Effect,
) -> Option<&'static str> {
    use crate::effect_vm::Effect;
    Some(match effect {
        // reveal a nullifier (nullifiers) + credit the balance (heap)
        Effect::NoteSpend { .. } => "noteSpendUMem",
        // insert an inbound bridged nullifier (nullifiers) + credit the balance (heap)
        Effect::BridgeMint { .. } => "bridgeMintUMem",
        _ => return None,
    })
}

/// The parseable descriptor JSON (third column) for a multi-domain umem-cohort lean-key in
/// [`UMEM_COHORT_MULTIDOMAIN_V1_STAGED_REGISTRY_TSV`]. `None` if the key is absent.
pub fn umem_cohort_multidomain_descriptor_json(lean_key: &str) -> Option<&'static str> {
    UMEM_COHORT_MULTIDOMAIN_V1_STAGED_REGISTRY_TSV
        .lines()
        .find_map(|line| {
            let mut it = line.splitn(3, '\t');
            if it.next() == Some(lean_key) {
                let _wire_name = it.next();
                it.next()
            } else {
                None
            }
        })
}

/// The wire-name suffix marking a descriptor as the rotated+umem WELD
/// ([`weld_umem_into_rotated_descriptor`]). A descriptor whose `name` ends with this is a STAGED
/// welded form — never a deployed-registry member.
pub const ROTATED_UMEM_WELD_SUFFIX: &str = "-umem-welded-staged";

/// The wire-name suffix marking a descriptor as the WIDE rotated+umem WELD
/// ([`weld_umem_into_wide_descriptor`]) — the WIDE (8-felt / ~124-bit faithful commit) twin of
/// [`ROTATED_UMEM_WELD_SUFFIX`]. A descriptor whose `name` ends with this is a STAGED welded form
/// over a WIDE descriptor (preserving the wide member's 16 commit PIs / 8-felt before-after
/// anchors); never a deployed-registry member.
pub const WIDE_UMEM_WELD_SUFFIX: &str = "-umem-wide-welded-staged";

/// The wire-name suffix marking a descriptor as the WIDE rotated+umem MULTI-DOMAIN WELD
/// ([`weld_umem_multidomain_into_wide_descriptor`]) — the two-domain twin of
/// [`WIDE_UMEM_WELD_SUFFIX`]. A descriptor whose `name` ends with this welds the MULTI-DOMAIN umem
/// cohort (one guarded `umemOp` per touched domain — the NOTE/BRIDGE economic verbs' `heap` balance
/// credit + `nullifiers` freshness insert) onto a WIDE descriptor, preserving the wide member's 16
/// commit PIs (8-felt ~124-bit anchors). Never a deployed-registry member.
pub const WIDE_UMEM_MULTIDOMAIN_WELD_SUFFIX: &str = "-umem-multidomain-wide-welded-staged";

/// **THE ROTATED+UMEM WELD (STAGED, VK-RISK-FREE) — the last precursor before the gated VK epoch.**
///
/// Weld the universal-memory COHORT leg INTO a rotated R=24 descriptor: keep the WHOLE rotated
/// constraint set (gates / transitions / pi-bindings / chip lookups) AND the rotated 46-PI vector
/// (`ROT_PI_COUNT` — the OLD/NEW state-commit pins at PI `V1_PI_COUNT` / `+1` the IVC chain fold
/// reads as `old_root` / `new_root`), and APPEND a SINGLE-domain `umem_op` reconciliation leg over
/// 7 fresh main columns `[base .. base+7)` (`base` = the rotated trace width) plus the `umemory`
/// (id 6, arity 8) / `umem_boundary` (id 7, arity 7) tables — exactly the cohort emitter's width-7
/// `umemOp` shape (`key · present · value · prev_present · prev_value · prev_serial · guard`),
/// offset to `base`.
///
/// This is the deployed flag-day weld in struct form: the per-map memory reconciliation moves INTO
/// the rotated descriptor as the universal-memory leg (`prove_vm_descriptor2_umem` with a REAL
/// `UMemBoundaryWitness`), while the rotated PIs stay INTACT — which is exactly what resolves the
/// two reconciliation seams the staged cohort leg named: (a) the umem leg now rides the rotated
/// descriptor's committed PI vector, and (b) the IVC fold's `old_root`/`new_root` PI accessors keep
/// working over the welded leg (the 0-PI cohort form could not supply them).
///
/// STAGED: a NEW descriptor BESIDE the deployed rotated registry — no VK bump, nothing on the live
/// wire. `domain` is the cohort domain the welded effect touches (heap 1 / caps 2 / nullifiers 3),
/// checked against the leg's actual domain by the prover.
pub fn weld_umem_into_rotated_descriptor(
    rotated: &crate::descriptor_ir2::EffectVmDescriptor2,
    domain: u32,
) -> crate::descriptor_ir2::EffectVmDescriptor2 {
    weld_umem_into_descriptor_with_suffix(rotated, domain, ROTATED_UMEM_WELD_SUFFIX, false)
}

/// **THE COHORT-SPECIALIZED ROTATED+UMEM WELD (STAGED, VK-RISK-FREE) — the IVC-fold perf lever.**
///
/// Identical to [`weld_umem_into_rotated_descriptor`] except the universal boundary table (id 7) is
/// declared with [`TableSem::UMemBoundaryCohort`](crate::descriptor_ir2::TableSem::UMemBoundaryCohort)
/// — the SINGLE-ROW specialization. The single-domain welded leg (e.g. a `Transfer`'s lone Balance
/// touch) reconciles AT MOST ONE `(domain, key)` cell, so the general boundary's ~29 columns of key
/// decomposition + lexicographic strict-increase comparator (which exist SOLELY to prove the declared
/// address list is `Nodup`) are dead weight: with one row, `Nodup` is `List.nodup_singleton` (Lean
/// `UniversalMemory.universal_memory_sound_single`, `#assert_axioms`-clean). This weld routes the leg
/// through the width-9 `Ir2Air::UMemBoundaryCohort`, quartering the boundary instance's FRI columns —
/// and that instance is re-paid up the WHOLE IVC aggregation tree, so the saving compounds. The
/// single-row discipline is enforced in-circuit (`next.is_real = 0` on every transition); a
/// multi-address witness is REFUSED at assembly and in the AIR, never silently mis-proved. A
/// multi-address single-domain leg must use the general [`weld_umem_into_rotated_descriptor`].
pub fn weld_umem_into_rotated_descriptor_cohort(
    rotated: &crate::descriptor_ir2::EffectVmDescriptor2,
    domain: u32,
) -> crate::descriptor_ir2::EffectVmDescriptor2 {
    weld_umem_into_descriptor_with_suffix(rotated, domain, ROTATED_UMEM_WELD_SUFFIX, true)
}

/// **THE WIDE ROTATED+UMEM WELD (STAGED, VK-RISK-FREE) — the real flip precursor the VK epoch
/// needs.** Weld the universal-memory COHORT leg INTO a WIDE descriptor (a member of
/// [`WIDE_REGISTRY_STAGED_TSV`], the verified Lean `v3RegistryCapOpenWide`, carrying the two 60×8
/// BEFORE/AFTER carriers + the 16 wide commit PIs = the 8-felt ~124-bit before/after anchors).
///
/// IDENTICAL append shape to [`weld_umem_into_rotated_descriptor`] — the single-domain cohort
/// `umemOp` over 7 fresh main columns `[base .. base+7)` (`base` = the WIDE trace width, PAST the
/// wide carriers) plus the `umemory` / `umem_boundary` tables — but onto the WIDE base. **Crucially
/// it PRESERVES the wide descriptor's `public_input_count` AND every existing constraint (incl. all
/// 16 wide-commit `PiBinding`s), so the welded form keeps the 8-felt before/after anchors at the
/// SAME PI offsets (the leg's LAST 16 PIs) — NO narrowing.** The weld is purely ADDITIVE (it appends
/// columns / tables / one `umemOp` constraint and NEVER edits `public_input_count` or any PI
/// binding), which is exactly why a proof under the welded descriptor binds the ~124-bit commitment
/// identically to the wide descriptor — the no-narrowing scar the VK epoch refused to cross.
///
/// This is the genuine deployable flag-day weld: the per-map memory reconciliation moves INTO the
/// WIDE rotated descriptor as the universal-memory leg, while the WIDE PIs (the 8-felt commit
/// `verify_full_turn_bound` binds) stay intact. STAGED: a NEW descriptor BESIDE the deployed wide
/// registry — no VK bump, nothing on the live wire. `domain` is the cohort domain the welded effect
/// touches (heap 1 / caps 2 / nullifiers 3), checked against the leg's actual domain by the prover.
pub fn weld_umem_into_wide_descriptor(
    wide: &crate::descriptor_ir2::EffectVmDescriptor2,
    domain: u32,
) -> crate::descriptor_ir2::EffectVmDescriptor2 {
    weld_umem_into_descriptor_with_suffix(wide, domain, WIDE_UMEM_WELD_SUFFIX, false)
}

/// **THE WIDE ROTATED+UMEM MULTI-DOMAIN WELD (STAGED, VK-RISK-FREE) — the last family tail.** The
/// two-domain twin of [`weld_umem_into_wide_descriptor`]: weld the MULTI-DOMAIN umem cohort leg INTO
/// a WIDE descriptor (a member of [`WIDE_REGISTRY_STAGED_TSV`]). Where the single-domain weld appends
/// ONE `umemOp` over 7 fresh columns, this appends the FIXED multi-domain cohort shape (the verified
/// Lean `EffectVmEmitUMemCohortMulti.umemCohortDesc2`, the byte-pinned
/// [`UMEM_COHORT_MULTIDOMAIN_V1_STAGED_REGISTRY_TSV`]): `6 + domains.len()` fresh main columns
/// `[base .. base + 6 + domains.len())` — `base+0..base+5` shared (`key · present · value ·
/// prev_present · prev_value · prev_serial`), one PER-DOMAIN guard at `base + 6 + i` — and ONE
/// `umemOp` per touched domain (in the supplied COLUMN order, the producer's sorted-domain-code order
/// `{heap (1), nullifiers (3)}`), each guarded at its own column. The NOTE/BRIDGE economic verbs touch
/// TWO domains in one effect (a `nullifiers` freshness insert + a `heap` balance credit), on which the
/// single-domain weld fails closed; this is their WIDE weld.
///
/// IDENTICAL no-narrowing property to [`weld_umem_into_wide_descriptor`]: it PRESERVES
/// `public_input_count` AND every existing constraint (incl. all 16 wide-commit `PiBinding`s), so the
/// 8-felt before/after anchors ride through INTACT at the SAME PI offsets. The cross-DOMAIN economic
/// invariant (the credit == the spent/minted value) is NOT a memory-reconciliation property — it rides
/// the effect's own rotated AIR (the whole rotated constraint set the weld preserves), exactly as in the
/// narrow multi-domain cohort. STAGED: a NEW descriptor BESIDE the deployed wide registry — no VK bump,
/// nothing on the live wire. `domains` is the per-op domain set in column order (heap 1 / caps 2 /
/// nullifiers 3), checked against the leg's actual domains by the prover.
pub fn weld_umem_multidomain_into_wide_descriptor(
    wide: &crate::descriptor_ir2::EffectVmDescriptor2,
    domains: &[u32],
) -> crate::descriptor_ir2::EffectVmDescriptor2 {
    use crate::descriptor_ir2::{
        MemKind, TID_UMEM_BOUNDARY, TID_UMEMORY, TableDef2, TableSem, UMemOpSpec, VmConstraint2,
    };
    use crate::lean_descriptor_air::LeanExpr;

    // The first fresh universal-memory operand column (the base form occupies `[0, base)`).
    let base = wide.trace_width;
    let mut welded = wide.clone();
    welded.name = format!("{}{WIDE_UMEM_MULTIDOMAIN_WELD_SUFFIX}", wide.name);
    // Shared base cols 0..5 + one guard per domain.
    welded.trace_width = base + 6 + domains.len();
    for t in welded.tables.iter_mut() {
        if t.sem == TableSem::Main {
            t.arity = welded.trace_width;
        }
    }
    // The universal-memory tables: `umemory` (arity 8) + the GENERAL `umem_boundary` (arity 7) — the
    // multi-domain cohort reconciles 2+ `(domain,key)` cells, so the single-row cohort boundary
    // (whose `Nodup` is vacuous) does NOT apply; it carries the general lexicographic comparator (the
    // byte-pinned multi-domain cohort descriptor declares the general `umem_boundary`).
    welded.tables.push(TableDef2 {
        id: TID_UMEMORY,
        name: "umemory".to_string(),
        arity: 8,
        sem: TableSem::UMemory,
    });
    welded.tables.push(TableDef2 {
        id: TID_UMEM_BOUNDARY,
        name: "umem_boundary".to_string(),
        arity: 7,
        sem: TableSem::UMemBoundary,
    });
    // One welded universal-memory WRITE op per touched domain — byte-for-byte the multi-domain cohort
    // `umemOp` shape (shared key/value/prev cols, per-domain guard), offset to `base`.
    for (i, &domain) in domains.iter().enumerate() {
        welded.constraints.push(VmConstraint2::UMemOp(UMemOpSpec {
            guard: LeanExpr::Var(base + 6 + i),
            domain,
            key: LeanExpr::Var(base),
            present: LeanExpr::Var(base + 1),
            value: LeanExpr::Var(base + 2),
            prev_present: LeanExpr::Var(base + 3),
            prev_value: LeanExpr::Var(base + 4),
            prev_serial: LeanExpr::Var(base + 5),
            kind: MemKind::Write,
        }));
    }
    welded
}

/// The shared, purely-ADDITIVE umem-cohort weld (the body of both
/// [`weld_umem_into_rotated_descriptor`] and [`weld_umem_into_wide_descriptor`]): append the
/// single-domain cohort `umemOp` over 7 fresh main columns + the `umemory` / `umem_boundary` tables
/// onto `desc`, marking the result with `suffix`. It NEVER touches `public_input_count` nor any
/// existing constraint, so the base descriptor's whole PI vector + every PI binding survive
/// unchanged — the property that lets the WIDE weld keep the 16 wide-commit PIs (the 8-felt
/// ~124-bit anchors) intact.
fn weld_umem_into_descriptor_with_suffix(
    desc: &crate::descriptor_ir2::EffectVmDescriptor2,
    domain: u32,
    suffix: &str,
    cohort: bool,
) -> crate::descriptor_ir2::EffectVmDescriptor2 {
    use crate::descriptor_ir2::{
        MemKind, TID_UMEM_BOUNDARY, TID_UMEMORY, TableDef2, TableSem, UMemOpSpec, VmConstraint2,
    };
    use crate::lean_descriptor_air::LeanExpr;

    // The first fresh universal-memory operand column (the base form occupies `[0, base)`).
    let base = desc.trace_width;
    let mut welded = desc.clone();
    welded.name = format!("{}{suffix}", desc.name);
    welded.trace_width = base + 7;
    // Widen the MAIN table arity (sem `Main`) to the welded width; the rotated chip/range/memory/
    // map tables keep their arities (the umem leg adds its own tables, below).
    for t in welded.tables.iter_mut() {
        if t.sem == TableSem::Main {
            t.arity = welded.trace_width;
        }
    }
    // Declare the universal-memory tables (the cohort emitter shape: `umemory` arity 8 carries the
    // domain-tagged Blum tuple + serial/gap lanes; `umem_boundary` arity 7 the declared
    // `(domain,key)` init/final image).
    welded.tables.push(TableDef2 {
        id: TID_UMEMORY,
        name: "umemory".to_string(),
        arity: 8,
        sem: TableSem::UMemory,
    });
    // The cohort weld declares the SINGLE-ROW boundary specialization: at most one declared
    // `(domain,key)` cell ⇒ the inter-row comparator + key decomposition are dropped (width 9 vs
    // 38; `Nodup` is free). The arity stays 7 (the witness-supplied init/final image shape is
    // unchanged); only the AIR routing + assembled trace width differ.
    welded.tables.push(TableDef2 {
        id: TID_UMEM_BOUNDARY,
        name: if cohort {
            "umem_boundary_cohort".to_string()
        } else {
            "umem_boundary".to_string()
        },
        arity: 7,
        sem: if cohort {
            TableSem::UMemBoundaryCohort
        } else {
            TableSem::UMemBoundary
        },
    });
    // The single welded universal-memory WRITE op over the appended 7 columns — byte-for-byte the
    // cohort `umemOp` (`circuit/descriptors/umem-cohort-v1-staged-registry.tsv`), offset to `base`.
    welded.constraints.push(VmConstraint2::UMemOp(UMemOpSpec {
        guard: LeanExpr::Var(base + 6),
        domain,
        key: LeanExpr::Var(base),
        present: LeanExpr::Var(base + 1),
        value: LeanExpr::Var(base + 2),
        prev_present: LeanExpr::Var(base + 3),
        prev_value: LeanExpr::Var(base + 4),
        prev_serial: LeanExpr::Var(base + 5),
        kind: MemKind::Write,
    }));
    welded
}

/// **THE FAITHFUL 8-FELT WIDE TRANSFER descriptor (STAGED-ADDITIVE slice).** The
/// `v3RegistryWide` transfer member (`wideAppend transferV3 bb (bb+51)`, width 816 / PI 54) —
/// the byte source of the first wide prove+verify roundtrip. Emitted from the verified Lean
/// `EffectVmEmitRotationWide.v3RegistryWide` (`metatheory/EmitWideTransferProbe.lean`), a `key\t
/// name\tjson` single line. ADDITIVE: the live 1-felt `V3_STAGED_REGISTRY_TSV` is UNTOUCHED — this
/// is the parallel wide path beside it. The wide carriers (cols 608..815) re-absorb the SAME
/// rotated limbs the 1-felt block lays into a genuine 8-felt (~124-bit) commitment, published on
/// PIs 38..53.
pub const WIDE_TRANSFER_STAGED_TSV: &str =
    include_str!("../descriptors/rotation-wide-transfer-staged.tsv");

/// **THE FAITHFUL 8-FELT WIDE REGISTRY (STAGED-ADDITIVE slice 2).** A member-for-member, name-stable
/// COVER of the live V3 registry (`rotation-v3-staged-registry.tsv`, 57 members) made 8-felt-wide:
/// each live member wrapped through the proven `wideAppend host bb (bb+51)` at its real per-member
/// BEFORE-limb base `bb` (the underlying v1 FACE width). The `key\tname\tjson` per line (key = the
/// live registry key, e.g. `burnVmDescriptor2R24`), emitted from the verified Lean
/// `CapOpenEmit.v3RegistryCapOpenWide` + the WRITE-bearing tail + the three live-only members
/// (`transferCapOpenTB` / `heapWrite` / `supplyMint`), in the LIVE order
/// (`metatheory/EmitWideRegistryProbe.lean`). `grantCapWriteCapOpen` is reconciled OUT (it is not a
/// live `V3_STAGED_REGISTRY_TSV` member). ADDITIVE: the live 1-felt `V3_STAGED_REGISTRY_TSV` / FP / VK
/// are UNTOUCHED — this is the parallel wide path beside them. The transfer row (row 0) is
/// byte-identical to `WIDE_TRANSFER_STAGED_TSV`. The wide carriers land PAST each member's host
/// width, re-absorbing the SAME rotated limbs the 1-felt block lays into a genuine 8-felt
/// (~124-bit) commitment (each wide member = its host width + the 960-column
/// `trace_rotated::WIDE_CARRIER_APPENDIX`, carrying the 16 wide commit PIs = the 8-felt
/// before/after anchors; the per-member widths are pinned by the drift tooth in
/// `wide_registry_parses_and_is_name_stable`).
pub const WIDE_REGISTRY_STAGED_TSV: &str =
    include_str!("../descriptors/rotation-wide-registry-staged.tsv");
pub const WIDE_REGISTRY_STAGED_FP: &str =
    "872fcb0d5ebdf809bddfb2808dd345859c200baa662ae6021701d5a9f06226a7";

/// **THE LEAN-EMITTED WIDE+UMEM WELDED REGISTRY (STAGED, VK-RISK-FREE) — the WIDE+umem weld's
/// MISSING VERIFIER LEG.** A member-for-member, name-stable welded twin of the wire's WIDE cap-open
/// registry: the 45 AUTHORITY-crown emit-source members (`CapOpenEmit.v3RegistryCapOpenWide`) PLUS
/// the 9 §10 WRITE-bearing cap-open tail wrappers (`CapOpenEmit.v3RegistryCapOpenWriteWide` minus
/// `grantCapWriteCapOpen`, which has no bare wide twin) — the `…WriteCapOpenVmDescriptor2R24`
/// descriptors the deployed wire routes a cap WRITE turn to (delegate / introduce / refresh / revoke
/// (Delegation/Capability) / spawn-via-cap). Each member is welded with the universal-memory cohort
/// leg (`umemOp` over 7 fresh columns PAST the wide carriers + the `umemory` / `umem_boundary`
/// tables) at the domain its effect touches, emitted from the verified Lean
/// `EffectVmEmitUMemWeldWide.weldedWideRegistry` (driver `metatheory/EmitWideUMemWeldRegistryProbe.lean`).
/// The `key\tname\tjson` per line; the KEY is the LIVE registry key (`transferVmDescriptor2R24` /
/// `delegateWriteCapOpenVmDescriptor2R24` etc.), the NAME carries [`WIDE_UMEM_WELD_SUFFIX`].
///
/// The weld is purely ADDITIVE — it appends columns / tables / one `umemOp` and NEVER edits
/// `public_input_count` nor any PI binding — so every welded member keeps the 16 wide-commit PIs
/// (the 8-felt ~124-bit before/after anchors) at the SAME offsets (NO narrowing). A welded proof
/// from [`prove_wide_umem_welded_staged`] verifies UNIQUELY against its member here (the Lean weld is
/// byte-parity-pinned to the Rust [`weld_umem_into_wide_descriptor`] — the `wide_umem_weld_registry_*`
/// tests). This is the descriptor set the wire verifiers (`verify_effect_vm_rotated_with_cutover`,
/// the IVC `admit_welded_leg`) iterate as a NEW accepted form BESIDE the bare wide registry. ADDITIVE:
/// the live 1-felt / bare wide registries / FP / VK are UNTOUCHED; `umem_witness_enabled` stays false.
pub const WIDE_UMEM_WELD_REGISTRY_TSV: &str =
    include_str!("../descriptors/rotation-wide-umem-welded-registry-staged.tsv");
pub const WIDE_UMEM_WELD_REGISTRY_FP: &str =
    "d17064a2435fe41e68202995201f2661ba98b8e81365cda09be8ce8b9834dcde";

// ============================================================================
// THE WIDE-CARRIER GEOMETRY VERSION BOUNDARY (the flag-day rotation, v2).
//
// v1 (RETIRED): 169 pre-iroot limbs → 57 carriers → 456-column block span → 912-column
//   appendix, commit carrier 56.
// v2 (LIVE):    178 pre-iroot limbs → 60 carriers → 480-column block span → 960-column
//   appendix, commit carrier 59 (`trace_rotated::WIDE_NUM_CARRIERS` et al., derived from
//   `NUM_PRE_LIMBS` by the shared `wide_carriers_for_limbs`).
//
// This is an APPROVED FLAG-DAY rotation: there is NO compatibility shim at the same
// assurance rung. A carried v1 registry member / VK-bearing descriptor is refused HERE with
// a TYPED error (`WideGeometryVersionError::RetiredV1`), never silently accepted or silently
// widened. The detector is STRUCTURAL and shift-invariant: it reads the descriptor's own 16
// wide anchor pins (the LAST 16 PI slots — 8 first-row BEFORE-commit columns, 8 last-row
// AFTER-commit columns) and measures the carrier BLOCK SPAN as the column distance between
// the BEFORE and AFTER commit carriers, which appended tails (umem welds, teeth, digest
// appendixes, refuse welds) never move.
// ============================================================================

/// The LIVE wide-carrier geometry version (see the boundary note above).
pub const WIDE_CARRIER_GEOMETRY_VERSION: u32 = 2;
/// The RETIRED v1 per-block carrier span (57 carriers × 8 = 456 columns over the 169-limb body).
pub const WIDE_CARRIER_BLOCK_SPAN_RETIRED_V1: usize = 456;

/// Typed refusal at the wide-carrier geometry-version boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WideGeometryVersionError {
    /// The artifact carries the RETIRED v1 (57-carrier / 456-block-span / 912-appendix)
    /// carrier shape. Old registries/VKs are version-refused, not widened.
    RetiredV1 {
        /// The presented descriptor's name.
        name: String,
        /// The measured BEFORE→AFTER commit-carrier span (456 for v1).
        block_span: usize,
    },
    /// The artifact's anchor pins measure a block span that matches NO known wide-carrier
    /// geometry version (neither the live v2 nor the retired v1).
    UnknownGeometry {
        /// The presented descriptor's name.
        name: String,
        /// The measured BEFORE→AFTER commit-carrier span.
        block_span: usize,
    },
    /// The artifact claims a wide PI tail but its 16 wide anchor pins are missing or
    /// malformed (no first-row BEFORE / last-row AFTER commit pins at the tail slots).
    MissingAnchors {
        /// The presented descriptor's name.
        name: String,
    },
}

impl core::fmt::Display for WideGeometryVersionError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::RetiredV1 { name, block_span } => write!(
                f,
                "'{name}': RETIRED wide-carrier geometry v1 (block span {block_span} = 57 \
                 carriers; the live version is v{WIDE_CARRIER_GEOMETRY_VERSION}: 60 carriers / \
                 480-column block / commit carrier 59) — old registries/VKs are version-refused, \
                 not silently widened"
            ),
            Self::UnknownGeometry { name, block_span } => write!(
                f,
                "'{name}': wide anchor pins measure carrier block span {block_span}, which is \
                 no known wide-carrier geometry version (live v{WIDE_CARRIER_GEOMETRY_VERSION} \
                 = 480; retired v1 = {WIDE_CARRIER_BLOCK_SPAN_RETIRED_V1})"
            ),
            Self::MissingAnchors { name } => write!(
                f,
                "'{name}': wide-shaped descriptor is missing its 16 wide anchor pins (no \
                 first-row BEFORE / last-row AFTER commit pins at the PI tail)"
            ),
        }
    }
}

impl std::error::Error for WideGeometryVersionError {}

/// **The structural wide-carrier geometry-version detector.** Reads the descriptor's own 16
/// wide anchor pins — the LAST 16 PI slots, of which slot `piCount-16` is the first-row
/// BEFORE-commit lane-0 pin and slot `piCount-8` the last-row AFTER-commit lane-0 pin — and
/// measures the carrier BLOCK SPAN as `after_col - before_col`. That span is exactly
/// `WIDE_NUM_CARRIERS × 8` for every `wideAppend`-derived member and is INVARIANT under every
/// appended tail (umem weld columns, teeth columns, digest appendixes, refuse welds), so it
/// classifies any carried wide artifact regardless of composition:
///
/// * `Ok(WIDE_CARRIER_GEOMETRY_VERSION)` — the live v2 span (480);
/// * `Err(RetiredV1)` — the retired v1 span (456): explicit version refusal;
/// * `Err(UnknownGeometry)` / `Err(MissingAnchors)` — fail closed on anything else.
pub fn wide_carrier_geometry_version(
    d: &crate::descriptor_ir2::EffectVmDescriptor2,
) -> Result<u32, WideGeometryVersionError> {
    use crate::descriptor_ir2::VmConstraint2;
    use crate::effect_vm::trace_rotated::WIDE_CARRIER_BLOCK_SPAN;
    use crate::lean_descriptor_air::{VmConstraint, VmRow};
    let pi = d.public_input_count;
    if pi < 16 {
        return Err(WideGeometryVersionError::MissingAnchors {
            name: d.name.clone(),
        });
    }
    let mut before0: Option<usize> = None; // first-row pin of PI slot pi-16 (BEFORE lane 0)
    let mut after0: Option<usize> = None; // last-row pin of PI slot pi-8 (AFTER lane 0)
    for c in &d.constraints {
        if let VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index }) = c {
            match row {
                VmRow::First if *pi_index == pi - 16 => before0 = Some(*col),
                VmRow::Last if *pi_index == pi - 8 => after0 = Some(*col),
                _ => {}
            }
        }
    }
    let (Some(b), Some(a)) = (before0, after0) else {
        return Err(WideGeometryVersionError::MissingAnchors {
            name: d.name.clone(),
        });
    };
    let Some(block_span) = a.checked_sub(b) else {
        return Err(WideGeometryVersionError::MissingAnchors {
            name: d.name.clone(),
        });
    };
    if block_span == WIDE_CARRIER_BLOCK_SPAN {
        Ok(WIDE_CARRIER_GEOMETRY_VERSION)
    } else if block_span == WIDE_CARRIER_BLOCK_SPAN_RETIRED_V1 {
        Err(WideGeometryVersionError::RetiredV1 {
            name: d.name.clone(),
            block_span,
        })
    } else {
        Err(WideGeometryVersionError::UnknownGeometry {
            name: d.name.clone(),
            block_span,
        })
    }
}

/// **The v2 admission gate** — `Ok(())` iff the carried wide artifact rides the LIVE
/// wide-carrier geometry version. Every wide acceptance boundary (the IVC `admit_welded_leg`,
/// registry consumers) calls THIS, so the retired 57/56 shape is refused with the typed
/// [`WideGeometryVersionError`], never silently admitted.
pub fn require_wide_carrier_geometry_v2(
    d: &crate::descriptor_ir2::EffectVmDescriptor2,
) -> Result<(), WideGeometryVersionError> {
    wide_carrier_geometry_version(d).map(|_| ())
}

// ============================================================================
// THE CUSTOM PROOF-BIND COMMITMENT VERSION BOUNDARY (the flag-day rotation, v2).
//
// v1 (RETIRED): the Custom member published a 4-felt `custom_proof_commitment`
//   (~62-bit birthday collision resistance) — 8 exposure pins total: commit limbs
//   0..4 (cols `PARAM_BASE+4..8`) at the exposure base, then the 4 low vk-hash
//   limbs (cols `PARAM_BASE..+4`) immediately after.
// v2 (LIVE): the full 8-felt `WideHash` class (~124-bit birthday) — 12 exposure
//   pins: commit limbs 0..4 (cols `PARAM_BASE+4..8`), commit limbs 4..8 (the
//   member-local COMMIT-TEETH columns past the host,
//   `trace_rotated::CUSTOM_COMMIT_TEETH_BASE`), then the 4 low vk-hash limbs.
//
// APPROVED FLAG-DAY rotation (proof-bridge upstream blocker #2): NO compatibility
// shim at the same assurance rung. A carried v1 custom descriptor / VK is refused
// HERE with a TYPED error (`CustomCommitVersionError::RetiredV1`), never silently
// accepted, zero-padded, or widened. The detector is STRUCTURAL and
// shift-invariant: it locates the commitment exposure block by the FIRST-row pin
// of column `PARAM_BASE + CUSTOM_PROOF_COMMIT_BASE` (commit limb 0) and
// classifies the pins at the four slots after the low commit block — the v1
// layout puts the VK block there (param columns); v2 puts the commit teeth
// (non-param columns) there, with the VK block after.
// ============================================================================

/// The LIVE custom proof-bind commitment version (see the boundary note above).
pub const CUSTOM_COMMIT_VERSION: u32 = 2;
/// The RETIRED v1 commitment width (felts).
pub const CUSTOM_COMMIT_WIDTH_RETIRED_V1: usize = 4;
/// The LIVE v2 commitment width (felts).
pub const CUSTOM_COMMIT_WIDTH_V2: usize = 8;

/// Typed refusal at the custom proof-bind commitment version boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CustomCommitVersionError {
    /// The artifact publishes the RETIRED v1 4-felt `custom_proof_commitment`
    /// (the VK block rides directly after the low commit limbs — no commit
    /// teeth). Old custom descriptors/VKs are version-refused, not widened.
    RetiredV1 {
        /// The presented descriptor's name.
        name: String,
        /// The exposure block's commitment PI base (slot of commit limb 0).
        commit_pi_lo: usize,
    },
    /// The artifact carries no first-row pin of the `custom_proof_commitment`
    /// column (`PARAM_BASE + CUSTOM_PROOF_COMMIT_BASE`) — it is not a
    /// custom-exposure member at all; fail closed.
    MissingCommitPins {
        /// The presented descriptor's name.
        name: String,
    },
    /// The pins after the low commit block match NEITHER the retired v1 VK
    /// block NOR the live v2 commit-teeth + VK layout; fail closed.
    UnknownLayout {
        /// The presented descriptor's name.
        name: String,
        /// The exposure block's commitment PI base (slot of commit limb 0).
        commit_pi_lo: usize,
    },
}

impl core::fmt::Display for CustomCommitVersionError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::RetiredV1 { name, commit_pi_lo } => write!(
                f,
                "'{name}': RETIRED custom proof-bind commitment v1 (4 felts / ~62-bit birthday, \
                 exposure at PI {commit_pi_lo}..{}) — the live version is \
                 v{CUSTOM_COMMIT_VERSION}: {CUSTOM_COMMIT_WIDTH_V2} felts (~124-bit) with the \
                 second squeeze block on the commit-teeth columns; old custom artifacts are \
                 version-refused, never zero-padded or silently widened",
                commit_pi_lo + CUSTOM_COMMIT_WIDTH_RETIRED_V1
            ),
            Self::MissingCommitPins { name } => write!(
                f,
                "'{name}': no first-row `custom_proof_commitment` exposure pin (col \
                 PARAM_BASE+CUSTOM_PROOF_COMMIT_BASE) — not a custom-exposure member (fail closed)"
            ),
            Self::UnknownLayout { name, commit_pi_lo } => write!(
                f,
                "'{name}': the pins after the low commit block (PI {commit_pi_lo}..{}) match \
                 neither the retired v1 VK block nor the live v{CUSTOM_COMMIT_VERSION} \
                 commit-teeth layout (fail closed)",
                commit_pi_lo + CUSTOM_COMMIT_WIDTH_RETIRED_V1
            ),
        }
    }
}

impl std::error::Error for CustomCommitVersionError {}

/// **The structural custom-commitment version detector.** Locates the custom
/// exposure block by the FIRST-row pin of the `custom_proof_commitment` column
/// (`PARAM_BASE + CUSTOM_PROOF_COMMIT_BASE`, commit limb 0 — shift-invariant:
/// the param union never moves) and classifies the four PI slots directly after
/// the low commit block:
///
/// * `Ok(CUSTOM_COMMIT_VERSION)` — v2: those slots pin NON-param columns (the
///   commit teeth carrying limbs 4..8), and the VK block (cols
///   `PARAM_BASE..+4`) rides at the four slots after THEM;
/// * `Err(RetiredV1)` — v1: those slots pin the VK block directly (cols
///   `PARAM_BASE..+4`) — the 4-felt legacy exposure: explicit version refusal;
/// * `Err(MissingCommitPins)` / `Err(UnknownLayout)` — fail closed.
pub fn custom_commit_version(
    d: &crate::descriptor_ir2::EffectVmDescriptor2,
) -> Result<u32, CustomCommitVersionError> {
    use crate::descriptor_ir2::VmConstraint2;
    use crate::effect_vm::columns::{PARAM_BASE, param};
    use crate::lean_descriptor_air::{VmConstraint, VmRow};

    let commit_col0 = PARAM_BASE + param::CUSTOM_PROOF_COMMIT_BASE;
    // Collect ALL first-row pins keyed by PI slot.
    let mut first_pins: std::collections::BTreeMap<usize, usize> =
        std::collections::BTreeMap::new();
    let mut commit_pi_lo: Option<usize> = None;
    for c in &d.constraints {
        if let VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index }) = c {
            if *row == VmRow::First {
                first_pins.insert(*pi_index, *col);
                if *col == commit_col0 {
                    commit_pi_lo = Some(*pi_index);
                }
            }
        }
    }
    let Some(lo) = commit_pi_lo else {
        return Err(CustomCommitVersionError::MissingCommitPins {
            name: d.name.clone(),
        });
    };
    let is_vk_block = |base: usize, pins: &std::collections::BTreeMap<usize, usize>| -> bool {
        (0..4)
            .all(|k| pins.get(&(base + k)) == Some(&(PARAM_BASE + param::CUSTOM_VK_HASH_BASE + k)))
    };
    // The four slots after the low commit block.
    let mid = lo + CUSTOM_COMMIT_WIDTH_RETIRED_V1;
    if is_vk_block(mid, &first_pins) {
        // v1: commit limbs 0..4, then the VK block directly — the retired 4-felt exposure.
        return Err(CustomCommitVersionError::RetiredV1 {
            name: d.name.clone(),
            commit_pi_lo: lo,
        });
    }
    // v2: slots mid..mid+4 must pin four NON-param columns (the commit teeth, contiguous and
    // ascending), and the VK block must ride directly after them.
    let teeth_ok = (0..CUSTOM_COMMIT_WIDTH_RETIRED_V1).all(|k| {
        first_pins
            .get(&(mid + k))
            .is_some_and(|&col| col >= crate::effect_vm::trace_rotated::V1_WIDTH)
    });
    if teeth_ok && is_vk_block(mid + CUSTOM_COMMIT_WIDTH_RETIRED_V1, &first_pins) {
        return Ok(CUSTOM_COMMIT_VERSION);
    }
    Err(CustomCommitVersionError::UnknownLayout {
        name: d.name.clone(),
        commit_pi_lo: lo,
    })
}

/// Require the LIVE (v2, 8-felt) custom proof-bind commitment layout; refuse the
/// retired 4-felt v1 (and anything unclassifiable) with a typed error. The custom
/// fold arm and the custom-wide leg mint call this at admission — old 4-felt
/// custom artifacts never enter the upgraded assurance rung.
pub fn require_custom_commit_teeth_v2(
    d: &crate::descriptor_ir2::EffectVmDescriptor2,
) -> Result<(), CustomCommitVersionError> {
    custom_commit_version(d).map(|_| ())
}

/// The rotated probe layout at register count `r` (the Rust twin of the Lean parametric
/// layout `EffectVmEmitRotationR`: columns are FUNCTIONS of R; the chunking is 4-wide head,
/// 3-wide chip groups while ≥ 3 remain, singletons after — arity ∈ {2,4}, NEVER 3 — and the
/// iroot rides its own arity-2 final site, literally last).
pub fn rotation_layout_for(r: usize) -> RotationLayoutR {
    let m = r + 3; // post-head pre-iroot fresh inputs
    let num_sites = 1 + m / 3 + m % 3 + 1; // head + 3-groups + singletons + the iroot site
    RotationLayoutR {
        num_registers: r,
        committed_height: r + 6,
        iroot: r + 7,
        state_commit: r + 8,
        block_size: r + 9,
        chain_base: r + 9,
        num_chain: num_sites - 1,
        probe_width: r + 9 + num_sites - 1,
    }
}

/// See [`rotation_layout_for`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RotationLayoutR {
    pub num_registers: usize,
    pub committed_height: usize,
    pub iroot: usize,
    pub state_commit: usize,
    pub block_size: usize,
    pub chain_base: usize,
    pub num_chain: usize,
    pub probe_width: usize,
}

// ==== ALL unique descriptors (name -> json, fingerprint): the total name registry ====
pub const ALL_DESCRIPTORS: &[(&str, &str, &str)] = &[
    (
        "dregg-effectvm-attenuateA-v1",
        DREGG_EFFECTVM_ATTENUATEA_V1_JSON,
        DREGG_EFFECTVM_ATTENUATEA_V1_FP,
    ),
    (
        "dregg-effectvm-bridgemint-v1",
        DREGG_EFFECTVM_BRIDGEMINT_V1_JSON,
        DREGG_EFFECTVM_BRIDGEMINT_V1_FP,
    ),
    (
        "dregg-effectvm-burn-v1",
        DREGG_EFFECTVM_BURN_V1_JSON,
        DREGG_EFFECTVM_BURN_V1_FP,
    ),
    (
        "dregg-effectvm-celldestroy-v2",
        DREGG_EFFECTVM_CELLDESTROY_V2_JSON,
        DREGG_EFFECTVM_CELLDESTROY_V2_FP,
    ),
    (
        "dregg-effectvm-cellseal-v2",
        DREGG_EFFECTVM_CELLSEAL_V2_JSON,
        DREGG_EFFECTVM_CELLSEAL_V2_FP,
    ),
    (
        "dregg-effectvm-cellunseal-v2",
        DREGG_EFFECTVM_CELLUNSEAL_V2_JSON,
        DREGG_EFFECTVM_CELLUNSEAL_V2_FP,
    ),
    (
        "dregg-effectvm-createcell-v2",
        DREGG_EFFECTVM_CREATECELL_V2_JSON,
        DREGG_EFFECTVM_CREATECELL_V2_FP,
    ),
    (
        "dregg-effectvm-createcellfromfactory-v2",
        DREGG_EFFECTVM_CREATECELLFROMFACTORY_V2_JSON,
        DREGG_EFFECTVM_CREATECELLFROMFACTORY_V2_FP,
    ),
    (
        "dregg-effectvm-emitEvent-v1",
        DREGG_EFFECTVM_EMITEVENT_V1_JSON,
        DREGG_EFFECTVM_EMITEVENT_V1_FP,
    ),
    (
        "dregg-effectvm-exerciseA-holdlayer-v2",
        DREGG_EFFECTVM_EXERCISEA_HOLDLAYER_V2_JSON,
        DREGG_EFFECTVM_EXERCISEA_HOLDLAYER_V2_FP,
    ),
    (
        "dregg-effectvm-incrementNonce-v2",
        DREGG_EFFECTVM_INCREMENTNONCE_V2_JSON,
        DREGG_EFFECTVM_INCREMENTNONCE_V2_FP,
    ),
    (
        "dregg-effectvm-makesovereign-v2",
        DREGG_EFFECTVM_MAKESOVEREIGN_V2_JSON,
        DREGG_EFFECTVM_MAKESOVEREIGN_V2_FP,
    ),
    (
        "dregg-effectvm-mint-v1",
        DREGG_EFFECTVM_MINT_V1_JSON,
        DREGG_EFFECTVM_MINT_V1_FP,
    ),
    (
        "dregg-effectvm-notecreate-v1",
        DREGG_EFFECTVM_NOTECREATE_V1_JSON,
        DREGG_EFFECTVM_NOTECREATE_V1_FP,
    ),
    (
        "dregg-effectvm-notespend-v1",
        DREGG_EFFECTVM_NOTESPEND_V1_JSON,
        DREGG_EFFECTVM_NOTESPEND_V1_FP,
    ),
    (
        "dregg-effectvm-pipelinedSendA-v2",
        DREGG_EFFECTVM_PIPELINEDSENDA_V2_JSON,
        DREGG_EFFECTVM_PIPELINEDSENDA_V2_FP,
    ),
    (
        "dregg-effectvm-introduce-v2",
        DREGG_EFFECTVM_INTRODUCE_V2_JSON,
        DREGG_EFFECTVM_INTRODUCE_V2_FP,
    ),
    (
        "dregg-effectvm-receiptArchiveA-v2",
        DREGG_EFFECTVM_RECEIPTARCHIVEA_V2_JSON,
        DREGG_EFFECTVM_RECEIPTARCHIVEA_V2_FP,
    ),
    (
        "dregg-effectvm-refreshDelegation-v2",
        DREGG_EFFECTVM_REFRESHDELEGATION_V2_JSON,
        DREGG_EFFECTVM_REFRESHDELEGATION_V2_FP,
    ),
    (
        "dregg-effectvm-refusal-v2",
        DREGG_EFFECTVM_REFUSAL_V2_JSON,
        DREGG_EFFECTVM_REFUSAL_V2_FP,
    ),
    (
        "dregg-effectvm-revokecapability-v1",
        DREGG_EFFECTVM_REVOKECAPABILITY_V1_JSON,
        DREGG_EFFECTVM_REVOKECAPABILITY_V1_FP,
    ),
    (
        "dregg-effectvm-revokeDelegation-v2",
        DREGG_EFFECTVM_REVOKEDELEGATION_V2_JSON,
        DREGG_EFFECTVM_REVOKEDELEGATION_V2_FP,
    ),
    (
        "dregg-effectvm-setPermissionsA-v2",
        DREGG_EFFECTVM_SETPERMISSIONSA_V2_JSON,
        DREGG_EFFECTVM_SETPERMISSIONSA_V2_FP,
    ),
    (
        "dregg-effectvm-setVK-v2",
        DREGG_EFFECTVM_SETVK_V2_JSON,
        DREGG_EFFECTVM_SETVK_V2_FP,
    ),
    (
        "dregg-effectvm-spawnA-v3-actorrow",
        DREGG_EFFECTVM_SPAWNA_V3_ACTORROW_JSON,
        DREGG_EFFECTVM_SPAWNA_V3_ACTORROW_FP,
    ),
    (
        "dregg-effectvm-transfer-v1",
        DREGG_EFFECTVM_TRANSFER_V1_JSON,
        DREGG_EFFECTVM_TRANSFER_V1_FP,
    ),
    (
        "dregg-effectvm-record-v1",
        DREGG_EFFECTVM_RECORD_V1_JSON,
        DREGG_EFFECTVM_RECORD_V1_FP,
    ),
];

/// Look up the EffectVM descriptor JSON bound to a running-prover **selector index**
/// (`effect_vm::columns::sel`). Returns the byte-exact Lean-emitted wire JSON, or
/// `None` if no verified descriptor is registered for that selector yet.
pub fn descriptor_for_selector(sel: usize) -> Option<&'static str> {
    SELECTOR_DESCRIPTORS
        .iter()
        .find(|(s, _, _, _)| *s == sel)
        .map(|(_, _, json, _)| *json)
}

/// The descriptor `name` (canonical wire identity) bound to a selector index.
pub fn descriptor_name_for_selector(sel: usize) -> Option<&'static str> {
    SELECTOR_DESCRIPTORS
        .iter()
        .find(|(s, _, _, _)| *s == sel)
        .map(|(_, name, _, _)| *name)
}

/// Look up a descriptor JSON by its canonical `name` (e.g. `"dregg-effectvm-burn-v1"`).
/// This is the TOTAL registry: every unique emitted descriptor, including the
/// name-only ones with no dedicated selector. Returns the byte-exact wire JSON.
pub fn descriptor_for_name(name: &str) -> Option<&'static str> {
    ALL_DESCRIPTORS
        .iter()
        .find(|(n, _, _)| *n == name)
        .map(|(_, json, _)| *json)
}

/// The committed SHA-256 fingerprint of the descriptor JSON for `name`.
pub fn fingerprint_for_name(name: &str) -> Option<&'static str> {
    ALL_DESCRIPTORS
        .iter()
        .find(|(n, _, _)| *n == name)
        .map(|(_, _, fp)| *fp)
}

/// Look up an IR-v2 descriptor JSON by its Lean def-name key (e.g. `"transferVmDescriptor2"`,
/// `"setFieldVmDescriptor2-3"`). The byte-exact `emitVmJson2` wire (`"ir":2`), interpreted by
/// `descriptor_ir2::parse_vm_descriptor2`. ADDITIVE: the v1 path (`descriptor_for_selector` /
/// `descriptor_for_name`) stays the live one until the cutover lane flips the pointer.
pub fn descriptor2_for_key(key: &str) -> Option<&'static str> {
    V2_DESCRIPTORS
        .iter()
        .find(|(k, _, _)| *k == key)
        .map(|(_, json, _)| *json)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_ir2::parse_vm_descriptor2;
    use crate::lean_descriptor_air::parse_vm_descriptor;

    /// Self-contained SHA-256 (FIPS 180-4), no external dep, so the drift
    /// fingerprints are reproducible from this file alone. Returns the lowercase
    /// hex digest of `data`.
    fn sha256_hex(data: &[u8]) -> String {
        const K: [u32; 64] = [
            0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
            0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
            0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
            0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
            0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
            0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
            0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
            0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
            0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
            0xc67178f2,
        ];
        let mut h: [u32; 8] = [
            0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
            0x5be0cd19,
        ];
        let mut msg = data.to_vec();
        let bitlen = (data.len() as u64) * 8;
        msg.push(0x80);
        while msg.len() % 64 != 56 {
            msg.push(0);
        }
        msg.extend_from_slice(&bitlen.to_be_bytes());

        for chunk in msg.chunks(64) {
            let mut w = [0u32; 64];
            for i in 0..16 {
                w[i] = u32::from_be_bytes([
                    chunk[4 * i],
                    chunk[4 * i + 1],
                    chunk[4 * i + 2],
                    chunk[4 * i + 3],
                ]);
            }
            for i in 16..64 {
                let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
                let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
                w[i] = w[i - 16]
                    .wrapping_add(s0)
                    .wrapping_add(w[i - 7])
                    .wrapping_add(s1);
            }
            let (mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh) =
                (h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7]);
            for i in 0..64 {
                let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
                let ch = (e & f) ^ ((!e) & g);
                let t1 = hh
                    .wrapping_add(s1)
                    .wrapping_add(ch)
                    .wrapping_add(K[i])
                    .wrapping_add(w[i]);
                let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
                let maj = (a & b) ^ (a & c) ^ (b & c);
                let t2 = s0.wrapping_add(maj);
                hh = g;
                g = f;
                f = e;
                e = d.wrapping_add(t1);
                d = c;
                c = b;
                b = a;
                a = t1.wrapping_add(t2);
            }
            h[0] = h[0].wrapping_add(a);
            h[1] = h[1].wrapping_add(b);
            h[2] = h[2].wrapping_add(c);
            h[3] = h[3].wrapping_add(d);
            h[4] = h[4].wrapping_add(e);
            h[5] = h[5].wrapping_add(f);
            h[6] = h[6].wrapping_add(g);
            h[7] = h[7].wrapping_add(hh);
        }
        let mut out = String::with_capacity(64);
        for word in h {
            for byte in word.to_be_bytes() {
                out.push_str(&format!("{byte:02x}"));
            }
        }
        out
    }

    /// Sanity: the SHA-256 impl matches the FIPS test vector for "abc".
    #[test]
    fn sha256_self_test() {
        assert_eq!(
            sha256_hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        assert_eq!(
            sha256_hex(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
    }

    /// Every registered descriptor re-parses via `parse_vm_descriptor` into the
    /// structure the prover consumes, with the parsed `name` matching the registry
    /// key and a positive trace width. (The Lean↔JSON drift gate is generate-fresh
    /// `scripts/check-descriptor-drift.sh`, not a self-consistent FP rehash.)
    #[test]
    fn all_descriptors_parse() {
        assert_eq!(ALL_DESCRIPTORS.len(), 27, "expected 27 unique descriptors");
        for (name, json, _fp) in ALL_DESCRIPTORS {
            let desc = parse_vm_descriptor(json)
                .unwrap_or_else(|e| panic!("descriptor {name} failed to parse: {e}"));
            assert_eq!(
                &desc.name, name,
                "descriptor {name}: parsed name {:?} != registry key",
                desc.name
            );
            assert!(desc.trace_width > 0, "descriptor {name}: zero trace_width");
        }
    }

    /// The selector table is consistent with the name registry: each selector's
    /// JSON is identical to the `ALL_DESCRIPTORS` entry of the same name, and every
    /// selector descriptor parses.
    #[test]
    fn selector_table_consistent() {
        for (sel, name, json, _fp) in SELECTOR_DESCRIPTORS {
            let by_name = descriptor_for_name(name)
                .unwrap_or_else(|| panic!("selector {sel} name {name} not in ALL_DESCRIPTORS"));
            assert_eq!(
                *json, by_name,
                "selector {sel}: JSON differs from name registry"
            );
            assert_eq!(descriptor_for_selector(*sel), Some(*json));
            assert_eq!(descriptor_name_for_selector(*sel), Some(*name));
            parse_vm_descriptor(json)
                .unwrap_or_else(|e| panic!("selector {sel} descriptor failed to parse: {e}"));
        }
        // No selector index is registered twice.
        let mut sels: Vec<usize> = SELECTOR_DESCRIPTORS.iter().map(|(s, _, _, _)| *s).collect();
        sels.sort_unstable();
        let n = sels.len();
        sels.dedup();
        assert_eq!(sels.len(), n, "duplicate selector index in registry");
        // The transfer selector (1) resolves to the transfer descriptor.
        assert_eq!(
            descriptor_name_for_selector(crate::effect_vm::columns::sel::TRANSFER),
            Some("dregg-effectvm-transfer-v1")
        );
        // An unregistered selector (NOOP) yields None.
        assert_eq!(
            descriptor_for_selector(crate::effect_vm::columns::sel::NOOP),
            None
        );
    }

    /// The name-only descriptors are real, distinct, and present in the total
    /// registry (they just lack a dedicated Rust selector slot).
    #[test]
    fn name_only_descriptors_present() {
        assert_eq!(NAME_ONLY_DESCRIPTORS.len(), 1);
        for (name, json, _fp) in NAME_ONLY_DESCRIPTORS {
            assert_eq!(descriptor_for_name(name), Some(*json));
            // not bound to any selector
            assert!(
                SELECTOR_DESCRIPTORS.iter().all(|(_, n, _, _)| n != name),
                "name-only descriptor {name} unexpectedly has a selector"
            );
        }
    }

    /// THE IR-v2 ROUND-TRIP: every `V2_DESCRIPTORS` entry round-trips through the v2 decoder
    /// `descriptor_ir2::parse_vm_descriptor2` — a `"ir":2` wire with the five EPOCH tables and the
    /// lookup/mem_op/map_op grammar, NOT the v1 wire — into the structure the prover consumes
    /// (five tables, positive width, empty v1 carriers). The Lean↔JSON drift gate is generate-fresh
    /// `scripts/check-descriptor-drift.sh`, not a self-consistent FP rehash.
    #[test]
    fn v2_descriptors_parse() {
        assert_eq!(V2_DESCRIPTORS.len(), 28, "expected 28 IR-v2 descriptors");
        for (key, json, _fp) in V2_DESCRIPTORS {
            // round-trips through the v2 multi-table decoder
            let d = parse_vm_descriptor2(json)
                .unwrap_or_else(|e| panic!("v2 descriptor {key} failed parse_vm_descriptor2: {e}"));
            assert_eq!(
                d.tables.len(),
                5,
                "v2 descriptor {key}: not the five EPOCH tables"
            );
            assert!(d.trace_width > 0, "v2 descriptor {key}: zero trace_width");
            // graduated v1 descriptors carry NO legacy hash-site/range carriers (lookup-shaped).
            assert!(
                d.hash_sites.is_empty() && d.ranges.is_empty(),
                "v2 descriptor {key}: a graduated descriptor must carry empty v1 carriers"
            );
            // the accessor resolves it
            assert_eq!(descriptor2_for_key(key), Some(*json));
        }
        // The transfer v2 graduated descriptor is present and 186-wide (the validated reference).
        let t = parse_vm_descriptor2(
            descriptor2_for_key("transferVmDescriptor2").expect("transfer v2 present"),
        )
        .unwrap();
        assert_eq!(
            t.trace_width, 216,
            "graduated transfer = 188 base + 7·4 chip lane cols (Phase B-GATE: 4 hash sites)"
        );
        assert_eq!(t.public_input_count, 42);
    }

    /// THE ROTATION LAYOUT DRIFT GUARD (staged): rebuild the Lean
    /// `rotationLayoutManifest` byte-for-byte from `effect_vm::columns::rotation`
    /// + `pi::v3` and compare against the committed Lean-emitted file. Both sides
    /// PIN (Lean `#guard`s the same literal), neither parses — a layout fact can
    /// only change by re-emitting from Lean AND re-anchoring these constants.
    #[test]
    fn rotation_layout_matches_lean() {
        use crate::effect_vm::columns::rotation as rot;
        use crate::effect_vm::pi;
        let twin = format!(
            "{{\"v\":\"dregg-rotation-layout-v3-staged\",\"block_size\":{},\"cells_root\":{},\
             \"reg_base\":{},\"num_registers\":{},\"cap_root\":{},\"nullifier_root\":{},\
             \"heap_root\":{},\"lifecycle\":{},\"epoch\":{},\"committed_height\":{},\
             \"iroot\":{},\"state_commit\":{},\"chain_base\":{},\"num_chain\":{},\
             \"probe_width\":{},\"chain_arity\":{},\"pi_v3\":{{\"v2_base_count\":{},\
             \"committed_height\":{},\"rate_bound_tag\":{},\"challenge_window_tag\":{}}}}}",
            rot::BLOCK_SIZE,
            rot::CELLS_ROOT,
            rot::REG_BASE,
            rot::NUM_REGISTERS,
            rot::CAP_ROOT,
            rot::NULLIFIER_ROOT,
            rot::HEAP_ROOT,
            rot::LIFECYCLE,
            rot::EPOCH,
            rot::COMMITTED_HEIGHT,
            rot::IROOT,
            rot::STATE_COMMIT,
            rot::CHAIN_BASE,
            rot::NUM_CHAIN,
            rot::PROBE_WIDTH,
            rot::CHAIN_ARITY,
            pi::BASE_COUNT,
            pi::v3::COMMITTED_HEIGHT,
            pi::v3::RATE_BOUND_TAG,
            pi::v3::CHALLENGE_WINDOW_TAG,
        );
        assert_eq!(
            twin, ROTATION_LAYOUT_V3_STAGED_JSON,
            "rotation layout drift: columns::rotation / pi::v3 no longer match the \
             Lean-emitted manifest (re-emit EmitRotationV3.lean and re-anchor)"
        );
    }

    /// The v3-staged probe registry: round-trip through the IR-v2 decoder + PRESENCE
    /// at EVERY register count — each probe's chip-lookup chain must absorb EVERY
    /// rotated limb column exactly once, in the absorption order, with the final
    /// digest on `STATE_COMMIT` (a re-emit that drops a limb — e.g. the heap_root, or
    /// a widened register — fails HERE, before any prover runs). The presence-refusal
    /// tooth scales with the block: a wider block with untested columns would be
    /// worse than a narrow one.
    #[test]
    fn v3_staged_descriptors_parse_and_cover_all_limbs() {
        use crate::descriptor_ir2::VmConstraint2;
        use crate::effect_vm::columns::rotation as rot;
        use crate::lean_descriptor_air::LeanExpr;
        assert_eq!(
            V3_STAGED_DESCRIPTORS.len(),
            3,
            "expected 3 v3-staged descriptors"
        );
        // The R=16 entry is the deployed reference: its parametric twin must agree with
        // the pinned `columns.rs::rotation` constants exactly.
        let l16 = rotation_layout_for(16);
        assert_eq!(l16.committed_height, rot::COMMITTED_HEIGHT);
        assert_eq!(l16.iroot, rot::IROOT);
        assert_eq!(l16.state_commit, rot::STATE_COMMIT);
        assert_eq!(l16.block_size, rot::BLOCK_SIZE);
        assert_eq!(l16.chain_base, rot::CHAIN_BASE);
        assert_eq!(l16.num_chain, rot::NUM_CHAIN);
        assert_eq!(l16.probe_width, rot::PROBE_WIDTH);
        // R=24: exact 3-fill (no mid arity-2 site); R=32: two arity-2 mid sites.
        assert_eq!(rotation_layout_for(24).probe_width, 43);
        assert_eq!(rotation_layout_for(24).num_chain, 10);
        assert_eq!(rotation_layout_for(32).probe_width, 55);
        assert_eq!(rotation_layout_for(32).num_chain, 14);
        for (key, json, _fp) in V3_STAGED_DESCRIPTORS {
            let r = match *key {
                "rotationProbeVmDescriptor2" => 16,
                "rotationProbeVmDescriptorR24" => 24,
                "rotationProbeVmDescriptorR32" => 32,
                other => panic!("unknown v3-staged key {other}"),
            };
            let lay = rotation_layout_for(r);
            let d = parse_vm_descriptor2(json)
                .unwrap_or_else(|e| panic!("v3 staged {key} failed parse_vm_descriptor2: {e}"));
            // Phase B-GATE: graduated width = probe width + 7·n_sites lane cols
            // (n_sites = num_chain head/body absorbs + 1 iroot absorb).
            assert_eq!(
                d.trace_width,
                lay.probe_width + 7 * (lay.num_chain + 1),
                "{key}: probe width + 7·n_sites chip lane cols"
            );
            assert_eq!(d.public_input_count, 2);
            assert!(
                d.hash_sites.is_empty() && d.ranges.is_empty(),
                "graduated carriers only"
            );
            // PRESENCE: walk the chip lookups in order; collect fresh (non-chain) absorbed
            // columns; they must be exactly 0..=IROOT in order, and each non-final site's
            // digest must be the next chain carrier, the final site's digest STATE_COMMIT.
            // Also: every site's fresh-input arity ∈ {4 head, 3, 1} (+1 digest ⇒ chip
            // arity ∈ {2,4}; an arity-3 site would REFUSE on the deployed chip AIR).
            let mut absorbed: Vec<usize> = Vec::new();
            let mut digests: Vec<usize> = Vec::new();
            for c in &d.constraints {
                if let VmConstraint2::Lookup(l) = c {
                    let vars: Vec<usize> = l
                        .tuple
                        .iter()
                        .filter_map(|e| match e {
                            LeanExpr::Var(v) => Some(*v),
                            _ => None,
                        })
                        .collect();
                    // Phase B-GATE: the 17-wide tuple's var run is `[input vars …, out0 (digest),
                    // lane1..lane7]`. The output block is the last CHIP_OUT_LANES vars; the digest
                    // (out0) is its HEAD, the inputs are everything before it.
                    use crate::descriptor_ir2::CHIP_OUT_LANES;
                    let split = vars.len() - CHIP_OUT_LANES;
                    let inputs = &vars[..split];
                    let digest = &vars[split];
                    digests.push(*digest);
                    let fresh: Vec<usize> = inputs
                        .iter()
                        .copied()
                        .filter(|v| *v < lay.block_size)
                        .collect();
                    let chained = inputs.len() - fresh.len();
                    assert!(
                        (chained == 0 && fresh.len() == 4)
                            || (chained == 1 && (fresh.len() == 3 || fresh.len() == 1)),
                        "{key}: site shape must be 4-fresh head or digest+3 / digest+1 \
                         (chip arity ∈ {{2,4}}), got {chained} chained + {} fresh",
                        fresh.len()
                    );
                    absorbed.extend(fresh);
                }
            }
            let expected: Vec<usize> = (0..=lay.iroot).collect();
            assert_eq!(
                absorbed, expected,
                "{key}: the probe must absorb every rotated limb column exactly once, in \
                 the absorption order (cells root, {r} registers, cap/nullifier/heap \
                 roots, lifecycle, epoch, committed height, iroot LAST)"
            );
            let expected_digests: Vec<usize> = (0..lay.num_chain)
                .map(|k| lay.chain_base + k)
                .chain(std::iter::once(lay.state_commit))
                .collect();
            assert_eq!(
                digests, expected_digests,
                "{key}: chained digest carriers, final = STATE_COMMIT"
            );
        }
    }

    /// THE CAVEAT-OPERAND LAYOUT DRIFT GUARD (staged): rebuild the Lean
    /// `rotationCaveatLayoutManifest` byte-for-byte from
    /// `columns::rotation::caveat` and compare against the committed
    /// Lean-emitted file. Both sides PIN (Lean `#guard`s the same literal),
    /// neither parses.
    #[test]
    fn rotation_caveat_layout_matches_lean() {
        use crate::effect_vm::columns::rotation::caveat as cav;
        let twin = format!(
            "{{\"v\":\"dregg-rotation-caveat-layout-v3-staged\",\"r\":{},\
             \"caveat_base\":{},\"count_col\":{},\"entry_base\":{},\"entry_size\":{},\
             \"max_caveats\":{},\"manifest_size\":{},\"chain_base\":{},\"num_chain\":{},\
             \"caveat_commit\":{},\"probe_width\":{},\"domain_registers\":{},\
             \"domain_heap\":{},\"pub_commit\":{},\"pub_height\":{},\"pub_caveat\":{}}}",
            cav::R,
            cav::BASE,
            cav::COUNT_COL,
            cav::ENTRY_BASE,
            cav::ENTRY_SIZE,
            cav::MAX_CAVEATS,
            cav::MANIFEST_SIZE,
            cav::CHAIN_BASE,
            cav::NUM_CHAIN,
            cav::CAVEAT_COMMIT,
            cav::PROBE_WIDTH,
            cav::DOMAIN_REGISTERS,
            cav::DOMAIN_HEAP,
            cav::PUB_COMMIT,
            cav::PUB_HEIGHT,
            cav::PUB_CAVEAT,
        );
        assert_eq!(
            twin, ROTATION_CAVEAT_LAYOUT_V3_STAGED_JSON,
            "caveat-operand layout drift: columns::rotation::caveat no longer matches \
             the Lean-emitted manifest (re-emit EmitRotationV3.lean and re-anchor)"
        );
    }

    /// The staged caveat probe: round-trip through the IR-v2 decoder + PRESENCE — the
    /// chip-lookup chain must absorb the WHOLE R=24 rotated block (cells root … iroot)
    /// AND the WHOLE 29-felt caveat manifest block (count + every entry's type tag,
    /// DOMAIN TAG, KEY, params) exactly once, in order, with the rotation digest
    /// landing on `state_commit` and the caveat digest on `CAVEAT_COMMIT`. A re-emit
    /// that drops a manifest column (e.g. a domain tag) fails HERE, before any prover
    /// runs.
    #[test]
    fn v3_staged_caveat_descriptor_parses_and_covers_manifest() {
        use crate::descriptor_ir2::VmConstraint2;
        use crate::effect_vm::columns::rotation::caveat as cav;
        use crate::lean_descriptor_air::LeanExpr;
        assert_eq!(V3_STAGED_CAVEAT_DESCRIPTORS.len(), 1);
        let (key, json, _fp) = V3_STAGED_CAVEAT_DESCRIPTORS[0];
        let d = parse_vm_descriptor2(json)
            .unwrap_or_else(|e| panic!("{key} failed parse_vm_descriptor2: {e}"));
        // Phase B-GATE: graduated width = caveat probe width + 7·n_sites chip lane cols (the
        // before/after rotated absorbs + the caveat absorbs); the surplus is a multiple of 7.
        assert!(
            d.trace_width >= cav::PROBE_WIDTH && (d.trace_width - cav::PROBE_WIDTH) % 7 == 0,
            "{key}: caveat probe width + 7·n_sites chip lane cols"
        );
        assert_eq!(d.public_input_count, 3, "{key}: three PI pins");
        assert!(
            d.hash_sites.is_empty() && d.ranges.is_empty(),
            "graduated carriers only"
        );
        let rot = rotation_layout_for(cav::R);
        // Walk the chip lookups in order; collect fresh (non-carrier) absorbed columns.
        // Fresh = a rotated limb column (0..=iroot) or a caveat manifest column
        // (BASE..BASE+MANIFEST_SIZE). Expected coverage: the rotation absorption order,
        // then the manifest columns in order. Digest carriers: the rotation chain +
        // state_commit, then the caveat chain + CAVEAT_COMMIT.
        let is_fresh =
            |v: usize| v <= rot.iroot || (cav::BASE..cav::BASE + cav::MANIFEST_SIZE).contains(&v);
        let mut absorbed: Vec<usize> = Vec::new();
        let mut digests: Vec<usize> = Vec::new();
        for c in &d.constraints {
            if let VmConstraint2::Lookup(l) = c {
                let vars: Vec<usize> = l
                    .tuple
                    .iter()
                    .filter_map(|e| match e {
                        LeanExpr::Var(v) => Some(*v),
                        _ => None,
                    })
                    .collect();
                // Phase B-GATE: 17-wide tuple — output block is the last CHIP_OUT_LANES vars; out0
                // (the digest) is its head, inputs precede it.
                use crate::descriptor_ir2::CHIP_OUT_LANES;
                let split = vars.len() - CHIP_OUT_LANES;
                let inputs = &vars[..split];
                let digest = &vars[split];
                digests.push(*digest);
                let fresh: Vec<usize> = inputs.iter().copied().filter(|v| is_fresh(*v)).collect();
                let chained = inputs.len() - fresh.len();
                assert!(
                    (chained == 0 && fresh.len() == 4)
                        || (chained == 1 && (fresh.len() == 3 || fresh.len() == 1)),
                    "{key}: site shape must be 4-fresh head or carrier+3 / carrier+1 \
                     (chip arity ∈ {{2,4}}), got {chained} chained + {} fresh",
                    fresh.len()
                );
                absorbed.extend(fresh);
            }
        }
        let expected: Vec<usize> = (0..=rot.iroot)
            .chain(cav::BASE..cav::BASE + cav::MANIFEST_SIZE)
            .collect();
        assert_eq!(
            absorbed, expected,
            "{key}: must absorb every rotated limb AND every caveat manifest felt \
             (count, type tags, DOMAIN TAGS, KEYS, params) exactly once, in order"
        );
        let expected_digests: Vec<usize> = (0..rot.num_chain)
            .map(|k| rot.chain_base + k)
            .chain(std::iter::once(rot.state_commit))
            .chain((0..cav::NUM_CHAIN).map(|k| cav::CHAIN_BASE + k))
            .chain(std::iter::once(cav::CAVEAT_COMMIT))
            .collect();
        assert_eq!(
            digests, expected_digests,
            "{key}: rotation chain → state_commit, then caveat chain → CAVEAT_COMMIT"
        );
    }

    /// THE FULL-COHORT REGEN guard (`ROTATION-CUTOVER.md` §5 item 1): every line of the
    /// staged 26-descriptor registry round-trips through the IR-v2 decoder, and each
    /// descriptor carries the rotated appendix EXACTLY — two rotated state blocks (each
    /// absorbing cells-root … iroot in order onto its own state-commit carrier) + the
    /// widened-caveat region (the 29-felt manifest onto CAVEAT_COMMIT), with the four
    /// appended PI pins (rotated OLD/NEW commit · height · caveat commit) at the
    /// descriptor's own `piCount..piCount+3`. A re-emit that drops a limb, a manifest felt,
    /// or a PI pin fails HERE, before any prover runs. STAGED: nothing on the live wire.
    #[test]
    fn v3_staged_registry_parses_and_covers() {
        use crate::descriptor_ir2::VmConstraint2;
        use crate::effect_vm::columns::EFFECT_VM_WIDTH;
        use crate::effect_vm::columns::rotation::caveat as cav;
        use crate::lean_descriptor_air::{LeanExpr, VmConstraint};

        // The DEPLOYED rotated geometry (the v12 pre_limbs re-lay: NUM_PRE_LIMBS = 112 — the bare
        // R=24 registers + cells/cap/nullifier/commitments/heap/lifecycle/epoch/height/disc roots +
        // the 8-felt completion limbs 37..87 + the v12 carrier-material octets 88..111). Source-of-truth = the canonical
        // `trace_rotated` constants (which STEP-1 grew), NOT re-hardcoded literals; mirrors the Lean
        // `EffectVmEmitRotationV3` §1 constants and the caveat region inside it.
        use crate::effect_vm::trace_rotated::{
            B_CHAIN_BASE, B_COMMITTED_HEIGHT, B_IROOT, B_SPAN, B_STATE_COMMIT,
        };
        const V1_WIDTH: usize = EFFECT_VM_WIDTH;
        // chain carriers occupy `[B_CHAIN_BASE, B_SPAN)` (the head digest + one per 3-wide group).
        const B_NUM_CHAIN: usize = B_SPAN - B_CHAIN_BASE; // 37 (v12: 112 limbs)
        // The caveat region grew 39 → 43 with the dsl rc-EMIT: the 4-felt `Witnessed{Dfa}`
        // route-commitment carrier rides in-region offsets 39..=42 on EVERY rotated member's
        // layout (`trace_rotated::C_SPAN`); only the PI pins (`withDfaRcPins`) are per-member.
        const C_SPAN: usize = crate::effect_vm::trace_rotated::C_SPAN; // 43 (v12 + rc)
        const C_COMMIT: usize = cav::MANIFEST_SIZE + cav::NUM_CHAIN; // 29 + 9 = 38
        const APPENDIX_SPAN: usize = 2 * B_SPAN + C_SPAN; // 345 (v12 + rc)

        let mut n = 0usize;
        for line in V3_STAGED_REGISTRY_TSV.lines() {
            if line.is_empty() {
                continue;
            }
            n += 1;
            let mut it = line.splitn(3, '\t');
            let key = it.next().expect("tsv key");
            let name = it.next().expect("tsv name");
            let json = it.next().expect("tsv json");
            let d = parse_vm_descriptor2(json)
                .unwrap_or_else(|e| panic!("v3 registry {key} failed parse_vm_descriptor2: {e}"));

            // THE CAP-OPEN MEMBERS (the LIVE `transferCapOpenEffV3`/`attenuateCapOpenEffV3` + 6 fan-out) carry
            // the 59-column cap-membership APPENDIX past the shared rotated layout (= V1_WIDTH +
            // APPENDIX_SPAN + 59) plus 1 leaf + 16 node chip-lookups + the cap-open base gates. The
            // appendix is 59 = the 58 prior columns + 1 `effBit` column (residual (a): the turn's
            // ACTUAL effect-kind bit, against which the general `facetEffGate` binds the leaf mask —
            // not the constant EFFECT_TRANSFER). Both share the appendix (base-agnostic), so they are
            // audited on the SAME own contract (width, PI count, cap-open chip lookups present) and
            // SKIP the rotated-cohort absorb/digest/pin equalities below.
            // The cap-open authority members: the 2 transfer/attenuate legs + the 6 effect-general
            // fan-out legs (delegate, introduce, grantCap, revoke, refreshDelegation,
            // revokeCapability), each carrying the SAME 59-column appendix (base-agnostic) over its
            // own rotated base. The fan-out legs' appendix binds the cap to THAT effect-kind bit (the
            // general `facetEffGate` / `effBitGateFor (1<<<n)`), not the constant EFFECT_TRANSFER.
            if key.contains("CapOpen") {
                // The TURN-IDENTITY weld (`transferCapOpenTBVmDescriptor2R24`,
                // CapOpenTurnPins.effCapOpenV3TB) is the cap-open PLUS two turn-identity columns
                // (capOpenActorCol/capOpenDstCol) and three turn-identity PI pins (welding the
                // cap-open `src`/`actor`/`dst` columns to the published turn PIs). So it carries the
                // 91-column cap-membership appendix + 2 turn-identity columns = +93, and 46 + 3 = 49
                // PIs. The cap-membership chip-lookup count (1 leaf + 16 node) is unchanged.
                let is_tb = key.contains("CapOpenTB");
                let extra_cols = if is_tb { 2 } else { 0 };
                // The spawn cap-open members (`spawnCapOpen`/`spawnWriteCapOpen`) are the ONLY cap-fanout
                // members built over a BIRTH base (`spawnV3`/`spawnWriteV3`): spawn carries the extra
                // new-cell-key PI weld (`ROT_NEW_CELL_KEY_PI = 46`, the child id pinned on row 0), so its
                // rotated base publishes 47 PIs (the 46-PI vector + 1), not 46. So the cap-open wrapper
                // inherits 47 PIs. Every other cap-open member rides a non-birth base (46 PIs).
                let is_spawn = key.starts_with("spawn");
                let extra_pis = if is_tb { 3 } else { 0 } + if is_spawn { 1 } else { 0 };
                // Phase H-CAP-8: the FAITHFUL 8-FELT cap-open appendix. The native `node8` arity-16
                // tree commits the WHOLE 8-felt digest group per absorb (the 7 spare permutation
                // lanes are PROMOTED into the bound fold — no separate `7·17` lane tail). The Lean
                // twin `CapOpenEmit.CAP_OPEN_SPAN = 7 + 8 + DEPTH·17 + 8 + 2 + MASK_BITS`:
                //   7 leaf scalar + 8 leaf-digest + DEPTH·(8 sib + 1 dir + 8 node) + 8 cap_root
                //   + src + effBit + 32 mask-bit = 7 + 8 + 16·17 + 8 + 2 + 32 = 329.
                let cap_span = 7 + 8 + 16 * 17 + 8 + 2 + 32; // CAP_OPEN_SPAN = 329
                // The cap-WRITE members (`effCapOpenWriteV3`: attenuate + the delegation-mutating
                // writes) carry the AFTER-SPINE recompute appendix PAST the 329-col read appendix —
                // `CapOpenEmit.AFTER_SPINE_SPAN = 15 + 8·DEPTH = 143` (after-leaf + after-leaf-digest
                // + DEPTH·8 after-node), forcing the faithful 8-felt cap-WRITE (`*_forces_write8`).
                let after_spine_span = 15 + 8 * 16; // AFTER_SPINE_SPAN = 143
                // THE AVAILABILITY-WELD PAD (GAP #4, cap-open member): a hardened `…-v1-avail`
                // transfer cap-open member widens its v1 FACE by the avail witness columns, so its
                // rotated base — and hence the graduated width the cap-open appendix anchors at —
                // shifts by the pad. Zero for every bare member.
                let cap_avail_pad =
                    crate::effect_vm::trace_rotated::avail_pad_for_descriptor_name(name);
                let rot_base = V1_WIDTH + APPENDIX_SPAN + cap_avail_pad;
                let appendix = cap_span + extra_cols;
                // The rotated base graduates by `7·n_rot_sites` wire-commit lane cols (still 7-felt;
                // only the CAP DIGEST groups went 8-felt). So the width is
                //   rot_base + 7·n_sites + 329 (+ 2 TB) (+ 143 after-spine for write/attenuate).
                // 143 % 7 ≠ 0, so the with/without-after-spine forms are mutually EXCLUSIVE — the
                // residual cleanly decides which member this is (no name-keyed dispatch).
                assert!(
                    d.trace_width >= rot_base + appendix,
                    "{key}: cap-open trace width below rotated base + 329 cap-membership appendix"
                );
                let surplus = d.trace_width - rot_base - appendix;
                let has_after_spine = surplus % 7 != 0;
                let lane_surplus = if has_after_spine {
                    surplus.checked_sub(after_spine_span)
                } else {
                    Some(surplus)
                };
                assert!(
                    matches!(lane_surplus, Some(s) if s % 7 == 0),
                    "{key}: cap-open trace width = rotated base (+ 7·n_rot_sites lane cols) + 329 \
                     cap-membership appendix (+2 TB cols) (+143 after-spine for write/attenuate)"
                );
                assert_eq!(
                    d.public_input_count,
                    46 + extra_pis,
                    "{key}: cap-open carries the rotated 46-PI vector (+3 turn-identity PIs for TB)"
                );
                // The cap-open READ appendix declares EXACTLY 17 poseidon2 chip lookups whose DIGEST
                // (out0, tuple col CHIP_RATE+1) lands in the cap-membership CORE column block
                // `[cap_open_base, cap_open_base + 287)` (= leaf 7 + leaf-digest 8 + DEPTH·17 level
                // blocks; `capRoot` starts at +287): 1 leaf absorb + 16 node absorbs. The after-spine
                // recompute's own 17 lookups land at `[cap_open_base + 329, …)` — PAST the core
                // window — so a write member still counts exactly the read spine's 17.
                use crate::descriptor_ir2::CHIP_RATE;
                // Recover the appendix base from the total width. The cap appendix starts at the
                // GRADUATED rotated width (`base.traceWidth`); for write/attenuate members the
                // after-spine sits past it, so subtract it too: `cap_open_base = trace_width -
                // CAP_OPEN_SPAN(329) - extra_cols (- AFTER_SPINE_SPAN(143) if write)`.
                let cap_membership_core = 7 + 8 + 16 * 17; // leaf + leaf-digest + DEPTH·17 = 287
                let cap_open_base = d.trace_width
                    - cap_span
                    - extra_cols
                    - if has_after_spine { after_spine_span } else { 0 };
                let cap_lookups = d
                    .constraints
                    .iter()
                    .filter(|c| {
                        if let VmConstraint2::Lookup(l) = c {
                            matches!(
                                l.tuple.get(CHIP_RATE + 1),
                                Some(LeanExpr::Var(v))
                                    if *v >= cap_open_base && *v < cap_open_base + cap_membership_core
                            )
                        } else {
                            false
                        }
                    })
                    .count();
                assert_eq!(
                    cap_lookups, 17,
                    "{key}: cap-open read appendix declares 1 leaf + 16 node chip lookups"
                );
                continue;
            }

            // Phase B-GATE: graduation appends `7·n_sites` chip lane columns past the rotated base,
            // so the GRADUATED width's surplus over the appendix is a multiple of 7 (n_sites varies
            // by v1 face; concrete widths pinned by the emit goldens + fingerprints). Two deployed
            // welds ride KNOWN, non-lane columns PAST the graduated width — account for each
            // EXPLICITLY (never fold it into the 7·n_sites lane count), CONFIRM it landed, and strip
            // back to the graduated width before the mod-7 lane check:
            //   · the GENTIAN FLAG-DAY bare-floor-refuse weld (`BareCohortFloorRefuse`) appends three
            //     disjoint decode+refuse aux blocks ANCHORED at GRAD_ROT_WIDTH onto every deployed
            //     bare cohort member (the `-gentian-deployed-bare-refuse` suffix), extending its width
            //     to exactly `floor_col(last)+1`;
            //   · the STAGED discharge/vault satisfaction descriptors ride their satisfaction-gate
            //     FIELD columns past the graduated transfer base (settleEscrow's ride EXISTING field
            //     columns and add none; discharge/vault add the cursor/total/due + G5 free-param /
            //     no-dilution gadget columns).
            use crate::effect_vm::bare_floor_refuse_weld as refuse;
            use crate::effect_vm::trace_rotated::GRAD_ROT_WIDTH;
            // THE AVAILABILITY-WELD PAD (GAP #4): a hardened `…-v1-avail` transfer/burn member
            // widens its v1 FACE by the avail witness columns, so its rotated appendix, refuse
            // anchor, and rc carrier all shift by the pad. Zero for every bare member.
            let avail_pad = crate::effect_vm::trace_rotated::avail_pad_for_descriptor_name(name);
            // §HETEROGENEOUS GEOMETRY. Two members do NOT graduate to `GRAD_ROT_WIDTH`, and the
            // reason is the ROTATION-SITE COUNT, not the face width:
            //   * `setFieldDynV1Face` has the SAME v1 face width (`EFFECT_VM_WIDTH`) as the cohort but
            //     `hashSites := []` — ZERO hash sites against the standard 4. Since
            //     `GRAD_ROT_WIDTH = ROT_WIDTH + 7·N_ROT_SITES`, dropping 4 sites drops exactly
            //     4·7 = 28 LANE columns, so it graduates at 1647 − 28 = 1619 (width 1664).
            //   * `custom` rides that same zero-site shape PLUS the 4 COMMIT-TEETH columns of the
            //     8-felt proof-bind rotation, appended PAST the lanes: base 1623 (width 1668).
            // The lane deficit is a multiple of 7 BY CONSTRUCTION (it is 7 per dropped site), so it
            // cannot break the `% 7` lane invariant below. Custom's 4 teeth CAN — they are not lane
            // columns — so they are the only thing that must come out before the modulus is taken.
            const SETFIELD_DYN_LANE_DEFICIT: usize = 28; // 4 dropped hash sites × 7 lane cols
            const CUSTOM_COMMIT_TEETH: usize = 4;
            let (lane_deficit, commit_teeth) = match key {
                "customVmDescriptor2R24" => (SETFIELD_DYN_LANE_DEFICIT, CUSTOM_COMMIT_TEETH),
                "setFieldDynVmDescriptor2R24" => (SETFIELD_DYN_LANE_DEFICIT, 0),
                _ => (0, 0),
            };
            let is_refuse_welded = name.ends_with("-gentian-deployed-bare-refuse");
            let graduated_width = if is_refuse_welded {
                // The three per-tag refuse blocks anchor at the member's OWN graduated width
                // (GRAD_ROT_WIDTH + its avail pad); the deployed width extends EXACTLY to cover
                // the last floor column (`floor_col(NB-1)+1`). CONFIRM the flip is REAL: assert
                // that exact geometry AND that all three `floor_col(b) == 0` refuse gates are
                // PRESENT in the committed descriptor (a positive coverage tooth for the
                // flag-day, not a width fudge). Derived from the weld's own constants, so a
                // stride/block change moves BOTH the width tooth and the gate check together.
                const NB: usize = refuse::CAPACITY_TAGS.len();
                // The refuse blocks anchor at the member's OWN graduated base (see §HETEROGENEOUS
                // GEOMETRY above), so re-base the cohort's `GRAD_ROT_WIDTH`-anchored `floor_col`.
                let member_base = GRAD_ROT_WIDTH - lane_deficit + commit_teeth;
                let rebase = |c: usize| c - GRAD_ROT_WIDTH + member_base;
                let refuse_end = rebase(refuse::floor_col(NB - 1)) + 1 + avail_pad;
                assert_eq!(
                    d.trace_width, refuse_end,
                    "{key}: refuse-welded member width must extend exactly to cover the {NB} \
                     bare-floor-refuse aux blocks anchored at its own graduated width"
                );
                for b in 0..NB {
                    let fc = rebase(refuse::floor_col(b)) + avail_pad;
                    assert!(
                        d.constraints.iter().any(|c| matches!(
                            c,
                            VmConstraint2::Base(VmConstraint::Gate(LeanExpr::Var(v))) if *v == fc
                        )),
                        "{key}: bare-floor-refuse gate (floor_col({b}) == {fc} == 0) missing — the \
                         gentian flag-day weld did not land on this cohort member"
                    );
                }
                member_base + avail_pad
            } else if key == "dischargeSatVmDescriptor2R24" || key == "vaultSatVmDescriptor2R24" {
                // The STAGED discharge/vault satisfaction descriptors graduate on the transfer base
                // (GRAD_ROT_WIDTH) and carry their satisfaction-gate FIELD columns PAST it. Pin the
                // exact committed widths (a drift tooth on the satisfaction-gadget span, read from the
                // committed registry TSV) and strip back to the graduated base for the lane check.
                let expected = if key == "dischargeSatVmDescriptor2R24" {
                    1720 // GRAD_ROT_WIDTH(1647) + the cursor/total/due + G5 free-param bind columns
                } else {
                    // GRAD_ROT_WIDTH(1647) + the no-dilution (Ta·m ≤ Sa·d) satisfaction columns.
                    // Re-pinned 2121 → 2185 from the emitted TSV: the satisfaction-gadget span grew
                    // by 64 columns with the arity-3 IMT / AAFI accumulator rewiring. This is a raw
                    // drift tooth (a literal read off the committed artifact), so it MUST be re-read
                    // whenever the gadget changes — it does not derive itself.
                    2185
                };
                assert_eq!(
                    d.trace_width, expected,
                    "{key}: staged satisfaction descriptor width = graduated base + its \
                     satisfaction-gate columns"
                );
                GRAD_ROT_WIDTH
            } else {
                d.trace_width
            };
            // The graduated width is the (avail-padded) v1 face + the rotated appendix + `7·n_sites`
            // LANE columns + any COMMIT-TEETH columns appended past the lanes. Every member shares the
            // same v1 face width, and a dropped hash site removes a whole 7-column lane, so the lane
            // residue stays ≡ 0 (mod 7) for setFieldDyn's zero-site shape without any special-casing.
            // Only custom's 4 COMMIT-TEETH columns are non-lane, so they are the one thing that must
            // be taken out before the modulus — otherwise its residue is 4 and the invariant would be
            // "fixed" by fudging a face delta that does not exist.
            let lane_base = V1_WIDTH + avail_pad + APPENDIX_SPAN + commit_teeth;
            assert!(
                graduated_width >= lane_base && (graduated_width - lane_base) % 7 == 0,
                "{key}: rotated GRADUATED trace width = (avail-padded) v1 face + appendix + \
                 7·n_sites lane cols + commit teeth"
            );
            assert!(
                d.hash_sites.is_empty() && d.ranges.is_empty(),
                "{key}: graduated carriers only"
            );

            // The three appendix blocks, past the (avail-padded) v1 layout.
            let before_base = V1_WIDTH + avail_pad;
            let after_base = before_base + B_SPAN;
            let caveat_base = before_base + 2 * B_SPAN;

            // A "fresh limb" of the appendix is a column inside one of the three blocks'
            // LIMB ranges (before/after rotated limbs 0..=iroot, or the caveat manifest
            // 0..MANIFEST_SIZE) — NOT a chain-carrier column (those ride the accumulator as
            // inputs but are not absorbed data). We audit only appendix sites (digest >=
            // V1_WIDTH); the v1 descriptor's own chip lookups absorb columns < V1_WIDTH.
            let is_limb = |v: usize| -> bool {
                (before_base..=before_base + B_IROOT).contains(&v)
                    || (after_base..=after_base + B_IROOT).contains(&v)
                    || (caveat_base..caveat_base + cav::MANIFEST_SIZE).contains(&v)
            };
            let mut digests: Vec<usize> = Vec::new();
            let mut absorbed: Vec<usize> = Vec::new();
            for c in &d.constraints {
                if let VmConstraint2::Lookup(l) = c {
                    if l.table != crate::descriptor_ir2::TID_P2 {
                        continue;
                    }
                    // Phase B-GATE: the 17-wide tuple is `[arity, in0..in7, out0, lane1..lane7]`.
                    // out0 (the digest) is at fixed position CHIP_RATE + 1; the input vars are the
                    // bare-Var entries in `[1 ..= CHIP_RATE]` (lanes are NOT inputs).
                    use crate::descriptor_ir2::CHIP_RATE;
                    let LeanExpr::Var(digest) = l.tuple[CHIP_RATE + 1] else {
                        panic!("{key}: chip lookup out0 (col CHIP_RATE+1) must be a bare Var");
                    };
                    if digest >= V1_WIDTH {
                        digests.push(digest);
                        for e in &l.tuple[1..=CHIP_RATE] {
                            if let LeanExpr::Var(v) = e {
                                if is_limb(*v) {
                                    absorbed.push(*v);
                                }
                            }
                        }
                    }
                }
            }

            // Expected fresh absorption: before-block limbs 0..=iroot, after-block limbs,
            // then the caveat manifest 0..MANIFEST_SIZE — all relative to their bases.
            let mut expected_absorbed: Vec<usize> = Vec::new();
            expected_absorbed.extend((0..=B_IROOT).map(|i| before_base + i));
            expected_absorbed.extend((0..=B_IROOT).map(|i| after_base + i));
            expected_absorbed.extend((0..cav::MANIFEST_SIZE).map(|i| caveat_base + i));
            assert_eq!(
                absorbed, expected_absorbed,
                "{key}: appendix must absorb the BEFORE block, the AFTER block, then the \
                 29-felt caveat manifest, each limb exactly once in absorption order"
            );

            // Expected digest carriers: before chain → before state_commit; after chain →
            // after state_commit; caveat chain → caveat commit.
            let mut expected_digests: Vec<usize> = Vec::new();
            expected_digests.extend((0..B_NUM_CHAIN).map(|k| before_base + B_CHAIN_BASE + k));
            expected_digests.push(before_base + B_STATE_COMMIT);
            expected_digests.extend((0..B_NUM_CHAIN).map(|k| after_base + B_CHAIN_BASE + k));
            expected_digests.push(after_base + B_STATE_COMMIT);
            // Caveat region: carriers/commit are BLOCK-RELATIVE here (the cav::* constants are
            // absolute within the standalone caveat probe at base cav::BASE).
            let cav_chain_rel = cav::CHAIN_BASE - cav::BASE; // 29
            expected_digests.extend((0..cav::NUM_CHAIN).map(|k| caveat_base + cav_chain_rel + k));
            expected_digests.push(caveat_base + C_COMMIT);
            assert_eq!(
                digests, expected_digests,
                "{key}: before chain→state_commit, after chain→state_commit, \
                 caveat chain→CAVEAT_COMMIT"
            );

            // The four rotated commit pins always sit at the v1 prefix count (42..=45),
            // bound to: first-row before state_commit, last-row after state_commit,
            // last-row after committed_height, last-row caveat commit. (The pins do NOT
            // ride `public_input_count - 4`: note-spend appends a FIFTH nullifier pin past
            // them, so the commit-pin base is the FIXED v1 prefix `V1_PI_COUNT = 34`.)
            //
            // heapWrite is the LONE exception: its base descriptor (`heapWriteVmDescriptor`)
            // declares ZERO v1 PIs (its faithfulness rides the three recompute chip lookups,
            // not a published-param prefix), so `rotateV3` lands the four commit pins at the
            // FRONT (indices 0..=3). It carries no fifth pin, so `public_input_count == 4`.
            let is_heap_write = key == "heapWriteVmDescriptor2R24";
            const V1_PI_COUNT: usize = 42;
            let pi_base = if is_heap_write {
                d.public_input_count - 4
            } else {
                V1_PI_COUNT
            };
            let mut pins: Vec<(usize, usize)> = Vec::new(); // (col, pi_index)
            for c in &d.constraints {
                if let VmConstraint2::Base(VmConstraint::PiBinding { col, pi_index, .. }) = c {
                    // only the rotated appendix pins (>= the v1 prefix); the four commit pins.
                    if (pi_base..pi_base + 4).contains(pi_index) {
                        pins.push((*col, *pi_index));
                    }
                }
            }
            pins.sort_by_key(|(_, pi)| *pi);
            assert_eq!(
                pins,
                vec![
                    (before_base + B_STATE_COMMIT, pi_base),
                    (after_base + B_STATE_COMMIT, pi_base + 1),
                    (after_base + B_COMMITTED_HEIGHT, pi_base + 2),
                    (caveat_base + C_COMMIT, pi_base + 3),
                ],
                "{key}: four appended PI pins (rotated OLD/NEW commit · height · caveat commit)"
            );

            // THE C4 LAST-FLIP-GATE: the rotated NOTE-SPEND carries a FIFTH appended PI pin
            // (`EffectVmEmitRotationV3.noteSpendV3`) welding the spend row's folded nullifier
            // (`param::NULLIFIER = param0`, col `PARAM_BASE + 0`) to rotated PI slot 38 on the
            // FIRST row — the rotated analog of the v1 hand-AIR D5 cross-binding (offset 198),
            // so a note-spending turn can rotate (`verify_full_turn` step 8 reads PI[46]). Every
            // OTHER cohort member has EXACTLY the four commit pins and 38 PIs.
            use crate::effect_vm::columns::{PARAM_BASE, param};
            let nullifier_pins: Vec<(usize, usize)> = d
                .constraints
                .iter()
                .filter_map(|c| match c {
                    VmConstraint2::Base(VmConstraint::PiBinding { col, pi_index, .. })
                        if *pi_index >= pi_base + 4 =>
                    {
                        Some((*col, *pi_index))
                    }
                    _ => None,
                })
                .collect();
            // THE UNIFORM DSL rc-EMIT (`withDfaRcPins`): every rotated COHORT member (+ the
            // fee-in-proof transfer) publishes the 4-felt `Witnessed{Dfa}` route-commitment
            // carrier (caveat-region offsets 39..=42) as its LAST 4 member PIs. Strip + assert
            // the quad here so the per-effect branches below keep their pre-rc expectations;
            // fail-closed on membership (a cohort member MISSING the rc pins, or a tail member
            // GROWING them, both fail).
            let rc_col = caveat_base + crate::effect_vm::trace_rotated::C_DFA_RC_OFF;
            let (rc_pins, nullifier_pins): (Vec<(usize, usize)>, Vec<(usize, usize)>) =
                nullifier_pins
                    .into_iter()
                    .partition(|(col, _)| (rc_col..rc_col + 4).contains(col));
            let has_rc = !rc_pins.is_empty();
            // NOT rc-wrapped: heapWrite (v3RegistryHeap tail, no v1 prefix), the dedicated
            // supply-mint (tail `withSelectorGate sel::MINT mintV3` over the BARE body), and the three
            // STAGED capacity-satisfaction welds (escrow/discharge/vault — no live routing). Everything
            // else here is the rc-wrapped cohort (+ transferFee).
            let rc_exempt = is_heap_write
                || key == "supplyMintVmDescriptor2R24"
                || key == "settleEscrowSatVmDescriptor2R24"
                || key == "dischargeSatVmDescriptor2R24"
                || key == "vaultSatVmDescriptor2R24";
            assert_eq!(
                has_rc, !rc_exempt,
                "{key}: dsl rc pins present iff the member is the rc-wrapped cohort"
            );
            if has_rc {
                let rc_expected: Vec<(usize, usize)> = (0..4)
                    .map(|k| (rc_col + k, d.public_input_count - 4 + k))
                    .collect();
                assert_eq!(
                    rc_pins, rc_expected,
                    "{key}: the 4 rc pins publish the rc carrier (region offsets 39..=42) as the \
                     LAST 4 member PIs"
                );
            }
            // The member's PRE-rc PI count — what every per-effect branch below pins.
            let base_pi_count = d.public_input_count - if has_rc { 4 } else { 0 };
            // THE RECORD-FORCING PIN (the deployment-soundness close, `EffectVmEmitRotationV3
            // .rotateV3WithRecordPin`): cellSeal/cellUnseal/cellDestroy AND receiptArchive force the
            // AFTER block's lifecycle limb (col `after_base + B_LIFECYCLE`) — the deployed apply moves
            // the cell lifecycle (Sealed/Live/Destroyed/Archived); setPermissions/setVK AND the
            // refusal audit write force the AFTER record-digest / authority-digest limb (col
            // `after_base + B_AUTHORITY_DIGEST`) — the refusal audit lands in `fields_root`, which the
            // r23 authority digest folds. Each carries a FIFTH last-row PI pin to slot 38, so the
            // committed write is FORCED.
            use crate::effect_vm::trace_rotated::{B_AUTHORITY_DIGEST, B_LIFECYCLE};
            let record_digest_pin_member = matches!(
                key,
                "setPermsVmDescriptor2R24"
                    | "setVKVmDescriptor2R24"
                    | "refusalVmDescriptor2R24"
                    // makeSovereign keeps the record pin on `B_RECORD_DIGEST` as belt-and-suspenders
                    // for the opaque authority residue (Lean `makeSovereignV3`, the mode gate is the
                    // primary soundness; PI 38 welds the AFTER authority-digest limb).
                    | "makeSovereignVmDescriptor2R24"
            );
            let lifecycle_record_pin_member = record_digest_pin_member
                || matches!(
                    key,
                    "cellSealVmDescriptor2R24"
                        | "cellUnsealVmDescriptor2R24"
                        | "cellDestroyVmDescriptor2R24"
                        | "receiptArchiveVmDescriptor2R24"
                );
            // The createCell / factory / spawn ACCOUNTS-SET grow-gate family: the fifth pin welds
            // the new-cell key (param0) to PI[46], and the two cells_root map-ops force the
            // accounts set-insert on limb 0 (`EffectVmEmitRotationV3.{createCellV3,factoryV3,
            // spawnV3}`).
            let new_cell_key_pin_member = matches!(
                key,
                "createCellVmDescriptor2R24" | "factoryVmDescriptor2R24" | "spawnVmDescriptor2R24"
            );
            if key == "noteSpendVmDescriptor2R24" {
                assert_eq!(
                    base_pi_count, 47,
                    "noteSpend: rotated 46-PI + the appended nullifier slot"
                );
                assert_eq!(
                    nullifier_pins,
                    vec![(PARAM_BASE + param::NULLIFIER, pi_base + 4)],
                    "noteSpend: the fifth pin welds the folded nullifier (param0) to PI[46]"
                );
            } else if key == "noteCreateVmDescriptor2R24" {
                // The COMMITMENTS-SET grow-gate (the `commitments_root` flag-day): the fifth pin
                // welds the published note commitment (param0) to PI[46], and the
                // `commitmentsInsertOp` map-op forces the commitment set-insert on limb 27
                // (`EffectVmEmitRotationV3.noteCreateV3`).
                assert_eq!(
                    base_pi_count, 47,
                    "noteCreate: rotated 46-PI + the appended commitment slot"
                );
                assert_eq!(
                    nullifier_pins,
                    vec![(PARAM_BASE + param::NULLIFIER, pi_base + 4)],
                    "noteCreate: the fifth pin welds the published commitment (param0) to PI[46]"
                );
            } else if key == "factoryVmDescriptor2R24" {
                // STEP-3 factory carriers (`factoryV3Carriers = withAfterOctetPins (withAfterOctetPins
                // factoryV3 B_CHILD_VK_OCTET) B_CONTRACT_HASH_OCTET`): the new-cell-key grow-gate pin
                // (param1 CHILD_VK_DERIVED → PI[46]) PLUS the 16 committed carrier-octet pins — the
                // AFTER-block child_vk8 octet (limbs 88..=95 → PI[47..54]) then the contract_hash8
                // octet (limbs 96..=103 → PI[55..62]), last-row, the v12 big-bang exposure the
                // factory/hatchery fold tooths bind.
                use crate::effect_vm::trace_rotated::{B_CHILD_VK_OCTET, B_CONTRACT_HASH_OCTET};
                assert_eq!(
                    base_pi_count, 63,
                    "factory: rotated 46-PI + the new-cell-key slot + the 16 carrier-octet pins"
                );
                let mut expected = vec![(PARAM_BASE + param::CHILD_VK_DERIVED, pi_base + 4)];
                for i in 0..8 {
                    expected.push((after_base + B_CHILD_VK_OCTET + i, pi_base + 5 + i));
                }
                for i in 0..8 {
                    expected.push((after_base + B_CONTRACT_HASH_OCTET + i, pi_base + 13 + i));
                }
                assert_eq!(
                    nullifier_pins, expected,
                    "factory: the grow-gate key pin (PI[46]) + the child_vk8 (PI[47..54]) + \
                     contract_hash8 (PI[55..62]) committed-octet pins"
                );
            } else if new_cell_key_pin_member {
                assert_eq!(
                    base_pi_count, 47,
                    "{key}: rotated 46-PI + the appended new-cell-key slot"
                );
                // createCell/spawn key on param0 (the new-cell id).
                let key_col = PARAM_BASE;
                assert_eq!(
                    nullifier_pins,
                    vec![(key_col, pi_base + 4)],
                    "{key}: the fifth pin welds the new-cell key to PI[46] (the accounts-set \
                     grow-gate)"
                );
            } else if record_digest_pin_member {
                // H1: the record-digest movers (setPerms/setVK/makeSovereign/refusal) pin ALL 8 faithful
                // authority limbs (`withRecordPin8Headroom2`): limb-0 (`B_AUTHORITY_DIGEST`) → PI[46] +
                // the 7 headroom limbs (AFTER offsets 12..18) → PI[47..53], so a 31-bit-colliding
                // wide-open authority forged into ANY limb is UNSAT (the GENTIAN close for movers).
                assert_eq!(
                    base_pi_count, 54,
                    "{key}: rotated 46-PI + the 8 authority record-pins (47..53)"
                );
                let mut expected = vec![(after_base + B_AUTHORITY_DIGEST, pi_base + 4)];
                for i in 0..7 {
                    expected.push((after_base + 12 + i, pi_base + 5 + i));
                }
                assert_eq!(
                    nullifier_pins, expected,
                    "{key}: the 8 record-pins weld the AFTER authority limbs (24, 12..18) to PI[46..53]"
                );
            } else if lifecycle_record_pin_member {
                assert_eq!(
                    base_pi_count, 47,
                    "{key}: rotated 46-PI + the appended record-forcing slot"
                );
                assert_eq!(
                    nullifier_pins,
                    vec![(after_base + B_LIFECYCLE, pi_base + 4)],
                    "{key}: the fifth pin welds the AFTER block's correctly-written lifecycle \
                     limb to PI[46] (the deployment-soundness gate)"
                );
            } else if key == "transferFeeVmDescriptor2R24" {
                // THE FEE-IN-PROOF transfer: the fifth pin welds the after-block RESERVED limb (col
                // `STATE_AFTER_BASE + state::RESERVED`, the fee carrier) to PI[46], the fee debited
                // INSIDE the proven transition (the bal-lo gate forces `after = before − amount − fee`).
                use crate::effect_vm::columns::{STATE_AFTER_BASE, state};
                assert_eq!(
                    base_pi_count, 47,
                    "transferFee: rotated 46-PI + the appended fee slot"
                );
                assert_eq!(
                    nullifier_pins,
                    vec![(STATE_AFTER_BASE + state::RESERVED, pi_base + 4)],
                    "transferFee: the fifth pin welds the after-block RESERVED fee limb (col 89) to PI[46]"
                );
            } else if key == "setFieldDynVmDescriptor2R24" {
                // THE DYNAMIC setField fields-root weld (WAVE 3): the fifth pin welds the AFTER
                // block's committed `fields_root` sub-limb to PI[46], so a forged post-`fields_root`
                // is UNSAT in-circuit (Lean `setFieldDynForcedV3`). The column is the Lean's
                // `afterFieldsRootCol setFieldDynV1Face.traceWidth` = face + B_SPAN + B_FIELDS_ROOT.
                //
                // This pin ROTTED once already (439 → 451) when the REVOKED-ROOT flag day grew
                // `B_SPAN` 227 → 239 (+12), because it is a hand-pinned literal. It is re-pinned from
                // the emitted registry TSV (this file's stated practice for it), NOT derived, and the
                // reason is worth naming rather than hiding: the derived form would be
                // `V1_WIDTH + B_SPAN + B_FIELDS_ROOT`, but that yields 463 — Rust's `EFFECT_VM_WIDTH`
                // (188) and the Lean `setFieldDynV1Face` base (451 − 239 − 36 = 176) DISAGREE by 12.
                // Until that Lean/Rust face-width divergence is reconciled, a "derived" form here
                // would be a fabricated identity, so the literal stands with the discrepancy recorded.
                const SETFIELD_DYN_AFTER_FIELDS_ROOT_COL: usize = 451;
                assert_eq!(
                    base_pi_count, 47,
                    "setFieldDyn: rotated 46-PI + the appended fields-root weld slot"
                );
                assert_eq!(
                    nullifier_pins,
                    vec![(SETFIELD_DYN_AFTER_FIELDS_ROOT_COL, pi_base + 4)],
                    "setFieldDyn: the fifth pin welds the AFTER fields_root weld col (451) to PI[46]"
                );
            } else if key == "mintVmDescriptor2R24" {
                // THE SUPPLY-MINT hash weld: the fifth pin welds the published mint-hash param
                // (`PARAM_BASE + param::MINT_HASH`, col 68) to PI[46] on the first row, so a live
                // `Effect::Mint` (e.g. a Stripe-attested credit) rides the ALREADY-EMITTED PI-46
                // binding — the minted supply anchor is a committed public input, not free. base_pi 47.
                assert_eq!(
                    base_pi_count, 47,
                    "mint: rotated 46-PI + the appended mint-hash slot"
                );
                assert_eq!(
                    nullifier_pins,
                    vec![(PARAM_BASE + param::MINT_HASH, pi_base + 4)],
                    "mint: the fifth pin welds the published mint-hash (param0, col 68) to PI[46]"
                );
            } else if key == "settleEscrowSatVmDescriptor2R24"
                || key == "dischargeSatVmDescriptor2R24"
                || key == "vaultSatVmDescriptor2R24"
            {
                // THE THREE WELDED CAPACITY-SATISFACTION descriptors (VK-EPOCH §6 BLOCKER 1 + G5
                // 18/19, STAGED): the fifth pin welds the capacity SELECTOR column (param2, col 70) to
                // PI[46] on the first row, so a verifier that knows the cell declares the capacity (the
                // deployed COVERAGE carrier `CapacityCarrier`) can FORCE the selector on; the
                // selector-gated satisfaction gates over the rotated FIELD columns then force the
                // in-AIR arm — settleEscrow's Deposited→Consumed (`SETTLE_ESCROW`), discharge's
                // cursor/total/due + the G5 free-param binds (`DISCHARGE_OBLIGATION`), vault's
                // no-dilution `Ta·m ≤ Sa·d` (`VAULT_DEPOSIT`). All three share the SAME selector pin
                // (col 70 → PI[46]) and 47 PIs; they differ only in the satisfaction-gate field columns
                // (accounted in the graduated-width check above). NO live routing — staged beside the
                // cohort; the descriptors a flippable capacity weld commits a VK for. Refinements in
                // `metatheory/Dregg2/Deos/{SettleEscrowSat,DischargeSat,VaultSat}Descriptor.lean`.
                use crate::effect_vm::columns::PARAM_BASE;
                assert_eq!(
                    base_pi_count, 47,
                    "{key}: rotated 46-PI + the appended capacity-selector slot"
                );
                assert_eq!(
                    nullifier_pins,
                    vec![(PARAM_BASE + 2, pi_base + 4)],
                    "{key}: the fifth pin welds the capacity selector (param2, col 70) to PI[46]"
                );
            } else if is_heap_write {
                // heapWrite: the base carries no v1 PIs, so the rotated descriptor publishes
                // EXACTLY the four commit pins (indices 0..=3) — no fifth pin. The new heap_root is
                // forced by the genuine sorted-Merkle SPLICE `.write` map_op (PHASE-E) + the address
                // chip lookup that gives it the sorted KEY — not a published param.
                assert_eq!(
                    d.public_input_count, 4,
                    "heapWrite: the four rotated commit pins, no v1 PI prefix"
                );
                assert!(
                    nullifier_pins.is_empty(),
                    "heapWrite: carries no fifth pin (the splice map_op rides the map_ops table)"
                );
            } else if key == "customVmDescriptor2R24" {
                // G2 custom-leg PI exposure (`EffectVmEmitRotationV3.customPiExposure`) — the
                // PROOF-BIND FLAG-DAY ROTATION (blocker #2, 4 → 8 commitment felts): customV3
                // publishes the deployed custom fold-binding anchors PAST the rotated 46-PI vector —
                // `custom_proof_commitment` limbs 0..4 (PARAM_BASE+4..7) → PI[46..49], limbs 4..8
                // (the commit-teeth cols `CUSTOM_COMMIT_TEETH_BASE..+4`) → PI[50..53], and
                // `custom_program_vk_hash` (PARAM_BASE+0..3) → PI[54..57], all on the FIRST row
                // (the binding is fold-enforced, like memOp/umemOp, NOT a row poly). So custom
                // carries 58 PIs (46 + 12 anchors).
                use crate::effect_vm::trace_rotated::CUSTOM_COMMIT_TEETH_BASE;
                assert_eq!(
                    base_pi_count, 58,
                    "custom: rotated 46-PI + the 12 custom fold-binding anchors (46..57)"
                );
                let mut expected: Vec<(usize, usize)> = Vec::new();
                for i in 0..4 {
                    expected.push((PARAM_BASE + 4 + i, pi_base + 4 + i)); // commit limbs 0..4 → 46..49
                }
                for i in 0..4 {
                    expected.push((CUSTOM_COMMIT_TEETH_BASE + i, pi_base + 8 + i)); // commit limbs 4..8 → 50..53
                }
                for i in 0..4 {
                    expected.push((PARAM_BASE + i, pi_base + 12 + i)); // program_vk_hash → 54..57
                }
                assert_eq!(
                    nullifier_pins, expected,
                    "custom: 12 fold-binding pins weld proof_commitment limbs 0..4 \
                     (PARAM_BASE+4..7)→PI[46..49] + limbs 4..8 (commit teeth)→PI[50..53] \
                     + program_vk_hash (PARAM_BASE+0..3)→PI[54..57]"
                );
                // The versioned boundary classifies THIS committed member as live v2 (and the
                // retired 4-felt layout as an explicit RetiredV1 refusal — see the boundary test).
                assert_eq!(
                    custom_commit_version(&d),
                    Ok(CUSTOM_COMMIT_VERSION),
                    "the committed custom member must classify as commit-teeth v2"
                );
            } else {
                assert_eq!(
                    base_pi_count, 46,
                    "{key}: non-record-pin cohort carries the rotated 46-PI"
                );
                assert!(
                    nullifier_pins.is_empty(),
                    "{key}: only note-spend / the 7 record-pin effects carry a fifth pin"
                );
            }
        }
        assert_eq!(
            n, 60,
            "expected the 36-member rotated cohort (28 v2-graduated + 8 widened) + the 6 fan-out \
             cap-open members (delegate/introduce/grantCap/revoke/refreshDelegation/revokeCapability \
             — each *CapOpenVmDescriptor2R24) + the 2 LIVE effect-general legs \
             (transfer/attenuate *CapOpenEffVmDescriptor2R24) + the TURN-IDENTITY weld \
             (transferCapOpenTBVmDescriptor2R24, CapOpenTurnPins — the cap-open + 2 turn-identity \
             columns + 3 turn-identity PI pins welding src/actor/dst to the published turn) + the \
             FEE-IN-PROOF transfer (transferFeeVmDescriptor2R24 — the fee debited in-proof, 47 PIs) \
             + THE WRITE-BEARING TAIL (`v3RegistryHeap` 45..52): heapWriteVmDescriptor2R24 (the \
             Class-A heap-root recompute, `Rfix 56`) + the SIX write-forcing cap-open wrappers \
             (delegate/introduce/delegateAtten/revokeDelegation/revokeCapability/refreshDelegation \
             *WriteCapOpenVmDescriptor2R24 — the apex's `Rfix 1/10/11/14/55` re-pointed plus the \
             revokeCapability cap-tree REMOVE route-forge close, guarantee A: the cap-tree / \
             deleg-tree WRITE forced into the commitment) + the SPAWN cap-handoff close (the \
             authority-only spawnCapOpenVmDescriptor2R24 + the WRITE-forcing \
             spawnWriteCapOpenVmDescriptor2R24, `Rfix 19` re-pointed — the parent→child CAPABILITY \
             HANDOFF cap-tree INSERT forced ALONGSIDE the accounts grow-gate; both carry spawn's \
             extra birth new-cell-key PI so 47 PIs) + the EXERCISE cap-open close (the \
             exerciseCapOpenVmDescriptor2R24 — `Rfix 16` re-pointed; the FROZEN exercise base + the \
             EFF_EXERCISE depth-16 cap-membership crown forcing the exercise hold-gate \
             `exerciseGuard`'s `confersEdgeTo target` membership in-circuit — the LAST named cap-open \
             residual CLOSED) + the DEDICATED SUPPLY-MINT (supplyMintVmDescriptor2R24, SUPPLY-MODEL.md \
             Stage 2b — the turn-layer `Effect::Mint` on its OWN selector `sel::MINT = 14`; the SAME \
             proven credit/tick/freeze body as mintVmDescriptor2R24 save the appended selectorGate \
             operand, so it proves + self-verifies under a dedicated selector, not by riding \
             BridgeMint's). \
             The Signature-pinned capOpenAttenuateV3/transferCapOpenV3 were DELETED (Stage D). \
             + the THREE WELDED CAPACITY-SATISFACTION descriptors (VK-EPOCH §6 BLOCKER 1 + G5 18/19 \
             — the staged welded EffectVmDescriptor2s carrying the selector-gated satisfaction gates \
             over the rotated FIELD columns + the shared selector PI pin (col 70 → PI 46), 47 PIs each; \
             NO live routing, NO VK committed): settleEscrowSatVmDescriptor2R24 (tag 17, \
             Deposited→Consumed, no extra columns) + dischargeSatVmDescriptor2R24 (tag 18, the \
             cursor/total/due + G5 free-param binds) + vaultSatVmDescriptor2R24 (tag 19, the \
             no-dilution Ta·m ≤ Sa·d gates) — the descriptors a flippable capacity weld commits VKs for."
        );
    }

    /// **THE WIDE REGISTRY drift + coverage pin (STAGED-ADDITIVE slice 2).** The 57-member faithful
    /// 8-felt wide registry TSV is fingerprint-stable (the Lean `EmitWideRegistryProbe.lean` is the
    /// byte source), parses member-for-member, and is name-stable against the live 1-felt registry
    /// (the flip is a name-stable repoint). The transfer member (row 0) is the v12 TEETH-EXPOSING
    /// advance (+2 claim PIs / +2 teeth columns) of the single-line `WIDE_TRANSFER_STAGED_TSV`.
    /// ADDITIVE: pins the wide path WITHOUT touching the live `V3_STAGED_REGISTRY_*`.
    #[test]
    fn wide_registry_parses_and_is_name_stable() {
        use crate::descriptor_ir2::parse_vm_descriptor2;

        // Every wide member parses; the wide geometry is `host + 608` carrier columns + 16 PIs. The
        // keys are NAME-STABLE against the live 1-felt registry, member-for-member (the flip repoint
        // does not rename).
        let live_keys: Vec<&str> = V3_STAGED_REGISTRY_TSV
            .lines()
            .filter(|l| !l.is_empty())
            .map(|l| l.split('\t').next().expect("live key"))
            // The THREE STAGED capacity-satisfaction-weld members (VK-EPOCH §6 BLOCKER 1 + G5 18/19 —
            // settleEscrow/discharge/vault), appended LAST to the rotated registry; their WIDE+umem
            // mirrors are a separate named step (the wide cohort is the deployable host set). Excluded
            // from the member-for-member wide-cover parity until those welds land — they carry no live
            // routing, so the wide registry has 57 members to the live registry's 60.
            .filter(|k| {
                *k != "settleEscrowSatVmDescriptor2R24"
                    && *k != "dischargeSatVmDescriptor2R24"
                    && *k != "vaultSatVmDescriptor2R24"
            })
            .collect();
        let mut n = 0usize;
        for (i, line) in WIDE_REGISTRY_STAGED_TSV.lines().enumerate() {
            if line.is_empty() {
                continue;
            }
            n += 1;
            let mut it = line.splitn(3, '\t');
            let key = it.next().expect("wide key");
            let _name = it.next().expect("wide name");
            let json = it.next().expect("wide json");
            assert_eq!(
                key, live_keys[i],
                "wide registry key {i} name-stable with the live registry"
            );
            let d = parse_vm_descriptor2(json).unwrap_or_else(|e| panic!("{key} wide parses: {e}"));
            // the wide member is `host + WIDE_CARRIER_APPENDIX (960)` (the v2 flag-day 60-carrier
            // appendix) and `host.piCount + 16`. The committed wide widths — READ OFF THE EMITTED
            // rotation-wide-registry-staged.tsv, never hand-derived — are:
            //   * 2607 — the rotated-cohort base wide (GRAD_ROT_WIDTH 1647 + 960; supplyMint);
            //   * 2623 — the AVAILABILITY-HARDENED transferFee (fee-avail host 1663 + 960);
            //   * 2627 — setFieldDyn (host 1619 = GRAD_ROT_WIDTH − 28) + the gentian 48-column
            //     floor-refuse weld (2579 + 48);
            //   * 2631 — custom (host 1619 + the 4 COMMIT-TEETH columns of the 8-felt proof-bind
            //     rotation = 1623) + the wide appendix + the gentian 48-column refuse weld
            //     (1623 + 960 + 48);
            //   * 2655 — the bare-cohort members: 2607 + the gentian 48-column floor-refuse weld;
            //   * 2660 — the AVAILABILITY-HARDENED burn (burn-avail host 1700 + 960);
            //   * 2664 — the AVAILABILITY-HARDENED transfer (transfer-avail host 1704 + 960);
            //   * 2687 — the KEY_COMMIT-gated sovereign (2607 + the 32-column chip-digest appendix
            //     + 48, `CarrierComposed.makeSovereignV3DeployedWide`);
            //   * 2936 — the cap-open family + the §J′ insert hosts (host 1976 + 960);
            //   * 2946 — the avail-hardened transferCapOpenEff leg (host 1986 + 960);
            //   * 2948 — the turn-identity-pinned transferCapOpenTB (host 1988 + 960);
            //   * 2984 — cap-open bare-cohort hosts + the gentian refuse (2936 + 48);
            //   * 3065 — heapWrite's after-spine membership host (HEAP_WRITE_HOST_WIDTH 2105 + 960);
            //   * 3079 — the refusal fields-write weld + cap-WRITE after-spine members
            //     (REFUSAL_WRITE_HOST_WIDTH 2119 + 960);
            //   * 3127 — the refusal fields-write / cap-WRITE bare-cohort members (3079 + 48).
            // The retired 2657 (pre-avail membership-teeth transfer) and 2938 (pre-avail
            // transferCapOpenTB) widths are GONE: the availability-hardening pads (transfer/burn/fee)
            // grew those hosts, and the AAFI accumulator-insert flip moved the cap-open transfer legs.
            // Any member off this exact set (a carrier block that grew/shrank, or a refuse weld
            // mis-sized) fails this drift tooth. The RETIRED v1 (912-appendix) widths are refused
            // structurally by `wide_carrier_geometry_version` (the versioned boundary).
            assert!(
                matches!(
                    d.trace_width,
                    2607 | 2623
                        | 2627
                        | 2631
                        | 2655
                        | 2660
                        | 2664
                        | 2687
                        | 2936
                        | 2946
                        | 2948
                        | 2984
                        | 3065
                        | 3079
                        | 3127
                ),
                "{key}: wide width {} is a known wide geometry (2607 / 2623 / 2627 / 2631 / 2655 / 2660 / 2664 / 2687 / 2936 / 2946 / 2948 / 2984 / 3065 / 3079 / 3127)",
                d.trace_width
            );
            // Every wide member carries the 16 wide-commit PIs (the 8-felt ~124-bit before/after
            // anchors) appended PAST its host's PI vector, so `piCount = host.piCount + 16`. The
            // rotated cohort / `-eff` / cap-open / write members host the full 46-PI rotated vector →
            // 62; the turn-identity-pinned `transferCapOpenTB` hosts 49 → 65; the minimal-PI Class-A
            // `heapWrite` hosts just 4 → 20. The floor (≥ 20) is exactly the 16 anchors + heapWrite's
            // 4 host PIs — every member fits the 16 wide PIs, NO narrowing.
            assert!(
                d.public_input_count >= 20,
                "{key}: wide PI count {} carries the 16 wide-commit PIs",
                d.public_input_count
            );
            if i == 0 {
                // v12 big-bang: row 0 is the TEETH-EXPOSING advance of the plain wide transfer
                // (`CarrierComposed.transferV3MembershipWide` — the 2 `(sender_leaf,
                // authorized_root)` claim PIs at 50..51 ahead of the anchors, teeth columns past
                // the carriers). The single-line `WIDE_TRANSFER_STAGED_TSV` stays the PLAIN wide
                // transfer, so byte-identity is retired for the exact +2/+2 advance relation.
                let plain = parse_vm_descriptor2(
                    WIDE_TRANSFER_STAGED_TSV
                        .lines()
                        .next()
                        .unwrap()
                        .splitn(3, '\t')
                        .nth(2)
                        .unwrap(),
                )
                .expect("plain wide transfer parses");
                assert_eq!(
                    d.public_input_count,
                    plain.public_input_count + 2,
                    "wide registry row 0 (transfer) = the plain wide transfer + 2 membership claim PIs"
                );
                // The plain single-line `WIDE_TRANSFER_STAGED_TSV` is the BARE transfer: neither
                // availability-hardened, nor teeth-advanced, nor refuse-welded. The registry row 0 is
                // the AVAIL-HARDENED membership-teeth transfer AND (being a bare cohort route) carries
                // the gentian floor-refuse weld. Its refuse blocks therefore anchor at
                // `plain + TRANSFER_AVAIL_PAD + 2 teeth` (verified against the emitted descriptor: the
                // three floor gates land at 2631 / 2647 / 2663, stride 16), and the member extends
                // exactly to cover the last floor column — `floor_col(NB−1) + 1`, i.e. 45 columns past
                // its own anchor, NOT a padded `3·REFUSE_STRIDE = 48`. Both the extent and the pad are
                // derived from the weld's own constants, so a stride/pad change moves this tooth with
                // them. The PI relation stays `plain + 2` (the refuse weld adds constraints + columns
                // but NO public inputs).
                use crate::effect_vm::bare_floor_refuse_weld as wrefuse;
                let refuse_extent = wrefuse::floor_col(wrefuse::CAPACITY_TAGS.len() - 1) + 1
                    - crate::effect_vm::trace_rotated::GRAD_ROT_WIDTH;
                let avail_pad = crate::effect_vm::trace_rotated::TRANSFER_AVAIL_PAD;
                assert_eq!(
                    d.trace_width,
                    plain.trace_width + avail_pad + 2 + refuse_extent,
                    "wide registry row 0 (transfer) = the plain wide transfer + the availability pad \
                     + 2 teeth columns + the gentian floor-refuse extent"
                );
            }
        }
        assert_eq!(
            n,
            live_keys.len(),
            "the wide registry is a member-for-member cover of the live V3 registry (57 members)"
        );
        assert_eq!(n, 57, "the wide registry covers all 57 live V3 members");
    }

    /// **THE LEAN-EMITTED WIDE+UMEM WELDED REGISTRY: drift pin + per-member weld parity (the
    /// MISSING VERIFIER LEG, grounded).** The welded registry TSV is fingerprint-stable (the Lean
    /// `EmitWideUMemWeldRegistryProbe.lean` is the byte source), parses member-for-member, is
    /// name-stable on the KEYS with the bare wide registry, and — the load-bearing tooth — each Lean
    /// welded member is BYTE-IDENTICAL to applying the Rust additive [`weld_umem_into_wide_descriptor`]
    /// to the corresponding bare wide member at the welded member's own domain. That parity is what
    /// makes a welded proof (built Rust-side via `weld_umem_into_wide_descriptor`) verify UNIQUELY
    /// against the Lean-grounded registry member on the wire. The NO-NARROWING invariant
    /// (`piCount` unchanged, `traceWidth = host + 7`) is checked per member.
    #[test]
    fn wide_umem_weld_registry_parity_and_no_narrowing() {
        use crate::descriptor_ir2::{VmConstraint2, parse_vm_descriptor2};

        // The bare wide members, keyed. The welded registry is now a member-for-member 57/57 cover of
        // the bare wide registry: v3RegistryCapOpenWide (the first 45 bare members) + the 9 §10
        // WRITE-bearing cap-open tail wrappers + the 3 live-only wide members (transferCapOpenTB /
        // heapWrite / supplyMint) — every welded key is a bare WIDE_REGISTRY_STAGED_TSV key.
        let bare: std::collections::HashMap<&str, &str> = WIDE_REGISTRY_STAGED_TSV
            .lines()
            .filter(|l| !l.is_empty())
            .map(|l| {
                let mut it = l.splitn(3, '\t');
                let k = it.next().expect("bare key");
                let _n = it.next();
                let j = it.next().expect("bare json");
                (k, j)
            })
            .collect();

        let mut n = 0usize;
        for line in WIDE_UMEM_WELD_REGISTRY_TSV.lines() {
            if line.is_empty() {
                continue;
            }
            n += 1;
            let mut it = line.splitn(3, '\t');
            let key = it.next().expect("welded key");
            let name = it.next().expect("welded name");
            let json = it.next().expect("welded json");
            assert!(
                name.ends_with(WIDE_UMEM_WELD_SUFFIX),
                "{key}: welded member name carries the WIDE_UMEM_WELD_SUFFIX"
            );
            let welded = parse_vm_descriptor2(json)
                .unwrap_or_else(|e| panic!("{key} welded member parses: {e}"));
            // Extract the welded leg's domain (the single appended umemOp).
            let domain = welded
                .constraints
                .iter()
                .find_map(|c| match c {
                    VmConstraint2::UMemOp(spec) => Some(spec.domain),
                    _ => None,
                })
                .unwrap_or_else(|| panic!("{key}: welded member declares a umemOp"));

            let bare_json = bare
                .get(key)
                .unwrap_or_else(|| panic!("{key}: welded key is a bare wide registry key"));
            let bare_desc = parse_vm_descriptor2(bare_json)
                .unwrap_or_else(|e| panic!("{key} bare member parses: {e}"));

            // THE PARITY TOOTH: the Lean-emitted welded member == the Rust additive weld of the bare
            // member at the same domain. The welded VK is Lean-grounded AND the Rust producer's weld
            // agrees with it (the ONE-circuit/VK invariant).
            let rust_welded = weld_umem_into_wide_descriptor(&bare_desc, domain);
            assert_eq!(
                welded, rust_welded,
                "{key}: Lean-emitted welded member must byte-match the Rust weld_umem_into_wide_descriptor"
            );

            // NO-NARROWING: `piCount` unchanged, `traceWidth = host + 7`.
            assert_eq!(
                welded.public_input_count, bare_desc.public_input_count,
                "{key}: the weld must NOT change public_input_count (the 8-felt anchors stay put)"
            );
            assert_eq!(
                welded.trace_width,
                bare_desc.trace_width + 7,
                "{key}: the weld appends exactly the 7 umem columns"
            );
        }
        assert_eq!(
            n, 57,
            "the welded registry is a member-for-member 57/57 cover of the bare wide registry: all 45 \
             v3RegistryCapOpenWide emit-source members + the 9 §10 WRITE-bearing cap-open tail wrappers \
             (the write twins the wire routes cap WRITE turns to, minus grantCapWriteCapOpen which has \
             no bare wide twin) + the 3 live-only wide members (transferCapOpenTB / heapWrite / \
             supplyMint)"
        );

        // The byte fingerprint pin (the committed-descriptor discipline; Lean is the byte source).
        // Mirrors how `WIDE_REGISTRY_STAGED_FP` pins the bare wide registry.
        assert_eq!(
            sha256_hex(WIDE_UMEM_WELD_REGISTRY_TSV.as_bytes()),
            WIDE_UMEM_WELD_REGISTRY_FP,
            "the welded-wide registry TSV drifted from its committed fingerprint — regenerate via \
             `lake env lean --run EmitWideUMemWeldRegistryProbe.lean` and update WIDE_UMEM_WELD_REGISTRY_FP"
        );
    }

    /// The widened-entry codec teeth: round-trip + FAIL-CLOSED decode. A forged
    /// domain tag REFUSES; a registers-domain key outside the R=24 file REFUSES;
    /// a heap-domain key carries an arbitrary felt (the operand the u8 slot index
    /// could not express).
    #[test]
    fn rot_caveat_entry_codec_fail_closed() {
        use crate::effect_vm::RotCaveatEntry;
        use crate::effect_vm::columns::rotation::caveat as cav;
        use crate::field::BabyBear;
        // Heap-domain round-trip with a large felt key.
        let heap = RotCaveatEntry {
            type_tag: crate::effect_vm::pi::SLOT_CAVEAT_TAG_FIELD_GTE,
            domain_tag: cav::DOMAIN_HEAP,
            key: BabyBear::new(123_456_789),
            params: [
                BabyBear::new(50),
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
            ],
        };
        let mut buf = [BabyBear::ZERO; 7];
        heap.write_to(&mut buf);
        assert_eq!(
            RotCaveatEntry::from_felts(&buf).expect("heap entry decodes"),
            heap
        );
        // Registers-domain round-trip (key inside the file).
        let slot = RotCaveatEntry {
            type_tag: crate::effect_vm::pi::SLOT_CAVEAT_TAG_MONOTONIC,
            domain_tag: cav::DOMAIN_REGISTERS,
            key: BabyBear::new(3),
            params: [BabyBear::ZERO; 4],
        };
        slot.write_to(&mut buf);
        assert_eq!(
            RotCaveatEntry::from_felts(&buf).expect("slot entry decodes"),
            slot
        );
        // A forged domain tag REFUSES (caps plane = 2 is NOT caveat-scopable).
        let mut forged = buf;
        forged[1] = BabyBear::new(2);
        assert!(
            RotCaveatEntry::from_felts(&forged).is_err(),
            "forged domain tag must refuse"
        );
        // A registers-domain key outside the R=24 file REFUSES.
        let mut oob = buf;
        oob[2] = BabyBear::new(cav::R as u32);
        assert!(
            RotCaveatEntry::from_felts(&oob).is_err(),
            "register key ≥ R must refuse"
        );
        // The zero entry is "no caveat".
        let zero = [BabyBear::ZERO; 7];
        assert_eq!(
            RotCaveatEntry::from_felts(&zero).expect("zero entry decodes"),
            RotCaveatEntry::zero()
        );
    }

    /// **THE CUSTOM PROOF-BIND COMMITMENT VERSION BOUNDARY (flag-day v2, blocker #2).**
    ///
    /// A LEGACY 4-felt custom artifact — the retired eight-pin exposure (commit limbs 0..4 at
    /// cols `PARAM_BASE+4..8` → PI 46..49, then the VK block DIRECTLY after at 50..53, NO commit
    /// teeth) — is REFUSED by the versioned route with the TYPED
    /// `CustomCommitVersionError::RetiredV1`, never silently widened or zero-padded. The live v2
    /// twelve-pin layout classifies `Ok(2)`; a pin-less descriptor and a garbled layout fail
    /// closed with their own typed variants. Also: the COMMITTED registry members (narrow + wide)
    /// classify as live v2.
    #[test]
    fn custom_commit_version_boundary_refuses_legacy_four_felt() {
        use crate::descriptor_ir2::{EffectVmDescriptor2, VmConstraint2};
        use crate::effect_vm::columns::{PARAM_BASE, param};
        use crate::effect_vm::trace_rotated::CUSTOM_COMMIT_TEETH_BASE;
        use crate::lean_descriptor_air::{VmConstraint, VmRow};

        let pin = |col: usize, pi_index: usize| {
            VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::First,
                col,
                pi_index,
            })
        };
        let mk =
            |name: &str, constraints: Vec<VmConstraint2>, pi_count: usize| EffectVmDescriptor2 {
                name: name.to_string(),
                trace_width: CUSTOM_COMMIT_TEETH_BASE + 4,
                public_input_count: pi_count,
                tables: vec![],
                constraints,
                hash_sites: vec![],
                ranges: vec![],
            };

        // The RETIRED v1 exposure: commit limbs 0..4 at 46..49, VK block directly after.
        let mut legacy_pins = Vec::new();
        for k in 0..4 {
            legacy_pins.push(pin(
                PARAM_BASE + param::CUSTOM_PROOF_COMMIT_BASE + k,
                46 + k,
            ));
        }
        for k in 0..4 {
            legacy_pins.push(pin(PARAM_BASE + param::CUSTOM_VK_HASH_BASE + k, 50 + k));
        }
        let legacy = mk("custom-legacy-4felt", legacy_pins, 54);
        assert_eq!(
            custom_commit_version(&legacy),
            Err(CustomCommitVersionError::RetiredV1 {
                name: "custom-legacy-4felt".to_string(),
                commit_pi_lo: 46,
            }),
            "a legacy 4-felt custom artifact MUST be version-refused (typed), never widened"
        );
        assert!(require_custom_commit_teeth_v2(&legacy).is_err());
        // The typed refusal names the retirement explicitly.
        let msg = require_custom_commit_teeth_v2(&legacy)
            .unwrap_err()
            .to_string();
        assert!(
            msg.contains("RETIRED") && msg.contains("version-refused"),
            "the refusal must name the version retirement: {msg}"
        );

        // The LIVE v2 exposure: commit limbs 0..4, commit teeth 4..8, then the VK block.
        let mut v2_pins = Vec::new();
        for k in 0..4 {
            v2_pins.push(pin(
                PARAM_BASE + param::CUSTOM_PROOF_COMMIT_BASE + k,
                46 + k,
            ));
        }
        for k in 0..4 {
            v2_pins.push(pin(CUSTOM_COMMIT_TEETH_BASE + k, 50 + k));
        }
        for k in 0..4 {
            v2_pins.push(pin(PARAM_BASE + param::CUSTOM_VK_HASH_BASE + k, 54 + k));
        }
        let live = mk("custom-live-8felt", v2_pins, 58);
        assert_eq!(custom_commit_version(&live), Ok(CUSTOM_COMMIT_VERSION));

        // No commit pin at all: not a custom-exposure member — fail closed.
        let none = mk("no-commit-pins", vec![pin(0, 3)], 10);
        assert!(matches!(
            custom_commit_version(&none),
            Err(CustomCommitVersionError::MissingCommitPins { .. })
        ));

        // Garbled: commit limbs 0..4 present but the following slots pin neither the VK block
        // nor teeth (a param column that is not the VK block) — fail closed as UnknownLayout.
        let mut garbled_pins = Vec::new();
        for k in 0..4 {
            garbled_pins.push(pin(
                PARAM_BASE + param::CUSTOM_PROOF_COMMIT_BASE + k,
                46 + k,
            ));
        }
        for k in 0..4 {
            garbled_pins.push(pin(PARAM_BASE + 2, 50 + k)); // a bogus mid-block pin
        }
        let garbled = mk("custom-garbled", garbled_pins, 54);
        assert!(matches!(
            custom_commit_version(&garbled),
            Err(CustomCommitVersionError::UnknownLayout { .. })
        ));

        // The COMMITTED members classify as live v2 — narrow (v3rot registry) and wide.
        // Both registries are `key\tname\tjson` (3 fields — see V3_STAGED_REGISTRY_TSV docs).
        let narrow_json = V3_STAGED_REGISTRY_TSV
            .lines()
            .find_map(|line| {
                let mut it = line.splitn(3, '\t');
                if it.next() == Some("customVmDescriptor2R24") {
                    let _name = it.next();
                    it.next()
                } else {
                    None
                }
            })
            .expect("custom member IS in the v3 staged registry");
        let narrow = parse_vm_descriptor2(narrow_json).expect("narrow custom parses");
        assert_eq!(custom_commit_version(&narrow), Ok(CUSTOM_COMMIT_VERSION));

        let wide_json = WIDE_REGISTRY_STAGED_TSV
            .lines()
            .find_map(|line| {
                let mut it = line.splitn(3, '\t');
                if it.next() == Some("customVmDescriptor2R24") {
                    let _name = it.next();
                    it.next()
                } else {
                    None
                }
            })
            .expect("custom member IS in the wide staged registry");
        let wide = parse_vm_descriptor2(wide_json).expect("wide custom parses");
        assert_eq!(custom_commit_version(&wide), Ok(CUSTOM_COMMIT_VERSION));
    }
}
