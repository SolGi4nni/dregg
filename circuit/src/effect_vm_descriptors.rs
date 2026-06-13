//! # `effect_vm_descriptors` — the Lean-emitted EffectVM descriptor REGISTRY.
//!
//! This is the foundation for the EffectVM circuit cutover: a registry of every
//! verified-by-construction `EffectVmDescriptor` that Lean's `emitVmJson` renders,
//! embedded here as committed JSON and keyed by the running prover's per-effect
//! **selector index** (`effect_vm::columns::sel`). The descriptor interpreter
//! (`lean_descriptor_air::parse_vm_descriptor` + `EffectVmDescriptorAir`) ingests
//! the selected JSON to drive the verified circuit for that effect.
//!
//! ## Provenance (anti-drift)
//!
//! Each `*.json` under `circuit/descriptors/` is the **byte-exact** output of the
//! Lean executable `Dregg2/Circuit/Emit/EmitAllJson.lean` (run via
//! `lake env lean --run`), which imports every `EffectVmEmit<Effect>.lean` module
//! and prints `<def>\t<name>\t<emitVmJson desc>`. The JSON is NOT hand-written.
//! The `*_FP` constants are the SHA-256 of those exact bytes; the drift test
//! (`tests/effect_vm_descriptor_registry.rs` + the `#[test]` below) re-hashes the
//! embedded bytes and re-parses each via `parse_vm_descriptor`, so any Lean→Rust
//! drift (a re-emit that changes a gate / a stale committed JSON) fails CI.
//!
//! ## Coverage (HONEST)
//!
//! 25 UNIQUE descriptors are registered (VERB-LOCKSTEP: the 22 descriptors of
//! the factory-dissolved families — escrow/obligation-adjacent legs, the queue
//! family, seal/unseal/seal-pair, the swiss/sturdyref/handoff family, bridge
//! lock/finalize/cancel — died with their `Effect` variants; their semantics
//! are the factory-cell story). The `attenuateA` cap-root-move object is
//! SHARED by attenuate / delegate (ATTENUATE_CAPABILITY=48, GRANT_CAP=3);
//! `revokeDelegation-v2` / `introduce-v2` carry their OWN frozen-frame +
//! nonce-TICK descriptors, and the cap-table semantics are bound OFF-row via
//! each module's universe-A connector.
//!
//!   * `SELECTOR_DESCRIPTORS`: 24 of the 29 LIVE EffectVM selectors carry a
//!     descriptor (the 5 others — NOOP, SET_FIELD, CUSTOM, REVOKE_CAPABILITY,
//!     CELL_UNSEAL — have no emit module yet). Two selectors (3/48 cap moves)
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
//! refresh: re-run `EmitAllJson.lean`, rewrite `circuit/descriptors/*.json`,
//! recompute the `*_FP` SHA-256s, and regenerate this block. The drift test will
//! reject any inconsistency.

// ==== include_str! consts + sha256 fingerprints (auto-generated; do not hand-edit) ====
pub const DREGG_EFFECTVM_ATTENUATEA_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-attenuateA-v1.json");
pub const DREGG_EFFECTVM_ATTENUATEA_V1_FP: &str =
    "c9132246c00ed71bc4f297803e631b849fa2e9ee2c481e543d4d4e3a9c5a97e0";
pub const DREGG_EFFECTVM_BRIDGEMINT_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-bridgemint-v1.json");
pub const DREGG_EFFECTVM_BRIDGEMINT_V1_FP: &str =
    "fce2cb4ce9685f8b322a075ded2896d5c39378242d2e8da0e7f8650d0cf35872";
pub const DREGG_EFFECTVM_BURN_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-burn-v1.json");
pub const DREGG_EFFECTVM_BURN_V1_FP: &str =
    "3c49af13cae8285f136b8cdf06632a76bd2f5c0c3a156eba3275254d3fbd5d50";
// GRADUATED (nonce-tick reconcile, v2): frozen-balance + ticked-nonce effect; the Lean descriptor
// now ticks the runtime nonce (`gNonce`) AND carries the full last-row balance PI binding
// (`boundaryLastPins`), so the descriptor decides IDENTICALLY to the hand-AIR on the real witness
// (honest accept + forged-balance/forged-state-commit reject). Body STRUCTURALLY IDENTICAL to the
// validated `createsealpair-v2` (only the `name` differs). Name bumped `-v1`→`-v2`; FP updated.
pub const DREGG_EFFECTVM_CELLDESTROY_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-celldestroy-v2.json");
pub const DREGG_EFFECTVM_CELLDESTROY_V2_FP: &str =
    "9630d7317d3f21c659e6b8566f97e63ef2c3b71869d99b7bddb2f85431558f65";
pub const DREGG_EFFECTVM_CELLSEAL_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-cellseal-v2.json");
pub const DREGG_EFFECTVM_CELLSEAL_V2_FP: &str =
    "a3809a09772bf80225b4f35050e9dc861c1d53b0db3f13b06fb6cd7d622e9b91";
// GRADUATED (lifecycle Sealed→Live, v2): the runtime row is the SAME frozen-frame + nonce-tick
// passthrough as cellSeal (the trace arm ticks the nonce, freezes the economic block; the single
// CELL_UNSEAL_TARGET param binds the cell). The lifecycle flip is the off-row face, verified in
// `EffectVmEmitCellUnseal` (`cellUnsealA_full_sound`). Body structurally identical to cellseal-v2
// with `selectorGates 50`.
pub const DREGG_EFFECTVM_CELLUNSEAL_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-cellunseal-v2.json");
pub const DREGG_EFFECTVM_CELLUNSEAL_V2_FP: &str =
    "c7d5d45d8acac041d5221e974bf758d6883db5f2c1e8250338902288aeeffba1";
// GRADUATED (lifecycle/birth reconcile, v2): the WIRE descriptor is now the RUNTIME ACTOR row
// (frozen-frame + nonce-tick + last-row PI pins, body structurally identical to the validated
// `revokeDelegation-v2` template). The pre-v2 JSON pinned the BORN-EMPTY CHILD cell, which the
// runtime row (the acting cell's Stage-3 passthrough) cannot satisfy; the child face stays verified
// in the Lean module (`EffectVmEmitCreateCell`, off-row via `createCellA_full_sound`).
pub const DREGG_EFFECTVM_CREATECELL_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-createcell-v2.json");
pub const DREGG_EFFECTVM_CREATECELL_V2_FP: &str =
    "9d81f918ff15101414f96a36272af597638d7d1c7f6ef17030ac2221d5823868";
// GRADUATED (lifecycle/birth reconcile, v2): same actor-row reconcile as createcell-v2; the minted
// cell's born-empty face stays in `EffectVmEmitCreateCellFromFactory`.
pub const DREGG_EFFECTVM_CREATECELLFROMFACTORY_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-createcellfromfactory-v2.json");
pub const DREGG_EFFECTVM_CREATECELLFROMFACTORY_V2_FP: &str =
    "3724ed691f5677f5dac0777947868dec6b424004c30ac78c87ac0c394b926e8f";
// emitEvent GRADUATED into the cutover (passthrough+tick reconcile): the Lean emit module
// `EffectVmEmitEmitEvent` now ticks the runtime nonce (`gNonce`), freezes the economic block (NOT the
// commit), and carries the selector-binding gate (`selectorGates 25`). The prior JSON froze the nonce +
// the commit (made the honest TICKED trace UNSAT). Name unchanged (`-v1`); body + fingerprint updated.
pub const DREGG_EFFECTVM_EMITEVENT_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-emitEvent-v1.json");
pub const DREGG_EFFECTVM_EMITEVENT_V1_FP: &str =
    "9da75b2120a3492a37719177d343c681a8f3acd967f0fed880cf7aa0f400c250";
// GRADUATED (nonce-tick + last-row PI pins, v2): the Lean emit module was reconciled onto the runtime
// Stage-3 passthrough batch (whole economic block frozen, nonce ticks via `gNonce`) AND grew the
// `boundaryLastPins` last-row balance PI binding. Body STRUCTURALLY IDENTICAL to the validated
// `createsealpair-v2`; the JSON had not been re-emitted. Name `-v1`→`-v2`; FP updated.
pub const DREGG_EFFECTVM_EXERCISEA_HOLDLAYER_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-exerciseA-holdlayer-v2.json");
pub const DREGG_EFFECTVM_EXERCISEA_HOLDLAYER_V2_FP: &str =
    "0a01f957422c4ef75200ac138a6ccf3ac31ed6574adce88f377935e7a6f6a367";
// GRADUATED (nonce-tick + last-row PI pins, v2): the explicit nonce-only effect. The Lean module was
// reconciled to the runtime TICK (`new_state.nonce += 1`) via `gNonce` and grew `boundaryLastPins`,
// dropping the prior param-bound nonce gate; body STRUCTURALLY IDENTICAL to `createsealpair-v2`. The
// committed JSON was the stale param-bound v1. Name `-v1`→`-v2`; FP updated.
pub const DREGG_EFFECTVM_INCREMENTNONCE_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-incrementNonce-v2.json");
pub const DREGG_EFFECTVM_INCREMENTNONCE_V2_FP: &str =
    "85ca061301a6a634367313ec2f6e15ae52dcf2ebba24b8b7d8613fccb693190b";
// GRADUATED (sovereign mode-bit reconcile, v2): the WIRE descriptor is the RUNTIME row — frame
// freeze + `reserved += 256` (the packed mode_flag bit the hand-AIR enforces) + nonce tick + last-row
// PI pins. The pre-v2 JSON pinned the executor's REBIND-TO-ZERO face (readable record dropped behind
// `stateCommitment`), which the runtime row cannot satisfy; that face stays verified in
// `EffectVmEmitMakeSovereign`. WHICH sovereignty semantics is canonical (rebind-zero vs mode-bit)
// remains an open protocol decision — the cutover models what the runtime proves today.
pub const DREGG_EFFECTVM_MAKESOVEREIGN_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-makesovereign-v2.json");
pub const DREGG_EFFECTVM_MAKESOVEREIGN_V2_FP: &str =
    "bcba40ad392d89fa1834b2a7e652c1044478ea67c651b614f360b811d2756dfd";
pub const DREGG_EFFECTVM_MINT_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-mint-v1.json");
pub const DREGG_EFFECTVM_MINT_V1_FP: &str =
    "afbf531ac2c17447f90764960691587f86b0b18ecd06d5425ed8e6ef1cfd2935";
pub const DREGG_EFFECTVM_NOTECREATE_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-notecreate-v1.json");
pub const DREGG_EFFECTVM_NOTECREATE_V1_FP: &str =
    "d323c2f0602c55bea80576e2d8d78c6f06eebd445dafd1345a68a2077e63f98d";
pub const DREGG_EFFECTVM_NOTESPEND_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-notespend-v1.json");
pub const DREGG_EFFECTVM_NOTESPEND_V1_FP: &str =
    "68f057ead33d6a66fe778eb8c2659e5d98d81ea0259cbb5a2c755caf24aa0cdb";
// GRADUATED (nonce-tick + last-row PI pins, v2): see exercise note. Body STRUCTURALLY IDENTICAL to
// `createsealpair-v2`. Name `-v1`→`-v2`; FP updated.
pub const DREGG_EFFECTVM_PIPELINEDSENDA_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-pipelinedSendA-v2.json");
pub const DREGG_EFFECTVM_PIPELINEDSENDA_V2_FP: &str =
    "56083a4facb4ff4f08f8eec97d369e0a0f24bb178414f45b168b70bd2a6817af";
// GRADUATED (lifecycle-SET reconcile, v2): the WIRE descriptor is the RUNTIME row — pure
// frozen-frame + nonce-tick (the hand-AIR freezes field[1] and ticks the nonce; the archive
// lifecycle write lives off-row via effects_hash). The pre-v2 JSON SET field[1] := 1 and froze the
// nonce (the executor face), UNSAT on the runtime trace; that face stays verified in
// `EffectVmEmitReceiptArchive`.
pub const DREGG_EFFECTVM_RECEIPTARCHIVEA_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-receiptArchiveA-v2.json");
pub const DREGG_EFFECTVM_RECEIPTARCHIVEA_V2_FP: &str =
    "1a33f199855913a32adf965c3f207e54ea38c922929ab61a2f3fb0252ce91dcc";
// GRADUATED (nonce-tick + last-row PI pins, v2): refreshDelegation already ticked the runtime nonce
// (`gNonce`) but the committed JSON carried only `boundaryFirstPins` (anti-ghost WEAK: the forged
// last-row balance tooth did not bite). The Lean module grew `boundaryLastPins` + the 2 balance ranges.
// Name `-v1`→`-v2`; FP updated.
pub const DREGG_EFFECTVM_REFRESHDELEGATION_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-refreshDelegation-v2.json");
pub const DREGG_EFFECTVM_REFRESHDELEGATION_V2_FP: &str =
    "ad6b56c715fd9d4dd269ea5739281a60011aa4da967af865cd147f06a8c08be5";
// GRADUATED (nonce-tick + last-row PI pins, v2): revokeDelegation was PRE-v2 pointed at the
// `attenuateA` cap-root-MOVE descriptor, which the runtime hand-AIR does NOT enforce on a revoke row
// (it FREEZES `cap_root`); it "passed" only by fixture accident (cap_root = param2 = 0). The v2 Lean
// module emits the runtime frozen-frame + nonce-TICK directly; the cap-table edge removal is bound
// OFF-row via the universe-A connector. Body STRUCTURALLY IDENTICAL to `createsealpair-v2`.
pub const DREGG_EFFECTVM_REVOKEDELEGATION_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-revokeDelegation-v2.json");
pub const DREGG_EFFECTVM_REVOKEDELEGATION_V2_FP: &str =
    "854fd94989861477bba0c811fe895ade347a22f88ce66c7ae074a173f223343a";
// GRADUATED (nonce-tick + last-row PI pins, v2): introduce, same reconcile as revokeDelegation (was
// PRE-v2 pointed at `attenuateA`). The cap-table grant is bound OFF-row via the universe-A connector.
pub const DREGG_EFFECTVM_INTRODUCE_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-introduce-v2.json");
pub const DREGG_EFFECTVM_INTRODUCE_V2_FP: &str =
    "e1050c3cd4b2456190ba2ebf2868771de31d143c3e9a4da8786a43e6df94d89f";
// GRADUATED (nonce-tick reconcile, v2): see celldestroy/cellseal note. Body STRUCTURALLY IDENTICAL
// to `createsealpair-v2`. Name bumped `-v1`→`-v2`; FP updated.
pub const DREGG_EFFECTVM_REFUSAL_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-refusal-v2.json");
pub const DREGG_EFFECTVM_REFUSAL_V2_FP: &str =
    "519d878769bf55262470e89d55b1a846e4db0c015b2e8bbbdcd1796c0fa699c8";
// GRADUATED (nonce-tick + last-row PI pins, v2): see exercise note. Body STRUCTURALLY IDENTICAL to
// `createsealpair-v2`. Name `-v1`→`-v2`; FP updated.
pub const DREGG_EFFECTVM_SETPERMISSIONSA_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-setPermissionsA-v2.json");
pub const DREGG_EFFECTVM_SETPERMISSIONSA_V2_FP: &str =
    "f988c68ab91e611e5c5d8190396c85dfdcdf9c14703172fb3218dc140571a4e9";
pub const DREGG_EFFECTVM_SETVK_V2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-setVK-v2.json");
pub const DREGG_EFFECTVM_SETVK_V2_FP: &str =
    "baf0e80f132bfa9ed8e0a6f210655052472df520d8d76c23873ec1561d660628";
// GRADUATED (lifecycle/birth reconcile, v3): the WIRE descriptor is the RUNTIME ACTOR (parent) row
// (frozen-frame + nonce-tick). The pre-v3 `v2quint-childcell` JSON pinned the born-empty + cap-handoff
// CHILD cell, which the runtime row cannot satisfy; the child face stays verified in
// `EffectVmEmitSpawn` (off-row via `spawnA_full_sound`).
pub const DREGG_EFFECTVM_SPAWNA_V3_ACTORROW_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-spawnA-v3-actorrow.json");
pub const DREGG_EFFECTVM_SPAWNA_V3_ACTORROW_FP: &str =
    "1f233ec3c0990b76853eca4cd86dc444e0bea63adc831e7f15430c29ecc9d0a5";
pub const DREGG_EFFECTVM_TRANSFER_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-transfer-v1.json");
pub const DREGG_EFFECTVM_TRANSFER_V1_FP: &str =
    "34ce263778bbbd209abe2e8a44af4ff492e2570f5aab55362c5fd219184b66df";
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
    "8c0a25d8b1c4b63ad0957516ff89eb7f10d8e3ba5ad310d2d64950a12ab3d6a8";

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
    "dfbb072d8b4abe68b7ea2c184f40971f473869102079865263ab25e125a91abd";
pub const DREGG_EFFECTVM_BURN_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-burn-ir2.json");
pub const DREGG_EFFECTVM_BURN_IR2_FP: &str =
    "b774cca29d918f917e620474352c308d040632b396392cebf9852ebe1eeba609";
pub const DREGG_EFFECTVM_MINT_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-mint-ir2.json");
pub const DREGG_EFFECTVM_MINT_IR2_FP: &str =
    "5fc8021abf225b689bccadc7a5f66810d7aec0a737e177f6c7a24451f7230627";
pub const DREGG_EFFECTVM_NOTE_SPEND_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-note-spend-ir2.json");
pub const DREGG_EFFECTVM_NOTE_SPEND_IR2_FP: &str =
    "233986f9087db17190ead8738d7bcc17c3a249cfbd144d231b75718d952e8718";
pub const DREGG_EFFECTVM_NOTE_CREATE_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-note-create-ir2.json");
pub const DREGG_EFFECTVM_NOTE_CREATE_IR2_FP: &str =
    "7c7bd3857023489bd6d8aa08360bc48031a8db3d35d8b2a5b09e183b318b3c0d";
pub const DREGG_EFFECTVM_CELL_SEAL_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-cell-seal-ir2.json");
pub const DREGG_EFFECTVM_CELL_SEAL_IR2_FP: &str =
    "d5438a848af9324effc6f2fc355cc7567c10f0a48acec7d812ec718beb0c84ed";
pub const DREGG_EFFECTVM_CELL_DESTROY_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-cell-destroy-ir2.json");
pub const DREGG_EFFECTVM_CELL_DESTROY_IR2_FP: &str =
    "3ed698e913022364620d16e7ce92d95c04c5ab52985a98b7397a7860649d78d1";
pub const DREGG_EFFECTVM_REFUSAL_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-refusal-ir2.json");
pub const DREGG_EFFECTVM_REFUSAL_IR2_FP: &str =
    "2b50ef88cc82bcd6e6cd93e80d9a12537ebc86ee3c7ffdf74170a5da979c8629";
pub const DREGG_EFFECTVM_SET_PERMS_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-perms-ir2.json");
pub const DREGG_EFFECTVM_SET_PERMS_IR2_FP: &str =
    "09b4b9853b19a1a0160fc75a86c2fd2e4e7134d0a98c2e5746f7f2224f14a5e3";
pub const DREGG_EFFECTVM_SET_VK_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-vk-ir2.json");
pub const DREGG_EFFECTVM_SET_VK_IR2_FP: &str =
    "1d1b77641197e4d0d293a778a5038405cbac7776ad0f1c5608b4b97ed0ed1845";
pub const DREGG_EFFECTVM_EXERCISE_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-exercise-ir2.json");
pub const DREGG_EFFECTVM_EXERCISE_IR2_FP: &str =
    "68bbb2fc28d868296f3f28127d068cef81c3572598bff6f173665a2b6caeb623";
pub const DREGG_EFFECTVM_PIPELINED_SEND_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-pipelined-send-ir2.json");
pub const DREGG_EFFECTVM_PIPELINED_SEND_IR2_FP: &str =
    "12b06b7a67a5c64dfe5ff19530fc0d4e4f7b8f1268e3365bf26d3199a732caa3";
pub const DREGG_EFFECTVM_REFRESH_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-refresh-ir2.json");
pub const DREGG_EFFECTVM_REFRESH_IR2_FP: &str =
    "4cff64900f8e448d096dc68d5c3492221bfb969ba4c2921ae4d7567f23745ae5";
pub const DREGG_EFFECTVM_INCREMENT_NONCE_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-increment-nonce-ir2.json");
pub const DREGG_EFFECTVM_INCREMENT_NONCE_IR2_FP: &str =
    "4d1d14fe2a6c2dab9c1ced872f5923a527297c62d85163a7ab52ad889667c34e";
pub const DREGG_EFFECTVM_REVOKE_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-revoke-ir2.json");
pub const DREGG_EFFECTVM_REVOKE_IR2_FP: &str =
    "084f26bb514051cc3c8091c7d8cdc3da5fb2c062d5fed17c759df2a86c2e5e1f";
pub const DREGG_EFFECTVM_INTRODUCE_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-introduce-ir2.json");
pub const DREGG_EFFECTVM_INTRODUCE_IR2_FP: &str =
    "844f639b3bc67bf7bfeda2fdb8495ac72735c427bdda5978c735bbd302e52a4b";
pub const DREGG_EFFECTVM_ATTENUATE_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-attenuate-ir2.json");
pub const DREGG_EFFECTVM_ATTENUATE_IR2_FP: &str =
    "606d2db855d06129c0f1f4faba6ccf6b84ae7e4fef6885c48914f653a2cd658d";
pub const DREGG_EFFECTVM_SET_FIELD_DYN_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-field-dyn-ir2.json");
pub const DREGG_EFFECTVM_SET_FIELD_DYN_IR2_FP: &str =
    "d0e1e196fd68f91afeb507f0760b2054eacda1759d81a3db6e772fa8485f3bfe";
pub const DREGG_EFFECTVM_SET_FIELD_0_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-field-0-ir2.json");
pub const DREGG_EFFECTVM_SET_FIELD_0_IR2_FP: &str =
    "df2405f05a4e4efd301f197a8e54e86579a11fd31fcdf79a7f73ac6cf1229480";
pub const DREGG_EFFECTVM_SET_FIELD_1_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-field-1-ir2.json");
pub const DREGG_EFFECTVM_SET_FIELD_1_IR2_FP: &str =
    "44784f2bd822f00de34045ff3ba7bd0fb3db871f11ed2bee1b4ccbcdfb352f0d";
pub const DREGG_EFFECTVM_SET_FIELD_2_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-field-2-ir2.json");
pub const DREGG_EFFECTVM_SET_FIELD_2_IR2_FP: &str =
    "fd2d4779f83ff487bc4537018dcf851aa4426c25fc68d4da100821b10d8865db";
pub const DREGG_EFFECTVM_SET_FIELD_3_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-field-3-ir2.json");
pub const DREGG_EFFECTVM_SET_FIELD_3_IR2_FP: &str =
    "608f692524f8e3ad836f5029ebfa2a97dbaa96a48bdbe82dfdc57ada7997ab6c";
pub const DREGG_EFFECTVM_SET_FIELD_4_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-field-4-ir2.json");
pub const DREGG_EFFECTVM_SET_FIELD_4_IR2_FP: &str =
    "3e7d0504b72738ef816d4a3655150d5a02189e45e6a41bee11b2b2d10b454adf";
pub const DREGG_EFFECTVM_SET_FIELD_5_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-field-5-ir2.json");
pub const DREGG_EFFECTVM_SET_FIELD_5_IR2_FP: &str =
    "405612aa93b657c728f7e99da9a5eb7000639b1db538aafaee8494b42ea17a78";
pub const DREGG_EFFECTVM_SET_FIELD_6_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-field-6-ir2.json");
pub const DREGG_EFFECTVM_SET_FIELD_6_IR2_FP: &str =
    "a0d6d4a1792b06c72b66f0fc5a14ff33705ace8616a613667394ffeb437988e9";
pub const DREGG_EFFECTVM_SET_FIELD_7_IR2_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-set-field-7-ir2.json");
pub const DREGG_EFFECTVM_SET_FIELD_7_IR2_FP: &str =
    "4edd664b2f61ac9f5a4fe9ab7873d9a9c6469d8bb9b7a1dd1c3ec4f392811bf4";

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
    "518b290c2cc9aabd04a113611480059762d6720b04b2d6667e49aec49bfde3da";

/// The staged rotation-state probe descriptor (`rotationProbeVmDescriptor2` =
/// `graduateV1` of the 8-site chained absorption + the two PI pins; Lean keystones
/// `rotationProbeV2_pins_commit` / `rotationProbe_commit_binds_published`).
pub const DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-rotation-state-v3-staged.json");
pub const DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_FP: &str =
    "f80801c9eb428d005232c250ff2d873432a7edb982dd6c0bf39c669311554c26";

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
    "78924093cf0617e1c80b7384e99a72bffaff4df4283e131108797e7ea9a5f360";
pub const DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_R32_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-rotation-state-v3-staged-r32.json");
pub const DREGG_EFFECTVM_ROTATION_STATE_V3_STAGED_R32_FP: &str =
    "cbe22881a7de7a73473f5ba75a445b1e7c2906b2f2fd39fd466364f616dfbdb5";

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
    "a1d926d7c8cd8ac08e1957eae3353e87bf9bbcfaebf89bbb1dea6f981bdbb89b";

/// The caveat-operand staged registry (kept SEPARATE from `V3_STAGED_DESCRIPTORS`
/// so the three rotation-probe pins stay byte-frozen and their coverage walker
/// unchanged).
pub const V3_STAGED_CAVEAT_DESCRIPTORS: &[(&str, &str, &str)] = &[(
    "rotationCaveatProbeVmDescriptor2",
    DREGG_EFFECTVM_ROTATION_CAVEAT_V3_STAGED_JSON,
    DREGG_EFFECTVM_ROTATION_CAVEAT_V3_STAGED_FP,
)];

/// THE FULL-COHORT REGEN at the rotated R=24 block (`ROTATION-CUTOVER.md` §5 item 1):
/// all 26 cohort descriptors re-emitted past their v1 layout with the rotated
/// BEFORE/AFTER blocks + the widened-caveat region (Lean `rotateV3` /
/// `EffectVmEmitRotationV3.lean`; `v3Registry` is the source). The TSV is `key\tname\tjson`
/// per line, sha-256 pinned by `v3_staged_registry_parses_matches_fingerprint_and_covers`.
/// STAGED: a new constant, no VK bump, the live wire untouched. Each descriptor's
/// `trace_width = EFFECT_VM_WIDTH (186) + APPENDIX_SPAN (125) = 311`; the rotated
/// commitments ride four appended PI slots (rotated OLD/NEW commit · height · caveat commit).
pub const V3_STAGED_REGISTRY_TSV: &str =
    include_str!("../descriptors/rotation-v3-staged-registry.tsv");
pub const V3_STAGED_REGISTRY_FP: &str =
    "1d94da6e28f1d4af27b3e897505e34453e861971a49b52bb79cc01ce045c4dcc";

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

    /// THE DRIFT GUARD: every registered descriptor (a) re-hashes to its committed
    /// fingerprint and (b) re-parses via `parse_vm_descriptor` without error, with
    /// the parsed `name` matching the registry key. Binds the Rust registry to the
    /// Lean `emitVmJson` bytes — any Lean re-emit that changes a descriptor, or a
    /// stale committed JSON, fails here.
    #[test]
    fn all_descriptors_parse_and_match_fingerprint() {
        assert_eq!(ALL_DESCRIPTORS.len(), 26, "expected 26 unique descriptors");
        for (name, json, fp) in ALL_DESCRIPTORS {
            // (a) fingerprint binding
            let got = sha256_hex(json.as_bytes());
            assert_eq!(
                &got, fp,
                "descriptor {name}: SHA-256 drift — committed {fp}, embedded bytes hash {got}"
            );
            // (b) parses + name round-trips
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
    /// JSON+fingerprint is identical to the `ALL_DESCRIPTORS` entry of the same
    /// name, and every selector descriptor parses.
    #[test]
    fn selector_table_consistent() {
        for (sel, name, json, fp) in SELECTOR_DESCRIPTORS {
            let by_name = descriptor_for_name(name)
                .unwrap_or_else(|| panic!("selector {sel} name {name} not in ALL_DESCRIPTORS"));
            assert_eq!(
                *json, by_name,
                "selector {sel}: JSON differs from name registry"
            );
            assert_eq!(
                Some(*fp),
                fingerprint_for_name(name),
                "selector {sel}: fingerprint differs from name registry"
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
        for (name, json, fp) in NAME_ONLY_DESCRIPTORS {
            assert_eq!(descriptor_for_name(name), Some(*json));
            assert_eq!(fingerprint_for_name(name), Some(*fp));
            // not bound to any selector
            assert!(
                SELECTOR_DESCRIPTORS.iter().all(|(_, n, _, _)| n != name),
                "name-only descriptor {name} unexpectedly has a selector"
            );
        }
    }

    /// THE IR-v2 DRIFT GUARD + ROUND-TRIP: every `V2_DESCRIPTORS` entry (a) re-hashes to its
    /// committed fingerprint (Lean→Rust byte binding) and (b) round-trips through the v2 decoder
    /// `descriptor_ir2::parse_vm_descriptor2` — a `"ir":2` wire with the five EPOCH tables and the
    /// lookup/mem_op/map_op grammar, NOT the v1 wire. Any re-emit of `EmitAllJsonV2.lean` that
    /// changes a descriptor (or a stale committed JSON) fails here.
    #[test]
    fn v2_descriptors_parse_and_match_fingerprint() {
        assert_eq!(V2_DESCRIPTORS.len(), 26, "expected 26 IR-v2 descriptors");
        for (key, json, fp) in V2_DESCRIPTORS {
            // (a) fingerprint binding
            let got = sha256_hex(json.as_bytes());
            assert_eq!(
                &got, fp,
                "v2 descriptor {key}: SHA-256 drift — committed {fp}, embedded bytes hash {got}"
            );
            // (b) round-trips through the v2 multi-table decoder
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
            t.trace_width, 186,
            "graduated transfer keeps the 186 base width"
        );
        assert_eq!(t.public_input_count, 34);
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
        // The manifest file itself is fingerprint-pinned (stale-file tooth).
        assert_eq!(
            sha256_hex(ROTATION_LAYOUT_V3_STAGED_JSON.as_bytes()),
            ROTATION_LAYOUT_V3_STAGED_FP,
            "rotation layout manifest: SHA-256 drift"
        );
    }

    /// The v3-staged probe registry: fingerprint binding + round-trip through the
    /// IR-v2 decoder + PRESENCE at EVERY register count — each probe's chip-lookup
    /// chain must absorb EVERY rotated limb column exactly once, in the absorption
    /// order, with the final digest on `STATE_COMMIT` (a re-emit that drops a limb —
    /// e.g. the heap_root, or a widened register — fails HERE, before any prover
    /// runs). The presence-refusal tooth scales with the block: a wider block with
    /// untested columns would be worse than a narrow one.
    #[test]
    fn v3_staged_descriptors_parse_match_fingerprint_and_cover_all_limbs() {
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
        for (key, json, fp) in V3_STAGED_DESCRIPTORS {
            let r = match *key {
                "rotationProbeVmDescriptor2" => 16,
                "rotationProbeVmDescriptorR24" => 24,
                "rotationProbeVmDescriptorR32" => 32,
                other => panic!("unknown v3-staged key {other}"),
            };
            let lay = rotation_layout_for(r);
            assert_eq!(
                &sha256_hex(json.as_bytes()),
                fp,
                "v3 staged {key}: SHA-256 drift"
            );
            let d = parse_vm_descriptor2(json)
                .unwrap_or_else(|e| panic!("v3 staged {key} failed parse_vm_descriptor2: {e}"));
            assert_eq!(d.trace_width, lay.probe_width, "{key}: probe width");
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
                    let (digest, inputs) = vars.split_last().expect("chip tuple has a digest");
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
        assert_eq!(
            sha256_hex(ROTATION_CAVEAT_LAYOUT_V3_STAGED_JSON.as_bytes()),
            ROTATION_CAVEAT_LAYOUT_V3_STAGED_FP,
            "caveat-operand layout manifest: SHA-256 drift"
        );
    }

    /// The staged caveat probe: fingerprint binding + round-trip through the IR-v2
    /// decoder + PRESENCE — the chip-lookup chain must absorb the WHOLE R=24 rotated
    /// block (cells root … iroot) AND the WHOLE 29-felt caveat manifest block (count +
    /// every entry's type tag, DOMAIN TAG, KEY, params) exactly once, in order, with
    /// the rotation digest landing on `state_commit` and the caveat digest on
    /// `CAVEAT_COMMIT`. A re-emit that drops a manifest column (e.g. a domain tag)
    /// fails HERE, before any prover runs.
    #[test]
    fn v3_staged_caveat_descriptor_parses_matches_fingerprint_and_covers_manifest() {
        use crate::descriptor_ir2::VmConstraint2;
        use crate::effect_vm::columns::rotation::caveat as cav;
        use crate::lean_descriptor_air::LeanExpr;
        assert_eq!(V3_STAGED_CAVEAT_DESCRIPTORS.len(), 1);
        let (key, json, fp) = V3_STAGED_CAVEAT_DESCRIPTORS[0];
        assert_eq!(&sha256_hex(json.as_bytes()), fp, "{key}: SHA-256 drift");
        let d = parse_vm_descriptor2(json)
            .unwrap_or_else(|e| panic!("{key} failed parse_vm_descriptor2: {e}"));
        assert_eq!(d.trace_width, cav::PROBE_WIDTH, "{key}: probe width");
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
                let (digest, inputs) = vars.split_last().expect("chip tuple has a digest");
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

    /// THE FULL-COHORT REGEN drift guard (`ROTATION-CUTOVER.md` §5 item 1): the staged
    /// 26-descriptor registry is sha-pinned (whole TSV), every line round-trips through the
    /// IR-v2 decoder, and each descriptor carries the rotated appendix EXACTLY — two rotated
    /// state blocks (each absorbing cells-root … iroot in order onto its own state-commit
    /// carrier) + the widened-caveat region (the 29-felt manifest onto CAVEAT_COMMIT), with
    /// the four appended PI pins (rotated OLD/NEW commit · height · caveat commit) at the
    /// descriptor's own `piCount..piCount+3`. A re-emit that drops a limb, a manifest felt,
    /// or a PI pin fails HERE, before any prover runs. STAGED: nothing on the live wire.
    #[test]
    fn v3_staged_registry_parses_matches_fingerprint_and_covers() {
        use crate::descriptor_ir2::VmConstraint2;
        use crate::effect_vm::columns::EFFECT_VM_WIDTH;
        use crate::effect_vm::columns::rotation::caveat as cav;
        use crate::lean_descriptor_air::{LeanExpr, VmConstraint};

        // Whole-TSV fingerprint (the Lean driver `EmitRotationV3.lean` is the byte source).
        assert_eq!(
            sha256_hex(V3_STAGED_REGISTRY_TSV.as_bytes()),
            V3_STAGED_REGISTRY_FP,
            "v3 full-cohort registry TSV: SHA-256 drift (re-run EmitRotationV3.lean)"
        );

        // The rotated geometry (R=24), relative to a block base. Mirrors the Lean
        // `EffectVmEmitRotationV3` §1 constants and the caveat region inside it.
        const V1_WIDTH: usize = EFFECT_VM_WIDTH; // 186
        const B_SPAN: usize = 43;
        const B_STATE_COMMIT: usize = 32;
        const B_COMMITTED_HEIGHT: usize = 30;
        const C_SPAN: usize = 39;
        const C_COMMIT: usize = 38;
        const APPENDIX_SPAN: usize = 2 * B_SPAN + C_SPAN; // 125
        let rot = rotation_layout_for(24);
        assert_eq!(rot.iroot, 31, "R=24 iroot offset");
        assert_eq!(rot.state_commit, B_STATE_COMMIT);
        assert_eq!(rot.committed_height, B_COMMITTED_HEIGHT);

        let mut n = 0usize;
        for line in V3_STAGED_REGISTRY_TSV.lines() {
            if line.is_empty() {
                continue;
            }
            n += 1;
            let mut it = line.splitn(3, '\t');
            let key = it.next().expect("tsv key");
            let _name = it.next().expect("tsv name");
            let json = it.next().expect("tsv json");
            let d = parse_vm_descriptor2(json)
                .unwrap_or_else(|e| panic!("v3 registry {key} failed parse_vm_descriptor2: {e}"));
            assert_eq!(
                d.trace_width,
                V1_WIDTH + APPENDIX_SPAN,
                "{key}: rotated trace width = v1 width + appendix"
            );
            assert!(
                d.hash_sites.is_empty() && d.ranges.is_empty(),
                "{key}: graduated carriers only"
            );

            // The three appendix blocks, at fixed bases past the v1 layout.
            let before_base = V1_WIDTH;
            let after_base = V1_WIDTH + B_SPAN;
            let caveat_base = V1_WIDTH + 2 * B_SPAN;

            // A "fresh limb" of the appendix is a column inside one of the three blocks'
            // LIMB ranges (before/after rotated limbs 0..=iroot, or the caveat manifest
            // 0..MANIFEST_SIZE) — NOT a chain-carrier column (those ride the accumulator as
            // inputs but are not absorbed data). We audit only appendix sites (digest >=
            // V1_WIDTH); the v1 descriptor's own chip lookups absorb columns < V1_WIDTH.
            let is_limb = |v: usize| -> bool {
                (before_base..=before_base + rot.iroot).contains(&v)
                    || (after_base..=after_base + rot.iroot).contains(&v)
                    || (caveat_base..caveat_base + cav::MANIFEST_SIZE).contains(&v)
            };
            let mut digests: Vec<usize> = Vec::new();
            let mut absorbed: Vec<usize> = Vec::new();
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
                    let (digest, inputs) = vars.split_last().expect("chip tuple has a digest");
                    if *digest >= V1_WIDTH {
                        digests.push(*digest);
                        for v in inputs {
                            if is_limb(*v) {
                                absorbed.push(*v);
                            }
                        }
                    }
                }
            }

            // Expected fresh absorption: before-block limbs 0..=iroot, after-block limbs,
            // then the caveat manifest 0..MANIFEST_SIZE — all relative to their bases.
            let mut expected_absorbed: Vec<usize> = Vec::new();
            expected_absorbed.extend((0..=rot.iroot).map(|i| before_base + i));
            expected_absorbed.extend((0..=rot.iroot).map(|i| after_base + i));
            expected_absorbed.extend((0..cav::MANIFEST_SIZE).map(|i| caveat_base + i));
            assert_eq!(
                absorbed, expected_absorbed,
                "{key}: appendix must absorb the BEFORE block, the AFTER block, then the \
                 29-felt caveat manifest, each limb exactly once in absorption order"
            );

            // Expected digest carriers: before chain → before state_commit; after chain →
            // after state_commit; caveat chain → caveat commit.
            let mut expected_digests: Vec<usize> = Vec::new();
            expected_digests.extend((0..rot.num_chain).map(|k| before_base + rot.chain_base + k));
            expected_digests.push(before_base + B_STATE_COMMIT);
            expected_digests.extend((0..rot.num_chain).map(|k| after_base + rot.chain_base + k));
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

            // The four appended PI pins live at the descriptor's OWN piCount..piCount+3,
            // bound to: first-row before state_commit, last-row after state_commit,
            // last-row after committed_height, last-row caveat commit.
            let pi_base = d.public_input_count - 4;
            let mut pins: Vec<(usize, usize)> = Vec::new(); // (col, pi_index)
            for c in &d.constraints {
                if let VmConstraint2::Base(VmConstraint::PiBinding { col, pi_index, .. }) = c {
                    if *pi_index >= pi_base {
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
        }
        assert_eq!(n, 26, "expected the full 26-member cohort");
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
}
