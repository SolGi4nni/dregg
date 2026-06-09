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
//! 47 UNIQUE descriptors are registered. The `attenuateA` cap-root-move object is
//! now SHARED by only 3 emit entries — attenuate / delegate / delegateAtten —
//! since the CUTOVER NONCE-TICK RECONCILE gave `revokeDelegation` (sel 30) and
//! `introduce` (sel 35) their OWN frozen-frame + nonce-TICK descriptors
//! (`revokeDelegation-v2` / `introduce-v2`): the runtime hand-AIR runs them as
//! state-PASSTHROUGH rows (it FREEZES `cap_root`; the cap-table move rides
//! `effects_hash` OFF-row), so the prior `attenuateA` cap-MOVE descriptor was wrong
//! for them (it "passed" only by the cap_root=param2=0 fixture accident). The
//! cap-table semantics are bound OFF-row via each module's universe-A connector.
//! Of the `attenuateA` users, two bind a Rust selector (ATTENUATE_CAPABILITY=48,
//! GRANT_CAP=3 via delegate); delegateAtten has no distinct selector.
//!
//!   * `SELECTOR_DESCRIPTORS`: 44 of the 54 EffectVM selectors carry a descriptor
//!     (the 10 others — NOOP, SET_FIELD, the obligation family, CUSTOM, SLASH,
//!     REVOKE_CAPABILITY, the committed-escrow release/refund, CELL_UNSEAL — have
//!     no emit module yet). Two selectors (3/48 cap moves) point at the shared
//!     `attenuateA` JSON, so the 44 selector rows reference 43 distinct descriptor
//!     names.
//!
//!   * `NAME_ONLY_DESCRIPTORS`: 3 verified descriptors (`mint`, `swissDropA`,
//!     `swissHandoffA`) whose effect has NO dedicated Rust selector in the current
//!     `sel::` enum — they are real, registered by name, but not yet selectable by
//!     index (the cutover step that adds their selectors will move them up).
//!     (The RECORD-LAYER STAGE 2 `record` descriptor is registered in
//!     `ALL_DESCRIPTORS` directly — it is the transfer descriptor's `fields_root`-
//!     binding variant, selected by name on a map-write row, not a new selector.)
//!
//! ## PARTIAL / IR-BLOCKED descriptors (registered honestly)
//!
//! Several descriptors are the **economic-leg only** projection of an effect whose
//! full semantics touch an off-trace side-table the per-row EffectVM IR can't yet
//! re-derive (the Lean module headers flag this as "IR-BLOCKED" / "the per-row IR
//! STOPS here"). They are registered because the leg they DO emit is verified, and
//! the registry is honest about the gap. Known-partial: the cap-root-move family
//! (`attenuateA`, used by delegate/revoke/introduce — `cap_root` is a scalar
//! digest of the cap-table FUNCTION the IR can't unfold), the swiss-table family
//! (`swissDropA`/`swissHandoffA`/`swissExportA`/`enlivenRefA`/`dropRefA` — scalar
//! `swiss_root` digest moves), and the passthrough-with-hash effects
//! (`setPermissionsA`/`setVK`/`refreshDelegation`/`emitEvent`/the bridge/escrow
//! finalize-record variants — state passthrough + an `effects_hash` binding whose
//! preimage lives off-trace). The transfer/burn/mint/note descriptors are FULL
//! economic-state descriptors (balance limb move + frame freeze + GROUP-4 commit).
//!
//! ## DO NOT hand-edit
//!
//! The const block and the tables below are generated from the Lean emit. To
//! refresh: re-run `EmitAllJson.lean`, rewrite `circuit/descriptors/*.json`,
//! recompute the `*_FP` SHA-256s, and regenerate this block. The drift test will
//! reject any inconsistency.

use crate::lean_descriptor_air::parse_vm_descriptor;

// ==== include_str! consts + sha256 fingerprints (auto-generated; do not hand-edit) ====
pub const DREGG_EFFECTVM_ATTENUATEA_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-attenuateA-v1.json");
pub const DREGG_EFFECTVM_ATTENUATEA_V1_FP: &str = "c9132246c00ed71bc4f297803e631b849fa2e9ee2c481e543d4d4e3a9c5a97e0";
pub const DREGG_EFFECTVM_BRIDGECANCEL_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-bridgecancel-v1.json");
pub const DREGG_EFFECTVM_BRIDGECANCEL_V1_FP: &str = "acfb87fed619fef91f7f0cc3cc03181c2c9e398a3cf18dbfe34ab75bc6b57155";
// bridgeFinalize GRADUATED into the cutover (nonce-tick reconcile): the Lean emit module
// `EffectVmEmitBridgeFinalize` ticks the runtime nonce (`gNonce`). The prior JSON body froze the
// nonce (made the honest trace UNSAT). Name unchanged (`-v1`); body + fingerprint updated.
pub const DREGG_EFFECTVM_BRIDGEFINALIZE_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-bridgefinalize-v1.json");
pub const DREGG_EFFECTVM_BRIDGEFINALIZE_V1_FP: &str = "646486490a468ef57d77146591e2ed6d88f2a557b81636fb623627e82b599306";
pub const DREGG_EFFECTVM_BRIDGELOCK_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-bridgelock-v1.json");
pub const DREGG_EFFECTVM_BRIDGELOCK_V1_FP: &str = "16d0afc4afd206d4c9fd91c1f4d4b84ef688518b5bdee851460f6f1736432b74";
pub const DREGG_EFFECTVM_BRIDGEMINT_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-bridgemint-v1.json");
pub const DREGG_EFFECTVM_BRIDGEMINT_V1_FP: &str = "fce2cb4ce9685f8b322a075ded2896d5c39378242d2e8da0e7f8650d0cf35872";
pub const DREGG_EFFECTVM_BURN_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-burn-v1.json");
pub const DREGG_EFFECTVM_BURN_V1_FP: &str = "3c49af13cae8285f136b8cdf06632a76bd2f5c0c3a156eba3275254d3fbd5d50";
// GRADUATED (nonce-tick reconcile, v2): frozen-balance + ticked-nonce effect; the Lean descriptor
// now ticks the runtime nonce (`gNonce`) AND carries the full last-row balance PI binding
// (`boundaryLastPins`), so the descriptor decides IDENTICALLY to the hand-AIR on the real witness
// (honest accept + forged-balance/forged-state-commit reject). Body STRUCTURALLY IDENTICAL to the
// validated `createsealpair-v2` (only the `name` differs). Name bumped `-v1`→`-v2`; FP updated.
pub const DREGG_EFFECTVM_CELLDESTROY_V2_JSON: &str = include_str!("../descriptors/dregg-effectvm-celldestroy-v2.json");
pub const DREGG_EFFECTVM_CELLDESTROY_V2_FP: &str = "9630d7317d3f21c659e6b8566f97e63ef2c3b71869d99b7bddb2f85431558f65";
pub const DREGG_EFFECTVM_CELLSEAL_V2_JSON: &str = include_str!("../descriptors/dregg-effectvm-cellseal-v2.json");
pub const DREGG_EFFECTVM_CELLSEAL_V2_FP: &str = "a3809a09772bf80225b4f35050e9dc861c1d53b0db3f13b06fb6cd7d622e9b91";
pub const DREGG_EFFECTVM_CREATECELL_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-createcell-v1.json");
pub const DREGG_EFFECTVM_CREATECELL_V1_FP: &str = "6748d54ecad55f8190ff064c97766845297d9dfe7a2244089fe69a7a2a7fcfa3";
pub const DREGG_EFFECTVM_CREATECELLFROMFACTORY_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-createcellfromfactory-v1.json");
pub const DREGG_EFFECTVM_CREATECELLFROMFACTORY_V1_FP: &str = "5955a93092695bed0d410de4bea35016f95d1839ec2677e520d967ebba8ca98f";
pub const DREGG_EFFECTVM_CREATECOMMITTEDESCROW_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-createcommittedescrow-v1.json");
pub const DREGG_EFFECTVM_CREATECOMMITTEDESCROW_V1_FP: &str = "963a4b07617d0d787950183770e1acceac12f502136f1ca2474851eb43c0c66a";
pub const DREGG_EFFECTVM_CREATEESCROW_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-createescrow-v1.json");
pub const DREGG_EFFECTVM_CREATEESCROW_V1_FP: &str = "41198cc4252aa87c0a104722b5aae2299cc4843461ea0d60bb16a1446b4abdd1";
// createSealPair GRADUATED into the cutover (nonce-tick reconcile): the Lean emit module
// `EffectVmEmitCreateSealPair` ticks the runtime nonce (`gNonce`), renamed to `-v2`. The prior
// `-v1` JSON froze the nonce (the `exec_nonce_is_frozen_not_ticked` cutover bug) and made the
// honest trace UNSAT under the descriptor.
pub const DREGG_EFFECTVM_CREATESEALPAIR_V2_JSON: &str = include_str!("../descriptors/dregg-effectvm-createsealpair-v2.json");
pub const DREGG_EFFECTVM_CREATESEALPAIR_V2_FP: &str = "641929a552046fd6ea2455b10ea4c4e0d11d7709a237252dfcd9187bf119f1b7";
pub const DREGG_EFFECTVM_DROPREFA_V2_JSON: &str = include_str!("../descriptors/dregg-effectvm-dropRefA-v2.json");
pub const DREGG_EFFECTVM_DROPREFA_V2_FP: &str = "3daa5525aa9a4accef64e8cdbec2a13ed85cb7f7fe2abe9468acb19ce64b8c32";
pub const DREGG_EFFECTVM_EMITEVENT_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-emitEvent-v1.json");
pub const DREGG_EFFECTVM_EMITEVENT_V1_FP: &str = "1ed2b76564fc123f7968cfb75d8a89f85485585cabecd389ce4948dd2def6480";
pub const DREGG_EFFECTVM_ENLIVENREFA_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-enlivenRefA-v1.json");
pub const DREGG_EFFECTVM_ENLIVENREFA_V1_FP: &str = "61920ca6cce36632eddffcf03f16c5a82cd1dd6c62e17bcef38f6b21854da6cc";
// GRADUATED (nonce-tick + last-row PI pins, v2): the Lean emit module was reconciled onto the runtime
// Stage-3 passthrough batch (whole economic block frozen, nonce ticks via `gNonce`) AND grew the
// `boundaryLastPins` last-row balance PI binding. Body STRUCTURALLY IDENTICAL to the validated
// `createsealpair-v2`; the JSON had not been re-emitted. Name `-v1`→`-v2`; FP updated.
pub const DREGG_EFFECTVM_EXERCISEA_HOLDLAYER_V2_JSON: &str = include_str!("../descriptors/dregg-effectvm-exerciseA-holdlayer-v2.json");
pub const DREGG_EFFECTVM_EXERCISEA_HOLDLAYER_V2_FP: &str = "0a01f957422c4ef75200ac138a6ccf3ac31ed6574adce88f377935e7a6f6a367";
// GRADUATED (nonce-tick + last-row PI pins, v2): the explicit nonce-only effect. The Lean module was
// reconciled to the runtime TICK (`new_state.nonce += 1`) via `gNonce` and grew `boundaryLastPins`,
// dropping the prior param-bound nonce gate; body STRUCTURALLY IDENTICAL to `createsealpair-v2`. The
// committed JSON was the stale param-bound v1. Name `-v1`→`-v2`; FP updated.
pub const DREGG_EFFECTVM_INCREMENTNONCE_V2_JSON: &str = include_str!("../descriptors/dregg-effectvm-incrementNonce-v2.json");
pub const DREGG_EFFECTVM_INCREMENTNONCE_V2_FP: &str = "85ca061301a6a634367313ec2f6e15ae52dcf2ebba24b8b7d8613fccb693190b";
pub const DREGG_EFFECTVM_MAKESOVEREIGN_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-makesovereign-v1.json");
pub const DREGG_EFFECTVM_MAKESOVEREIGN_V1_FP: &str = "9175f5d2a84f5d689ad8cfe70bf95f1fb881ea10fe25c00a83405a823b13f68a";
pub const DREGG_EFFECTVM_MINT_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-mint-v1.json");
pub const DREGG_EFFECTVM_MINT_V1_FP: &str = "afbf531ac2c17447f90764960691587f86b0b18ecd06d5425ed8e6ef1cfd2935";
pub const DREGG_EFFECTVM_NOTECREATE_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-notecreate-v1.json");
pub const DREGG_EFFECTVM_NOTECREATE_V1_FP: &str = "d323c2f0602c55bea80576e2d8d78c6f06eebd445dafd1345a68a2077e63f98d";
pub const DREGG_EFFECTVM_NOTESPEND_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-notespend-v1.json");
pub const DREGG_EFFECTVM_NOTESPEND_V1_FP: &str = "68f057ead33d6a66fe778eb8c2659e5d98d81ea0259cbb5a2c755caf24aa0cdb";
// GRADUATED (nonce-tick + last-row PI pins, v2): see exercise note. Body STRUCTURALLY IDENTICAL to
// `createsealpair-v2`. Name `-v1`→`-v2`; FP updated.
pub const DREGG_EFFECTVM_PIPELINEDSENDA_V2_JSON: &str = include_str!("../descriptors/dregg-effectvm-pipelinedSendA-v2.json");
pub const DREGG_EFFECTVM_PIPELINEDSENDA_V2_FP: &str = "56083a4facb4ff4f08f8eec97d369e0a0f24bb178414f45b168b70bd2a6817af";
pub const DREGG_EFFECTVM_QUEUEALLOCATE_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-queueallocate-v1.json");
pub const DREGG_EFFECTVM_QUEUEALLOCATE_V1_FP: &str = "f02e678678ff4de0390b974badf5028f1406dfc0656edbe23d67b55a86696fed";
pub const DREGG_EFFECTVM_QUEUEATOMICTX_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-queueatomictx-v1.json");
pub const DREGG_EFFECTVM_QUEUEATOMICTX_V1_FP: &str = "42b8bd50b9b5dfa40193f8ab9f752dd72e3e2031f2b96b7c98de672653612eb1";
pub const DREGG_EFFECTVM_QUEUEDEQUEUE_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-queuedequeue-v1.json");
pub const DREGG_EFFECTVM_QUEUEDEQUEUE_V1_FP: &str = "e313f3018adb25dc1a44d210bb5a9f49b11fb187b264441ab0b8ed4541631479";
pub const DREGG_EFFECTVM_QUEUEENQUEUE_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-queueenqueue-v1.json");
pub const DREGG_EFFECTVM_QUEUEENQUEUE_V1_FP: &str = "2d5effcd5480a4a18edede751e8bad3be85eb627f69bce35ea7447cdb88edb66";
pub const DREGG_EFFECTVM_QUEUEPIPELINESTEP_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-queuepipelinestep-v1.json");
pub const DREGG_EFFECTVM_QUEUEPIPELINESTEP_V1_FP: &str = "0dc0d7e21d7b05a023032a723f550cd2c755e669215d512f8e05b967211ee527";
pub const DREGG_EFFECTVM_QUEUERESIZE_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-queueresize-v1.json");
pub const DREGG_EFFECTVM_QUEUERESIZE_V1_FP: &str = "706bfc6e1050fddf124e7acbedb46d29cf9cea1daa54d167bd8923fba661a6a2";
pub const DREGG_EFFECTVM_RECEIPTARCHIVEA_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-receiptArchiveA-v1.json");
pub const DREGG_EFFECTVM_RECEIPTARCHIVEA_V1_FP: &str = "f79fdc4aa4bda0a1801c0808ad83391fa320c8aa5497bfac11e425050eaaf1d5";
// GRADUATED (nonce-tick + last-row PI pins, v2): refreshDelegation already ticked the runtime nonce
// (`gNonce`) but the committed JSON carried only `boundaryFirstPins` (anti-ghost WEAK: the forged
// last-row balance tooth did not bite). The Lean module grew `boundaryLastPins` + the 2 balance ranges.
// Name `-v1`→`-v2`; FP updated.
pub const DREGG_EFFECTVM_REFRESHDELEGATION_V2_JSON: &str = include_str!("../descriptors/dregg-effectvm-refreshDelegation-v2.json");
pub const DREGG_EFFECTVM_REFRESHDELEGATION_V2_FP: &str = "ad6b56c715fd9d4dd269ea5739281a60011aa4da967af865cd147f06a8c08be5";
// GRADUATED (nonce-tick + last-row PI pins, v2): revokeDelegation was PRE-v2 pointed at the
// `attenuateA` cap-root-MOVE descriptor, which the runtime hand-AIR does NOT enforce on a revoke row
// (it FREEZES `cap_root`); it "passed" only by fixture accident (cap_root = param2 = 0). The v2 Lean
// module emits the runtime frozen-frame + nonce-TICK directly; the cap-table edge removal is bound
// OFF-row via the universe-A connector. Body STRUCTURALLY IDENTICAL to `createsealpair-v2`.
pub const DREGG_EFFECTVM_REVOKEDELEGATION_V2_JSON: &str = include_str!("../descriptors/dregg-effectvm-revokeDelegation-v2.json");
pub const DREGG_EFFECTVM_REVOKEDELEGATION_V2_FP: &str = "854fd94989861477bba0c811fe895ade347a22f88ce66c7ae074a173f223343a";
// GRADUATED (nonce-tick + last-row PI pins, v2): introduce, same reconcile as revokeDelegation (was
// PRE-v2 pointed at `attenuateA`). The cap-table grant is bound OFF-row via the universe-A connector.
pub const DREGG_EFFECTVM_INTRODUCE_V2_JSON: &str = include_str!("../descriptors/dregg-effectvm-introduce-v2.json");
pub const DREGG_EFFECTVM_INTRODUCE_V2_FP: &str = "e1050c3cd4b2456190ba2ebf2868771de31d143c3e9a4da8786a43e6df94d89f";
pub const DREGG_EFFECTVM_REFUNDESCROW_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-refundescrow-v1.json");
pub const DREGG_EFFECTVM_REFUNDESCROW_V1_FP: &str = "370d7c3874235c88b7162d1386fa36067a7516c3ae95b31d34fa7aeec31f4162";
// GRADUATED (nonce-tick reconcile, v2): see celldestroy/cellseal note. Body STRUCTURALLY IDENTICAL
// to `createsealpair-v2`. Name bumped `-v1`→`-v2`; FP updated.
pub const DREGG_EFFECTVM_REFUSAL_V2_JSON: &str = include_str!("../descriptors/dregg-effectvm-refusal-v2.json");
pub const DREGG_EFFECTVM_REFUSAL_V2_FP: &str = "519d878769bf55262470e89d55b1a846e4db0c015b2e8bbbdcd1796c0fa699c8";
pub const DREGG_EFFECTVM_RELEASEESCROW_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-releaseescrow-v1.json");
pub const DREGG_EFFECTVM_RELEASEESCROW_V1_FP: &str = "6f0795ddbcafd92c396a5e577f9734eb74aff5f72be631375a84869595177bc8";
pub const DREGG_EFFECTVM_SEAL_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-seal-v1.json");
pub const DREGG_EFFECTVM_SEAL_V1_FP: &str = "6f1ffd64fa01eae2db238e525663ceb65dbd2293507d5af1cc63f6fc2911da81";
// GRADUATED (nonce-tick + last-row PI pins, v2): see exercise note. Body STRUCTURALLY IDENTICAL to
// `createsealpair-v2`. Name `-v1`→`-v2`; FP updated.
pub const DREGG_EFFECTVM_SETPERMISSIONSA_V2_JSON: &str = include_str!("../descriptors/dregg-effectvm-setPermissionsA-v2.json");
pub const DREGG_EFFECTVM_SETPERMISSIONSA_V2_FP: &str = "f988c68ab91e611e5c5d8190396c85dfdcdf9c14703172fb3218dc140571a4e9";
pub const DREGG_EFFECTVM_SETVK_V2_JSON: &str = include_str!("../descriptors/dregg-effectvm-setVK-v2.json");
pub const DREGG_EFFECTVM_SETVK_V2_FP: &str = "baf0e80f132bfa9ed8e0a6f210655052472df520d8d76c23873ec1561d660628";
pub const DREGG_EFFECTVM_SPAWNA_V2QUINT_CHILDCELL_JSON: &str = include_str!("../descriptors/dregg-effectvm-spawnA-v2quint-childcell.json");
pub const DREGG_EFFECTVM_SPAWNA_V2QUINT_CHILDCELL_FP: &str = "81b11945d4c56422bcfc06e2eda41d5c88b13f54535d72bbd5799d9506445a65";
pub const DREGG_EFFECTVM_SWISSDROPA_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-swissDropA-v1.json");
pub const DREGG_EFFECTVM_SWISSDROPA_V1_FP: &str = "8bc84b33c605643f10ad1e050685ce9a94992bed0571d61a510f5dc75f3b7990";
pub const DREGG_EFFECTVM_SWISSEXPORTA_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-swissExportA-v1.json");
pub const DREGG_EFFECTVM_SWISSEXPORTA_V1_FP: &str = "5fe467e4bc9f4b33536beced2a16362cbe9a6b642a69e4d8a995d4cdaafa7ff3";
pub const DREGG_EFFECTVM_SWISSHANDOFFA_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-swissHandoffA-v1.json");
pub const DREGG_EFFECTVM_SWISSHANDOFFA_V1_FP: &str = "6703274e8ef64e24afbf67093175472cb8bc1266ee6f5a7678848fecc4e45b34";
pub const DREGG_EFFECTVM_TRANSFER_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-transfer-v1.json");
pub const DREGG_EFFECTVM_TRANSFER_V1_FP: &str = "34ce263778bbbd209abe2e8a44af4ff492e2570f5aab55362c5fd219184b66df";
// RECORD-LAYER STAGE 2 (`_RECORD-LAYER-UPGRADE.md` §B.5/§E Stage 2): the transfer descriptor with
// GROUP-4 site 3's previously-spare 4th input ({"t":"zero"}) replaced by the `fields_root` carrier
// cell (col 89 = state_after.FIELDS_ROOT = the RESERVED slot), absorbing the user-field-map root into
// `state_commit`. Width-neutral (186); constraints/ranges/sites 0..2 byte-identical to transfer.
// Verified by construction in `Dregg2.Circuit.Emit.EffectVmEmitRecordRoot` (anti-ghost:
// `recordDescriptor_commit_binds_fieldsRoot`).
pub const DREGG_EFFECTVM_RECORD_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-record-v1.json");
pub const DREGG_EFFECTVM_RECORD_V1_FP: &str = "295c53af8da86b299aeb507e76796c2711202175a0086250b8185b88bf2793da";
pub const DREGG_EFFECTVM_UNSEAL_V1_JSON: &str = include_str!("../descriptors/dregg-effectvm-unseal-v1.json");
pub const DREGG_EFFECTVM_UNSEAL_V1_FP: &str = "f7ce0ac00c4721a0c8940cb45dd0744878e6fabaaa11c7d894cc5c6cd4fce11f";
pub const DREGG_EFFECTVM_VALIDATEHANDOFFA_V2_JSON: &str = include_str!("../descriptors/dregg-effectvm-validateHandoffA-v2.json");
pub const DREGG_EFFECTVM_VALIDATEHANDOFFA_V2_FP: &str = "295e4e1c49423ac647102c6040d040eb4522952fc0f832e8ec43eaa30c102077";

// ==== selector index -> (descriptor name, const json, fingerprint) ====
pub const SELECTOR_DESCRIPTORS: &[(usize, &str, &str, &str)] = &[
    (1, "dregg-effectvm-transfer-v1", DREGG_EFFECTVM_TRANSFER_V1_JSON, DREGG_EFFECTVM_TRANSFER_V1_FP), // TRANSFER: transferVmDescriptor
    (3, "dregg-effectvm-attenuateA-v1", DREGG_EFFECTVM_ATTENUATEA_V1_JSON, DREGG_EFFECTVM_ATTENUATEA_V1_FP), // GRANT_CAP: delegateVmDescriptor (unattenuated cap-root grant = attenuate template)
    (4, "dregg-effectvm-notespend-v1", DREGG_EFFECTVM_NOTESPEND_V1_JSON, DREGG_EFFECTVM_NOTESPEND_V1_FP), // NOTE_SPEND: noteSpendVmDescriptor
    (5, "dregg-effectvm-notecreate-v1", DREGG_EFFECTVM_NOTECREATE_V1_JSON, DREGG_EFFECTVM_NOTECREATE_V1_FP), // NOTE_CREATE: noteCreateVmDescriptor
    (10, "dregg-effectvm-seal-v1", DREGG_EFFECTVM_SEAL_V1_JSON, DREGG_EFFECTVM_SEAL_V1_FP), // SEAL: sealVmDescriptor
    (11, "dregg-effectvm-unseal-v1", DREGG_EFFECTVM_UNSEAL_V1_JSON, DREGG_EFFECTVM_UNSEAL_V1_FP), // UNSEAL: unsealVmDescriptor
    (12, "dregg-effectvm-makesovereign-v1", DREGG_EFFECTVM_MAKESOVEREIGN_V1_JSON, DREGG_EFFECTVM_MAKESOVEREIGN_V1_FP), // MAKE_SOVEREIGN: makeSovereignVmDescriptor
    (13, "dregg-effectvm-createcellfromfactory-v1", DREGG_EFFECTVM_CREATECELLFROMFACTORY_V1_JSON, DREGG_EFFECTVM_CREATECELLFROMFACTORY_V1_FP), // CREATE_CELL_FROM_FACTORY: factoryVmDescriptor
    (14, "dregg-effectvm-swissExportA-v1", DREGG_EFFECTVM_SWISSEXPORTA_V1_JSON, DREGG_EFFECTVM_SWISSEXPORTA_V1_FP), // EXPORT_STURDY_REF: swissExportVmDescriptor
    (15, "dregg-effectvm-enlivenRefA-v1", DREGG_EFFECTVM_ENLIVENREFA_V1_JSON, DREGG_EFFECTVM_ENLIVENREFA_V1_FP), // ENLIVEN_REF: enlivenVmDescriptor
    (16, "dregg-effectvm-dropRefA-v2", DREGG_EFFECTVM_DROPREFA_V2_JSON, DREGG_EFFECTVM_DROPREFA_V2_FP), // DROP_REF: dropRefVmDescriptor
    (17, "dregg-effectvm-validateHandoffA-v2", DREGG_EFFECTVM_VALIDATEHANDOFFA_V2_JSON, DREGG_EFFECTVM_VALIDATEHANDOFFA_V2_FP), // VALIDATE_HANDOFF: validateHandoffVmDescriptor
    (18, "dregg-effectvm-queueallocate-v1", DREGG_EFFECTVM_QUEUEALLOCATE_V1_JSON, DREGG_EFFECTVM_QUEUEALLOCATE_V1_FP), // ALLOCATE_QUEUE: queueAllocateVmDescriptor
    (19, "dregg-effectvm-queueenqueue-v1", DREGG_EFFECTVM_QUEUEENQUEUE_V1_JSON, DREGG_EFFECTVM_QUEUEENQUEUE_V1_FP), // ENQUEUE_MESSAGE: queueEnqueueVmDescriptor
    (20, "dregg-effectvm-queuedequeue-v1", DREGG_EFFECTVM_QUEUEDEQUEUE_V1_JSON, DREGG_EFFECTVM_QUEUEDEQUEUE_V1_FP), // DEQUEUE_MESSAGE: queueDequeueVmDescriptor
    (21, "dregg-effectvm-queueresize-v1", DREGG_EFFECTVM_QUEUERESIZE_V1_JSON, DREGG_EFFECTVM_QUEUERESIZE_V1_FP), // RESIZE_QUEUE: queueResizeVmDescriptor
    (22, "dregg-effectvm-queueatomictx-v1", DREGG_EFFECTVM_QUEUEATOMICTX_V1_JSON, DREGG_EFFECTVM_QUEUEATOMICTX_V1_FP), // ATOMIC_QUEUE_TX: queueAtomicVmDescriptor
    (23, "dregg-effectvm-queuepipelinestep-v1", DREGG_EFFECTVM_QUEUEPIPELINESTEP_V1_JSON, DREGG_EFFECTVM_QUEUEPIPELINESTEP_V1_FP), // PIPELINE_STEP: queuePipelineVmDescriptor
    (25, "dregg-effectvm-emitEvent-v1", DREGG_EFFECTVM_EMITEVENT_V1_JSON, DREGG_EFFECTVM_EMITEVENT_V1_FP), // EMIT_EVENT: emitEventVmDescriptor
    (26, "dregg-effectvm-setPermissionsA-v2", DREGG_EFFECTVM_SETPERMISSIONSA_V2_JSON, DREGG_EFFECTVM_SETPERMISSIONSA_V2_FP), // SET_PERMISSIONS: setPermsVmDescriptor (GRADUATED: nonce-tick + last-row PI pins)
    (27, "dregg-effectvm-setVK-v2", DREGG_EFFECTVM_SETVK_V2_JSON, DREGG_EFFECTVM_SETVK_V2_FP), // SET_VERIFICATION_KEY: setVKVmDescriptor (GRADUATED: nonce-tick + last-row PI pins)
    (28, "dregg-effectvm-createsealpair-v2", DREGG_EFFECTVM_CREATESEALPAIR_V2_JSON, DREGG_EFFECTVM_CREATESEALPAIR_V2_FP), // CREATE_SEAL_PAIR: createSealPairVmDescriptor (GRADUATED: nonce-tick)
    (29, "dregg-effectvm-refreshDelegation-v2", DREGG_EFFECTVM_REFRESHDELEGATION_V2_JSON, DREGG_EFFECTVM_REFRESHDELEGATION_V2_FP), // REFRESH_DELEGATION: refreshVmDescriptor (GRADUATED: nonce-tick + last-row PI pins)
    (30, "dregg-effectvm-revokeDelegation-v2", DREGG_EFFECTVM_REVOKEDELEGATION_V2_JSON, DREGG_EFFECTVM_REVOKEDELEGATION_V2_FP), // REVOKE_DELEGATION: revokeVmDescriptor (GRADUATED: frozen-frame + nonce-tick; cap-table move OFF-row)
    (31, "dregg-effectvm-createcell-v1", DREGG_EFFECTVM_CREATECELL_V1_JSON, DREGG_EFFECTVM_CREATECELL_V1_FP), // CREATE_CELL: createCellVmDescriptor
    (32, "dregg-effectvm-spawnA-v2quint-childcell", DREGG_EFFECTVM_SPAWNA_V2QUINT_CHILDCELL_JSON, DREGG_EFFECTVM_SPAWNA_V2QUINT_CHILDCELL_FP), // SPAWN_WITH_DELEGATION: spawnVmDescriptor
    (33, "dregg-effectvm-bridgecancel-v1", DREGG_EFFECTVM_BRIDGECANCEL_V1_JSON, DREGG_EFFECTVM_BRIDGECANCEL_V1_FP), // BRIDGE_CANCEL: bridgeCancelVmDescriptor
    (34, "dregg-effectvm-exerciseA-holdlayer-v2", DREGG_EFFECTVM_EXERCISEA_HOLDLAYER_V2_JSON, DREGG_EFFECTVM_EXERCISEA_HOLDLAYER_V2_FP), // EXERCISE_VIA_CAPABILITY: exerciseVmDescriptor (GRADUATED: nonce-tick + last-row PI pins)
    (35, "dregg-effectvm-introduce-v2", DREGG_EFFECTVM_INTRODUCE_V2_JSON, DREGG_EFFECTVM_INTRODUCE_V2_FP), // INTRODUCE: introduceVmDescriptor (GRADUATED: frozen-frame + nonce-tick; cap-table grant OFF-row)
    (36, "dregg-effectvm-pipelinedSendA-v2", DREGG_EFFECTVM_PIPELINEDSENDA_V2_JSON, DREGG_EFFECTVM_PIPELINEDSENDA_V2_FP), // PIPELINED_SEND: pipelinedSendVmDescriptor (GRADUATED: nonce-tick + last-row PI pins)
    (37, "dregg-effectvm-createescrow-v1", DREGG_EFFECTVM_CREATEESCROW_V1_JSON, DREGG_EFFECTVM_CREATEESCROW_V1_FP), // CREATE_ESCROW: createEscrowVmDescriptor
    (38, "dregg-effectvm-bridgelock-v1", DREGG_EFFECTVM_BRIDGELOCK_V1_JSON, DREGG_EFFECTVM_BRIDGELOCK_V1_FP), // BRIDGE_LOCK: bridgeLockVmDescriptor
    (39, "dregg-effectvm-createcommittedescrow-v1", DREGG_EFFECTVM_CREATECOMMITTEDESCROW_V1_JSON, DREGG_EFFECTVM_CREATECOMMITTEDESCROW_V1_FP), // CREATE_COMMITTED_ESCROW: escrowCreateVmDescriptor
    (40, "dregg-effectvm-bridgemint-v1", DREGG_EFFECTVM_BRIDGEMINT_V1_JSON, DREGG_EFFECTVM_BRIDGEMINT_V1_FP), // BRIDGE_MINT: bridgeMintVmDescriptor
    (41, "dregg-effectvm-bridgefinalize-v1", DREGG_EFFECTVM_BRIDGEFINALIZE_V1_JSON, DREGG_EFFECTVM_BRIDGEFINALIZE_V1_FP), // BRIDGE_FINALIZE: bridgeFinalizeVmDescriptor
    (42, "dregg-effectvm-releaseescrow-v1", DREGG_EFFECTVM_RELEASEESCROW_V1_JSON, DREGG_EFFECTVM_RELEASEESCROW_V1_FP), // RELEASE_ESCROW: releaseEscrowVmDescriptor
    (43, "dregg-effectvm-refundescrow-v1", DREGG_EFFECTVM_REFUNDESCROW_V1_JSON, DREGG_EFFECTVM_REFUNDESCROW_V1_FP), // REFUND_ESCROW: refundEscrowVmDescriptor
    (46, "dregg-effectvm-burn-v1", DREGG_EFFECTVM_BURN_V1_JSON, DREGG_EFFECTVM_BURN_V1_FP), // BURN: burnVmDescriptor
    (47, "dregg-effectvm-celldestroy-v2", DREGG_EFFECTVM_CELLDESTROY_V2_JSON, DREGG_EFFECTVM_CELLDESTROY_V2_FP), // CELL_DESTROY: cellDestroyVmDescriptor (GRADUATED: nonce-tick + last-row PI pins)
    (48, "dregg-effectvm-attenuateA-v1", DREGG_EFFECTVM_ATTENUATEA_V1_JSON, DREGG_EFFECTVM_ATTENUATEA_V1_FP), // ATTENUATE_CAPABILITY: attenuateVmDescriptor (canonical cap-root move)
    (49, "dregg-effectvm-cellseal-v2", DREGG_EFFECTVM_CELLSEAL_V2_JSON, DREGG_EFFECTVM_CELLSEAL_V2_FP), // CELL_SEAL: cellSealVmDescriptor (GRADUATED: nonce-tick + last-row PI pins)
    (51, "dregg-effectvm-receiptArchiveA-v1", DREGG_EFFECTVM_RECEIPTARCHIVEA_V1_JSON, DREGG_EFFECTVM_RECEIPTARCHIVEA_V1_FP), // RECEIPT_ARCHIVE: receiptArchiveVmDescriptor
    (52, "dregg-effectvm-refusal-v2", DREGG_EFFECTVM_REFUSAL_V2_JSON, DREGG_EFFECTVM_REFUSAL_V2_FP), // REFUSAL: refusalVmDescriptor (GRADUATED: nonce-tick + last-row PI pins)
    (53, "dregg-effectvm-incrementNonce-v2", DREGG_EFFECTVM_INCREMENTNONCE_V2_JSON, DREGG_EFFECTVM_INCREMENTNONCE_V2_FP), // INCREMENT_NONCE: incrementNonceVmDescriptor (GRADUATED: nonce-tick + last-row PI pins)
];

// ==== name-only descriptors (verified, but no dedicated Rust selector slot yet) ====
pub const NAME_ONLY_DESCRIPTORS: &[(&str, &str, &str)] = &[
    ("dregg-effectvm-mint-v1", DREGG_EFFECTVM_MINT_V1_JSON, DREGG_EFFECTVM_MINT_V1_FP), // mintVmDescriptor: supply MINT (balance credit); no dedicated EffectVM sel (distinct from BRIDGE_MINT)
    ("dregg-effectvm-swissDropA-v1", DREGG_EFFECTVM_SWISSDROPA_V1_JSON, DREGG_EFFECTVM_SWISSDROPA_V1_FP), // swissDropVmDescriptor: CapTP swiss-table refcount-decrement; distinct from DROP_REF GC
    ("dregg-effectvm-swissHandoffA-v1", DREGG_EFFECTVM_SWISSHANDOFFA_V1_JSON, DREGG_EFFECTVM_SWISSHANDOFFA_V1_FP), // swissHandoffVmDescriptor: CapTP swiss-table cert-bind/refcount-bump; distinct from VALIDATE_HANDOFF
];

// ==== ALL unique descriptors (name -> json, fingerprint): the total name registry ====
pub const ALL_DESCRIPTORS: &[(&str, &str, &str)] = &[
    ("dregg-effectvm-attenuateA-v1", DREGG_EFFECTVM_ATTENUATEA_V1_JSON, DREGG_EFFECTVM_ATTENUATEA_V1_FP),
    ("dregg-effectvm-bridgecancel-v1", DREGG_EFFECTVM_BRIDGECANCEL_V1_JSON, DREGG_EFFECTVM_BRIDGECANCEL_V1_FP),
    ("dregg-effectvm-bridgefinalize-v1", DREGG_EFFECTVM_BRIDGEFINALIZE_V1_JSON, DREGG_EFFECTVM_BRIDGEFINALIZE_V1_FP),
    ("dregg-effectvm-bridgelock-v1", DREGG_EFFECTVM_BRIDGELOCK_V1_JSON, DREGG_EFFECTVM_BRIDGELOCK_V1_FP),
    ("dregg-effectvm-bridgemint-v1", DREGG_EFFECTVM_BRIDGEMINT_V1_JSON, DREGG_EFFECTVM_BRIDGEMINT_V1_FP),
    ("dregg-effectvm-burn-v1", DREGG_EFFECTVM_BURN_V1_JSON, DREGG_EFFECTVM_BURN_V1_FP),
    ("dregg-effectvm-celldestroy-v2", DREGG_EFFECTVM_CELLDESTROY_V2_JSON, DREGG_EFFECTVM_CELLDESTROY_V2_FP),
    ("dregg-effectvm-cellseal-v2", DREGG_EFFECTVM_CELLSEAL_V2_JSON, DREGG_EFFECTVM_CELLSEAL_V2_FP),
    ("dregg-effectvm-createcell-v1", DREGG_EFFECTVM_CREATECELL_V1_JSON, DREGG_EFFECTVM_CREATECELL_V1_FP),
    ("dregg-effectvm-createcellfromfactory-v1", DREGG_EFFECTVM_CREATECELLFROMFACTORY_V1_JSON, DREGG_EFFECTVM_CREATECELLFROMFACTORY_V1_FP),
    ("dregg-effectvm-createcommittedescrow-v1", DREGG_EFFECTVM_CREATECOMMITTEDESCROW_V1_JSON, DREGG_EFFECTVM_CREATECOMMITTEDESCROW_V1_FP),
    ("dregg-effectvm-createescrow-v1", DREGG_EFFECTVM_CREATEESCROW_V1_JSON, DREGG_EFFECTVM_CREATEESCROW_V1_FP),
    ("dregg-effectvm-createsealpair-v2", DREGG_EFFECTVM_CREATESEALPAIR_V2_JSON, DREGG_EFFECTVM_CREATESEALPAIR_V2_FP),
    ("dregg-effectvm-dropRefA-v2", DREGG_EFFECTVM_DROPREFA_V2_JSON, DREGG_EFFECTVM_DROPREFA_V2_FP),
    ("dregg-effectvm-emitEvent-v1", DREGG_EFFECTVM_EMITEVENT_V1_JSON, DREGG_EFFECTVM_EMITEVENT_V1_FP),
    ("dregg-effectvm-enlivenRefA-v1", DREGG_EFFECTVM_ENLIVENREFA_V1_JSON, DREGG_EFFECTVM_ENLIVENREFA_V1_FP),
    ("dregg-effectvm-exerciseA-holdlayer-v2", DREGG_EFFECTVM_EXERCISEA_HOLDLAYER_V2_JSON, DREGG_EFFECTVM_EXERCISEA_HOLDLAYER_V2_FP),
    ("dregg-effectvm-incrementNonce-v2", DREGG_EFFECTVM_INCREMENTNONCE_V2_JSON, DREGG_EFFECTVM_INCREMENTNONCE_V2_FP),
    ("dregg-effectvm-makesovereign-v1", DREGG_EFFECTVM_MAKESOVEREIGN_V1_JSON, DREGG_EFFECTVM_MAKESOVEREIGN_V1_FP),
    ("dregg-effectvm-mint-v1", DREGG_EFFECTVM_MINT_V1_JSON, DREGG_EFFECTVM_MINT_V1_FP),
    ("dregg-effectvm-notecreate-v1", DREGG_EFFECTVM_NOTECREATE_V1_JSON, DREGG_EFFECTVM_NOTECREATE_V1_FP),
    ("dregg-effectvm-notespend-v1", DREGG_EFFECTVM_NOTESPEND_V1_JSON, DREGG_EFFECTVM_NOTESPEND_V1_FP),
    ("dregg-effectvm-pipelinedSendA-v2", DREGG_EFFECTVM_PIPELINEDSENDA_V2_JSON, DREGG_EFFECTVM_PIPELINEDSENDA_V2_FP),
    ("dregg-effectvm-queueallocate-v1", DREGG_EFFECTVM_QUEUEALLOCATE_V1_JSON, DREGG_EFFECTVM_QUEUEALLOCATE_V1_FP),
    ("dregg-effectvm-queueatomictx-v1", DREGG_EFFECTVM_QUEUEATOMICTX_V1_JSON, DREGG_EFFECTVM_QUEUEATOMICTX_V1_FP),
    ("dregg-effectvm-queuedequeue-v1", DREGG_EFFECTVM_QUEUEDEQUEUE_V1_JSON, DREGG_EFFECTVM_QUEUEDEQUEUE_V1_FP),
    ("dregg-effectvm-queueenqueue-v1", DREGG_EFFECTVM_QUEUEENQUEUE_V1_JSON, DREGG_EFFECTVM_QUEUEENQUEUE_V1_FP),
    ("dregg-effectvm-queuepipelinestep-v1", DREGG_EFFECTVM_QUEUEPIPELINESTEP_V1_JSON, DREGG_EFFECTVM_QUEUEPIPELINESTEP_V1_FP),
    ("dregg-effectvm-queueresize-v1", DREGG_EFFECTVM_QUEUERESIZE_V1_JSON, DREGG_EFFECTVM_QUEUERESIZE_V1_FP),
    ("dregg-effectvm-introduce-v2", DREGG_EFFECTVM_INTRODUCE_V2_JSON, DREGG_EFFECTVM_INTRODUCE_V2_FP),
    ("dregg-effectvm-receiptArchiveA-v1", DREGG_EFFECTVM_RECEIPTARCHIVEA_V1_JSON, DREGG_EFFECTVM_RECEIPTARCHIVEA_V1_FP),
    ("dregg-effectvm-refreshDelegation-v2", DREGG_EFFECTVM_REFRESHDELEGATION_V2_JSON, DREGG_EFFECTVM_REFRESHDELEGATION_V2_FP),
    ("dregg-effectvm-refundescrow-v1", DREGG_EFFECTVM_REFUNDESCROW_V1_JSON, DREGG_EFFECTVM_REFUNDESCROW_V1_FP),
    ("dregg-effectvm-refusal-v2", DREGG_EFFECTVM_REFUSAL_V2_JSON, DREGG_EFFECTVM_REFUSAL_V2_FP),
    ("dregg-effectvm-revokeDelegation-v2", DREGG_EFFECTVM_REVOKEDELEGATION_V2_JSON, DREGG_EFFECTVM_REVOKEDELEGATION_V2_FP),
    ("dregg-effectvm-releaseescrow-v1", DREGG_EFFECTVM_RELEASEESCROW_V1_JSON, DREGG_EFFECTVM_RELEASEESCROW_V1_FP),
    ("dregg-effectvm-seal-v1", DREGG_EFFECTVM_SEAL_V1_JSON, DREGG_EFFECTVM_SEAL_V1_FP),
    ("dregg-effectvm-setPermissionsA-v2", DREGG_EFFECTVM_SETPERMISSIONSA_V2_JSON, DREGG_EFFECTVM_SETPERMISSIONSA_V2_FP),
    ("dregg-effectvm-setVK-v2", DREGG_EFFECTVM_SETVK_V2_JSON, DREGG_EFFECTVM_SETVK_V2_FP),
    ("dregg-effectvm-spawnA-v2quint-childcell", DREGG_EFFECTVM_SPAWNA_V2QUINT_CHILDCELL_JSON, DREGG_EFFECTVM_SPAWNA_V2QUINT_CHILDCELL_FP),
    ("dregg-effectvm-swissDropA-v1", DREGG_EFFECTVM_SWISSDROPA_V1_JSON, DREGG_EFFECTVM_SWISSDROPA_V1_FP),
    ("dregg-effectvm-swissExportA-v1", DREGG_EFFECTVM_SWISSEXPORTA_V1_JSON, DREGG_EFFECTVM_SWISSEXPORTA_V1_FP),
    ("dregg-effectvm-swissHandoffA-v1", DREGG_EFFECTVM_SWISSHANDOFFA_V1_JSON, DREGG_EFFECTVM_SWISSHANDOFFA_V1_FP),
    ("dregg-effectvm-transfer-v1", DREGG_EFFECTVM_TRANSFER_V1_JSON, DREGG_EFFECTVM_TRANSFER_V1_FP),
    ("dregg-effectvm-unseal-v1", DREGG_EFFECTVM_UNSEAL_V1_JSON, DREGG_EFFECTVM_UNSEAL_V1_FP),
    ("dregg-effectvm-validateHandoffA-v2", DREGG_EFFECTVM_VALIDATEHANDOFFA_V2_JSON, DREGG_EFFECTVM_VALIDATEHANDOFFA_V2_FP),
    ("dregg-effectvm-record-v1", DREGG_EFFECTVM_RECORD_V1_JSON, DREGG_EFFECTVM_RECORD_V1_FP),
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


#[cfg(test)]
mod tests {
    use super::*;

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
        assert_eq!(ALL_DESCRIPTORS.len(), 47, "expected 47 unique descriptors");
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
            assert!(
                desc.trace_width > 0,
                "descriptor {name}: zero trace_width"
            );
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
        assert_eq!(descriptor_for_selector(crate::effect_vm::columns::sel::NOOP), None);
    }

    /// The name-only descriptors are real, distinct, and present in the total
    /// registry (they just lack a dedicated Rust selector slot).
    #[test]
    fn name_only_descriptors_present() {
        assert_eq!(NAME_ONLY_DESCRIPTORS.len(), 3);
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
}
