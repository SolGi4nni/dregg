# V1-DELETION RUNBOOK — PATH-PRESERVE Phase 5b (#103) + 5c, ordered to grep-zero

> **✅ DONE (2026-06-14): grep-zero LANDED.** The v1 effect-VM proof is removed from the `recursion`
> build (0 true live-under-recursion v1 refs across `circuit/src sdk/src turn/src node/src`). End-state
> is **FENCE-not-delete**: the v1 OLD-PROVER (`EffectVmAir` / `effect_vm_p3_full_air` / the SDK cutover /
> the executor secondary-verify arms / the v1 sovereign producer / the MCP demo tools) is retained
> `#[cfg(not(feature = "recursion"))]` for the v1 floor, with fail-closed `#[cfg(feature = "recursion")]`
> arms (no silent skip). DELETED outright (dead in both builds): the Silver joint surface
> (`JointParticipant`/`prove_joint_turn`/`verify_joint_turn`), `DescriptorForestNode`/
> `verify_descriptor_forest` (the last `EffectVmP3Proof` struct field), and the v1
> `BilateralAggregationAir`/`AggregationInnerRow`/`build_aggregation_trace` block. Bucket E/D STAYS
> (`generate_effect_vm_trace`, `EFFECT_VM_WIDTH`, `AIR_DESCRIPTOR`, `CUTOVER_READY_SELECTORS`,
> `EffectVmShapeAir`, `CrossSideExistenceAir`/`BundleTreeFoldAir`, the V2 bilateral). Bucket F was already
> landed (the rotated `DescriptorParticipant` is the recursion leaf). Two latent bugs were fixed in the
> same drive: (1) `dregg-node`/`dregg-verifier` had NO `recursion` feature (their `#[cfg(feature=
> "recursion")]` gates misaligned with the recursion-by-default circuit) — added one (default-on,
> forwarding to `dregg-circuit/recursion`); (2) the workspace `exclude` was missing recently-added in-tree
> separate `[workspace]` roots (`starbridge-web-surface`/`starbridge-v2`/`deos-leptos`/`deos-web-cells`/
> `servo-render`/`dregg-tui`) — "multiple workspace roots" broke workspace-wide cargo; added to `exclude`.
> Named residue: the standalone `dregg-verifier` has no rotated replay-chain verify yet (its v1 verify is a
> fail-closed stub under recursion — a separate lane, like the wasm-rotated Option-A). Gates GREEN on
> persvati: `cargo build --features recursion -p {circuit,sdk,turn,node}` (exit 0) + `cargo test --features
> recursion --no-run -p …` (exit 0) + circuit `not(recursion)` floor (exit 0). The steps below are the
> historical plan (kept for the audit trail).

> Scoped against HEAD (post Phases 0-4 + Bucket F). The main loop runs this once bucket-F's
> K-fold is green. **STATE CORRECTION:** the cutover is materially further along than
> `PATH-PRESERVE.md`/`V1-DELETION-MANIFEST.md` imply — the recursion leaf structs are ALREADY
> rotated-only (`DescriptorParticipant`/`ChainTurn` carry `RotatedParticipantLeg`, the
> `EffectVmP3Proof` field is dropped; remaining tokens are doc-comments), and the main sovereign
> executor verify ALREADY dispatches `recursion → verify_and_commit_proof_rotated` (no `EffectVmAir`),
> `not(recursion) → verify_and_commit_proof_v1` (`turn/src/executor/proof_verify.rs:43-50`).

## What ACTUALLY remains (in order)

**STEP 0 — baseline gate.** bucket-F K-fold green (the trigger). Capture the STEP-7 grep counts now (un-edited) so each step shows monotone burn-down.

**STEP 1 — THE WALL (do FIRST; NOT mechanical): cut the node async-attestation + HTTP-commit-revalidation off v1.** The live v1 chain in recursion builds: `node/src/api.rs:2486 revalidate_http_witness → :2511 generate_effect_vm_trace → :2518 bespoke_air_accepts` (callers `:2773/3036/3467/6264`); `api.rs:2540 enqueue_async_proof → prove_pool.rs:177 EffectVmAir prove`; predicate at `circuit/src/effect_vm_p3_full_air.rs:2451`; SDK twin `sdk/src/full_turn_proof.rs:2672`. The F-DOS-1 contract is "no STARK proving under `state.write()`," NOT "a FRI-free v1 check" — the executor already committed first. **1a:** drop the inline v1 `bespoke_air_accepts` revalidation (defense-in-depth atop the authoritative executor). **1b:** `prove_pool::run_job` proves the ROTATED `Ir2BatchProof` (reuse `prove_cohort_run_chain` / the rotated witness `turn/src/rotation_witness.rs`) instead of `EffectVmAir`. Breaks: `ProveJob` shape (`prove_pool.rs:54-65`), `WitnessedReceipt::from_components` (`:183`), the witnessed-receipt trace-replay (`turn/src/witnessed_receipt.rs:87/114`) → accept rotated or fence `not(recursion)`. Verify: `f_dos_1_request_path_liveness` + `api_` tests green; `grep bespoke_air_accepts|EffectVmAir node/src/{api,prove_pool}.rs` → 0 recursion-live.

**STEP 2 — MCP attestation surfaces → rotated/fenced.** `node/src/mcp.rs:260/479/4601/4650` (mint/verify v1 attestations). Re-point to STEP-1's rotated helpers. Verify `mcp` tests; `grep EffectVmAir node/src/mcp.rs → 0`.

**STEP 3 — executor secondary verify arms.** `turn/src/executor/atomic.rs:588/883` (atomic-turn default-AIR), `authorize.rs:1409` (bearer-cap STARK), `proof_verify.rs:845 verify_sovereign_witness_stark` (caller `execute.rs:798`) → route through `verify_vm_descriptor2` or fence (mirror the `proof_verify.rs:43-50` dispatch). `proof_verify.rs:1874 verify_bundle_with_stark` = DELETABLE (no live caller). The pre-marked `#[cfg_attr(feature="recursion", allow(dead_code))]` helper cluster (`proof_verify.rs:1501/1555/1597/1895/1913/1953/1969/1979/2181/2302`) is v1-only → STAYS under `not(recursion)`, deletes under recursion (STEP 6/5).

**STEP 4 — circuit Silver/forest bespoke v1 surfaces → DELETE (all dead/test-only, no live consumers).** `circuit/src/effect_vm/per_action.rs:170/200`; `proof_forest.rs` `verify_forest`/`ForestNode` + `DescriptorForestNode` (`:280`, the **last `EffectVmP3Proof` struct field**, ctors in `#[cfg(test)]`); `joint_turn_aggregation.rs` `JointParticipant`/`verify_participant` (`:94`) + `prove_joint_turn`/`verify_joint_turn` (zero external consumers). KEEP `DescriptorParticipant`/`RotatedParticipantLeg` (the live rotated cutover).

**STEP 5 — 5c mechanical delete fan-out** (after 1-4 disconnect the v1 prover):
- 5c.1 `CutoverFallback` + `cutover_route` + `prove_effect_vm_with_cutover` (`sdk/src/full_turn_proof.rs:623-698/750-797`) + the live v1 fallback leg (`:1418-1435` — **doc's `:1185-1202`, LINE-MOVED**). GUARD: add a `debug_assert!` that recursion-build finalized turns never hit `:1418` BEFORE deleting (the Phase-4 RED condition).
- 5c.2 delete `circuit/src/effect_vm_p3_full_air.rs` whole (`EffectVmP3Proof:77`, `EffectVmP3Air:1258`, `prove_effect_vm_p3:2345`, `bespoke_air_accepts:2451`) + drop `pub mod` (`lib.rs:270`). Blocked until STEP 1.
- 5c.3 `circuit/src/effect_vm/air.rs`: delete the `EffectVmAir` struct + impls; **KEEP `EFFECT_VM_WIDTH` + `generate_effect_vm_trace`** (Bucket E — the rotated leg is built on them, `trace_rotated.rs:50/203`). Drop the `EffectVmAir` re-exports (`effect_vm/mod.rs:206`, `lib.rs:332`).
- 5c.4 **DO NOT DELETE `effect_vm_p3_air.rs`** — its `EffectVmShapeAir` is LIVE in `recursive_witness_bundle.rs:237/360/412/420` (manifest mislabel).
- 5c.5 `bilateral_aggregation_air.rs`: delete only the v1 `BilateralAggregationAir:307`/`AggregationInnerRow:723`/`AGG_WIDTH:260`/`build_aggregation_trace:793` block; **KEEP** `CrossSideExistenceAir`/`BundleTreeFoldAir` (Bucket D, live) + `AggregationInnerRowV2`/`build_aggregation_trace_v2`.
- 5c.6 **`ACTIVE_BASE_COUNT` (`effect_vm/pi.rs:290`) STAYS as a constant** (the rotated PI prefixes the v1 layout); delete only the v1-reconstruction uses (`proof_verify.rs:312` in `verify_and_commit_proof_v1`).
- 5c.7 delete v1 tests WITH their targets: `effect_vm/tests.rs` v1-AIR fns (keep `generate_effect_vm_trace`/width-shape tests); `turn/src/tests.rs` recursion-dead blocks (`:7636/7655/7765/7802/7853/8009/8168/8258`); the differential harnesses' v1-vs-rotated cases.

**STEP 6 — Bucket-E fence confirmed STAY:** `generate_effect_vm_trace`, `EFFECT_VM_WIDTH`, `EffectVmShapeAir`/`effect_vm_p3_air.rs`, `verify_and_commit_proof_v1` + its `not(recursion)` helper cluster + tests, the wasm prover (`wasm/src/runtime.rs:710`, `bindings_lightclient.rs:389` — the separate Option-A wasm-rotated ember-decision; does NOT block native grep-zero). ⚑ EMBER-FLAG: confirm `wasm/Cargo.toml`'s feature graph truly builds the prover `not(recursion)`, else a `#[cfg(feature="recursion")]` rotated wasm branch is needed (the separate decision).

**STEP 7 — grep-zero (terminal gate), recursion build, minus Bucket-E:**
```
scripts/pbuild hardswap 'grep -rn "EffectVmAir\|EffectVmP3Air\|EffectVmP3Proof\|prove_effect_vm_p3\|CutoverFallback\|BilateralAggregationAir\|AggregationInnerRow\b\|bespoke_air_accepts" circuit/src sdk/src turn/src node/src --include="*.rs" | grep -v "cfg(not(feature = \"recursion\"))" | grep -v EffectVmShapeAir | grep -v AggregationInnerRowV2'
```
→ 0 lines. Then `cargo build --features recursion -p dregg-circuit -p dregg-sdk -p dregg-turn -p dregg-node && cargo test --features recursion …` → exit 0. (`EFFECT_VM_WIDTH`/`ACTIVE_BASE_COUNT`/`generate_effect_vm_trace` are NOT grep-zero targets — they STAY.)

## Walls vs mechanical
- **Walls (real work):** STEP 1 (the `bespoke_air_accepts`/async-attestation cutover — bucket-E item-1) + the rotate-or-fence judgment in STEPS 2-3.
- **Mechanical (once 1-4 disconnect v1):** all of STEP 5.
- **Ember-flag:** STEP 6 wasm `not(recursion)` graph (separate Option-A decision; does not block native grep-zero).
