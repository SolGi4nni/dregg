# ROTATION-CUTOVER — the flag-day checklist (the one VK epoch)

*(operational checklist, 2026-06-12. The design is `docs/UNIVERSAL-MAP-ROTATION.md`
(master) + `docs/EPOCH-DESIGN.md` (tables/commitment); the PROVEN target layout is
`metatheory/Dregg2/Circuit/RotationLayout.lean`; the staged wire propagation is
`metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotation.lean`. This file tracks what
FLIPS at the cutover commit, which pins bump, and what is staged vs. live today.)*

## §EXEC — the EXECUTION resume state (2026-06-13, the cutover-EXECUTE lane)

ember RATIFIED the two design decisions (move-proving-to-executor/node +
prover-free-verify). The residue is EMPTY (the rotated registry has all **36**
cohort members incl. `revokeCapabilityVmDescriptor2R24` + `customVmDescriptor2R24`;
verified `cut -f1 circuit/descriptors/rotation-v3-staged-registry.tsv | wc -l` = 36).
The executor (`dregg-turn`) depends on `dregg-circuit` with DEFAULT features, so
`verify_vm_descriptor2` (recursion-gated) IS visible natively.

THE TWO DISTINCT PROOF FLOWS (do NOT conflate — a subagent once mislabeled them):
  * **FLOW A** (sovereign, TEST-ONLY): producer `sdk::cipherclerk::execute_sovereign_turn_with_proof`
    (`cipherclerk.rs:5160` `stark::prove(&EffectVmAir)`) → verifier `turn::executor::proof_verify::
    verify_and_commit_proof` (`:420` `stark::verify(&EffectVmAir)`) + `verify_sovereign_witness_stark`
    (`:544`). MATCHED PAIR; only callers are `tests/src/sovereign_proof.rs`. Moving it cannot
    brick live turns. THE BRIEF's step (a)+(b) maps HERE.
  * **FLOW B** (full-turn, LIVE devnet, gated `full_turn_proving_enabled`): producer `node::turn_proving::
    prove_and_verify_finalized_turn{,_freshness,_capability}` → `prove_effect_vm_p3` (via sdk
    `prove_turn_self_sovereign`/`prove_full_turn`) → verifier `dregg_sdk::verify_full_turn{,_bound}`.
    Bigger surface; the live path. Comes AFTER A.

CHECKPOINT LADDER (each a coherent green boundary; relaunch from the last done):
  1. ✅ **C1 = FLOW A produce+verify ROTATED, native green — DONE (2026-06-13).** The matched
     pair (test-only) is rotated: producer `sdk::cipherclerk::prove_sovereign_turn_rotated`
     (routed from `execute_sovereign_turn_with_proof` under `recursion`) mints the rotated
     `Ir2BatchProof` via `rotation_witness::produce` + `prove_effect_vm_rotated_ir2_with_caveat`
     and stores the trace's PI 34/35 (the v9 felts) as old/new commitment; verifier
     `turn::executor::verify_and_commit_proof_rotated` reconstructs the 38-PI (placeholder block
     witnesses for the witness-independent PIs 0..33+37, then overrides PI 34←stored, PI
     35←claimed, PI 36←cell height) and verifies via `verify_vm_descriptor2`. The weak hand-AIR
     `EffectVmAir` leg is RETIRED on the sovereign proof-carrying path. New `dregg-turn` +
     `dregg-sdk` feature `recursion` (default-on; forwards to `dregg-circuit/recursion`) gates
     it; `not(recursion)` (wasm) keeps `verify_and_commit_proof_v1` / the v1 producer. Validated
     by `sdk/tests/sovereign_rotated_c1.rs` (honest accept + anti-ghost reject — both green) and
     compiles under BOTH `recursion` and `--no-default-features`. TWO PRECISE OBSTRUCTIONS found
     + fixed (NOT papered): (i) the trace's after-block `STATE_COMMIT` welds r0..r10 from the v1
     sub-trace's after-state, so the stored NEW commitment must be the trace's PI 35, NOT a
     separately-recomputed `compute_v9(after_cell)` (they diverge); (ii) `execute.rs` PHASE 1
     debits `turn.fee` + increments the nonce BEFORE the proof-carrying path, so the verifier
     reconstructs the pre-fee/pre-increment state (`balance + fee`, `nonce − 1`) — cross-checked
     by OLD_COMMIT (PI 34). The `dregg-tests` harness (`tests/src/sovereign_proof.rs`, edited to
     register the v9 commitment) is mid-edit by a PARALLEL agent (737 unrelated compile errors in
     other modules), so C1 is validated via the self-contained `sdk/tests/` integration instead.
  2. ✅ **C2 = prover-free `verify_vm_descriptor2` split — DONE (2026-06-13).** A `verifier`
     feature on `dregg-circuit` (`["plonky3","dep:p3-batch-stark","dep:p3-lookup",
     "dep:p3-poseidon2-circuit-air"]`; `recursion = ["verifier", + the recursion-prover crates]`)
     compiles `verify_vm_descriptor2{,_with_config}` + the AIRs + `ir2_config` under
     `dregg-circuit --no-default-features --features verifier` (no `prove_batch` / DFT-prover
     link). `descriptor_ir2` is module-gated `any(recursion, verifier)`; the PROVE surface
     (`prove_vm_descriptor2*`, `prove_vm_descriptor2_inner`, `build_traces` + the trace-fill
     helpers `eval_c`/`perm_aux`/`fill_*`/`to_matrix`/`next_pow2`, the `Ir2Traces` struct, the
     `prove_batch`/`StarkInstance` imports, the prover-only `crate::` imports, `MIN_TABLE_HEIGHT`,
     and the test module) is `recursion`-only. `verify_batch` is prover-free, and
     `ProverData::from_airs_and_degrees(..).common` builds only the symbolic `Lookups` + (empty,
     for the IR-v2 AIRs) preprocessed — no DFT, no `prove_batch`. Verified on persvati: BOTH the
     verifier-only lib (`--no-default-features --features verifier`, zero `descriptor_ir2`
     warnings) AND the default lib (recursion, prover path intact) build green. Files:
     `circuit/Cargo.toml`, `circuit/src/lib.rs`, `circuit/src/descriptor_ir2.rs`.
  3. C3 = FLOW B live-path move (decision #1): `prove_full_turn` → rotated `Ir2BatchProof`
     (changes `AttachedSubProof`/`ComposedProof` effect-vm leg), `verify_full_turn` → rotated
     verify, executor `verify_and_commit_proof` already rotated from C1. SDK thins to submit/verify.
     ALSO ROTATE HERE (with its matched producer): `verify_sovereign_witness_stark`
     (`proof_verify.rs:752`, live at `execute.rs:798`) — the `sovereign_witnesses[].transition_proof`
     leg, still v1 `EffectVmAir::new` at `:845`. Held OUT of C1 because it has NO live rotated
     producer (every live producer sets `transition_proof: None`; only `node/src/mcp.rs:6165` + the
     observability demo attach one), so rotating its verifier alone = a verify-without-producer brick.
     It rotates once a witness producer mints rotated `Ir2BatchProof`s (or its callers retire at C7).

     ⚠️ **HARD WALL found 2026-06-13 (needs an ember architecture decision before C3 can proceed
     to v1-deletion).** `prove_full_turn`'s effect-vm leg is an `EffectVmP3Proof` that THREE LIVE
     recursive-composition surfaces ingest / re-prove as the v1 **186-column** statement — so the
     effect-vm leg cannot rotate to the 311-col/38-PI `Ir2BatchProof` without rotating them too,
     and C7 cannot delete `EffectVmAir` / `generate_effect_vm_trace` / `EffectVmP3Proof` while they
     stand:
       * **`circuit/src/ivc_turn_chain.rs`** (LIVE — `lightclient`'s `WholeChainProof`,
         whole-history recursion): `prove_descriptor_leaf` (:507) re-proves `EffectVmDescriptorAir`
         over `descriptor_recursion_matrix(186-col base_trace)` through the recursion fork's
         in-circuit verifier (a uni-STARK leaf-wrap statement-equality argument);
       * **`circuit/src/joint_turn_aggregation.rs`** (LIVE — `lightclient`'s `DescriptorParticipant`):
         the aggregation AIR is built on `EffectVmAir::new(...)` (:67/:94) directly;
       * **`turn/src/aggregate_bilateral_prover.rs`** (LIVE — `node/blocklace_sync.rs:3265` +
         `node/mcp.rs:6587` bilateral bundle): outer STARK via `EffectVmAir` + the
         `wr.public_inputs[..ACTIVE_BASE_COUNT]` 204-PI v1 slice (C4 already scoped the 204→38
         reslice, but the outer AIR itself is v1).
     The flat FLOW B (the `prove_full_turn`/`verify_full_turn`/node-`turn_proving`/
     `verify_sovereign_witness_stark` quartet) is INSEPARABLE from these — they ingest the very
     `EffectVmP3Proof` it mints. **The decision needed:** how does the lightclient's WholeChainProof
     recursion (and the joint-turn aggregation) wrap the rotated MULTI-TABLE `BatchProof` — the
     existing leaf-wrap is a uni-STARK statement-equality, and there is NO in-circuit verifier /
     leaf-wrap for a rotated `BatchProof` in the recursion fork yet — OR does the whole-history
     recursion get re-architected, OR frozen on a legacy v1 leaf for historical turns while the
     live turn path rotates (which keeps v1 alive and contradicts "grep-zero v1 refs")?
     `proof_forest.rs` has NO non-test consumer (it can die at C7). C2 (verifier split) is the last
     unblocked rung; C3 onward is gated on this decision.

     ✅ **WALL PARTIALLY FELL 2026-06-13 (C3 leaf-wrap GREEN, commit `bbea731e7`/fork `72ffc56`;
     aggregation gate GREEN this lane).** Decision #1 = OPTION (a): build the in-circuit verifier /
     leaf-wrap for the rotated multi-table `BatchProof`. DONE for the two RECURSION knots:
       * `circuit/src/ivc_turn_chain.rs::prove_descriptor_leaf_rotated[_with_config]` (:610/:639)
         wraps a rotated `Ir2BatchProof` as a `RecursionInput::NativeBatchStark` leaf and the wrapped
         root self-verifies in-circuit (`rotation_batchstark_leaf_smoke.rs::rotated_transfer_leaf_folds_as_batchstark`).
       * **NEW (this lane) — the aggregation gate:** `rotation_batchstark_leaf_smoke.rs::
         two_rotated_leaves_aggregate_at_wrap_config` PROVES two rotated leaves fold up an
         aggregation layer at `ir2_leaf_wrap_config` (log_blowup 6) and the aggregated root
         self-verifies — GREEN in 339.87 s on persvati. So `prove_chain_core` (ivc) +
         `prove_joint_core` (joint) can rotate by (i) threading a rotated `Ir2BatchProof<DreggRecursionConfig>`
         + its `EffectVmDescriptor2` through `FinalizedTurn`/`JointCell`, (ii) minting leaves via
         `prove_descriptor_leaf_rotated_with_config(.., ir2_leaf_wrap_config())`, (iii) running the
         binding-leaf wrap + `aggregate_tree` at `ir2_leaf_wrap_config` instead of `create_recursion_config`.
         NOTE: the stale doc comment on `create_recursion_config_for_inner_fri` ("prover side unchanged,
         log_blowup 3") is WRONG — it delegates to `create_recursion_config_with_fri(inner_blowup,..)`,
         so the rotated leaf OUTPUT is log_blowup 6; the whole chain must run at that one engine.
       * The recursion knots are SETUP/DEMO-invoked (`lightclient::fold_and_attest` +
         `lightclient/src/bin/whole_history_demo.rs`); NO `node/`/`sdk/` production loop folds a chain.
     ⚠️ **STILL A HARD WALL — the BILATERAL aggregation outer AIR (knot 3).**
     `circuit/src/bilateral_aggregation_air.rs::BilateralAggregationAir` is a plain `StarkAir`
     (NOT the recursion machinery) proven via `dregg_circuit::stark::try_prove` over per-row
     `wr.public_inputs[..ACTIVE_BASE_COUNT]` (the 204-PI v1 slice). It is **LIVE** via the node HTTP
     endpoint `node/src/api.rs::post_aggregate_bundle` (:3299) + `node/src/mcp.rs:6587` — NOT covered
     by the C3 leaf-wrap (which is for the chain/joint uni→batch recursion). Rotating it is a
     from-scratch ROTATED OUTER AIR + Lean emission (a 38-PI inner-row aggregation AIR), distinct
     from the mechanical 204→38 reslice. This is the precise residual C3/C4 wall blocking grep-zero
     of `EffectVmAir` / `ACTIVE_BASE_COUNT` on the live bilateral path.

### §EXEC.2 — THE C4-C7 EXECUTE LANE (2026-06-13, the v1-deletion sprint)

State coming in is FURTHER than the census: **C3 ARCHITECTURE PROVEN** (leaf-wrap +
2-leaf aggregation gate both green, `bbea731e7`/`983255781`/fork `72ffc56`); **the
residue is RESOLVED** (`rotation-v3-staged-registry.tsv` has all 36 cohort members incl.
`revokeCapabilityVmDescriptor2R24` + `customVmDescriptor2R24` — `RevokeCapability` was
graduated by the cap-crown `53c6e417c`); **C6 cell commitment is ALREADY v9 LIVE**
(`CANONICAL_COMMITMENT_CONTEXT = "…v9"`, `cell/src/commitment.rs:110`; the cap-crown
flag-day bumped it).

**THE BILATERAL DECISION (made 2026-06-13, ember architecture-grant "implement whatever
all new things we need"): BUILD — emit a Lean-authored rotated aggregation AIR (law #1).**
Census verdict: `post_aggregate_bundle` is a REAL feature — HTTP `/turns/aggregate`
(`api.rs:1723`), MCP `dregg_bilateral_action` (`mcp.rs:1821`), WASM
`DreggRuntime::prove_bilateral_aggregate`, the verifier CLI, and the adversarial gauntlet
`teasting/tests/multi_cell_cross_fed_binding.rs` (cross-federation conservation — the only
mechanism preventing cross-federation double-spend). So RETIRE is OFF the table.

PRECISE SCOPE CORRECTION (verified, do not re-conflate): the bilateral AIR does NOT ingest
an `EffectVmP3Proof` / the effect-vm 38-PI. Its constraints read the **bilateral-schedule
PI contract** — `inner_pi::{TURN_HASH_BASE 25, EFFECTS_HASH_GLOBAL_BASE 29, ACTOR_NONCE 33,
PREVIOUS_RECEIPT_HASH_BASE 34, OUTBOUND_TRANSFER_COUNT 38..44, OUTGOING_TRANSFER_ROOT_BASE
45..72, IS_AGENT_CELL 73}` — a ~49-felt turn-identity+schedule layout that happens to live
inside the v1 PI module. The ONLY v1 coupling is (a) `PI_BUFFER_WIDTH =
inner_pi::ACTIVE_BASE_COUNT` (the 204 buffer width) and (b) those offset constants living in
`effect_vm::pi`. The "38-PI" in the prior wall note conflated the effect-vm rotation PI with
the bilateral inner-row PI — the bilateral inner row is the schedule contract, sized to its
own count, NOT 38. The aggregation AIR is a DISTINCT constraint family (cumulative-sum +
first/last-row boundary + cross-row schedule replay), so the Lean emission is a NEW module
(`EffectVmEmitBilateralAgg.lean`), not a `rotateV3` lift of a per-effect descriptor.

✅ **THE LEAN FOUNDATION LANDED (2026-06-13, this lane; axiom-clean, full `Dregg2` builds):**
  * **The grammar unlock** — the IR-v2 base grammar could not express a cross-row
    constraint (the `EmittedExpr` gate body reads only the current row), so the cumulative
    `next[cum] = local[cum] + next[is_agent]` was inexpressible. Added a NEW two-row primitive
    to `Dregg2/Circuit/DescriptorIR2.lean`: `WindowExpr` (`loc c`/`nxt c`/const/add/mul),
    `WindowConstraint {body, onTransition}` + its `holdsAt`/`toJson`, and the
    `VmConstraint2.windowGate` variant (+ its `holdsAt`/`toJson` arms). Zero regression — the
    whole emit tree (`EffectVmEmitV2`/`RotationV3`/…) + the full `Dregg2` root rebuild clean.
  * **The descriptor** — `Dregg2/Circuit/Emit/EffectVmEmitBilateralAgg.lean`:
    `bilateralAggDescriptor` (the DECOUPLED `Sched.*` 49-felt schedule layout as its own region
    + `Agg.*` 87-col main + `OuterPi.*` 23 fixed PI), CG-2 (turn-id PI bindings on both boundary
    rows) + CG-3 (schedule replay equalities) + CG-4 (boolean/padding gates + the two
    `windowGate` cumulative transitions) + the boundaries. Byte-pinned `#guard`s (width 87,
    PI 23, 70 constraints, exactly 2 window gates, versioned wire).
  * **The teeth** (axiom-clean): `agg_rejects_turn_mismatch` (a row disagreeing on turn-id is
    UNSAT) + `agg_rejects_bad_agent_count` (the last-row `cum ≠ 1` boundary — two agent rows
    REFUSED) — the cross-federation-double-spend rejections as theorems.
  * REMAINING (the Rust lane, NOT yet done): decode `windowGate` in `descriptor_ir2.rs` (the
    `when_transition` arm over the WindowExpr) + emit `bilateralAggDescriptor` to JSON
    (EmitAllJson) + RESTRUCTURE the witnessed-receipt to carry the standalone 49-felt schedule
    block (so the aggregation reads it independently of the rotated effect-vm 38-PI) + rewire
    `aggregate_bilateral_prover.rs` to interpret the Lean descriptor instead of the hand AIR +
    re-prove the `teasting/multi_cell_cross_fed_binding` gauntlet. THEN the bilateral path
    grep-zeroes `effect_vm::pi`/`ACTIVE_BASE_COUNT`.

EXECUTION ORDER tonight (highest-leverage, lowest-risk first; everything staged-green or
WIP, NEVER committed by this lane — the main loop commits):
  * C6-cleanup: the stale "v8 is LIVE / do NOT bump" comment at `cell/src/commitment.rs`
    is FIXED (the live ctx is v9). ✅
  * C4-recursion: widen `FinalizedTurn`/`DescriptorParticipant`/`JointCell` to carry a
    rotated `Ir2BatchProof<DreggRecursionConfig>` + its `EffectVmDescriptor2`; mint leaves
    via `prove_descriptor_leaf_rotated_with_config(.., ir2_leaf_wrap_config())`; run
    `prove_chain_core`/`prove_joint_core` at the wrap config (the aggregation gate proves
    this folds). The two consumers are SETUP/DEMO-invoked (lightclient), so this is
    self-contained.
  * FLOW-B flat leg: widen `FullTurnWitness` with the rotation witnesses [before/after
    RotationWitness]; route `prove_full_turn`'s effect-vm leg through
    `prove_effect_vm_rotated_ir2_with_caveat`; change `AttachedSubProof.effect_vm_proof`
    wire type → `Ir2BatchProof`; thread from node `turn_proving` + the ~70 call-sites.
  * THE BILATERAL Lean build (the long pole): `EffectVmEmitBilateralAgg.lean` emits the
    aggregation AIR (the schedule-PI layout + CG-2..CG-5 + the cumulative/boundary
    constraints) as a Lean-proved descriptor; the Rust side interprets it (decoupling the
    bilateral AIR from `effect_vm::pi`); re-prove the gauntlet.
  * C5 regen (registry→default, R=24 live, re-pin, reseed FFI) → C7 DELETE + grep-zero.
  4. C4 = reroute the ~70 v1 call-sites + `aggregate_bilateral_prover.rs` (204→38 PI slice) + un-gate.
  5. C5 = regen (EmitAllJson→v3Registry live, R=16 probe→R=24, re-pin artifacts, reseed FFI closure).
  6. C6 = VK epoch + succession record.
  7. C7 = DELETE v1 (`effect_vm_p3_full_air.rs`, `effect_vm_p3_air.rs`, `effect_vm/air.rs`
     `EffectVmAir`, `EffectVmP3Proof`, 186-col `generate_effect_vm_trace`, `CutoverFallback`);
     grep-confirm ZERO v1 refs.

KEY FACT for C1 verify: the executor does NOT reconstruct iroot/cells_root — the producer
publishes the v9 commitment (which absorbs them) as the NEW_COMMIT PI; the verifier compares
the proof's NEW_COMMIT PI against `turn.execution_proof_new_commitment` (the claimed v9 felt) and
OLD_COMMIT against the stored v9 commitment. The proof binds the transition; no witness rebuild.

C1 RE-VERIFIED 2026-06-13 (fresh persvati build, independent of the prior pass's self-report):
`sdk/tests/sovereign_rotated_c1` both green under `recursion`; `dregg-turn` green under BOTH
default and `--no-default-features`. MEASURED proof sizes (`effect_vm_ir2_size_measure`, the same
real provers): **v1 hand-AIR 358900 B (350.5 KiB), verify 16.8 ms → rotated IR-v2 123292 B
(120.4 KiB), verify 5.0 ms** = 0.344 ratio (−65.6 % size), verify 3.4× faster — the economics win
rides on top of the soundness win. (One hygiene fix: removed a dead `use serde::Deserialize;` in
`executor/mod.rs` whose WIP `cfg_attr` gate was inverted; unused in both configs.)

## §0 — Standing law

1. **Zero Rust-authored constraint semantics.** Every table, relation, and layout
   fact is emitted from Lean; Rust interprets (`descriptor_ir2.rs:53-58`). A layout
   change starts in Lean, lands as a re-emitted artifact, and only then re-anchors
   the Rust constants behind a drift guard.
2. **Nothing flips before GATE 0** (the IR-v2 size regression measured green —
   `docs/PROOF-ECONOMICS.md` §2b, `circuit/tests/effect_vm_ir2_size_measure.rs`).
3. **The live v1 path stays byte-identical until the cutover commit.** Staged
   artifacts ride the recursion-gated IR-v2 path only.

## §1 — What is ALREADY LANDED (staged or live-additive; verify, don't re-do)

| piece | where | state |
|---|---|---|
| registers 8→16 + heap_root in cell state, commitment context v6→v7 | `f5a25fd16` (cell/turn) | LIVE (cell-side; additive context bump) |
| executor admits heap fields (SetField ≥ STATE_SLOTS → fields_map) | `b133354fc` (turn) | LIVE |
| committed_height limb (context v8) + PI v3 tail wiring (`pi::v3`, ACTIVE_BASE_COUNT fan-out) | `007c2f1d2` | LIVE (tail populated; nothing reads it on-wire yet) |
| fresh-key sorted INSERT (`MapKind::Insert`, wire code 3) | `696fa1032` (descriptor_ir2) | STAGED (IR-v2 path) |
| THE TARGET COMMITMENT LAYOUT, proven: `RotatedLimbs` (23 limbs, iroot LAST), `rotatedCommit_binds` anti-ghost keystone, `resolve` (FactoryDescriptor.fields), `PiV3` offsets | `metatheory/Dregg2/Circuit/RotationLayout.lean` | PROVEN (Lean; no wire) |
| THE WIRE PROPAGATION, staged: rotated 25-slot state block (absorption-ordered), `wireCommit` = 4-ary chained chip realization + re-proved keystone (`wireCommit_binds` + heap_root/reg/named-field/log teeth), `rotationProbeVmDescriptor2` (graduated IR-v2 probe: 8 chip lookups + published-commit/height PI pins), `rotationLayoutManifest` (byte-pinned) | `metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotation.lean`, driver `EmitRotationV3.lean` | STAGED (this lane) |
| staged artifacts on the Rust side: `circuit/descriptors/rotation-layout-v3-staged.json` + `dregg-effectvm-rotation-state-v3-staged.json`, `effect_vm_descriptors.rs::V3_STAGED_DESCRIPTORS` (sha-256 pinned), `columns.rs::rotation` (drift-guarded `rotation_layout_matches_lean`), probe prove/verify/size + per-column tamper-refusal in `descriptor_ir2.rs` | circuit | STAGED (this lane) |
| PI v3 drift guard (`pi_v3_offsets_match_lean`) | `circuit/src/effect_vm/pi.rs` | LIVE test |
| THE WIDENED CAVEAT OPERAND, staged: `(domain_tag, key)` entries (7 felts, umem `domainCode` discipline, key u8→felt) + `caveat_operand_no_aliasing` keystone + `caveatCommit_binds` + the R=24 caveat probe (`rotationCaveatProbe_binds_published`) + forged-domain/tampered-heap-key teeth | `metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationCaveat.lean`, `circuit` (`columns.rs::rotation::caveat`, `trace.rs::RotCaveatEntry`, `V3_STAGED_CAVEAT_DESCRIPTORS`, `descriptor_ir2.rs` teeth) | STAGED (this lane) |
| THE FULL-COHORT REGEN at the rotated R=24 block, staged: `rotateV3` (ONE parametric transformation — appends two rotated state blocks + the widened-caveat region past ANY v1 descriptor, +125 cols, 4 appended PI pins; col-chained ⇒ byte-identical to the digest-chained R=24 probe, `#guard` tripwire), v1-survival keystone `rotateV3_satisfiedVm_v1` (every per-effect theorem composes unchanged), end-to-end `rotV3_binds_published` (one theorem, 26 descriptors — same published commits ⇒ equal whole before+after blocks + iroots + height + caveat manifest under the ONE CR floor), `v3Registry` (all 26 graduated, `attenuateV3`/`setFieldDynV3` keep their extras), welds r0↔BALANCE_LO · r1↔NONCE · r2↔BALANCE_HI · r3..r10↔fields · CAP_ROOT↔CAP_ROOT | `metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean`, Rust twin `circuit/descriptors/rotation-v3-staged-registry.tsv` + `V3_STAGED_REGISTRY_TSV` (sha-256 pinned; `v3_staged_registry_parses_matches_fingerprint_and_covers` walks all 26 — absorption + chain + 4 PI pins) | STAGED (this lane) |

## §2 — The staged commitment shape (what the cutover realizes)

The per-state commitment becomes the CHAINED 4-ary chip absorption (Lean
`wireCommit`; the chip absorbs ≤ 4 base elements per permutation), over the
absorption order pinned by `RotatedLimbs.toList`:

```
cells_root · r0..r15 · cap_root · nullifier_root · heap_root
           · lifecycle · epoch · committed_height · iroot   (LAST)
```

8 permutation sites (4 + 3·6 + 2 limbs), intermediate digests on chain carriers,
final digest = `state_commit`. Anti-ghost: `wireCommit_binds` (equal commits ⇒
equal limbs ∧ equal iroot, under the ONE `Poseidon2SpongeCR` floor);
`wireCommit_binds_log` composes `mroot_injective` (tamper/truncate/extend/REORDER
of the receipt log all refused). The layout manifest is byte-pinned BOTH sides
(Lean `#guard` / Rust `rotation_layout_matches_lean`) — neither side parses, both
pin.

**Note (balance/nonce):** `RotatedLimbs` carries NO separate balance/nonce limbs —
in the rotated world the cell's scalar state rides the NAMED register file
(`FactoryDescriptor.fields` → `resolve`) or the heap domain (the umem projection
already maps Balance/Nonce keys into the heap domain — `turn/src/umem.rs`). The
flag-day regen must fix the canonical name→register assignment for the kernel's
own scalars (an ember-visible decision; HORIZONLOG'd).

### §2a — THE AUTHORITY-DIGEST DESIGN (G3 design call, the rotated-commitment authority coverage)

The rotated v9 commitment (`cell/src/commitment.rs::compute_canonical_state_commitment_v9`)
binds the FULL authority-bearing cell state v8 commits — it does NOT drop authority state.
The decision (made + implemented 2026-06-13, Opus):

* **The problem.** v8 (BLAKE3, `CANONICAL_COMMITMENT_CONTEXT "…v8"`) absorbs the whole cell:
  identity, `mode`, the eight `Permissions` fields, the `verification_key`, `delegate`, the
  `delegation` snapshot, the `program`, and the full CellState authority sub-state
  (`field_visibility`, `commitments`, `proved_state`, the side-table/overflow roots, all 16
  `fields`). The rotated v9 NAMED limbs cover only a SUBSET: balance/nonce (r0/r1/r2),
  `fields[0..8]` (r3..r10), cap_root (r25), nullifier/heap roots (r26/r27),
  lifecycle/epoch/committed_height (r28/r29/r30). Everything else would be DROPPED by a
  rotated commitment that left the app-register headroom (r11..r23) zeroed — a soundness hole
  (two cells identical in the named limbs but differing in permissions/VK commit identically).

* **The fix — bind an AUTHORITY DIGEST into register r23.** `compute_authority_digest_felt`
  (one Poseidon2 felt) folds EXACTLY the authority residue no named limb carries: identity,
  mode, permissions, VK, delegate, delegation snapshot, program, `field_visibility`,
  `commitments`, `proved_state`, `swiss_table_root`, `refcount_table_root`, `fields_root`,
  `system_roots_digest`, and `fields[8..16]` (fields[0..8] are welded, so only the high
  fields go here). It walks the SAME byte serialization v8 uses (one source of truth for
  "what is authority state"), then hashes to a felt. The digest is cell-local; the
  turn-context limbs (cells_root/nullifier_root/iroot) ride `V9RotationContext`. So v9
  **covers all authority state (via r23) AND binds turn-context (via the context limbs)** —
  the design problem's two requirements, both met.

* **Why r23, and why NO Lean change.** The Lean welds (`EffectVmEmitRotationV3.weldsAt`)
  constrain ONLY r0..r10 + cap_root — r11..r23 are freely-witnessed limbs. The anti-ghost
  keystone (`wireCommitR_binds` / `RotationLayout.rotatedCommit_binds_reg`) ALREADY proves
  EVERY register is bound by the commitment. So r23 is "just a register" to the circuit and
  Lean: the authority digest binds with zero new keystone, zero Lean edit. The three-way
  agreement holds by construction — the cell-side v9, the producer
  (`turn/src/rotation_witness.rs::produce`), and the circuit trace generator
  (`trace_rotated.rs::fill_block`, which carries r23 from the witness) all derive r23 from the
  SAME `compute_authority_digest_felt(cell)`.

* **The tooth.** `cell/src/commitment.rs::v9_binds_full_authority_state` proves the property:
  two cells differing ONLY in permissions / VK / a high field / proved_state / a side-table
  root / mode commit distinctly under v9. This is what a zeroed-headroom rotated commitment
  would FAIL.

### §2c — THE COHORT-GENERAL GENERATOR (G4)

The rotated trace generator (`trace_rotated.rs::generate_rotated_effect_vm_trace`) was always
shape-general (the v1 sub-trace `generate_effect_vm_trace` dispatches every effect's selector
+ rows; the rotated appendix is parametric, not per-effect). What was transfer-only was the
DESCRIPTOR RESOLUTION and the caveat manifest. Now:

* `trace_rotated::rotated_descriptor_name_for_effect(effect)` resolves the `*VmDescriptor2R24`
  registry member for any of the 26 cohort effects (the 17 selector-mapped base effects +
  `setFieldDyn` + the 8 per-slot `setField`s), `None` (fail-closed) for a non-cohort effect.
  `effect_vm::trace::effect_selector` is the single source of truth (extracted from the trace
  generator's selector match, no duplication). The coverage tooth
  (`resolvers_cover_exactly_the_rotated_registry`) proves the resolvers reach EXACTLY the 26
  registry members.
* `sdk::full_turn_proof::prove_effect_vm_rotated_ir2_with_caveat` is the cohort-general
  rotated prover: it resolves the descriptor by effect, defaults to the empty caveat manifest
  (transfer keeps the two-domain reference manifest), proves the shared 311-col trace through
  the IR-v2 batch prover, and fails closed on empty / heterogeneous / non-cohort turns.

**Cohort boundary (honest) — WIDENED (STEP 1, 2026-06-13):** the rotated registry the Lean
`v3Registry` emitted was the 26 v2-graduated members; STEP 1 widened it to **34** by lifting
the 8 LIVE-path effects that had a graduated v1 wire descriptor through the SAME `rotateV3`:
`GrantCapability` (the bare unattenuated cap-root grant — `grantCapVmDescriptor2R24`),
`MakeSovereign`, `CreateCell`, `CreateCellFromFactory`, `SpawnWithDelegation`, `ReceiptArchive`,
`CellUnseal`, `EmitEvent`. Each is graduable (`#guard`ed) so `rotV3_sound_v1` /
`rotV3_binds_published` apply with no new proof; `rotated_descriptor_name` now resolves them;
the TSV + SHA + the `n == 34` cover guard + the resolver-coverage tooth are re-pinned green.
(STEP 1 also REPAIRED `EffectVmEmitEmitEvent.unify_emitEvent`, which had a stale `recKernel_ext`
arity after `EmitEventSpec` gained the `heaps` frame clause — the descriptor was sound but its
executor-connector proof leaked `sorryAx`; now axiom-clean and in the live `Dregg2` closure.)

**THE RESIDUE (two effects, precise obstructions — NOT papered over):** `RevokeCapability`
(selector 24) has NO graduated v1 descriptor at all (absent from `SELECTOR_DESCRIPTORS`; its
cap-root advance is being reshaped by the cap-crown lanes — it stays on the monolithic hand-AIR),
and `Custom` (selector 8) needs an accumulator/recursive proof-binding constraint kind the
per-row descriptor IR does not have. `rotated_descriptor_name` fails closed (`None`) for both.
The live-path rewrite (STEP 2) must keep a path for these two until a Lean-emission act adds
them (a new constraint kind for Custom; a graduated descriptor for RevokeCapability post
cap-crown). This is the precise residue the flag-day must resolve before v1 can fully die.

## §2b — Register count: MEASURED (16 vs 24 vs 32 — the always-paid vs metered economics)

Registers are **always-paid**: every register limb rides EVERY turn proof's commitment
chain — a main-trace column opened at each FRI query point plus its share of the chained
chip absorption — whether or not the app touches it, forever. Heap fields are **metered**:
umem rows enter a proof only when touched (the first REAL-TURN umem proof measures
**64.4 KiB**, `tests/effect_vm_umem_real_turn.rs`, landed `93a34fa74`). So "is 16 enough?"
is a price table, not a taste call. The staged probe was re-emitted at three register
counts from the PARAMETRIC Lean emission (`metatheory/Dregg2/Circuit/Emit/
EffectVmEmitRotationR.lean`: layout columns, arity-{2,4} chunking, and the chained
commitment are FUNCTIONS of R; the anti-ghost keystone `wireCommitR_binds` holds
parametrically in R under the one CR floor — no per-R axiom; the R=16 instance reproduces
the pinned emission BYTE-IDENTICALLY, `#guard`ed on the emitted JSON) and measured at the
production `ir2_config` (`descriptor_ir2.rs::rotation_probe_register_count_measurement`,
release, M-series laptop; teeth scale with the block: presence-refusal walks every limb
per R, spot tamper-refusal at low/high register + iroot + commit carrier per R, the full
33-column gauntlet stays on R=16):

| R | app registers (after balance/nonce) | chip sites | probe width | proof size | Δ vs 16 | opened-values | prove | verify |
|---|---|---|---|---|---|---|---|---|
| 16 | 14 | 9 (7×4 + 2×2) | 33 | 96,620 B (94.4 KiB) | — | 16,936 B | 23 ms | 3.2 ms |
| 24 | 22 | 11 (10×4 + 1×2, EXACT 3-fill) | 43 | 98,846 B (96.5 KiB) | **+2.2 KiB (+2.3%)** | 17,382 B | 28 ms | 2.9 ms |
| 32 | 30 | 15 (12×4 + 3×2) | 55 | 102,178 B (99.8 KiB) | **+5.4 KiB (+5.8%)** | 18,203 B | 18 ms | 3.1 ms |

(Chip table 2⁴ rows at every R — the chained sites dedupe per distinct absorption, so
9/11/15 sites all pad to 16; prove/verify differences are run-to-run noise at this scale.)

**Always-paid delta:** R=24 costs **+2.2 KiB per turn proof, forever** (~278 B per added
register); R=32 costs **+5.4 KiB** (~347 B per added register — the marginal register gets
DEARER past 24 because the 3-fill breaks: 24→32 adds 4 chip sites where 16→24 adds 2).
Against the metered baseline: a heap-resident field costs ~64.4 KiB on the turns that
TOUCH it (the real-turn umem proof) and zero on every other turn — registers are the L1
for hot scalars, the heap is where app state lives.

**Recommendation: R=24.**
  * The always-paid price is small and measured: +2.3% proof size per turn, forever — and
    22 app registers (after balance/nonce take r0/r1) retires the "14 doesn't seem like
    enough" concern with real headroom.
  * R=24 is the chunking sweet spot: the 31 pre-iroot limbs fill 4+9·3 EXACTLY, so the
    chain is 10 arity-4 sites + the lone arity-2 iroot tail — the cleanest chip realization
    of the three (R=16 and R=32 both carry mid-chain arity-2 sites).
  * R=32's further +3.2 KiB buys 8 more always-paid limbs at a WORSE per-register rate, for
    state that the heap economics says should be metered instead: a register only beats a
    heap field when it is touched on a large fraction of turns, and cold scalars belong in
    the heap (`umem` rows only when touched).
  * The decision stays cheap to revisit before the flag-day: the emission is parametric
    (`rotationProbeVmDescriptorR2 R`), so re-measuring any other R is one driver line.

## §3 — The cutover sequence (one motion, in order)

Pre-gates (ALL green before anything flips):

- [x] **The register-count decision** (§2b): MEASURED at R ∈ {16, 24, 32} (table above)
      — **CONFIRMED R=24 by ember, 2026-06-12 ("22 it is")**: 22 app registers after
      balance/nonce take r0/r1, +2.2 KiB always-paid per turn. The flag-day regen fixes
      `NUM_REGISTERS = 24`; the R-parametric emission (`rotationProbeVmDescriptorR2`)
      and `wireCommitR_binds` make this a parameter instantiation, not new design.

- [x] **Caveat operand widened (staged)** — the second wire-shape pre-gate: the in-circuit
      caveat operand is no longer slot-only. The rotated entry is **7 felts
      `[type_tag, domain_tag, key, p0..p3]`** (`SlotCaveatEntry`'s 6 + the domain tag; the
      key widens u8 → felt so HEAP KEYS are reachable); domain tags are the umem
      `domainCode` wire codes (registers 0 · heap 1; everything else REFUSES, fail closed);
      the manifest is 1 count + 4 entries = **29 felts**, bound by its own chained chip
      commitment (`caveatCommit`, arity-{2,4} chunking, 10 sites). Lean keystones
      (`EffectVmEmitRotationCaveat.lean`): **`caveat_operand_no_aliasing`** (a slot operand
      and a heap operand can NEVER collide — domain separation as a theorem),
      `caveatCommit_binds` (equal commits ⇒ equal manifests), and the end-to-end
      `rotationCaveatProbe_binds_published` at the CONFIRMED R=24 (probe layout: rotation
      block `0..42` · manifest `43..71` · chain `72..80` · `CAVEAT_COMMIT` 81 · width 82;
      probe proof measures ~107.9 KiB ≈ +11.4 KiB over the bare R=24 probe). Rust staged
      twins + teeth: `columns.rs::rotation::caveat`, `trace.rs::RotCaveatEntry`
      (fail-closed `from_felts`), `rotation_caveat_layout_matches_lean` byte pin,
      forged-domain-tag / tampered-heap-key refusal gauntlet (`descriptor_ir2.rs`).
      REMAINS (HORIZONLOG'd): the executor's runtime discharge of heap-keyed caveats
      (named premise `HeapCaveatRuntimeDischarge`) + the flag-day fold of the staged
      manifest into the live PI region (replaces `SLOT_CAVEAT_MANIFEST_BASE` 101..126).

- [x] **GATE 0**: `effect_vm_ir2_size_measure` at-or-under the v1 350.5 KiB
      baseline (per-effect; the staged probe's block-only shape measures ~tens of
      KiB — see the test print — but the GATE is the per-effect transfer figure).
      **GREEN**: v1 358,900 B (350.5 KiB) → IR-v2 123,292 B (120.4 KiB), ratio 0.344
      (-65.6%); re-confirmed this lane post-regen (the additive staging does not move it).
- [x] The 3-verb executor bridge (`RecordKernelState` → the ONE universal map)
      landed and soaked (`VerbCompression.lean:87-89` — "rides THE ONE ROTATION";
      first real-turn umem proof landed `93a34fa74`).
      **EXTENDED THIS LANE**: the per-turn ROTATION PRODUCERS now derive the
      witness-carried rotated limbs (`cells_root`, `iroot` MMR, `lifecycle`/`epoch`)
      from the real `RecordKernelState` — `turn/src/rotation_witness.rs` (the file
      §5 items 3-5 named as DELIBERATELY UNBUILT), built TOGETHER with the rotated
      trace builder that consumes them (`circuit/tests/effect_vm_rotation_flip.rs`).
- [ ] Lean adapters: cap-leaf value-codec · MMR boundary-derivation · guardAtom
      atoms (`UNIVERSAL-MAP-ROTATION.md` §3) — to whatever extent the rotation
      carries §2.2/§2.3 (detachable: the LAYOUT items §2.1/§2.4/§2.6 do not
      depend on them).
- [ ] `absent` map-op realization driven through a real nullifier witness
      (staged `MapKind::Insert` landed; the absent lane has its gauntet tests).

**LANE STATUS (the producers + trace builder + differential, staged-additive):** the
genuinely-new deferred long pole is DONE and GREEN — `turn/src/rotation_witness.rs`
(producers) + `circuit/tests/effect_vm_rotation_flip.rs` (rotated trace builder +
end-to-end prove+verify of `transferVmDescriptor2R24` at ~144.1 KiB + cell≡circuit
differential + anti-ghost teeth) land BESIDE v1 (v1 byte-identical, no VK bump, all 11
registry drift guards + 3 gate harnesses still green). The flip steps below are now the
MECHANICAL irreversible tail (registry-default + VK + cell context v8→v9 + executor PI +
v1 deletion) — the rotated path is proven green FIRST, exactly the cutover doc's safety
sequencing (§5.1: measure before the irreversible bump). **v1 is left DORMANT-BUT-PRESENT.**

The flip itself (ONE commit, regenerated, nothing hand-edited):

1. [ ] Re-anchor the per-effect Lean emit modules onto the rotated state block
       (the 25-slot absorption-ordered block replaces the 14-slot v1 block; the
       `EffectVmEmitRotation` probe is the validated reference shape — descriptors
       gain the 8-site chained commitment in place of the GROUP-4 tree; selector
       block dies into the verb/thin-main packing chosen by the regen).
2. [ ] ONE descriptor regeneration: `EmitAllJsonV2.lean` (or its successor)
       re-emits the full cohort against the rotated block; `EmitRotationV3.lean`'s
       manifest becomes the LIVE layout manifest.
3. [ ] Rust re-anchor: `columns.rs` live constants ← the manifest (the staged
       `rotation` module graduates to THE layout); `trace.rs` row population +
       `air.rs` constraint fan-out regenerate against the new width;
       `effect_vm_descriptors.rs` v1 registry replaced by the rotated registry
       (fingerprints all bump).
4. [ ] Cell/turn: `compute_canonical_state_commitment` context v8 → v9 = the
       rotated absorption order (cells root first, iroot last) — the cell-side
       commitment and the circuit-side commitment converge on ONE shape;
       executor PI assembly reads `pi::v3` slots as LIVE (VK_PI_LAYOUT_VERSION
       2→3 already staged, `CUSTOM_PROOFS_BASE` already moved).
5. [ ] VK/commitment bump + succession drill.
6. [ ] Graduation completes: `CutoverFallback` + the legacy AIR path die;
       RESERVED/retired-selector columns die.

Post-flip gauntlets (block the deploy, not the commit):

- [ ] differential gauntlets: cell ≡ circuit per map · per-effect AGREE against
      the rotated executor · the memory-argument adversarial suite (tampered
      read refuses).
- [ ] **the persvati workspace gauntlet** (`ssh persvati`, full
      `cargo test --workspace` + `lake build` on the build node) — REQUIRED
      before deploy.
- [ ] deploy when ember says deploy.

## §4 — Which pins bump at the flip

| pin | today | at the flip |
|---|---|---|
| `CANONICAL_COMMITMENT_CONTEXT` | v8 | v9 (rotated absorption order) |
| `VK_PI_LAYOUT_VERSION` | 3 (staged tail populated) | 3 live-read (verifier reads COMMITTED_HEIGHT from PI) |
| `pi::BASE_COUNT` | 201 frozen | superseded by the regenerated layout (PiV3 pins re-anchored) |
| v1 descriptor fingerprints (`ALL_DESCRIPTORS`) | frozen | ALL bump (regen) |
| `EFFECT_VM_WIDTH` 186 / state block 14 | frozen | dies (regen decides the thin-main packing; NOT 186+Δ — `EPOCH-DESIGN.md`) |
| `V3_STAGED_DESCRIPTORS` | 1 probe | the probe is subsumed by the live registry (delete or keep as reference gauntlet) |

## §5 — What remains UNDONE after this lane (the honest list)

1. ~~**The full-cohort regen at the rotated block** (§3 step 1-2) — the probe pins
   the SHAPE; the 26 per-effect descriptors still emit against the 186/14 layout.~~
   **DONE (staged), this lane + WIDENED to 34 (STEP 1, 2026-06-13)** —
   `EffectVmEmitRotationV3.lean::v3Registry` re-emits all **34** cohort members at the rotated
   R=24 block via the ONE parametric `rotateV3` (the 26 v2-graduated + the 8 LIVE-path effects
   STEP 1 added: grantCap · makeSovereign · createCell · factory · spawn · receiptArchive ·
   cellUnseal · emitEvent); the soundness keystones (`rotateV3_satisfiedVm_v1`,
   `rotV3_binds_published`) lift ONCE for all 34, axiom-clean; Rust twin
   `rotation-v3-staged-registry.tsv` is sha-pinned (`n == 34` cover guard) and the
   coverage/drift test walks every descriptor's absorption + chain + 4 PI pins. STAGED
   beside v1/v2 (no VK bump, the live wire untouched). RESIDUE: `RevokeCapability` (24) +
   `Custom` (8) still have no rotated descriptor (precise obstructions, §2c). The FLIP
   (§3 steps 1-6) replaces the v1 registry with this rotated one — still the main loop's act.
2. **The balance/nonce register-name assignment** (§2 note) — ember decision.
3. ~~**The cells_root producer**~~ **BUILT THIS LANE** (`turn/src/rotation_witness.rs::cells_root`):
   the turn-level boundary view over present cells (sorted-Poseidon2 root via
   `dregg_circuit::heap_root`, set-valued — `cells_root_is_set_valued`). Built
   TOGETHER with the rotated trace builder that consumes it
   (`circuit/tests/effect_vm_rotation_flip.rs`), so it is validated, not unvalidatable:
   the rotated transfer (`transferVmDescriptor2R24`) proves+verifies end-to-end on a
   real turn (~144.1 KiB) and the cell≡circuit differential asserts the producer's
   limb EQUALS the trace's before/after `cells_root` carrier.
4. ~~**The iroot producer**~~ **BUILT THIS LANE** (`rotation_witness.rs::iroot`): the
   left-leaning Poseidon2 MMR fold over the receipt log — the Rust twin of the Lean
   `mroot_injective`. The non-omission tooth is tested (`iroot_binds_the_whole_log`:
   tamper/truncate/extend/reorder each move the root); the differential binds the
   producer's iroot to the trace's after-block iroot carrier, and the anti-ghost
   gauntlet REFUSES a tampered iroot at prove time.
5. ~~**lifecycle/epoch carriers in the trace**~~ **BUILT THIS LANE**
   (`rotation_witness.rs::lifecycle_felt`/`epoch_felt`): the lifecycle limb folds the
   variant discriminant + payload so distinct states commit distinctly
   (`lifecycle_felt_separates_states`); the rotated trace builder populates them and
   the differential asserts producer == trace for both. The REGEN-TO-DEFAULT that
   moves these onto the LIVE wire (replacing the v1 columns) remains the flip's act
   (§3 steps 2-4) — staged-additive today, v1 untouched.
6. ~~**GATE 0 re-measure** after the regen (the staged probe measures the block
   shape only).~~ **MEASURED green, this lane**: the per-effect GATE figure is the
   transfer IR-v2 size (`effect_vm_ir2_size_measure`), which the staged additive regen
   does NOT move — v1 `350.5 KiB` → IR-v2 `120.4 KiB` (ratio 0.344, -65.6%), well under the
   350.5 KiB ceiling. The rotated cohort's own block-shape adds the +125-col appendix only
   when it graduates to the live wire (the flip), where it re-measures against the flipped
   per-effect baseline.
7. **The 3-verb circuit descriptors** (gated on the executor rotation —
   `UNIVERSAL-MAP-ROTATION.md` §2.3; never before it).
8. ~~**cell ≡ circuit rotated differential**~~ **LANDED THIS LANE (staged)**
   (`circuit/tests/effect_vm_rotation_flip.rs`): the producer's limbs derived from the
   real executed turn's `RecordKernelState` EQUAL the limbs the circuit trace carries
   — the welded scalars (`r0↔balance_lo` … `cap_root`) on the before block, the
   witness-carried limbs (`cells_root` · map roots · `lifecycle` · `epoch` ·
   `committed_height` · `iroot`) on both blocks, and the producer's
   independently-computed `wire_commit(before)` == the row-0 trace `STATE_COMMIT`
   carrier. The LIVE-WIRE differential (cell `compute_canonical_state_commitment` v9
   == circuit) lands with the cell-context bump at the flip (§4).
9. **Heap-caveat runtime discharge** — the executor leg of the widened operand:
   discharge heap-domain entries at run time the way `verify_slot_caveat_manifest`
   discharges slot entries (the semantics are already pinned: `tagHeapAtom` →
   `HeapAtom.lift k` → `evalHeap`, `EffectVmEmitRotationCaveat.lean` §5; the named
   premise is `HeapCaveatRuntimeDischarge`). At the flag-day the staged 29-felt
   manifest replaces the live 25-felt slot manifest in the regenerated PI region.
