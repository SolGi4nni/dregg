# V1-DELETION-MANIFEST — the isolated-component catalog (C7 grep-zero plan)

*(2026-06-14, during THE FLIP. This is the precise inventory of the legacy v1
effect-VM proof component — what gets DELETED at C7, what must be MIGRATED first,
what is test-only, and the grep-zero checklist. Built so C7 is a mechanical
Workflow fan-out the instant the VK epoch lands green. Cross-ref:
`docs/ROTATION-CUTOVER.md` §EXEC.3 (the C7 deletion list) + `HORIZONLOG.md` ⚑⚑
PRE-FLIP GATE. Symbol counts are file-counts from the 2026-06-14 grep baseline.)*

## The boundary, in one line

v1 = the IR-v1 / 186-column hand-AIR effect-VM proof (`EffectVmAir` /
`EffectVmP3Air` / `EffectVmP3Proof` / `generate_effect_vm_trace` / the v1
`bilateral_aggregation_air` / `CutoverFallback`). Rotated = the IR-v2 R=24
multi-table `Ir2BatchProof` via the Lean-emitted descriptor interpreter
(`descriptor_ir2` + `trace_rotated` + the v3 registry). The flip makes rotated
the default; C7 deletes v1. The two share `circuit/src/lean_descriptor_air.rs`
infra (`LeanExpr`/`JsonCursor`/`parse_expr`/…) — those STAY (bucket D).

## Bucket A — PURE v1, DELETE at C7 (no rotated-path role)

| target | where | refs | note |
|---|---|---|---|
| `EffectVmP3Air` | `circuit/src/effect_vm_p3_full_air.rs` | 6 files | the full 186-col AIR; 30 self-refs in-file |
| `EffectVmP3Air` shape-mirror | `circuit/src/effect_vm_p3_air.rs` | — | 5 `ACTIVE_BASE_COUNT` refs |
| `EffectVmAir` + `EFFECT_VM_WIDTH=186` | `circuit/src/effect_vm/air.rs` | 36 files | the bulk is `effect_vm/tests.rs` (bucket C) |
| `EffectVmP3Proof` + `prove_effect_vm_p3` | `circuit/src/…` (+1 sdk) | 7 / 8 files | the v1 SDK effect-vm leg type — **BUT ALSO the recursion/aggregation LEAF type** (`proof_forest.rs:280 ForestNode.proof`, `joint_turn_aggregation.rs:130/197/213 DescriptorParticipant.proof`); the `rotated` leg is only ADDITIVE there → its deletion is GATED on the bucket-F 5-file mandatory-rotated-leaf cutover, NOT a pure delete |
| `BilateralAggregationAir` block | `circuit/src/bilateral_aggregation_air.rs` | 4 files | KEEP the FILE for `CrossSideExistenceAir`/`BundleTreeFoldAir` (bucket D) — delete only the `BilateralAggregationAir` + `AggregationInnerRow`/`AGG_WIDTH`/`build_aggregation_trace` block |

> **CORRECTION (C7 fix-round-3, 2026-06-14, deep re-trace).** `generate_effect_vm_trace` was
> listed here as "PURE v1, DELETE." **That is WRONG and would REGRESS the verified-green rotated
> path.** It is the SHARED canonical trace+PI generator, NOT the v1 old-prover. The rotated leg is
> literally BUILT ON IT — `effect_vm/trace_rotated.rs:203` (`generate_rotated_effect_vm_trace`)
> opens with `let (mut trace, pis) = generate_effect_vm_trace(...)` ("the v1 reference trace + PIs —
> the byte-identical live machinery") and widens each row with the rotated appendix. It is ALSO the
> generator for the conservation net_delta, the FRI-free `revalidate_turn_self_sovereign`, and EVERY
> node post-state-commitment derivation (`turn_proving.rs:526/688/821`, `mcp.rs`, `api.rs`). Reaching
> grep-zero on it in recursion builds requires RE-DERIVING the entire proven 311-column rotated trace
> generator from scratch (with fresh differential validation) — a multi-week rewrite that REGRESSES
> the current green rotated machinery. It is moved to **Bucket E** below. The pure-v1 OLD-PROVER
> symbols (`EffectVmP3Air`/`EffectVmAir`/`EffectVmP3Proof`/`prove_effect_vm_p3`/`EFFECT_VM_WIDTH`/
> `CutoverFallback`) remain deletable IN PRINCIPLE — but only AFTER bucket F (the recursion-leaf
> cutover) AND the heterogeneous-turn coverage (Bucket G) land, else the deletion ships RED.
| `CutoverFallback` | `sdk/src/full_turn_proof.rs` | 2 files | 8 in-file refs + 1 test; retired by Wall A |

## Bucket B — MIGRATE first, then the v1 ref dies (live consumers)

| consumer | where | status |
|---|---|---|
| full-turn prove (vk_hash / conservation / unconditional trace) | `sdk/src/full_turn_proof.rs` | **Wall A — LANE LIVE** (`a744069d`) |
| bilateral verify reads v1 PI slice | `turn/src/aggregate_bilateral_prover.rs` + `witnessed_receipt.rs` | **Wall B — LANE LIVE** (`a744069d`) |
| FLOW-B freshness arm | `node/src/blocklace_sync.rs` + `turn_proving.rs` | **Wall C — LANE LIVE** (`a9fe8d40`) |
| node WR producer populates `bilateral_schedule` | `node/src/blocklace_sync.rs` `materialize_blocklace_artifacts` | **MAIN LOOP, deferred til Wall C lands** (node/ collision) |
| **#103 executor verify** `verify_and_commit_proof` off bespoke `EffectVmAir` → rotated `Ir2BatchProof` (+ retire `air.rs:1365-1374` legacy cap arm) | `turn/src/executor/proof_verify.rs` (16 refs) | **MAIN LOOP, rides the VK epoch — do AFTER walls land** (must match the finalized rotated leg) |
| sovereign prove path | `sdk/src/cipherclerk.rs` (8) | confirm rotation-threaded or rotation:None-clean |
| MCP / API / atomic produce-verify surfaces | `node/src/{mcp.rs(18),api.rs(4),prove_pool.rs}`, `turn/src/executor/{atomic.rs(6),mod.rs,execute.rs,authorize.rs}`, `turn/src/turn.rs` | mostly rotation:None-clean per §EXEC.3 "(a) most need no edit" — confirm each at C7 prep, thread only the load-bearing ones |

## Bucket C — TEST harnesses (delete WITH their targets at C7)

`circuit/src/effect_vm/tests.rs` (65 `EffectVmAir` refs) · the ~40 v1 harnesses
named in §EXEC.3: `circuit/tests/effect_vm_descriptor_cutover_harness.rs`,
`effect_vm_{grant,attenuate,revoke}_non_amp.rs`, the v1 call-sites in
`effect_vm_p3_descriptor_differential.rs` / `turn_revalidation_vs_prove.rs`. The
differential harnesses (v1-vs-rotated) lose their reason to exist once v1 is gone.

## Bucket D — KEEP (shared infra / rotated-path deps in the same files)

`circuit/src/lean_descriptor_air.rs` — DELETE only `EffectVmDescriptorAir::eval`
+ `prove_vm_descriptor`/`verify_vm_descriptor` (v1 surface); KEEP
`LeanExpr`/`VmConstraint`/`RangeSpec`/`EffectVmDescriptor`/`i64_to_babybear`/
`const_to_expr`/`JsonCursor`/`parse_expr` (imported by `descriptor_ir2.rs`).
`bilateral_aggregation_air.rs` `CrossSideExistenceAir` + `BundleTreeFoldAir` (the
CG-5 / proof-of-proofs; they do NOT read `effect_vm::pi`; retire in a later Lean lane).
The wasm path keeps v1 UNTIL the Option-A wasm-rotated prover lands (then it joins bucket A).

## Bucket E — SHARED canonical generator, NOT deletable in recursion builds (the scope-correction)

`generate_effect_vm_trace` (`circuit/src/effect_vm/trace.rs`, ~145 src refs). It is NOT v1; it is the
ONE trace+PI generator the whole system shares, INCLUDING the rotated leg (which is a v1-trace
SUPERSET — see the CORRECTION box above). It cannot reach grep-zero in recursion builds without a
from-scratch re-derivation of the proven 311-column rotated generator. **Therefore `generate_effect_vm_trace`
is REMOVED from the C7 grep-zero target for recursion builds.** Its eventual removal is a future
"rotated generator stops being a v1-superset" lane (re-derive the rotated trace natively + new
differential), not part of C7. (It is also the wasm `not(recursion)` floor's generator — see the
Option-A residual.)

## Bucket F — recursion/aggregation LEAF cutover, MUST precede the `EffectVmP3Proof` delete (5 files)

`proof_forest.rs::ForestNode.proof`, `joint_turn_aggregation.rs::DescriptorParticipant.proof` (×3
build sites), `ivc_turn_chain.rs`, `joint_turn_recursive.rs`, `recursive_witness_bundle.rs` all carry
`EffectVmP3Proof` as the recursion LEAF with the `rotated: Option<RotatedParticipantLeg>` only
ADDITIVE (the in-file comment says the rotated leg becomes mandatory only "once present everywhere" —
NOT YET). Deleting `EffectVmP3Proof` FORCES first: make the rotated leg MANDATORY in all five, drop
the v1 field, and fix every host-admission read. This is soundness-bearing (the leaf type is what the
recursion verifier admits), so it is its own lane — not part of the bucket-A leaf drop.

## Bucket G — HETEROGENEOUS / non-synthetic finalized-turn coverage (the ARGUS-preserving prereq)

The v1 fallback leg in `sdk/src/full_turn_proof.rs:1185-1202` (`prove_effect_vm_with_cutover` →
`EffectVmP3Proof`) is the AUDITED prover for any finalized turn the node passes `rotation: None` for:
a HETEROGENEOUS-per-actor turn (e.g. one agent does Transfer AND SetField — `cohort_ok` fails at
`turn_proving.rs:380-387/468-479` because the rotated AIR is structurally ONE-descriptor-per-proof),
a NON-synthetic actor cell (`cell_is_synthetic_shaped`/`cell_matches_v1_prestate` gate,
`turn_proving.rs:353-357/445-448`), or a multi-spend turn. These ARE reachable live turns (a `Turn`
proves as ONE finalized turn over `signed_turn.turn.agent` with the FULL `call_forest.total_effects()`
projected onto that actor — `blocklace_sync.rs:2605-2722`; there is NO per-effect decomposition that
would make them vacuous). **Removing the v1 fallback without first building heterogeneous coverage
DROPS those turns' per-turn proof = an ARGUS light-client-unfoolability REGRESSION.** The PRESERVE
fix is multi-cohort CHAINED rotated proving: split the turn into maximal homogeneous cohort-runs,
prove each rotated (chaining `OLD_COMMIT`/`NEW_COMMIT` s0→s1→…→sN), attach N `effect-vm-rotated`
legs, and teach `verify_full_turn` (currently `.find(|sp| label==effect-vm*)` at
`full_turn_proof.rs:1688-1719`, hardcoded to EXACTLY ONE effect-vm leg) to COLLECT + chain-check them
(leg_k.OLD == leg_{k-1}.NEW; first.OLD == expected_old; last.NEW == expected_new; effects_hash /
net_delta re-derived across the chain) — a soundness-CORE prover + verifier + chained-witness-builder
change with its own differential proof (chain ≡ monolithic transition) and Lean re-emission review.
This is genuine multi-phase circuit+verifier work; it cannot land verified-green in one phase, and a
half-landed version (prover chains but verifier doesn't, or vice versa) is RED.

## The grep-zero checklist (run after C7; each must reach 0 in recursion-enabled builds)

```
EffectVmAir · EffectVmP3Air · EffectVmP3Proof · prove_effect_vm_p3
CutoverFallback · EFFECT_VM_WIDTH · ACTIVE_BASE_COUNT (v1 PI)
BilateralAggregationAir · AggregationInnerRow (v1)
```
**`generate_effect_vm_trace` is NOT in the recursion-build grep-zero target** (Bucket E — the shared
generator the rotated leg is built on). The `EffectVmP3Proof`/`prove_effect_vm_p3` zero is GATED on
Bucket F (recursion-leaf cutover) + Bucket G (heterogeneous coverage); deleting them before those is
RED. Caveat (the Option-A decision): the `#[cfg(not(feature="recursion"))]` wasm path keeps
`generate_effect_vm_trace` (3 wasm files) until the wasm-rotated prover lands — but since Bucket E
removed it from the recursion target, that residual is now purely the wasm-floor lane.

## Execution shape

**REVISED (fix-round-3): C7 is NOT a mechanical fan-out.** The bucket-A leaf drop cannot land green
on its own — `EffectVmP3Proof`/`prove_effect_vm_p3` are blocked by Bucket F (the 5-file recursion-leaf
cutover) AND Bucket G (heterogeneous/non-synthetic finalized-turn coverage), and `generate_effect_vm_trace`
is out of scope entirely (Bucket E). The honest sequence is: **(F)** make the rotated participant leg
mandatory in the 5 recursion files + drop the `EffectVmP3Proof` field + fix host-admission reads →
**(G)** build multi-cohort chained rotated proving + the `verify_full_turn` chain-check + the chained
differential → **(#103)** flip `proof_verify.rs` + `prove_pool.rs` off `EffectVmAir` → **then** the
bucket-A/C delete fan-out can run and reach grep-zero (minus Bucket E) green. F + G are
soundness-CORE, multi-phase, and need their own verified-green landings BEFORE any deletion. Doing the
deletion first ships RED.

**✅ DECIDED 2026-06-14 (ember): PRESERVE.** Bucket G is no longer a fork — ember settled it the only
dregg-coherent way: *"we need to build path-preserve for SURE. any other decision wouldn't be dregg."*
So C7 is gated on BUILDING chained heterogeneous + non-synthetic rotated proving (keeps every finalized
turn proven, ARGUS light-client unfoolability intact) — a multi-lane circuit+verifier campaign, no crypto
primitive, no further decision. WEAKEN (commit heterogeneous/non-synthetic turns proof-pending) is
rejected: it would silently narrow the per-turn-proof claim the whole system exists to make. The build
lane = `docs/PATH-PRESERVE.md` (the staged, persvati-green plan). The original framing, for the record:
PRESERVE keeps the guarantee, WEAKEN was the smaller code change but a real north-star regression.
(Gated on: the VK epoch landed green — v3Registry default + re-pin + #103 + notify + reseed — which it is.)
