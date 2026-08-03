# The faithful state commitment & the cap-write keystones

What this IS at HEAD. Every Merkle-root component of the deployed rotated state
commitment is a faithful **8-felt (~124-bit)** binding — matching the system's
own ~130-bit FRI/STARK soundness floor, never a lossy ~31-bit 1-felt fold — and
the **cap-write family** is closed: every cap-writing
effect rides a shape-matched, circuit-forced keystone descriptor. The law
itself is [`docs/FAITHFUL-COMMITMENT-LAW.md`](../FAITHFUL-COMMITMENT-LAW.md); this
page grounds the deployed realization at file:line. Every load-bearing claim below
is cited to Rust file:line or a Lean `Module.decl`.

Companions: [`circuit.md`](circuit.md) (the prove/verify crates),
[`cells.md`](cells.md) (the cell-side commitment), [`lean-circuit.md`](lean-circuit.md)
(the soundness apex the keystones feed).

## Geometry — the limb regions at HEAD

| Const | Value | Location |
|---|---|---|
| `NUM_PRE_LIMBS` | **178** | `circuit/src/effect_vm/trace_rotated.rs:96` |
| `V9_NUM_PRE_LIMBS` | **178** (cell-side twin) | `cell/src/commitment.rs:757` |
| `B_SPAN` | **239** | `circuit/src/effect_vm/trace_rotated.rs:101` |
| `N_ROT_SITES` / `GRAD_ROT_WIDTH` | **134** / **1647** | `circuit/src/effect_vm/trace_rotated.rs:132/:138` |
| `WIDE_NUM_CARRIERS` / `WIDE_WIDTH` | **60** / `GRAD_ROT_WIDTH + 960` = **2607** | `trace_rotated.rs:4064/:4071` (const-asserted `178 → 60` at `:4084-4102`) |
| `CHIP_RATE` | **16** | `circuit/src/descriptor_ir2.rs:299` |
| `CHIP_NODE8_ARITY` | **16** | `circuit/src/descriptor_ir2.rs:322` |

The regions (the absorption order Lean pins as `preLimbsAt`, `preLimbsAt_length =
178`): base limbs `0..=37` — cells_root, r0..r23, the cap/nullifier/commitments/
heap root lane-0s, lifecycle/epoch/height/disc, perms/vk/mode/fields_root, and
`revoked_root` = base limb 37 (the credential-revocation accumulator root — the
base widen every limb index ≥ 37 shifts around); faithful completion lanes
`38..=88` (perms/vk/cap/heap/fields lanes 1..7 + the three accumulator
completion groups + revoked_root's `82..=88`); carrier-material octets
`89..=112`; the flat-fields`[0..7]` completion octets `113..=168` (`113 + 7·i`,
the `field_limbs8` split closing the last degraded felt); circuit-only
cells-completion `169..=175` (zero in the flat producers, filled by the
createCell trace generator); pads `176..=177` — landing the wide body at
`174 = 58×3` clean (`trace_rotated.rs:92-96`,
`turn/src/rotation_witness.rs:62-71`).

## The node8 primitive — ONE hash gadget under all six roots

The shared arity-16 compression `perm(L8 ‖ R8)[0..8]` (8-felt in, 8-felt out, no
tag lane, no lane-0 squeeze):

- **Rust**: `cap_node8` (`circuit/src/cap_root.rs:149`; `CAP_DIGEST_W = 8`,
  `cap_root.rs:134`; `CanonicalCapTree` with 8-felt levels, `cap_root.rs:313`);
  `heap_node8` (`circuit/src/heap_root.rs:566` — "The IDENTICAL compression
  `cap_root::cap_node8` commits — cap/heap/fields share this ONE node8 lane",
  `heap_root.rs:561`; `HEAP_DIGEST_W = 8`, `:548`; `CanonicalHeapTree8`, `:728`;
  `compute_canonical_heap_root_8`, `:624`; `recompose_membership_8`, `:690`).
- **Chip realization**: the node8 lookup tuple `[16, L8, R8, out8]`
  (`circuit/src/descriptor_ir2.rs:1940`), all 8 output lanes bound
  (`CHIP_OUT_LANES = 8`, `descriptor_ir2.rs:2053`), boolean-gated selector.
- **Lean**: the width-agnostic Merkle spine `CapMerkleGeneric` (`StepG`
  `CapMerkleGeneric.lean:30`, `recomposeG` `:39`, the injectivity keystone
  `recomposeG_inj_of_path` `:51`) instantiated by the 8-felt schemes:
  `Cap8Scheme` (`DeployedCapTree.lean:637`), `nodeOf8` (`:667` — "BYTE-IDENTICAL
  to `cap_root.rs::cap_node8`"), **`nodeOf8_injective`** (`:679`,
  `#assert_axioms` at `:934`), `heapNodeOf8_injective`
  (`DeployedHeapTree.lean:71`), `fieldsNodeOf8_injective`
  (`DeployedFieldsTree.lean:75`). The CR carrier is `Compress8CR`
  (`DeployedCapTree.lean:630`) — a Prop hypothesis, never an axiom.

## The six roots — deployed keystone descriptors + apex pins

Each root's write is FORCED by a shape-matched after-spine/insert descriptor whose
`Rfix` position the assembled apex quantifies over (registry `v3RegistryHeap`,
`metatheory/Dregg2/Circuit/CircuitSoundnessAssembled.lean:141`, length 61 `:285`):

| Root | Keystone descriptor | Shape | Keystone theorem | Apex pin |
|---|---|---|---|---|
| cap_root | `effCapOpenWriteV3` / `effCapInsertV3` / `effCapRemoveV3` (`CapOpenEmit.lean:855/:931/:950`) | update / insert / remove (next section) | `effCapOpenWriteV3_forces_write8` (`CapOpenEmit.lean:2282`) + the insert/remove twins | `Rfix 12` (attenuate) + the family pins below |
| heap_root | `effHeapWriteV3` (`HeapOpenEmit.lean:400`) | update-at-key | `heapOpen_writesTo8` (`HeapOpenEmit.lean:223`) | `Rfix 56`, pos 45 (`CircuitSoundnessAssembled.lean:470`) |
| fields_root | `effFieldsWriteV3` (`FieldsOpenEmit.lean:384`) | update-at-key | `fieldsOpen_writesTo8` (`FieldsOpenEmit.lean:218`) | `Rfix 39`, pos 55 (`:485`) |
| nullifier_root | `effAccumInsertV3` … `(some SEL_NOTE_SPEND)` | sorted-INSERT | `accumInsert_writesTo8` (`AccumulatorInsertEmit.lean:117`) | `Rfix 27`, pos 56 (`:500`) |
| commitments_root | `effAccumInsertV3` … `none` | sorted-INSERT | + `accumInsert_writesTo8_setGrows` (`:134`) | `Rfix 28`, pos 57 (`:514`) |
| cells_root | `effAccumInsertV3` … `none` | sorted-INSERT | (same keystone) | `Rfix 17`, pos 58 (`:530`) |

`#assert_axioms` on the insert pins at `CircuitSoundnessAssembled.lean:840-843`;
the capstone footprint is ⊆ `{propext, Classical.choice, Quot.sound}` (`:83`).

### The INSERT-shaped accumulator keystone

`effAccumInsertV3` (`AccumulatorInsertEmit.lean:243`) is INSERT-shaped, not
update-shaped: the before-root opens a genuine **non-membership bracket** (the
sorted-tree gap witness) and the after-root is the **spliced membership** — the
twin pair `nonMembership_sound8` (`SortedTreeNonMembershipHeap8.lean:149`,
`#assert_axioms` `:184`) + `update_sound8` (`:164`). Trace-forced consumers:
`effAccumInsertV3_forces_afterMembership` (`AccumulatorInsertEmit.lean:340`),
`effAccumInsertV3_forces_write8` (`:402`).

**The selector-gated KEY/VALUE binds** (the noteSpend residual close): the bind
combinator `bindGateI` (`AccumulatorInsertEmit.lean:183`) takes `sel : Option Nat`
— `none ⇒` the unconditional `eqGate`, `some s ⇒ sel·(leaf−col) = 0` (active on
the firing row, vacuous on padding); `keyBindGateI` `:218`, `valueBindGateI`
`:223`, forced by `bindGateI_forces` `:192`. noteSpend instantiates
`some SEL_NOTE_SPEND` (`CircuitSoundnessAssembled.lean:240`) because its
`valueCol = NOTE_VALUE_LO` is per-row economically constrained (must be 0 on
padding — irreconcilable with an unconditional per-row bind); noteCreate /
createCell pass `none` (`:247`, `:256`). MEMBERSHIP + rootPin welds stay
unconditional in all three.

### The Rust producers (the genuine node8 fill)

The rotated trace producers fill genuine `CanonicalHeapTree8::root8()` — never a
lane-0 squeeze, never a `[x; 8]` replicate — into both rotated blocks, and the
two flat pre-limb twins (`cell/src/commitment.rs::compute_rotated_pre_limbs`,
`commitment.rs:1061`; `turn/src/rotation_witness.rs::produce`,
`rotation_witness.rs:404-495`) carry the SAME faithful 8-felt fills byte-identically:

- nullifier: lane 0 = limb 26 ‖ lanes 1..7 = limbs 68..74
  (`trace_rotated.rs:1521-1531`, `commitment.rs:1130`);
- commitments: lane 0 = limb 27 ‖ 75..81 (`trace_rotated.rs:1718-1728`);
- cells: lane 0 = limb 0 ‖ 169..175 — the circuit-only completion group, kept
  off revoked_root's `82..=88` (`trace_rotated.rs:1629-1642`; ZERO in the flat
  twins, filled by the createCell trace generator);
- revoked_root: lane 0 = limb 37 ‖ 82..88 — the credential-revocation
  accumulator, opened in-circuit against the COMMITTED root
  (`trace_rotated.rs:1820-1830`, `commitment.rs:1176-1185`);
- cap: 25 ‖ 52..58, heap: 28 ‖ 59..65, fields: 36 ‖ 66,67,19..23, authority
  digest: 24 ‖ 12..18, perms: 33 ‖ 38..44, vk: 34 ‖ 45..51, and the
  flat-fields octets lane 0 = `4 + i` ‖ `113 + 7·i .. +6` — all through the
  `Faithful8` wall's `write_lanes` (`commitment.rs:1061-1185`).

## The cap-write family close — all 8 cap-writing effects on shape-matched keystones

**Why three shapes:** the witness heaps are native `CanonicalHeapTree8`
(`circuit/src/heap_root.rs:728`), so a scalar **arity-2 cap map-op is
shape-UNSAT for an honest prover** ("the scalar map-op is GONE from the deployed
wrapper (it was shape-UNSAT against the native-8-felt witness heaps)",
`sdk/src/full_turn_proof.rs:7307`). And UPDATE-at-key alone cannot carry the
family: delegate/introduce/delegateAtten INSERT a fresh cap key and
revokeDelegation REMOVEs one — both change the cap key-set, so there is no
shared before/after path for an update spine. Hence three keystone shapes
(INSERT, REMOVE, UPDATE), with all 8 cap-writing effects on shape-matched
wrappers.

| Effect | Wrapper (all in `CapOpenEmit.lean`) | Keystone | Rfix pin (`CircuitSoundnessAssembled.lean`) |
|---|---|---|---|
| delegate | `delegateWriteCapOpenV3` (`:1008`) | `effCapInsertV3` | `Rfix 1`, pos 46 (`:582`) |
| introduce | `introduceWriteCapOpenV3` (`:960`) | `effCapInsertV3` | `Rfix 10`, pos 47 (`:591`) |
| delegateAtten | `delegateAttenWriteCapOpenV3` (`:1048`) | `effCapInsertV3` | `Rfix 11`, pos 48 (`:594`) |
| spawn | `spawnWriteCapOpenV3` (`:1023`) | `effCapInsertV3` | `Rfix 19`, pos 52 (`:617`) |
| revoke / revokeDelegation | `revokeDelegationWriteCapOpenV3` (`:971`) | `effCapRemoveV3` | `Rfix 2` / `Rfix 14`, pos 49 (`:588`, `:598`) |
| revokeCapability | `revokeCapabilityWriteCapOpenV3` (`:986`) | `effCapRemoveV3` | ⚠ `Rfix 24` still pins the authority-only `revokeCapabilityCapOpenV3`, pos 41 (`:610`) — see residuals |
| attenuate | `attenuateCapOpenEffV3` (`:1082`) | `effCapOpenWriteV3` | `Rfix 12` (`:553`) |
| refreshDelegation | `refreshDelegationWriteCapOpenV3` (`:996`) | `effCapOpenWriteV3` | `Rfix 55`, pos 50 (`:603`) |

The three shapes:

- **INSERT** (`effCapInsertV3`, `CapOpenEmit.lean:931` = `effCapOpenV3` + the 8
  AFTER cap-root welds `afterCapRootWelds` `:918`): keystones `capInserts8`
  (`CapInsertEmit.lean:82`), **`capInsert_writesTo8`** (`:125` — genuine
  `nonMembership_sound` bracket + `MembersAt8` afterRoot + `update_sound`),
  `capInsert_writesTo8_setGrows` (`:142`), trace-forced
  `effCapInsertV3_forces_afterMembership` (`:241`) /
  `effCapInsertV3_forces_write8` (`:286`). The Rust witness is
  `CanonicalCapTree::insert_witness` (`circuit/src/cap_root.rs:780`) — fail-closed
  on sentinel/present key, pred/succ non-membership bracket, `debug_assert`
  recompose = rebuilt root.
- **REMOVE** (`effCapRemoveV3`, `CapOpenEmit.lean:950` = base + the 8 BEFORE
  welds `beforeCapRootWelds` `:939`): keystones `capRemoves8`
  (`CapRemoveEmit.lean:79` — tombstone zero-fold via `sortedRemove`),
  **`capRemove_writesTo8`** (`:122`), `capRemove_writesTo8_setShrinks` (`:139`),
  `effCapRemoveV3_forces_write8` (`:280`). Rust:
  `CanonicalCapTree::remove_witness` (`cap_root.rs:832`) — BEFORE membership
  path, then `new_root = recompose_membership(CAP_ZERO8, …)` — the tombstone
  zero-fold (`:848`), matching the cell-side tombstone semantics
  ([`auth.md`](auth.md) revocation section).
- **UPDATE** (`effCapOpenWriteV3`, `CapOpenEmit.lean:855`, the §12-relocated
  block `:774`): the arity-7 after-spine — §11
  (`CapOpenEmit.lean:2101` ff.) is the pure keystone (two node8 spines sharing a
  path), §12 (`:2175` ff.) the wiring (`effCapOpenWriteV3_afterCore` `:2195`,
  `effCapOpenWriteV3_forces_write8` `:2282`).

**Rust routing**: `build_effect_vm_cap_open_leg` (`sdk/src/full_turn_proof.rs:2894`)
branches by shape — `attenuate_after_spine` (`:2945`, attenuate + refresh),
`insert_after_spine` (`:2962`, delegate/introduce/delegateAtten/spawn),
`remove_after_spine` (`:2983`, revokeDelegation + revokeCapability). The
effect-kind → route table is `cap_open_route_for_run`
(`sdk/src/full_turn_proof.rs:2195`); the light-client verify allow-list is
`turn/src/executor/proof_verify.rs:138-159`. The three descriptor registries
(`circuit/descriptors/rotation-v3-staged-registry.tsv` + the wide + umem-welded
twins) pin the deployed keystone descriptors; no arity-2 map-op `_forces_write`
theorem exists (the shape is UNSAT against the 8-felt witness heaps).

**Teeth**: witness unit teeth in `circuit/src/cap_root.rs` —
`insert_witness_recomposes_rebuilt_root_and_brackets` (`:1035`),
`remove_witness_matches_tombstone_root` (`:1074`),
`revocation_witness_rejects_fabricated_slot` (`:1345`),
`membership_witness_rejects_forged_leaf` (`:1426`),
`sparse_matches_dense_at_depth_16` (`:1576`). Prove+verify leg tests in
`sdk/src/full_turn_proof.rs` — delegate `:9068`, introduce `:9464`,
delegateAtten `:9716`, spawn `:9503`, revokeCapability route `:8099`, refresh
`:8317`; the no-silent-forge REMOVE tooth
`write_cap_open_wrapper_requires_cap_tree_write_witness_no_silent_forge`
(`:7096`); the forge-masked harness `run_insert_after_spine_prove_verify_forge_masked`
(`:8628`); domain-2 gauntlets `sdk/tests/wide_umem_weld_domain2_siblings.rs`,
`sdk/tests/wide_umem_weld_matrix_gauntlet.rs`.

## The standalone DSL-p3 cap-membership leg (8-felt, no lane-0)

The standalone DSL-AIR cap-membership leg binds the GENUINE 8-felt cap_root:
`ConstraintExpr::MerkleHash8 { output_cols[8], left_cols[8], right_cols[8] }` —
the multi-output node8 gadget in `circuit/src/dsl/dsl_p3_air.rs` (input state
`L8 ‖ R8` seeded into all 16 lanes, byte-identical to `cap_node8`,
`dsl_p3_air.rs:364`; **all 8 genuine permutation output lanes bound — "NOT
eight copies of lane 0"**, `dsl_p3_air.rs:586`). The leg is
`circuit/src/dsl/cap_membership.rs` (`cap_membership_circuit_descriptor` `:91`,
the `MerkleHash8` fold `:133`, descriptor `"dregg-cap-membership-dsl-v2-node8"`
`:200`) with a **16-felt PI vector `[leaf_digest(8) ‖ cap_root(8)]`**
(`cap_membership.rs:206`); the SDK emits and re-verifies it
(`verify_cap_membership_p3`, `sdk/src/full_turn_proof.rs:48`, posture at `:670`).

## The gate (the law's enforcement) — LOCAL, not GitHub

`.ast-grep/rules/faithful-commitment-felt.yml` carries exactly two rules:
`degraded-felt-commitment` (`:23` — the `fold_bytes32_to_bb($_)` patterns) and
`replicated-felt-commitment` (`:62` — the `[$X; 8]` replicate, with
`[0;8]`-style constants excluded). `scripts/check-no-degraded-felt.sh` runs them
over the commitment producers with an inline `// ast-grep-ignore` allowlist;
[`docs/FAITHFUL-COMMITMENT-LAW.md`](../FAITHFUL-COMMITMENT-LAW.md) is the law text.
The script DERIVES its scan scope from the rules' `files:` blocks and refuses
(exit 2) if the two rules disagree, so the scope has one authority. That scope is
**eight** producers as of 2026-07-31, not the original three.

It runs from `scripts/local-gates.sh:142` (the `no-degraded-felt` row, invoked
`--rev HEAD`), **not** from GitHub Actions: the `no-degraded-felt` job was one of
nine deleted from `.github/workflows/ci.yml` on 2026-07-29 because each duplicated
a local-gates row character-for-character (manifest at `ci.yml:815`). Local is
the stricter bar. With `main` unprotected, a red here reports and blocks nothing
automatically.

**⚑ The gate is RED at HEAD, and has never passed (measured 2026-08-02).**
`scripts/check-no-degraded-felt.sh --rev HEAD` — a clean extract of the commit,
not the shared working tree — exits 1 with two errors, both real production
degradations left un-suppressed on purpose:

- `cell/src/commitment.rs:561`, `cap_root::fold_bytes32(cap.target)` — the
  cap-tree leaf's target field in the DEPLOYED canonical state commitment.
- `node/src/turn_proving.rs:1159`, `nullifier_to_field` — its image IS
  `PI[NOTESPEND_NULLIFIER]`, and the key the double-spend freshness search and
  the `canonical_spent_nullifier_set` consensus anchor run on.

Repairing either is a Lean-authored AIR change plus a VK epoch and a re-genesis
(`CapLeaf` is a 7-field Poseidon2 leaf opened in-circuit; `PI[NOTESPEND_NULLIFIER]`
is an AIR public input), not a Rust edit. Earlier green verdicts predate the two
widenings that made these visible — scope 3→8 files on 2026-07-31, the alias
names `fold_bytes32` / `fold_value32` on 2026-08-01 — so they were green under a
narrower rule. The gate also cannot yet tell a net-new fold from these two: there
is no ratchet baseline.

The type-level capstone is BUILT: `dregg_circuit::Faithful8`
(`circuit/src/faithful8.rs:83`) — a private-field newtype whose only public
constructors are the faithful conversions (`from_bytes32`, `from_field_limbs8`,
`from_wire_commit_chip`, the 30-bit `from_canonical_key`; the raw `from_root8`
is crate-private to the tree/commit modules) — so a degraded octet is a type
error at the producer, not a lint finding
(`docs/FAITHFUL-COMMITMENT-LAW.md:100`). (Distinct from the Lean
`DeployedFaithful8`, `DeployedCapTree.lean:730`.)

## Honest residuals (named, none hidden)

1. **The setField[0..7] value8 weld — a completeness residual, STAGED.** The two
   flat producers emit the faithful `Faithful8::from_field_limbs8` 8-lane split
   (lane 0 at the welded limb `4 + i`, lanes 1..7 at the completion lanes
   `113 + 7·i .. +6`); the no-degraded-felt gate reports **zero `fields[0..7]`
   entries** — that residual is genuinely gone from the producers, though the gate
   as a whole is red on the two unrelated sites named above —
   and the shared value wrap freezes all 56 completion lanes on a value turn
   (`rotateV3FrozenAuthority_rejects_fields_forge`,
   `Emit/EffectVmEmitRotationV3.lean:3213`, `#assert_axioms`-clean). The DEPLOYED
   setField registry members are `withSelectorGate SEL_SET_FIELD (v3OfFrozen
   (setFieldTickFace slot))` — the freeze-**ALL** variant, which freezes the
   WRITTEN slot's completion lanes too (`v3RegistryBare`,
   `Emit/EffectVmEmitRotationV3.lean:5798-5799`). So the deployed setField's high
   224 bits are FROZEN to the pre-state (a forge of them is UNSAT — no
   ledgerless silent-forge, `circuit/tests/setfield_completion_lane_forge.rs`),
   at the cost of an honest LARGE-value write being unprovable — a
   **completeness** residual, not a soundness hole. The close is STAGED beside
   the deployed VK: the freeze-EXCEPT member (`setFieldV3 slot =
   v3OfFrozenSetField slot …`, `:3350`) frees the written slot's 7 completion
   lanes, and `setFieldValue8V3` (`:5482`) publishes them as 7 tail PIs bound to
   the declared value8, in the staged registry `v3RegistrySetFieldValue8`
   (`:5375` §VALUE8). Adoption is the gated VK-epoch re-point.
2. **`transferCapOpenTB` — the ONE load-bearing ~31-bit LC surface left.**
   `compute_canonical_state_commitment_v9_felt8` (`cell/src/commitment.rs:1358`;
   32-byte form `_v9_8`, `:1377`) is the deployed end-to-end binding — the
   executor anchors the 16 wide commit PIs to the trusted 8-felt commits
   (`turn/src/executor/proof_verify.rs:609-611`, `:1125-1133` — "the ~31-bit
   1-felt waist is GONE"). The 1-felt `_v9_felt` (`:1324`) has test/bench
   callers only (`:1355`). What genuinely remains 1-felt on the LC wire:
   `transferCapOpenTB` — the sole cap-open key with NO proven wide twin (its
   `effCapOpenV3TB` host carries two extra turn-identity columns, so the cohort
   weld excludes it), and wide membership is read straight off the proven wide
   registry, so it alone stays on the 1-felt V3 route
   (`sdk/src/full_turn_proof.rs:2690-2712`). Closing it = the transferCapOpenTB
   wide-twin grind.
3. **`BUS_FACT` is not gone** — the node8 map-op chain rides its dedicated chip
   lanes, but the legacy arity-2 fact bus is still defined and active for the
   remaining scalar map-op chains (`circuit/src/descriptor_ir2.rs:358`, the
   `fact_bus.table_entry` at `:2816`).
4. **revokeCapability's apex pin lags its deployed route** — `Rfix 24` pins the
   authority-only `revokeCapabilityCapOpenV3` (pos 41,
   `CircuitSoundnessAssembled.lean:610`), while the deployed prover proves the
   REMOVE write wrapper whenever the node supplies the c-list witness, with a
   *named* authority-only fallback on an empty c-list
   (`sdk/src/full_turn_proof.rs:2385-2396` — "An empty c-list falls back to the
   authority-only `key` (named, not a silent forge)"). The Lean write wrapper +
   its `ClosureAll` rung exist (`revokeCapability_closedLog_capOpenSat`,
   `ClosureAll.lean:971`); moving the `Rfix 24` pin onto the write wrapper is the
   open apex-registry step.
5. **The terminal crypto carriers** — `StarkSound`
   (`CircuitSoundness.lean:482`), `Poseidon2SpongeCR`
   (`Poseidon2Binding.lean:178`), `Compress8CR` (`DeployedCapTree.lean:630`): the
   FRI/STARK-soundness and Poseidon2-CR floor, carried as classes/Prop
   hypotheses. Zero raw `axiom` declarations in `Dregg2/Circuit/`.
