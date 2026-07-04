# WELD-STATE — the grounded carrier-deployment / universal-fold weld map

*Grounded to git HEAD `956b8be93` (working tree clean; `origin/main` at `53a3b4336`,
local main ahead by 2). Written 2026-07-01. This is a READ-ONLY census: what is
built-and-committed vs what is the-emit-not-yet-run, so we weld the RIGHT thing.*

*EXTENDED 2026-07-02 at HEAD `bae447985` (14 commits past `956b8be93`): §1f (the
CAP-WRITE FAMILY CLOSE — landed since this map was written), plus inline
`[@bae447985]` corrections where the newer HEAD moved a line or sharpened a claim.
Everything marked `[@bae447985]` is re-verified against that HEAD; full grounding
in `docs/reference/faithful-commitment.md`.*

> Reconcile-first note. The two topic memories (`project-carrier-deployment-architecture.md`,
> `project-universal-fold-buff-lightclient.md`) are dated 2026-06-30/07-01 and their
> commit hashes are UNRELIABLE against HEAD — e.g. the memory calls `356f55b68` "the
> INSERT-shaped keystone accumInsert_writesTo8 + apex Rfix," but git shows `356f55b68`
> is a notecreate negative-tooth test commit. The memory prose describes branch states
> that got re-ordered on merge. Everything below is verified against the code at HEAD,
> not the memory.

---

## 0. TL;DR — the two-sentence state

The **faithful-state-commitment VK-epoch is DONE and on main**: all six committed roots
(cap · heap · fields · nullifier · commitments · cells) are deployed faithful 8-felt at
v11 geometry, `#assert_axioms`-clean, the accumulator-insert `noteSpend` residual closed.
The **carrier universal-fold mechanism is BUILT for all 7 carriers but DEPLOYED for only
one** (custom): the leaf + binding-node + negative-tooth + Lean refutation are committed
for every carrier, but the *third edge* (teeth == committed-authority in the deployed AIR)
+ the deployed-path wiring exist ONLY for custom. **The big bang is NOT fireable as one
shot yet** — the per-carrier Step-1 teeth-emit (the security-critical acceptance gate) and
the witness-socket generalization are unbuilt for the other six.

---

## 1. What the VK-epoch just landed + what it UNBLOCKED

The epoch that "just finished" is the **faithful state commitment** (the v9→v10→v11
geometry campaign). It widened the DEPLOYED per-cell state commitment from ~31-bit folds
to faithful 8-felt Merkle roots. This was the *precondition* the carrier bang was blocked
on: memory `project-carrier-deployment-architecture.md` §BLOCKER — "ANCHOR carriers to
FAITHFUL committed forms ONLY — never a 31-bit fold." Now the anchors are faithful.

### 1a. Geometry at HEAD (verified)

| Const | Value at HEAD | Location |
|---|---|---|
| `NUM_PRE_LIMBS` | **88** (v11) | `circuit/src/effect_vm/trace_rotated.rs:90` |
| `V9_NUM_PRE_LIMBS` | **88** | `cell/src/commitment.rs:702` |
| `B_SPAN` | **119** | `circuit/src/effect_vm/trace_rotated.rs:97` |
| `CAP_OPEN_SPAN` | **329** | `trace_rotated.rs:2273` |
| `WIDE_WIDTH` | `GRAD_ROT_WIDTH + 480` | `trace_rotated.rs:3341` `[@bae447985]` |

Path: `37 (v9) → 67 (v10, +8-felt state) → 88 (v11, +21 accumulator-8-felt lanes 67..87)`;
`B_SPAN 51 → 91 → 119`. (Two stale prose comments still say "67" / "37" —
`effect_vm_descriptors.rs:1961`, `effect_vm_rotation_flip.rs:58` — dead comments, not live
consts.)

### 1b. The six roots — all deployed faithful 8-felt

Each root is pinned by `rfl` in the apex registry `v3RegistryHeap`
(`metatheory/Dregg2/Circuit/CircuitSoundnessAssembled.lean`), forcing a faithful 8-felt
write/insert (never the lane-0 squeeze):

| Root | After-spine descriptor | Shape | Apex pin |
|---|---|---|---|
| cap_root | `effCapOpenWriteV3` (`CapOpenEmit.lean:585`) — `[@bae447985]` now ONE of THREE shapes; the full cap-write family (insert/remove/update, all 8 effects) is §1f | update / insert / remove | `Rfix 12` + the §1f family pins |
| heap_root | `effHeapWriteV3` (`HeapOpenEmit`) | update-at-key | `Rfix 56`, pos 45 |
| fields_root | `effFieldsWriteV3` (`FieldsOpenEmit`) | update-at-key | `Rfix 39`, pos 55 |
| nullifier_root | `effAccumInsertV3` (`some SEL_NOTE_SPEND`) | sorted-INSERT | `Rfix 27`, pos 56 |
| commitments_root | `effAccumInsertV3` (`none`) | sorted-INSERT | `Rfix 28`, pos 57 |
| cells_root | `effAccumInsertV3` (`none`) | sorted-INSERT | `Rfix 17`, pos 58 |

The three update-at-key roots share the cap-open after-spine template; the three
accumulators use the INSERT-shaped keystone (non-membership + splice) —
`AccumulatorInsertEmit.lean` + `SortedTreeNonMembershipHeap8.lean`.

### 1c. The noteSpend residual — CLOSED at HEAD

The `a52c2f6cb` gap ("noteSpend value-col gap") was: the deployed `valueCol = NOTE_VALUE_LO`
is per-row economically constrained (must be 0 on padding), irreconcilable with
`effAccumInsertV3`'s UNCONDITIONAL per-row VALUE-bind. **Closed by `e1a0ebaf5`**
(`feat(accum8 noteSpend): selector-gate the insert KEY/VALUE binds`): the KEY/VALUE binds
became `sel·(leaf−col)=0` — active on the firing row, vacuous on padding; MEMBERSHIP +
rootPin welds stay unconditional. noteSpend passes `some SEL_NOTE_SPEND`; noteCreate /
createCell pass `none` (byte-identical, no drift). All three insert families PROVE+VERIFY;
`effect_vm_wide_roundtrip.rs` has no `#[ignore]`.

### 1d. Degraded-felt gate + the one remaining residual

`.ast-grep/rules/faithful-commitment-felt.yml` is LIVE on main with **two** rules:
`degraded-felt-commitment` (`fold_bytes32_to_bb`) and `replicated-felt-commitment`
(`[$X; 8]` replicate); `scripts/check-no-degraded-felt.sh` + a `ci.yml` job enforce it over
`commitment.rs` / `rotation_witness.rs` / `trace_rotated.rs`.

**One genuine open, explicitly allowlisted (NOT a root):** the flat per-record field limbs
`fields[0..7]` still fold 32B→1 felt (~31-bit) — `cell/src/commitment.rs:990`,
`turn/src/rotation_witness.rs:360` (`// ast-grep-ignore … residual`). The pre_limbs 67..87
are "zero-filled until producer-welded." `[@bae447985]` precision: that zero-fill is the
TWO FLAT-RECORD TWINS ONLY (`cell/src/commitment.rs` `compute_rotated_pre_limbs` +
`turn/src/rotation_witness.rs`, per the const comments at `commitment.rs:702` /
`rotation_witness.rs:67`); the CIRCUIT TRACE producers DO fill genuine
`CanonicalHeapTree8::root8()` into the accumulator lanes (nullifier 26‖67..73
`trace_rotated.rs:1094-1110`, commitments 27‖74..80 `:1272-1287`, cells 0‖81..87
`:1192-1207` — commit `cbaf7b05b`). Also `[@a1a627d4d+]` CORRECTION: the whole-image STATE_COMMIT digest flag-day
ALREADY FIRED (`9e5a83935`, 2026-06-19) — `compute_canonical_state_commitment_v9_felt8`
(`commitment.rs:1219`) IS the deployed end-to-end 8-felt binding (producer/executor/LC);
the earlier "staged" reading here quoted a stale header comment (since fixed). The one
load-bearing ~31-bit LC surface left is the `transferCapOpenTB` 1-felt V3-registry
fallback (`full_turn_proof.rs:4285-4295`, the sole cap-open key without a wide twin) —
the transferCapOpenTB wide-twin grind is its named close. This is the `fields[0..7]` / flat-mem grind, a
named follow-up — it is NOT one of the six Merkle roots and does NOT block the carrier bang
(carriers anchor to the roots, not the flat field limbs). But it IS a ~31-bit surface still
standing; flag it as the standing crumb.

### 1e. What this UNBLOCKS

Carriers may now anchor their teeth to FAITHFUL 8-felt committed forms (the six roots)
instead of the 31-bit folds the memory's §BLOCKER forbade. `[@wave-1 7c4257824]`
CORRECTION for factory: the six ROOTS are faithful, but the cells_root LEAF CONTENTS are
still 1-felt `(key, key)` and col 69 holds the owner-key fold, NOT child_vk — so factory
gained no usable anchor from this epoch (see §3 factory row + §5 item 9); the DEEPEST
carriers can anchor to faithful roots.
The MerkleHash/node8 primitive the campaign forged (arity-16 node8, `CHIP_RATE 16` —
`[@bae447985]` the const lives in `circuit/src/descriptor_ir2.rs:279`) is the
shared hash gadget the hash-heavy carrier family (custom-routing, dsl, membership path,
cap-crown Hash3Cap) needs — it now exists.

### 1f. `[@bae447985]` THE CAP-WRITE FAMILY CLOSE — landed since this map was written

Commits `48d981698..bae447985` (the 14 past `956b8be93`). **All 8 cap-writing effects
now ride SHAPE-MATCHED keystones** — the update-at-key `effCapOpenWriteV3` (§1b) grew an
INSERT and a REMOVE twin, and every cap-write was rewrapped:

| shape | keystone | effects (wrapper → Rfix pin) |
|---|---|---|
| INSERT ×4 | `effCapInsertV3` (`CapOpenEmit.lean:661`; `capInsert_writesTo8` `CapInsertEmit.lean:123` — genuine non-membership bracket + spliced membership) | delegate (`Rfix 1`, pos 46) · introduce (`Rfix 10`, 47) · delegateAtten (`Rfix 11`, 48) · spawn (`Rfix 19`, 52) |
| REMOVE ×2 | `effCapRemoveV3` (`CapOpenEmit.lean:680`; `capRemove_writesTo8` `CapRemoveEmit.lean:120` — tombstone ZERO-fold) | revoke/revokeDelegation (`Rfix 2`/`Rfix 14`, pos 49) · revokeCapability (deployed route — but see the seam below) |
| UPDATE ×2 | `effCapOpenWriteV3` (`CapOpenEmit.lean:585`; §11/§12 `:1747-1990`) | attenuate (`Rfix 12`) · refreshDelegation (`Rfix 55`, pos 50) |

**Root cause (why this was a LIVENESS break):** the heap-8-felt migration made the
witness heaps `CanonicalHeapTree8`, which made every scalar arity-2 cap map-op
**shape-UNSAT for an HONEST prover** (`sdk/src/full_turn_proof.rs:7111`; commit
`48d981698` names the shape gap: `writesTo8` was UPDATE-at-key only, but
delegate/insert/revoke *change the cap key-set* — no shared before/after path). The gap
sat unexercised while the SDK test suite carried 7 `E0308` compile breaks lagging the
same migration (`5ea008aab` — "the big-bang `--tests` check was truncated by a
disk-full moment"). The arity-2 map-op `_forces_write` theorems were deleted as
shape-UNSAT (`6a7283580`); the registries were regenerated + FP-re-pinned
(`824c2963e`, `136de6281`, `bae447985`) — registry length stays 59 (the wrappers were
REWRAPPED in place, not appended).

Rust: `CanonicalCapTree::{insert_witness,remove_witness}` (`circuit/src/cap_root.rs:768`,
`:818`) + the three-shape router `build_effect_vm_cap_open_leg`
(`sdk/src/full_turn_proof.rs:2845`: `:2898` update / `:2915` insert / `:2936` remove).
Teeth: witness unit teeth `cap_root.rs:1015-1556` (`bd5a6e5b5`); prove+verify leg tests
per effect + the no-silent-forge REMOVE tooth `full_turn_proof.rs:7124` (`c2d9feabd`,
`bae447985`). Apex: the `Rfix` pins above are `#assert_axioms`-clean
(`CircuitSoundnessAssembled.lean:761-767`).

**One honest seam:** `Rfix 24` (revokeCapability) still pins the authority-only
`revokeCapabilityCapOpenV3` (`CircuitSoundnessAssembled.lean:525`), while the deployed
prover proves the REMOVE write wrapper whenever the node supplies the c-list witness
(named empty-c-list fallback — `full_turn_proof.rs:2331-2352`, "named, not a silent
forge"). The Lean write wrapper + `ClosureAll` rung exist
(`revokeCapabilityWriteCapOpenV3` `CapOpenEmit.lean:716`;
`revokeCapability_closedLog_capOpenSat` `ClosureAll.lean:971`); moving the `Rfix 24`
pin is the open apex-registry step.

Also landed in the same span: the portable relative mathlib path restored
(`metatheory/lakefile.toml:10` → `../../../src/mathlib4`, commit `d3c16c7f1`).

**What this means for the carrier map below:** nothing in §2–§6 regresses; the
cap-write close is a §1-family (faithful-commitment) completion. The cap-root anchor
carriers weld to is now written by ALL 8 cap-writes through circuit-forced keystones —
strictly better anchoring for the third-edge builds.

---

## 2. Carrier universal-fold mechanism — built vs deployed (per-carrier)

All 7 carriers have leaf + binding-node + negative-tooth + Lean refutation COMMITTED as
reusable primitives. Corpus is sorry-free; `#assert_axioms` present in every refute file.
**Only `custom` is flipped to the positive floor proof AND wired into the deployed
aggregation path.** The other six are staged library primitives + refutations — NOT on the
deployed light-client fold.

| carrier | leaf | binding node | negative tooth | refute (BackingAttack) | BindingFromFold (positive)? | deployed-wired? |
|---|---|---|---|---|---|---|
| **custom** | `custom_leaf_adapter.rs:994/1179` | `joint_turn_recursive.rs:591` | `joint_turn_recursive.rs:1174` + integration `tests/custom_binding_deployed_tooth.rs`, `custom_binding_production_path.rs` | — (superseded) | **YES** `CustomBindingFromFold.lean` (7 pins) | **YES** (buff-in-production) |
| bridge | `bridge_leaf_adapter.rs:170/227` | `joint_turn_recursive.rs:797` | `bridge_leaf_adapter.rs:353` + `tests/bridge_binding_mechanism.rs` | `BridgeBackingAttack.lean` (7) | no | no |
| sovereign | `sovereign_leaf_adapter.rs:181/221` | `joint_turn_recursive.rs:898` | `sovereign_leaf_adapter.rs:375` | `SovereignBackingAttack.lean` (10) | no | no |
| factory | `factory_leaf_adapter.rs:177/214` | `factory_leaf_adapter.rs:338` | `factory_leaf_adapter.rs:468/590` | `FactoryBackingAttack.lean` (12) | no | no |
| hatchery | `hatchery_leaf_adapter.rs:176/214` | `hatchery_leaf_adapter.rs:343` | `hatchery_leaf_adapter.rs:477/595` | `HatcheryBackingAttack.lean` (8) | no | no |
| membership | `membership_leaf_adapter.rs:197/235` | `membership_leaf_adapter.rs:431` | `membership_leaf_adapter.rs:574` + `tests/membership_binding_mechanism.rs` | `MembershipBackingAttack.lean` (8) | no | no |
| dsl (Dfa) | `dsl_leaf_adapter.rs:112` — REUSES `prove_custom_leaf_with_commitment` | `dsl_leaf_adapter.rs:141` — REUSES `prove_custom_binding_node_segmented` | `dsl_leaf_adapter.rs:321` | `DslBackingAttack.lean` (7) | no | no |

Provenance: bridge/sovereign landed `aa34a6244`; factory/hatchery/membership `9cade93a2`;
dsl `02ef3cdd7`; `CustomBindingFromFold` `fa496cfa7`.

### Shared plumbing (the big-bang integration layer)

- **`prove_descriptor_leaf_dual_expose_at`** (`ivc_turn_chain.rs:1526`) — **GENERALIZED,
  done.** Parametric `(claim_pi_lo, claim_len)`; the old hardcoded `_dual_expose`
  (`:1481`, `CUSTOM_COMMIT_PI_LO=46`) is now a convenience wrapper. Step-3 of the uniform
  build is ready for every carrier.
- **`prove_chain_core_rotated`** (`circuit-prove/src/ivc_turn_chain.rs:2818`) — **only the
  custom arm is wired** (`match &leg.custom_witness`, `:2886`). No bridge/sovereign/
  factory/hatchery/membership/dsl witness arm exists. Step-5 done for custom only.
- **Witness socket** — **NOT generalized.** `RotatedParticipantLeg`
  (`joint_turn_aggregation.rs:6`) still carries a single `pub custom_witness:
  Option<CustomWitnessBundle>` (`:125`). No `carrier_witness: Option<CarrierWitness>` enum
  exists in the tree. Step-2 done for custom only.

### The other staged big-bang inputs

- **G5 capacity satisfaction (17/18/19)** — welds BUILT: `circuit/src/effect_vm/
  discharge_weld.rs`, `vault_weld.rs`, tests `discharge_obligation_air_teeth.rs`,
  `settle_escrow_capacity_weld.rs`, `gentian_carrier_floor_prove.rs`; Lean
  `metatheory/Dregg2/Deos/CapacitySatisfaction.lean`. (Note: the escrow floor's v11
  geometry drift was the LAST commit `956b8be93` — `settleEscrow` AFTER-gate cols
  v10→v11, `B_SPAN 51→119`.) Staged; the emit+producer-fill is part of the bang.
- **flat-mem boundary** — `satisfied2_init_root` + the `whole_image_fold_bound_mem_
  forged_minit_refuses` tooth built (memory §ALSO BUILT); the per-effect `setFieldDyn` VK
  weld is the bang piece. This overlaps the `fields[0..7]` residual (§1d).
- **The apex** (`lightclient_unfoolable` + assembled/forest/closure) is
  `#assert_axioms`-clean at HEAD (`docs/reference/lean-circuit.md`; pins at
  `CircuitSoundnessAssembled.lean:752-775`).

---

## 3. THE FAIL-OPEN LAW / THIRD-EDGE status per carrier

The load-bearing law (memory §"THE LOAD-BEARING LAW"): the *connect* alone is VACUOUS —
the leaf re-proves whatever tuple the prover hands it; the binding node enforces
`leg.teeth == leaf.tuple`, but a forger fills both with arbitrary `T`. Soundness needs the
**THIRD EDGE**: `leg.teeth == committed-authority`, enforced IN THE DEPLOYED AIR (a
PiBinding/gate tying the emitted PI to a committed-state limb). This is Step-1 of the
uniform build — the security-critical acceptance gate. Steps 2–5 without it = a vacuous
binding.

**The BackingAttack refutations ARE the proof that the third edge is currently ABSENT for
the six non-custom carriers** — each `*BackingAttack.lean` exhibits a forged input the
deployed proof accepts but a re-executor rejects (vacuous-as-deployed-LC). That is by
design: the campaign refutes its own green first, then repairs.

| carrier | depth | authority committed today? | third edge (in-AIR teeth==committed) | Step-1 remaining |
|---|---|---|---|---|
| **custom** | — | yes (PI 46–49 deployed) | **PRESENT** | none — buff-in-production. (NB: the deeper per-turn `proofBind True→boundAt` in-AIR flip + 4→8-felt lift is a SEPARATE deployed VK epoch, still pending — `docs/reference/lean-circuit.md` §Custom, `CustomApex.lean`. The recursion-tree fold is what's buffed.) |
| **factory** | SHALLOW→**BLOCKED-ON-WIDENING** | `[@wave-1 7c4257824]` CORRECTED: child_vk is NOT committed at HEAD in ANY in-AIR form, at any width. Rotated PI 38 carries the born cell's vm KEY = `hash_to_bb(owner_pubkey)` under the MISNOMER `child_vk_derived` (`turn/src/executor/effect_vm_bridge.rs:131-139`); the actual installed authority `effective_vk` (`apply.rs:2376-2421`) never reaches the VmEffect at all; the cells leaf is `(key, key)` with 1-felt contents (`trace_rotated.rs:1167-1189` — 8-felt-ness is in the DIGESTS only, `HeapLeaf` = 1-felt addr + 1-felt value); params carry no vk limbs (factory uses param0/param1 only, both ~31-bit `fold_bytes32_to_bb` folds); the born cell's state block is off-row, bound only via byte-domain blake3 `effects_hash` (Lean `EffectVmEmitCreateCellFromFactory.lean` §RT) | absent | the third edge CANNOT be built until a faithful committed carrier of child_vk EXISTS — a WIDENING epoch first (§5 item 9: three routes + blast radii). Do NOT expose unanchored witness-column teeth (6 free param cols exist — using them = the vacuous connect). Derivation (child_vk=Poseidon2(factory_vk‖params)) = named off-AIR. |
| **dsl** | `[@wave-5 BUILD-PASS]` SHALLOW → **BLOCKED-ON-VK-EMIT** (the `[@wave-4]` non-VK Layer A is REFUTED at the code level) | Witnessed{Dfa} `⇒ None` (`mod.rs:462`) — commits NOTHING TODAY, AND the `[@wave-4]` fix site is WRONG: `SLOT_CAVEAT_MANIFEST_BASE` (≈102, the V1/`BASE_COUNT=209` layout) is NOT in the DEPLOYED ROTATED fold dpis. The rotated leg's dpis are the COMPACT `pis[..V1_PI_COUNT=42]` + 4 (rotated commits/height + ONE folded `caveatCommit` felt at PI 45) = `ROT_PI_COUNT=46` (`trace_rotated.rs:427-432`); wide appends teeth after 46 (custom's rc at 46..49, `joint_turn_recursive.rs:104`). A tag-20 entry at PI≈102 would be a value the rotated fold path NEVER reads. `rc` IS still a self-contained 4-felt `custom_proof_pi_commitment` (no v12 widening) — but exposing it faithfully needs a NEW rotated-cohort PI slot appended after 46 = a **VK-affecting descriptor-emit** (the code's own `dsl_leaf_adapter.rs:72-81` §"THE BIG-BANG PIECE" already states this: "rides the VK regen"). | absent — the DUAL-EXPOSE leg leaf cannot be minted until the rotated Dfa-gated cohort emits `rc` at a fixed PI (VK regen) | STOP: Layer A as specified (`mod.rs` tag-20 at `SLOT_CAVEAT_MANIFEST_BASE`) is vacuity-laundering (dead PI offset). The sound emit is a rotated-descriptor rc-PI append + VK regen (big-bang lane), NOT non-VK. `DslBackingAttack.lean` STANDS. |
| **membership** | `[@wave-3]` SHALLOW→**BLOCKED-ON-WIDENING** | CORRECTED: NEITHER anchor is a faithful AIR-committed felt in the rotated leg. The sender leaf is `poseidon2::hash_many(encode_hash(sender_PUBKEY))` (1-felt) — 0 hits for pubkey/sender/compress in `trace_rotated.rs`; OWNER_CELL_ID commits a DIFFERENT value (`cell_id = BLAKE3(pubkey‖token)`) by a DIFFERENT hash (`canonical_32_to_felts_4`, 4-felt) AND is ZERO-DEFAULTED in the rotated generator (`trace_rotated.rs:372-377 ..Default::default()`). The authorized_root VALUE is uncommitted: the SenderAuthorized manifest entry (tag 11) carries only the slot INDEX with `params=[0;4]` (`executor/mod.rs:341`), the value lives only in the folded `fields_root` digest (limb 36), and `verify.rs:523` DEFERS tag 11. | absent | see `[@wave-3]` block below — the third edge cannot be built non-vacuously at HEAD; the census's "plain connect to OWNER_CELL_ID / root committed as value" was WRONG (both anchors walled). |
| **hatchery-invariant** | SHALLOW | invariant_digest === child_program_vk === FACTORY's child_vk | absent | RIDES factory's CreateCellFromFactory leg + one extra connect to a re-proved contract-attestation leaf. SHARES factory teeth. |
| **bridge** | **DEEPEST** | the 26-limb tuple is ENTIRELY uncommitted; mint_hash read in ZERO constraints | absent | ⚑ folding `bridge_action_air` is UNSOUND (prover-chosen tuple, no Merkle/key). SOUND path: re-prove the REAL foreign note_spend STARK as a foldable G2 leaf (`note_spend_leaf_adapter.rs`, new), recompute mint_hash in-circuit, connect to a newly-exposed mint_hash PI on `mintV3`. Double-mint = orthogonal re-exec nullifier guard. |
| **hatchery-contract** | **DEEPEST** | contract_hash stored-only (SDK `MintedKind.hpres`), off-VK, read by zero constraints | absent | NEW on-VK binding: add contract_hash[8] teeth on FactoryDescriptor + its hash. (The invariant half is shallow, rides factory.) |
| **sovereign** | **DEEPEST** | owner key IS committed (BLAKE3 leaf `commitment.rs:209` + v9 r23 + content-addressed CellId) → `KEY_COMMIT=Poseidon2(pubkey)` is sound; teeth are prover-free PiSlot self-pins | **partial** — the 4-felt `SOVEREIGN_WITNESS_KEY_COMMIT` teeth columns exist (`columns.rs:274`, `air.rs:190`) but are prover-free self-pins; the inner transition-proof VK is sentinel-zero (`pi.rs:240`, STAGED) | P1 (non-VK): socket + producer fill the dead-zero teeth (`cipherclerk::prove_sovereign_turn_rotated` has `before_cell.public_key()`) + sovereign arm. P2 (VK, load-bearing): named rotated pubkey limb + `IS_SOVEREIGN_CELL`-gated in-AIR `Poseidon2(pubkey_limb)==teeth` → forged key UNSAT. Ed25519 stays off-AIR (verified `authorize.rs:889`). |

"committed-in-state ≠ grounded-in-fold" (sovereign: pubkey IS committed but teeth are
prover-free self-pins → needs the grounding hash-site).

### `[@wave-2]` BANG WAVE (sovereign) — the third edge is BLOCKED-ON-WIDENING (stop-condition)

Grounded at HEAD `746435722`. The sovereign third edge was ATTEMPTED and the
stop-condition fired — the SECOND carrier after factory to hit a widening wall (this
supersedes this row's earlier "partial, P1-then-P2 is a per-carrier wave" reading).

**What is real (verified in-source):** the owner pubkey IS committed and the teeth
columns DO exist — that part of the anchor is sound:
- `KEY_COMMIT` teeth cols exist: `columns.rs:274-277` (aux 23..26) + PI pins
  `air.rs:189` / `pi.rs:240`; leaf + binding node + refutation all committed
  (`sovereign_leaf_adapter.rs`, `joint_turn_recursive.rs:900`,
  `SovereignBackingAttack.lean`).
- The pubkey is committed into the FAITHFUL ~124-bit 8-felt authority digest
  (`compute_authority_digest_8` = `blake3(authority_residue_bytes)` where
  `authority_residue_bytes` absorbs `cell.public_key`, `commitment.rs:849`) and into the
  whole-state BLAKE3 commitment (`:209`). Both are genuinely faithful (not 31-bit).

**Why the FAITHFUL third edge is NOT buildable at HEAD (the wall):** P2 requires an
in-AIR gate `Poseidon2(pubkey_limb) == teeth` anchored to a FAITHFUL COMMITTED pubkey.
But the owner pubkey enters felt-commitment form **only through BLAKE3 folds**
(`commitment.rs:209/849/1850` — verified: those are the *only* sites) — it is NOT carried
as a Poseidon2/AIR-reconstructable committed column anywhere in the rotated trace
(`grep pubkey circuit/src/effect_vm/trace_rotated.rs` = 0 hits). The teeth today are
row-0 self-pins (aux == PI boundary, `trace.rs:1005-1014`), off-AIR recomputed by the
executor (`proof_verify.rs:2548 pubkey_to_witness_key_commit`); the fold's binding node
`connect`s leg.teeth == leaf.key_commit (both prover-controlled — the vacuous connect the
fail-open law forbids). To make the teeth non-forgeable in-AIR you need the pubkey as a
committed AIR-reconstructable form, and there are exactly two routes, both bigger than a
per-carrier wave:
  - **(a) geometry widening** — surface the pubkey as named rotated pre-limbs feeding
    `compute_rotated_pre_limbs` → `wireCommitR` → `state_commit`. `V9_NUM_PRE_LIMBS` is
    fully allocated at 88 (limbs 67..87 are the accumulator-8-felt completion, §1d — no
    free/reserved slot), so this GROWS the vector = a v12 geometry epoch: ALL rotated VKs
    move, keystone re-grounds, registry-wide regen + `Rfix` re-pins, devnet re-genesis.
    The direct mirror of factory's §5 item-9 route (a).
  - **(b) in-AIR Ed25519** — verify the owner signature over `(key_commit, sequence,
    anchor, new)` in-circuit, forcing `key_commit` to a verifying key. This is the NAMED
    TERMINAL crypto seam the leaf docstring (`sovereign_leaf_adapter.rs:50-59`), the
    binding-node seams (`joint_turn_recursive.rs:895`), and `SovereignBackingAttack.lean`
    §C all already name as off-AIR. Not a per-carrier wave.

Recomputing the committed BLAKE3 authority digest in-AIR from pubkey felts (to bind teeth
to the existing faithful anchor without widening) is terminal-infeasible — BLAKE3 is not
AIR-friendly (the reason it is the named off-AIR seam).

**Decision:** do NOT run P1 in isolation. P1 (fill the dead-zero teeth + set
`is_sovereign_cell = 1` + the sovereign witness arm) changes deployed sovereign-proof PI
VALUES with ZERO soundness benefit absent P2, and wiring the fold + flipping
`SovereignBackingAttack → SovereignBindingFromFold` on P1 alone would LAUNDER VACUITY
(the connect stays forger-controlled). The `SovereignBackingAttack.lean` refutation
STANDS (correct at HEAD). The sovereign third edge is blocked behind an ember-decision on
route (a) vs (b), exactly like factory. hatchery-contract/bridge (the other DEEPEST) are
unaffected by this finding.

### `[@wave-3]` BANG WAVE (membership) — the third edge is BLOCKED-ON-WIDENING (stop-condition)

Grounded at HEAD `dcf9b289e`. The membership third edge was ATTEMPTED and the stop-condition
fired — the THIRD carrier after factory + sovereign to hit a widening wall. This SUPERSEDES
the census verdict this wave was launched with ("membership is CLASS-1, buildable NOW, no
v12; sender anchors to OWNER_CELL_ID via a plain connect; authorized_root committed as
pointer + value"). Two independent groundings refute BOTH halves of that verdict.

**The membership relation's two endpoints (`sender_leaf`, `authorized_root`) are neither of
them a faithful, AIR-reconstructable committed felt in the deployed rotated leg** — so there
is nothing to `connect` a published teeth column TO. A `connect` to either would be the exact
vacuous / dead-zero self-pin the FAIL-OPEN LAW forbids:

- **SENDER (a sovereign-style wall, WORSE):** the deployed off-AIR check
  (`membership_verifier.rs:143`) is `leaf = compress(candidate)` where `candidate` is the
  turn sender's raw 32-byte **PUBLIC KEY** (`execute_tree.rs:1322` → `PredicateInput::Sender(pk)`)
  and `compress` is 1-felt `poseidon2::hash_many(encode_hash(bytes))`. That value is NOT in
  the rotated AIR: `grep pubkey|public_key|sender|compress trace_rotated.rs` = 0 hits (every
  `hash_many` there is a STATE_COMMIT / Merkle-node hash). OWNER_CELL_ID (PI 194) does NOT
  serve as its anchor for THREE independent reasons: (i) it commits a DIFFERENT value —
  `cell_id = BLAKE3(pubkey ‖ token)` (`types/src/lib.rs:701`), not the pubkey; (ii) by a
  DIFFERENT hash — `canonical_32_to_felts_4` (4-felt, `trace.rs:26`), not `hash_many` (so a
  plain connect is a type mismatch, never satisfiable, and there is no in-AIR re-derive since
  the 4-felt form does not yield back the 32 bytes `compress` needs); and (iii) in the ROTATED
  generator `owner_cell_id` is **zero-defaulted** (`trace_rotated.rs:372-377`, 0 hits) — so
  OWNER_CELL_ID is `canonical_id_to_felts_4([0;32])`, a dead-zero sentinel, exactly like the
  sovereign KEY_COMMIT teeth. A connect to it is the vacuous connect.
- **ROOT (uncommitted value):** `authorized_root = root_felt_from_slot(commitment)` — the low
  4 bytes of `fields[set_root_index]`. In the rotated AIR that slot reaches committed state
  ONLY through the folded `fields_root` digest (limb 36, whole-map Poseidon2 fold — the
  individual felt is not recoverable without an in-AIR MAP-OPEN). The SenderAuthorized caveat
  manifest entry (tag 11 = `SLOT_CAVEAT_TAG_SENDER_AUTHORIZED`) carries only the slot INDEX
  with `params=[0;4]` (`executor/mod.rs:326-343`), and `verify.rs:523-529` DEFERS the tag
  (in-AIR no-op). So binding the root needs a NEW in-AIR fields_root open gadget — not the
  "committed as value" plain connect the verdict claimed.

**The one genuinely closed seam (worth recording, but NOT sufficient):** the §5-item-4
terminal Merkle seam is CLOSED for the LEAF. `custom_leaf_adapter::cellprogram_to_descriptor2`
now maps `ConstraintExpr::MerkleHash` via the `TID_P2` lane-witnessing weld
(`custom_leaf_adapter.rs:802`, Merkle-path test `:1524+`), and `merkle_poseidon2_descriptor`
(`dsl/descriptors.rs:102`) IS a `MerkleHash` descriptor — so the REAL membership Merkle STARK
is re-provable as a fully-witnessed foldable leaf (like dsl routing), NOT the trivial 2-felt
tuple binder the current `membership_leaf_adapter.rs` uses (its "MerkleHash refused / path
off-AIR" docstring at `:34-57` is STALE). BUT a fully-witnessed leaf folds VACUOUSLY without
the third edge: the prover picks ANY `(sender, root)` pair, proves a genuine path between
them, and nothing forces `sender == the real actor` or `root == the cell's real authorized
set` (exactly the §A/§A′ forgeries of `MembershipBackingAttack.lean`). The walls are the
ENDPOINT ANCHORS, not the path.

**Decision:** do NOT build. Building the census's "plain connect" (leaf.sender == OWNER_CELL_ID,
leaf.root == manifest param) would LAUNDER VACUITY — OWNER_CELL_ID is a dead-zero domain
mismatch and the manifest param is zeroed. Do NOT touch the rotated `owner_cell_id`
zero-default in isolation either (changing that deployed PI value has zero soundness benefit
absent the full binding — the same "P1 alone is forbidden" logic as sovereign). The
`MembershipBackingAttack.lean` refutation STANDS (correct at HEAD; both §A and §A′ live).
Blocked behind an ember-decision on one of two routes, both bigger than a per-carrier wave:
  - **(a) v12 geometry widening** — surface `compress(sender_pubkey)` as a named rotated
    pre-limb AND open the authorized-root felt out of `fields_root` in-AIR. `V9_NUM_PRE_LIMBS`
    is full at 88 (no free slot), so this GROWS the vector: all rotated VKs move, keystone
    re-grounds, registry-wide regen + Rfix re-pins, devnet re-genesis. The direct mirror of
    factory §5 item-9 (a) and sovereign §5 item-10 (a).
  - **(b) semantic redefinition of `AuthorizedSet`** — make the authorized set a set of 4-felt
    OWNER_CELL_IDs (not 1-felt `compress(pubkey)` leaves). This requires FIRST fixing the
    rotated leg to actually populate `owner_cell_id` (today zero-defaulted), THEN changing the
    executor's `membership_verifier` leaf domain to match, PLUS re-genesis of every deployed
    cell's authorized-set root. An ember-decision about what "authorized set" MEANS, not a
    circuit wave.

hatchery-invariant does NOT ride membership; factory/sovereign/bridge are unaffected.

### `[@wave-4]` BANG WAVE (dsl) — VERIFY-FIRST verdict: **BUILDABLE (the last clean class-1)**, NOT a stop
> ⚠ **SUPERSEDED by `[@wave-5]` below.** The "non-VK Layer A via `SLOT_CAVEAT_MANIFEST_BASE`" recipe
> in this block is REFUTED at the code level (that PI offset is absent from the deployed rotated fold
> dpis; the faithful `rc` emit is VK-affecting). Read `[@wave-5]` for the corrected verdict. The paper
> record below is retained for the shape of the reasoning, not the state.

Grounded at HEAD `a64cb90ac`. dsl was the last class-1 candidate; unlike factory/sovereign/
membership (all three STOPPED on a widening wall), the dsl VERIFY-FIRST verdict is **BUILD** —
dsl genuinely rides custom's non-vacuous fold-binding. The census did NOT over-promise here.

**Does custom bind via the FOLD, non-vacuously? YES (verified in-source).**
- `CustomBindingFromFold.lean:147` (`custom_binding_from_fold`) proves a verifying aggregate
  FORCES, for the effect-vm leg's exposed commitment `c`: ∃ a verifying custom sub-proof `q` with
  `piCommit q = c` (+ anti-ghost VK determinism). It rests on `{FRI floor via AggAirSound,
  Poseidon2SpongeCR, the connect}` — `StarkSoundCustom` is GONE; the vacuous deployed
  `proofBind ⇒ True` gate is NOT the binder. `#assert_axioms`-clean (7 pins).
- The DEPLOYED wire (`ivc_turn_chain.rs:2906-2934`, `CarrierWitness::Custom` arm): the custom leg
  gets a DUAL-EXPOSE leaf re-exposing the deployed proof's `custom_proof_commitment` at IR2 PI
  46..49 (`CUSTOM_COMMIT_PI_LO=46`, `joint_turn_recursive.rs:104`), folded against the RE-PROVEN
  custom sub-proof leaf through `prove_custom_binding_node_segmented` — the `connect` ties the two
  4-felt commitments IN the recursion tree; a forged claim with no backing sub-proof is UNSAT.
  Pinned end-to-end by `tests/custom_binding_deployed_tooth.rs`.
- ⚑ KEY: custom's PI 46..49 is NOT constrained by the deployed AIR (the proofBind gate is vacuous
  `True`, `CustomCarrierAttack`). It is bound SOLELY because it is a FRI-bound PI of the deployed
  proof that the fold re-exposes and connects to a genuine sub-proof. "Committed" here = "a
  FRI-bound PI", NOT "the deployed AIR constrains it".

**Does dsl ride the SAME mechanism, non-vacuously? YES.** The anchor `rc` (the Dfa route-commitment)
IS `custom_proof_pi_commitment(DfaProofWire.public_inputs)` — the SAME host function, the SAME 4-felt
shape (`dsl_leaf_adapter.rs:300-312` pins `exposed == host == off-AIR bound.proof_commitment()`).
The leaf (`prove_dsl_leaf_with_commitment`, `:112`) and binding node
(`prove_dsl_binding_node_segmented`, `:141`) REUSE `prove_custom_leaf_with_commitment` /
`prove_custom_binding_node_segmented` term-for-term. `DslBackingAttack.dslEngineBinding_of_floor`
(`:163`) already proves the binding reduces to `Poseidon2SpongeCR` ALONE.

**Why dsl is NOT the factory/sovereign/membership wall.** Those three STOPPED because their teeth had
to MATCH AN EXTERNAL COMMITTED-STATE value (child_vk / owner-pubkey / sender-`compress` / authorized-
root) that does not exist as a faithful AIR-committed felt → a v12 geometry widening. **dsl's `rc` is
NOT an external anchor — it is the sub-proof's OWN output (self-referential), bound by the FOLD, not
by matching committed state.** Concretely: `rc[0..4]` fits FAITHFULLY in a deployed manifest entry's
`params[0..4]` (4 consecutive felts — the entry shape `[type_tag, slot_index, p0..p3]`,
`pi.rs:421`), UNLIKE membership's tag-11 which zeroes its params (value only in the folded
`fields_root`). No widening; the emit is a bounded per-descriptor/manifest change, the SAME kind as
custom's `customPiExposure`.

**The one census under-specification (a build-design point, NOT a wall).** A Dfa caveat is a
PRECONDITION with NO effect descriptor of its own (custom has `customVmDescriptor2R24` + PI 46..49;
dsl has neither). So "emit `rc` at TAIL like custom" needs a concrete site. The sound, bounded site:
route `rc` into the DEPLOYED off-AIR slot-caveat manifest (`SLOT_CAVEAT_MANIFEST_BASE`, in the base
PI region) as a tag-20 entry — that makes `rc` a FRI-bound PI of every Dfa-gated turn's deployed
proof, which is ALL the fold needs (`prove_descriptor_leaf_dual_expose_at(claim_pi_lo = that param
slot, claim_len = 4)` reads it and connects). This is EXACTLY custom's posture (a FRI-bound-but-
AIR-unconstrained PI, bound by the fold). The in-AIR caveat-commit chain (`CAVEAT_COMMIT`,
`V3_STAGED_CAVEAT_DESCRIPTORS`) is STAGED and is only needed for OMISSION-proofness (forcing `rc`'s
publication when a cell declares a Dfa caveat) — the SAME coverage residual custom carries (its
deeper `proofBind True→boundAt` epoch, §5 item 6) and the capacity-caveat coverage floor
(`required_capacity_caveat_tags`, `mod.rs:588`). Not a dsl-specific wall.

**The build (bounded, per the census + the emit-site resolution above):**
1. **Layer A (non-VK):** `mod.rs:462` split `Witnessed{Dfa} ⇒ None` → `Some(SlotCaveatEntry{
   type_tag = TAG_DFA (20), slot_index = 0, params = rc[0..4]})`. Non-VK (manifest is off-AIR-
   reevaluated PI DATA, not AIR constraints) but it CHANGES deployed PI values.
2. **Step-2:** `from_bound_dsl` projection filling `CarrierWitness::Dsl(DslWitnessBundle)`
   (`joint_turn_aggregation.rs:366` — the socket + bundle ALREADY EXIST), fail-closed None off-wire.
3. **Step-5:** fill the `CarrierWitness::Dsl(_)` arm (`ivc_turn_chain.rs:2953`, currently fail-closed)
   = `dual_expose_at(manifest rc slot, 4)` + `prove_dsl_leaf_with_commitment` +
   `prove_dsl_binding_node_segmented`; add the deployed-path fold tooth (TWIN of
   `custom_binding_deployed_tooth.rs`: honest Dfa turn FOLDS + LC-verifies through
   `prove_turn_chain_recursive → verify_turn_chain_recursive`, a forged `rc` → UNSAT).
4. **Flip** `DslBackingAttack.lean → DslBindingFromFold.lean` (mirror `CustomBindingFromFold`),
   `#assert_axioms`-clean — ONLY AFTER the positive tooth bites.

**⚠ ANTI-VACUITY, per the sovereign/membership stops:** Layer A alone is FORBIDDEN as an isolated
commit — it churns deployed PI values with zero soundness benefit absent Step-5, and flipping the
refutation on it alone would launder vacuity. The build is all-or-nothing (Layer A + Step-5 fold
tooth + flip together, one coordinated change, + devnet re-genesis since PI values shift).
`DslBackingAttack.lean` STANDS at HEAD (correct — the emit is not yet built).

**Status this wave:** VERIFY-FIRST verdict rendered (BUILD, distinct from the 3 walls, recipe +
emit-site pinned). The coordinated Layer-A+Step-5+flip build was NOT executed this session (a
correct, non-vacuous fold-tooth-biting build exceeds a safe single pass; a partial commit is
forbidden). dsl is the ONE confirmed remaining class-1 carrier.

### `[@wave-5]` BANG WAVE (dsl BUILD-PASS) — the non-VK Layer A is REFUTED; emit is VK-gated. **STOP.**

Grounded at HEAD `06cde93ac`, code-level verify-first (executed the BUILD pass; stopped at Layer A
when the fix-site failed to ground). The `[@wave-4]` recipe's Layer A — "route `rc` into the
DEPLOYED off-AIR slot-caveat manifest (`SLOT_CAVEAT_MANIFEST_BASE`) as a tag-20 entry, making `rc` a
FRI-bound PI of every Dfa-gated turn's deployed proof" — rests on a PI-LAYOUT MISCONCEPTION and does
NOT hold on the deployed light-client fold path:

- **The deployed fold consumes ROTATED-COMPACT legs, not the V1/`BASE_COUNT=209` layout.**
  `prove_turn_chain_recursive → prove_chain_core_rotated` folds `RotatedParticipantLeg`s. A rotated
  leg's dpis are built as `pis[..V1_PI_COUNT=42]` + 4 appended felts (rotated OLD/NEW commit, committed
  height, and ONE folded `caveatCommit` felt at PI 45) = `ROT_PI_COUNT = 46`
  (`circuit/src/effect_vm/trace_rotated.rs:427-432`, `V1_PI_COUNT=42`/`ROT_PI_COUNT=46` at `:186-188`).
  Wide legs append their teeth AFTER 46 (custom's `custom_proof_commitment` at IR2 PI 46..49,
  `custom_program_vk_hash` at 50..53 — `joint_turn_recursive.rs:104`, `generate_rotated_custom_wide`).
- **`SLOT_CAVEAT_MANIFEST_BASE` (≈102) is ABSENT from the rotated fold dpis.** It is computed from the
  V1 209-wide base layout (`pi.rs:425`, `SLOT_CAVEAT_COUNT+1`) and is written only by the V1 base-PI
  builder (`trace.rs:1434-1440`), which the rotated wide generators do NOT run for that region — only
  the first 42 base felts survive into a rotated leg. A tag-20 entry at PI≈102 is therefore a value the
  rotated fold path (and every dual-expose `claim_pi_lo`) NEVER reads. Routing `rc` there churns deployed
  PI values with ZERO soundness benefit = exactly the vacuity-laundering the anti-vacuity law forbids.
- **The rotated caveat carrier is ONE folded felt (PI 45), not 4 exposable `rc` felts.** The rotated
  `RotatedCaveatManifest` commits via the in-AIR `caveatCommit` chain folded to the single PI-45 felt
  (`trace_rotated.rs:431`); `dual_expose_at` needs 4 CONSECUTIVE exposed felts to `connect` to the
  leaf's 4-felt commitment. A single folded commitment cannot carry the 4-felt bind.
- **The faithful emit is VK-affecting — and the code already says so.** Exposing `rc` faithfully needs a
  NEW rotated-cohort PI slot appended after 46 (the twin of custom's 46..49), which extends the
  descriptor's `air_public_targets` = a VK change. `circuit-prove/src/dsl_leaf_adapter.rs:64-81`
  (§"The named big-bang piece") states this verbatim: "**THE BIG-BANG PIECE (VK-affecting
  descriptor-emit):** the deployed turn / precondition descriptor must EMIT the Dfa caveat's
  PI-commitment … at fixed PI slots … That emit rides the VK regen. Until it lands, the DUAL-EXPOSE Dfa
  leg leaf … cannot be minted." When the `[@wave-4]` doc (non-VK) and the code disagree, the code wins
  (MEMORY grounded-what-is rule) — and here the code was right all along.

**Why this is milder than the factory/sovereign/membership walls (but still a STOP).** Those three need
a v12 GEOMETRY WIDENING to faithfully commit an EXTERNAL state anchor (child_vk / owner-pubkey /
authorized-root). dsl needs no widening — `rc` is self-referential (the sub-proof's own 4-felt output,
`custom_proof_pi_commitment`), and the FOLD MECHANISM is fully READY (`prove_dsl_leaf_with_commitment` /
`prove_dsl_binding_node_segmented` reuse the custom path term-for-term, `DslBackingAttack.
dslEngineBinding_of_floor` reduces to Poseidon2-CR). dsl's gate is a plain **rotated-descriptor rc-PI
append + VK regen** (schedule it into the big-bang / VK-epoch lane, an ember/big-bang decision), NOT a
geometry epoch. But it IS VK-affecting, so it is NOT the "non-VK, buildable class-1" the `[@wave-4]`
verdict promised.

**What was NOT done (correctly).** No `mod.rs` Layer A churn (the tag-20-at-`SLOT_CAVEAT_MANIFEST_BASE`
entry is vacuous), no `CarrierWitness::Dsl` fold arm, no `DslBackingAttack → DslBindingFromFold` flip.
`DslBackingAttack.lean` STANDS at HEAD (correct — the emit is not built, and now shown to be VK-gated).
The refutation is the resumable artifact; a re-run resumes from "schedule the VK-affecting rc-emit," not
from a partial non-VK build. Corollary: with dsl reclassified, there is NO remaining non-VK class-1
carrier — every off-custom carrier is either a geometry wall (factory/sovereign/membership/bridge) or a
VK-emit gate (dsl), i.e. all remaining third edges ride a VK/geometry epoch.

---

## 4. THE BIG BANG — is it fireable now? NO. Here's the exact remaining emit.

The memory says "every mechanism built; the bang is purely the emit+regen+flip." That is
TRUE for **custom** and TRUE for the faithful-commitment anchors. It is **NOT yet true**
for the other six carriers' third-edge teeth, nor for the witness-socket generalization.
The bang as one coordinated regen is **NOT fire-able** until those Step-1/Step-2/Step-5
pieces land per carrier.

### What IS ready to fire (built + committed)
- Faithful 8-felt anchors (the six roots) — the precondition. DONE.
- The node8 hash primitive (arity-16, `CHIP_RATE 16`) — the shared hash gadget. DONE.
- `prove_descriptor_leaf_dual_expose_at` — parametric Step-3. DONE.
- All 7 carrier leaves + binding nodes + negative teeth + Lean BackingAttack refutations. DONE.
- Custom: third edge + deployed wiring + `CustomBindingFromFold` positive. DONE (production).
- G5 17/18/19 satisfaction welds + flat-mem boundary anchor. STAGED.
- The apex `#assert_axioms`-clean at current VKs. DONE.

### What must be BUILT before the bang (the actual remaining emit, ordered)
Per carrier (the uniform 5-step build; Steps 3 is done shared, so per carrier = 1,2,4,5):
1. **Step-1 teeth-emit + THE THIRD EDGE** (per carrier, security-critical): on the
   carrier's deployed descriptor add the `PiBinding{First}` publishing the authority tuple
   at TAIL slots `[CARRIER_PI_LO..]` AND the in-AIR gate tying each emitted PI to its
   FAITHFUL committed-state anchor. Bump that descriptor's `public_input_count` only
   (per-descriptor, no ripple to the other 56). This is where the six are UNBUILT.
2. **Step-2 witness socket**: generalize `custom_witness: Option<CustomWitnessBundle>` →
   `carrier_witness: Option<CarrierWitness>` enum on `RotatedParticipantLeg`
   (`joint_turn_aggregation.rs:125`); per-carrier `from_bound_*` projection, fail-closed
   None off-wire. ONE shared restructure (clobber hazard — main-loop owned).
3. **Step-4 leaf + connect**: reuse the built leaf/node adapters. Zero new mechanism.
4. **Step-5 wire + tooth + flip refute→positive**: add the match arm in
   `prove_chain_core_rotated` (THE shared edit, clobber hazard); add a deployed-path fold
   tooth (twin of `custom_binding_deployed_tooth.rs`); flip `*BackingAttack.lean` →
   `*BindingFromFold.lean` positive.

Then, and ONLY then, the coordinated finale:
5. **ONE descriptor regen** exposing every carrier's tuple PIs + emit G5 17/18/19 + the
   flat-mem per-effect weld → **fill the producers** → **ONE apex re-verify**
   (`lightclient_unfoolable` + 5 AssuranceCase guarantees + `deployed_system_secure_grounded`
   clean under the new VKs) → **flip** the whole cluster (deployed default rotates once,
   gated human-go, + devnet re-genesis since commitment VALUES shift).

**Blast radius** (memory §BLAST RADIUS): per-descriptor `public_input_count` (no global
count); append at TAIL `[CARRIER_PI_LO..]`; never touch the shared `[0..46)` prefix. Each
carrier touches only {its bare + wide + welded descriptor} + 3 registry fingerprints.

---

## 5. NOT-FIRE-ABLE-YET — the honest list

1. **The one-shot big bang** — not fireable. Six carriers lack Step-1 (the third edge),
   Step-2 (witness socket), Step-5 (deployed wiring + positive flip). Firing a regen now
   would ship 2–5 without the tie = **vacuous binding** for those six (the exact fail-open
   the law forbids).
2. **The witness-socket generalization** (`CarrierWitness` enum) is unbuilt — a
   prerequisite for wiring any non-custom carrier into `prove_chain_core_rotated`.
3. **The two DEEPEST NEW bindings** are genuine multi-step builds, not emits:
   - bridge: the `note_spend_leaf_adapter.rs` G2 backing leaf (re-prove the real
     note-spend STARK) — folding `bridge_action_air` is UNSOUND, do not shortcut.
   - hatchery-contract: the new on-VK `contract_hash[8]` teeth.
4. **The Merkle-PATH / Hash* in-AIR re-verification** remains the single named TERMINAL
   off-AIR seam for the hash-heavy family (membership path, dsl routing, custom routing
   programs) until the node8 lane-witnessing chain is extended to chain a full Merkle path
   (the node8 primitive exists but `custom_leaf_adapter` still REFUSES chained Hash*/
   MerkleHash). This is the highest-leverage single build after the third edges.
5. **The `fields[0..7]` flat-record ~31-bit residual** (§1d) — allowlisted, self-deleting
   when fields-welded; not a root, does not block carriers, but is a standing ~31-bit
   surface to close.
6. **Custom's deeper per-turn `proofBind True→boundAt` + 4→8-felt lift** — a separate
   gated VK epoch (`CustomApex.lean`, `docs/reference/lean-circuit.md` §Custom). The
   recursion-tree fold is buffed; this in-AIR per-turn gate is a distinct deployment.
7. `[@bae447985]` **The revokeCapability `Rfix 24` apex pin** (§1f seam) — the deployed
   prover rides the REMOVE keystone; the apex registry pin still names the
   authority-only leg. One re-pin + re-verify, small and named.
8. `[@bae447985]` **The whole-image 8-felt STATE_COMMIT digest flag-day** (§1d
   precision) — component roots are faithful; the final 1-felt digest squeeze → 8-felt
   chip-chain cut (`commitment.rs:1219`) is the deliberately-gated separate epoch.
9. `[@wave-1 7c4257824]` **The factory child_vk COMMITTED-CARRIER widening** — the
   BANG-WAVE-1 stop-condition finding (supersedes this map's earlier "child_vk committed
   at PI 38" claim, which was WRONG at HEAD — see the corrected §3 factory row). The
   faithful anchor does not exist and every widening route is bigger than a per-carrier
   wave; pick ONE deliberately:
   - **(a) geometry widening (the true perms/vk pattern):** +8 pre-limbs carrying the
     born child's vk8 on factory rows (`NUM_PRE_LIMBS` 88→96, `B_SPAN` bump = v12
     geometry) — ALL rotated descriptors' VKs move, keystone re-grounds, registry-wide
     regen + Rfix re-pins. The v10→v11-scale campaign; the semantically cleanest anchor
     (the turn's own commitment binds what it birthed).
   - **(b) cells-leaf preimage extension:** factory's inserted leaf digests
     `chip_absorb(addr ‖ value ‖ child_vk[0..8))` instead of arity-2 — descriptor
     blast radius is factory-family-only, BUT forks the shared `HeapLeaf`/`digest8`
     (heap_root.rs, all accumulators) + needs a mixed-arity Lean sorted-insert keystone
     variant + is a cells_root record-SEMANTICS decision (factory-born records bind
     their birth authority; createCell-born stay `(key,key)`) — an ember-decision.
   - **(c) caveat-manifest tag entry:** child_vk8 as a tagged manifest entry riding the
     in-AIR chip-chained caveatCommit→PI 45 — the same pattern as dsl Layer A (wave 3);
     needs manifest-capacity + verifier-twin grounding; converges the factory lane onto
     the dsl/membership lane.
   ALSO under this item: the `child_vk_derived` MISNOMER (`effect_vm_bridge.rs:138`
   lowers `hash_to_bb(owner_pubkey)`) — whichever route lands must either rename the
   field to what it is (the born cell's vm key) or make it carry what it says; today it
   is neither, and the kernel key is `CellId::derive_raw(owner_pubkey, token_id)` (owner
   AND token) while the vm key folds owner_pubkey alone — a second named divergence.
   hatchery-invariant (which RIDES the factory teeth) is blocked behind the same item.
10. `[@wave-2]` **The sovereign third-edge WIDENING** — the BANG-WAVE (sovereign)
    stop-condition finding (§3 sovereign row `[@wave-2]` block). Unlike factory, the owner
    key IS committed faithfully (~124-bit 8-felt BLAKE3 authority digest), but ONLY through
    BLAKE3 folds (`commitment.rs:209/849`) — never as an AIR-reconstructable Poseidon2 limb.
    So P2's in-AIR `Poseidon2(pubkey_limb)==teeth` gate has no faithful anchor to bind, and
    surfacing one is a bigger epoch: (a) a v12 geometry widening adding the pubkey to the
    rotated pre-limbs (`V9_NUM_PRE_LIMBS` full at 88, no free slot — all rotated VKs move +
    registry regen + devnet re-genesis), or (b) in-AIR Ed25519 (the named terminal seam).
    P1 in isolation is forbidden (deployed-PI churn with no soundness gain; flipping the
    refutation on P1 alone launders vacuity). Blocked behind an ember-decision on route
    (a) vs (b). The `SovereignBackingAttack.lean` refutation STANDS.
11. `[@wave-3]` **The membership third-edge WIDENING** — the BANG WAVE (membership)
    stop-condition finding (§3 membership row `[@wave-3]` block). The census verdict that
    launched the wave ("CLASS-1, plain connect to OWNER_CELL_ID, root committed as value") was
    WRONG on both anchors: (i) the sender leaf is `compress(sender_PUBKEY)` (1-felt hash_many),
    absent from the rotated AIR — OWNER_CELL_ID is a different value (`BLAKE3(pubkey‖token)`),
    a different hash (4-felt canonical), AND zero-defaulted in the rotated leg
    (`trace_rotated.rs:372`); (ii) the authorized-root value is uncommitted — only in the
    folded `fields_root` (needs an in-AIR map-open), the manifest tag-11 entry zeroes its
    params, and `verify.rs:523` defers it. The Merkle-PATH seam (§5 item 4) IS now closed for
    the leaf (`MerkleHash` maps via TID_P2), but a witnessed leaf folds vacuously without the
    walled endpoint anchors. Routes: (a) a v12 geometry widening surfacing `compress(pubkey)`
    + a fields_root open (all rotated VKs move + regen + re-genesis), or (b) a semantic
    redefinition of `AuthorizedSet` to 4-felt OWNER_CELL_IDs (first un-defaulting the rotated
    `owner_cell_id`, then the executor domain + set-root re-genesis — an ember-decision). P1 in
    isolation (un-defaulting owner_cell_id alone) is forbidden (deployed-PI churn, no soundness
    gain). The `MembershipBackingAttack.lean` refutation STANDS.

---

## 6. THE SAFE ORDERED NEXT WELD-STEP (what to fire, how not to make it vacuous)

**Do NOT fire a descriptor regen / VK flip yet.** The safe next weld is a per-carrier
BUILD, not the bang. Recommended order (shallow-first — cheapest, exercises the shared
template, de-risks the socket before the DEEPEST binds):

1. **Build the `CarrierWitness` enum socket ONCE** (Step-2, main-loop owned — shared-file
   clobber hazard on `joint_turn_aggregation.rs`). Generalize `custom_witness` →
   `carrier_witness`, keeping custom as the first variant so nothing regresses.
   Fail-closed `None` off-wire (re-exec rung, never fabricated).

2. **FACTORY third edge first** (SHALLOW, and hatchery-invariant rides it):
   `[@wave-1 7c4257824]` **ATTEMPTED AND STOPPED — the stop-condition fired.** The
   instruction below assumed child_vk is committed 1-felt at PI 38; grounding showed it
   is not committed AT ALL (corrected §3 factory row) and every widening route is a
   bigger epoch (§5 item 9). The factory third edge is BLOCKED behind that widening
   decision; do not re-run this step until one of the §5-item-9 routes is chosen and
   landed. The rest of the guidance stands for THAT day: expose the faithful **8-felt**
   child_vk teeth gated against the landed committed carrier. ⚑ **Anti-vacuity guidance:
   DO NOT anchor the tooth at the 31-bit fold** (memory's "factory fold8 gate I almost
   shipped anchored child_vk to the 31-bit col69 = a single linear equation = fake") —
   and equally DO NOT expose unanchored witness-column teeth. The third edge must gate
   against the faithful committed form. Add the deployed-path fold tooth (twin of
   `custom_binding_deployed_tooth.rs`) — honest-accept + forged→UNSAT through
   `prove_turn_chain_recursive → verify_turn_chain_recursive` — and flip
   `FactoryBackingAttack.lean → FactoryBindingFromFold.lean`.

3. **membership + dsl** (SHALLOW, share the caveat-manifest pattern): `[@wave-3]` **membership
   ATTEMPTED AND STOPPED — the stop-condition fired** (§3 membership row + §5 item 11). The
   "4-felt OWNER_CELL_ID leaf-domain redefinition (plain connect)" the census recommended is
   NOT buildable at HEAD: OWNER_CELL_ID is a dead-zero domain-mismatched sentinel in the
   rotated leg and the authorized-root value is uncommitted (only in the folded fields_root).
   Both anchors are walls; building the connect would launder vacuity. Blocked behind an
   ember-decision (route (a) v12 widening vs (b) AuthorizedSet redefinition). **dsl:
   `[@wave-5]` BUILD-PASS ATTEMPTED AND STOPPED** (§3 dsl row + the `[@wave-5]` block). The
   `[@wave-4]` non-VK Layer A is REFUTED at the code level: its fix-site `SLOT_CAVEAT_MANIFEST_BASE`
   (≈102, V1/`BASE_COUNT=209` layout) is ABSENT from the DEPLOYED ROTATED fold dpis (which are
   `pis[..42]` + 4 = `ROT_PI_COUNT=46`, `trace_rotated.rs:427-432`; the rotated caveat carrier is ONE
   folded felt at PI 45, not 4 exposable `rc` felts). dsl's `rc` IS still a self-contained 4-felt
   `custom_proof_pi_commitment` (no v12 widening) and the fold mechanism is READY — but faithful
   exposure needs a NEW rotated-cohort PI slot appended after 46 = a **VK-affecting descriptor-emit**
   (the code's own `dsl_leaf_adapter.rs:64-81` §"THE BIG-BANG PIECE" already says "rides the VK
   regen"). Milder than the geometry walls (self-referential anchor, no widening) but STILL VK-gated,
   so NOT the non-VK class-1 the `[@wave-4]` verdict promised. Layer-A-at-≈102 = vacuity-laundering
   (dead offset) — NOT built. `DslBackingAttack.lean` STANDS. **Net: NO remaining non-VK class-1
   carrier; every off-custom third edge rides a VK or geometry epoch.**

4. **sovereign P1 then P2**: `[@wave-2]` **ATTEMPTED AND STOPPED — the stop-condition
   fired** (§3 sovereign row, the `[@wave-2]` block). P1 (non-VK) fills the dead-zero
   KEY_COMMIT teeth from `before_cell.public_key()` + adds the sovereign arm; P2 (VK)
   welds the `IS_SOVEREIGN_CELL`-gated in-AIR `Poseidon2(pubkey_limb)==teeth`. But P2's
   faithful anchor does not exist at HEAD: the owner pubkey is committed only via BLAKE3
   folds (`commitment.rs:209/849`), never as an AIR-reconstructable Poseidon2 limb, so the
   in-AIR gate needs either (a) a v12 geometry widening surfacing the pubkey as a rotated
   pre-limb (no free slot — `V9_NUM_PRE_LIMBS` full at 88) or (b) in-AIR Ed25519 (the
   named terminal seam) — both bigger than a per-carrier wave. Do NOT run P1 alone
   (changes deployed PI values with no soundness gain; flipping the refutation on P1 alone
   launders vacuity). Blocked behind an ember-decision on route (a) vs (b), like factory.
   Ed25519 stays off-AIR.

5. **bridge + hatchery-contract** (DEEPEST, own lanes): bridge = the `note_spend_leaf_
   adapter.rs` G2 backing leaf + mint_hash-in-circuit + `mintV3` PI expose (NEVER fold
   `bridge_action_air`); hatchery-contract = the `contract_hash[8]` teeth on
   FactoryDescriptor.

6. **THEN the coordinated bang** (§4 step 5): one regen + producer fill + one apex
   re-verify + gated flip + devnet re-genesis.

**The anti-vacuity discipline for EVERY step** (the whole point): a carrier is only truly
folded when the THIRD EDGE is present — `leg.teeth == committed-authority` enforced in the
DEPLOYED AIR against a FAITHFUL (8-felt, not 31-bit) committed anchor. The negative tooth
must bite through the real `prove_turn_chain_recursive → verify_turn_chain_recursive` path
(honest-accept AND forged→UNSAT), not just a unit-level `forged_*_does_not_fold`. Prove
each load-bearing spec non-vacuous (true AND false) before flipping its BackingAttack to
BindingFromFold. The BackingAttack is not deleted until its positive replacement bites.

---

## Partition (to avoid clobber, per memory §IMPLEMENTATION SWARM PARTITION)
factory + hatchery share the CreateCellFromFactory leg (one lane). dsl + membership share
the caveat-manifest pattern (one lane). bridge = own (note_spend leaf). sovereign = own (P1
non-VK first, then P2). The `prove_chain_core_rotated` match arm + the `CarrierWitness`
socket = ONE integration-lane edit (main loop owns — shared-file clobber hazard).
