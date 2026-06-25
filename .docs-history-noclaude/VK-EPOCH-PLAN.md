# VK-EPOCH-PLAN — the structural unlock for 18-of-30 effects on-wire + light-client-verifiable

Status: DESIGN (read-mostly grounding spike). Base = green HEAD `b92a210c2`.
This is checklist **(C)** of `docs/SAFELY-LIVE-CHECKLIST.md` — the single highest-leverage box.
Ground for every claim is `file:line` at HEAD.

> **The headline correction this spike forces.** The checklist's box-C one-liner ("`compute_commitment`
> (cell_state.rs:76) absorbs the record-digest + sorted roots") is a *stale framing of an
> already-mostly-closed gap*. The cell-side commitment the light client actually pins (`Cell::state_commitment`
> → `compute_canonical_state_commitment`, `cell/src/commitment.rs:192`) ALREADY absorbs lifecycle, perms,
> vk, fields_root, the 8 system roots (nullifier/commitment/deleg/…), heap_root, and committed_height. The
> per-effect-VM `compute_commitment` (`circuit/src/effect_vm/cell_state.rs:128`) is **not** the binding wire
> commitment — it is the *in-AIR continuity column* + a lossy single-felt `record_digest` residue. The REAL
> VK-epoch is therefore not "teach the commitment new columns" — it is **make the in-circuit forcing
> reflect each write so the anchored post-commit cannot be the producer's bare claim**, and resolve the
> two-commitment split (v1 lossy STATE_COMMIT vs wide v9 STATE_COMMIT) so the light client rides ONE
> faithful surface. The "absorb the roots into compute_commitment" work is the **last residue** (the cap/
> nullifier/deleg map-op write witnesses), not the whole epoch.

---

## 1. The current commitment surfaces (file:line) — THREE, not one

There are three distinct commitment computations in the deployed Rust, plus the Lean apex target. The
audit's "compute_commitment binds nothing" conflates them. Disentangled:

### 1a. The in-AIR continuity column — `CellState::compute_commitment` (the LOSSY one)
`circuit/src/effect_vm/cell_state.rs:128-140`. Preimage tree:
```
inter1 = hash_4_to_1(balance_lo, balance_hi, nonce, field[0])
inter2 = hash_4_to_1(field[1..4])
inter3 = hash_4_to_1(field[5..7], capability_root)
commit = hash_4_to_1(inter1, inter2, inter3, record_digest)   ← cell_state.rs:139
```
`record_digest` (`cell_state.rs:40`, `:113-124`) is a SINGLE Poseidon2 felt folding *all* authority
residue (permissions / vk / lifecycle / deathCert / delegate / mode / system roots / `fields[8..]`).
This is the `STATE_COMMIT` column the v1 trace carries, and the 8-felt salt-expansion
`compute_commitment_8` (`cell_state.rs:165-192`) feeds the v1 `OLD_COMMIT`/`NEW_COMMIT` PIs (base 0/8,
`circuit/src/effect_vm/pi.rs:26-30`). **The lossiness is real here**: two post-states differing only in,
say, lifecycle collapse into the same `record_digest` unless something *forces* the residue felt to the
correct value (it is a prover-chosen FREE input absent a gate).

### 1b. The cell-side wire commitment — `compute_canonical_state_commitment` (the FAITHFUL BLAKE3 ctx-v9)
`cell/src/commitment.rs:192`. This is what `Cell::state_commitment()` returns (`cell/src/cell.rs:499-501`),
which is what the executor pins as `entry.old_commitment`/`new_commitment` →
`OLD_COMMIT`/`NEW_COMMIT` (8-felt) in `turn/src/executor/atomic.rs:753-757`, `:777`, `:807-811`.
It absorbs (verbatim absorption sites):
- balance / nonce / fields[0..16] (the body),
- `committed_height` (`commitment.rs:346`),
- `swiss_table_root`, `refcount_table_root` (`:350-351`),
- `fields_root` (the overflow user-field map, `:364`),
- **`system_roots_digest()`** (`:378`) — the 8 side-table roots: escrow/queue/refcount/sturdyref/
  **deleg/nullifier/commit**/sealedBoxes (`cell/src/commitment.rs:366-371`),
- `heap_root` (`:378+`),
- lifecycle / perms / vk / deathCert (folded earlier in the body / via `compute_authority_digest_felt`,
  `cell/src/commitment.rs:751`).

**So the cell-side commitment ALREADY binds every column the 18 effects write.** A light client that
pins this 8-felt commit *already* cannot accept a post-state differing only in lifecycle/perms/vk/
nullifier-root — IF the proven transition is forced to produce that exact post-cell.

### 1c. The wide rotated in-circuit commitment — `compute_canonical_state_commitment_v9_felt` (37 limbs)
`cell/src/commitment.rs:1020`, `_v9_8` at `:1052`. The 37-limb `wireCommitR` (Lean
`RotatedCommitDifferential.rotatedLimbs`, `metatheory/Dregg2/Circuit/RotatedCommitDifferential.lean:98`)
NAMES distinct limbs: `authorityDigest`@24, `capRoot`@25, `nullifierRoot`@26, `commitmentsRoot`@27,
`heapRoot`@28, `lifecycle`@29, `epoch`@30, `committedHeight`@31, `lifecycleDisc`@32, `permsDigest`@33,
`vkDigest`@34, `mode`@35, `fieldsRoot`@36 (limb names: `cell/src/commitment.rs:636-646`,
`V9_NUM_PRE_LIMBS = 37`). This is computed IN-TRACE as the rotated block's `B_STATE_COMMIT` (col 38,
`circuit/src/effect_vm/trace_rotated.rs:148`) and published as the wide 16-felt anchor (the LAST 16 PIs),
pinned in `turn/src/executor/proof_verify.rs:622-626` from `before8`/`after8`. The 1-felt
`V1_PI_COUNT`(42/43) rotated override is **RETIRED** in favor of this wide 8-felt anchor
(`proof_verify.rs:607-615`).

### 1d. The Lean apex target — `recStateCommit` / `S_live.commit`
`metatheory/Dregg2/Circuit/StateCommit.lean:196`: `recStateCommit k t = cmb (cellDigest …) (RH k)`.
`RH` (the rest-hash) is *proven injective on the whole `RecordKernelState`* via `RestHashIffFrame`
(`StateCommit.lean:229`) — it binds accounts, caps, nullifiers, revoked, commitments, bal, slotCaveats,
factories, lifecycle, deathCert, delegate, delegations, delegationEpoch[At], heaps (15 components,
`metatheory/Dregg2/Exec/RecordKernel.lean:309`). `S_live.commit ≡ recStateCommit` by `rfl`
(`metatheory/Dregg2/Circuit/ClosureSurface.lean:125`). The deployed `_v9` (1c) is the concrete
realization the apex's `RH`-binds-everything assumption is *meant to* discharge — the
`RotatedKernelRefinement*` modules carry the per-root force-lemmas (`metatheory/Dregg2.lean:565-570`).

### THE EXACT DELTA
| surface | binds the 18-effects' columns? | gating it light-client-faithful |
|---|---|---|
| 1a v1 lossy `compute_commitment` (cell_state.rs:139) | NO — one opaque `record_digest` felt | the residue felt is prover-free unless a gate forces it |
| 1b cell-side `compute_canonical_state_commitment` (commitment.rs:192) | **YES** — every column absorbed | only as faithful as the *claimed* post-cell (executor-trusted, see §4) |
| 1c wide `_v9` 37-limb (commitment.rs:1020) | **YES** — distinct named limbs | the WAVE in-circuit gates force some limbs (disc); others ride the off-cell anchor |
| 1d Lean `recStateCommit` (StateCommit.lean:196) | YES (proven on whole kernel) | the proof target the wire must converge to |

**The VK-epoch delta is the v1↔v9 split**: the v1 OLD/NEW_COMMIT (PI 0/8, the ~124-bit anchor that
`atomic.rs:806-811` hard-checks) rides 1b *lossily projected through 1a's continuity column*; the wide
1c anchor rides alongside it. The epoch retires the v1 lossy STATE_COMMIT and makes the published binding
the **wide v9** everywhere, AND closes the per-effect *forcing* gates so the wide post-commit cannot be a
bare producer claim.

---

## 2. The 18 effects → which root binds each write-column

From `docs/SAFELY-LIVE-CHECKLIST.md:14-17` (8 on-wire / 18 not-on-wire / 4 modelled-floor). The 18 split
into 5 families; per family, the write-column and the root that binds it once the epoch lands:

| # | effect | write-column | binding root (1c limb) | forcing status at HEAD |
|---|---|---|---|---|
| 1 | setPermissions | perms_digest | `permsDigest`@33 + authorityDigest@24 | WAVE-2 limb shipped (`rotateV3WithPermsVKGate`); the AUTHORITY payload still rides the record-pin **off-cell anchor** (`proof_verify.rs:727-729`, `apply_effect_to_cell` re-derive — full-node, not light-client) |
| 2 | setVK | vk_digest | `vkDigest`@34 + authorityDigest@24 | same as #1 |
| 3 | cellSeal | lifecycle disc + payload | `lifecycleDisc`@32 (IN-CIRCUIT gate) + `lifecycle`@29 (payload) | DISC forced in-circuit (`rotateV3WithDiscGate`, `proof_verify.rs:668-676`); PAYLOAD off-cell anchor |
| 4 | cellUnseal | lifecycle disc | `lifecycleDisc`@32 | disc in-circuit; payload off-cell |
| 5 | cellDestroy | lifecycle disc + deathCert | `lifecycleDisc`@32 + `lifecycle`@29 (folds deathCert) | disc in-circuit; deathCert off-cell |
| 6 | receiptArchive | lifecycle(Archived) | `lifecycleDisc`@32 | disc in-circuit; MODELLED-FLOOR spec-bridge open (checklist B) |
| 7 | refusal | fields_root(audit) | `fieldsRoot`@36 + authorityDigest@24 | record-digest off-cell anchor (`proof_verify.rs:698`) |
| 8 | makeSovereign | mode | `mode`@35 | WAVE-3 limb (`rotateV3WithModeGate`); rebind not yet forced (VALUE_PARTIAL, CFC.md) |
| 9 | setFieldDyn | fields_root | `fieldsRoot`@36 | WAVE-3 limb (`rotateV3WithFieldsRootGate`); value-on-readback partial |
| 10 | createCell | accounts/cells_root | `cellsRoot`@0 (cross-cell set-insert) | grow-gate `generate_rotated_create_cell_trace_with_accounts_tree` (`trace_rotated.rs:755`) — in-circuit set-insert |
| 11 | createCellFromFactory | accounts + factory | `cellsRoot`@0 | as #10 |
| 12 | spawn | accounts + cap handoff | `cellsRoot`@0 + `capRoot`@25 | birth via #10; cap handoff frozen (CFC self-contradiction) — needs §A cap-write |
| 13 | noteCreate | commitments_root | `commitmentsRoot`@27 | grow-gate (note-create analog of `generate_rotated_note_spend_trace_with_nullifier_tree`) |
| 14 | noteSpend | nullifier_root | `nullifierRoot`@26 | **IN-CIRCUIT** map-op grow-gate (`generate_rotated_note_spend_trace_with_nullifier_tree`, `trace_rotated.rs:672`) — the EXEMPLAR |
| 15 | delegate | cap_root (write) | `capRoot`@25 | **BLOCKED** — cap-tree write-witness DA gap (§A) |
| 16 | introduce | cap_root (write) | `capRoot`@25 | BLOCKED (§A) |
| 17 | delegateAtten | cap_root (write) | `capRoot`@25 | BLOCKED (§A) |
| 18 | revokeDelegation | deleg-tree / cap_root | `capRoot`@25 (wrong primitive — needs deleg-tree, checklist C-2) | BLOCKED (§A) + deleg-tree column |

**The mechanism that makes a write light-client-faithful is per-family:**
- **In-circuit gate** (the gold standard, no trusted post-cell): noteSpend (#14, map-op grow-gate),
  lifecycle DISC (#3-6, `rotateV3WithDiscGate`), createCell (#10-11, accounts set-insert grow-gate).
  These are *already* light-client-faithful for their forced limb.
- **Off-cell anchor** (full-node only — the verifier re-derives the post-cell via
  `apply_effect_to_cell` and anchors the residue PI, `proof_verify.rs:718-735`): setPermissions/setVK/
  refusal (record-digest) and the lifecycle *payload*. A **ledgerless light client cannot run this
  re-derivation** — it has the consumed effect's hash, not the pre-cell. So these are forced for a
  full node but NOT a light client. **This is the actual residue the VK-epoch must convert from anchor
  to in-circuit gate.**
- **Map-op write, blocked** (§A): the four cap-write wrappers (#15-18) — the write witness
  (`map_heaps`) data-availability gap.

---

## 3. The cap-write data-availability blocker (§A) — the gating sub-task

From `docs/SAFELY-LIVE-CHECKLIST.md:20-53`, verified at HEAD:
- The write wrappers (`delegate/introduce/delegateAtten/revokeDelegationWriteCapOpenVmDescriptor2R24`)
  ARE in `V3_STAGED_REGISTRY_TSV` (registry availability RESOLVED).
- Each carries a genuine `map_op` read+insert binding BEFORE cap-root (col 65) → AFTER cap-root (col 87)
  via sorted-Poseidon2 — the cap-tree analog of noteSpend's nullifier map-op.
- **The blocker**: `prove_effect_vm_cap_open` threads NO `map_heaps` (passes `&[]`,
  `sdk/src/full_turn_proof.rs`), and `CapMembershipWitness` carries only one opened leaf + path, NOT the
  cell's full sorted c-list. `node/src/turn_proving.rs` has the consumed cap, not the whole c-list. So
  routing to the write wrapper produces an UNPROVABLE proof — it fail-closes (no silent forge, proven by
  `write_cap_open_wrapper_requires_cap_tree_write_witness_no_silent_forge`).

**This is a 5-step data-plumbing task** (checklist A, lines 44-48), NOT VK-affecting in itself:
extend `ConsumedCapWitness`/`CapMembershipWitness` → plumb from `node/src/turn_proving.rs` → add a
cap-tree→`map_heaps` bridge (mirror `generate_rotated_note_spend_trace_with_nullifier_tree`) → thread
through `prove_effect_vm_cap_open` → re-point `cap_open_route_for_run`. It runs in PARALLEL to the
commitment epoch and gates effects #15-18 only.

---

## 4. The VK-affecting blast radius — the flag-day checklist

Changing the *binding wire commitment* (retiring v1 lossy STATE_COMMIT, promoting wide v9 to the sole
anchor + adding in-circuit force gates) is VK-affecting because it changes the AIR's published-PI
structure and the constraint set. What regenerates:

1. **The VK itself.** `verify_vm_descriptor2` over the widened descriptors → new verifying key. Every
   descriptor whose `public_input_count` or constraint set changes re-derives (the record-pin family is
   already at 63 PIs, `proof_verify.rs:686`; promoting more families to in-circuit gates widens more).
2. **The descriptors.** `circuit/src/effect_vm_descriptors.rs` — the per-effect `rotateV3With*Gate`
   variants. New in-circuit force gates for the record-digest/lifecycle-payload families (replacing the
   off-cell anchors) are new descriptor constraints → `scripts/check-descriptor-drift.sh` re-baseline.
3. **The genesis image / deployed devnet state.** If the *sole* anchor moves from v1 to v9, the stored
   `old_commitment` per cell must be the v9 form. AUDIT THIS: `Cell::state_commitment()`
   (`cell/src/cell.rs:499`) returns the *cell-side BLAKE3 v9* (1b) already — so the ledger's stored
   commitments are ALREADY the faithful form; the v1 8-felt (1a) is a *derived projection* for the PI
   anchor. **Migration is likely NIL for stored state** — the cell-side commitment doesn't change; only
   the *circuit's PI layout / anchor selection* changes. (CONFIRM with a one-cell round-trip before the
   flag-day: does `compute_canonical_state_commitment` change byte-for-byte? It should NOT — the named
   limbs are already absorbed, §1b. If it does not change, **no state re-commit is needed**.)
4. **Test fixtures.** Frozen descriptor JSON / proof fixtures pinning PI prefixes:
   `circuit/tests/effect_vm_rotation_flip.rs`, `circuit/tests/effect_vm_commit_lean_differential.rs`,
   `sdk/tests/*`, the rotated-descriptor JSON constants (`rotated_descriptor_json`,
   `effect_vm_rotation_flip.rs:83`). These re-baseline against the new VK.
5. **The Lean differential.** `RotatedKernelRefinement*` force-lemmas (`metatheory/Dregg2.lean:565-570`)
   per converted family — each off-cell-anchor→in-circuit-gate conversion needs its `_sat` discharger so
   editing the gate reds the apex (the checklist's green-check shape).
6. **The light-client verifier path.** `verify_proof_carrying_turn` / `proof_verify.rs:542-745` — drop
   the off-cell `apply_effect_to_cell` anchor block (`:718-735`) once the gate is in-circuit; the wide
   anchor (`:622-626`) becomes load-bearing alone.

**What does NOT regenerate** (the de-scoping wins): the cell-side commitment bytes (§1b already faithful)
→ **no ledger state migration**; the `system_roots_digest` / `fields_root` absorption (already in
`commitment.rs`); the noteSpend / createCell / lifecycle-disc gates (already in-circuit).

---

## 5. Staged vs atomic — recommendation: STAGED (the WAVE pattern continues)

The mechanism is **already staged and proven**: the WAVE flag-day pattern appends committed pre-limbs to
the wide rotated commitment with a selector-gated in-circuit weld, one family at a time:
- WAVE 0: authority-residue continuity (`HORIZONLOG.md:1047`).
- WAVE 1 LIFECYCLE-DISC: `NUM_PRE_LIMBS 32→33`, `B_DISC=32`, `rotateV3WithDiscGate` (`HORIZONLOG.md:933-954`).
- WAVE 2 PERMS/VK: `33→35`, `B_PERMS=33`/`B_VK=34`, `rotateV3WithPermsVKGate` (`HORIZONLOG.md:900-931`).
- WAVE 3 MODE/FIELDS_ROOT: `35→37`, `B_MODE=35`/`B_FIELDS_ROOT=36` (`commitment.rs:642-646`, in-progress).

**The record-digest+roots absorption is NOT a new wave — the limbs already exist (§1c).** What remains is
NOT appending limbs; it is **converting the off-cell anchors to in-circuit force gates** for the families
that still ride the anchor (record-digest: setPermissions/setVK/refusal; lifecycle payload). Each such
conversion is its own mini-flag-day (it changes that family's descriptor VK), driveable independently:

- **STAGE A (cap-write DA, §3)** — VK-free data plumbing; unblocks #15-18. PARALLEL.
- **STAGE B (record-digest in-circuit force)** — convert setPermissions/setVK/refusal from off-cell
  anchor to an in-circuit `rotateV3WithAuthorityForceGate` that forces `authorityDigest`@24 to the
  effect's mandated value as the lifecycle-disc gate forces the disc. VK-affecting, family-scoped.
- **STAGE C (lifecycle-payload in-circuit force)** — the deathCert/reason_hash opaque payload at
  `lifecycle`@29 (the disc is already in-circuit). Belt-and-suspenders today (`proof_verify.rs:674-676`);
  convert to a gate. VK-affecting, family-scoped.
- **STAGE D (note-create grow-gate)** — `commitmentsRoot`@27 in-circuit (mirror noteSpend). VK-affecting.
- **STAGE E (deleg-tree column, checklist C-2)** — `refreshDelegation`/`revokeDelegation` need a deleg-tree
  map-op + runtime column (cap_root is the wrong primitive, `SAFELY-LIVE-CHECKLIST.md:74`). VK-affecting.
- **STAGE F (anchor cutover)** — once B/C/D land, the v1 lossy STATE_COMMIT (1a) anchor is dead weight;
  retire it so the wide v9 (1c) is the sole published binding. THE flag-day proper.

**Recommendation: STAGED, family-at-a-time, F last.** Atomic is unnecessary and risky — each family's
conversion is independently provable (its own `_sat` discharger reds the apex) and independently
deployable behind its descriptor's VK. The "VK epoch" is a *sequence of family-scoped VK bumps*, not one
monolith, because the binding commitment (§1b) and most gates (disc/noteSpend/createCell) are already
faithful. F (the v1-anchor retirement) is the only step touching the shared PI prefix — schedule it as
the single coordinated landing once every family rides an in-circuit gate.

---

## 6. The green check that proves it closed

The checklist's stated green (`SAFELY-LIVE-CHECKLIST.md:73`):
> a light-client test rejecting a post-state differing ONLY in (lifecycle | permissions | vk | nullifier-root)
> under the deployed VK.

Sketch (one test per converted family; the lifecycle and noteSpend ones can pass TODAY for the in-circuit
gates, which makes them the regression guard the conversions must preserve):

```rust
// circuit/tests/vk_epoch_light_client_binding.rs  (new)
//
// For each family F in {lifecycle, permissions, vk, nullifier_root, commitments_root, mode, fields_root}:
//   1. Build an HONEST turn that writes column F (e.g. setPermissions { cell, perms: P }).
//   2. Prove it -> proof π, claimed post-commit C_honest (the wide v9 8-felt).
//   3. Construct a FORGED post-cell identical to the honest post-cell EXCEPT column F
//      (e.g. perms: P' != P), and its wide v9 commit C_forged.
//   4. Re-run the LIGHT-CLIENT verify path (verify_proof_carrying_turn / verify_vm_descriptor2)
//      with the SAME proof π but anchoring after8 := bytes32_to_felt8(C_forged).
//   5. ASSERT verify REJECTS (the in-circuit force gate makes the proof's bound forced-limb
//      disagree with the C_forged anchor => verify_vm_descriptor2 UNSAT).
//   6. CRITICAL light-client discriminator: the verify path must reject WITHOUT calling
//      apply_effect_to_cell (no pre-cell re-derivation). Assert the reject comes from the
//      descriptor's in-circuit gate, not the off-cell anchor block (proof_verify.rs:718-735) —
//      i.e. run with the anchor block DISABLED and it must still reject. This is the
//      light-client-vs-full-node discriminator the epoch closes.
```

The Lean side (per family): editing the family's `rotateV3With*Gate` reds the apex (the mutation-test
shape, `SAFELY-LIVE-CHECKLIST.md:62`) — i.e. `<family>_descriptorRefines_sat` consumes the in-circuit
gate, so removing the force-constraint breaks the refinement proof. This is what distinguishes a genuine
gate from a published-value pin.

**Vacuity guard** (per `feedback-dont-launder-vacuity`): each test must show the verify ACCEPTS the
honest C_honest AND REJECTS the forged C_forged — both poles, so the binding is non-vacuous.

---

## 7. Honest size estimate

- **§3 cap-write DA plumbing (STAGE A)** — 5 concrete steps, no VK change, the noteSpend bridge is the
  template. **~1 day** (the witness-type extension + node plumbing is the bulk).
- **STAGE B (record-digest in-circuit force)** — 1 new descriptor gate variant + its `_sat` discharger +
  verifier-path simplification + fixtures + VK bump. **~1 day** for the family (3 effects share the gate).
- **STAGE C (lifecycle payload)** — the disc is done; the payload gate is a smaller delta. **~half a day.**
- **STAGE D (note-create grow-gate)** — mirror noteSpend exactly. **~half a day.**
- **STAGE E (deleg-tree column)** — a NEW map primitive (deleg-tree, distinct from cap-tree). **~1-2 days**
  (the runtime column + map-op + descriptor + Lean column are genuinely new).
- **STAGE F (v1-anchor retirement flag-day)** — the coordinated landing once B-E are in; touches the
  shared PI prefix + every fixture. **~1 day**, but must be scheduled as the single flag-day.
- **The Lean `_sat` dischargers** run as parallel subagent proof work alongside each stage.

**Total: a coordinated multi-step epoch, ~5-7 focused days**, NOT a single blind build and NOT hours. The
de-scoping insight that shrinks it from the original framing: the binding commitment (§1b) already
absorbs every column → **no ledger-state migration**, and the gold-standard in-circuit gates
(noteSpend/disc/createCell) already exist as templates → the work is *converting anchors to gates*
family-by-family, each independently provable and deployable, with F as the one true flag-day.

---

## Appendix — the one verification to run FIRST (the migration question)
Before any flag-day, confirm **no ledger-state re-commit is needed** by checking that
`compute_canonical_state_commitment` (the stored `old_commitment` source, §1b) does NOT change across the
epoch — it already absorbs lifecycle/perms/vk/system_roots/fields_root (`cell/src/commitment.rs:346-378`,
`:751`). The epoch changes the CIRCUIT (descriptors/VK/anchor selection), not the cell-commitment bytes.
If a one-cell round-trip (`Cell::state_commitment()` before vs after the branch) is byte-identical, the
deployed devnet state (`34.224.208.52`) needs NO re-commit — only a VK/binary redeploy. **This is the
single most blast-radius-shrinking fact and must be confirmed empirically before scheduling STAGE F.**
