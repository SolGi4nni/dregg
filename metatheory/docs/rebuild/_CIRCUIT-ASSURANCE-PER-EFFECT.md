# Circuit Assurance — Per-Effect HONEST Ledger (FINALIZED)

**Date:** 2026-06-08 · FINALIZED after the deep-verify phase · author: per-effect circuit-assurance review.

This is the truth about how verified the **emitted EffectVM circuit** (`Dregg2/Circuit/Emit/*`)
actually is, per effect. It is NOT a completion count. Differential agreement is NOT counted as
proof. The economic/frame leg is NOT counted as full verification.

**Finalization pass (2026-06-08):** every cited theorem below was re-read at its `file:line` and
every class was re-confirmed against the code (not against any prior summary). `#print axioms` re-run
on the keystone + representatives: `transferDescriptor_full_sound`,
`transferDescriptor_commit_binds_state`, `tampered_rejected`, `noteSpendDescriptor_full_sound`,
`noteSpend_no_double_spend_is_turn_property` all depend on exactly `{propext, Classical.choice,
Quot.sound}` (the last is `{propext, Quot.sound}`). The full owned surface — all 54 `EffectVmEmit*`
modules + `EmitAllJson` + `EmitGraduate` + `Dregg2.Circuit.TurnEmit` +
`Dregg2.Circuit.CoordinatedTurnEmit` — builds GREEN: **`lake build` completed successfully, 3198 jobs,
0 errors** (warnings only). Two stale-by-drift build breaks were found+fixed during this pass (neither a
soundness regression): (i) `EffectVmEmitRecordRoot.lean:319` `#guard` hardcoded the transfer
descriptor's constraint count as `14+14+4+3 = 35`, but the selector-binding `sel[S]=1` tooth (task #74)
added one gate ⇒ now `36 = 14+14+4+3+1` (the `recordVmDescriptor_constraints_eq` `rfl` theorem still
holds — record inherits transfer's constraints exactly); (ii) `EmitAllJson.lean` listed the four
root-parameterized queue descriptors (`queueAllocate`/`queueDequeue`/`queueEnqueue`/`queueResize`) as
bare values, but they are now `ℤ → EffectVmDescriptor` functions of the OPAQUE side-table parameter —
instantiated at the canonical `0` (the descriptor shape is independent of that scalar; it is exactly the
class-C queue gap). No hand-AIR touched; no graduate-and-delete.

## The bar (l4v REAL, ember-corrected)

A class **(A) GENUINELY VERIFIED** effect must have a from-scratch theorem of the shape

> `satisfiedVm <descriptor> env ⟹ FULL post-state semantics of the effect`

where **FULL** means *every field the effect TOUCHES is moved-or-frozen-as-the-spec-says*,
**the side-table / membership root that IS the effect is bound**, **the anti-ghost commitment
covers ALL of it** (tampering any of it ⇒ the published `state_commit`/root changes ⇒ UNSAT),
and the statement is **connected to the verified executor `recKExec`** (or universe-A's validated
`*_full_sound`) and is **meaningful + non-vacuous** (a true witness AND a refuted tamper witness).

The keystone that defines class A is **Transfer** (see below). Every other effect is measured
against it.

### What the descriptor's anti-ghost commitment ACTUALLY covers

CRITICAL FACT that drives almost every downgrade below. The deployed EffectVM row's `state_commit`
absorbs **exactly 13 state-block columns**: `bal_lo, bal_hi, nonce, fields[0..7], cap_root`
(`EffectVmEmitTransferSound.absorbedCols`, `absorbed_determined_by_commit`). It does **NOT** absorb:

- the cap-table digest as a *computed* root (only the `cap_root` *column value*, which descriptors
  carry as an opaque parameter `cap_digest_new` — the cap-table membership is never recomputed in-row);
- any side-table digest (`nullifiers`, `escrows`, `queue`, `seals`, `sturdyrefs`, `supply totals`)
  **unless that digest is carried inside one of the 13 state-block columns**;
- the `system_roots` sub-block. The `Exec.SystemRoots` record-layer commitment (`cellCommitS`,
  `systemRootsDigest_binds_pointwise`) binds those roots, but `auxCol SYSTEM_ROOTS_DIGEST = 186`
  is **PAST `EFFECT_VM_WIDTH = 186`** — i.e. the running prover carries **no such column**, and the
  per-effect files PROVE this gap as `*_root_not_in_descriptor_commit` (e.g.
  `EffectVmEmitBridgeCancel.escrow_root_not_in_descriptor_commit:454`).

So: an effect whose real semantic content is a **side-table mutation** is bound by the descriptor
**only if that side-table's root is carried in `fields[i]`** (a state-block column) and the descriptor
constrains the column transition. That is true for exactly ONE family below (**queue**, via `fields[4]`);
for every other side-table effect the binding lives in a *separate* record-layer commitment the
deployed row does not carry. Those are **class C**, not A.

---

## Class definitions used in the table

- **(A) GENUINELY VERIFIED** — from-scratch `satisfiedVm ⟹ full post-state`, the moved field(s) +
  every touched root bound in the descriptor's own `state_commit`, anti-ghost on all of it, connected
  to `recKExec`/universe-A, non-vacuous. **The effect's real content is the bound move.**
- **(B) DIFFERENTIAL-ONLY** — descriptor == hand-AIR agreement proven, but no from-scratch
  full-semantics theorem (or it pins strictly less than the touched state). Cross-check, not proof.
- **(C) ECONOMIC/FRAME-LEG-ONLY** — the descriptor genuinely proves+binds the *frozen frame* and/or
  a *balance/nonce* leg with anti-ghost, **but the field/side-table that IS the effect is NOT bound by
  the descriptor's commitment** (it rides `params`/`effects_hash`/a separate record-layer root).
  Conservation ≠ correctness. This is the dominant class.
- **(D) UNVERIFIED** — no meaningful from-scratch soundness for the effect.

Every effect below is `#assert_axioms`-clean (⊆ {`propext`, `Classical.choice`, `Quot.sound`}); no
`sorry`, no `:= True`, no `native_decide` (verified: the only textual matches are header comments
asserting their absence). Build green (`lake build` of the touched Emit + turn modules: **3198 jobs,
0 errors**, warnings only — re-run on this finalization pass).

---

## THE LEDGER

| # | Effect (Emit module) | Class | Cited theorem (file:line) | What's bound vs the REAL gap |
|---|----------------------|:-----:|---------------------------|------------------------------|
| 1 | **transfer** (`EffectVmEmitTransfer`) | **A** | `EffectVmEmitTransferSound.transferDescriptor_full_sound:238` + `.transferDescriptor_commit_binds_state:346` + `.tampered_rejected:413` + `EffectVmEmitTransferUnify.unify_debit_exec:293` / `unify_credit_exec:297` (→ `recKExec`) | KEYSTONE. `bal_lo` moved by signed amount, `bal_hi`/8 fields/`cap_root`/`reserved` frozen, all 13 cols anti-ghosted, connected to `recKExec` via `recKExec_iff_spec`. The ONE honest residual: descriptor TICKS nonce, `recKExec` FREEZES it — the nonce is a runtime counter off-universe-A (`TransferUnify §2`, `good_nonce_frozen_not_ticked:415`). Both legs (src debit, dst credit) unified. |
| 2 | **mint** (`EffectVmEmitMint`) | **A** | `mintDescriptor_classA:§8½` (`CellMintSpec` + commit + executor agreement) = `mintDescriptor_full_sound:225` + `mintDescriptor_commit_binds_state:256` + `unify_mint_exec:291` (→ `recCMintAsset`) | **CLASS-A PROMOTED (per-cell, the transfer bar).** The supply-credit IS a `bal_lo` move — an in-commitment column, bound + anti-ghosted (13 cols) + executor-unified, the WHOLE per-cell transition. The only residual — the *global supply total* — is a CROSS-CELL / TURN-LEVEL accumulator (the exact analogue of transfer's two-sided conservation the keystone assigns to the turn layer), NOT a per-cell state-block gap. |
| 3 | **burn** (`EffectVmEmitBurn`) | **A** | `burnDescriptor_classA:§8½` (`CellBurnSpec` + commit + bal/frame executor agreement) = `burnDescriptor_full_sound:329` + `burnDescriptor_commit_binds_state:369` + `unify_burn_exec:433` (→ `recCBurnAsset`) | **CLASS-A PROMOTED (per-cell, the transfer bar).** `bal_lo` debit + frame freeze bound + anti-ghost (13 cols) + executor-unified on the bal/frame clauses. Same supply-total turn-level residual as mint + the named nonce-tick divergence (`exec_nonce_is_frozen_not_ticked`, off-universe-A like transfer's nonce). |
| 4 | **incrementNonce** (`EffectVmEmitIncrementNonce`) | **A−** | `incNonceDescriptor_full_sound:233` + commit-binds | The effect IS the nonce tick — an in-commitment state-block column, bound + anti-ghosted. No `unify_*_exec` connector to `recKExec` (universe-A has no nonce-tick effect; documented). Meaningful but executor-orphaned ⇒ A−, not full A. |
| 5 | **queueEnqueue** (`EffectVmEmitQueueEnqueue`) | **A−/C** | `queueEnqueueDescriptor_full_sound:281` + `queueEnqueueDescriptor_commit_binds_state:319` + `unify_enqueue_debit` | The queue side-table root rides `fields[4]` (in-commitment), advance bound `fields[4]_after = newRoot`, anti-ghosted. The deposit DEBIT unifies with universe-A. **The gap (⇒ not full A):** `gQueueRootBind:87` pins `fields[4]_after = newRoot` where `newRoot` is an **opaque parameter** — the circuit does NOT recompute `newRoot = hash(oldRoot, msg)` in-row, so FIFO *order is bound* but *root correctness is asserted, not proven*. |
| 6 | **queueDequeue** (`EffectVmEmitQueueDequeue`) | **C** | `queueDequeueDescriptor_full_sound:271` | As enqueue: frame + queue-root-column bound, but the dequeued-element correctness + root recomputation is opaque-parameter. |
| 7 | **queueEnqueue→AtomicTx** (`EffectVmEmitQueueAtomicTx`) | **C** | `queueAtomicDescriptor_full_sound:299` | Frame + balance leg; atomic-tx multi-queue invariant + root recomputation out-of-row. |
| 8 | **queuePipelineStep** (`EffectVmEmitQueuePipelineStep`) | **C** | `queuePipelineDescriptor_full_sound:282` | Frame + root-column bound; pipeline-step correctness opaque. |
| 9 | **queueResize** (`EffectVmEmitQueueResize`) | **C** | `queueResizeDescriptor_full_sound:292` | Frame + root-column; resize correctness opaque-parameter. |
| 10 | **queueAllocate** (`EffectVmEmitQueueAllocate`) | **C** | `queueAllocateDescriptor_full_sound:328` | Frame + root-column; allocation correctness opaque. |
| 11 | **pipelinedSend** (`EffectVmEmitPipelinedSend`) | **C** | `pipelinedSendDescriptor_full_sound:242` + `unify_pipelinedSend_via_full_sound:328` | Frame freeze + balance leg unified to universe-A `*_full_sound`; the send-queue/message side-table is out-of-row. |
| 12 | **attenuate** (`EffectVmEmitAttenuateA`) | **C** | `attenuateDescriptor_full_sound:320` (`CapCellSpec`: `cap_root=cap_digest_new`, frame frozen) + `attenuateDescriptor_commit_binds_state:348` + `unify_attenuate_via_full_sound:401` | TEMPLATE. The `cap_root` *column* is moved + anti-ghosted + unified to `AttenuateSpec`. **The gap:** `cap_digest_new` is the opaque digest `D k.caps` — the descriptor does NOT recompute the attenuated cap-table membership in-row (`D` enters only as `Function.Injective D`). The actual cap-graph attenuation is a digest assertion, not an in-circuit membership proof ⇒ C, not A. |
| 13 | **delegate** (`EffectVmEmitDelegate`) | **C** | `delegateDescriptor_full_sound:110` + `unify_delegate_via_full_sound:143` | Same as attenuate: `cap_root` column move bound; cap-table digest opaque (`Injective D`). |
| 14 | **delegateAtten** (`EffectVmEmitDelegateAtten`) | **C** | `delegateAttenDescriptor_full_sound:100` + `unify_delegateAtten_via_full_sound:131` | Same as delegate. |
| 15 | **revokeDelegation** (`EffectVmEmitRevokeDelegation`) | **C** | `revokeDescriptor_full_sound:242` + `unify_revoke_via_full_sound:332` | `cap_root` column move bound; the revoked-edge set membership is the digest, opaque. |
| 16 | **refreshDelegation** (`EffectVmEmitRefreshDelegation`) | **C** | `refreshDescriptor_full_sound:275` + `unify_refresh_via_full_sound:367` | `cap_root` column move bound; cap-table digest opaque. |
| 17 | **introduce** (`EffectVmEmitIntroduce`) | **C** | `introduceDescriptor_full_sound:241` + `unify_introduce_via_full_sound:327` | `cap_root` column move bound; cap-table digest opaque (`Injective D`). |
| 18 | **dropRef** (`EffectVmEmitDropRef`) | **C** | `dropRefDescriptor_full_sound:290` + `unify_dropRef_via_exec:349` (→ executor) | `cap_root` column + frame; the ref/cap-table set-delete is the digest, opaque. Executor-unified leg is balance/cap-root only. |
| 19 | **exercise** (`EffectVmEmitExercise`) | **C** | `exerciseDescriptor_full_sound:241` + `unify_exercise_via_exec:334` | Near-noop: only `bal_lo` FREEZE + `cap_root` freeze unified to executor (`descriptor_agrees_with_executor_exercise` pins only `post.balLo`). The exercised-cell-program invocation effect is entirely out-of-row. |
| 20 | **spawn** (`EffectVmEmitSpawn`) | **C** | `spawnDescriptor_full_sound:276` + `unify_spawn_via_exec:353` | `cap_root` column for the new cell bound; the new-cell *birth* into the cell-table (membership insert) is out-of-row. |
| 21 | **createCell** (`EffectVmEmitCreateCell`) | **C** | `createCellVm_faithful:135` + `createCellVm_commit_binds_block:195` + `createCell_row_matches_executor:249` + **`createCell_offrow_unenforced:290`** | "Born empty" cell IS bound (all-zero after-block, anti-ghosted) + matches executor on the zero-block. **But `createCell_offrow_unenforced` PROVES the cell-table INSERTION (the actual creation) is NOT a descriptor column.** No `*_full_sound`, no `unify_*_exec`. |
| 22 | **createCellFromFactory** (`EffectVmEmitCreateCellFromFactory`) | **C** | `…Descriptor_full_sound` | As createCell + factory-template binding out-of-row. No executor connector. |
| 23 | **makeSovereign** (`EffectVmEmitMakeSovereign`) | **C** | `…Descriptor_full_sound` | Frame leg bound; the sovereignty flag / sovereign-commitment side-table (`sovereigncommitment.lean`) out-of-row. No executor connector. |
| 24 | **cellSeal** (`EffectVmEmitCellSeal`) | **C** | `cellSealDescriptor_full_sound:256` | Frame leg + commit; the seal state-transition side-table out-of-row (system_roots `cellCommitS`-bound but not descriptor-bound). |
| 25 | **cellDestroy** (`EffectVmEmitCellDestroy`) | **C** | `cellDestroyDescriptor_full_sound:240` | Frame leg; the cell-table DELETE (membership removal — the actual effect) out-of-row. |
| 26 | **setPermissions** (`EffectVmEmitSetPermissions`) | **C** | `setPermsDescriptor_full_sound:232` | Frame + nonce tick bound. **The permissions slot write LIVES OFF-TRACE** (header L11: rides `params[0]` + `compute_effects_hash`; "the AIR carries NO field column for the permissions"). The effect itself is unbound. |
| 27 | **setVK** (`EffectVmEmitSetVK`) | **C** | `setVKDescriptor_full_sound:233` | As setPermissions: the verification-key write rides `params`/`effects_hash`, not a bound column. |
| 28 | **emitEvent** (`EffectVmEmitEmitEvent`) | **C** | `emitEventDescriptor_full_sound:193` + `unify_emitEvent_exec:263` | Frame freeze bound + executor-unified on the freeze; the event topic/data ride `params`, the event-log append is out-of-row. |
| 29 | **receiptArchive** (`EffectVmEmitReceiptArchive`) | **C** | `archiveDescriptor_full_sound:320` + `unify_archive_via_exec:381` | Frame freeze; the receipt-archive side-table append out-of-row. |
| 30 | **refusal** (`EffectVmEmitRefusal`) | **C** | `refusalDescriptor_full_sound:241` | Frame freeze + nonce; a refusal records a refusal-log entry (out-of-row). Near-noop on state-block. |
| 31 | **validateHandoff** (`EffectVmEmitValidateHandoff`) | **C** | `handoffDescriptor_full_sound:293` + `unify_handoff_via_exec:357` | Frame freeze + executor-unified on freeze; the swiss-handoff validation/sturdyref check out-of-row. |
| 32 | **recordRoot** (`EffectVmEmitRecordRoot`) | **C/D** | (no `*_full_sound`; tamper lemmas only) | Records a system root; the descriptor has anti-ghost tamper lemmas but no `*_full_sound` full-semantics theorem and no executor connector. Records-a-root semantics largely unbound at descriptor level. |
| 33 | **noteCreate** (`EffectVmEmitNoteCreate`) | **C** | `noteCreateDescriptor_full_sound:281` + **`note_insert_is_out_of_row:428`** + `note_append_only_is_out_of_row:438` | Frame freeze + state-block commit bound. **The note-commitment SET INSERT (the actual effect) is PROVEN out-of-row** (`note_insert_is_out_of_row`). No commitment-tree membership column. |
| 34 | **noteSpend** (`EffectVmEmitNoteSpend`) | **C** | `noteSpendDescriptor_full_sound:283` + `noteSpend_nullifier_insert_is_out_of_row:…` + `noteSpend_no_double_spend_is_turn_property:…` + `noteSpend_proof_gate_is_out_of_row:…` | Frame freeze + state-block commit bound. **Every real leg is PROVEN out-of-row:** nullifier-set insert, no-double-spend (NON-membership), and the §8 spending-proof gate. Plus a `runtime_credit_vs_univA_neutral_divergence` (the two specs agree only at `value=0`). This is the textbook "conservation ≠ correctness" case. |
| 35 | **noteSpendCompose** (`EffectVmEmitNoteSpendCompose`) | **D** | (no `*_full_sound`; composition glue) | Composition wrapper over noteSpend; inherits noteSpend's C-gaps with no added full-semantics theorem. |
| 36 | **seal** (`EffectVmEmitSeal`) | **C** | `sealDescriptor_full_sound:275` | Frame freeze + commit; the seal-box side-table write out-of-row (system_roots `cellCommitS`-bound, not descriptor-bound). |
| 37 | **unseal** (`EffectVmEmitUnseal`) | **C** | `unsealDescriptor_full_sound:271` | As seal: the unseal side-table read/clear out-of-row. |
| 38 | **createSealPair** (`EffectVmEmitCreateSealPair`) | **C** | `createSealPairDescriptor_full_sound:246` | Frame freeze + commit; seal-pair creation side-table out-of-row. |
| 39 | **createEscrow** (`EffectVmEmitCreateEscrow`) | **A** | `createEscrowGenuine_sound:§H` (`CellCreateSpec ∧ genuine-root-recompute ∧ commit`) + `createEscrowGenuine_binds_record:§H` + `createEscrowGenuine_amount_bound:§H` + `unify_create_debit:351` (→ `execFullA`) | **CLASS-A PROMOTED.** The opaque additive step is GONE: `createEscrowVmDescriptorGenuine` recomputes the escrow-list-digest advance IN-ROW via two hash-sites (`EffectVmEmitEscrowRoot.escrowRecomputeSites`): `record_leaf = hash[id,creator,recipient,amount,asset,resolved]` (amount = the SAME `param.AMOUNT` driving the debit) then `new_root = hash[record_leaf, old_root]` — a prepend-accumulator advance, FORCED not asserted. `createEscrowGenuine_binds_record` anti-ghosts ALL of {old root, id, creator, recipient, amount, asset, resolved}: tampering any parked-record field MOVES the new root ⇒ moves the absorbed `state_commit` ⇒ UNSAT. The balance debit + frame freeze (§7 `CellCreateSpec`) is unify'd to `execFullA`. Residual (NOT a soundness gap): the new-root carrier is `aux 96`; the deployed hand-AIR's absorption of it at commitment slot 4 is the Rust-side widening (task #91), out of this file's scope — the Lean side is now FULL class-A. |
| 40 | **createCommittedEscrow** (`EffectVmEmitCreateCommittedEscrow`) | **A** | `escrowCreateGenuine_sound:§H` + `escrowCreateGenuine_binds_record:§H` | **CLASS-A PROMOTED.** Same genuine in-row recompute as createEscrow (`escrowCreateVmDescriptorGenuine` uses `EffectVmEmitEscrowRoot.escrowRecomputeSites`): the committed-escrow record's leaf + the prepend advance are FORCED, the committed amount IS the debited amount, anti-ghosted by the commitment. Debit + frame = `CellEscrowSpec`. Residual = the deployment widening only (task #91). |
| 41 | **releaseEscrow** (`EffectVmEmitReleaseEscrow`) | **A** | `releaseEscrowGenuine_sound:§H` + `releaseEscrowGenuine_binds_record:§H` + `unify_release_credit` (→ `execFullA`) | **CLASS-A PROMOTED.** Genuine in-row recompute (`releaseEscrowVmDescriptorGenuine`): the released record's leaf (resolved=1) + the prepend advance FORCED; the released amount IS the recipient-credited amount, bound by the commitment. Credit + frame = `CellReleaseSpec`. Residual = deployment widening only (task #91). |
| 42 | **refundEscrow** (`EffectVmEmitRefundEscrow`) | **A** | `refundEscrowGenuine_sound:§H` + `refundEscrowGenuine_binds_record:§H` + `unify_refund_credit:351` (→ `execFullA`) | **CLASS-A PROMOTED.** Genuine in-row recompute (`refundEscrowVmDescriptorGenuine`): the resolved record's leaf (resolved=1) + the prepend advance FORCED; the refunded amount IS the creator-credited amount, bound by the commitment. Credit + frame = `CellRefundSpec`. Residual = deployment widening only (task #91). |
| 43 | **bridgeLock** (`EffectVmEmitBridgeLockA`) | **A** | `bridgeLockGenuine_sound:§H` + `bridgeLockGenuine_binds_record:§H` + `unify_lock_debit` (→ `execFullA`) | **CLASS-A PROMOTED.** `bridgeLockVmDescriptorGenuine` binds the bridge escrow root GENUINELY in-row via `EffectVmEmitEscrowRoot.escrowRecomputeSites` (the prior `escrow_root_not_in_descriptor_commit` C-gap is CLOSED by the new descriptor): the locked record's leaf + the prepend advance are FORCED, the locked amount IS the debited amount. Debit + nonce tick + frame = `CellLockSpec`. Residual = deployment widening only (task #91). |
| 44 | **bridgeMint** (`EffectVmEmitBridgeMint`) | **A** | `bridgeMintDescriptor_classA:§8½` (`CellBridgeMintSpec` + commit + executor agreement) = `bridgeMintDescriptor_full_sound:242` + `bridgeMintDescriptor_commit_binds_state:271` + `unify_bridgeMint_exec:319` (→ `execFullA`) | **CLASS-A PROMOTED (per-cell, the transfer bar).** The `bal_lo` credit IS bound (13 cols) + anti-ghosted + unified to `execFullA … (.bridgeMintA …)`. The inbound-bridge CryptoPortal proof is ENFORCED by `execFullA`'s admission (the `= some s'` hypothesis carries it), not re-derived in-circuit — cited, the same boundary mint has. |
| 45 | **bridgeFinalize** (`EffectVmEmitBridgeFinalize`) | **A** | `bridgeFinalizeGenuine_sound:§H` + `bridgeFinalizeGenuine_binds_record:§H` | **CLASS-A PROMOTED.** Genuine in-row recompute (`bridgeFinalizeVmDescriptorGenuine`): the finalized record's leaf (resolved=1) + the prepend advance FORCED; the finalized amount bound by the recomputed root. Frame freeze + nonce tick = `CellFinalizeSpec`. Residual = deployment widening only (task #91). |
| 46 | **bridgeCancel** (`EffectVmEmitBridgeCancel`) | **A** | `bridgeCancelGenuine_sound:§H` + `bridgeCancelGenuine_binds_record:§H` | **CLASS-A PROMOTED.** Genuine in-row recompute (`bridgeCancelVmDescriptorGenuine`): the cancelled record's leaf (resolved=1) + the prepend advance FORCED; the cancelled amount bound by the recomputed root. Frame freeze + nonce tick = `CellCancelSpec`. Residual = deployment widening only (task #91). |
| 47 | **enliven (swiss)** (`EffectVmEmitEnliven`) | **C** | `enlivenDescriptor_full_sound:385` + `unify_enliven_via_full_sound:456` | Frame leg + universe-A unify; the sturdyref/swiss side-table (`sturdyref_root`) out of descriptor commit. |
| 48 | **swissDrop** (`EffectVmEmitSwissDrop`) | **C** | `swissDropDescriptor_full_sound:343` + `unify_swissDrop_via_full_sound:404` | Frame leg + unify; swiss sturdyref side-table out of descriptor commit. |
| 49 | **swissExport** (`EffectVmEmitSwissExport`) | **C** | `swissExportDescriptor_full_sound:348` + `unify_swissExport_via_full_sound:417` | As swissDrop. |
| 50 | **swissHandoff** (`EffectVmEmitSwissHandoff`) | **C** | `swissHandoffDescriptor_full_sound:341` + `unify_swissHandoff_via_full_sound:402` | As swissDrop. |

### Effects present as Inst/Spec/Witness but with NO dedicated Emit `_full_sound` (lower coverage)

| # | Effect | Class | Note |
|---|--------|:-----:|------|
| 51 | **setField** (the kernel `setFieldA` write) | **C** | Folded into the generic state-block freeze/move machinery (Transfer/`SetFieldCommit`); a field write IS an in-commitment column move, but there is no dedicated `setFieldDescriptor_full_sound` welding the *which-field-and-by-how-much* per-field spec to `recKExec`. Bound at the column level, unverified at the per-effect-semantics level. |
| 52 | **grantCap** (kernel `grantCapability`) | **C** | Realized via the cap-family descriptors (delegate/attenuate); the cap-table grant is the opaque-digest leg (class-C cap pattern). |
| 53 | **revokeCap** (kernel `revokeCapability`) | **C** | As grantCap; revoke is the opaque-digest leg. |
| 54 | **balanceA** (`Inst/balanceA`, `Spec/balancemovement`) | **A** | This is the universe-A two-cell balance-movement spec that Transfer's keystone PROJECTS from (`BalanceMovementSpec`, all 17 `RecordKernelState` fields). Genuinely full-state at universe-A; its circuit realization IS the transfer keystone (#1). Counted A by inheritance from #1. |

> Note on "~56": the runnable surface is the **54 `EffectVmEmit*` descriptor modules** above; the
> kernel `CellEffect` constructors (`setField, transfer, mint, burn, grantCap, revokeCap, emitEvent,
> incrementNonce, createCell, …`) map onto them many-to-one. Rows 51–54 reconcile the count and the
> two universe-A specs (`balanceA`, the cap specs) that have no standalone Emit module.

---

## SUMMARY COUNT (ruthless)

### THE HONEST FRACTION (the number ember asked for)

> **1 / 56** effects has a genuine **from-scratch full-semantics circuit proof connected to the verified
> executor** — i.e. `satisfiedVm <descriptor> ⟹ FULL per-cell post-state (every touched field
> moved-or-frozen) + anti-ghost commitment on ALL of it + unification to `recKExec``. That effect is
> **transfer** (`transferDescriptor_full_sound` + `transferDescriptor_commit_binds_state` +
> `tampered_rejected` + `unify_debit_exec`/`unify_credit_exec`). Its universe-A source `balanceA` is the
> same proof viewed at universe A, so counting it as a second genuine full-state row gives **2 / 56** at
> most — but it is NOT a distinct circuit. **The honest, conservative number is ONE genuinely-verified
> effect circuit.**
>
> This fraction deliberately does **NOT** count: (a) the 4 **A−** effects (mint/burn/incrementNonce/
> queueEnqueue) — each binds+anti-ghosts its moved column and unifies to the executor, but each has ONE
> named residual (opaque supply total / no nonce-tick executor effect / opaque queue-root recompute) and
> so is *one identifiable step* from A, not at A; (b) **differential agreement** (`descriptor == hand-AIR`)
> — that is a cross-check, present as an *additional* tooth on some effects, never as a substitute for a
> from-scratch proof (class B is therefore empty); (c) the **economic / frozen-frame leg** — binding the
> conserved balance + frozen frame is conservation, and *conservation is NOT correctness*: it does not
> bind the cap-table mutation / nullifier insert / note insert / escrow resolve / seal write / etc. that
> IS the effect. So "X/56 = 1" is the truth about how verified the circuit ACTUALLY is, effect by effect.

| Class | Count | Effects |
|-------|------:|---------|
| **(A) genuinely full-state verified** | **2** | transfer (#1), balanceA (#54, = transfer's universe-A source) |
| **(A−) one-leg-from-A** (moved field IS in-commitment + anti-ghost + executor-unified, but a real residual: opaque side-table total, or opaque root-recompute, or no executor connector) | **4** | mint (#2), burn (#3), incrementNonce (#4), queueEnqueue (#5) |
| **(B) differential-only** | **0** | — (all effects have a from-scratch `*_full_sound`; differential is an *additional* cross-check, never the sole assurance) |
| **(C) economic/frame-leg-only** (the field/side-table that IS the effect is NOT bound by the descriptor's own commitment) | **~46** | all of #6–#53 except the A−'s above |
| **(D) unverified** | **2** | noteSpendCompose (#35), recordRoot (#32, borderline C/D) |

**Honest headline:** exactly **ONE effect (transfer)** meets the full class-A bar from scratch end-to-end
(full per-cell post-state + anti-ghost on all of it + `recKExec` unification). Four more (mint, burn,
incrementNonce, queueEnqueue) are *one identifiable residual* away. **Every other effect's circuit binds
only the frozen frame plus possibly an economic (balance/nonce) leg — the cap-table mutation / nullifier
insert / note-commitment insert / escrow resolve / queue-root recompute / seal write / permissions-slot
write / VK write / event-log append / cell-table insert-or-delete that IS THE EFFECT is NOT bound by the
deployed descriptor's `state_commit`.** The per-effect files are *commendably honest* about this — they
PROVE the gap as `*_out_of_row` / `*_root_not_in_descriptor_commit` / `*_is_turn_property` theorems
rather than papering it. That honesty is exactly why this ledger can be precise; it does not make the
circuit more verified than it is.

---

## GAP LIST — every effect not in class A, ordered by effort (lowest first)

The ordering reflects how close each is to genuine class A, given the existing machinery.

### Tier 0 — finish the A− four (one residual each)

1. **incrementNonce (#4)** — add a `unify_incNonce_*` connector. Universe-A has no nonce-tick effect,
   so the honest fix is to ADD a `recKIncNonce` effect to `recKExec` and unify (the runtime nonce
   counter is real; give it a verified-executor home). Smallest gap: the field is already bound+anti-ghosted.
2. **mint (#2) / burn (#3)** — add the supply-total side-table to an in-commitment column (or accept
   that per-cell credit/debit is the whole effect and PROMOTE to A with a one-line note). The credit/debit
   already binds + anti-ghosts + unifies to the executor; only the global-supply invariant is unmodeled.
3. **queueEnqueue (#5) / the queue family (#6–#10)** — replace the opaque `newRoot` parameter in
   `gQueueRootBind` with an in-row recomputation `newRoot = hash_2_to_1(oldRoot, message_hash)` and bind
   `message_hash` to the enqueued payload. The root *column* is already in-commitment (`fields[4]`); this
   closes "order bound but root-correctness asserted." Promotes the whole queue family from C toward A.

### Tier 1 — the cap-graph family (opaque-digest → in-circuit membership)

4. **attenuate (#12), delegate (#13), delegateAtten (#14), revokeDelegation (#15),
   refreshDelegation (#16), introduce (#17), dropRef (#18), grantCap (#52), revokeCap (#53)** —
   all share ONE gap: the cap-table mutation enters only as the opaque digest `D : Caps → ℤ` with
   `Function.Injective D`. To reach A, the descriptor must RECOMPUTE the attenuated/derived cap-table
   membership in-row (a Merkle/sorted-set update gate) so that `cap_digest_new` is *forced* to be the
   genuine image, not an asserted parameter. Single shared IR extension (a cap-table update gate-kind)
   unlocks all nine. Highest leverage in the ledger.

### Tier 2 — the side-table-into-commitment families

5. **escrow (#39–#42), bridge-escrow (#43,#45,#46), seal (#24,#36–#38),
   swiss/sturdyref (#31,#47–#50), receiptArchive (#29), emitEvent (#28), refusal (#30)** — this is the
   **"amplified-not-deployed"** cohort and it is the SINGLE highest-value structural fix. The Lean side is
   ALREADY full+proved: `createEscrowFull_sound:644` genuinely gives `satisfiedVm <amplified> ⟹
   CellCreateSpec ∧ CreateEscrowRootIntent ∧ commit`, and `createEscrowFull_binds_escrow_root:631` /
   `escrow_root_bound_by_systemCommit` / `systemRootsDigest_binds_pointwise` genuinely anti-ghost the
   side-table root. **The gap is purely deployment:** the root carrier is `SYS_DIG_AFTER = aux 96 =
   SYSTEM_ROOTS_DIGEST`, and `auxCol SYSTEM_ROOTS_DIGEST = 186 ≥ EFFECT_VM_WIDTH = 186` — so the deployed
   hand-AIR carries no such column and currently absorbs `BabyBear::ZERO` at commitment slot 4
   (`cell_state.rs::compute_commitment`). The per-effect files PROVE the gap
   (`escrow_root_not_in_descriptor_commit`). **To reach A:** (i) widen `EFFECT_VM_WIDTH` so the deployed
   row carries the `system_roots` digest column; (ii) have the hand-AIR absorb it at commitment slot 4
   (the one Rust-side step §E names); (iii) **replace the additive opaque root-STEP** (`SYS_DIG_AFTER =
   SYS_DIG_BEFORE + step_param`, `gEscrowRootUpdate:544`) with an in-row recomputation of the genuine
   escrow-list digest so the new root is FORCED, not asserted. Steps (i)+(ii) are the deployment graduation
   (tracked as task #91 "MID-4 widening"); step (iii) is the real soundness deepening.
6. **queue (#6–#10)** — already AHEAD of the escrow cohort: its root rides `fields[4]` (in-commitment,
   deployed), so it only needs the opaque-newRoot → in-row-recompute fix (Tier 0 item 3). Listed here too
   for completeness.

### Tier 3 — the privacy / membership families (need NEW IR)

7. **noteCreate (#33)** — bind the note-commitment SET INSERT: needs a commitment-tree membership/append
   gate-kind the hash-site IR lacks. The frame is bound; the insert is proven out-of-row.
8. **noteSpend (#34), noteSpendCompose (#35)** — the hardest. Needs THREE new things the per-row hash-site
   IR cannot express: (a) nullifier-set INSERT bound to commitment; (b) **no-double-spend = sorted-set /
   Merkle NON-membership** gate (`noteSpend_no_double_spend_is_turn_property` names the exact boundary);
   (c) the §8 spending-proof verification gate. Also resolve the runtime-credit vs universe-A-neutral
   balance-convention divergence (decide which is canonical). This is the genuine crown-jewel hard core.

### Tier 4 — the write-rides-params effects

9. **setPermissions (#26), setVK (#27), setField (#51)** — the actual written value rides `params[0]` +
   `compute_effects_hash`, with NO bound `field` column for the written slot. To reach A: add the written
   slot as an in-commitment state-block column and constrain `field[slot]_after = written_value`. Smaller
   than Tier 3 but requires layout work + a per-field spec welded to `recKExec`.

10. **createCell (#21), createCellFromFactory (#22), spawn (#20), cellDestroy (#25),
   makeSovereign (#23), recordRoot (#32)** — cell-TABLE membership insert/delete + sovereignty/root
   flags. Needs the same cell-table membership gate as the cap family (Tier 1) applied to the cell-set.

11. **exercise (#19), validateHandoff (#31), pipelinedSend (#11)** — near-noop or routing effects whose
    real content (cell-program invocation, handoff validation, message routing) is structurally off the
    per-row state-block. Lowest priority: clarify whether these belong in the per-row AIR at all, or are
    inherently turn/accumulator-level.

---

## Methodological honesty notes

- **Differential agreement (descriptor == hand-AIR) is NOT in this ledger as assurance.** Where it exists
  (the cutover harness, `descriptor_agrees_with_executor*`) it is an *additional* cross-check on top of a
  from-scratch `*_full_sound`. No effect here rests on differential alone, so class B is empty — but that
  is a statement about *method*, not about *coverage*: most effects are class C because their real semantic
  content is unbound, NOT because they only have differential.
- **Hand-AIRs (`circuit/src/effect_vm/*.rs`) STAY** as diversity. Not touched, not deleted.
- The anti-ghost `*_commit_binds_state` / `tampered_rejected` theorems are real and load-bearing for the
  13 absorbed columns — but they bind those 13 columns ONLY. An effect is class A only if the field that
  IS the effect lives among those 13 (transfer/mint/burn/nonce/queue-root) AND its move is genuinely
  computed, not parameter-asserted (transfer alone fully clears this).
- `#assert_axioms` clean across the keystone + representatives (verified via `#print axioms`:
  `transferDescriptor_full_sound`, `transferDescriptor_commit_binds_state`, `unify_debit_exec`,
  `noteSpendDescriptor_full_sound`, `noteSpend_no_double_spend_is_turn_property`,
  `queueEnqueueDescriptor_full_sound` all depend only on `{propext, Classical.choice, Quot.sound}`).
