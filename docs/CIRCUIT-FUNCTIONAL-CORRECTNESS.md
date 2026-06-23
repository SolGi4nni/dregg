# Circuit Functional Correctness — Light-Client Unfoolability

> The state of the circuit-soundness proof: what a light client that verifies only a rotated proof
> can conclude, what is PROVEN to force it, what is a NAMED commitment-bound residual, and what is an
> irreducible cryptographic floor. Present-tense and precise about proven-vs-residual-vs-floor; the
> per-effect obligation table at the end is the map.

## The property (the apex)

A light client verifies a rotated proof against the live VK and runs nothing else. Soundness:
`verifyBatch accept ⟹ ∃ a genuine kernel transition committing to the published (pre, post)`.

`Dregg2/Circuit/CircuitSoundness.lean` — `lightclient_unfoolable` proves exactly that from *only*
`(pi, π)` + named floors. It **derives** `∃ pre post` (no hypothesized decode): `StateDecode`
faithfulness is a theorem (`recStateCommit` injectivity pins each of `pre.kernel`/`post.kernel` as the
unique kernel committing to the published root), and the cross-step frame is *derived* from the
commitment binding (`stateDecodeChain_frame_continuous`). Axiom-clean.

The apex is **parametric in the per-effect kernel step relation `kstep`**, so the same theorem is
instantiated at the toy arm (`dispatchArm`) and the FAITHFUL arm (`dispatchArmFacet`). Its carried
obligations are exactly the cryptographic floors (named below); the circuit-forcing content is proven.

## Scope — single-transition soundness, NOT freshness

`lightclient_unfoolable` proves **SINGLE-TRANSITION soundness**: every accepted batch decodes to a
genuine kernel step committing to the published `(pre, post)`. It takes `pi.turn` as a **given**. It
proves NOTHING about whether the transition is **FRESH** (not already applied) or correctly **ordered**
across turns. A light client verifying `(pi, π)` learns "this is a REAL transition" — NOT "this is a
fresh, unreplayed transition".

Cross-turn FRESHNESS / NO-REPLAY / ordering is **not part of the apex**. It rests on the DEPLOYED
machinery, which the apex does not model:

- the **commitment-chain CAS** (`proof_verify.rs`): the live stored commitment must equal the proof's
  pre-anchor; applying the proof advances the live commitment to the post-anchor;
- **cell-nonce monotonicity** (`cell_state.rs` "Monotonic"): the agent nonce is bound into
  `recStateCommit` (it lives in the agent cell's leaf hash) and strictly increases each turn, so the
  committed state never cycles — a consumed `pre` never recurs.

A light client that wants freshness **must additionally track the live stored commitment** (the CAS)
and reject any proof whose pre-anchor ≠ the live commitment. The proof alone does not establish
freshness; "a light client that runs nothing cannot be fooled" covers the **authenticity** of a single
transition, not replay.

The cross-turn close is proven separately in `Dregg2/Circuit/CrossTurnFreshness.lean` (axiom-clean):
the genuinely-hard fact — **the commitment cannot hide a stale nonce** (`commit_inj_nonce`, from the CR
set via `CommitSurface.commit_binds`) — drives `commit_no_repeat` (the live-commitment sequence never
repeats under a strictly-monotone agent nonce) and hence `no_replay` (a fixed pre-anchor opens the CAS
gate **at most once**) + `replay_rejected_after_apply` (every later turn rejects the same proof). The
monotone-nonce hypothesis is grounded by `prologue_strictly_increases_nonce` (the deployed
never-rolled-back fee/nonce prologue, `Admission.commitPrologue_nonce`). The named **residual** (neither
an axiom nor a hole) is the mechanical composition that wires the full `Admission.runTurn`-driven
accepted sequence into a monotone `TurnChain` (over the already-proved `recKExec_preserves_AccountsWF`
and `admissible_links_to_head`) and proves the agent nonce strictly increases across the whole
prologue+body. The replay defense is **modeled and proven at its core**, and the residual to the
deployed CAS is named, not laundered.

## The four proven legs

The soundness case rests on four things that are PROVEN in Lean (axiom-clean, pinned in
`Dregg2/Claims.lean` and assembled by guarantee in `Dregg2/AssuranceCase.lean`), and bottoms out only
on the named cryptographic floor.

### 1. The commitment binds every kernel write

A light client's `pi.post` binds the per-cell **state commitment**, whose preimage is
(`circuit/src/effect_vm/cell_state.rs`, `compute_commitment` / `compute_commitment_8`):

```
hash( balance_lo, balance_hi, nonce, field[0..7], capability_root, record_digest )
```

a `hash_4_to_1` tree over four intermediates, the LAST of which absorbs the **`record_digest`** — a
single Poseidon2 felt that folds ALL authority-bearing cell state the other limbs do not carry:
`permissions`, `verification_key`, `lifecycle`, `deathCert`, `delegate`, `delegation`, `program`,
`mode`, the field-visibility / sealed-mask, the side-table roots (`system_roots_digest`, `fields_root`,
swiss/refcount roots), and `fields[8..]`. The digest is computed cell-locally by
`dregg_cell::compute_authority_digest_felt` (`cell/src/commitment.rs`).

So the deployed commitment binds the FULL kernel: two states differing in ANY kernel field commit
differently. Mutation-confirm (green tests, `cell/src/effect_vm/cell_state.rs`):

- `record_digest_binds_commitment_p0_2` — two cells differing ONLY in their authority residue commit
  DIFFERENTLY (the lossy form was indistinguishable; the `record_digest` limb closes it).
- `empty_record_digest_is_legacy_noop` — a residue-free cell (`empty_record_digest()` = ZERO)
  reproduces the legacy commitment byte-identically, so the cutover is a no-op for cells with no
  authority residue (no flag-day).

The 8-felt PI form (`compute_commitment_8`) squeezes the same four intermediates + `record_digest` to
~124-bit collision resistance, matching the FRI floor.

This realizes the Lean apex's commitment `recStateCommit k t = cmb(cellDigest …, RH k)`
(`StateCommit.lean`), where `RH` is injective on the **whole kernel** (`RestHashIffFrame` binds
`accounts`, `caps`, `bal`, `nullifiers`, `revoked`, `commitments`, `slotCaveats`, `factories`,
`lifecycle`, `deathCert`, `delegate`, `delegations`, `delegationEpoch(At)`, `heaps`). That is what
makes `StateDecode` faithfulness (`stateDecode_post_faithful`) hold: equal commitment ⇒ equal *full*
kernel. The concrete `CommitSurface` instance `S_live` (`ClosureSurface.lean`) has
`.commit = recStateCommit` with `.commit_binds = recStateCommit_binds_kernel` proven from the standard
Poseidon CR carriers — no narrower wire commitment, no new axiom.

### 2. Hostile-witness extraction is closed for all 32 live effects

`Dregg2/Circuit/CircuitOpenFronts.lean` — `countOpenFronts = 0`. Every live effect has an `*_extract`
theorem proving that ANY public-input-bound satisfying witness — an ARBITRARY satisfying trace, pinned
ONLY by the verifier's PI check on the gate-relevant digest wires + the guard region, with NO dead
whole-trace `hEnc` hypothesis — FORCES the genuine kernel step; a forged or hostile witness is refuted
by the anti-ghost `*_extract_rejects_*` teeth. All 32 are `#assert_axioms`-clean, instantiated across
the component frameworks:

- v2 single (17): `mint`, `transfer`, `balanceA`, `burn`, `attenuate`, `delegate`, `delegateAtten`,
  `introduce`, `revoke`, `revokeDelegation`, `noteCreate`, `noteSpend`, `bridgeMint`, `cellSeal`,
  `cellUnseal`, `refreshDelegation`, `receiptArchiveLifecycle` (`WitnessExtractPerEffect`).
- v1 single (9): `setPermissions`, `setVK`, `setProgram`, `incrementNonce`, `emitEvent`,
  `makeSovereign`, `refusal`, `receiptArchive`, `pipelinedSend` (`WitnessExtractV1PerEffect`).
- dual (2): `cellDestroy`, `heapWrite` (`WitnessExtractDual`).
- triple (1): `createCellA` (`WitnessExtract3`, over accounts + bal + born-empty-side).
- quint (2): `spawnA`, `createCellFromFactoryA` (`WitnessExtract5`, over the 5 components).
- composite (1): `exerciseA` (`WitnessExtractComposite`) — BOTH legs forced from circuit evidence: the
  hold-gate leg is hostilely extracted (an arbitrary PI-bound satisfying hold witness forces
  `ExerciseHoldSpec`/`exerciseGuard`), AND the inner fold is forced from the inner emitted circuit witness
  (`exerciseA_extract` threads an `exerciseInnerTurnWitness` — a `TurnEmittedChain` over the inner forest —
  through `exercise_inner_emitted_refines_turnSpec` ∘ the per-step extractor; not a carried bridge).

There is no remaining gap in the per-effect adversarial-extraction lane: 32 closed / 0 open.

### 3. The executor genuinely enforces (the triangles)

The verified executor (`execFullA` / `execFullForestG`, the body behind the
`dregg_exec_full_forest_auth` FFI) genuinely enforces the security-critical moves — a deep sweep across
all live effects confirms the five weakness classes are clean:

- **Revocation executes the epoch step.** `recKRevokeDelegationFull` runs both legs of the revoke:
  it bumps the parent's `delegationEpoch` (`recKRevokeDelegationFull_bumps_parent_epoch`) and resets the
  child's `delegationEpochAt` to 0 (`recKRevokeDelegationFull_stales_child`), so child snapshots are
  staled, not merely the cap edge removed.
- **Attenuation fails closed out-of-bounds.** `execFullA_attenuateA_outOfBounds_none`: an attenuate
  whose target slot is not a held cap returns `none`. Non-amplification holds on the success arm
  (`execFullA_attenuateA_non_amplifying`).
- **Spawn / refresh stamp `delegationEpochAt`.** The executor stamps the child's epoch at birth /
  re-stamps it at refresh (`spawnEpochAtMap` / `refreshEpochAtMap`).
- **Node caps genuinely attenuate.** The two deployed authority surfaces (ownership and the held
  `Cap.node`/`endpoint` caps) are reconciled by the faithful `authorizedFacetB` gate
  (`Dregg2/Exec/FacetAuthority.lean`, tier × facet, byte-faithful to `cell/src/permissions.rs` +
  `cell/src/facet.rs`); a cap demanding a facet the held cap lacks is rejected.
- **Destroyed-is-terminal.** `mint`/`burn`/`send`/`emitEvent`/`makeSovereign` require `acceptsEffects`
  liveness (`lifecycle cell == lcLive`), not mere membership — a Sealed/Destroyed cell rejects effects
  (`makeSovereignSpec_rejects_destroyed`, the R6 liveness gate; the `acceptsEffects` gates in
  `HandlerExecutor`).

These are the cross-corner triangles: full-state executor spec ⟺ executor ⟺ circuit spec, with the
anti-vacuity teeth (the fail-closed pole bites).

### 4. The verifier anchors

For the effects whose write is forced into the published commitment, the deployed verifier
(`turn/src/executor/proof_verify.rs::verify_and_commit_proof_rotated`, step 6b) ANCHORS the published
PI rather than checking `published == published`: it clones the trusted before-cell, applies the kernel
effect through the SHARED `dregg_turn::rotation_witness::apply_effect_to_cell` weld (the same projection
the producer uses, so honest proofs are not rejected), and overrides the published limb to
`compute_authority_digest_felt(post_cell)` (record-digest class) / `lifecycle_felt_cell(post_cell)`
(lifecycle class). So the gate forces `pubPost = digest(stepped pre)`.

Anchored families (both-polarity tests green — honest accept BITES, forged-after rejected):

- The **record-digest anchor family** (8 effects): `setPermissions`, `setVK`, `refusal`,
  `cellSeal`, `cellUnseal`, `cellDestroy`, `receiptArchive`, `makeSovereign`. Test:
  `sdk/tests/sovereign_rotated_c1.rs` `record_pin_anchor`; Lean: `rotateV3WithRecordPin_rejects_wrong_post`.
  (For `setPermissions`/`setVK`/`refusal` and the lifecycle movers the anchor is now belt-and-suspenders:
  each carries an in-circuit force — the perms/VK weld, the `refusal` `fields_root` `.write` map-op, the
  disc + lifecycle-payload hash gates — so the move is light-client-forced without the off-cell anchor.)
- The **value-forced effects** (6): `transfer`, `burn`, `mint`, `bridgeMint`, `setField`,
  `incrementNonce` — the effect writes a directly-named bound column (`bal`/`field[slot]`/`nonce`).
  The transfer path is sound through the live sovereign verifier (PI↔STATE_COMMIT, tamper test green).
- The map-op effects (the note / capability / fields-root families) via their own in-circuit gates:
  `noteSpend`'s double-spend non-membership is FORCED in-circuit (`SortedTreeNonMembership.lean`), the
  capability family's exact key-set move is forced (`CapTreeUpdate.lean`; `attenuate` is set-exact, not
  non-amp-only — the ARGUS non-amplification crown, #103), and `refusal`'s audit write is forced by a
  `.write` map-op on the openable `fields_root` (`EffectVmEmitRotationV3.refusalFieldsWriteV3`).

## The named residuals (the honest fine print)

For three epoch/snapshot moves, concordance is PROVEN — the commitment binds the field (it folds into
`record_digest`), the extractor forces the gate, and the executor performs the move — but the deployed
FROZEN v1-face descriptor does not yet WRITE-GATE-FORCE the move; it commitment-binds it via
`record_digest`. Each is carried as an explicit, data-bearing, fail-closed `Prop` (never an open hole,
never an axiom), conjoined onto the deployed step, and the faithful refinement is proven against it:

- **`RevokeDelegationEpochResidual`** (`Dregg2/Circuit/EffectRefinement.lean`) — the parent
  `delegationEpoch` bump + child `delegationEpochAt` reset; the cap-edge remove is decode-forced, the
  epoch step is the residual.
- **`SpawnEpochStampResidual`** (`EffectRefinement.lean`) — the child's birth epoch stamp. The
  cap/delegate/delegations HANDOFF is forced by the deployed quint (the close of the spawn
  cap-handoff residual, `CircuitSoundnessAssembled.lean`); only the `delegationEpochAt` stamp is the
  residual. `spawn_full_circuit_refines_spec` proves the deployed quint + residual ⟹ `SpawnFullSpec`.
- **`RefreshEpochStampResidual`** (`EffectRefinementBatch2.lean`) — the freshness-restore epoch stamp;
  the `delegations`-move key set is decode-forced, the stamp is the residual.

The closure shape for all three is the moving-face descriptor cutover (the v1-frozen `delegationEpochAt`
face becomes write-gate-forcing) — the §3.EPOCH lane. This is per-effect descriptor + verifier-anchor
engineering on a commitment that already binds the field; it is NOT a commitment change.

`emitEvent` and `makeSovereign` need NO separate residual: emitEvent leaves the entire kernel frame
unchanged (forced), and makeSovereign's mode transition + its lifecycle liveness gate are already in
the bound frame.

## The irreducible cryptographic floor (named, not assumed-away)

The apex bottoms out on exactly the floors every verified-SNARK soundness proof bottoms out on. These
are `Prop`-portals / typeclass parameters (never `axiom`), the cryptographer's domain, the standard
symbolic-model boundary:

- `StarkSound` / `StarkComplete` — the audited p3 batch-STARK FRI verifier soundness
  (`verify ⟹ ∃ Satisfied2 witness`); not provable in Lean.
- `Poseidon2SpongeCR` + the commitment-surface CR set + `logHashInjective` — the hash / commitment /
  log collision-resistance (`recStateCommit` injectivity binds the full kernel).
- `blake3-CR` (out-of-circuit content/transcript hash) and `ed25519` EUF-CMA (signatures).
- `WitnessDecodes` — the prover-witness decode interface (the prover's trace decodes to the per-effect
  encode columns); realizable, NOT the refinement obligation.

There is no opaque carried obligation: the circuit-forcing content (each descriptor forces its kernel
step, the double-spend non-membership, the capability non-amplification) is proven and load-bearing in
the apex.

## The obligation table — the real terrain (per live effect)

A read of every live rotated descriptor against its kernel leaf spec. The criterion is **whether the
descriptor forces the leaf-spec move into the published commitment** (`descriptorRefines`). The
commitment binds the FULL kernel for all of these (leg 1); the table records HOW each effect's specific
write is forced into it.

| class | effects | what it means |
|---|---|---|
| **VALUE_FORCED** (gate pins a directly-named bound column) | `transfer`, `burn`, `mint`, `bridgeMint`, `setField`, `incrementNonce` | the gate pins the moved column (`bal`/`field[slot]`/`nonce`) into the commitment; forgery teeth bite |
| **RECORD-DIGEST ANCHORED** (gate + verifier-anchor wired) | `setPermissions`, `setVK`, `cellSeal`, `cellUnseal`, `cellDestroy`, `receiptArchive`, `makeSovereign` | the write lands in the `record_digest`/lifecycle limb the commitment binds, the descriptor pins it, AND `proof_verify.rs` step 6b anchors the PI to `compute_authority_digest_felt`/`lifecycle_felt_cell(trusted post-cell)` — both-polarity tests green. (`setPermissions`/`setVK` are ALSO light-client-forced by their in-circuit perms/VK weld; `cellSeal`/`cellUnseal`/`cellDestroy`/`receiptArchive` by the in-circuit disc gate + lifecycle-payload hash gate — the anchor is then belt-and-suspenders) |
| **MAP-OP FORCED** (in-circuit sorted-set / cap-tree / fields-root gate) | `noteSpend`, `noteCreate`, the capability family (`attenuate`, `delegate`, `delegateAtten`, `introduce`, `grantCap`, `revokeCapability`), `spawn` (the cap handoff), `refusal` (the audit write) | the exact sorted-set / cap-tree / fields-root move is forced in-circuit (`SortedTreeNonMembership`/`CapTreeUpdate`); `noteSpend` double-spend non-membership FORCED (two map-ops, `.absent`+`.insert`); `attenuate` set-exact; `refusal` carries ONE `.write` map-op (guard `SEL_REFUSAL`, key `refusalAuditKeyFelt`) FORCING `after_fields_root == write(before_fields_root, REFUSAL_AUDIT_KEY → audit_felt(params))` on the openable limb-36 `fields_root` (`EffectVmEmitRotationV3.refusalFieldsWriteV3_forces_write`, deployed in both registry TSVs) — so refusal is light-client-forced, NOT anchor-only; its record-digest PI-46 pin is belt-and-suspenders |
| **COMMITMENT-BOUND RESIDUAL** (commitment binds the field; write-gate is the §3.EPOCH cutover) | `revokeDelegation` (epoch step), `spawn` (birth epoch stamp), `refreshDelegation` (freshness-restore stamp) | the field folds into `record_digest` (bound), the extractor forces the gate, the executor performs the move; the FROZEN v1 face does not yet write-gate-force the epoch stamp — carried as the NAMED `*EpochStampResidual`, fail-closed, data-bearing |

`emitEvent` is a log-only effect (forced; full kernel frame unchanged). `custom` is out of scope (no
kernel arm). `heapWrite` has a proven fix but is absent from the live registry, so the apex does not
range over it; today a heap write is attested by the kernel theorems, not yet committed in-circuit
per-turn (the Phase-E relayout lane).

## The deployment boundary (named, not laundered)

- **The deployed VK epoch.** The runtime `compute_commitment` absorbs the committed `record_digest`
  limb (the VK-affecting change shipped as the epoch; Phase C 8-felt widening). The proof is closed
  about the correct circuit; the deploy makes the running system be `S_live`/`Rfix`. Future per-effect
  descriptor gates that change the VK ship as the next epoch + re-pin.
- **The carried `∀ e, descriptorRefines (R e) (kstep e)` composition.** Every live effect's rung is
  proven individually; the carried `∀` is the un-assembled composition (the Lean registry cutover +
  fold). Discharging it makes the apex stand unconditionally mod the floors.
- **The faithful-encoding carriers** (cap-tree↔`Caps`, nullifier-tree↔set, `SpineCommits`) — realizable
  hypotheses (the deployed Merkle fold), the same crypto-floor class as `Poseidon2SpongeCR`.
- **`TransferAuthoritySource`** (the authority leg) — the cap-tree opening the actor's real cap; the
  honest prover supplies it (REALIZABLE, named like `StarkSound`).

## References

- Apex: `Dregg2/Circuit/CircuitSoundness.lean` (`lightclient_unfoolable`); closure
  `Dregg2/Circuit/ClosureFanoutGenuine.lean`. Kernel ref: `Dregg2/Circuit/ActionDispatch.lean`.
- Open-front registry: `Dregg2/Circuit/CircuitOpenFronts.lean` (`countOpenFronts = 0`).
- Hostile-witness extraction: `Dregg2/Circuit/WitnessExtract*.lean`.
- Faithful authority: `Dregg2/Exec/FacetAuthority.lean`, `Dregg2/Circuit/DeployedCapTree.lean`,
  `DeployedCapOpen.lean`, `Emit/CapOpenEmit.lean`, `RotatedKernelRefinementFacet.lean`.
- Value / record-pin / cap-family rungs: `Dregg2/Circuit/RotatedKernelRefinement*.lean`,
  `EffectRefinement.lean`, `EffectRefinementBatch2.lean`; leaf specs `Dregg2/Circuit/Spec/*.lean`.
- Named residuals: `RevokeDelegationEpochResidual` / `SpawnEpochStampResidual` /
  `RefreshEpochStampResidual` in `EffectRefinement.lean` / `EffectRefinementBatch2.lean`.
- Commitment: `cell/src/commitment.rs` (`compute_authority_digest_felt`),
  `circuit/src/effect_vm/cell_state.rs` (`compute_commitment`, the binding tests).
- Live registry: `Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean` (`v3Registry`).
- Crypto floor: `Dregg2/Circuit/Poseidon2Binding.lean`. The assurance case by guarantee:
  `Dregg2/AssuranceCase.lean`. The pin-net: `Dregg2/Claims.lean`. Task #103 (capability crown).
