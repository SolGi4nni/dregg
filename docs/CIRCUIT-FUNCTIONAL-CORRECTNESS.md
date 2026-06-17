# Circuit Functional Correctness — Light-Client Unfoolability

> The state of the circuit-soundness proof: what a light client that verifies only a rotated proof
> can conclude, what is PROVEN to force it, and the per-effect terrain that remains. Honest about
> proven-vs-carried; the per-effect obligation table at the end is the real map of the work.

## The property (the apex — built, faithful, green)

A light client verifies a rotated proof against the live VK and runs nothing else. Soundness:
`verifyBatch accept ⟹ ∃ a genuine kernel transition committing to the published (pre, post)`.

`Dregg2/Circuit/CircuitSoundness.lean` — `lightclient_unfoolable` proves exactly that from *only*
`(pi, π)` + named floors. It **derives** `∃ pre post` (no hypothesized decode): `StateDecode`
faithfulness is a theorem (`recStateCommit` injectivity pins each of `pre.kernel`/`post.kernel` as the
unique kernel committing to the published root), and the cross-step frame is *derived* from the
commitment binding (`stateDecodeChain_frame_continuous`). Green, axiom-clean.

The apex is **parametric in the per-effect kernel step relation `kstep`**, so the same theorem is
instantiated at the toy arm (`dispatchArm`) and the FAITHFUL arm (`dispatchArmFacet`). Its carried
obligations — each explicit, none laundered:

- `StarkSound` — the audited p3 batch-STARK `verify ⟹ ∃ Satisfied2 witness` (FRI extraction). A
  legitimate crypto/audit floor; not provable in Lean.
- `Poseidon2SpongeCR` + the commitment-surface CR set.
- `hrefines` — the registry-wide family `∀ e, descriptorRefines (R e) (kstep e)`. Every live effect's
  rung is now PROVEN individually (see "Final state" below); the carried `∀` is the un-assembled
  composition, and for the ~20 fix effects the rung is against a fix descriptor pending the runtime
  realization.
- `WitnessDecodes` — the witness→kernel-state existence rung, per effect.

## Final state — every effect's VALUE rung proven; the boundary is the runtime commitment + VK epoch

All 36 live effects' VALUE rungs (`descriptorRefines`) are discharged, in one of three honest grades:

- **VALUE_FORCED, realized against the LIVE descriptor** (≈8): `transfer`, `burn`, `mint`, `bridgeMint`,
  `setField`, `incrementNonce`, `emitEvent`, `pipelinedSend` — the effect writes a column the deployed
  commitment already binds (`balance/nonce/field[i]/cap_root`) or (emitEvent/pipelinedSend) is forced by
  the live passthrough + `effects_hash`/PI. These are load-bearing NOW.
- **PRINCIPLED-FIX, proven against a fix descriptor** (≈12): `cellSeal`, `cellUnseal`, `cellDestroy`,
  `refusal`, `receiptArchive`, `setPermissions`, `setVK`, `makeSovereign`, `setFieldDyn`, `createCell`,
  `createCellFromFactory`, `noteCreate` — each adds a committed root limb (`lifecycleRoot`,
  `deathCertRoot`, `auditSlotRoot`, `sovereignCommitRoot`, `dynFieldSlotRoot`, `accountsRoot`,
  `commitmentsRoot`) + a gate forcing the side-table/field write, with both-polarity teeth. The rung is
  proven; it becomes load-bearing once the runtime realizes the limb (one shared change + VK epoch).
- **PHASE-D exact, via the sorted-tree gadget** (the capability family + `noteSpend` + `spawn`):
  `SortedTreeNonMembership.lean` (`nonMembership_sound`/`update_sound`, built on the proven
  `DeployedCapOpen` membership) + `CapTreeUpdate.lean` (insert/update/remove) force the exact sorted-set
  move. **`noteSpend`'s double-spend non-membership is FORCED in-circuit** (the hole is closed). The
  capability family (`delegate`/`introduce`/`grantCap`/`delegateAtten`/`attenuate`/`refresh`/`revoke`/
  `revokeDelegation`/`revokeCapability`) has its exact key-set move forced; `attenuate` is upgraded from
  non-amp-only to set-exact (the ARGUS non-amplification crown, #103). `spawn`'s handoff and the cap
  `Caps`-FUNCTION value (lifting the forced key-set move to the `Caps` function) ride the named faithful
  cap-tree↔kernel encoding carrier.

`custom` is out of scope (no kernel arm). `heapWrite` has a proven fix but is absent from the live
registry (the apex does not range over it).

**What remains for literal "closed-closed" (the precise boundary):**
1. **The runtime commitment realization (VK epoch — ember-gated).** `circuit/src/effect_vm/cell_state.rs::
   compute_commitment` must absorb the new committed root limbs (one digest folding the per-cell
   side-table/audit roots + the sorted cap/nullifier/commitment roots), and the trace-fills must emit
   them. ONE coordinated change realizes the whole fix + phase-D family; it changes the VK, so it ships
   as a VK epoch + registry re-pin. This is the one ember-reserved gate.
2. **The Lean registry cutover + composition.** Swap the fix descriptors into `v3Registry` so `R e` is the
   descriptor each proof is about, then assemble the per-effect rungs into `∀ e, descriptorRefines (R e)`
   — discharging the apex's carried `hrefines` so it stands unconditionally (mod the floors).
3. **The faithful-encoding carriers** (cap-tree↔`Caps`, nullifier-tree↔set, `SpineCommits`): realizable
   hypotheses (the deployed Merkle fold), the same crypto-floor class as `Poseidon2SpongeCR` — discharge
   or accept as named floors.
4. **`WitnessDecodes`** per effect; the prover wiring (the `&[]` cap path-witness at
   `sdk/src/full_turn_proof.rs:662`).

The crypto floors that legitimately remain are `StarkSound` and the Poseidon2 / permutation / Merkle CR.

## The authority leg — closed faithfully (the deployed two-axis gate)

Every kernel arm carries an authority check. The toy kernel used `authorizedB` (a `node`/`Auth.write`
shadow). The deployed model is **`AuthRequired` tier × `EffectMask` facet** (`cell/src/permissions.rs`,
`cell/src/facet.rs`). The faithful model and its in-circuit discharge:

- `Dregg2/Exec/FacetAuthority.lean` — `authorizedFacetB` (tier × facet), byte-faithful to the Rust;
  `execFaithful` gates on it; both-polarity teeth.
- `Dregg2/Circuit/DeployedCapTree.lean` — the deployed depth-16 7-field cap-tree, committing the
  chip's **rate-8** Poseidon2 absorb (`CapHashScheme` bundles one carrier `chipAbsorb` + `chipCR`);
  the rate-4/rate-8 reconciliation is **closed** (`chipAbsorb_realizes` by `rfl` — `SchemeRealizedByChip`
  discharged).
- `Dregg2/Circuit/DeployedCapOpen.lean` + `Emit/CapOpenEmit.lean` — the depth-16 cap-membership open
  as **generic Lean-emitted constraints** (chip `Lookup`s + gates; LAW#1-clean), emitted into the live
  descriptor `capOpenAttenuateV3`; `capOpenAttenuateV3_authorizes ⟹ authorizedFacetB`.
- `Dregg2/Circuit/RotatedKernelRefinementFacet.lean` — the faithful transfer keystone:
  `BalanceMovementSpecFacet` (authority conjunct = `authorizedFacetB`); `transfer_descriptorRefines_facet`
  (value leg reused from the transfer value rung; **authority leg FORCED in-circuit by the cap-open**,
  not carried). `execFaithful_iff_specFacet` is the faithful executor ⟺ spec (both directions).
- `Dregg2/Circuit/RotatedKernelForestFacet.lean` — the faithful WHOLE-TURN apex
  (`lightclient_turn_unfoolable_forest_facet`) over `fullActionStepFacet` (the `.balanceA` arm faithful),
  with the toy side-condition eliminated for the faithful transfer arm (`dispatchArmFacet_to_full
  ActionStepFacet`). Generic fold `turnDecodeChain_refines_turnSpec_gen`.

Named residual on the authority leg: `TransferAuthoritySource` — the cap-tree opening the *ledger*
commitment cannot certify (the honest prover opens the actor's real cap; REALIZABLE, named like
`StarkSound`). The tier is read as `Signature` (the `authTagGate` pins `auth_tag = 1`); generic
tier-read-off-leaf and the `Custom`-tier vk decode are named felt residuals.

## The per-effect VALUE rung — `descriptorRefines` discharged so far

`descriptorRefines (R e) kstep` requires the LIVE rotated descriptor, satisfied, to force the leaf
spec — i.e. to force `pubPost = commit(correctly-stepped pre)`. A gate that pins the moved column into
the published commitment is what makes this true; absent such a gate, a prover may publish a
commitment to an *un*-stepped post-state, so the rung is genuinely **false** (not merely unproven).

PROVEN value rungs (the descriptor genuinely forces the move; both-polarity forgery teeth bite):

- **transfer** — `RotatedKernelRefinement.lean` (`transfer_descriptorRefines`, the template). Forces
  the signed `bal_lo` debit/credit + availability.
- **burn / mint / bridgeMint** — `RotatedKernelRefinementMintBurn.lean`. The holder-debit / recipient-
  credit limb is gate-forced (`gBalLoDebit`/`gBalLoCredit`); burn's availability is the live range
  tooth. bridgeMint re-exports mint (same `recCMintAsset`/`mintV3`).
- **setField** (per slot) — `RotatedKernelRefinementSetField.lean`. The selector-gated write
  `gFieldWriteP1 slot` pins `fields[slot]_after = param1` onto an in-commitment state column; siblings
  frozen.

The standing honesty boundary, uniform across these (transfer included): the gate forces the
**designated moved column**, and the forgery tooth bites there; the secondary cell (a burn's well
credit), the cross-cell ledger frame, the kernel guard, the 16-field frame, and the receipt log ride
the named `rotatedEncodes*` decode — the record-layer residual a per-row value block cannot witness.

## The obligation table — the real terrain (36 live effects)

A read of every live rotated descriptor against its kernel leaf spec. The class is **whether the
descriptor forces the leaf-spec move into the published commitment**, decided per the `descriptorRefines`
criterion above.

| class | effects | what it means |
|---|---|---|
| **VALUE_FORCED** (rung PROVEN) | `transfer`✓, `burn`✓, `mint`✓, `bridgeMint`✓, `setField`✓, `incrementNonce`✓ | a gate pins the moved column into the commitment |
| **VALUE_PARTIAL** (forces some, named gap) | `attenuate` (in-circuit submask non-amp ✓; base post-root is a *supplied* digest, recompute lives only in the unwired Genuine variant), `setFieldDyn` (value on memory readback, not the cell-write column), `incrementNonce` (forces a generic +1 tick, not the leaf's `nonce → n`), `makeSovereign` (forces one mode bit, not the rebind), `pipelinedSend` (freezes economic block; nonce-tick contradicts the leaf's literal-freeze frame; receipt unbound) | a real but partial binding |
| **VALUE_MISSING** (real gap — the runtime freezes the target column and routes the write off-row) | `setPermissions`, `setVK`, `emitEvent`, `refusal`, `receiptArchive`, `createCell`, `createCellFromFactory`, `spawn`, `cellSeal`, `cellUnseal`, `cellDestroy`, `exercise`, `noteSpend`, `noteCreate`, `introduce`, `grantCap`, `refresh`, (`delegate`/`delegateAtten` have **no live descriptor at all**) | nothing forces `pubPost` to reflect the change — needs a RUNTIME+circuit fix (below), then a proof |

### The commitment preimage — the exact binding boundary (the criterion, ground-truth)

A light client's `pi.post` binds exactly the per-cell **state commitment**, whose preimage is
(`circuit/src/effect_vm/cell_state.rs:76`, `compute_commitment`):

```
hash( balance_lo, balance_hi, nonce, field[0..7], capability_root )
```

and NOTHING else. The 8 `field[i]` slots are **generic** developer slots (`slotName slot =
"slotfield{n}"`), not the kernel's semantic fields. So `reserved`/`mode_flag`/`sealed_field_mask` are
**not** committed; and the kernel's semantic fields (`permissions`, `verification_key`, `lifecycle`,
`deathCert`, `refusal`, the sorted cap-table, `nullifiers`, `commitments`) are committed only insofar
as the executor projects them onto a generic `field[i]` slot or the `cap_root`. The criterion for
`descriptorRefines` is therefore sharp: **a write is light-client-bound iff its target is `balance`,
`nonce`, a `field[i]` slot, or `cap_root`, AND the runtime actually writes it there.** (This corrects
two earlier PARTIAL guesses: `makeSovereign`'s `reserved += 256` mode bit is NOT in the preimage, so it
is genuinely unbound, not partial.)

### The deepest finding — the Lean commitment is RICHER than the circuit realizes

The Lean apex's commitment is `recStateCommit k t = cmb(cellDigest …, RH k)` (`StateCommit.lean:196`),
and `RH` is *assumed* injective on the **whole kernel** — `RestHashIffFrame` (`:229`) binds `accounts`,
`caps`, `bal`, `nullifiers`, `revoked`, `commitments`, `slotCaveats`, `factories`, **`lifecycle`**,
**`deathCert`**, `delegate`, `delegations`, `delegationEpoch(At)`, `heaps`. That is what makes
`StateDecode` faithfulness (`stateDecode_post_faithful`) hold: equal commitment ⇒ equal *full* kernel.

But the **deployed per-effect-VM circuit does not realize that commitment**. Its `state_commit` binds
only `balance/nonce/8-generic-fields/cap_root` (`cell_state.rs:76`), and `circuit/src/effect_vm/pi.rs`
publishes **no** `system_roots`. The Lean `system_roots` sub-block (`Exec/SystemRoots.lean`) is 8 roots
indexed for specific side-tables, and `lifecycle`/`deathCert`/`permissions`/`verification_key` are **not
among them**. So `RestHashIffFrame` is, for those fields, a CR carrier **stronger than the deployed
circuit computes** — the circuit cannot distinguish two post-states that differ only in `lifecycle` (or
permissions, deathCert, …), yet the apex assumes the commitment does.

This is the precise reason the ~16 VALUE_MISSING effects need a **commitment change, not a proof**: the
deployed circuit must actually bind those fields (extend the per-cell preimage, or publish system_roots
covering them — the principled unification is a per-touched-cell **record-digest** column that realizes
`RH`), and the runtime must emit them. Only then can the concrete `CommitSurface` instance satisfy
`commit_binds` for those fields and the per-effect `descriptorRefines` discharge. Until then, the apex
is faithful *to a commitment richer than the deployed VK* — honest as a Lean theorem, but its concrete
realization is exactly this gap. (The 6 VALUE_FORCED effects move only columns the circuit DOES bind, so
their rungs are realized.)

### The VALUE_MISSING wall — it is a runtime fix, not a Lean-only one (the session's key finding)

The six VALUE_FORCED rungs are exactly the effects whose runtime writes one of those bound columns
(`bal` for transfer/burn/mint, `field[slot]` for setField, `nonce` for incrementNonce).

For the ~17 VALUE_MISSING effects, the **runtime hand-AIR runs a Stage-3 passthrough row that FREEZES
all 8 `field[i]` columns** and routes the actual write off-row — through `params[0]` + `effects_hash`
(setPermissions/setVK/refusal/emitEvent/receiptArchive) or into kernel **side-tables that have no
committed column or systemRoot** (`lifecycle` for seal/unseal/destroy, `deathCert` for destroy,
`nullifiers`/`commitments` for the note family, the **sorted** cap-table for the capability family — see
attenuate's accumulator-vs-sorted-tree note above). Because the value is not in a bound column, no gate
can force `pubPost` to reflect it; transplanting a `setField`-style write-gate would force a column the
runtime freezes and make the honest trace UNSAT (a degradation, not a fix).

So closing these requires a **runtime + circuit change**: bind each effect's real write into a committed
column/root and have the runtime emit it there, then a `setField`-style refinement discharges. The
principled unification (matching the dregg3 "sorted-Poseidon2 everywhere" line): a **per-touched-cell
record-digest column** recomputed in-circuit would bind *all* cell-field writes (permissions/vk/lifecycle/
refusal/deathCert) at once; the capability family wants the **openable sorted cap-tree update**
(cap-reshape phase-D, #103); the note family wants **accumulator-root columns** for `nullifiers`/
`commitments`. Each is VK-affecting (and the deploy is the ember-gated VK epoch).

Two flagged severities:

- **`spawn` is actively self-contradictory**: its descriptor pins `cap_root` FROZEN (`gCapPass`), but
  `SpawnSpec`'s load-bearing content IS the parent→child capability handoff. The live descriptor and
  the leaf spec disagree on the security-critical move.
- **`heapWrite` has no live descriptor at all** (absent from `v3Registry`), and even `HeapWriteSpec`
  takes `newRoot` as a free parameter — a spec-level gap under the missing descriptor.

The capability family: only **`attenuate`** carries an in-circuit `granted ⊑ held` non-amp gate
(`attenuateV3`'s `submaskLookup`, proven `attenuateV3_non_amp`). `introduce`/`grantCap`/`refresh`/
`delegate` enforce non-amplification only out-of-circuit; the proven-but-unwired
`attenuateVmDescriptorGenuineNonAmp` (with real both-polarity non-amp theorems, 186-width) is the fix
material to wire in.

## What "closed-closed" requires (honest)

1. **Discharge `descriptorRefines` for every live effect.** 5/36 done (the VALUE_FORCED rungs). The
   ~5 PARTIAL need bounded extra binding; the ~17 MISSING need **descriptor fixes** (emit gates that
   bind the actual lifecycle/permissions/vk/log/handoff/deathCert/cap change into the committed column),
   then proofs. This is real circuit engineering, not only Lean — and it is VK-affecting.
2. **Wire each effect's faithful arm** into `fullActionStepFacet` (the cap-open authority, as transfer
   does) and lift the forest beyond all-transfer turns (retire the `hidx0 : e = 0` residual).
3. **Discharge `WitnessDecodes`** per effect.
4. **Prover wiring** — build the cap path-witness from the c-list (`sdk/src/full_turn_proof.rs:662`
   passes `&[]` today) and connect `TransferAuthoritySource`.
5. **VK epoch** — the descriptor fixes change the VK; an ember-gated epoch + re-pin after the live N=3
   run validates.

The crypto floors that legitimately remain are `StarkSound` and the Poseidon2 / permutation CR.

## References

- Apex: `Dregg2/Circuit/CircuitSoundness.lean` (`lightclient_unfoolable`, the forest §8, the generic
  fold). Kernel ref: `Dregg2/Circuit/ActionDispatch.lean` (`fullActionStep`, the ~30 leaf-spec arms).
- Faithful authority: `Dregg2/Exec/FacetAuthority.lean`, `Dregg2/Circuit/DeployedCapTree.lean`,
  `DeployedCapOpen.lean`, `Emit/CapOpenEmit.lean`, `RotatedKernelRefinementFacet.lean`,
  `RotatedKernelForestFacet.lean`.
- Value rungs: `Dregg2/Circuit/RotatedKernelRefinement.lean` (transfer), `…MintBurn.lean`,
  `…SetField.lean`; leaf specs `Dregg2/Circuit/Spec/*.lean`.
- Live registry: `Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean` (`v3Registry`, 36 entries);
  descriptor sources `Dregg2/Circuit/Emit/EffectVmEmit*.lean`.
- Crypto floor: `Dregg2/Circuit/Poseidon2Binding.lean`. Task #103 (capability crown).
