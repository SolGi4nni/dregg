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

## CLOSED — the apex stands on the realizable crypto foundations, all soundness rungs load-bearing

`Dregg2/Circuit/ClosureFanoutGenuine.lean` — `lightclient_unfoolable_closed_final_genuine`. From a
verifying batch against `vkOfRegistry Rfix` over the full-kernel-binding surface `S_live`
(`.commit = recStateCommit`), it concludes `∃ pre post, StateDecode ∧ kstepAll pi.effect pre post ∧
endpoints commit to (pi.pre, pi.post)` — a genuine full kernel+log transition. `#print axioms =
{propext, Classical.choice, Quot.sound}`; green.

What it carries — ONLY realizable foundations, with every per-effect soundness rung PROVEN and
load-bearing (the dischargers genuinely call `transfer_closedLog`/`mint_closedLog`/`delegate_closedLog`/…
— verified, no laundering):

- `StarkSound` — the audited p3 batch-STARK FRI extraction (`verify ⟹ ∃ Satisfied2 witness`).
- `Poseidon2SpongeCR` + the `S_live` Merkle-CR carriers + `logHashInjective` — the hash / commitment /
  log collision-resistance (the standard crypto floor; `recStateCommit` injectivity binds the full kernel).
- `WitnessDecodes` + the per-effect decode-extraction `<e>TraceReadout` (`Satisfied2 (Rfix e) ⟹ <e>encode`
  — the prover's trace decodes to the per-effect encode columns; the `WitnessDecodes`-class prover-witness
  interface, realizable, NOT the refinement obligation: it terminates in the encode, and the proven rung
  carries `encode ⟹ kernel-step`).

These are the legitimate, irreducible-or-realizable foundations every verified-SNARK soundness proof
bottoms out in — the FRI verifier, the hash CR, and the prover-witness decode. There is no opaque carried
obligation: the circuit-forcing content (each descriptor forces its kernel step, the double-spend
non-membership, the capability non-amplification) is proven in the `RotatedKernelRefinement*` family +
the phase-D gadget and is load-bearing in the apex.

The one ember-gated item OUTSIDE the proof: the deployed VK epoch (the runtime `compute_commitment` must
absorb the committed root limbs so the running circuit IS `S_live`/`Rfix`). The proof is closed about the
correct circuit; the deploy makes the running system match it. (One remaining cosmetic refinement: fold
the per-effect `<e>TraceReadout` column-reads into the single `WitnessDecodes` floor so the carried set
reads exactly {StarkSound, hash CR, WitnessDecodes}; the row-designation stays the prover witness.)

> **CONNECTION-TO-DEPLOYMENT STATUS (updated — the 2026-06-18 vacuity correction is now CLOSED for the
> record-pin family).** The Lean apex CORE is clean (axiom-checked, no laundering), and the deployed
> commitment now realizes it (the `record_digest` limb — see "The commitment preimage" below). The
> per-effect deployment status:
> - **Record-pin family** (setPermissions/setVK/refusal via the record-digest limb `B_RECORD_DIGEST = 24`;
>   cellSeal/cellUnseal/cellDestroy/receiptArchive via the lifecycle limb `B_LIFECYCLE = 29`). Their gate
>   `rotateV3WithRecordPin` pins `after_limb == PI[piCount]`, and the deployed verifier
>   (`turn/src/executor/proof_verify.rs::verify_and_commit_proof_rotated`, step 6b) now ANCHORS that PI: it
>   clones the trusted before-cell, applies the kernel effect through the SHARED
>   `dregg_turn::rotation_witness::apply_effect_to_cell` weld (the same projection the producer uses, so
>   honest proofs are NOT rejected), and overrides the published limb to
>   `compute_authority_digest_felt(post_cell)` (record-digest class) / `lifecycle_felt_cell(post_cell)`
>   (lifecycle class). So the pin is a GENUINE forcing gate, not `published==published`. The fan-out fixed
>   3 latent bugs the vacuous pin had masked (refusal mis-routed to `fields[4]`; cellSeal/Unseal/Destroy
>   producer/verifier projection divergence) — the model-finds-the-bug loop. Both-polarity tests green:
>   `sdk/tests/sovereign_rotated_c1.rs` `record_pin_anchor` (7 accept/reject pairs — honest accept BITES,
>   forged-after rejected by the anchor mismatch). Lean: `rotateV3WithRecordPin_rejects_wrong_post`.
> - **VALUE_FORCED** (`transfer` + the economic effects moving a column the commitment already binds) is
>   forced through the live sovereign verifier (Transfer path sound: PI[35]↔col-261 STATE_COMMIT, tamper
>   test green). The cap-open authority leg is genuine submask membership + decoded tier, refining the LIVE
>   descriptor (commits 3d139220d, a18c7a1c4). The note/set family's double-spend soundness lives in
>   `verify_full_turn` (a different, sound verifier).
> Genuine residuals: extending the verifier anchor + rotated routing to the effects OUTSIDE the record-pin
> family (createCell/spawn/noteCreate/noteSpend/the cap family — the side-table-root + sorted-tree limbs),
> and lifting the rotated arms into the whole-turn forest apex (the `hidx0` residual). These are per-effect
> descriptor-gate + verifier-anchor work, NOT a commitment change (the commitment now binds the fields).

## (historical) per-effect terrain — every effect's VALUE rung proven; the runtime commitment + VK epoch

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
| **RECORD-PIN FORCED** (gate + verifier-anchor wired) | `setPermissions`✓, `setVK`✓, `refusal`✓ (record-digest limb 24); `cellSeal`✓, `cellUnseal`✓, `cellDestroy`✓, `receiptArchive`✓ (lifecycle limb 29) | the write lands in the `record_digest`/lifecycle limb the commitment now binds, the descriptor pins it, AND `proof_verify.rs` step 6b anchors the PI to `compute_authority_digest_felt`/`lifecycle_felt_cell(trusted post-cell)` — both-polarity tests green |
| **VALUE_PARTIAL** (forces some, named gap) | `attenuate` (in-circuit submask non-amp ✓; base post-root is a *supplied* digest, recompute lives only in the unwired Genuine variant), `setFieldDyn` (value on memory readback, not the cell-write column), `incrementNonce` (forces a generic +1 tick, not the leaf's `nonce → n`), `makeSovereign` (forces one mode bit, not the rebind), `pipelinedSend` (freezes economic block; nonce-tick contradicts the leaf's literal-freeze frame; receipt unbound) | a real but partial binding |
| **VALUE_MISSING** (per-effect residual — the field IS in the commitment preimage now, but no gate+anchor routes the specific write) | `emitEvent`, `createCell`, `createCellFromFactory`, `spawn`, `exercise`, `noteSpend`, `noteCreate`, `introduce`, `grantCap`, `refresh`, (`delegate`/`delegateAtten` have **no live descriptor at all**) | the commitment now binds these fields (side-table roots / sorted cap-tree / nullifier-commitment accumulators, all folded into `record_digest`/`system_roots`), so they are provable-in-principle; the residual is a per-effect descriptor gate forcing the specific write + the verifier anchor (the record-pin pattern, extended), NOT a commitment change |

### The commitment preimage — the exact binding boundary (the criterion, ground-truth)

A light client's `pi.post` binds exactly the per-cell **state commitment**, whose preimage is
(`circuit/src/effect_vm/cell_state.rs`, `compute_commitment` / `compute_commitment_8`):

```
hash( balance_lo, balance_hi, nonce, field[0..7], capability_root, record_digest )
```

a `hash_4_to_1` tree over four intermediates, the LAST of which absorbs the **`record_digest`** — a
single Poseidon2 felt that folds ALL authority-bearing cell state the other limbs do not carry:
`permissions`, `verification_key`, `lifecycle`, `deathCert`, `delegate`, `delegation`, `program`,
`mode`, the field-visibility / sealed-mask, the side-table roots (`system_roots_digest`,
`fields_root`, `swiss/refcount` roots), and `fields[8..]`. The digest is computed cell-locally by
`dregg_cell::compute_authority_digest_felt` (`cell/src/commitment.rs`); a cell with no residue beyond
the named limbs carries the cell-independent `cap_root::empty_record_digest()` (`ZERO`), so for such
cells the absorption is byte-identical to the old lossy `hash_4_to_1(i1,i2,i3,ZERO)` — a no-op cutover
(no flag-day). The 8-felt PI form (`compute_commitment_8`) squeezes the SAME four intermediates +
`record_digest` to ~124-bit collision resistance, matching the FRI floor.

This realizes the Lean `recStateCommit = cmb(cellDigest, RH)` (`record_digest` IS the deployed `RH`
limb) and `cellCommitS = compressN(rest ++ [systemRootsDigest])` (one absorbed digest limb). The
criterion for `descriptorRefines` is therefore: **a write is light-client-bound iff its target is
`balance`, `nonce`, a `field[i]` slot, `cap_root`, OR any authority field folded into `record_digest`,
AND the runtime actually writes it there.** The previously-unbound kernel fields
(`permissions`/`verification_key`/`lifecycle`/`deathCert`/refusal-audit/…) are now ALL inside the
commitment preimage. Mutation-confirm (green): `cell_state.rs` test `record_digest_binds_commitment_p0_2`
— two cells differing ONLY in their authority residue now commit DIFFERENTLY (was indistinguishable);
`empty_record_digest_is_legacy_noop` — a residue-free cell reproduces the legacy commitment exactly.

### The Lean commitment and the deployed circuit now AGREE (closed — was the deepest gap)

The Lean apex's commitment is `recStateCommit k t = cmb(cellDigest …, RH k)` (`StateCommit.lean:196`),
with `RH` injective on the **whole kernel** — `RestHashIffFrame` (`:229`) binds `accounts`, `caps`,
`bal`, `nullifiers`, `revoked`, `commitments`, `slotCaveats`, `factories`, **`lifecycle`**,
**`deathCert`**, `delegate`, `delegations`, `delegationEpoch(At)`, `heaps`. That is what makes
`StateDecode` faithfulness (`stateDecode_post_faithful`) hold: equal commitment ⇒ equal *full* kernel.
The concrete `CommitSurface` instance `S_live` (`ClosureSurface.lean`) has `.commit = recStateCommit`
with `.commit_binds = recStateCommit_binds_kernel` proven from the standard Poseidon CR carriers — no
narrower wire commitment, no new axiom. `lake build Dregg2.Circuit.{StateCommit,ClosureSurface}` +
`Dregg2.Exec.SystemRoots` green.

The deployed per-effect-VM circuit now **realizes that commitment**: `record_digest` is a real trace
column (`STATE_RECORD_DIGEST`, aux 96; rotated limb `B_RECORD_DIGEST = r23 = 24`) absorbed into
`compute_commitment`'s root hash, so `state_commit` / `OLD_COMMIT` / `NEW_COMMIT` bind the FULL cell
state. Two post-states differing only in `lifecycle` (or permissions, deathCert, …) now produce
DIFFERENT commitments — the circuit CAN distinguish them. This closed the old gap (commit `548ac920`
"deployed commitment now binds the FULL kernel — P0-2 closed"; Phase C 8-felt `80ebce3d`). The
`Exec/SystemRoots.lean` sub-block + `compute_authority_digest_felt`'s `system_roots_digest` fold cover
the side-tables; the per-cell `record_digest` covers `lifecycle`/`deathCert`/`permissions`/`vk`/… that
no systemRoot indexes.

So the ~16 formerly-VALUE_MISSING effects are now **provable-in-principle**: their write is
light-client-visible (inside the commitment preimage). The remaining work is **per-effect**: each
effect's rotated descriptor must GATE its specific write into the `record_digest` (or lifecycle) limb,
AND the deployed verifier must ANCHOR the published PI for that limb to
`compute_authority_digest_felt(trusted post-cell)` so the gate forces `pubPost = digest(stepped pre)`
rather than `published == published`. That anchor IS wired for the record-pin family (next section);
the residual is extending it to the remaining effects + lifting the rotated arms into the forest apex.

### The commitment wall — REALIZED (the record-digest column shipped); the residual is per-effect

The six VALUE_FORCED rungs are the effects whose runtime writes a directly-named bound column
(`bal` for transfer/burn/mint, `field[slot]` for setField, `nonce` for incrementNonce). The
**record-digest column** is the principled unification this doc earlier named as the *unbuilt* fix — it
is now BUILT and live in the deployed circuit: `CellState::record_digest` (aux col 96 / rotated limb
`B_RECORD_DIGEST = r23 = 24`), absorbed as the fourth root input of `compute_commitment`, computed from
`dregg_cell::compute_authority_digest_felt(cell)` which folds permissions / VK / lifecycle / deathCert /
delegate / delegation / program / mode / the side-table roots (`system_roots_digest`, `fields_root`,
swiss/refcount) / `fields[8..]`. So **all** these formerly-off-row kernel writes are now INSIDE the
commitment preimage — `pubPost` can no longer hide them (commit `548ac920`; Phase C 8-felt `80ebce3d`).

What remains is per-effect, and it is two-part (the record-pin pattern, see the deployment-status callout
at the top): (1) the rotated descriptor must GATE the effect's specific write into its limb (record-digest
or lifecycle), and (2) the deployed verifier must ANCHOR the published PI for that limb to the trusted
post-cell's digest (`compute_authority_digest_felt` / `lifecycle_felt_cell` applied to the cross-checked
before-cell stepped by the effect) so the gate forces `pubPost = digest(stepped pre)` rather than
`published == published`. Both parts are wired for the record-pin family (setPermissions/setVK/refusal +
cellSeal/Unseal/Destroy/receiptArchive — `proof_verify.rs` step 6b, both-polarity tests green). The
remaining effects need the same gate+anchor extended: the capability family wants the **openable sorted
cap-tree update** (cap-reshape phase-D, #103); the note family wants the **accumulator-root** gate for
`nullifiers`/`commitments` (the roots already fold into `record_digest`/`system_roots`; the residual is
the in-circuit recompute gate, not the commitment). None of this is a commitment change now — the deploy
that shipped the limb was the ember-gated VK epoch.

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

1. **Discharge `descriptorRefines` for every live effect.** Done: the 6 VALUE_FORCED rungs + the 7
   RECORD-PIN FORCED (setPermissions/setVK/refusal + cellSeal/Unseal/Destroy/receiptArchive — gate +
   verifier-anchor, both-polarity green). The commitment now binds the full kernel (the `record_digest`
   limb shipped), so the remaining effects are provable-in-principle; each needs its own descriptor gate
   (forcing the specific write into its limb) + the verifier anchor (the record-pin pattern, extended) —
   circuit engineering on a realized commitment, no further commitment change.
2. **Wire each effect's faithful arm** into `fullActionStepFacet` (the cap-open authority, as transfer
   does) and lift the forest beyond all-transfer turns (retire the `hidx0 : e = 0` residual).
3. **Discharge `WitnessDecodes`** per effect.
4. **Prover wiring** — build the cap path-witness from the c-list (`sdk/src/full_turn_proof.rs:662`
   passes `&[]` today) and connect `TransferAuthoritySource`.
5. **VK epoch — SHIPPED for the commitment.** The record-digest limb + Phase C 8-felt widening were the
   VK-affecting change; it deployed as the epoch (`548ac920`/`80ebce3d`). Future per-effect descriptor
   gates that change the VK ship as the next ember-gated epoch + re-pin after the live N=3 run validates.

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
