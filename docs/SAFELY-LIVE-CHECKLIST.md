# SAFELY-LIVE-CHECKLIST — the mechanically-auditable burn-down

The goal "safely live within dregg" is satisfied when **every box below is checked, each by
its stated green check** — not by prose. Law #6: a named gap is never a deliverable. A box is
checked ONLY when its verification command is green at HEAD.

Reconciled against HEAD `867f6a66a` (audit a6473605). The dominant open axis is **WIRE, not
Lean**: 18 of 30 effects are FORCED-IN-LEAN (the apex consumes `Satisfied2(deployed descriptor)`,
editing the descriptor reds the apex) but the deployed producer selects the *plain* descriptor /
the verifier rides the record-pin residual. The single structural unlock is the producer
re-point + the VK epoch that absorbs the record-digest + sorted roots into `compute_commitment`.

## STATE TODAY (verified)
- FORCED-ON-WIRE + light-client-verifiable: **8/30** — transfer, burn, mint, bridgeMint, setField,
  incrementNonce, emitEvent, pipelinedSend (the moved column is already in `compute_commitment`'s preimage).
- FORCED-IN-LEAN-NOT-WIRE: **18/30** — lifecycle/permsVK/birth/notes/cap-write families.
- MODELLED-FLOOR (not yet `_sat`): receiptArchive, attenuate(2-arm), revoke(tag-2), refreshDelegation.
- cap-AUTHORITY light-client forge: **CLOSED** (verify rejects plain cap descriptors, e26fe42df).

## (A) WIRE — producer-selection re-point — BLOCKED BY A DATA-AVAILABILITY GAP (audit 2026-06-20)
The re-point CANNOT go green as written: the blocker is NOT the producer wiring or a WIDE-registry
gap — it is the cap-tree WRITE WITNESS (`map_heaps`) data availability. Findings:
- The write-bearing wrappers (`delegate/introduce/delegateAtten/revokeDelegationWriteCapOpenVmDescriptor2R24`)
  ARE in `V3_STAGED_REGISTRY_TSV` — the registry the SDK cap-open route (`cap_open_descriptor_json_by_key`)
  AND the light-client verifier (`verify_effect_vm_rotated_with_cutover`) both resolve against. So the
  registry-availability concern is RESOLVED FAVORABLY (the WIDE registry is a separate 8-felt-commit path,
  not this seam).
- Each write wrapper carries a genuine `map_op` `read`+`insert`/`write` (guard = the selector marker, NOT
  vacuous) binding the BEFORE cap-root (col 65) → AFTER cap-root (col 87) via a sorted-Poseidon2 cap-tree
  write. The IR-v2 prover realizes that `map_op` against a witness HEAP whose root == the BEFORE cap-root
  (`prove_vm_descriptor2`'s `map_heaps`, exactly as `note_spend` threads its nullifier tree) and CHECKS the
  genuine post-write root == the claimed AFTER cap-root (a wrong post-root is UNSAT — NOT fakeable).
- `prove_effect_vm_cap_open` threads NO `map_heaps` (passes `&[]`), and the data needed to build one — the
  cell's FULL sorted c-list leaf-set — is NOT carried by `CapMembershipWitness` (only one opened leaf + its
  path) NOR available at the node prove site (`node/src/turn_proving.rs` has the consumed cap, not the
  cell's whole c-list). So routing to the write wrapper produces an UNPROVABLE proof.
- PROVEN (no silent forge): the write wrapper FAIL-CLOSES with empty map_heaps ("no witness heap with
  root …"), it does NOT launder a fabricated post-cap-root. Test:
  `write_cap_open_wrapper_requires_cap_tree_write_witness_no_silent_forge` (sdk/src/full_turn_proof.rs, GREEN).
- NOTE: the task's "re-point `rotated_descriptor_name`" target is the WRONG seam — that resolver is the
  non-cap BASE cohort (36 members, EXCLUDES all `…CapOpen…` by `resolvers_cover_exactly`). The cap-effect
  selection seam is `cap_open_route_for_run` (`route.key`). Re-pointing EITHER to a write wrapper is
  unprovable until the write witness is threaded.
- [ ] CLOSURE (data-availability, NOT a re-point): (1) extend `ConsumedCapWitness`/`CapMembershipWitness`
      to carry the target cell's full sorted c-list leaf-set; (2) plumb it from `node/src/turn_proving.rs`;
      (3) add a cap-tree→`map_heaps` bridge generator (mirror `generate_rotated_note_spend_trace_with_nullifier_tree`);
      (4) thread it through `prove_effect_vm_cap_open` → `prove_vm_descriptor2`; (5) re-point
      `cap_open_route_for_run` to the write wrappers. THEN the cap-WRITE post-root becomes light-client-verifiable.
- [ ] the cap-WRITE light-client verifier tooth — extend `is_forbidden_plain_cap_descriptor` to ALSO reject
      the authority-ONLY CapOpen (introduceCapOpen/revokeCapOpen/grantCapCapOpen) for write-bearing cap
      effects. BLOCKED ON THE ABOVE: adding it now would reject the honest authority-only cap-open route
      (`cap_open_fanout_revoke_*` GREEN today) with NO provable write-bearing route to migrate to. Land it in
      the SAME breath as the producer re-point, not before.

## (B) GREEN-BOARD (VK-FREE-driveable NOW)
- [ ] `resolvers_cover_exactly_the_rotated_registry` RED (37 vs 36) — heapWriteVmDescriptor2R24 is a
      registry member with no resolver arm + no live HeapWrite Effect variant. Reconcile (add the
      Effect+selector+resolver if heapWrite is live, OR exclude it as separately-routed) — NOT a blind bump.
      **green:** `cargo test -p dregg-circuit resolvers_cover_exactly_the_rotated_registry`.
- [x] receiptArchive(40) spec-bridge — the dispatch arm reduces to the toy record-slot `ReceiptArchiveSpec`;
      reconcile the arm to `ReceiptArchiveLifecycleSpec` (what the deployed disc gate forces) + a `_sat` discharger.
      **green:** editing `receiptArchiveV3`'s disc gate reds the apex (a mutation test).
- [x] attenuate(12) + revoke(tag-2) `_sat` — the apex calls the modelled `attenuate_closedLog`/`revoke_closedLog`
      (encode-consuming), not a deployed-descriptor force-lemma. Wire `_sat` dischargers.
      **green:** editing the attenuate/revoke descriptor reds the apex.
- [ ] SetProgram circuit witness — SetProgram reuses EFFECT_SET_VERIFICATION_KEY's tag (action.rs:2191), no own rung.
      **green:** a `setProgramV3` descriptor + `closedLogExtract_setProgram_closed` in the apex.

## (C) VK EPOCH (ember-gated — but VK-FREEDOM ERA, so driveable; the unlock for all 18 not-on-wire)
- [ ] `compute_commitment` (cell_state.rs:76) absorbs the record-digest + sorted cap/nullifier/commitment/deleg
      roots, so the running circuit IS `S_live`/`Rfix` — the 18 FORCED-IN-LEAN writes become on-wire-realized,
      and a light client binds lifecycle/perms/vk/deathCert/nullifier/commitment columns, not just balance/nonce/field/cap_root.
      **green:** a light-client test rejecting a post-state differing ONLY in (lifecycle | permissions | vk | nullifier-root) under the deployed VK.
- [ ] refreshDelegation(55) deleg-tree write column — new deleg-tree map-op + its runtime column (cap_root is the wrong primitive).
      **green:** a `refreshDelegation_descriptorRefines_sat` consuming a deleg-tree write descriptor.

## INVARIANTS (must stay green throughout)
- [ ] `lake build Dregg2` axiom-clean (⊆ {propext, Classical.choice, Quot.sound}).
- [ ] `scripts/check-descriptor-drift.sh` PASS.
- [ ] `cargo test -p dregg-sdk --features prover` + `cargo test -p dregg-circuit` green.

## (D) OWN-LANE (NOT in the 30/30 write-binding scope — tracked, not blocking this goal)
- apexLowers distributed-modernization · l4v marshal translation-validation · WitnessDecodes prover wiring
  (the cap path-witness from the c-list) · network-genesis ceremony · HORIZONLOG compaction.

## HEADLINE GREEN-TEST (the goal is met when this is true)
30/30 effects FORCED-ON-WIRE + light-client-verifiable: every cap/write effect's producer selects + verifier
checks the authority-AND-write-bearing descriptor; (A)+(B)+(C) boxes checked; the INVARIANTS green; the board red-free.

## PROGRESS LOG (genuine green only — verified at source/by unambiguous test)
- ✅ attenuate(12) Class-A (b2ef6e23e) · resolvers_cover_exactly GREEN (b2ef6e23e) · receiptArchive(40) Class-A
  (56178b050, executor↔spec weld preserved) · cap-write descriptors nonce-TICK + Insert anchor-key (in 0f0921092
  — MISATTRIBUTED to a parallel seL4 commit by the shared-index hazard; work is safe in HEAD, lake green 4106).
- ✅ cap_write_revoke_proves_and_verifies_light_client GENUINELY passes (no catch_unwind) — the revoke cap-WRITE
  post-root proves + light-client-verifies. BUT the cap-write BOX stays UNCHECKED pending the no-silent-forge
  resolution (the empty-map_heaps test went green=success where it expected fail-closed — forge-vs-vacuous under
  resolution by ac39a343; a forge here = critical, must resolve before the box checks).
- ⬜ STILL OPEN: the no-silent-forge resolution (BLOCKING the cap-write box) · the verifier authority-only tooth
  (flips ON but breaks 3 existing tests that exercise the authority-only route — needs them reconciled) · the 3
  Insert Rust wiring (CapTreeWriteOp::Insert) · revoke(tag-2) frozen-face · refreshDelegation deleg-column ·
  SetProgram witness · the VK epoch (staged plan, docs/VK-EPOCH-PLAN.md).

## ⚠ PROVENANCE LESSON (2026-06-21): the shared-index hazard
A parallel agent's `git commit` swept up MY staged cap-write descriptor files into commit 0f0921092 (a seL4 commit).
The work is safe (in HEAD, green) but misattributed. LESSON: in a multi-agent swarm, do NOT leave files `git add`-staged
across a window where parallel agents may commit — stage-and-commit atomically in one shell, or the shared index leaks.
