# Codex design — the ordered segment-accumulator fix for the IVC mixed-root hole (2026-06-24)

Codex's recommended construction (gigabrain advice, not a review): close the mixed-root forgery by making the whole-chain claim sound-BY-CONSTRUCTION — a constant-size ordered segment accumulator carried by every descriptor leaf + each aggregation node, replacing the separate binding leaf in the soundness-critical path.

HORIZONLOG.md:4198:- **#103 cap-crown Phase-D — the 4-ary c-list `membership` leg vs. the sorted `cap-membership` leg (retire-or-keep).** `sdk/src/full_turn_proof.rs` attaches TWO distinct membership sub-proofs to a cap-gated turn, proving DIFFERENT claims: (a) the **4-ary c-list `membership` leg** (`:978-1012`, witness `MembershipWitness` `:177`, `prove_membership_p3` over the generic positions-indexed `P3MerklePoseidon2Air`, PI `[leaf_hash, root]`, vk `merkle_poseidon2_descriptor`) proves "an opaque capability `leaf_hash` is present in A Merkle tree at the witnessed positions" — a GENERIC membership statement; its root is not structurally pinned to the authenticated `cap_root`, and the leaf is an opaque hash (not the typed 7-field cap preimage). (b) the **sorted `cap-membership` leg** ("cap Phase D", `:1075-1100`, witness `CapMembershipWitness` `:212` ← `ConsumedCapWitness`, `prove_cap_membership_p3` over the SORTED `CanonicalCapTree`, directional path, vk `cap_membership_circuit_descriptor`, expectation `CapMembershipExpectation` `:239` pins `pi[CAP_ROOT]` to the trusted root `:248`) proves "the SPECIFIC CONSUMED capability's full 7-field leaf preimage opens against THE holder's real sorted `cap_root` tree" — the authority leg that ties the acting/consumed cap to the authenticated cap-state, with sorted single-leaf-per-slot semantics. **The two are not redundant:** the sorted leg gives the strictly stronger, structurally-pinned, typed-leaf guarantee; the 4-ary leg gives a weaker generic membership over an unpinned root with an opaque leaf. **Retire-vs-keep tradeoff:** for a cap-gated turn the sorted `cap-membership` leg SUBSUMES the authority claim the 4-ary leg makes (consumed-cap-in-the-real-cap_root ⊃ opaque-leaf-in-some-4-ary-tree), so the 4-ary leg is retireable FOR CAP-GATED TURNS on the claim alone. **Live-producer evidence (the deciding fact):** there is currently NO live producer that sets `membership: Some(MembershipWitness{..})` — the only two build sites (`full_turn_proof.rs:2303`, `:2774`) are both inside `#[cfg(test)] mod tests` (`:2107`) using `merkle_test_witness`; the only LIVE membership-leg producer is `cap_membership` (`node/src/turn_proving.rs:518`, `CapMembershipWitness::from_consumed`). So today the 4-ary `membership` leg is dead on the live path — its `Option`/`P3MerklePoseidon2Air`/`merkle_poseidon2_descriptor` plumbing is wired + SDK-tested but unfed. **The keep argument** is therefore forward-looking, not current: the 4-ary leg is the GENERIC credential/c-list membership primitive (opaque leaf, witnessed root, no sorted `cap_root` to open against) that a NON-cap predicate-credential turn-shape WOULD use — retiring it removes that future affordance and the `merkle_poseidon2` descriptor's only full-turn consumer. **Recommendation (ember to ratify):** keep the 4-ary leg as the general-membership primitive but DO NOT couple it to cap-gated turns (the sorted leg is the cap authority leg of record); OR, if no near-term non-cap credential turn-shape is planned, demote the 4-ary leg + its descriptor to a clearly-labelled "general membership, no live producer" status (Research tier) so it stops reading as a live cap-authority alternative. Before any removal, confirm no in-flight feature wires a live `membership: Some(..)`. Named: cap-crown #103 Phase-D map, 2026-06-13. (Left intact — characterization only, per the brief.)
HORIZONLOG.md:4212:`builder.when_transition()` (`descriptor_ir2.rs:1763-1772`) — every row BUT the last. So **Lean-Satisfied2 is
HORIZONLOG.md:4213:STRICTER than Rust-accept on the last row**, and the byte-identity descriptor differential does NOT catch it (the
HORIZONLOG.md:4224:when_transition) across the rotated descriptor; (2) trace which row feeds the published 8-felt commit + whether
HORIZONLOG.md:4240:   tooth) closes it. CONFIRM-AT-SETTLE: are multi-asset atomic turns reachable? If yes → live hole, not nicety.
HORIZONLOG.md:4279:- IR-v2 deployed path: `descriptor_ir2.rs:1763` puts Gate + Transition under `builder.when_transition()`.
HORIZONLOG.md:4295:precedent exists (`effect_vm_descriptor_exhaustive_differential.rs` = generator-driven differential vs the REAL
HORIZONLOG.md:4321:   descriptor_ir2.rs:1744) + the every-row Poseidon2 hash-site lookups over the last row's own state_after
HORIZONLOG.md:4322:   (descriptor_ir2.rs:1797). NO commitment-malleability hole. (Tightening, not a hole: the NoOp pad's
HORIZONLOG.md:4336:   degree bound is enforced symbolically by verify_batch. check_descriptor2 bounds-checks every producer index
HORIZONLOG.md:4337:   FIRST (descriptor_ir2.rs:4445/1172). One cheap defense-in-depth tightening: proof_verify.rs:357/359/391/393
HORIZONLOG.md:4341:Poseidon2, out-lanes assert_zero descriptor_ir2.rs:2039) · mem/map ops (committed sub-AIRs + zero-summed buses).
HORIZONLOG.md:4356:`Satisfied2` is NOT a faithful denotation of the deployed Rust `verify_vm_descriptor2`. The byte-identity
HORIZONLOG.md:4465:  + fields WITH provenance into the document commitment. The anti-forge tooth is TESTED — forging or
HORIZONLOG.md:4470:  `compute_heap_root` — the anti-forge tooth RE-PROVEN against the REAL root, not the `DefaultHasher`
HORIZONLOG.md:4534:  local arms via the actual Ir2Air::eval (96/216, no drift), bus arms via the actual prove/verify_vm_descriptor2
HORIZONLOG.md:4542:HYGIENE: --features verifier (light-client build) un-broken; wide-descriptor width-skew (188-col) regen IN FLIGHT.
HORIZONLOG.md:4572:ClosureFanoutGenuine.lean:828 is a 36-way split, every slot a proven <e>_descriptorRefines concluding the real
HORIZONLOG.md:4575:- CLASS A (circuit-descriptor-bound, edit propagates RED): 6 effects — transfer, mint, burn, setField,
HORIZONLOG.md:4582:  circuit denotation. Spec-edit still reds them (they refine real Spec); circuit-descriptor-edit does NOT.
HORIZONLOG.md:4583:  Worst: heapWrite(56) Rfix 56 = the WRONG descriptor (transfer fallback), descriptor-abstract by design.
HORIZONLOG.md:4596:- ⚑ THE MISSING WELD (the single highest-leverage edit on the board): the multi-turn IVC / finalized-history /
HORIZONLOG.md:4601:  stack. Likely ~one bridging theorem (modulo the IVC recursion shape).
HORIZONLOG.md:4603:  mint descriptor, rides kstepAll. Argus/Effects/BridgeMint.lean clean (the memory's "breakage" flag is STALE).
HORIZONLOG.md:4633:  axiom (multi-turn/IVC/joint/promises all proven-but-parallel).
HORIZONLOG.md:4647:PROVEN-BUT-UNJOINED weld, and the descriptor (VK-affecting) work is ALREADY DEPLOYED.
HORIZONLOG.md:4654:  never joined -> descriptor edit doesn't propagate red.
HORIZONLOG.md:4655:- THE FIX = non-VK-affecting PROOF-COMPLETION (not descriptor-completion): a cellSeal_forced extraction (transfer's
HORIZONLOG.md:4661:  active-row satisfiedVm -> *_forces -> decode -> root_binds -> kernel field; (4) rewire e_descriptorRefines +
HORIZONLOG.md:4663:- ⚑ THE (b)-GAP DISCRIMINATOR: a slot is a REAL descriptor gap (VK-affecting) iff its committed limb has NO
HORIZONLOG.md:4698:  DELEGATEATTEN, REVOKEDELEGATION, REFRESHDELEGATION. Root cause: the cap-open descriptor forces the authority
HORIZONLOG.md:4703:  false-but-hidden at the deployed descriptor: a prover can publish a wrong post-cap-root and the circuit won't
HORIZONLOG.md:4714:descriptor gaps [VK, mirror attenuate's keepWriteOp + _non_amp]; (c) revokeCapability force-lemma; (d) heapWrite
HORIZONLOG.md:4732:## ⚑ LIFECYCLE LAZY-fan landed (a6ef3b7c) — 3 Class-A + a 6th REAL GAP found (receiptArchive spec↔descriptor divergence)
HORIZONLOG.md:4734:banked, tree red from parallel CapFamily/PermsVK mid-edit): cellUnseal_descriptorRefines_sat (disc gate
HORIZONLOG.md:4735:forces lifecycle=lcLive), cellDestroy_descriptorRefines_sat (BOTH legs: lifecycle=lcDestroyed + deathCert via the
HORIZONLOG.md:4736:record-pin folded in the disc gate), refusal_descriptorRefines_sat (record-pin forces fieldOf refusalField = 1).
HORIZONLOG.md:4738:⚑ receiptArchive = a 6th REAL GAP (different kind: spec↔descriptor DIVERGENCE, not a missing write): deployed
HORIZONLOG.md:4741:(post.lifecycle = pre.lifecycle) — they CONTRADICT. Class-A unreachable from the deployed descriptor without a
HORIZONLOG.md:4742:descriptor change (bind the audit record slot) OR reconciling the spec to the deployed Archived side-table
HORIZONLOG.md:4743:semantics. = an EMBER/descriptor decision, not Lean wiring. Documented at RotatedKernelRefinementLifecycleDisc §6.
HORIZONLOG.md:4756:  the insertWriteOp descriptor + _forces_write keystones) + revokeCapability (removeWriteOp deployed)
HORIZONLOG.md:4761:  …Genuine face (a VK cutover, the …Genuine descriptors EXIST but aren't deployed). Cleanly Class-B-pending.
HORIZONLOG.md:4762:- receiptArchive: spec↔descriptor CONTRADICTION (spec writes record-slot+freezes lifecycle; descriptor forces
HORIZONLOG.md:4763:  lifecycle=Archived) — ember/descriptor decision.
HORIZONLOG.md:4766:NEXT: (a) wire the new *_descriptorRefines_sat into the apex fanout (ClosureFanoutGenuine — MAIN LOOP owns, serial);
HORIZONLOG.md:4767:(b) the VK JSON descriptor regen + drift-gate for the cap-write changes; (c) the 3 frozen-face cutover; (d)
HORIZONLOG.md:4812:  sealed Snapshot (reuses snapshot.rs:80 fail-closed root tooth) + ImageAttestation.
HORIZONLOG.md:4814:  reconstruct tooth, conservation Σ=0, factory provenance, program-for-life binding so a cell can't be smuggled
HORIZONLOG.md:4825:Guarantee A (Authority) circuit-FORCED (a circuit-descriptor edit reds the rung, mutation-confirmed) status by effect:
HORIZONLOG.md:4835:  deleg-tree map-op + runtime column (delegRoot_runtime_column_pending). The one genuine descriptor-architecture
HORIZONLOG.md:4838:SERIAL TAIL (main-loop owned, queued): (a) wire the new _descriptorRefines_sat + the capOpenSat rungs into the apex
HORIZONLOG.md:4840:descriptor regen for the new/changed descriptors (introduceWriteV3/CapOpen wrappers/heapWriteV3 — widths recorded);
HORIZONLOG.md:4853:FOLLOW-UPS (named, VK-free-driveable): (a) SetProgram's OWN circuit descriptor witness (reuses
HORIZONLOG.md:4854:EFFECT_SET_VERIFICATION_KEY's tag today, executor-sound; the descriptor rung is the VK follow-up); (b) wire the
HORIZONLOG.md:4860:After the soundness waves: (1) wire the new _descriptorRefines_sat + capOpenSat rungs (receiptArchive, heapWrite,
HORIZONLOG.md:4861:the 5 cap slots) into the apex fanout ClosureFanoutGenuine (13 wired, ~7-9 to add); (2) the JSON descriptor regen
HORIZONLOG.md:4862:for the new/changed descriptors (introduceWriteV3/CapOpen wrappers/heapWriteV3) + drift re-pin; (3) compact
HORIZONLOG.md:4865:## ⚑ JSON-EMIT FOLLOW-UP (2026-06-20) — the new apex descriptors aren't in emit_descriptors.py's list yet
HORIZONLOG.md:4867:revokeDelegationWriteCapOpenV3) + heapWriteV3 — the apex now PROVES about them. But scripts/emit_descriptors.py
HORIZONLOG.md:4868:emits from a FIXED descriptor-name list that does NOT include them (verified: grep -c WriteCapOpen|heapWrite in
HORIZONLOG.md:4869:emit_descriptors.py = 0), so the checked-in deployed JSON doesn't yet carry these descriptors (drift gate PASSES
HORIZONLOG.md:4873:edit): add the new descriptor names to the emitter so the deployed JSON carries exactly what the apex proves about,
HORIZONLOG.md:4876:## ⚑⚑⚑ AUTHORITY FLOOR — LAST MILE, the light-client forge CLOSED via the verifier tooth (2026-06-20, base 99cf43412, UNCOMMITTED)
HORIZONLOG.md:4879:under its PLAIN cohort descriptor. New `is_forbidden_plain_cap_descriptor` forbids the 5 plain cap-effect
HORIZONLOG.md:4880:descriptors (introduce/revoke/attenuate/grantCap/revokeCapability VmDescriptor2R24) as the uniquely-accepting
HORIZONLOG.md:4881:descriptor — a cap effect MUST bind a `…CapOpen…VmDescriptor2R24` (the depth-16 capOpenConstraintsEff membership
HORIZONLOG.md:4882:crown is IN that descriptor and ONLY there). So a malicious producer that strips the cap-open route to launder
HORIZONLOG.md:4884:- WHY the verifier tooth (not a blind producer resolver re-point): the deployed wire shares NO single resolver
HORIZONLOG.md:4885:  the way the verdict assumed. (1) The SDK light-client verifier iterates ALL cohort descriptors and binds the
HORIZONLOG.md:4886:  unique acceptor (it does NOT call `rotated_descriptor_name`) — so the FORCING had to be a forbidden-name tooth
HORIZONLOG.md:4890:  full_turn_proof.rs:1096/1687) — the verifier tooth makes that route MANDATORY (a producer can't get a cap
HORIZONLOG.md:4892:- NEW forge-rejection test `light_client_rejects_cap_effect_under_plain_descriptor`: proves a RevokeDelegation
HORIZONLOG.md:4895:  tooth: plain cap-effect ⇒ reject, cap-open ⇒ accept.
HORIZONLOG.md:4896:- NO VK/descriptor drift (verifier-behavior change only; no .tsv/.json touched — the cap-open descriptors forced
HORIZONLOG.md:4899:- RESIDUE (named, NOT in scope of this fix): (a) refreshDelegation stays on its plain descriptor — its deleg-tree
HORIZONLOG.md:4901:  authority — named, not a silent forge). (b) The …WriteCapOpen descriptors (introduceWrite/delegateWrite/
HORIZONLOG.md:4904:  (already wired). The write-op binding into the commitment (the ~17-effect descriptor-fix terrain in
HORIZONLOG.md:4914:- LIGHT-CLIENT GAP: the deployed producer selects the PLAIN cohort descriptors for cap effects
HORIZONLOG.md:4920:  from "host asserted it" — a malicious producer proves the cap effect via the non-cap path -> plain descriptor ->
