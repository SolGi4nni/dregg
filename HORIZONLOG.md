# HORIZONLOG — the named-follow-up burn-down

*(Standing rule: when a lane/commit NAMES a follow-up, residue, or closure lane,
it gets a line HERE in the same breath — "named in a report" is not durable.
Each line: what · where it was named · the closure shape. Remove lines when
closed (git history is the record). This is a burn-down list, not a parking
lot: per WE-DO-NOT-NAME-WE-SHIP, anything that sits here across many sessions
should be either scheduled or explicitly demoted to the Research tier with a
reason.)*

Last sweep: 2026-06-13 (flagged-items burndown — removed ~14 landed/struck items,
deduped the DreggDL/sel4/snapshot landings into git history, kept live tails).

## CIRCUIT-SOUNDNESS APEX — light-client unfoolability: faithful core LANDED, per-effect terrain MAPPED (2026-06-16)

The map + state lives in `docs/CIRCUIT-FUNCTIONAL-CORRECTNESS.md` (the obligation table is the resumable plan).

LANDED (green, #assert_axioms-clean): the parametric apex `lightclient_unfoolable` (CircuitSoundness.lean,
derives ∃ kernel transition; carries StarkSound + Poseidon2SpongeCR + hrefines + WitnessDecodes); the FAITHFUL
authority leg (two-axis `authorizedFacetB`) single-step (`RotatedKernelRefinementFacet.lean`,
`transfer_descriptorRefines_facet` — authority FORCED in-circuit by the cap-open) and WHOLE-TURN
(`RotatedKernelForestFacet.lean`, `lightclient_turn_unfoolable_forest_facet` + generic fold
`turnDecodeChain_refines_turnSpec_gen`); and 5/36 VALUE rungs (`descriptorRefines`): transfer, burn, mint,
bridgeMint, setField — `RotatedKernelRefinement{,MintBurn,SetField}.lean`, each gate-forcing the designated
moved column with both-polarity forgery teeth.

UPDATE (later same session) — EVERY effect's VALUE rung is now PROVEN. The ~17 VALUE_MISSING fixes were
built (the principled-fix committed-root-limb pattern: cellSeal/cellUnseal/cellDestroy/refusal/receipt
Archive/setPerms/setVK/makeSovereign/setFieldDyn/createCell/factory/noteCreate), and the PHASE-D gadget
LANDED (`SortedTreeNonMembership.lean` non-membership + `CapTreeUpdate.lean` insert/update/remove on the
proven `DeployedCapOpen` membership): **noteSpend's double-spend non-membership is FORCED in-circuit** and
the **capability family's exact sorted-set move is forced** (attenuate upgraded non-amp→set-exact, the
ARGUS crown #103). The remaining boundary to literal closed-closed:
  1. THE RUNTIME COMMITMENT REALIZATION (the one ember-gated VK epoch): `circuit/src/effect_vm/cell_state.rs
     ::compute_commitment` must absorb the new committed root limbs (per-cell side-table/audit roots + the
     sorted cap/nullifier/commitment roots) + the trace-fills emit them. ONE coordinated change realizes the
     whole fix+phase-D family; changes the VK ⇒ ships as a VK epoch + registry re-pin.
  2. The Lean registry cutover (swap fix descriptors into v3Registry so `R e` = the proven descriptor) +
     the COMPOSITION (assemble the per-effect rungs into `∀ e, descriptorRefines (R e)` ⇒ discharge the
     apex's carried `hrefines`).
  3. The faithful-encoding carriers (cap-tree↔Caps, nullifier-tree↔set, SpineCommits) — realizable
     hypotheses (the deployed Merkle fold), the Poseidon2SpongeCR floor class. + WitnessDecodes per effect +
     the prover wiring (`&[]` cap path-witness, `sdk/src/full_turn_proof.rs:662`).
  Full map: `docs/CIRCUIT-FUNCTIONAL-CORRECTNESS.md` §"Final state". `heapWrite` (no live registry entry,
  proven fix off-apex) and `custom` (no kernel arm, out of scope) noted.
  2. ~5 VALUE_PARTIAL (attenuate base-root-supplied-not-recomputed; setFieldDyn; incrementNonce generic-tick;
     makeSovereign rebind; pipelinedSend nonce-tick-vs-freeze) — bounded extra binding.
  3. Wire each effect's faithful arm into `fullActionStepFacet`; retire the forest `hidx0 : e=0` residual.
  4. Discharge `WitnessDecodes` per effect; connect `TransferAuthoritySource`; kill the `&[]` cap path-witness
     at `sdk/src/full_turn_proof.rs:662`. Then the VK epoch (ember-gated).
  Crypto floors that legitimately remain: `StarkSound`, Poseidon2/permutation CR.

## IN-CIRCUIT CAP-TREE MEMBERSHIP-OPEN — Lean soundness LANDED; Rust AIR wiring + prover + mask-reconcile NAMED (2026-06-16)

LANDED (green, #assert_axioms-clean, Poseidon2SpongeCR only): `metatheory/Dregg2/Circuit/DeployedCapOpen.lean`
— the in-circuit cap-tree membership-open as a `CapOpenConstraint` whose denotation rides the Poseidon2 chip bus
(`DescriptorIR2.chip_lookup_sound`) for the 7-field leaf absorb (= `capLeafDigest`) and each depth-16 `hash_fact`
node fold (= `nodeOf`, mixed by the direction bit), CONSTRAINS the top == `cap_root` column, binds `leaf.target ==
src` + `mask_lo == write-mask`. KEYSTONE `capOpen_sound`: `Satisfied ⟹ DeployedCapTree.MembersAt cap_root leaf ∧
leaf.target = src ∧ confersWriteLeaf leaf`; `capOpen_authorizes` chains `deployedCapOpen_implies_authorizedB ⟹`
kernel `authorizedB`. Discriminating teeth witness-FALSE (writeMaskGate/targetBindGate). Rust witness twin +
recompose + binding + tests landed in `circuit/src/cap_root.rs` (`CapMembershipWitness`, `recompose_membership`,
`membership_witness`, `recomposes`/`target_is`/`confers_write`; tests pin the depth-16 fold == root + forgery
rejection + binding teeth).

NAMED (remaining-steps, the Rust-AIR + prover legs of the original 4):
LANDED (2026-06-16, the LIVE emission + bridge + Rust appendix — no hand-authored Rust constraints, LAW#1):
  `metatheory/Dregg2/Circuit/Emit/CapOpenEmit.lean` lays `DeployedCapOpen`'s PROVEN constraints (leafLookup + 16
  nodeLookups + 16 dir-bool + rootPin/targetBind/writeMask) over a concrete `capOpenCols` appendix (58 cols past
  the rotated R=24 width 311) into `capOpenAttenuateV3` (width 369), with the bridge `capOpenAttenuateV3_satisfied`
  (a live `Satisfied2` REBUILDS `DeployedCapOpen.Satisfied`) ⟹ `capOpenAttenuateV3_sound` (MembersAt cap_root leaf
  ∧ target=src ∧ confersWriteLeaf) ⟹ `capOpenAttenuateV3_authorizes` (kernel `authorizedB`). `#assert_axioms`-clean,
  full `Dregg2` build green. Rust twin: `attenuateCapOpenVmDescriptor2R24` registry member (byte-identical
  `emitVmJson2`), `CapOpenWitness`/`fill_cap_open`/`generate_cap_open_attenuate_trace` in `trace_rotated.rs`
  (genuine absorb-node `hash_many` fills, proven by `cap_open_witness_and_appendix_are_genuine`), V3_STAGED FP
  bumped to `2d4a594b1deec12c111b1f965786f7c4550cabb4f71c6b50ffe2eb894fc2c5db`; the 311-wide attenuate base proves
  standalone. writeMaskGate emitted FAITHFULLY (mask_lo==3, the abstract rights mask — NOT faked to the deployed
  EffectMask, see (3)).

NAMED (the ONE thing blocking the end-to-end prove — `cap_open_attenuate_self_verifies` is `#[ignore]`d, not faked):
  (1) CHIP-ARITY RE-EMIT (Lean, proof-carrying): `DeployedCapOpen` declares chip lookups at arity 7 (leaf) and
      arity 3 (each node), assuming `CHIP_RATE = 8`. The DEPLOYED IR-v2 chip (`descriptor_ir2.rs` ~1841-1873) is
      rate-4 and enforces `arity ∈ {0,2,4}` — so arity-7 AND arity-3 absorbs are BOTH unrealizable as a single chip
      row (and the deployed `cap_root.rs::CapLeaf::digest` 7-field `hash_many` is itself a TWO-permute sponge).
      Re-emit `capLeafDigest`/`nodeOf`'s chip realization as an explicit fold of arity-2/arity-4 absorbs (sponge
      state threaded across rows), kept byte-identical to the deployed digest, and RE-PROVE the soundness lemmas
      (`leafDigest_sound`/`node_sound` upward). LEAN file change (NOT a Rust constraint edit); once it lands the Rust
      `fill_cap_open` mirrors the new fold and `cap_open_attenuate_self_verifies` un-ignores. (Alternative worth
      weighing: ride the `BUS_FACT` fact rows for nodes — the deployed cap-tree's real `hash_fact` shape — instead
      of absorb rows, which also re-binds the open to the DEPLOYED `CanonicalCapTree` root rather than the
      absorb-node tree the current emission commits.)
  (2) PROVER wire: `sdk/src/full_turn_proof.rs:662` — once (1) lands, route cap turns through the cap-open
      descriptor + witness (kill the `&[]`); note the new VK pin (VK changes — authorized).
  (3) MASK-CONVENTION RECONCILE (flag-day, ember decision): the Lean `confersWriteLeaf`/`writeMaskGate` pin
      `mask_lo == rightsMaskOf(endpoint[read,write]) = 3` over the abstract `Auth`-rights mask; the deployed
      `CapLeaf.mask_lo` is the low-16 of a `cell/facet.rs` `EffectMask` (effect-kind bitmap — DIFFERENT convention:
      EFFECT_TRANSFER=1<<1, EFFECT_GRANT_CAPABILITY=1<<2…). Align so the in-circuit write bit IS the deployed
      `mask_lo`'s write-conferring bit (or document the leaf carries the rights mask, not the effect mask).
      `cap_root.rs::confers_write` checks the submask SHAPE either convention shares; the constant alignment is the
      open item — do NOT fake a Rust constant that pretends they agree. (The membership + target-bind legs the
      LANDED work lands are convention-INDEPENDENT, so this only gates the write-rights leg.)

CLOSURE SHAPE: (1) is a proof-carrying Lean re-emit (the chip-arity floor the original emission missed); (2) a
witness pass once (1) lands; (3) an ember-adjacent data-model decision (which mask the cap leaf commits). Named:
in-circuit cap-membership-open, 2026-06-16.

## CIRCUIT FUNCTIONAL CORRECTNESS — light-client unfoolability apex NAMED; #103 cap-family residue mapped (2026-06-16)

NAMED: the leaf-circuit→kernel-step soundness rung does not yet exist as a composed apex over the live
rotated registry — `lightclient_unfoolable` (`verifyBatch vk pi π = accept ⟺ ∃ kernel transition`,
bidirectional per LAW#1) via `descriptorRefines (liveRegistry e) (fullActionStep e)` per live effect. Full
diagnosis + corrected ground-truth coverage in `docs/CIRCUIT-FUNCTIONAL-CORRECTNESS.md` (SUPERSEDES the
pre-investigation plan whose premise — "the live circuit enforces no non-amp" — is FALSE: `attenuateV3_non_amp`
(EffectVmEmitRotationV3.lean:1419) proves in-circuit non-amp on the LIVE wired attenuate descriptor).

RESIDUE (= the open scope of #103; attenuate = the done template #37): introduce / refresh / revokeDelegation /
grant route to FREEZE-AND-DEFER rotated descriptors (`v3Of {introduce,refresh,revoke}VmDescriptor` — cap_root
frozen, mutation bound out-of-row / DELEG record-root), so a light client trusts the EXECUTOR for their non-amp
(`EffectsAuthority.*_non_amplifying`, proven; Argus-term-IR modelled — neither is the descriptor the prover
selects). `introduceVmDescriptorGenuineNonAmp`/`refreshVmDescriptorGenuineNonAmp` (= the 186-wide
`attenuateVmDescriptorGenuineNonAmp`) are PROVEN-BUT-UNWIRED — the drift the apex's `vk=vkOfRegistry liveRegistry`
binding + a drift-guard `#guard` must forbid. Two universal rungs DO hold for all 36 (`rotV3_sound_v1` row-intent,
`rotV3_binds_published` whole-post-state commitment) — integrity complete, authority uneven.

CLOSURE SHAPE: (1) named `StarkSound` floor over the audited p3-batch-stark verifier (none exists — implicit in
`RecursiveAggregation.EngineSound`); (2) state `lightclient_unfoolable` + `descriptorRefines`, discharge per-effect
vs `fullActionStep` (ActionDispatch.lean:168; `attenuateV3_non_amp` = worked instance); (3) BUILD the four missing
in-row gadgets — NOT a transport (no V2 sibling source): introduce/grant = membership + cross-cell copy, refresh =
DELEG-root open+submask, revokeDelegation = removal gate (the `revokeCapabilityV3` shape); (4) drift-guard `#guard`
(every `*_non_amp` descriptor ∈ liveRegistry) + wire-or-delete the standalone Genuine descriptors; (5) VK epoch
(ember-gated). TO CONFIRM: delegateAtten wire→selector mapping (if it rides ATTENUATE_CAPABILITY=48 the headline
delegation is already covered); what `unfoolability_guarantee` grounds "executed correctly" on; `fullActionStep ⟺
execFullA`; Argus IR live-vs-parallel. Named: circuit functional correctness apex, 2026-06-16.

## DFA ROUTE-COMMITMENT — LANDED in the circuit + live verifier; node-relay binding NAMED (2026-06-15)

LANDED: the real `dregg-dfa-routing-v1` route-commitment-binding AIR now SHIPS as a DSL circuit
(`circuit/src/dsl/dfa_routing.rs`), faithful to the Lean model `Dregg2.Crypto.DfaAcceptanceAir` and the
standalone test AIR (`dregg-tests/src/dfa_circuit.rs`). It closes GAP-B (the running-hash route commitment
the generic `Lookup` DFA left open) via two new `ConstraintExpr` forms in `circuit/src/dsl/circuit.rs` —
`ChainedHash2to1` (cross-row `next.running = compress(this.running, next.entry)`, the C3 chain) and
`SeedHash2to1` (PI-seeded `running₀ = compress(table_commitment, entry₀)`, the Lean `seed` conjunct) —
plus a FRI-safe `TableFunction` (bivariate-Lagrange table membership, closing GAP-A `next = step(state,sym)`
where `Lookup` could NOT — `Lookup` is a non-polynomial step the native FRI rejects off-domain; this was a
real pre-existing trap: no DSL `Lookup` circuit ever proved through `stark::prove`). Both polarities GREEN
through the real `stark::prove`/`verify` FRI pipeline (8 tests, `cargo test -p dregg-circuit --lib
dsl::dfa_routing`) AND through the LIVE `DslCircuitDfaVerifier` — the relay's verifier (4 tests,
`executor::membership_verifier::tests::live_routing*` in `dregg-turn`): a correct route binds its
route_commitment/final_state; a forged final_state or route_commitment is rejected at the B2/B3 boundary
("a router cannot claim a delivery it did not make").

NAMED (node-relay binding — the remaining live wire): the relay-operator template
(`dregg-storage-templates/src/relay_operator.rs`) gates the `relay` method on `Witnessed { Dfa }` with a
PLACEHOLDER commitment `[0u8;32]` (a labeled seam — the comment says "executor overrides via slot-bound
resolution" but `cell/src/program.rs:3549` passes `wp.commitment` AS-IS), and `node`'s relay sets
`route_table_root = blake3_field(…)` (`node/src/relay_service.rs:1228`), neither equal to the routing
program's `vk_hash` — so the relay's Dfa caveat is currently FAIL-CLOSED at the node (the node never
installs the Dfa verifier). NOTE the "blocker" is a NON-issue: `dregg_dsl_runtime::ProgramRegistry`
(`node/src/state.rs:249`) is a `pub use` RE-EXPORT of `dregg_circuit::dsl::circuit::ProgramRegistry`
(`dregg-dsl-runtime/src/lib.rs:58`) — the SAME type `DslCircuitDfaVerifier` holds. CLOSURE SHAPE (two
edits, both in already-depended crates): (1) `dregg-storage-templates` — thread a `route_circuit_vk:
[u8;32]` param into `relay_operator_program_with` so the `WitnessedPredicate::dfa` commitment is the
routing `vk_hash`, not `[0u8;32]` (ripples to `relay_operator_program()` + the node/test callers); (2)
`node` — at startup deploy `dregg_circuit::dsl::dfa_routing::dfa_routing_descriptor("dregg-dfa-routing-v1",
router_transitions)` into `s.program_registry`, set `default_route_table_root()` := that `vk_hash`, and in
`node/src/executor_setup.rs::configure_turn_executor` do
`registry.register_builtin(Arc::new(dregg_turn::executor::DslCircuitDfaVerifier::new(Arc::new(
s.program_registry.clone()))))` (upgrades ONLY Dfa from its fail-closed default; the other kinds stay as
`registry_with_real_verifiers()` set them). The relay CLIENT produces wire bytes via
`dregg_turn::executor::prove_dfa_transition(programs, vk_hash, build_routing_witness(...).0, n, pi)`.
Both `DslCircuitDfaVerifier` + `prove_dfa_transition` are now re-exported from
`dregg_turn::executor`. Named: DFA route-commitment node-relay wire, 2026-06-15.

LAW#1 RESIDUAL (Lean-emit): `dfa_routing_descriptor` is a Rust-authored `CircuitDescriptor` faithful to
the authoritative Lean `Satisfies` (`metatheory/Dregg2/Crypto/DfaAcceptanceAir.lean` §2) — it follows the
SAME established pattern as every other DSL predicate circuit (`fold`, `committed_threshold`, `temporal`),
none of which is Lean-emitted (the `CircuitEmit.lean → EmittedDescriptor` path serves the KERNEL effects,
not the DSL predicate-circuit family). The new `ConstraintExpr` forms are generic data-driven gates, not a
bespoke hand-coded AIR. The law-#1 ideal end-state is a Lean emitter that PRODUCES this descriptor from the
`Satisfies` model with an emitted≡Satisfies proof (and the entry-hash/running-hash carriers consumed as
named CR, exactly as the Lean model does). Named: Lean-emit the dfa-routing descriptor + the DSL-predicate
family, 2026-06-15.

## CAP-CROWN IR — LANDED: in-circuit non-amplification (`granted ⊑ held`) binds on the DELEGATION family at the Lean-emit layer (2026-06-15)

The delegation/cap effects (`delegate`, `delegateAtten`, `attenuate`, `introduce`, `revoke`, `refresh`)
carried an "IR GAP — needs IR extension: cap-root hash-site" in their EffectVM-emit modules: the genuine
`cap_root` RECOMPUTE existed (§G, `attenuateVmDescriptorGenuine` — `new_cap_root = hash[edge_leaf,
old_root]`, op-tagged) but the in-circuit non-amplification (`granted ⊑ held`) did NOT bind on these
descriptors. CLOSED: a new shared GENUINE-NON-AMP descriptor `attenuateVmDescriptorGenuineNonAmp`
(`metatheory/Dregg2/Circuit/Emit/EffectVmEmitAttenuateA.lean` §G.4) = the genuine recompute PLUS the
shared `EffectVmEmitCapReshape.capDelegNonAmpGates` (the per-bit submask gate whose GRANTED mask
reconstructs `cp.RIGHTS` — the SAME `rights` felt the recompute hashes into the cap-edge leaf). The two
legs INTERLOCK on one felt: tamper `rights` to dodge the submask gate and the recomputed `cap_root` moves
⇒ `state_commit` moves ⇒ UNSAT. Re-exported per effect (`delegateVmDescriptorGenuineNonAmp` …, with
`*NonAmp_in_circuit` admits + `*NonAmp_rejects_amplify` rejects — both polarities, axiom-clean). Emitted
from Lean (LAW#1, no hand-authored AIR): `EmitAllJson` re-emits the byte-pinned
`circuit/descriptors/dregg-effectvm-attenuateA-v1-genuine-nonamp.json` (186-wide, 56 constraints, 6 hash
sites — additive + width-neutral); the Rust standalone loader `circuit/src/cap_delegation_nonamp_descriptor.rs`
parses it + fingerprints it (drift guard) + asserts the 8 delegation submask gates + the 2 recompute
sites are present. `lake build Dregg2` green; the EmitAllJson run + the loader teeth are the gates.

RESIDUAL (named, Phase E): the in-row recompute is the prepend-accumulator DIGEST advance, not yet the
in-row sorted-TREE update (membership-open + sorted-key range-checks, mirroring the revocation circuit's
C6/C7/C10/C11). The openable-root VALUE the digest carries is the cell≡circuit sorted-Poseidon2 root
(`EffectVmEmitCapReshape` §1 model + `circuit/tests/cap_root_cell_circuit_differential.rs`); the Phase-B
sorted OPEN is `EffectVmEmitV2.attenuateV2_non_amp`. This IR-layer non-amp is the descriptor-emit
counterpart of the p3-AIR Phase-B gates tracked at the "#103 cap-crown — TWO EffectVM AIRs" item below;
it does NOT itself graduate the bespoke sovereign `EffectVmAir` path (that remains the C5/C7-flip task).
Named: cap-crown IR non-amp LANDED, 2026-06-15.

## FIRMAMENT KEYSTONE — LANDED: the 5-PD assembly BOOTS the verified turn through the REAL executor seat (2026-06-15)

The `executor` seat of the 5-PD firmament (`sel4/dregg.system`) is a REAL Microkit PD
(`sel4/dregg-pd/executor-microkit-pd/`) embedding the verified `dregg_exec_full_forest_auth`
(= `execFullForestG` + admission, proved in `metatheory/`) + the ELF Lean runtime + real GMP + the real
crypto floor + the seL4 musl, and **the WHOLE 5-PD Microkit image now BOOTS in qemu-system-aarch64 with
that verified turn running `status:2 ok:1`** — ZERO faults across all five PDs. `make -C sel4
run-assembly-real` reproduces it end-to-end; verbatim serial in
`executor-microkit-pd/microkit-patch/assembly-boot-evidence.log`. The executor inits the embedded Lean
runtime, runs the verified turn (nonce 7→8, 30-unit transfer cell-0 100→70 / cell-1 5→35, nullifier 111
+ commitment 222), writes the 313-byte receipt to `commit_out` (RW), signals persist (ch2) + verifier
(ch3); persist reads the receipt back (`commit_out[0]='{'`) + gets commit-ready; verifier-stark proves
+verifies a real STARK; net brings virtio-net UP; the rbg app runs. The cap partition is enforced LIVE:
the executor holds `turn_in` READ-ONLY (a boot write to it faults — that was the last wall, fixed by
running the boot self-demo from the compiled-in wire, writing only `commit_out`).

THE WALL THAT FELL (the prior `-ffunction-sections` / "285-MiB text irreducible" diagnosis was the WRONG
lever — the text size was never the blocker): the on-device CapDL initialiser panicked **`OutOfSlots`**
because the **microkit TOOL hard-codes 4 KiB pages for every PD program-image segment**
(`tool/microkit/src/capdl/builder.rs`: `let page_size = PageSize::Small;`), so the ~300-MiB executor image
became ~83,000 frame caps and blew `ROOT_CNODE_SIZE_BITS`. FIX (the right, general one — a no-op for
small PDs): a one-function tool patch maps image segments with 2 MiB `PageSize::Large` where alignment
permits (the PD already links `-z max-page-size=0x200000`, so its segments are 2 MiB-aligned) → ~170 Large
frames + small tails, **2,322 total objects, 91 MiB initial task** (was 84,241 objects / ~340 MiB). The
patch + prebuilt tool + boot evidence are in `executor-microkit-pd/microkit-patch/` (built against the
microkit **2.2.0 tag** — `seL4/rust-sel4 cf43f5d` — to match the SDK's bundled `initialiser.elf`; a
`2.2.0-dev`-commit build pins `au-ts/rust-sel4 33cb1325`, an incompatible rkyv spec schema the SDK
initialiser can't read). The patch is upstreamable (map image segments with the largest aligned page).
INSTALL: `cp executor-microkit-pd/microkit-patch/microkit-2.2.0-patched $MICROKIT_SDK/bin/microkit`.

Residual (small, not blocking the keystone): the embedded turn is the demo `wideDemoInput`, not yet a
net-delivered live turn (the live `notified`-path read of `turn_in` is wired + correct, just unfed in
QEMU since net only brings the NIC up here — a real ingress→turn_in→executor delivery is the next strand).
Named: firmament keystone LANDED, 2026-06-15.

## DESKTOP KEYSTONE — CLOSED: the LIVE `cockpit::Cockpit` element tree renders on the seL4 framebuffer (TAB beside the live image, 2026-06-15)

THE #1 PRECIOUS is fully done, including its last swap: the deos-image PD (`sel4/dregg-pd/deos-image/`)
has TWO live modes on one ramfb framebuffer, switched with **TAB** — `Mode::Image` (the Pharo cell
browser) and `Mode::Cockpit` — and the cockpit is now the **REAL, LIVE `starbridge_v2::cockpit::Cockpit`
element tree** (not a hand-built look-alike): the CELL WORLD rail with the actual sovereign cells (ids,
balances, cap counts, the issuer well at −supply), the INSPECTOR reflecting the image (cells/height/
receipts/`state_root`/"executor embedded verified (TurnExecutor)"), the BLOCKLACE provenance (the real
receipt chain), and the HOME/SHELL/AGENT workspace. Rendered at 800×600 by the actual gpui renderer
(`gpui_wgpu::WgpuRenderer::render_scene_to_image`, the offscreen patch) on lavapipe (`type=Cpu`, no GPU/
window) on persvati, baked into the `#![no_std]` PD as raw RGBA8 (`src/cockpit_frame.rgba`, 1.92 MiB)
and swizzled RGBA→XRGB8888 at blit time. `make -C sel4 capture-image-modes` reproduces it end-to-end
(boots headless, screendumps image, QMP `send-key TAB`, screendumps the LIVE cockpit). Evidence:
`docs/desktop-os-research/patches/cockpit-on-sel4-framebuffer-LIVE.png` (the live cockpit scanned out
of seL4 ramfb) + `cockpit-render-800x600-LIVE.png` (the persvati render).

THE LAST SWAP — CLOSED (was "the one remaining swap"): the blitted Scene used to be a hand-built
cockpit-*shaped* `gpui::Scene`; it is now the live element tree, resolved the intended way. HOW: a
headless gpui `App`/`Window` (`gpui::HeadlessAppContext` over `TestPlatform`) drives the real
`cockpit::Cockpit` over the fully-seeded `world::demo_world` image; gpui paints its element tree into a
real frame; `Window::render_to_image` captures the resolved `gpui::Scene` through the offscreen wgpu
renderer. Entry: `starbridge-v2/src/main.rs::render_cockpit_headless` (`--render-cockpit <out>`, behind
a new `headless-render` feature). gpui reports a fixed 2× scale, so the 800-logical cockpit renders at
1600×1200 device px and is Lanczos-downscaled to 800×600 (full layout, no crop). Byte-proof: the new
`cockpit_frame.rgba` differs from the old hand-built bake in 1,376,735 / 1,920,000 bytes (a genuinely
different image, same geometry). The offscreen patch GREW the missing Linux headless renderer:
`gpui_wgpu::{WgpuRenderer::render_scene, WgpuHeadlessRenderer: PlatformHeadlessRenderer}` +
`gpui_linux::current_headless_renderer` + `gpui_platform::current_headless_renderer` routing to it on
Linux (the Metal headless renderer is the macOS counterpart). DEP REPOINT (committable, done): the
patch is pushed as `emberian/zed@dregg-offscreen` (off `fca2ccd`, rev
`407a6ffd977d82b828e392f92db5cb34edea9549`); starbridge-v2's `gpui`/`gpui_platform` git deps now point
there + a new `gpui_wgpu` dep at the same rev (the canonical patch
`docs/desktop-os-research/patches/gpui-offscreen.patch` carries the full offscreen+headless diff).
Fonts vendored OFL (`starbridge-v2/assets/fonts/{Lilex,IBMPlexSans}-Regular.ttf`). Named: desktop
keystone CLOSED — the live element tree is on glass, 2026-06-15.

## EVM BRIDGE — the STARK→SNARK wrap keystone: zkVM path BUILT, Plonky3-native BN254 terminal is the cost-optimization endgame (named 2026-06-15)

The EVM-bridge architecture + a running PoC landed (`docs/EVM-BRIDGE.md`, `/tmp/dregg-evm-e2e/`,
`/tmp/dregg-evm-wrap-poc/`, plus the green calldata codec in `bridge/src/ethereum.rs`). The keystone is
the wrap: dregg proves with Plonky3/BabyBear/FRI (post-quantum but gas-prohibitive on EVM), so dregg's
aggregate is recompressed into a BN254 Groth16 a ~270k-gas Solidity verifier checks. THREE rungs
(`docs/EVM-BRIDGE.md` §2.4): (B) **re-host dregg's own verifier in a RISC0 zkVM, settle their audited
Groth16** — VALIDATED this session: the full production `dregg-circuit --features verifier`
(`verify_vm_descriptor2`, the IR-v2 **Poseidon2** batch STARK + all of Plonky3) cross-compiles to
`riscv32im-risc0-zkvm-elf` via `embed_methods` (auto getrandom-custom + lower-atomic); the real
`RiscZeroGroth16Verifier` + `DreggBridgeVault.sol` compile under foundry, control IDs version-matched.
(A) bespoke gnark Poseidon2-FRI verifier circuit (cheaper to prove, new audit surface). (C) the endgame.

CLOSURE LANES: (1) finish the (B) loop — host generates the IR-v2 proof (`prove_vm_descriptor2`), zkVM
wraps to Groth16, `forge script DriveBridge` verifies on anvil + drives attest/lock/unlock/intent (the
plumbing is built; the Poseidon2 guest+host compile on persvati; run the wrap on a 24-core box). (2) swap
the guest's leaf-proof verify for the full `WholeChainProof` root (`verify_history`) — one-line, heavier.
(3) **THE COST ENDGAME — a Plonky3-native BN254 terminal** (§4.2/§2.4-C): make dregg's own recursion
(`emberian/plonky3-recursion`, the `WholeChainProof` fold) terminate in a BN254 Groth16 proof instead of
another BabyBear STARK — no RISC-V overhead, no separate FRI-verifier circuit. **STEP 1 BUILT + GREEN
(2026-06-15, `/Users/ember/dev/plonky3-bn254-wrap`, commit `e80f499`):** `OuterStarkConfig` — a Plonky3
`StarkConfig` whose FRI commitments + Fiat-Shamir transcript live in the BN254 scalar field
(Poseidon2-BN254 width-3 Merkle + `MultiField32Challenger`), from raw Plonky3 primitives pinned to dregg's
exact rev (82cfad73). A BabyBear AIR proves AND verifies through it (4 tests green — re-verified
`cargo test --release` 2026-06-15 — incl. the production HorizenLabs `RC3` constants
`production_constants_load_from_zkhash` + the `outer_config_carries_dregg_four_publics` interface tooth).
Keystone: `src/hasher.rs::MultiFieldPoseidon2Hasher`, the cross-field leaf
hasher (absorb BabyBear→pack into BN254→squeeze one Bn254 digest) that upstream Plonky3 does NOT ship and
SP1 carries by hand. KEY FINDING de-risked: `p3-bn254` (Poseidon2Bn254 + HorizenLabs params) AND
`MultiField32Challenger` (the transition primitive, `GrindingChallenger Witness=BabyBear`) ALREADY EXIST
in dregg's pinned upstream Plonky3 — the "no plonkish SNARK wrapper" gap is narrower than feared.
REMAINING (the two sharp edges, in that repo's README): **Step 2** — emit `OuterStarkConfig` from the
recursion fork's terminal layer (its Poseidon2 op-table + FRI private-data are BabyBear-w16-wired; the
smaller lift is a thin re-prove of the last BabyBear STARK under the outer config, mirroring SP1's
separate "shrink" layer). **Step 3** — the gnark Groth16 circuit (`/Users/ember/dev/dregg-gnark-wrap`,
sibling lane started this session) verifying an `OuterStarkConfig` proof with NATIVE BN254 Poseidon2 (no
nonnative hash emulation; the audit obligation is bit-for-bit constant/packing/FRI-param parity across the
Rust/Go seam). SHIP (B), BUILD (C). KEY FINDING (B): do NOT wrap the experimental `circuit/src/stark.rs`
(BLAKE3 Merkle, no zkVM accelerator — the
guest ran >200 CPU-min unfinished); use the production Poseidon2 path (field-native, ~10x lighter in
zkVM). Named: EVM bridge, 2026-06-15.

## PERFORMANCE PILLAR — LANDED: comprehensive criterion coverage of every hot path + measured numbers (2026-06-15)

The `dregg-perf` crate now covers comprehensive swathes of the system under BOTH proving and
witness-only loads, all measured (Apple M2 Max, bench profile). Five coverage gaps CLOSED with real,
runnable criterion benches (each drives the production PUBLIC API; numbers banked in
`docs/PERFORMANCE.md`, recipe in `docs/PERF.md`):
- (a) `turn_witness_vs_proving` — THE headline contrast, all four legs of one turn side by side:
  witness-only executor execute **~7 µs** · witness-gen **~319 µs** · full rotated prove **~147 ms** ·
  rotated verify **~149 ms**. **The proving multiplier ≈ 21,000×** — the empirical case for
  admit-then-prove-async.
- (b) `cohort_circuit` — the rotated IR-v2 multi-table batch STARK prove+verify per effect cohort:
  transfer-5table 52 ms/3.9 ms; and the UNIVERSAL-MEMORY economics MEASURED — a chip-bearing map-write
  proves **~227 ms** vs the same intent as no-chip umem ops **~14.9 ms** (~15× — the Blum multiset
  commits no Poseidon2 chip table).
- (c) `recursion_fold` — the bundle-tree aggregation fold: prove scales sub-linearly (10→14→36→98 ms for
  2→8→32→128 leaves) but **verify is ~CONSTANT ~2.4 ms regardless of fan-out** (the succinct-aggregation
  property, measured).
- (d) `embedded_commit` — the verified Lean kernel commit (`shadow_exec_full_forest_auth`, the node /
  seL4-executor-PD hot path) over the GOLDEN firmament-boot turn: **~157 µs** (microseconds, same order
  as the Rust executor — verified-and-cheap admit).
- (e) `ui_projection` — the deos desktop whole-system measure (gpui-free; the real GPU first-paint is on
  persvati): per-frame scene/affordance projection is **nanoseconds** (compose_scene 102 ns, paint_list
  472 ns, affordance_project 96 ns — never the bottleneck); the first-paint DATA cost is the five embedded
  commits (`demo_world_seed` ~5.8 s) — which is why the cockpit opens on the instant-genesis image and
  seeds turns async.

The full perf crate is clippy-clean; `cargo bench -p dregg-perf --no-run` green. SMOKE is default; FULL
(`PERF_FULL=1`) is the persvati ladder capture (the fold + cohort FULL ladders already captured + in the
doc). Named: performance pillar LANDED, 2026-06-15.

## ⚑ TWO PERF FINDINGS surfaced by the harness (closure lanes, named 2026-06-15)

1. **`prove_turn_self_sovereign` (rotation=None) is RETIRED under recursion and PANICS** ("thread a
   rotation witness — the live node always does"). The v1 effect-vm fallback was deleted in the cutover but
   this entry was left as a now-broken door. The perf benches/bins/`perf-report §6` that called it were
   migrated to the LIVE rotated `prove_full_turn` (via the new `dregg_perf::rotated_transfer_turn` helper,
   mirroring `sdk/tests/sovereign_rotated_c1.rs` wall_a). CLOSURE: either delete the
   `prove_turn_self_sovereign` entry (it can only panic) or make it mint a default rotation witness so it
   is honest — right now it is a trap for any caller. (`sdk/src/full_turn_proof.rs:2646`.)
2. **The cell commitment is dominated by the cap-root Poseidon2 tree (~225 ms v8 / ~157 ms v9)**, NOT the
   blake3 envelope (which alone is µs). `compute_canonical_state_commitment` absorbs the openable
   sorted-Poseidon2 capability root (`compute_canonical_capability_root`) — building that full-depth tree,
   even over an EMPTY cap set, is the ~225 ms. It is the heaviest non-FRI per-turn primitive and the long
   pole of the genesis/first-paint cost (`demo_genesis_instant` ~1.24 s). CLOSURE: a witness-vs-recompute
   split (compute once, cache, prove the delta) — the same lever the prover already uses — or a lazier
   cap-root that doesn't pay full depth for a small/empty cap map. (`cell/src/commitment.rs`.)

## DREGG-LEAN-FFI ARCHIVE IS A SHARED MUTABLE FILE — concurrent-feature-set build race (named 2026-06-15)

`dregg-lean-ffi/build.rs:966` writes the GIT-TRACKED `dregg-lean-ffi/libdregg_lean.a` (the canonical
185 MB Lean-closure archive) from EVERY cargo target's build-script: it splices the Dregg2 closure in,
then `gc_unreachable_members` PRUNES to the set reachable from THIS build's `dregg_*` exports. The object
CACHE is per-`OUT_DIR` (safe), but the ARCHIVE is ONE shared path. Two lanes with different feature sets
building concurrently RACE: a default-feature lane splices the full closure (~3041 reachable members),
a `--no-default-features` lane (e.g. `starbridge-v2 --features embedded-executor`) prunes it to a smaller
set (~150 MB), and a torn read mid-rewrite leaves the archive missing initializers
(`Undefined symbols: _initialize_Dregg2_Metatheory_EpistemicDial` / `…CreateCellFromFactory`). OBSERVED
LIVE during the Theme-2 lane: my `cargo test -p dregg-lean-ffi` link FAILED while a starbridge lane was
re-seeding the archive; my next run (after it settled) was green. So it's a transient swarm-safety bug,
not a code bug — but it makes `cargo test` of any archive-linking crate FLAKY under the swarm. FIX shape
(pick one): (a) make the archive per-`OUT_DIR` (copy the seeded base into `OUT_DIR`, splice+link THERE,
never touch the git path during a build) — cleanest, fully swarm-safe; (b) an flock around the
splice+GC+link critical section keyed on the archive path; (c) skip `gc_unreachable_members` when
`CARGO_FEATURE_*` indicates a reduced feature set (avoids the shrink-then-rebloat thrash). Until fixed:
build archive-linking crate tests SERIALLY, or in a pbuild lane dir. (My memory's "copy a shared file at
HEAD into your pbuild lane dir if a foreign in-flight edit breaks the crate" is the manual workaround.)

## ⚑⚑ PRIME-ORDER-SCHNORR-CURVE (named 2026-06-15 — MAKE-PRIVACY-REAL lane, the DEEP one; TWO bugs, both with a fix in hand)

**Two stacked breaks on the in-circuit Schnorr (confidential-VALUE) path — NOT core auth (Ed25519, real).**
Both are loudly `// SECURITY:`-marked in-file; a rigorous PARI/GP curve search + an against-the-code
probe nailed both AND the fix.

**BUG 1 (FOUNDATIONAL — `circuit/src/babybear8.rs`): BabyBear^8 is NOT a field.** The tower reuses
non-residue `W=11` for BOTH layers (`x^4−11` and `y^2−11`). But `x^2` already squares to 11, so
`y^2−11=(y−x^2)(y+x^2)` factors → the quotient is a product ring `F_{p^4}×F_{p^4}` with zero divisors,
not `F_{p^8}`. PROVEN against the real code (temp probe, since removed): `A=y−x^2` is nonzero,
`A·(y+x^2)=0`, `A.inverse()=None` (norm `11−11=0`). This voids the "size p^8 ⇒ ~124-bit DL" premise at
the foundation. FIX: the top-layer non-residue must be a genuine `F_{p^4}` element (NO base scalar works
— every `c∈F_p*` is a square in `F_{p^4}`); use `V=x`, giving the clean field `F_p[z]/(z^8−11)` with
`z=y`, `x=z^2` (minimal, keeps the "−11" flavor; basis maps `x^i=z^{2i}, y=z`).

**BUG 2 (`circuit/src/schnorr_curve.rs`): composite 31-bit generator order.** `GENERATOR=(1,2)` lives in
the base-field embedding `F_p⊂F_{p^8}`, order `2013191319=3·331·2027383` (~2^31, composite) →
Pollard-rho/Pohlig–Hellman recover sk in seconds. STRUCTURAL obstruction found: ANY curve defined over
the BASE field has `#E(F_{p^8})` divisible by `#E(F_p)·#E(F_{p^2})·#E(F_{p^4})` (nested point groups),
so it is never near-prime — the largest prime factor is bounded by the primitive part `≈p^4≈2^124`,
giving at best ~62-bit security. (Confirmed: all 6 j=0 sextic twists are catastrophically smooth, top
factors 83/81/59-bit; best base-field a≠0 gives a 124-bit-prime × 124-bit-cofactor split = 62-bit.)
**The curve MUST be defined directly over F_{p^8}, not descend to a subfield.**

**✅ LANDED (both bugs fixed; field + prime-order curve + 248-bit bigint scalars real, green).**
`babybear8.rs` is now the simple field `F_p[z]/(z^8−11)` in the **power basis** (`self.0[i] = coeff of z^i`;
`z^8=11` reduction; 8×8 Gauss inverse) — verified irreducible in PARI and `is_a_field_no_zero_divisors`
(2000-elt sweep + the old `A=y−x^2=z−z^4` zero-divisor now INVERTIBLE) + `frobenius_order_eight` pass.
The curve `y^2 = x^3 + (z+2)x + (z^3+8)` over F_{p^8} has **PRIME order**
`N = 269903886087112502248563194479599378757044855200285447932848137338699712099` (248-bit, **cofactor
h=1**) — re-verified `isprime(N)` + `ellcard(E)==N` + cofactor==1 (PARI, parisize 800M). In the power
basis: `CURVE_A=z+2=[2,1,0,…]`, `CURVE_B=z^3+8=[8,0,0,1,0,…]`, `ORDER` = N's 8 LE-u32 limbs
`[3630237283,2285651324,1488992648,1932759141,1148232707,1275750001,2335120239,10011291]`.
`GENERATOR`: x=1 (RHS `z^3+z+11` is a QR), y=`[417687251,1863107357,177749990,1036295843,398021929,
450362472,1199411012,113045356]`; `generator_has_order_n` (N·G=O), `generator_cofactor_is_one`
((N-1)·G=−G, no small mult =O), `scalar_mul_respects_order` ((N+5)·G=5·G) all green. `scalar_*_mod`
rewritten to full bigint mod N (left-to-right double-and-add `mul_mod`, bit-fold `reduce_mod_n`; no
single-limb path). AIR: `SCALAR_BITS 128→256`, `TRACE_HEIGHT 512→1024`, `challenge` field
`[BabyBear;8]→Scalar`, bit scan 31→32 bits/limb; `recompute_challenge` + the test helper now delegate
to the now-`pub` `schnorr_sig::compute_challenge_from_elements` (one canonical `e`). 42 schnorr tests +
19 babybear8 green; `// SECURITY:`/placeholder markers removed. **The privacy-layer DL soundness
foundation is real.** (Curve params + field/order proofs landed; the in-circuit Schnorr AIR remains an
executable model — STARK-backend wiring of this AIR is separate, unchanged-scope work.)

## ⚑ SEMIHOST EXECUTOR-PD LANDED (2026-06-14 — the cockpit on the sel4 PD world)

**The executor-PD's `turn_in → step → commit_out` cap partition RUNS on the semihost, and a cockpit
turn flows through it.** `sel4/dregg-firmament/src/executor_pd.rs` adds `ExecutorPd<R: TurnRunner>` —
the firmament HEART (FIRMAMENT.md §2 L3) as the Endpoint SERVER over the `EmulatedKernel`: an app-PD
stages a postcard `Turn` into `turn_in`, `pp_call`s the executor (the `ingress→executor` edge the real
`executor-stub` PD awaits on ch 1), the executor reads `turn_in`, runs the bytes through `R`, writes the
`TurnReceipt`/reason into `commit_out`, and replies. It rides the EXISTING kernel IPC (Endpoint
recv/reply + regions, the SAME the compositor-PD uses); NO executor logic of its own. starbridge-v2
`world.rs` plugs in the FULL real `World` as the runner (`WorldRunner` → `SemihostCockpit::
commit_turn_via_semihost`): a cockpit turn stages → signals → runs the IDENTICAL `World::commit_turn`
path behind the Endpoint → reads the receipt back out of `commit_out`. PROVEN: commits, rejects an
overspend fail-closed, and is **byte-for-byte equal to the direct path** (same `receipt_hash`, same
`state_root`). This is the §3 KEYSTONE payoff ("the verified executor-PD hosts on the semihost NOW")
turned runnable. Tests: firmament `tests/executor_pd_boot.rs` (cross-PD Endpoint) + `executor_pd.rs`
inline units + starbridge-v2 `world.rs` (the 3 semihost tests). Doc: `docs/SEMIHOST-COCKPIT.md`.

### residue named by this landing (closure lanes):
- **the gpui frontend still calls `World::commit_turn` DIRECTLY, not through `SemihostCockpit`** — the
  semihost path is wired + proven equivalent, but the cockpit's panels (`cockpit.rs`, the many commit
  sites) have not been CUT OVER to route through `commit_turn_via_semihost`. Closure = swap the commit
  call across the panels (mechanical; the byte-for-byte equivalence test is the safety net), then run the
  frontend as an app-PD client of the executor-PD + compositor-PD over the kernel Endpoints (the cross-PD
  `serve_turn`/`serve_present` path, not the inline drive). → starbridge-v2, the frontend cutover. NOT
  blocking (the backend runs the PD world today; this routes the UI through it). `docs/SEMIHOST-COCKPIT.md §6`.
- **the wgpu software-render path → compositor-PD framebuffer is DESIGNED, not built** — an app-PD
  rendering its surface with a software wgpu adapter (lavapipe) and `present()`ing the pixels to the
  compositor-PD's framebuffer region (the in-sel4 render). The authority gate (T1/T2/T3) runs; the pixel
  pipeline is the named graphics frontier (F1/F2/F3, R3 Stage C). → the graphics lane. `docs/SEMIHOST-COCKPIT.md §4`.

## ⚑⚑⚑ C7 GREP-ZERO LANDED (2026-06-14 — the v1 deletion drive, READ FIRST)

**THE FLIP IS DONE — v1 effect-VM proof reaches GREP-ZERO under `recursion`.** With PATH-PRESERVE
Phases 0-4 landed (chained rotated path is the live default on all 3 finalized-turn arms), the v1
hand-AIR (`EffectVmAir` / `effect_vm_p3_full_air` / `CutoverFallback` / `BilateralAggregationAir`) is
removed from the recursion build. The end-state is FENCE-not-delete: the v1 OLD-PROVER is retained
`#[cfg(not(feature = "recursion"))]` for the v1 floor (the SACRED wasm prover floor + the demo MCP
tools), and DELETED outright where dead in both builds (the Silver joint surface `JointParticipant`/
`prove_joint_turn`/`verify_joint_turn`; `DescriptorForestNode`/`verify_descriptor_forest` — the last
`EffectVmP3Proof` struct field; the v1 `BilateralAggregationAir`/`AggregationInnerRow`/
`build_aggregation_trace` block). `generate_effect_vm_trace`/`EFFECT_VM_WIDTH`/`AIR_DESCRIPTOR`/
`CUTOVER_READY_SELECTORS`/`EffectVmShapeAir`/`CrossSideExistenceAir`/`BundleTreeFoldAir`/the V2 bilateral
all STAY (Bucket D/E). The recursion-leaf is the ROTATED `DescriptorParticipant`/`RotatedParticipantLeg`
(Bucket F was already landed). **GREP-ZERO = 0 true live-under-recursion v1 refs** (236 literal matches,
all comments/strings/not(recursion)-fenced). Gates GREEN on persvati: `cargo build --features recursion
-p dregg-circuit -p dregg-sdk -p dregg-turn -p dregg-node` (Finished, exit 0) + `cargo test --features
recursion --no-run -p …` (exit 0) + circuit `not(recursion)` floor (exit 0). The executor secondary-verify
arms (`verify_sovereign_witness_stark`, the atomic-turn/bearer-cap default-AIR, `verify_bundle_with_stark`)
+ the SDK v1 cutover (`prove_effect_vm_with_cutover`/`verify_effect_vm_proof_with_cutover`/`revalidate_turn_
self_sovereign`) + the v1 sovereign producer (`cipherclerk::prove_sovereign_turn`/`emit_witnessed_receipt`)
+ the MCP demo v1 tools are all `not(recursion)`-fenced with fail-closed `recursion` arms (no silent skip).

### residue named by this drive (closure lanes):
- **`dregg-node`/`dregg-verifier` gained a `recursion` feature** (default-on, forwarding to
  `dregg-circuit/recursion`) — they previously had NO such feature so their `#[cfg(feature="recursion")]`
  gates misaligned with the recursion-by-default circuit. Latent bug exposed + fixed by this drive.
- **the standalone `dregg-verifier` has NO rotated replay-chain verify path** — under recursion its v1
  `verify_effect_vm_proof`/`replay_one_with_prev` are FAIL-CLOSED stubs. Closure lane: build the rotated
  replay-chain verify (`verify_vm_descriptor2`-based), analogous to the wasm-rotated Option-A. Until then
  the recursion-built verifier rejects (honest, not silent).
- **workspace `exclude` fix**: `starbridge-web-surface`/`starbridge-v2`/`deos-leptos`/`deos-web-cells`/
  `servo-render`/`dregg-tui` (recently-added in-tree separate `[workspace]` roots) were breaking
  workspace-wide `cargo` ("multiple workspace roots") — added to the root `Cargo.toml` `exclude`.
- the wasm `not(recursion)` prover floor stays the separate Option-A ember-decision (out of this scope).

## ⚑⚑⚑ POST-COMPACTION STATE (2026-06-14 late — READ FIRST)

**THE HARDSWAP — the VK EPOCH LANDED GREEN.** Rotated IR-v2 R=24 is now the DEFAULT registry,
v1 fallbacks retired, the −65.6% proof-size prize is LIVE (commits `6011fc77f` walls → `0802b305b`
live-path → `d33d02107` pre-VK gauntlet → `5b3772873` VK epoch #183). The tree is GREEN + COHERENT
(no half-deletion). **C7 grep-zero is gated on a BUILD, and the gating decision is ✅ DECIDED (ember,
2026-06-14): PATH-PRESERVE.** The deputy's deep re-trace (commits `7a8409572`/`fd478564c`/`5e71c24c2`/
`afe4e0606`, see `docs/V1-DELETION-MANIFEST.md` buckets E/F/G) found the v1 OLD-PROVER symbols can't be
deleted yet because (E) `generate_effect_vm_trace` is the SHARED generator the rotated leg is BUILT ON
(NOT v1 — never delete it), (F) `EffectVmP3Proof` is the recursion LEAF type in 5 files (mandatory-
rotated-leaf cutover first), (G) heterogeneous/non-synthetic finalized-turn coverage. ember settled G the
only dregg-coherent way — *"build path-preserve for SURE; any other decision wouldn't be dregg"* — so the
WEAKEN option (commit those turns proof-pending) is OFF the table. The C7 lane is now: **BUILD chained
multi-cohort + non-synthetic rotated proving so EVERY finalized turn stays proven (ARGUS unfoolability
intact), THEN bucket-F leaf cutover, THEN the bucket-A/C delete.** Staged persvati-green plan =
`docs/PATH-PRESERVE.md`. Each phase lands green; a half-landed prover-without-verifier is RED (forbidden).
(The interrupted `wf_9a7d5e77-b48` was looping on exactly this G decision — now resolved; `cv`-dug the
substantive thread, the decision is made.)

**LANDED 2026-06-14 (all green + committed):**
- verified-deos Lean crown WIDENED to 7 modules / 56 axiom-clean keystones (`482ba8db1`): `FogOfWar.noninterference`
  + `Rerender.snapshot_roundtrip` depend on NO axioms (the frustum-cull IS info-flow non-interference; snapshots
  re-expand losslessly per-viewer). lake `Dregg2` green (3930 jobs).
- fog-of-war webgame (`starbridge-web-surface`, own workspace, 78+4 green) — fog IS the membrane + the HONESTY
  CLOSURE: the no-peek `vk_hash` is now a REAL `canonical_predicate_vk` + registered `FogVisionVerifier` (the same
  registry `authorize.rs` dispatches through) + ed25519 proof (keystone `no_peek_for_real_only_the_secret_holder_can_prove_vision`).
- app-framework deos-EVOLUTION (`c55444e71`, 83+7 green) — cell-affordance surfaces in the bones + the dispatch
  seam CLOSED (`fire_through_executor` → real `EmbeddedExecutor` turn → executor's `TurnReceipt`).
- app-framework cap∧state GATED-AFFORDANCE rung (the Lean `Dregg2.Deos.GatedAffordance` Rust-mirror LANDED;
  app-framework 121-lib + council-board 5-int + 142 total green) — `GatedAffordance{affordance,state_cond}` +
  `FireError::StateConditionUnmet` + `GatedSurface::project_gated_for` (affordance.rs) + `DeosCell::{gated,
  project_gated_for,fire_gated_through_executor}` reading LIVE state via `EmbeddedExecutor::cell_state` (the author
  threads no `(old,new)`). Demo `examples/deos_council_board.rs` (+ `tests/deos_council_board.rs`): a button lights
  IFF caps∧state both pass; the htmx tooth (same approver, approve LIT in PENDING → DARK after RESOLVED); both
  anti-ghost refusals in-band (cap tooth Unauthorized + state tooth StateConditionUnmet, nothing submitted); a real
  verified turn through the executor; per-viewer frustum-snapshot rehydration (outsider refused). The model FOUND a
  bug: an affordance PRECONDITION (`==PENDING`) must NOT be the cell's lifetime INVARIANT (`Monotonic`) — conflating
  them made the executor reject the resolving turn; split → green.
- pg-dregg drainer daemon + Tier-D spike (verdict **D-SIDECAR**; 120 pg18 + 104 core + 21 proptest green).
- PATH-PRESERVE DECIDED + the staged plan (`867b41fcb`, `docs/PATH-PRESERVE.md`).
- the prior deos STEEL + dev-ex (rehydration stack · DEOS/DEOS-APPS docs · AGENTS.md · nextest split).

**LANDED 2026-06-14 (the empowered-doer wave, all green + committed):** PATH-PRESERVE Phase 0+1 (`fff442ca6` — the N-leg
chained rotated proving; chain≡monolithic + tampered-middle anti-ghost + conservation-across-chain teeth) · the bigger
fog-of-war WORLD (`16c374bbb`) · the app-framework deos-COMPOSITION (`7d7726879`, 142/142) · the embeddable-Lean-runtime
spike (`c93293686` — the pg-Tier-D + seL4-executor-PD blocker REFUTED by measurement: mimalloc is private + the task
manager is lazy; the executor PD already BOOTS; pg full-D = DAYS).

**⚑⚑ LEAD LANE (ember DECIDED 2026-06-14): FINISH THE CUTOVER to grep-zero — and HOLD the devnet redeploy until it lands.**
The staged ladder, each persvati-green (every finalized turn is ALREADY proven on current main — this is CLEANUP, not a
soundness gate): PATH-PRESERVE **Phase 3** (non-synthetic-cell witness — RUNNING `a100c225`) → **Phase 4** (the live cutover:
heterogeneous / non-synthetic turns route to the chain in `node/src/blocklace_sync.rs`, not the v1 fallback) → **bucket F**
(the 5-file recursion-leaf cutover, drop `EffectVmP3Proof`) → **#103** (executor off `EffectVmAir`) → **C7** (delete v1 +
grep-zero). The OTHER pillars braid in parallel but the cutover is the LEAD: pg full-Tier-D (days; wire `dregg_ffi_init_st`
into pgrx) · the deos predicate/caveat LANGUAGE uplift (the lamesauce fix) + the affordance→live-`TurnExecutor` seam ·
`./site` deos-integration · seL4 executor-PD productionization (weeks). ENDGAME (post-grep-zero): fresh-genesis devnet +
a running starbridge-v2 on ember's mac (host blocker: the gpui Metal Toolchain download, damaged Xcode `DVTDownloads`).

**HELD / NAMED (post-cutover unless noted):** sdk-ts/dist Docker rebuild · **devnet upgrade = EMBER's act, fresh genesis,
gated on cutover + follow-ups** · **`./site` integration with the deos/web directions** (pairs with the assurance-catalog
regen named below) · **seL4 / robigalia — a LIVE frontier that BOOTS** (corrected 2026-06-14; the prior "toolchain-absent / scaffold" line
was a compaction-degraded caricature — see `[[project-firmament-sel4-boots]]` + `sel4/README.md` + `docs/{SEL4-EMBEDDING,
FIRMAMENT,DREGG-DESKTOP-OS}.md` + `/tmp/sel4-boot-*.log`): the **Robigalia v0 demo BOOTS** real Rust PDs on seL4 in QEMU
on a NATIVE-macOS Microkit 2.2.0 toolchain (`~/sel4-sdk`, `make run`) — M0 banner ✅ · M1 verifier ✅ · M2 rbg
DirectoryCell ✅ · M-STARK a REAL on-device STARK ✅ · M5 riscv64 ✅ (serial-captured). The **firmament**
(`dregg-firmament/`) = ONE `Capability{target,rights}` across DISTANCE — local seL4-cap ↔ distributed dregg-cap ↔
surface(=a window), n=1-collapse to strong-local; the **semihost** (`EmulatedKernel` thread-v0 / `process_kernel`
MMU-process-v1 / real-Microkit) runs the SAME PD source three ways; the compositor-PD is real. THE blocker is essentially DONE — REFUTED + the executor PD BOOTS (measured 2026-06-14, `c93293686`,
`docs/EMBEDDABLE-LEAN-RUNTIME.md`): the mimalloc-override / worker-thread premise was WRONG (mimalloc is a PRIVATE heap,
the task manager is LAZY/single-threaded); the only real removal was the libuv thread (`dregg_ffi_init_st()`), and
`sel4/dregg-pd/executor-{pd,rootserver}/` already boot the Lean executor in a real PD (fresh qemu → status:2 ok:1).
**pg full Tier-D is now GREEN** (2026-06-14, persvati Linux + pg18.4 via cargo-pgrx): the verified `execFullForestG` RUNS
INSIDE a live pg18 backend under the SHARED Lean link (`DREGG_LEAN_LINK=shared`) — `pg_test`s
`pg_the_verified_executor_runs_inside_the_backend` + `pg_drainer_drains_the_queue_…` + `pg_drainer_runs_execfullforest_in_backend`
all OK; `runtime_available()`=true (`dregg_ffi_init_st` succeeds POST-FORK), the drainer's PRODUCE gate commits a real
`execFullForestG` receipt to `dregg.turns` (NOT the FoldProducer stand-in). The un-run Linux re-measure is DONE
(`dregg-lean-ffi/tests/embeddable_runtime_probe_linux.rs`): PROP-1 malloc→glibc (no interposition) both link modes;
PROP-3 committing turn + fail-closed both modes; PROP-2 = STATIC **2→2→2** (libuv-free) / SHARED **2→4→4** (init adds 2
libuv INFRA threads on Linux — refines §1.3's macOS single-thread count — but **the turn itself spawns 0**, created
post-fork, so nothing crosses the fork). `docs/EMBEDDABLE-LEAN-RUNTIME.md` §5 rewritten with the results. RESIDUAL (one,
named): pg-dregg does not link `dregg-turn`, so the in-backend producer SYNTHESIZES a conserving transfer rather than
decoding the submitter's postcard `SignedTurn` — lifting the full `SignedTurn→WForest` decode in-backend (the node-side
`dregg-turn` `lean_apply` marshaller, #171) is the one piece between this and "an arbitrary submitted turn executes
in-backend". seL4 executor-PD = WEEKS of productionization. verifier-PD is Lean-free-linkable (`no-lean-link`).
- **DEOS SPINE on seL4 — the persist-PD IS the `dregg.turns` commit log of the seL4 deos foundation; now REAL redb durability + the app-hosting economy (R2+R3+R8, host-GREEN).** `docs/PG-DREGG-ON-SEL4-DEOS-SPINE.md` + `sel4/persist-hosttest/`: the persist-PD's durable verified commit log + Tier-C chain gate. **Three organs, one gate, 21 tests green** (`cargo test --release`): (1) `commit_store.rs` — the chain-gate discipline `no_std`+`alloc`, REUSING `pg-dregg/src/mirror.rs:477` `verify_chain_step`/`ChainRefusal` + `persist/src/commit_log.rs` `CommitRecord` VERBATIM (rides INSIDE the persist PD via `#[path]`); (2) **`redb_store.rs` (NEW) — the REAL durable store**: the SAME gate + record committed into real `redb` ACID tables over a block-device `StorageBackend` (`len`/`read`/`set_len`/`sync_data`/`write` = exactly a block cap). Durability is REAL — `commits_survive_drop_and_reopen_over_the_same_bytes` (drop the store, reopen over the file bytes, head/cursor/log/indices recover, chain self-checks). 8 `#[test]`s. (3) **`hosting.rs` (NEW) — the app-hosting economy**: pay coin to be hosted = a conserving `Transfer` (app→host) committed through the durable spine; a lapsed fee EVICTS (a verified durable turn dropping the hosting), fail-closed; Σ value invariant. 6 `#[test]`s + `Dregg2/Apps/HostingLease.lean` (the lease = a TIME(period)+BUDGET(balance) caveat over the durable slot; 5 teeth + #guard, `#assert_all_clean`). Witness binaries `host_persist_spine` + `host_durable_hosting` green. Distinct from `docs/PG-DREGG-ON-SEL4.md` (the literal-Postgres VMM-guest ladder) — SQL face vs the native PD-pair spine. RESIDUAL (the named wall + levers, all the macOS user-mode-qemu-aarch64 checkpoint, NOT the semantics): (R3, REFINED) the **`BlockCapBackend`** — ONE `redb::StorageBackend` impl whose 5 ops go through the seL4 block cap (the durable redb store above it is host-green + unchanged; this is now a bounded device-driver trait impl, not "the backend"); (§3.3) the executor→persist `CommitRecord` serialization + `commit_out` shared-region framing (today the seat reads a sentinel byte) + the persist-PD ELF link carrying `commit_store.rs` (the crypto-floor on-device checkpoint shape); (§3.3) the ingress/submit-queue enqueue over `turn_in` (= `node/src/submit_queue_drainer.rs` shape). → `sel4/persist-hosttest/` + `sel4/dregg-pd/persist-stub/`, downstream of the executor PD boot (R0) DONE.

**STARFORGE:** dregg's agent joined the pen-pal agent-town — PR #12 `claude-of-dregg` (clone `~/clome/starforge-commons`),
first letter to sibling `claude-of-tulip`. dregg is REAL + in contact with other people now.

## ⚑ 2026-06-14 FLAGSHIP WAVE — LANDED (4 lanes, each main-loop-re-verified before commit); residual follow-ups below

The four lanes are in git history: faucet hardening (`0baf9da31`, full dregg-node suite 225/0 — caught+fixed a
production regression: the `is_solo` provisioning gate broke a single-but-unflagged node) · pg-dregg FLAGSHIP
(`425b6d28c`, 80/0 + live-pg18; demo+benches+loadgen+fuzz+VS-DBOS) · web-surface servo-forward (`starbridge-web-
surface/`, 20/0) · sdk pg-native (sdk-py 71/4-skip + sdk-ts 74/0). Open residuals these named:

- **sdk-ts dist needs a DOCKER rebuild + commit.** The `@dregg/sdk/pg` `./pg` export points at gitignored
  `dist/pg.{js,mjs,d.ts}` (+ `dist/index.*`); they were built ON-HOST this session because the Docker daemon
  could not pull `node:22` (NO npm install / zero fetch was done — only first-party tsc/tsup). Per the npm-in-
  Docker policy the dist was NOT committed. CLOSURE: rebuild sdk-ts dist in Docker node:22, `git add -f` the
  dist artifacts. (src + tests + package.json ARE committed; the package is consumable from source today.)
- **pg18 is STOPPED** (the Docker daemon churn stopped the shared cargo-pgrx pg18 cluster, port 28818). Restore
  with `cargo pgrx start pg18` before the next live-pg test/bench run.
- **web-surface → firmament/turn closures** (`docs/desktop-os-research/BUILD-STATUS.md`, agent-reported, main-
  loop decisions): (a) move the web caveat allowlists/permissions onto the real `cell/src/facet.rs` `EffectMask`
  free bits 24-31 (additive; narrowing machinery exists) instead of atop `SurfaceCapability`; (b) wire the
  `dregg://` fetch as a full `Effect`-bearing `TurnExecutor` turn whose receipt is the executor's `TurnReceipt`
  (the `ServedResourceCell` cell-program template) — today it is a verified cell-read + domain-separated receipt
  commitment; (c) the full `dregg://<fed>/<cell>/<swiss>` distributed fetch = bind `captp/` `SwissTable::enliven`
  + `Netlayer::dial` (this crate models the local resolve+attest half); (d) the LIBSERVO SEAM at `delegate.rs`
  `MockSurface` (replace with the real `servo::WebViewDelegate` impl when libservo + Metal/wgpu link). Quorum-sig
  crypto on `AttestedRoot` is the `hints` layer (structural now; the receipt-stream Merkle binding IS real).
- **ObservedFieldEquals embedded-executor wiring — CLOSED 2026-06-14** (the §11.2 cross-cell-read convergence):
  the turn executor now builds a real `FinalizedRootAuthority` (`execute_tree.rs::build_finalized_root_authority`)
  from its committed view of each referenced peer cell's GENUINE finalized commitment + field value, handed to the
  `WitnessBundle` as `finalized_roots: Some(&observed_authority)` — so the deos cross-cell observed-field atom now
  ACCEPTS a genuine read (local field == peer's finalized value) and REJECTS the mismatch/forge teeth on the
  embedded commit path (was fail-closed REJECT-only). Accept/reject pair: `coverage_state_constraints::
  observed_field_equals_accept_and_reject` (a peer oracle cell inserted into the shared ledger; its real
  `state_commitment()` is the program's `at_root`). Coverage gate: `ObservedFieldEquals => true`, removed from
  `NOT_YET_COVERED_CONSTRAINTS`, ratchet `MAX_UNCOVERED_CONSTRAINTS` 10→9. Side-catch (same gate did not even
  compile — `CollectionAggregate` was MISSING from the classifier match, RED at HEAD): added its honest executor
  accept/reject pair `collection_aggregate_accept_and_reject` (a seeded `heap_map` collection meeting/failing a
  CountSatGe statistic across a submitted SetField turn) + `CollectionAggregate => true` arm, so the gate is
  exhaustive and the not-yet list is honest at 9. Green on persvati: `cargo check -p dregg-turn` clean;
  `coverage_state_constraints` 25/25 + `protocol_coverage_gate` 3/3.
- **`cargo check --workspace --tests` is broadly RED — pre-existing dregg3-reduction test-corpus rot** (named
  2026-06-14, surfaced by the ObservedFieldEquals convergence gauntlet once the WitnessBundle ripple closed):
  ~172 `cannot find` errors (E0425/E0422/E0433 — stale `use Effect/Turn/TurnExecutor/Action/CallForest/…`) in
  the TEST targets of `protocol-tests/`, `dregg-dsl-tests/`, `dregg-tests` (`tests/src/`), and the `#[cfg(test)]`
  modules of `cell`/`turn`/`circuit`/`blocklace`/`bridge`/`rbg`/`token`/`trace`. Every crate LIB compiles — this
  is pure test-module bit-rot from the verb reduction, invisible because the default nextest profile filters it
  (per-crate green is the dev loop). CLOSURE: a "green the test corpus" lane — repair the stale imports file-by-
  file (most cascade from one missing `use` per file) until `--workspace --tests` = 0 errors, then keep it in CI.

## Rides THE ROTATION (dies at or lands with the one VK epoch — do not do separately)

- sbox_registers→0 descriptor metadata (chip uses inline x⁷; named in 0b05afc1a) — flip at the closing-ceremony regen.
- RESERVED mask removal + 186→159 column compaction (REORIENT EPOCH STATUS).
- registers 8→16 + FactoryDescriptor.fields · PI v3 (committed-height + rateBound/challengeWindow) · heap_root register.
- iroot bound into recStateCommit (non-omission obligation, 9dcd42cd9).
- cap-reshape phase D (in-circuit cap crown completion; #103 audit: A–E + RevokeCapability done. The 2026-06-13 burn-down to fully-coherent left TWO ember-decisions characterized under "Decisions pending (ember)": the two-AIRs sovereign-path soundness item + the 4-ary-vs-sorted membership-leg retire-or-keep. The stale-`EffectVmEmitCapRoot` item resolved NO-OP: that module is the load-bearing Phase-A digest spine under the whole cap family, already coherently scoped — clarified its V2/Phase-E layering with a forward-pointer doc note, not retired).
- #150 confirmation: does the umem `absent` + sorted-gap boundary fully retire DslRevocationTree (TREE_DEPTH=4)? One read-pass at cutover.
- fresh-key sorted-INSERT map-op (reuses MapAbsent adjacency; named in cff8509ba).
- per-turn chip amortization (blocked on an IR-v2 turn assembly; named in 0b05afc1a).
- MMR §6 CommitBindsMMR layout fact (node writes both roots at dense positions; the Receipt-apex residual premise, 7894e5789) — discharged-by-construction at the flag-day.
- balance/nonce → NAMED-register assignment (RotatedLimbs carries no separate balance/nonce limbs; the umem projection maps them to the heap domain — pick ONE canonical story; ember-visible decision, ROTATION-CUTOVER.md §2 note).
- cells_root + iroot per-turn PRODUCERS in turn/ (`turn/src/rotation_witness.rs`, NAMED in EffectVmEmitRotationV3.lean §3) + lifecycle/epoch trace carriers — ROTATION-CUTOVER.md §5 items 3-5. The staged-additive producers + trace builder + cell≡circuit differential ALREADY LANDED GREEN (51850ee91, no VK bump); these notes track the FLIP consumption. SEQUENCING: build the rest WITH the flip's rotated trace builder, not before.
- guardAtom IR kind (umem adapter c) confirmed NOT landed (absent from DescriptorIR2.lean + descriptor_ir2.rs): in-circuit policy/caveat enforcement for v2/v3 = cap-crown phase D + Policy.lean line, rides rotation.
- HEAP-KEYED CAVEATS executor runtime discharge (named premise `HeapCaveatRuntimeDischarge`; template = `verify_slot_caveat_manifest`; semantics welded via `tagHeapAtom`→`HeapAtom.lift`→`evalHeap`) — ROTATION-CUTOVER §5 item 9; at the flag-day the staged 29-felt manifest replaces the live 25-felt slot manifest in the regenerated PI region. (Wire shape STAGED; live v1 manifest untouched.)
- PI v3 rateBound/challengeWindow: carried-only (producer copies context into PI 202/203; verifier pins ZERO sentinels, proof_verify.rs:269-270). Enforcement arrives with optimistic-proving/dispute (#169) which owns these slots — nothing further pre-#169.

### ⚑⚑ C7 PRE-DELETION BLOCKER — four LIVE v1 deps survive the VK epoch in recursion builds (2026-06-14, C7 attempt)

**C7's gating premise is UNMET.** The manifest (`docs/V1-DELETION-MANIFEST.md`) + the PRE-FLIP GATE
framed C7 as "the VK epoch landed green ⇒ a mechanical delete fan-out." Against the CODE at HEAD
(`5b3772873`) that is false: the VK epoch (#182/#183) migrated the DEFAULT compose+prove path to
rotated, but the three walls (A/B/C) + the wasm-decision did NOT cover FOUR live v1 dependencies that
remain in **recursion-enabled** builds — so grep-zero (`generate_effect_vm_trace · EffectVmAir ·
EffectVmP3Air · EffectVmP3Proof · prove_effect_vm_p3 · CutoverFallback · EFFECT_VM_WIDTH`) is
PROVABLY-UNREACHABLE-in-recursion until these close, and a PARTIAL cutover ships RED (forbidden).
Items 2/3/4 are ordinary engineering (NO crypto primitive); item 1's keystone (a rotated FRI-free
revalidation primitive) is blocked at the PROVING-LIBRARY BOUNDARY (`p3-batch-stark`'s interaction-
aware constraint checker is `pub(crate)`+debug-only — see item 1). Together they are a multi-system
cutover, NOT a delete. The tree is GREEN + UNTOUCHED (baseline `pbuild hardswap` of
circuit/sdk/turn/node = exit 0; no edits made). The four, file:line'd:

1. **`bespoke_air_accepts` = the LIVE F-DOS-1 inline witness-revalidation, v1-AIR, no rotated twin.**
   `circuit/src/effect_vm_p3_full_air.rs:2451` checks `EffectVmAir::eval_constraints` FRI-free
   (sub-ms). LIVE callers: `node/src/api.rs:~2470` (HTTP commit path, `http_project_effects`→
   `generate_effect_vm_trace`→`bespoke_air_accepts`), `node/src/prove_pool.rs:22`,
   `sdk/src/full_turn_proof.rs:2391` (`revalidate_turn_self_sovereign`). `descriptor_ir2` exposes NO
   FRI-free `accepts` (only `prove_*`/`verify_*`). ** DEEPER THAN A WRAPPER (verified 2026-06-14):**
   a naive `p3_air::check_all_constraints(Ir2Air, ..)` does NOT compile — `Ir2Air::eval` needs
   `InteractionBuilder` (the LogUp `bus.lookup_key`, `descriptor_ir2.rs:~76`) which the plain debug
   builder lacks; and the only interaction-aware FRI-free checker, `p3-batch-stark::check_constraints`
   (`~/.cargo/git/checkouts/plonky3-*/82cfad7/batch-stark/src/check_constraints.rs:37`), is
   `pub(crate)` + `#[cfg(debug_assertions)]` — NOT exported. So the rotated revalidation primitive is a
   PROVING-LIBRARY-BOUNDARY dependency (this item is the true long pole). CLOSURE OPTIONS: (a) upstream
   a `pub` interaction-aware constraint-check in the `Plonky3@82cfad7` fork (or our recursion fork) and
   call it; (b) reimplement the LogUp permutation-trace assembly + multiset check inside dregg-circuit
   (substantial — reproduces `check_constraints`); or (c) accept that rotated revalidation runs the
   real `prove_vm_descriptor2`+`verify` (loses the sub-ms F-DOS-1 budget = a commit-path perf
   regression). PLUS the node commit path must assemble the rotated trace from real before/after
   `RotationWitness` (`dregg_cell::Cell` pre/post — today it re-derives a v1 trace from pre-state with
   NO cells).
2. **node `rotation: None` runtime FALLBACK still runs the v1 leg under recursion.**
   `node/src/turn_proving.rs:358/385` (`rotation_witness_for_self_sovereign_impl` returns `None` for
   non-synthetic-shaped cells / non-cohort / heterogeneous / no-op / non-graduated turns) →
   `prove_full_turn` then runs the v1 `generate_effect_vm_trace`+`prove_effect_vm_with_cutover` leg
   (`sdk/src/full_turn_proof.rs:1124-1131,1185-1201`). Plus `prove_and_verify_finalized_turn`
   (`turn_proving.rs:526`) calls `generate_effect_vm_trace` UNCONDITIONALLY for `new_commit`. CLOSURE:
   make the recursion build rotated-ONLY — non-cohort turns FAIL-CLOSED (proof skipped + loud log),
   not silent-v1. ⚠ behavior change: must confirm the rotated cohort
   (`trace_rotated::rotated_descriptor_name_for_effect`, 26 effects + per-field SetField; NoOp/
   heterogeneous fail-closed) covers every live turn shape, else this regresses live-turn proving.
3. **aggregation/forest/IVC proof TYPE is still `EffectVmP3Proof` (v1 leg co-resident).**
   `circuit/src/proof_forest.rs:243,280` + `joint_turn_aggregation.rs:130,197,213`
   (`DescriptorParticipant.proof: EffectVmP3Proof` + `Option<RotatedParticipantLeg>`) +
   `ivc_turn_chain.rs`. `EffectVmP3Proof = BatchProof<DreggStarkConfig>` and
   `Ir2BatchProof = BatchProof` are the SAME type, so this is mostly an alias cutover, BUT the v1
   `proof` field must be DROPPED and the `rotated` leg made MANDATORY (the unfinished C4 step the
   structs' own docs name: `joint_turn_aggregation.rs:138`).
4. **wasm in-browser prover is v1 + recursion is ON in the wasm graph.** `wasm/src/runtime.rs:710`
   (`generate_effect_vm_trace`+`EffectVmAir`+`stark::prove`) + `wasm/src/bindings_lightclient.rs:389`
   + the `BilateralAggregationAir` bundle (`wasm/src/bindings.rs`). wasm pulls circuit's DEFAULT
   features (= `recursion`, via observability/bridge/lightclient — see the `[patch]` note in
   `wasm/Cargo.toml`), so this is a RECURSION build and these unconditional refs block grep-zero
   there too. Option-A (ember-decided): migrate to `prove_effect_vm_rotated_ir2` (compiles in the
   wasm graph already) by synthesizing before/after `Cell::with_balance` + rotation witnesses for the
   demo inspector path. The brief's "`not(recursion)` wasm v1 FLOOR" residual is only coherent if the
   wasm prover gains a `#[cfg(feature="recursion")]` rotated branch (shipped wasm has recursion ON);
   a bare `not(recursion)` fence would DELETE the in-browser prover (a degradation — not acceptable).

SEQUENCING (each persvati-green): (1a) the additive `ir2_descriptor_accepts` checker + test [keystone,
zero-risk] → (3) the `EffectVmP3Proof`→`Ir2BatchProof` alias + drop-v1-leg in aggregation → (1b)+(2)
node commit-path rotation-witness assembly + rotated-only fail-closed → (4) wasm Option-A → then the
mechanical DELETE of bucket A (`effect_vm_p3_full_air.rs`, `effect_vm/air.rs` v1 surface,
`effect_vm_p3_air.rs` is actually `EffectVmShapeAir` used by `recursive_witness_bundle.rs` — KEEP or
re-home) + bucket-C harnesses + grep-zero verify. NOTE the manifest mislabels: "`EffectVmP3Air`
shape-mirror in effect_vm_p3_air.rs" is really `EffectVmShapeAir` (a recursion shape-probe, LIVE in
`recursive_witness_bundle.rs:237/360/412/420`), and bucket-A's `effect_vm_p3_full_air.rs` hosts the
LIVE `bespoke_air_accepts` + the `EffectVmP3Proof` alias — so it is NOT a clean delete. The ember-
decision: expand C7 to perform this four-part live-path cutover (a flip-scale phase), or land it as
the sequenced follow-on above.

⚑ SHARPENED (2026-06-14, C7 fix-round-1 — independent re-trace at greater depth; the two stoppers REFINED,
one of them DOWNGRADED OUT OF "crypto-primitive" territory):

- **Blocker #1 (item 1 keystone) is NOT a crypto-primitive dependency after all — it is an OPTIMIZATION we
  can simply drop.** Re-traced the F-DOS-1 contract end-to-end (`node/tests/f_dos_1_request_path_liveness.rs`
  §"the soundness bar"): the load-bearing invariant is "NO STARK proving under the `state.write()` lock," NOT
  "a sub-ms FRI-free revalidation." The sync `bespoke_air_accepts` is a DEFENSE-IN-DEPTH witness cross-check
  layered ON TOP of the executor, which already validated+committed the turn FIRST (`api.rs:2739`
  `execute_via_producer` → `match TurnResult::Committed`). So the keystone resolves with ZERO new crypto and
  ZERO commit-ack perf change: (a) DROP the sync `revalidate_http_witness`/`bespoke_air_accepts` call on the
  commit path (the executor is the authority; the witness check added nothing the executor didn't), and
  (b) make the async prove pool (`prove_pool::run_job`, today `EffectVmAir`+`stark::try_prove`) prove the
  ROTATED `Ir2BatchProof` instead — which is exactly the rotation's purpose, run async OFF the lock just like
  today's v1 async prove. The earlier "needs a `pub` `p3-batch-stark::check_constraints` / LogUp reimpl"
  framing is MOOT (verified: the emberian local fork `../plonky3-recursion` does NOT vendor `batch-stark` —
  it is upstream `Plonky3@82cfad7`; and even an export would not recover the sub-ms budget since LogUp
  permutation-trace assembly dominates — so the FRI-free-rotated-checker avenue was a dead end anyway, but
  it is also UNNEEDED). Item 1 is therefore ordinary (if cross-file) engineering.
- **Blocker #2 (item 2) is the ONE genuine ember-decision, and it is NARROW + precisely bounded.** The
  rotated R=24 cohort covers EVERY live single-effect selector (`trace_rotated.rs:438` "every LIVE selector
  resolves; NoOp + unknown fail closed" — verified by reading the full match). So `rotation_witness_for_self_
  sovereign` (`turn_proving.rs:353-387`) returns `None` — and `prove_full_turn` runs the v1 leg
  (`full_turn_proof.rs:1124-1131,1185-1202`) — for EXACTLY three live shapes, all reachable on the node's
  finalized-turn proving path (`blocklace_sync.rs:2643/2702`): (i) NoOp/IncrementNonce-only turns,
  (ii) **HETEROGENEOUS multi-cohort turns** (the `cohort_ok` all-same-descriptor gate fails), and
  (iii) **non-synthetic-shaped cells** (the `cell_is_synthetic_shaped` gate fails: any non-zero field or
  non-empty c-list). Rotated proving for (ii)+(iii) is NOT built (heterogeneous-batch rotated proving +
  non-synthetic-cell rotated witnesses are new capability). THE DECISION ember owns: when a recursion-build
  node finalizes a turn of shape (i)/(ii)/(iii), should it **commit UNPROVEN** (proof-pending→skipped — note
  this is ALREADY a tolerated state: `prove_pool::run_job:201` "receipt stays committed-but-unattested" when
  the async prover fails), or should heterogeneous/non-synthetic turns be **REFUSED**, or must rotated
  proving be BUILT for (ii)+(iii) before the flip? This changes production proving-COVERAGE semantics
  (today every such turn carries a v1 proof), so it is an ember scope-call, not a deputy default. Once
  decided, item 2 collapses to: replace the v1 leg in `full_turn_proof.rs:1185-1202` with the decided
  behavior (commit-unproven = drop the leg + Tentative; refuse = error; build-rotated = new prover), gate any
  residual v1 to `#[cfg(not(feature="recursion"))]`.
- **Item 3** (`EffectVmP3Proof` field on `DescriptorParticipant`) is the C4 drop-v1-leg: `EffectVmP3Proof`
  and `Ir2BatchProof` are the SAME `BatchProof<DreggStarkConfig>` (verified: `effect_vm_p3_full_air.rs:77`
  ≡ `descriptor_ir2.rs:144`), so the TYPE is a free rename — but a HONEST close drops the v1 `proof` field
  (minted by the v1 prover, read by host admission, `joint_turn_aggregation.rs:130/139`) and makes `rotated`
  mandatory; a bare type-rename that leaves the v1-prover-minted proof in place would LAUNDER grep-zero
  (forbidden). Rides item 1's async-rotated cutover (then the participant's proof IS rotated).
- **Item 4 (wasm)** is independent of #1/#2 and lands as ember's PRE-DECIDED `#[cfg(not(feature="recursion"))]`
  floor + a `#[cfg(feature="recursion")]` rotated branch (the in-browser prover must synthesize before/after
  `Cell` + rotation witnesses for the demo inspector). It does NOT block native-recursion grep-zero — but
  native grep-zero is NOT reachable until #1+#2+#3 land, because the v1 SYMBOLS stay live in those legs.

NET: the phase deliverable (grep-zero in recursion) is gated on ONE genuine ember-decision (blocker #2's
non-cohort behavior). Everything else is verified-ordinary engineering. A PARTIAL cutover (any subset of
1/2/3/4) leaves grep>0 in recursion AND ships RED (the v1 prover would be half-disconnected) — the mandate's
#1 forbidden outcome — so the tree is held GREEN + UNTOUCHED at HEAD (baseline `pbuild hardswap` of
circuit/sdk/turn/node = exit 0, "Finished `dev` profile") pending ember's call on blocker #2. Once decided,
the full cutover is a single coherent lane (items 1→3→2→4→delete), each persvati-green.

⚑ FIX-ROUND-2 (2026-06-14, deepest independent re-trace; one SCOPE-CORRECTION + one DECISION-REFRAME +
the recommendation INVERTED). Re-verified the four legs at HEAD, then traced two things the prior C7 entries
did NOT pin down — the result MATERIALLY enlarges item #3's scope and REVERSES the recommended ember answer:

  (A) SCOPE-CORRECTION — item #3 (recursion/aggregation) is NOT "drop a dead leaf"; it is a MANDATORY-leaf
      cutover across FIVE files. `proof_forest.rs::ForestNode.proof` IS `EffectVmP3Proof` (v1) — its only leaf
      (`circuit/src/proof_forest.rs:280`); `joint_turn_aggregation.rs::DescriptorParticipant.proof` IS
      `EffectVmP3Proof` (v1, `:130`) with `rotated: Option<RotatedParticipantLeg>` only ADDITIVE (`:143`; the
      in-file comment `:138` states the rotated leg "becomes mandatory" only "once present everywhere" — i.e.
      NOT YET). Same v1-leaf posture in `ivc_turn_chain.rs` (3 `EffectVmP3Proof` refs) + `joint_turn_recursive.rs`
      + `recursive_witness_bundle.rs`. So deleting `EffectVmP3Proof`/`generate_effect_vm_trace` FORCES, FIRST:
      make the rotated leg mandatory in all five, drop the v1 field, then fix every host-admission read
      (`joint_turn_aggregation.rs:130/139/192` "v1-leg-only constructor" no longer compiles). EXEC.3 point (c)
      flags this ("the recursion knots … their v1 cores delete only at C7") but the bucket-A manifest UNDER-COUNTS
      it as mechanical. This is a soundness-bearing recursion cutover lane in its own right — NOT a delete.

  (B) DECISION-REFRAME + RECOMMENDATION INVERTED. The prior entry recommended ember pick "commit-unproven"
      (route the non-cohort shapes — heterogeneous multi-cohort · non-synthetic-field cells · NoOp-only — to
      proof-pending/skipped) as "the smallest change, within the tolerated-degradation envelope." On re-trace
      that is the WRONG close and I withdraw the recommendation: commit-unproven WEAKENS the
      all-finalized-turns-carry-a-proof guarantee (ARGUS light-client unfoolability, the north star) for a
      WHOLE CLASS of REAL live turns — heterogeneous turns are ordinary (the SDK projector `convert_effects_to_vm`
      emits e.g. Transfer+SetField from a single call_forest; `sdk/src/cipherclerk.rs:5491-5527`), so this is not
      a degenerate corner but a standing production hole. Shipping it is precisely the regression the HARDSWAP
      mandate's #1 rule forbids ("NEVER SHIP RED … a broken HARDSWAP betrays the whole system"). The HONEST close
      PRESERVES the guarantee: make the rotated path TOTAL before deleting v1 — which means BUILDING (b1) rotated
      heterogeneous/multi-cohort proving (the rotated AIR is structurally ONE-descriptor-per-proof,
      `trace_rotated.rs:507` "EXACTLY the registry's 36 cohort members"; a mixed turn has NO rotated
      representation today) + (b2) a non-synthetic-field rotated witness (lift the
      `turn_proving.rs:353-357/445-448` `cell_is_synthetic_shaped`/`cell_matches_v1_prestate` gate) + (b3) confirm
      NoOp-only is unreachable on the finalized path (the SDK projector yields ≥1 cohort effect for any real
      actor turn — only the EXECUTOR-side bridge `effect_vm_bridge.rs:557` injects NoOp on an empty per-cell
      projection, a DIFFERENT projector not on the FullTurnProof path; CONFIRM, then it is a non-issue). (b1) is
      genuine unbuilt circuit work; it does NOT fit one verified-green phase.

  THE DECISION, SHARPENED: it is NOT "what should the non-cohort fallback do" (that framing presumes weakening).
  It is: **C7 = delete v1 ⇒ EITHER (Path-PRESERVE) build rotated coverage for heterogeneous + non-synthetic
  turns AND make the 5-file recursion stack's rotated leg mandatory FIRST (a multi-lane, multi-week
  circuit+recursion campaign, no crypto primitive, no further decision once chosen) — keeps the north-star
  guarantee intact; OR (Path-WEAKEN) ember explicitly accepts that heterogeneous / non-synthetic-field finalized
  turns commit WITHOUT a per-turn proof (proof-pending → skipped), shrinking the all-turns-carry-a-proof
  guarantee to the rotated-cohort-homogeneous-synthetic-cell subset — the smaller code change but a REAL
  north-star regression.** My recommendation (reversed from fix-round-1): **Path-PRESERVE.** The HARDSWAP ethos
  is l4v / green-or-bust; trading away the light-client's per-turn proof for a class of ordinary turns to make a
  delete land is the kind of "quick fix = debt hole" ember forbids. Path-WEAKEN is offered only because it is
  genuinely ember's north-star to spend or keep — it is not a deputy default, and it must be a DELIBERATE,
  documented narrowing of the ARGUS claim, not a silent side effect of a deletion.

  HELD GREEN (unchanged): tree UNTOUCHED at HEAD; baseline `pbuild hardswap` of circuit/sdk/turn/node under
  `--features dregg-circuit/recursion` = exit 0, "Finished `dev` profile" (re-run this round). grep-zero NOT met
  in recursion (correct — v1 stays live across legs #1-#4 above). No fake-green via cosmetic rename (would
  launder grep-zero while the v1 prover stays the live prover for heterogeneous/non-synthetic/recursion turns).

## THE ROTATION FLIP — the irreversible tail (ember-COMMISSIONED, a4c7368ae; touches cell/+live registry+executor PI)

*(The genuinely-new long pole — staged producers + rotated trace builder + cell≡circuit
differential — is DONE and GREEN beside v1, no VK bump. Two MORE staged-additive stages landed
2026-06-13 (Opus, G3-authority + G4-cohort); what remains is the deliberate live-path rewrite +
flip:)*

### ⚑⚑ THE PRE-FLIP GATE — the REAL gate before the VK epoch (flip-executor inventory, 2026-06-14)

**⚑⚑⚑ NOW EXECUTING (2026-06-14, ember: "it's time, steel ourselves for the horrors" — workflows+agents authorized).**
THREE lanes running on DISJOINT files (STAGED-ADDITIVE, reversible behind `recursion`; the main loop reviews each
diff before it rides the VK epoch):
- **Wall A+B** (agent `a744069d109bf72b4` — `sdk/src/full_turn_proof.rs` + `turn/src/aggregate_bilateral_prover.rs`
  + the `WitnessedReceipt` struct). REFINED inventory (main-loop, deeper than the flip-executor's): the rotated
  path already sources the composed PI (`full_turn_proof.rs:1078`) but leans on v1 in THREE spots to sever —
  (A1) the rotated sub-proof's `vk_hash` is the V1 descriptor (`:1083` → `effect_vm_circuit_descriptor()` =
  "dregg-effect-vm-v1"); fix to the ROTATED descriptor (`rotated_descriptor_name_for_effect` @`:856`); (A2) the
  conservation leg reads `effect_pi[NET_DELTA_MAG/SIGN]` from the UNCONDITIONAL v1 `generate_effect_vm_trace`
  (`:1043`/`:1191`) — read net_delta from the rotated PI instead; (A3) then gate the v1 `generate_effect_vm_trace`
  to `rotation.is_none()` only. WALL B: `build_inner_rows_v2` (`:193`) PROJECTS the 49-felt schedule from
  `wr.public_inputs[..ACTIVE_BASE_COUNT]` (v1 PI) — add a native `Option<[BabyBear;49]>` `bilateral_schedule` on
  `WitnessedReceipt` (Option + projection-fallback so node/ stays unchanged), prefer it in `build_inner_rows_v2`.
- **Wall C** (agent `a9fe8d40eb8f1e999` — `node/src/blocklace_sync.rs` + `node/src/turn_proving.rs`). Thread
  `rotateV3WithNullifierPin` (39-PI, nullifier@PI[38], the `cc1e1399c` descriptor — the §EXEC.3(b) "38-PI lacks
  NULLIFIER" note is STALE) into the `(None,Some(nullifier))` freshness arm, staged behind `recursion`.
- **pg-dregg maturation** (agent `a71feb983ca8f43ce` — `pg-dregg/` standalone, parallel, zero flip collision):
  the durable-workflow API + restart pg18.

SEQUENCING (each gated green; the main loop drives): walls A/B/C land + reviewed → **the main loop populates
`bilateral_schedule` at the node/ WR producer** (`materialize_blocklace_artifacts`, DEFERRED til Wall C lands, to
avoid the node/ collision) → **the VK epoch (C5/C6) = THE MAIN LOOP's irreversible act** (v3Registry→default regen
+ re-pin ~58 SHAs/11 guards + #103 sovereign graduation + notify Step-2 felt-batch + FFI reseed + the ONE
VK/cell-commitment bump; §EXEC.3 recipe) → **C7** delete v1 + grep-zero (a Workflow fan-out) → the **Option-A
wasm-rotated prover** (LAST — gates C7's full grep-zero, not the native cutover) → persvati gauntlet → held push →
**devnet redeploy = EMBER's act** (fresh genesis). Prize: −65.6% proof size (350.5→120.4 KiB), verify 3.4× faster.

--- (original flip-executor inventory, for the record) ---

The flip was ATTEMPTED and correctly NOT TAKEN: the rotation DESCRIPTORS are all correct+green (lake
`Dregg2` 3922 jobs axiom-clean; `effect_vm_rotation_flip` 4/4 — the magnesium PROOF is DONE), but the
LIVE-PATH cutover is NOT. The earlier "flip-safe, all gates closed" was an OVER-CLAIM (rise-to-meet-the-
claim correction); §EXEC.3's "WHAT'S STILL GATED" was accurate and is UNMET. The staged tree is GREEN, NO
edits were made. Three walls + an architecture decision gate even C5-(1) and MUST close before the VK epoch:

- **WALL A — the composed-PI / VK-hash source.** `prove_full_turn` (`sdk/src/full_turn_proof.rs:1042`)
  calls `generate_effect_vm_trace` (v1, 186-col) UNCONDITIONALLY; the rotated leg is an ADDED sub-proof
  under `witness.rotation.is_some()`, and `CutoverFallback` (`full_turn_proof.rs:568`) is the live routing.
  CLOSURE: make the rotated PI the composed-PI / VK-hash source so the v1 backbone can go; retire
  `CutoverFallback`.
- **WALL B — the bilateral verify stops reading `effect_vm::pi`.** `verify_aggregated_bundle`
  (`turn/src/aggregate_bilateral_prover.rs:185`) reads `wr.public_inputs[..ACTIVE_BASE_COUNT]` (the v1 PI
  slice). CLOSURE: carry the 49-felt schedule block in the witnessed receipt so the bilateral verify no
  longer reads the v1 PI.
- **WALL C — the FLOW-B note-spend freshness arm threads the rotated nullifier descriptor.** The
  `(None,Some(nullifier))` arm (`node/src/blocklace_sync.rs:2667`) calls
  `prove_and_verify_finalized_turn_freshness` with NO rotation. The descriptor is READY
  (`rotateV3WithNullifierPin`); the gap is the live node wiring + composed-PI binding. CLOSURE: thread the
  rotated nullifier descriptor into that call site.
- **THE WASM-PROVER ember-DECISION (gates C7 grep-zero).** v1 is the `#[cfg(not(feature="recursion"))]`
  wasm verify+PROVE path; `wasm/src/runtime.rs:710` calls `generate_effect_vm_trace` directly (the
  in-browser prover uses v1 because the IR-v2 prover pulls p3-recursion/DFT crates that don't fit wasm). C7
  grep-zero (deleting v1) is PROVABLY IMPOSSIBLE while wasm proves in-browser on v1 (134 live refs to
  `generate_effect_vm_trace`, 108 to `EffectVmAir`). **DECIDED (ember, 2026-06-14): Option A** — build a
  wasm-fittable rotated prover (replace the p3-recursion/DFT deps for the in-browser path) so wasm proves on
  rotated TOO → v1 dies EVERYWHERE, true grep-zero, web keeps in-browser proving. A FRONTIER build added to
  the pre-C7 work (the DFT/recursion-in-wasm problem is real) — C7 deletion waits on it, not a follow-up.

Only after these four does C5 (the v3Registry→default regen + re-pin + FFI reseed) become the safe, one
irreversible VK-epoch act. (The ✅ wall-A / wall-B `DONE` entries further below are the C4-era bilateral
*interpreter* + node self-sovereign threading — necessary parts, NOT the same as these four backbone walls;
the backbone v1 path is still UNCONDITIONAL per WALL A above.)

- ✅ DONE (staged-additive, green): **G3 AUTHORITY-DIGEST DESIGN** — the v9 rotated commitment now
  binds the FULL authority state (not a subset). `cell/src/commitment.rs::compute_authority_digest_felt`
  folds permissions/VK/delegate/delegation/program/mode/token_id + visibility/commitments/proved/
  side-table roots + fields[8..16] into register r23 (Lean welds leave r23 free → the anti-ghost
  keystone binds it, ZERO Lean change). Three-way agreement (cell v9 / producer rotation_witness /
  trace generator) holds — all derive r23 from the same fn. Tooth: `v9_binds_full_authority_state`.
  Doc: ROTATION-CUTOVER §2a. (cell + turn, no VK bump, v8 untouched.)
- ✅ DONE (staged-additive, green): **G4 COHORT-GENERAL GENERATOR** — `trace_rotated::
  rotated_descriptor_name_for_effect` resolves any of the 26 cohort effects to its `*VmDescriptor2R24`
  (fail-closed for non-cohort), `effect_vm::trace::effect_selector` extracted as the single source of
  truth; `sdk::prove_effect_vm_rotated_ir2_with_caveat` is the cohort-general rotated prover. Teeth:
  `resolvers_cover_exactly_the_rotated_registry` (=26), `non_cohort_effects_resolve_to_none`. Doc:
  ROTATION-CUTOVER §2c.
- ✅ CLOSED (the cohort boundary). The rotated registry now has all **36** cohort members
  (`circuit/descriptors/rotation-v3-staged-registry.tsv`), incl. the two former residues
  `revokeCapabilityVmDescriptor2R24` (cap-crown graduated) + `customVmDescriptor2R24` (ProofBind IR
  constraint, 3c27a51cf). Every LIVE selector resolves via `rotated_descriptor_name_for_effect`;
  none is bricked by deleting v1. The cutover-EXECUTE lane (ROTATION-CUTOVER §EXEC) drives the flip.
- ✅ DONE (cutover **C1**, 2026-06-13): the SOVEREIGN proof-carrying matched pair (FLOW A,
  test-only) is rotated — `executor::verify_and_commit_proof` routes (under `recursion`) to
  `verify_and_commit_proof_rotated` (38-PI reconstruction + `verify_vm_descriptor2`, hand-AIR
  `EffectVmAir` RETIRED on this path); producer `cipherclerk::prove_sovereign_turn_rotated` mints
  the rotated `Ir2BatchProof`. New `dregg-turn`/`dregg-sdk` `recursion` feature (default-on; wasm
  `not(recursion)` keeps the v1 leg `verify_and_commit_proof_v1`). Green: `sdk/tests/
  sovereign_rotated_c1.rs` (accept + anti-ghost) + both feature configs compile. Two obstructions
  found+fixed (NOT papered): stored NEW commit must be the trace's PI 35 (welds from the v1
  sub-trace after-state, ≠ `compute_v9(after_cell)`); verifier undoes `execute.rs` PHASE 1 (fee
  debit + nonce++) to reconstruct the producer's pre-state (cross-checked by OLD_COMMIT/PI 34).
  RE-VERIFIED 2026-06-13 (fresh persvati build, not a self-report): `sovereign_rotated_c1` both
  tests green under `recursion`; `dregg-turn` compiles green under BOTH `--no-default-features`
  and default. MEASURED win (`effect_vm_ir2_size_measure`): v1 hand-AIR 358900 B (350.5 KiB),
  verify 16.8 ms → rotated IR-v2 123292 B (120.4 KiB), verify 5.0 ms — **0.344 ratio (−65.6 %
  size), verify 3.4× faster**, on TOP of the soundness win (multi-table batch verifier replaces
  the weak hand-AIR). Hygiene: removed a dead `use serde::Deserialize;` in `executor/mod.rs`
  (the WIP's `cfg_attr(recursion, allow(unused_imports))` had the condition backwards — the
  import is unused in BOTH configs; submodules import serde themselves).
  SEQUENCING NOTE — `verify_sovereign_witness_stark` (the OTHER live sovereign verify leg,
  `execute.rs:798`, the `sovereign_witnesses[].transition_proof` path) STAYS on v1 `EffectVmAir`
  for now and is deliberately OUT of C1: it has NO matched rotated producer (every LIVE producer
  sets `transition_proof: None` — `sdk/src/cipherclerk.rs:4861`, federation/*, peer_exchange; only
  `node/src/mcp.rs:6165` + the observability demo feed it). The C1 rotated producer emits
  `sovereign_witnesses: HashMap::new()`, so it never exercises this leg. Rotating its verifier in
  isolation = a verify-without-producer brick (the exact hazard the cutover brief warns against);
  it rotates WITH the FLOW B / witness producer (C3) or retires at C7, NOT before.
- ✅ DONE (cutover **C2**, 2026-06-13): prover-free `verify_vm_descriptor2` split. A `verifier`
  feature on `dregg-circuit` (`recursion = ["verifier", + recursion-prover crates]`) compiles
  `verify_vm_descriptor2{,_with_config}` + AIRs + `ir2_config` under `--no-default-features
  --features verifier` (no `prove_batch`/DFT link); `descriptor_ir2` module-gated
  `any(recursion, verifier)`, the whole PROVE surface (`prove_vm_descriptor2*`, `build_traces` +
  trace-fill helpers, `Ir2Traces`, `prove_batch`/`StarkInstance` + prover-only imports,
  `MIN_TABLE_HEIGHT`, test mod) `recursion`-only. `verify_batch` is prover-free + `from_airs_and_
  degrees(..).common` builds only symbolic `Lookups` (the IR-v2 AIRs have empty preprocessed).
  Verified on persvati: verifier-only lib (zero `descriptor_ir2` warnings) AND default lib both
  green. Files: `circuit/Cargo.toml`, `circuit/src/lib.rs`, `circuit/src/descriptor_ir2.rs`.
- ⚠️ HARD WALL (cutover **C3**, found 2026-06-13 — needs an ember architecture decision before C3
  can proceed): `prove_full_turn`'s effect-vm leg is an `EffectVmP3Proof` that THREE LIVE
  recursive-composition surfaces ingest / re-prove as the v1 **186-col** statement, so it cannot
  rotate to `Ir2BatchProof` and C7 cannot delete `EffectVmAir`/`generate_effect_vm_trace`/
  `EffectVmP3Proof` while they stand: (1) `circuit/src/ivc_turn_chain.rs` (lightclient
  `WholeChainProof`) — `prove_descriptor_leaf` re-proves `EffectVmDescriptorAir` over the 186-col
  recursion matrix via the recursion-fork in-circuit verifier (a uni-STARK leaf-wrap); (2)
  `circuit/src/joint_turn_aggregation.rs` (lightclient `DescriptorParticipant`) — aggregation AIR
  built on `EffectVmAir::new`; (3) `turn/src/aggregate_bilateral_prover.rs` (node bilateral bundle,
  `blocklace_sync.rs:3265`/`mcp.rs:6587`) — outer STARK via `EffectVmAir` + the 204-PI slice. The
  flat FLOW B quartet (`prove_full_turn`/`verify_full_turn`/node-`turn_proving`/
  `verify_sovereign_witness_stark`) is INSEPARABLE — it mints the very proof they ingest. **Decision
  needed:** how does the whole-history recursion (and joint-turn aggregation) wrap the rotated
  MULTI-TABLE `BatchProof` (no batch-proof leaf-wrap/in-circuit-verifier exists in the recursion
  fork; the present leaf-wrap is uni-STARK only) — OR re-architect it — OR freeze a legacy v1 leaf
  for historical turns while live turns rotate (keeps v1 alive ⇒ contradicts grep-zero). Detail in
  ROTATION-CUTOVER §EXEC C3 ⚠. (`proof_forest.rs` has no non-test consumer; dies at C7.)
- ✅ DONE (cutover **C3**, 2026-06-13): the wall FELL via option (a). The rotated multi-table
  `Ir2BatchProof` leaf-wrap is GREEN (`ivc_turn_chain::prove_descriptor_leaf_rotated[_with_config]`,
  `RecursionInput::NativeBatchStark`, fork `72ffc56`/circuit `bbea731e7`) AND two rotated leaves
  AGGREGATE + self-verify at `ir2_leaf_wrap_config` (`983255781`,
  `rotation_batchstark_leaf_smoke::two_rotated_leaves_aggregate_at_wrap_config`). The recursion
  ARCHITECTURE is proven (wrap + aggregate).
- ✅ DONE (cutover **C4 recursion**, 2026-06-13, this lane — WIP, uncommitted): the two recursion
  consumers are REWIRED onto the rotated leaf-wrap. `DescriptorParticipant` gains a rotated leg
  (`rotated: Option<RotatedParticipantLeg>` {Ir2BatchProof<DreggRecursionConfig> + EffectVmDescriptor2
  + 38-PI}, `joint_turn_aggregation.rs`); `ivc_turn_chain::prove_turn_chain_recursive_rotated` +
  `prove_chain_core_rotated` + `generate_chain_trace_rotated` (reads rotated commits PI 34/35) and
  `joint_turn_recursive::prove_joint_turn_recursive_rotated` + `prove_joint_core_rotated` +
  `joint_turn_aggregation::recursion_binding_trace_descriptor_rotated` mint leaves via
  `prove_descriptor_leaf_rotated_with_config(.., ir2_leaf_wrap_config())` and run the whole tree at
  the wrap config. The v1 cores stay (deleted at C7). Circuit lib+tests+lightclient build GREEN. The
  two consumers are lightclient setup/demo-invoked (no node/sdk production loop folds a chain).
- ✅ DONE (cutover **C4 FLOW-B SDK leg**, 2026-06-13, this lane — WIP, uncommitted): `FullTurnWitness`
  widened with `rotation: Option<RotationTurnWitness>` (ungated — always-available types); when present,
  `prove_full_turn` proves the effect-vm leg via `prove_effect_vm_rotated_ir2_with_caveat` and attaches
  `"effect-vm-rotated"` (a multi-table `Ir2BatchProof`); `verify_full_turn{,_bound}` gains the
  `"effect-vm-rotated"` arm (`verify_effect_vm_rotated_with_cutover`, selector-bound over the 36-member
  cohort) + a rotated-aware commit binding (the rotated 38-PI is the v1 prefix `[0..34)` + 4 pins, so
  OLD/NEW_COMMIT at 0/4 bind unchanged). HONEST BOUNDARY (named, not degraded): the rotated 38-PI does
  NOT carry `NOTESPEND_NULLIFIER` (offset 198), so a note-spending turn with a freshness binding is
  REFUSED on the rotated leg and must use v1 until the rotated note-spend descriptor exposes the
  nullifier in-PI. sdk (default + no-default) + node build GREEN. The 2 node `turn_proving` callers set
  `rotation: None` (byte-identical v1 default) — threading the real producer witnesses from the live
  node turn (the Cell/Ledger/nullifier_root/receipt_log → `rotation_witness::produce`) is the next node
  step.
- ✅ DONE (cutover **C6**, 2026-06-13): the cell commitment is ALREADY v9 LIVE
  (`CANONICAL_COMMITMENT_CONTEXT = "…v9"`, the cap-crown flag-day `53c6e417c` bumped it). This lane
  CLEANED the stale "v8 is LIVE / do NOT bump" comment at `cell/src/commitment.rs:628`. The cell≡circuit
  v9 differential (`live_cell_v9_equals_circuit_state_commit`) already guards byte-identity.
- ✅ RESIDUE RESOLVED: the rotated registry has all **36** cohort members incl.
  `revokeCapabilityVmDescriptor2R24` (graduated by cap-crown) + `customVmDescriptor2R24` — no v1-only
  descriptor remains (`cut -f1 rotation-v3-staged-registry.tsv | wc -l` = 36).
- ⏳ REMAINING to grep-zero. **UPDATE 2026-06-13: walls (A) + (B) are now ✅ DONE + committed
  (`b0baf026c`) — see the wall-A / wall-B `✅ DONE` entries below. (A)'s only residual is the two
  SIBLING hand-AIRs `CrossSideExistenceAir` + `BundleTreeFoldAir` in the same file (they do NOT read
  `effect_vm::pi`); their Lean-emission lane ✅ LANDED (`92b41acce` — both emitted axiom-clean, found
  PURE not recursion; the hand-AIRs are now layout-of-record, deletable at C7). The remaining grep-zero
  walls are now just (C) + (D). **✅✅ ALL COHORT EFFECTS NOW ROTATE — the FLOW-B rotation campaign is COMPLETE
  and FLIP-SAFE (2026-06-14):** NOTE-SPEND (`cc1e1399c` — nullifier at PI[38], 39-PI, + the single-spend per-row
  double-spend GUARD, a model-found bug); CAPABILITY (`f967f39b0` — `rotation_witness_for_capability` from the REAL
  `full_turn_pre_cell`, binds the real authority digest r23, the over-grant tooth survives rotation —
  `cap_over_grant_refused_on_rotated_leg`); SETFIELD + BRIDGEMINT (`e9d6e357e` — the model found 3 real descriptor
  mismodels: nonce-passthrough-vs-TICK, payload@param0-vs-param1, ungated-write + `SEL_SET_FIELD=54`-is-`BALANCE_LO`,
  all enforced-fixed); SOURCE-COHERENCE (`05fe8a500` — the per-effect SetField/Mint SOURCE descriptors reconciled to
  runtime, the rotated tick-faces proved EQUAL to the source `:= rfl` so the registry routing is no longer a bypass
  of a buggy source; FULL library 3927-job axiom-clean; JSON byte-identical so the live wire is UNTOUCHED). The
  dynamic `setFieldDynV3` is proven STRUCTURALLY UNREACHABLE (a `field_idx≥8` SetField panics in v1 trace-gen before
  any rotated prove) → coherence-only, NOT a flip-blocker; the node v1-fallback predicate is REMOVED. **The model
  has STOPPED finding flip-blocking DESCRIPTOR gates (the magnesium PROOF is done); the LIVE-PATH cutover is NOT
  ready — see the ⚑⚑ PRE-FLIP GATE at the top of this section: walls A (backbone `prove_full_turn` still calls
  v1 unconditionally + `CutoverFallback` live), B (`verify_aggregated_bundle` reads the v1 PI slice), C (the
  note-spend freshness arm has NO rotation) + the wasm-prover ember-decision MUST close before the VK epoch.
  The "flip-safe, all gates closed" framing here was an OVER-CLAIM (corrected 2026-06-14).** The flip remains
  HELD for ember at the redeploy point-of-no-return, behind those four. Sole non-blocking residue: the unreachable
  `setFieldDynVmDescriptor2` slot-column (`SLOT:=1` vs runtime field_index@param0) — a separate `EffectVmEmitV2`
  coherence lane.** Original (A) plan, for the record: **(A) the BILATERAL rotated outer AIR** — DECISION =
  BUILD, emit from Lean (law #1). `bilateral_aggregation_air.rs::BilateralAggregationAir` is a plain
  hand-authored `StarkAir` reading `wr.public_inputs[..ACTIVE_BASE_COUNT]` and the bilateral-schedule
  PI offsets (`effect_vm::pi::{TURN_HASH_BASE 25..IS_AGENT_CELL 73}`). It does NOT ingest an
  `EffectVmP3Proof` — it reads the witnessed-receipt's bilateral-schedule PI layout (a ~75-felt contract
  living inside the v1 PI module). Grep-zero needs a Lean-emitted aggregation descriptor (a NEW IR2
  constraint kind — a general two-row `windowGate` for the cumulative-sum CG-4 — since `EmittedExpr`
  gate bodies see only `local`, and the WR PI vector restructured so the bilateral schedule is fed
  independently of the rotated effect-vm 38-PI). Real from-scratch Lean build (`EffectVmEmitBilateralAgg.lean`).
  LIVE via node HTTP `/turns/aggregate` (`api.rs:1723`) + MCP `dregg_bilateral_action` + WASM + the
  `teasting/tests/multi_cell_cross_fed_binding.rs` cross-federation gauntlet. **(B) node FLOW-B producer
  threading** (the 2 `turn_proving` callers → real rotation witnesses). **(C) the ~70 plain-produce/verify
  + test/demo call-sites** (node mcp/api/prove_pool, the ~40 v1 test harnesses). **(D) C5 regen**
  (v3Registry→default, re-pin, reseed FFI) → **C7 DELETE** v1 (`effect_vm_p3_full_air.rs`, `effect_vm/air.rs`,
  186-col `generate_effect_vm_trace`, `ACTIVE_BASE_COUNT`, `CutoverFallback`, `lean_descriptor_air.rs` v1)
  + grep-zero per ROTATION-CUTOVER §EXEC grep_zero_checklist.
- ✅ DONE (wall A — the BILATERAL Rust interpreter, 2026-06-13, this lane — WIP, uncommitted): the
  bilateral aggregation now proves+verifies through the LEAN-emitted descriptor (law #1), retiring the
  hand-AIR on the live path. (1) **`descriptor_ir2.rs` grew the `windowGate` primitive**: a `WindowExpr`
  enum (`Loc`/`Nxt`/`Const`/`Add`/`Mul`, the two-row twin of `LeanExpr`) + `WindowGateSpec` + the
  `VmConstraint2::WindowGate` variant + a `parse_window_expr`/`"window_gate"` decode arm (wire
  `{"t":"window_gate","on_transition":bool,"body":{loc/nxt/const/add/mul}}`) + `JsonCursor::parse_bool`
  (in `lean_descriptor_air.rs`, shared infra) + the AIR `eval` arm (`on_transition` → `when_transition()`,
  else every-row) + the `check_descriptor2` bounds arm. The other 36 descriptors are byte-untouched. (2)
  **The descriptor artifact** `circuit/descriptors/dregg-bilateral-aggregation-v2.json` (6990 B, emitted
  from `emitVmJson2 bilateralAggDescriptor`; width 87, PI 23, 70 constraints, 2 window gates) + the
  accessor `bilateral_aggregation_air::bilateral_aggregation_descriptor()` + the decoupled-layout modules
  (`sched`/`agg`/`outer_pi_v2`, Lean-mirrored) + `schedule_block_from_inner_pi` (the 49-felt window
  `inner_pi[25..74]` re-based to 0) + `build_aggregation_trace_v2` + `prove_aggregation_v2`/
  `verify_aggregation_v2` (route through `descriptor_ir2::{prove,verify}_vm_descriptor2`). Teeth:
  `bilateral_descriptor_parses_with_lean_pinned_shape`, `schedule_block_offsets_match_v1_pi_window`. (3)
  **`aggregate_bilateral_prover.rs` rewired**: `prove_aggregated_bundle` builds the 87-col v2 trace (no v1
  PI buffer) + proves via the descriptor (postcard'd `Ir2BatchProof`); `verify_aggregated_bundle`
  deserializes + verifies via the descriptor + binds the shipped trace BY CANONICAL RECONSTRUCTION (re-derive
  the 87-col trace from the Turn + claimed schedule blocks, require equality — strictly stronger than the old
  commitment match) + the per-row schedule cross-check (step 5). The 7 in-file adversarial tests rewired to
  the descriptor path. **The descriptor path is `recursion`/`verifier`-gated**; the `not(recursion)` wasm
  build keeps a stub (returns Err — the bilateral demo there is optional, the single-turn proof stands). This
  RETIRES `BilateralAggregationAir` on the live path and grep-zeroes `ACTIVE_BASE_COUNT`/`effect_vm::pi` on
  the bilateral prove/verify (the only residual coupling, `SCHEDULE_PI_BASE = inner_pi::TURN_HASH_BASE`, is a
  single offset constant, retired when the rotated WR carries `sched` natively). VERIFIED: circuit
  `--features verifier` green; `dregg-turn` lib green (FFI link). NOTE: `CrossSideExistenceAir` +
  `BundleTreeFoldAir` (the CG-5 cross-side-existence + proof-of-proofs hand-AIRs, same file) are a SEPARATE
  soundness layer that does NOT read `effect_vm::pi` — they stay as custom-STARK AIRs (a future Lean-emission
  lane); retiring the whole `bilateral_aggregation_air.rs` FILE is gated on emitting those two too.
- ✅ DONE (wall B — node FLOW-B producer threading, 2026-06-13, this lane — WIP, uncommitted): the live
  node self-sovereign turn proves ROTATED. New `sdk::prove_turn_self_sovereign_rotated` (+ `RotationTurnWitness`
  re-export) forwards the rotation witnesses into `prove_full_turn`'s rotated effect-vm leg.
  `turn_proving::prove_and_verify_finalized_turn` gained a `rotation: Option<RotationTurnWitness>` param +
  `rotation_witness_for_self_sovereign` (builds the before/after witnesses from the REAL pre/post `Cell` +
  a single-cell ctx-ledger snapshot + the empty nullifier root + the receipt-hash log, mirroring the C1
  sovereign path). SELF-VALIDATING GATE: returns `Some` only when the actor cell is representable by the
  cap-less `CellState::new` pre-state (balance/nonce match · all fields zero · empty c-list) — so the
  rotated leg's OLD_COMMIT (PI 0, the v1 prefix) agrees with the v1 leg `verify_full_turn` checks; any
  divergence falls back to v1. `blocklace_sync.rs` captures the pre-execution `Cell` (`full_turn_pre_cell`)
  and wires the `(None,None)` self-sovereign arm. The FRESHNESS (note-spend) + CAPABILITY arms stay v1 by
  design (the rotated 38-PI omits `NOTESPEND_NULLIFIER` at offset 198 — the C4 honest boundary). 5 test
  call-sites + the live call-site updated.
- ⏳ REMAINING (wall C + C5/C7): the ~70 plain-produce/verify sites are CONCENTRATED in
  `sdk/full_turn_proof.rs` (the impl) + `node/turn_proving.rs` (27) + tests/perf/wasm/verifier — most need
  NO edit now (they pass `rotation: None` = byte-identical v1; the flip to rotated-default is the C5 regen
  act). The precise C5/C7 readiness package is in ROTATION-CUTOVER §EXEC.3 (regen recipe + deletion list +
  what's still gated). The VK epoch is the MAIN-LOOP cutover-settle (must batch with the notify Step-2
  felt-encoders into ONE VK bump — docs/NOTIFY-CASCADE.md).

## Metatheory closures (Lean-side, lane-sized — tails of landed work)

- ASSURANCE §5 Stage-1 / CRITICAL-2 codec-in-TCB: the LEAN half is now CLOSED — `Dregg2/Exec/FFI/Refine.lean` proves `execFullForestAuthStep` (the `@[export dregg_exec_full_forest_auth]` body) REFINES the model (`export_refines_on_parseable`/`_endToEnd`, composed with the existing `CodecRoundtrip.parseWWire_encode`), so the turn/effect wire codec is inside the proof (pinned in Claims §28b). RESIDUAL = the RUST codec, two named obligations, NOT closed: (1) **translation-validation of `dregg-lean-ffi/src/marshal.rs`** — a 2231-line hand-rolled byte-for-byte mirror of the Lean grammar (`marshal_turn_hosted` emit at `marshal.rs:617`; `unmarshal_result` decode at `:1710`), upheld TODAY only by `dregg-lean-ffi/src/marshal_roundtrip.rs` differential vs the real FFI symbol — the obligation is `marshal_turn_hosted(w) = encodeWWire(lift w)` as a theorem (generate the Rust from Lean, or a verified-Rust mirror), not a test corpus; (2) the **Lean→C / `libdregg_lean.a` link** boundary (no binary-correspondence statement that the linked `.a` IS the `@[export]`ed Lean) — the seL4 C-to-binary analogue. Both are the §5 Stage-1 remainder; obligation #1 is the sharper "translation-validation" one. → dregg-lean-ffi/, post-rotation (disjoint from the proof-wire flip).
- Argus joint-AIR fold (Silver→Gold layer: per-leg descriptors folded; not an Argus/ statement).
- Coeffect dst-liveness (named in the 4dd84a3ae audit; outside the four apex modules).
- BiorthRelational: threshold-D iff at Shamir t-of-n (proved at 2-of-2 additive); n-ary trace statement (reduced to the adjacent-step atom).
- Trustline: `settled`-era pureCredit — Lean has both collateral points; the Rust pureCredit realization (issuer-well draws) is open (7da845758 divergence 1-as-Rust).
- Quorum unification (#170) consumer migration: `BlsQuorumCert.lean`/`EpochReconfig.lean` still transcribe the historical `n−⌊n/3⌋` + carry `StrictBft`; `MembershipSafety.lean` still has the `n=0↦0` guard. The unified `supermajorityThreshold` Lean twin LANDED (QuorumThreshold.lean) — migrate the consumers onto it (bls_quorum_diff.rs/epoch_diff.rs/membership_safety_differential.rs pin the relations until migration).
- Channels delegation_epoch wire carrier: the Lean-producer/wire path has no per-cell `delegation_epoch` carrier yet (a `DelegationEpochEquals` program evaluated there fails closed — wire lockstep before channels ride the producer); pre-atom channel cells keep the old program (no live-cell program-upgrade verb).
- Channels CountGe tails: per-element approval binding (exhibited ≠ "approved THIS turn" — the actor-bound approval-slot ceremony must write the quorum commitment slot before `councilGated` replaces `senderIs admin` in the deployed program); CountGe AIR projection (witness-side scalar only).
- Cell-program grammar atoms — Rust mirror (cutover-settle lockstep, NOT a separate edit): three new `Exec/Program.lean` atoms LANDED axiom-clean (apps gaps 2/3/4) and need their `cell/src/program.rs` twins APPENDED (variant-index-based, fail-closed, mirroring the Lean evaluator) at the next program.rs cutover-settle: (1) `SimpleStateConstraint::SenderMemberOf { members }` — sender ∈ literal id-set, reads `ctx.sender` (the clean multi-admin form of `AnyOf[SenderIs…]`; `MissingContextField` on no sender); (2) `StateConstraint::AffineDeltaLe { terms, c }` — `Σ cᵢ·(new[fᵢ]−old[fᵢ]) ≤ c`, reads BOTH old+new (a real multi-field budget-delta gate; needs an `affine_delta_sum` over the pre/post state, fail-closed on any absent term either side); (3) `SimpleStateConstraint::BalanceDeltaLte { max }` / `BalanceDeltaGte { min }` — `new.balance−old.balance` rate gates on the sealed kernel balance, read the executor's pre-turn `old_balance` + post-turn `new_balance` (fail-closed on an absent endpoint; the executor must expose the PRE-turn balance to `evaluate_constraint_full`, the `TurnCtx.balanceBefore` twin — today the ctx carries only post). Lean keystones: `evalSimpleCtx_senderMemberOf_iff` · `evalConstraint_affineDeltaLe_iff` · `evalSimpleCtx_balanceDeltaLe_iff`/`_balanceDeltaGe_iff`. COST-class (§8, honored in the atom docs): all three are the BOUNDED/ordering pole EXCEPT `senderMemberOf` which is i-confluent-FREE (single-turn-context predicate). NOTE: `BalanceDeltaGte`/`BalanceDeltaLte` SUPERSEDE the flash-well "relative-balance atom" HORIZONLOG item below (its Lean twin is now this landing). → cell/, post-rotation (variant-index APPEND keeps factory VKs / content addresses byte-identical, per CELL-PROGRAM-LANGUAGE §2).

## Node / runtime closures

- **Stage-5 consensus de-vac (Klein/HIGH-6) — `docs/STAGE5-CONSENSUS-DEVAC.md`.** LANDED: the running-node witness that consensus runs at n>1 — `scripts/devnet-n3-ordering.sh` + `node/tests/three_node_ordering_rule.rs` boot 3 REAL nodes in `--federation-mode full` (3-validator genesis, supermajority(3)=3) and assert [A] full-mode multi-party tau path engaged + [B] cross-node block exchange over the real gossip wire (both PASS). Verified: the Lean BFT model is NON-vacuous (`bft_safety` is adversary-parametrized, liveness reduced to a DLS88/HotStuff `Pacemaker`; the empty-adversary inhabitant is only a satisfiability witness) and the tau rule faithfully refines the Rust (`BlocklaceFinality.lean`). **✅ S5-1 CLOSED (`ed35b23b2`, 2026-06-14):** the running node now COMMITS a turn through the rule at n≥2 — `three_node_ordering_rule.rs` green under `DREGG_TEST_REQUIRE_FINALITY=1` (4/4+3/3); `devnet-n3-ordering.sh REQUIRE_FINALITY=1` → [C] CONVERGED `latest_height 1 1 1` at n=3 (supermajority(3)=3, the strongest case). FOUR measured defects closed (the doc named only dissemination): (1) the Dandelion privacy-STEM misroute → `publish_eager` direct full-payload push to all committee peers; (2) a CHAIN-not-round-synchronous DAG (one creator/round → `is_super_ratified` never fired) → round-disciplined production (the exact `build_rounds` shape `tau` finalizes); (3) THE root cause = HALF-DUPLEX connections (gossip read only INBOUND streams → the last-booted node could send but never receive → deadlock under supermajority==n) → spawn `serve_connection` on outbound too (~50%→12/12) + QUIC keep-alive + a `Frontier` liveness nonce + a connectivity gate; (4) a turn-execution double-apply once finality fired (faucet eager-exec → nonce-replay / dest-not-found on peers) → faucet scratch-clone in multi-party mode + `execute_finalized_turn` materializes a missing Transfer dest as a remote stub. FOLLOW-UP (NOT blocking, devnet-correct today): a production-hardening pass on faucet/finalized-execution cell-provisioning semantics → node/api + execute_finalized. Then S5-2 live commit refinement, S5-3 #170 quorum-consumer migration, S5-4 consensus leg of the composed apex, S5-5 equivocator Lean↔Rust differential pin, S5-6 finality-on-demand (`docs/CONSENSUS-FLEX.md`). → net/gossip + blocklace/dissemination + node/blocklace_sync.
- **pg-dregg Tier-C proof-attest — S1+S3 DONE, only the node producer (S2) remains.** The whole-chain IVC proof now crosses the SQL boundary for real: `circuit::ivc_turn_chain::WholeChainProofBytes` + `verify_turn_chain_recursive_from_blobs` (S1) and pg-dregg's `tier-c` leg wiring the REAL verifier (S3) are LANDED and green — the byte round-trip + tamper teeth pass (`circuit/tests/ivc_turn_chain_rotated.rs::whole_chain_proof_bytes_roundtrip_and_tamper`, 428s real fold), and the pg-dregg admit/refuse polarity is proven (`pg-dregg/tests/tier_c_real_proof.rs`, `--features tier-c`, ignored real fold). The fork (`emberian/plonky3-recursion`) needs NO edit: at the pinned rev `72ffc56` `BatchStarkProof` already derives `Serialize/Deserialize` (`#[serde(bound="")]`) and the binding `Proof<SC>` rides the pinned Plonky3 rev's serde. REMAINS = **S2, the node-side PRODUCER** (named in `pg-dregg/src/attest.rs` + `turn_proofs.rs` + `docs/PG-DREGG.md §10.2`): when finality advances, fold the new finalized turns (`prove_turn_chain_recursive` / `fold_two_turns`) and write the serialized transport + window bounds into `dregg.turn_proofs(lo, hi, genesis_root, final_root, proof bytea, vk)` the SRF reads. A real `tier-c` `ChainFolder` impl replaces `turn_proofs::StandInFolder`. → node + pg-dregg, post-rotation.
- Stale-cap c-list sweep (channels 72d43dc64 residue): epoch-step turn should `RevokeCapability` superseded grants. STILL OPEN — a real verb gap, NOT a quick fix: `member_cap_grants` installs into each MEMBER's c-list, while `RevokeCapability {cell,slot}` removes from a cell's OWN c-list; sweeping a departed member needs cross-cell `Delegate` authority the operator doesn't hold. `RevokeDelegation` epoch bump already DARKENS prior-epoch group caps at admission (R7 `CapabilityStale`) → this is c-list GC (storage), not soundness. Honest closure = a new verb shape (member-initiated self-revoke or group-scoped revoke authority). → node/turn, post-flip.
- Adjudication: bond cell → program-toothed obligation cell; tau-exclusion via a membership cell (court is the value leg only; 460d4d6bd residues). STILL OPEN — bond is a plain operator cell, not yet deployed via the obligation factory; deferred to AFTER the FLASH-WELL/blueprint `obligation_factory_descriptor` lands+verifies, then `post_bond` deploys via the factory in one slice. (That pattern now landed — unblocked for a future lane.)
- Storage: erasure coding + dedup-beyond-content-addressing — IN-CRATE half closed (storage/src/availability.rs, 10 tests). REMAINS: the node put/get HTTP route (gated by storage-gateway-mandate cell) can now CALL the in-crate availability route — the "weld to the shell" half. → node, post-flip.
- Trustline payment-channel parity: channel close (TL_STATE_CLOSED residual-escrow return) · one-factory collateral parameter · MCP `dregg_extend_trustline` · remote-silo pubkey registration (n=1 collapses it) · multilateral rippling (TRUSTLINES.md §7).
- Trustline pureCredit HTTP lane: node OpenRequest has no `collateral` field → HTTP open is fullReserve-only; `trustline_service::parse_collateral` is dead (`#[allow(dead_code)]`+TODO(collateral-axis)). Rust semantics+SDK exist; wiring the request field is the lane. → turn/node.
- Hosted-operator epoch-key custody posture (sovereign-member groups ride the SDK noun client-side; channels residue — partly an ember-decision).
- Divergence-ledger doc churn: `turn/tests/rust_lean_divergence_finder.rs:684` overwrites the git-tracked `metatheory/docs/rebuild/_RUST-LEAN-DIVERGENCE-LEDGER.md` on every run, dirtying trees + blocking persvati pushes — emit to a build-artifact path (or commit deliberately). One-line fix. → turn/ (off-limits this run; STILL LIVE, tree dirty at HEAD).
- CLI `config init` not path-injectable: `cli/src/config.rs::config_path()` hardcodes `~/.dregg` → `dregg config init` mutates real home, preflight can only gate read-only `config show`. Honor `DREGG_HOME`-style override, then restore a hermetic preflight `cli_config_init` check. → cli/.
- node recovery overlay first-writer-wins bug (surfaced by the snapshot lane): `node/src/state.rs` recovery uses `insert_cell` (strict insert), so a post-checkpoint write to a cell the checkpoint ALREADY holds is silently dropped; the convergence root-mismatch only LOGS, does not fail closed. Fix = `upsert_cell` (the verified `CrashRecovery.upd` point-update needs remove-then-insert). → node/persist, post-flip.
- persist snapshot wire half: in-crate `ship_snapshot`/`apply_snapshot`/`apply_snapshot_verified`/`install_snapshot` LANDED green (persist/src/snapshot.rs, 7 tests, shape = CrashRecovery.lean). REMAINS: node-side `GET /snapshot/{from}` serve + joiner consume route so a fresh node bootstraps over the network. → node, post-flip.
- checkpoint-prune → commit-log compaction (§2.1): `prune_before` trims attested roots but commit-log records below a finalized checkpoint are never compacted (unbounded WAL). Add `CommitLog::compact_below(height)` preserving the index-audit invariant. → persist.

## Product surfaces (post-rotation)

- dregg-query: attested-queries feature only (Q2 of docs/EPISTEMIC-DATALOG.md) — NOT the full Datalog engine.
- Flash-well: `BalanceDeltaGte` relative-balance atom collapses the fee-ratchet ladder into one constraint + closes the donation-cushion residue; `Dregg2.Apps.FlashWell` keystones land with it. ✅ The Lean `Exec.Program` twin is now LANDED (`balanceDeltaGe`/`balanceDeltaLe`, axiom-clean, keystones `evalSimpleCtx_balanceDeltaGe_iff`/`_balanceDeltaLe_iff`); REMAINING = the Rust evaluator arm (see the cell-program grammar-atoms Rust-mirror item in Metatheory closures above — both ride the same program.rs cutover-settle) + the donation-cushion app keystone. The blueprint + SDK are AUTHORED (cell/src/blueprint.rs flash-well, sdk/src/flashwell.rs) but sprint-UNVERIFIED.
- Willow geometry for storage caps (3D area caveats, range reconciliation) — adopted design, not scheduled.
- range-based set reconciliation (§1.5/§3.2d, Willow shape): the shared primitive behind scalable anti-entropy (O(diff·log) not O(state)) AND storage partial-sync; cap chains as the pluggable authorization. Adopt the geometry, keep our proofs.
- eclipse hardening at scale (§1.1): peer_score buckets by SocketAddr today; add /24·/48 prefix + AS-diversity bucketing so a single cloud /24 cannot fill the eager set.
- availability route follow-ons (§3.1): swap XOR-prototype erasure (erasure.rs:11) for real Reed–Solomon; real Merkle-path chunk proof vs manifest.root (erasure.rs:226 is integrity-only).
- proving-modality dial #169 (§4.1): make prove-on-demand vs checkpoint vs eager a CONFIGURED axis, not hardcoded policy; settlement/pipelining depth (§4.2) parameterized by topology (n=1 = immediate settlement). Owns the PI 202/203 slots.
- Room-as-OS + delay-tolerant polis (docs/ROOM-AS-OS.md, docs/DELAY-TOLERANT-POLIS.md).
- **pg-dregg M3** (named 2026-06-13; M2 mirror + Tier-C chain-gate + the §11 write outbox LANDED + live on pg17/pg18; `node/src/pg_mirror.rs` `pg_live::PgSink` writes through over tokio-postgres incl. caps/memory in one txn). UPDATE 2026-06-13 (pg-dregg wide-safe lane, Opus): the **range-attest SRF SHAPE + the federation subscriber RE-VALIDATION are now BUILT** (`pg-dregg/src/attest.rs` + `mirror::revalidate_replicated_chain` + the `dregg_attest_range`/`dregg_attest_explain`/`dregg_install_federation`/`dregg_revalidate_replicated_chain` externs; core green, 50 `cargo test` + 2 new `#[pg_test]`s; docs/PG-DREGG.md §10.2.1 + §15 rewritten). What REMAINS — the genuinely NODE-/CIRCUIT-touching settle items (this lane does NOT touch node/ or circuit/): (a) **the outbox drainer** (§11.4): a node-side tokio task drains `dregg.submit_queue` as `dregg_kernel`, runs the submit gates + `execute_via_producer` (#171), resolves + mirrors back. (b) **the proof-gate circuit-link S1-S3** (§10.2.1): **S1** serialize `circuit::ivc_turn_chain::WholeChainProof` (it holds plonky3 proof objects, NOT serde today — needs derives + a versioned envelope); **S2** node-side proof PRODUCER (fold finalized turns via `prove_turn_chain_recursive`/`fold_two_turns` → write a `dregg.turn_proofs(lo,hi,genesis_root,final_root,proof bytea,vk)` table the SRF reads); **S3** the `tier-c` feature's `dregg-circuit` dep (`--features verifier`/`recursion`, **Lean-FREE** — §8.1) flips `attest::verify_serialized_proof` from the fail-closed stub to the real `verify_turn_chain_recursive`. Until S1-S3 the SRF attests NOTHING (safe direction, §10.3). Tier D (executor in-backend) stays the north star, gated on the pg/Lean process-model spike. The 4 §6/§13 ember-decisions now carry crisp recommendations (docs/PG-DREGG.md §13.1: instant-revocation default · typed-tables-lead/views-over-memory end-state · C-embed · spike-gated full-D else D-sidecar). UPDATE 2026-06-14 (pg-dregg proof-gate lane, Opus, `pg-dregg/src/` only): **S1 SETTLED + S2 BUILT; S3 reduced to ONE named circuit line.** **S1 (the serde verdict):** `WholeChainProof` is NOT serde as a whole — but its `root` is `RecursionOutput(pub BatchStarkProof, pub Rc<CircuitProverData>)`, and the verifier (`verify_turn_chain_recursive`) reads ONLY `root.0` + `binding_proof` + the 4 publics, NEVER the prover-only `Rc` `root.1` (verified by reading the fn body: it touches `proof.root.0`/`genesis_root`/`final_root`/`num_turns`/`chain_digest`/`binding_proof` and nothing else). `BatchStarkProof` AND `RecursionCompatibleProof` (a uni-STARK `Proof`) BOTH derive `Serialize`/`Deserialize` (`#[serde(bound="")]`). So the verify-sufficient subset IS fully serde → shipped as `attest::SerializedWholeChainProof` (a versioned postcard transport: `[version][root.0 blob][binding blob][3×root bytes][num_turns]`, real encode/decode + 5 fail-closed `cargo test`s). A `WholeChainProof` VALUE can't be rebuilt from bytes (the `Rc` is prover-only) — so the ONE remaining circuit-side line is a ~6-line `verify_turn_chain_recursive_from_parts(&BatchStarkProof, &Proof, publics, &vk)` split of the existing fn (which already uses only those parts). **S2 (BUILT):** `pg-dregg/src/turn_proofs.rs` — `TurnProofProducer<F: ChainFolder>` folds a finalized window into ONE `dregg.turn_proofs(lo,hi,genesis_root,final_root,proof bytea,vk)` row (DDL `mirror::ddl::turn_proofs()` + `dregg_install_turn_proofs`), with watermark discipline (dense, non-overlapping windows) + an anti-fabrication tooth (a folder can't claim wider coverage than the window) + the `dregg_attest_window`/`dregg_attest_window_explain` externs that look the proof up FROM the table. The circuit fold plugs in behind the `ChainFolder` seam (same discipline as `Producer`/`Projector`), so the default build stays circuit-free; 7 `cargo test`s prove the producer over a stand-in folder. **S3 (the flip):** `attest::verify_serialized_proof` now DECODES the transport in BOTH builds (real, tested), then under `tier-c` calls `verify_turn_chain_recursive_from_parts` (named, the dead-behind-cfg real leg) — off, fail-closed AFTER a successful decode (proven: a WELL-FORMED transport STILL attests nothing, not just garbage). VERIFY: 120 core `cargo test` green (12 new) + clean `cargo check --features "pg18 pg_test"`. The `cargo pgrx test pg18` RUNTIME is environmentally broken on this box (a pre-existing unmodified M1 pg_test fails identically at `framework.rs:217` initdb/locale — NOT this lane). REMAINING for the flip: add `dregg-circuit` (`verifier`/`recursion`, Lean-free) to the `tier-c` feature + the circuit-side `verify_turn_chain_recursive_from_parts` split — both circuit-side, mechanical; the transport decode + publics mapping are live + tested.

### SDK polyglot crypto/binding closures

- **sdk-ts organ-noun crypto closures** (named 2026-06-13; sdk-ts now mirrors two-nouns + organ-noun as thin typed clients, green): three crypto ops stay node/wasm-side (pure TS has no Poseidon2/X25519/STARK): (a) `mailbox-verify-dequeue-proof-in-ts` (re-run storage queue Merkle verify over a drained batch); (b) `channel-seal-open-in-ts` (X25519→HKDF→ChaCha20-Poly1305 epoch-key seal/open so a TS member decrypts the fan-out — example uses placeholder ciphertext today); (c) `attested-verify-in-ts` (`verify_full_turn` STARK + federation threshold-sig check so `AttestedQuery` returns a CHECKED verdict — the light-client crown, likely waits on a wasm `verify_full_turn` export). (a)+(b) are the first users of `@dregg/sdk/wasm`.
- **userspace-verify TS/Py binding** (named 2026-06-13; `dregg-userspace-verify/` landed green, 22 tests): expose `analyze()` to TS/Py so `sdk-ts`/`sdk-py` call it pre-submission. (a) cheap path: SDK serializes its forest to JSON, shells/WASM-calls `dregg-uverify --json`; (b) integrated: a `#[no_mangle]` FFI `uverify_analyze(json_ptr,len)->json` in a small cdylib, bound from TS (napi/wasm) and Py (ctypes/pyo3 — the bridge already links libdregg). `Assurance`/`Finding`/`Locus` are Serialize+Deserialize → wire shape settled; the lane is the glue + an SDK `analyze()` sugar at `.sign()`-time.
- **DreggDL node `POST /deploy` ingress** (follow-up to the landed `dregg-deploy` + its TS/Py bindings, a7734efcc/a49448d09): a node endpoint accepting a DreggDL doc → `dregg-deploy::check` (refuse non-conserving/amplifying up front) → lower + submit per-root turns → return receipt chain + resolved factory_vks/cell-ids. Static check = pre-submission gate; executor stays the trust boundary. `dregg-deploy apply` = the same flow SDK-side. → node, post-flip.
- **sdk-py self-contained wheel**: (carried — packaging the Py binding as a standalone wheel that bundles libdregg). → sdk-py.

## APPS-POLISH lane (starbridge-apps demo-worthiness)

- **compute-exchange/ + gallery/ stub dirs** carry only a `manifest.json` (no crate) — decide: build them or delete the stubs.
- **escrow-market follow-ups** (escrow-market, 12 tests green): (a) the no-burn equality is settle-scoped in `child_program_vk` but NOT in the executor-installed flat `state_constraints` (executor installs `Predicate(state_constraints)`, evaluated unconditionally — apply.rs); to enforce exact conservation on the settle turn, either teach factory-birth install to use the cell's `Cases` program (`child_program_vk`) OR add a settle-gated relational atom. Until then no-burn rests on `build_settle_action` emitting a balanced split. (b) real ledger-balance binding — ESCROWED/RELEASED/REFUNDED are slot integers, not moved balance; wire settle to a real value transfer (trustline/flashwell `.turn()`) for the organ-true version. → starbridge-apps/turn, post-flip.
- **userspace-verify integration point** (depends on the landed toolkit): escrow's `released+refunded==escrowed` conservation predicate is the first app-level customer for the static checks — lift it to a published checker. Same shape for agent-provenance `verify_chain` + bounty-board lifecycle monotonicity.
- **polis factory-birth co-location**: polis's executor-path teeth live in `sdk/tests/polis_*_e2e.rs`, not a `polis/tests/factory_birth.rs` like the other apps — co-locating a birth test makes it self-contained.
- **privacy-voting ballot unlinkability** (named in its README): the app gives one-vote-per-ballot + monotone tamper-evident tallies, NOT ballot/voter unlinkability (no mixnet/nullifier-set). True secrecy is a separate, stronger lane.

## HANDOFF READINESS (the pug bar — a stranger evaluates dregg as a finished, usable thing)

*(ember 2026-06-12: hand the system to pug to evaluate usefulness/usability for HIS purposes.
Everything here is judged by "works without ember in the loop.")*

- FRESH-CLONE BUILD: clone → documented steps → running node, no tribal knowledge. The FFI archive seeding (elan on PATH, lake build, seed-dregg2-closure.sh) is tribal-knowledge-heavy + bit US twice this session — it must be ONE documented command (or build.rs does it) with a loud, teaching failure mode.
- QUICKSTART re-verified against POST-ROTATION reality, every command actually run (it was verified pre-rotation; #110's closure predates the organs + rotation).
- The organs reachable as a STRANGER would: SDK two-nouns + trustline/channel/mailbox/storage nouns each with a copy-paste example that runs against a local node; error messages that teach.
- An evaluator's README: what dregg IS, what it guarantees (AssuranceCase in human terms), what it does NOT yet do (honest scope), the three things to try in the first ten minutes.
- The site/playground consistent with the shipped system (no stale pre-rotation surfaces).
- One real end-to-end story pug can run start-to-finish (two agents · trustline · channel · mailbox — money moves, messages flow, a removed member goes dark, every receipt checkable). The demo IS the evaluation artifact.

## Crypto / protocol artifacts (bounded, sequenced after the rotation)

- DKG ceremony-as-cell-app: rounds over blocklace broadcast + seal-pair channels + slashable complaints (core landed 29509149d; transport is the artifact). Slash itself defers to the court→obligation-cell lane (node-closures adjudication item).
- ECVRF per-agent sortition: LANDED (federation/src/vrf.rs — RFC 9381, sortition_select/verify_sortition, SDK surface in sdk/src/identity.rs). REMAINS: full compile+test gauntlet (authored in-sprint); ticket transport serde (byte codecs only); dalek `decompress` canonicality vs §5.5 unaudited; juror-seat binding of ticket pubkey → key-set opening is documented, not yet a checked verb.
- KERI identity event-log export: LANDED (node/src/identity_export.rs — portable KEL, route GET /identity/export/{cell}). REMAINS: full compile+test gauntlet; per-cell state-commitment openings against `ledger_root` (today the snapshot↔turn binding rests on the exporting node's commit log); cooling-window length check needs charter data.
- Proactive resharing anchored in epoch-transition certs; proactive-deletion requirements (dkg.rs NOTES).
- drand-style beacon chaining (only once heights can fork; one line in beacon_message).
- OCapN netlayer adapter (2–4 week artifact): the enabling `Netlayer`/`ocapn://` trait LANDED in captp (captp/src/netlayer.rs). REMAINS the adapter: Syrup codec + `op:start-session` handshake + descriptor translation onto our session/gc tables + a wire Goblins speaks → a Goblins peer holding a dregg sturdy ref.
- MLS/TreeKEM fan-out swap for channels (replaces only `seal_epoch_key_to_roster`; cell interface unchanged).
- VRF-grade public beacon (its own later effort; ORGANS §6).

## PRIVACY/OFFLINE-CELL lane

- **Rust private-participant turn role** (design + Lean model landed: docs/PRIVATE-OFFLINE-CELLS.md + Dregg2/Distributed/PrivateLeg.lean, keystone joint_turn_sound_with_private_legs, #assert_axioms-clean). To SHIP: a private-participant leg type in `coord/src/atomic.rs` — an AtomicForest participant whose contribution is (commitPre, commitPost, proof) not an applied action, with a commit-path verify-gate implementing MixedAdmissible (every private leg's STARK verifies + binds the shared jid); the AIR the `CarrierEncodesPrivLeg` hypothesis names (recKExecAsset + recStateCommit state-root opening, producible offline); state-root continuity across turns (commitPost[i]=commitPre[i+1], mirroring HistoryAggregation.ChainBound). Liveness out of scope (a dark private participant aborts the all-or-none turn). Crypto floor = STARK extractability (no new assumption). → coord/turn, post-flip.

## seL4 / DreggDL lane (design+scoping landed)

*(Scoping docs: docs/SEL4-EMBEDDING.md (bootable-image roadmap; THE blocker = libuv-free/IO-free
Lean leanrt+GMP on musl/seL4) + docs/CAPDL-POLYGLOT-DX.md (DreggDL = describe the cap graph once,
3 SDKs instantiate it). The dregg-deploy parser crate + TS/Py bindings + sel4 verifier-PD scaffold
ALL LANDED (a7734efcc / a49448d09 / 152e6b3a5). Remaining lanes:)*

- **sel4 cross-build tail** (verifier-PD scaffolded, `no-lean-link` PROVEN Lean-free at HEAD): the actual cross-build to `aarch64-sel4-microkit` (needs Microkit SDK + rust-sel4 toolchain, absent here) + `getrandom`-custom / `p3-maybe-rayon` serial-fallback for the bare target. → sel4/.
- **Lean runtime bottom-half port (THE blocker, weeks–quarter)**: IO-free, libuv-free `leanrt`+GMP so `libdregg_lean.a` links on musl/seL4. Blocks the **executor PD only** — the verifier PD is UNBLOCKED (`no-lean-link` proves it links Lean-free). Until the port, `no-lean-link` builds the node marshal-only (shadow-off) — bring-up scaffold ONLY, never the authoritative ship.
- **First rbg→seL4 port: `DirectoryFactory` → `seL4_Untyped_Retype`** (sel4/RBG-TO-SEL4.md): the smallest real port turning an rbg idea into a kernel-enforced mechanism (factory's slot-caveat becomes the Untyped retype template). Additive, NOT gated on the Lean-runtime blocker; belongs in a `sel4/factory-pd/` sibling once rust-sel4 is wired.

## STARBRIDGE-V2 (native gpui shell — embedded verified executor)

*(The master interface EMBEDS the real verified executor + runs a live local dregg world natively
— headless heart gpui-free + `cargo test`-able, 183 lib tests green; the window OPENS via gpui
`runtime_shaders`. Build-out lanes from docs/STARBRIDGE-V2.md coverage matrix:)*

- LANDED (2026-06-13, the fork-seam unblock + 4 capabilities): the `embedded-executor`
  feature now COMPILES (the local plonky3-recursion `[patch]` replicated into
  `starbridge-v2/Cargo.toml` — the standalone workspace did not inherit the breadstuffs
  root patch, so `dregg-circuit`'s `NativeBatchStark` reference failed to resolve). Then:
  **organ panels** (`organs::OrganSurvey` — trustline + flash-well LIVE cell-state decoded
  from the embedded ledger via the published `blueprint` slot constants; channel/mailbox/court
  surfaced HONESTLY as remote-path, kind·seam·route, never faked; ORGANS tab) · **whole-graph
  ocap delegation layout** (`graph::OcapGraph` — nodes/edges + MULTI-HOP reachability (BFS
  transitive closure = a cell's blast radius) + layered delegation-depth layout + cycle
  detection; GRAPH tab) · **proof-attach + STARK verification-status board** (`proofs::ProofBoard`
  — the three honest tiers verified-by-construction/executor-signed/STARK-attached + the route
  to the next; PROOFS tab) · **A2 swarm deepened** (`swarm::Swarm::run_atomic` = N-action
  atomic forest bundle all-or-nothing; `swarm::Swarm::bind_surface` = per-member cap-confined
  firmament SurfaceCapability pane). All gpui-free + `cargo test`-able; the three new tabs +
  ⌘K nav commands wired into the cockpit. (Fixed a pre-existing latent over-grant in
  `swarm_world()` exposed by the unblock — the test helper granted coord a cap to a worker it
  did not hold; now seeds both mandate caps at genesis.)
- **organ OPERATING verbs** (open/draw/repay/settle/close) — LANDED (`organ_ops::OrganDriver`,
  11 tests). The cockpit now DRIVES trustline + flash-well organs as REAL turns through the
  embedded executor (not just reflects them): each verb shapes the protocol effect sequence and
  commits it via `World::commit_turn`, with the REAL `dregg_cell::blueprint` per-organ program
  installed on the organ cell (via `World::set_cell_program`) so the executor's per-cell predicate
  gate (`execute_tree.rs`) enforces the invariant IN-PROTOCOL — an over-line draw is refused by
  the `FieldLteField(drawn ≤ ceiling)` tooth, a fee-evading flash-well borrow by the
  `StrictMonotonic(ratchet)` tooth, a touch on a closed organ by the lifecycle table (all
  asserted refused, not faked). The embedded single-custody collapse: the organ cell is born
  open-permissions, its own pubkey is its `SenderIs{owner}` governance root, and the operator-root
  installs the adopt-grant well-cap on the borrower — the SDK's `Trustline`/`FlashWell` dance
  collapsed to the single image (no dregg-core change — both organs are embed-core). Carried
  residue: the `AgentRuntime`-shaped bridge to the SDK handles themselves is NOT built (the verbs
  re-shape the SAME effect sequences against `World`'s `DreggEngine` rather than driving
  `dregg_sdk::trustline::Trustline` directly — one model, two surfaces, kept in step by sharing
  the blueprint program + slot constants).
- **N9 STINGRAY CEILING WELD** — LANDED (`swarm_budget::StingraySwarmBudget` + `Swarm::
  attach_stingray_budget`, 13 tests). The swarm's shared budget is now a REAL
  `dregg_coord::StingrayCounter` (the single-image shared pool: `n=1`, `f=0`, the one slice
  ceiling IS the pool `B`), wired the way the SDK's `runtime::set_budget_gate` attaches a
  `BudgetSlice`: every dispatch draw-checks its DECLARED fee against the pool BEFORE its turn runs
  (fail-closed `SwarmError::PoolExhausted` on a breach — the counter's gate, not a summation),
  and settles the ACTUAL metered cost after. The conservation invariant `total_drawn() == Σ metered
  across members` is the counter's own accounting (PROVABLE, not best-effort), bounded by `B`; the
  aggregate strip reflects the counter (`total_spent`), and the pool exposes the identical
  `BudgetSlice` the executor's `set_budget_gate` would attach (one model, two surfaces). This is
  the depth lift over N1's per-member FLOOR meter — simbi's "UI counter vs verified conservation
  bound" gap closed.
- **LIVE NODE connection** — LANDED (headless heart green; the gpui strip compiles). The wire
  client + model (`NodeClient::{Mock,Http}` + `src/model`) MOVED into the LIBRARY (gpui-free,
  `cargo test`-able) and gained a `live-node` feature (`native-full` + `sel4-thin` both enable it;
  pulls `reqwest`, whose blocking client needs no caller tokio runtime). `client::LiveNode::sync()`
  fetches `/status` + `/api/cells` and projects them into the SAME uniform `reflect::Inspectable`
  the embedded world uses (no parallel view path); `client::LiveNode::connect_stream()` spawns a
  BACKGROUND SSE reader on `/api/events/stream` that feeds the PURE `live_node::SseParser` and
  pushes decoded receipts onto an mpsc channel. The cockpit drains it each frame
  (`drain_live_stream`) and fires `cx.notify()` PER RECEIPT — the ReceiptInspector advances live,
  REPLACING the snapshot. `live_node::ReceiptFeed` is the cursor + bounded ring + resume model.
  The PURE layer (SSE parse · live reflection · receipt-feed cursor) is fully `cargo test`-able
  with byte fixtures (10 new lib tests; the reqwest byte-pull is the only `live-node`-gated part).
  `--node <url>` wires it through `main.rs` → `Cockpit::with_node`; a LIVE NODE strip in the rail
  header shows the remote producer/liveness/height + the live receipt feed head + resume cursor.
  Remaining for the WINDOW: pixels need the Metal Toolchain (host blocker below).
- **native deos AFFORDANCE surface** — LANDED (`src/affordance.rs`, 5 lib tests). htmx-on-crack with
  the firing→executed-turn SEAM CLOSED through the embedded executor (the thesis `starbridge-web-
  surface` could only MODEL — it has no embedded executor). `CellAffordance` (named effect-template +
  `AuthRequired` a viewer must hold) · `AffordanceSurface::project_for` (progressive ATTENUATION via
  the REAL `dregg_cell::is_attenuation`, `required ⊆ held`) · `fire` → `AffordanceIntent` (anti-ghost:
  an unauthorized actor is REFUSED, not run) · `AffordanceIntent::fire_through_world` hands the real
  `Effect` to `World::commit_turn` so the receipt is the EXECUTOR's own (`FireOutcome::Committed`) and
  a guarantee-violating fire (over-transfer) is REFUSED by the executor (`FireOutcome::Refused`) —
  both gates real, in-band. The window cap gating an affordance IS the firmament
  `Capability{Surface(cell)}` (a window); an affordance-fire is a cap-gated verified turn, the deos
  thesis native. The FRUSTUM-SNAPSHOT (rehydration) is also real: `AffordanceSnapshot` is TINY (the
  cell + the declared names, NOT the data); `rehydrate_for` re-expands it PER-VIEWER through the same
  `is_attenuation` gate (a narrow-cap viewer rehydrates a narrow interactive surface from the SAME
  snapshot; the live surface is the source of truth, so a dropped affordance does not rehydrate).
  (Cockpit affordance-PANEL: a follow-up; the surface + snapshot + their 5 tests are the heart.)
- **starbridge-web-surface LIVE receipt-stream PRIMITIVE** — LANDED (`starbridge-web-surface/src/
  receipt_stream.rs`, 11 tests; NEXT-WAVE.md item D). The standalone thesis crate (which MODELS
  surfaces, no embedded executor) gained `ReceiptStream` — a subscription over the node's
  `/api/events/stream` receipt feed so a surface's organs become LIVE reflections of the committing
  node, not snapshots. Built ON the genuine shapes (`dregg_query::ReceiptEventRow` envelope +
  the full `dregg_turn::TurnReceipt` the SSE `data:` carries; the dense `chain_index` cursor the
  node serves as `Last-Event-ID`; `Dynamics::since(cursor)` semantics). The NEW tooth over the
  cockpit's existing `ReceiptFeed` (which only DEDUPS by index, trusting the body): **forge-
  rejection** — `ingest` REJECTS an out-of-order frame (`IngestError::OutOfOrder`, a gap/rewind in
  the dense chain) AND a forged one (`IngestError::Forged`, body does not re-hash to its claimed
  `receipt_hash` via the REAL `TurnReceipt::receipt_hash`), and `verify_against(&AttestedRoot)`
  checks the whole delivered prefix against the federation's `receipt_stream_root`
  (`merkle_root_of_receipt_hashes`). `StreamedReceipt` is the `WorldEvent`-shaped item; the pure
  `ingest`/`since`/`verify_against` core is `cargo test`-able with NO runtime; `ReceiptStreamPoll`
  (`stream` feature, default) is the `futures_core::Stream` the gpui executor `.await`s. Verified
  NARROW: `cargo test -p starbridge-web-surface` green both `--no-default-features` (121 lib, pure)
  and default (122 lib, +the Stream poll test) + 4 integration.
  **FOLLOW-ON — the cockpit gpui-executor subscription (starbridge-v2, a DIFFERENT lane owns it):**
  re-point the cockpit's live receipt path (`starbridge-v2/src/{live_node,client,cockpit}.rs` —
  the `ReceiptFeed` + `drain_live_stream` + `cx.notify()` wiring) at THIS verifying primitive, so a
  cockpit reflecting a REMOTE/untrusted node gains forge-rejection (today's `ReceiptFeed::ingest`
  trusts the body); drive `ReceiptStreamPoll::poll_next` on gpui's async executor (`cx.spawn`),
  storing the waker on feed so a fed `ingest` wakes the poll (the no-op-waker test shows the SHAPE;
  the real waker is the cockpit's). Single-source the two `ReceiptEvent` mirrors (this crate's
  `ReceiptEnvelope`/`ReceiptEventRow` + `starbridge-v2/src/model::ReceiptEvent`) under the named
  `dregg-wire-types` extraction below while there.
- **native federation/remote-node panel** (the LIVE NODE connection above is the wire; a richer
  multi-peer federation panel + the channel/mailbox/court LIVE reflections ride a connected node).
- **seL4 framebuffer backend** — a gpui renderer targeting a framebuffer cap (SEL4-EMBEDDING end state) + **seL4 channel transport** (a `NodeClient::Channel` over an seL4 endpoint, same contract over IPC not TCP).
- **single-source wire types** — replace `starbridge-v2/src/model/` hand-mirrors with a shared `dregg-wire-types` crate depended on by both node + shell.
- **finish-the-window (HOST gap, not a crate defect)**: the runtime-shader path opens the window; the offline Metal Toolchain download is blocked by a damaged Xcode `DVTDownloads.framework`. The remaining ahead-of-time-shader option = provision the Metal Toolchain on a healthy Xcode.

## DREGG-ANALYZER (forensic/observability trace analysis)

*(New crate dregg-analyzer/ — ingests CAPTURED TRACES, ATTESTS via the REAL verifiers. The five
capture types are EXACT MIRRORS — they import-and-reuse the system's own structs (`CheckpointData`,
`CommitRecord`, `TurnReceipt`, `CallForest`) rather than redefining them, so a format drift is a
compile error, not a silent skew. The AnalysisReport is now DEEPENED beyond the per-source summary:
the blocklace report surfaces the concrete EQUIVOCATION-FORK WITNESS (the real `EquivocationProof`
`block_a ∥ block_b` pair the protocol would slash on, recovered by re-running the node's own
`detect_equivocation`); the receipts report builds the RECEIPT-LINK GRAPH (distinct agents +
federation replay-domain set w/ cross-federation flag + Final/Tentative finality breakdown +
encrypted-path count + introduction/routing/derivation/consumed-cap edges — all bound into the v3
receipt hash, so on an intact chain they are attested non-strippable); the WAL report carries the
RECOVERY OVERLAY (per-record replay detail + touched-cell re-touch count + block-hwm resume anchor)
AND the ledger-root CONVERGENCE TRAIL (distinct-root count + a stagnant-root-with-touched-cells
Critical anomaly). Build-out lanes:)*

- **live-capture hooks** (THE TAIL — node-side, out of this crate's scope) — a node trace-export mode emitting `BlocklaceCapture`/`ReceiptStrandCapture`/`WalCapture` from the running node (the on-disk/wire types are already exact mirrors, so an export endpoint is a thin dump). → node.
- **Studio/Workbench visualization binding** — render the `AnalysisReport` (DAG w/ equivocation fork, finality bar, receipt link graph, WAL replay overlay) in the Starbridge/starbridge-v2 shell (report is already JSON-serializable).
- **gossip capture provenance** — the network source is `Observed`-only (gossip = liveness); a signed dissemination-receipt would graduate some eclipse signals to `Verified`.

## Overnight 2026-06-14 — wide-safe wave seams (named follow-ups; the work itself is committed green)

*(While the cutover flip is HELD for ember, the night ran a 5-lane wide-safe braid. Each lane named an
honest scope-limit; closure levers below. The flip — C5/C7 + #103 graduation + the notify VK epoch +
the devnet redeploy — remains the one held item, one-command-ready per §EXEC.3, awaiting ember at the
redeploy point-of-no-return.)*

- **in-browser / over-wire recursion-verify** (web-forward, `2dcede9b3`): `WholeChainProof.root` is an
  `Rc`-backed `RecursionOutput` with NO serde, so the in-tab whole-history recursion-verify (and the
  pg-dregg S1 proof-gate) is placeholdered behind a versioned envelope. Closure = fork-side
  (plonky3-recursion) recursion-proof serialization (the same follow-up `ivc_turn_chain` already names).
  → plonky3-recursion fork. SHARED by web-forward + pg-dregg S1.
- **browser-extension at-rest key** (`8a8ab52ba`): the MV3 front door keeps the key in
  `chrome.storage.local` for the demo; production at-rest hardening (BIP39+PBKDF2+AES-256-GCM, auto-lock)
  is the shape the sibling wasm cipherclerk already ships. The property PROVEN is the trusted-path
  mediation (key never reaches the page), not at-rest encryption. → sdk-ts/extension.
- **ADOS narration R1 join** (`eeb5655f2`): the narration-vs-truth panel correlates at the FEED level
  (`Correlation::FeedLevelOnly`); claim-to-a-SPECIFIC-turn needs the tool-call→effect compiler (R1). The
  divergence panel ships now; the compiler is the deeper join. → starbridge-v2 + the R1 compiler.
- **persist history-below-checkpoint** (`9f031f7e8`): after `compact_below`, `identity_export`
  (`commit_records_from(0)`) returns only survivors — pre-checkpoint EVENT history is no longer locally
  reconstructable (an archival node simply does not compact). Finalized-STATE correctness is untouched
  (the checkpoint ⊕ overlay is exact). → node/identity_export (a feature-scope decision, not a bug).
- **cli hermetic preflight** (`9427a18e5`): `config_path()` now honors `DREGG_HOME`; restore the hermetic
  `cli_config_init` preflight check that this unblocks. → preflight/cli.
- **N5 killer-demo deferred step-5** (starbridge-v2, `1535f46a7`): the four-surface headline demo proves
  frames 1-4 (mint / agent turn / notify handoff / dual refusal) as REAL receipted turns + exits 0 on the
  headline contract; the demo's **step 5 = the pg-dregg Tier-B SQL mirror read** is NOT wired (it needs a
  live pg mirror outside the starbridge-v2 crate — the N2/pg lane). Closure = stand the pg mirror, add the
  SQL read-back frame. → starbridge-v2 + pg-dregg (the outbox/mirror lane), post-flip. NOT blocking.
- **N13 over-wire byte-verify** (web-forward, `6fb9e8087`): the web-surface killer-demo page is now verified
  e2e (20-check Playwright over the 5-step state machine via the real wasm bindings — the over-share is the
  genuine executor `DelegationDenied`, not a banner) + discoverable. The remaining **over-wire byte-verify**
  (a fetched whole-history proof verified in-tab) is the SAME `WholeChainProof` serde seam already named
  above — closes when the fork-side recursion-proof serialization lands. → SHARED with the recursion-verify
  seam. NOT a separate item.
- **assurance-catalog drift** (the assurance lane, UNCOMMITTED at HEAD): the assurance lane's in-tree edits
  to `metatheory/Dregg2/AssuranceCase.lean` (+ `Exec/ForestMemoryProgram.lean`, `Exec/UniversalBridge.lean`,
  `Cargo.lock`) change the assurance source-of-truth, so the generated catalog
  `site/src/_includes/studio/assurance-catalog.generated.json` is STALE until regenerated. Closure = after the
  assurance lane commits, re-run the catalog generator (the studio build step) so the site reflects the new
  AssuranceCase. → site, AFTER the assurance lane lands. (One-step, mechanical; tracked so it isn't lost.)
- **signed-turn producer admit (LANDED, not a follow-up)**: the default-on Lean producer
  (`DREGG_LEAN_PRODUCER`) now ADMITS a genuine `Authorization::Signature` turn (the N=4 testnet's remote
  signed-submission path). Root cause was two width mismatches under the `Crypto.Reference` portal
  (`verify stmt proof = stmt == proof`): (1) the `Signature` arm mapped to a 256-bit R-half statement vs a
  u64 proof that could never echo; (2) the wire `prev` crossed as a full-256 digest while the host
  `stored_head` crossed as low-64, so the ChainHead leg rejected EVERY non-genesis turn. FIX:
  `turn::lean_shadow::sig_echo_wire` recomputes the executor's real `verify_strict` (target pubkey ·
  federation/nonce/position-bound message · full 64-byte sig) and folds the verdict into a self-echoing
  low-64 `(statement, proof)` pair (genuine ⇒ echo ⇒ admit; forged/tampered/cross-fed ⇒ non-echo ⇒ veto);
  `prev_hash` now uses the same low-64 projection as `stored_head`. Lean teeth `signature_teeth_same_wire`
  (+ `#guard`s, `#assert_axioms` kernel-clean). Green: `DREGG_LEAN_PRODUCER=1` node
  `remote_signed_envelope_e2e_*` + `three_node_full_mode_runs_the_ordering_rule` PASS; `dregg-turn` 555
  pass; `lake build` green. (Recorded as the durable note; the commit is the record.)
- **bearer/token producer-admit parity for REAL data (the sibling latent gap)**: the bearer/token WHO-leg
  fix (`c35153ce5`) folds the full sig/discharge chain so a FORGED credential ⇒ veto (sound), and its teeth
  use synthetic `.bearer 7 7`/`.token 9 9` (echoing). But on a REAL bearer/token turn the wire still carries
  `deleg_msg`/`issuer_key` as a full-256 digest vs a low-64 `deleg_sig`/`sig` — so a GENUINE bearer/token
  turn would NOT echo under `Crypto.Reference` and the authoritative producer would VETO it (the same
  width-mismatch class the Signature fix just closed). LATENT because no test drives a real bearer/token turn
  through `DREGG_LEAN_PRODUCER=1` (the divergence corpus is all `Unchecked`). Closure = give bearer/token the
  `sig_echo_wire` treatment (recompute the real ed25519/biscuit verdict in the marshaller, emit a low-64
  self-echoing pair) + an e2e producer test that submits a genuine bearer/token turn and asserts ADMIT. →
  turn/lean_shadow, when a bearer/token turn rides the verified producer. (Not in the Signature-arm brief;
  named so it isn't lost.)

- **circuit-soundness apex REDUCED to {four realizable floors + the dischargeable decode-extraction
  family} (`Dregg2/Circuit/ClosureAll.lean`, 2026-06-17).** `lightclient_unfoolable_closed` instantiates
  the apex at `S_live`/`Rfix`/`kstepAll`, carrying {`StarkSound`, `Poseidon2SpongeCR` + the `CommitSurface`
  CR fields, `WitnessDecodes`, `mkLog` (the `logHashInjective` log binding), and `∀ e, ClosedLogExtract e`}.
  `#print axioms` = {propext, Classical.choice, Quot.sound}, green (3978). HONEST: `ClosedLogExtract e` IS
  the per-effect `Satisfied2 (R e) → StateDecodeLog → kstep` refinement (= `descriptorRefines` + log) — the
  circuit-forcing RUNGS are PROVEN (the `RotatedKernelRefinement*` family + the 31 `*_closedLog` wrappers),
  but the `Satisfied2 ⟹ encode` DECODE-EXTRACTION is still CARRIED inside `ClosedLogExtract` (and the
  `extract` hypothesis of `closedLogExtract_transfer`). That extraction is a THEOREM (dischargeable — the
  trace columns ARE in the `Satisfied2` witness), NOT a floor. So this is a clean REDUCTION, not closure.
  GENUINE REMAINING WORK: (a) DISCHARGE the per-effect `Satisfied2 (R e) ⟹ <effect>Encode` decode-extraction
  (the column readout; the cap-tree/guard openings ride the realizable prover-witness residual, the
  `TransferAuthoritySource` class) — `TransferDecodeBridge` did the ledger half. (b) FIX the
  `Rfix := v3Registry[e]?` index seam — it keys by LIST POSITION, = `actionTag` only for leading slots, so
  non-leading effects' rungs aren't yet at their genuine descriptor; re-key `Rfix` by `actionTag`.
  (c) `exercise` (tag 16) genuinely has NO outer `.log` receipt (its log advances in the inner fold) —
  `exercise_closedLog` bridges faithfully (not a hole). Named: circuit-soundness reduction, 2026-06-17.

## Decisions pending (ember)

- #93 proof-audit: build a harness, or declare `#assert_axioms` + non-vacuity-both-polarities + the Convergence gauntlet its successor and close. (Recommendation: the latter — WRITTEN UP as docs/ASSURANCE.md §4 with the close-rationale; awaiting ember's flip to close.)
- Hosted key custody posture (above).
- starbridge-apps stub dirs compute-exchange/gallery: build or delete (above).
- **#103 cap-crown — TWO EffectVM AIRs, the weaker one LIVE on the sovereign path (SOUNDNESS-shaped, not janitorial). ✅ DECIDED 2026-06-13 (ember): shape (i) — GRADUATE the sovereign bespoke path onto the rotated multi-table AIR AT THE FLIP, so in-circuit non-amplification (granted ⊑ held vs the authenticated cap_root) holds EVERYWHERE. This is now a C5/C7 flip TASK: cut `cipherclerk.execute_sovereign_turn_with_proof` + `proof_verify.rs::verify_and_commit_proof` off the bespoke `EffectVmAir` onto the rotated `Ir2BatchProof` path, and retire the `air.rs:1365-1374` legacy cap arm with it.** There are two constraint systems for the EffectVM proof: (a) the AUDITED p3-batch-stark `EffectVmP3Air` (`circuit/src/effect_vm_p3_full_air.rs`), which carries the GRADUATED cap-crown Phase-B gates (sorted-tree membership-open + leaf-update + submask + expiry-monotone, its `attn` module ~`:189-310`; the non-amp gauntlets `circuit/tests/effect_vm_{attenuate,grant,revoke}_non_amp.rs` exercise exactly these); and (b) the BESPOKE FRI `EffectVmAir` (`circuit/src/effect_vm/air.rs`), whose `eval_constraints` still pins AttenuateCapability `cap_root` as the LEGACY nested-digest `new_cap_root = H2(old_cap_root, H2(slot_hash, narrower))` (`air.rs:1365-1374`) — it has NO sorted-open / submask / non-amp tooth (verified: no `cap_root::`/`CAP_TREE_DEPTH`/membership markers in air.rs). The default full-turn path emits + verifies the p3 proof (`prove_full_turn`→`prove_effect_vm_p3`, stored in `FullTurnProof.proof_bytes`; verified live via `dregg_sdk::verify_full_turn`/`verify_full_turn_bound`, `node/src/turn_proving.rs:246/414/532`) — so the graduated AIR gates the default path. BUT the bespoke `EffectVmAir` IS still live on the **sovereign-cell bespoke-STARK path**: `AgentCipherclerk::execute_sovereign_turn_with_proof` produces `stark::prove(&EffectVmAir,…)` bytes into `turn.execution_proof` (`sdk/src/cipherclerk.rs:5160-5166`, also `:6305`), and `TurnExecutor::verify_and_commit_proof` verifies them via `stark::verify(&EffectVmAir,…)` (`turn/src/executor/proof_verify.rs:420-421`), reached when `turn.execution_proof.is_some()` && cell is sovereign (`turn/src/executor/execute.rs:476`). The two species CANNOT silently cross — `stark::proof_from_bytes` requires a `b"DREG"` magic header and fails closed on the postcard p3 blob (`circuit/src/stark.rs`). **Reachability (severity calibration):** `execute_sovereign_turn_with_proof` is a `pub fn` SDK API (not cfg-gated) but its ONLY in-repo callers are `tests/src/sovereign_proof.rs:73/125`; NO service/binary (node/cli/discord-bot/demos/starbridge) drives it — so this is a LATENT public-API-surface gap exercised only by in-repo tests, NOT a shipped-node-flow hole. (The sibling `execute_with_program` `:6278/:6305` is the other bespoke `execution_proof` writer, same API-surface posture.) NET: on the sovereign bespoke path, an `AttenuateCapability` is checked only for the legacy digest-advance shape, NOT for in-circuit non-amplification (`granted ⊑ held` against the authenticated `cap_root`) — so a caller of that API gets the weaker cap guarantee. **Decision shapes:** (i) graduate the sovereign path onto the p3 AIR (cut `cipherclerk.execute_sovereign_turn_with_proof` over to `prove_effect_vm_p3` + `verify_effect_vm_p3`, retire the bespoke `EffectVmAir` cap arm) — the coherent close, lands the same non-amp guarantee everywhere; or (ii) declare the sovereign bespoke-STARK path deprecated/decommissioned (no live caller ships it) and delete it wholesale; or (iii) accept the weaker sovereign cap-binding as an explicit documented scope-limit. NOT deleted: deleting only the `air.rs:1365-1374` cap arm while the sovereign path still verifies through `EffectVmAir` would BREAK that path's cap-root binding (left intact pending this decision). CROSS-REF: the ROTATION FLIP tail above ALREADY plans to "rewrite executor `proof_verify.rs::verify_and_commit_proof` … bespoke `stark::verify` → the rotated Ir2BatchProof" and to DELETE `effect_vm_p3_full_air.rs` — so decision-shape (i)/(ii) has a natural landing AT the flip; the open question is whether the sovereign cap-binding gap is acceptable in the interim (it is live on the bespoke path TODAY, pre-flip) or wants an earlier targeted fix. Named: cap-crown #103 burn-down, 2026-06-13.
- **#103 cap-crown Phase-D — the 4-ary c-list `membership` leg vs. the sorted `cap-membership` leg (retire-or-keep).** `sdk/src/full_turn_proof.rs` attaches TWO distinct membership sub-proofs to a cap-gated turn, proving DIFFERENT claims: (a) the **4-ary c-list `membership` leg** (`:978-1012`, witness `MembershipWitness` `:177`, `prove_membership_p3` over the generic positions-indexed `P3MerklePoseidon2Air`, PI `[leaf_hash, root]`, vk `merkle_poseidon2_descriptor`) proves "an opaque capability `leaf_hash` is present in A Merkle tree at the witnessed positions" — a GENERIC membership statement; its root is not structurally pinned to the authenticated `cap_root`, and the leaf is an opaque hash (not the typed 7-field cap preimage). (b) the **sorted `cap-membership` leg** ("cap Phase D", `:1075-1100`, witness `CapMembershipWitness` `:212` ← `ConsumedCapWitness`, `prove_cap_membership_p3` over the SORTED `CanonicalCapTree`, directional path, vk `cap_membership_circuit_descriptor`, expectation `CapMembershipExpectation` `:239` pins `pi[CAP_ROOT]` to the trusted root `:248`) proves "the SPECIFIC CONSUMED capability's full 7-field leaf preimage opens against THE holder's real sorted `cap_root` tree" — the authority leg that ties the acting/consumed cap to the authenticated cap-state, with sorted single-leaf-per-slot semantics. **The two are not redundant:** the sorted leg gives the strictly stronger, structurally-pinned, typed-leaf guarantee; the 4-ary leg gives a weaker generic membership over an unpinned root with an opaque leaf. **Retire-vs-keep tradeoff:** for a cap-gated turn the sorted `cap-membership` leg SUBSUMES the authority claim the 4-ary leg makes (consumed-cap-in-the-real-cap_root ⊃ opaque-leaf-in-some-4-ary-tree), so the 4-ary leg is retireable FOR CAP-GATED TURNS on the claim alone. **Live-producer evidence (the deciding fact):** there is currently NO live producer that sets `membership: Some(MembershipWitness{..})` — the only two build sites (`full_turn_proof.rs:2303`, `:2774`) are both inside `#[cfg(test)] mod tests` (`:2107`) using `merkle_test_witness`; the only LIVE membership-leg producer is `cap_membership` (`node/src/turn_proving.rs:518`, `CapMembershipWitness::from_consumed`). So today the 4-ary `membership` leg is dead on the live path — its `Option`/`P3MerklePoseidon2Air`/`merkle_poseidon2_descriptor` plumbing is wired + SDK-tested but unfed. **The keep argument** is therefore forward-looking, not current: the 4-ary leg is the GENERIC credential/c-list membership primitive (opaque leaf, witnessed root, no sorted `cap_root` to open against) that a NON-cap predicate-credential turn-shape WOULD use — retiring it removes that future affordance and the `merkle_poseidon2` descriptor's only full-turn consumer. **Recommendation (ember to ratify):** keep the 4-ary leg as the general-membership primitive but DO NOT couple it to cap-gated turns (the sorted leg is the cap authority leg of record); OR, if no near-term non-cap credential turn-shape is planned, demote the 4-ary leg + its descriptor to a clearly-labelled "general membership, no live producer" status (Research tier) so it stops reading as a live cap-authority alternative. Before any removal, confirm no in-flight feature wires a live `membership: Some(..)`. Named: cap-crown #103 Phase-D map, 2026-06-13. (Left intact — characterization only, per the brief.)

## Research tier (explicitly not scheduled)

- Transcendental-syntax S3 (substructural recovery from the dregg side) + S5 (stella instantiation).
- UC-security / CryptHOL (#31) + research pillars (revocation/info-flow/metadata).
- Hypersystem/simplicial joint turns (dregg4 vision).
