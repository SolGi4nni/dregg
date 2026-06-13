# ROTATION-CUTOVER — the flag-day checklist (the one VK epoch)

*(operational checklist, 2026-06-12. The design is `docs/UNIVERSAL-MAP-ROTATION.md`
(master) + `docs/EPOCH-DESIGN.md` (tables/commitment); the PROVEN target layout is
`metatheory/Dregg2/Circuit/RotationLayout.lean`; the staged wire propagation is
`metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotation.lean`. This file tracks what
FLIPS at the cutover commit, which pins bump, and what is staged vs. live today.)*

## §0 — Standing law

1. **Zero Rust-authored constraint semantics.** Every table, relation, and layout
   fact is emitted from Lean; Rust interprets (`descriptor_ir2.rs:53-58`). A layout
   change starts in Lean, lands as a re-emitted artifact, and only then re-anchors
   the Rust constants behind a drift guard.
2. **Nothing flips before GATE 0** (the IR-v2 size regression measured green —
   `docs/PROOF-ECONOMICS.md` §2b, `circuit/tests/effect_vm_ir2_size_measure.rs`).
3. **The live v1 path stays byte-identical until the cutover commit.** Staged
   artifacts ride the recursion-gated IR-v2 path only.

## §1 — What is ALREADY LANDED (staged or live-additive; verify, don't re-do)

| piece | where | state |
|---|---|---|
| registers 8→16 + heap_root in cell state, commitment context v6→v7 | `f5a25fd16` (cell/turn) | LIVE (cell-side; additive context bump) |
| executor admits heap fields (SetField ≥ STATE_SLOTS → fields_map) | `b133354fc` (turn) | LIVE |
| committed_height limb (context v8) + PI v3 tail wiring (`pi::v3`, ACTIVE_BASE_COUNT fan-out) | `007c2f1d2` | LIVE (tail populated; nothing reads it on-wire yet) |
| fresh-key sorted INSERT (`MapKind::Insert`, wire code 3) | `696fa1032` (descriptor_ir2) | STAGED (IR-v2 path) |
| THE TARGET COMMITMENT LAYOUT, proven: `RotatedLimbs` (23 limbs, iroot LAST), `rotatedCommit_binds` anti-ghost keystone, `resolve` (FactoryDescriptor.fields), `PiV3` offsets | `metatheory/Dregg2/Circuit/RotationLayout.lean` | PROVEN (Lean; no wire) |
| THE WIRE PROPAGATION, staged: rotated 25-slot state block (absorption-ordered), `wireCommit` = 4-ary chained chip realization + re-proved keystone (`wireCommit_binds` + heap_root/reg/named-field/log teeth), `rotationProbeVmDescriptor2` (graduated IR-v2 probe: 8 chip lookups + published-commit/height PI pins), `rotationLayoutManifest` (byte-pinned) | `metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotation.lean`, driver `EmitRotationV3.lean` | STAGED (this lane) |
| staged artifacts on the Rust side: `circuit/descriptors/rotation-layout-v3-staged.json` + `dregg-effectvm-rotation-state-v3-staged.json`, `effect_vm_descriptors.rs::V3_STAGED_DESCRIPTORS` (sha-256 pinned), `columns.rs::rotation` (drift-guarded `rotation_layout_matches_lean`), probe prove/verify/size + per-column tamper-refusal in `descriptor_ir2.rs` | circuit | STAGED (this lane) |
| PI v3 drift guard (`pi_v3_offsets_match_lean`) | `circuit/src/effect_vm/pi.rs` | LIVE test |
| THE WIDENED CAVEAT OPERAND, staged: `(domain_tag, key)` entries (7 felts, umem `domainCode` discipline, key u8→felt) + `caveat_operand_no_aliasing` keystone + `caveatCommit_binds` + the R=24 caveat probe (`rotationCaveatProbe_binds_published`) + forged-domain/tampered-heap-key teeth | `metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationCaveat.lean`, `circuit` (`columns.rs::rotation::caveat`, `trace.rs::RotCaveatEntry`, `V3_STAGED_CAVEAT_DESCRIPTORS`, `descriptor_ir2.rs` teeth) | STAGED (this lane) |
| THE FULL-COHORT REGEN at the rotated R=24 block, staged: `rotateV3` (ONE parametric transformation — appends two rotated state blocks + the widened-caveat region past ANY v1 descriptor, +125 cols, 4 appended PI pins; col-chained ⇒ byte-identical to the digest-chained R=24 probe, `#guard` tripwire), v1-survival keystone `rotateV3_satisfiedVm_v1` (every per-effect theorem composes unchanged), end-to-end `rotV3_binds_published` (one theorem, 26 descriptors — same published commits ⇒ equal whole before+after blocks + iroots + height + caveat manifest under the ONE CR floor), `v3Registry` (all 26 graduated, `attenuateV3`/`setFieldDynV3` keep their extras), welds r0↔BALANCE_LO · r1↔NONCE · r2↔BALANCE_HI · r3..r10↔fields · CAP_ROOT↔CAP_ROOT | `metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean`, Rust twin `circuit/descriptors/rotation-v3-staged-registry.tsv` + `V3_STAGED_REGISTRY_TSV` (sha-256 pinned; `v3_staged_registry_parses_matches_fingerprint_and_covers` walks all 26 — absorption + chain + 4 PI pins) | STAGED (this lane) |

## §2 — The staged commitment shape (what the cutover realizes)

The per-state commitment becomes the CHAINED 4-ary chip absorption (Lean
`wireCommit`; the chip absorbs ≤ 4 base elements per permutation), over the
absorption order pinned by `RotatedLimbs.toList`:

```
cells_root · r0..r15 · cap_root · nullifier_root · heap_root
           · lifecycle · epoch · committed_height · iroot   (LAST)
```

8 permutation sites (4 + 3·6 + 2 limbs), intermediate digests on chain carriers,
final digest = `state_commit`. Anti-ghost: `wireCommit_binds` (equal commits ⇒
equal limbs ∧ equal iroot, under the ONE `Poseidon2SpongeCR` floor);
`wireCommit_binds_log` composes `mroot_injective` (tamper/truncate/extend/REORDER
of the receipt log all refused). The layout manifest is byte-pinned BOTH sides
(Lean `#guard` / Rust `rotation_layout_matches_lean`) — neither side parses, both
pin.

**Note (balance/nonce):** `RotatedLimbs` carries NO separate balance/nonce limbs —
in the rotated world the cell's scalar state rides the NAMED register file
(`FactoryDescriptor.fields` → `resolve`) or the heap domain (the umem projection
already maps Balance/Nonce keys into the heap domain — `turn/src/umem.rs`). The
flag-day regen must fix the canonical name→register assignment for the kernel's
own scalars (an ember-visible decision; HORIZONLOG'd).

### §2a — THE AUTHORITY-DIGEST DESIGN (G3 design call, the rotated-commitment authority coverage)

The rotated v9 commitment (`cell/src/commitment.rs::compute_canonical_state_commitment_v9`)
binds the FULL authority-bearing cell state v8 commits — it does NOT drop authority state.
The decision (made + implemented 2026-06-13, Opus):

* **The problem.** v8 (BLAKE3, `CANONICAL_COMMITMENT_CONTEXT "…v8"`) absorbs the whole cell:
  identity, `mode`, the eight `Permissions` fields, the `verification_key`, `delegate`, the
  `delegation` snapshot, the `program`, and the full CellState authority sub-state
  (`field_visibility`, `commitments`, `proved_state`, the side-table/overflow roots, all 16
  `fields`). The rotated v9 NAMED limbs cover only a SUBSET: balance/nonce (r0/r1/r2),
  `fields[0..8]` (r3..r10), cap_root (r25), nullifier/heap roots (r26/r27),
  lifecycle/epoch/committed_height (r28/r29/r30). Everything else would be DROPPED by a
  rotated commitment that left the app-register headroom (r11..r23) zeroed — a soundness hole
  (two cells identical in the named limbs but differing in permissions/VK commit identically).

* **The fix — bind an AUTHORITY DIGEST into register r23.** `compute_authority_digest_felt`
  (one Poseidon2 felt) folds EXACTLY the authority residue no named limb carries: identity,
  mode, permissions, VK, delegate, delegation snapshot, program, `field_visibility`,
  `commitments`, `proved_state`, `swiss_table_root`, `refcount_table_root`, `fields_root`,
  `system_roots_digest`, and `fields[8..16]` (fields[0..8] are welded, so only the high
  fields go here). It walks the SAME byte serialization v8 uses (one source of truth for
  "what is authority state"), then hashes to a felt. The digest is cell-local; the
  turn-context limbs (cells_root/nullifier_root/iroot) ride `V9RotationContext`. So v9
  **covers all authority state (via r23) AND binds turn-context (via the context limbs)** —
  the design problem's two requirements, both met.

* **Why r23, and why NO Lean change.** The Lean welds (`EffectVmEmitRotationV3.weldsAt`)
  constrain ONLY r0..r10 + cap_root — r11..r23 are freely-witnessed limbs. The anti-ghost
  keystone (`wireCommitR_binds` / `RotationLayout.rotatedCommit_binds_reg`) ALREADY proves
  EVERY register is bound by the commitment. So r23 is "just a register" to the circuit and
  Lean: the authority digest binds with zero new keystone, zero Lean edit. The three-way
  agreement holds by construction — the cell-side v9, the producer
  (`turn/src/rotation_witness.rs::produce`), and the circuit trace generator
  (`trace_rotated.rs::fill_block`, which carries r23 from the witness) all derive r23 from the
  SAME `compute_authority_digest_felt(cell)`.

* **The tooth.** `cell/src/commitment.rs::v9_binds_full_authority_state` proves the property:
  two cells differing ONLY in permissions / VK / a high field / proved_state / a side-table
  root / mode commit distinctly under v9. This is what a zeroed-headroom rotated commitment
  would FAIL.

### §2c — THE COHORT-GENERAL GENERATOR (G4)

The rotated trace generator (`trace_rotated.rs::generate_rotated_effect_vm_trace`) was always
shape-general (the v1 sub-trace `generate_effect_vm_trace` dispatches every effect's selector
+ rows; the rotated appendix is parametric, not per-effect). What was transfer-only was the
DESCRIPTOR RESOLUTION and the caveat manifest. Now:

* `trace_rotated::rotated_descriptor_name_for_effect(effect)` resolves the `*VmDescriptor2R24`
  registry member for any of the 26 cohort effects (the 17 selector-mapped base effects +
  `setFieldDyn` + the 8 per-slot `setField`s), `None` (fail-closed) for a non-cohort effect.
  `effect_vm::trace::effect_selector` is the single source of truth (extracted from the trace
  generator's selector match, no duplication). The coverage tooth
  (`resolvers_cover_exactly_the_rotated_registry`) proves the resolvers reach EXACTLY the 26
  registry members.
* `sdk::full_turn_proof::prove_effect_vm_rotated_ir2_with_caveat` is the cohort-general
  rotated prover: it resolves the descriptor by effect, defaults to the empty caveat manifest
  (transfer keeps the two-domain reference manifest), proves the shared 311-col trace through
  the IR-v2 batch prover, and fails closed on empty / heterogeneous / non-cohort turns.

**Cohort boundary (honest) — WIDENED (STEP 1, 2026-06-13):** the rotated registry the Lean
`v3Registry` emitted was the 26 v2-graduated members; STEP 1 widened it to **34** by lifting
the 8 LIVE-path effects that had a graduated v1 wire descriptor through the SAME `rotateV3`:
`GrantCapability` (the bare unattenuated cap-root grant — `grantCapVmDescriptor2R24`),
`MakeSovereign`, `CreateCell`, `CreateCellFromFactory`, `SpawnWithDelegation`, `ReceiptArchive`,
`CellUnseal`, `EmitEvent`. Each is graduable (`#guard`ed) so `rotV3_sound_v1` /
`rotV3_binds_published` apply with no new proof; `rotated_descriptor_name` now resolves them;
the TSV + SHA + the `n == 34` cover guard + the resolver-coverage tooth are re-pinned green.
(STEP 1 also REPAIRED `EffectVmEmitEmitEvent.unify_emitEvent`, which had a stale `recKernel_ext`
arity after `EmitEventSpec` gained the `heaps` frame clause — the descriptor was sound but its
executor-connector proof leaked `sorryAx`; now axiom-clean and in the live `Dregg2` closure.)

**THE RESIDUE (two effects, precise obstructions — NOT papered over):** `RevokeCapability`
(selector 24) has NO graduated v1 descriptor at all (absent from `SELECTOR_DESCRIPTORS`; its
cap-root advance is being reshaped by the cap-crown lanes — it stays on the monolithic hand-AIR),
and `Custom` (selector 8) needs an accumulator/recursive proof-binding constraint kind the
per-row descriptor IR does not have. `rotated_descriptor_name` fails closed (`None`) for both.
The live-path rewrite (STEP 2) must keep a path for these two until a Lean-emission act adds
them (a new constraint kind for Custom; a graduated descriptor for RevokeCapability post
cap-crown). This is the precise residue the flag-day must resolve before v1 can fully die.

## §2b — Register count: MEASURED (16 vs 24 vs 32 — the always-paid vs metered economics)

Registers are **always-paid**: every register limb rides EVERY turn proof's commitment
chain — a main-trace column opened at each FRI query point plus its share of the chained
chip absorption — whether or not the app touches it, forever. Heap fields are **metered**:
umem rows enter a proof only when touched (the first REAL-TURN umem proof measures
**64.4 KiB**, `tests/effect_vm_umem_real_turn.rs`, landed `93a34fa74`). So "is 16 enough?"
is a price table, not a taste call. The staged probe was re-emitted at three register
counts from the PARAMETRIC Lean emission (`metatheory/Dregg2/Circuit/Emit/
EffectVmEmitRotationR.lean`: layout columns, arity-{2,4} chunking, and the chained
commitment are FUNCTIONS of R; the anti-ghost keystone `wireCommitR_binds` holds
parametrically in R under the one CR floor — no per-R axiom; the R=16 instance reproduces
the pinned emission BYTE-IDENTICALLY, `#guard`ed on the emitted JSON) and measured at the
production `ir2_config` (`descriptor_ir2.rs::rotation_probe_register_count_measurement`,
release, M-series laptop; teeth scale with the block: presence-refusal walks every limb
per R, spot tamper-refusal at low/high register + iroot + commit carrier per R, the full
33-column gauntlet stays on R=16):

| R | app registers (after balance/nonce) | chip sites | probe width | proof size | Δ vs 16 | opened-values | prove | verify |
|---|---|---|---|---|---|---|---|---|
| 16 | 14 | 9 (7×4 + 2×2) | 33 | 96,620 B (94.4 KiB) | — | 16,936 B | 23 ms | 3.2 ms |
| 24 | 22 | 11 (10×4 + 1×2, EXACT 3-fill) | 43 | 98,846 B (96.5 KiB) | **+2.2 KiB (+2.3%)** | 17,382 B | 28 ms | 2.9 ms |
| 32 | 30 | 15 (12×4 + 3×2) | 55 | 102,178 B (99.8 KiB) | **+5.4 KiB (+5.8%)** | 18,203 B | 18 ms | 3.1 ms |

(Chip table 2⁴ rows at every R — the chained sites dedupe per distinct absorption, so
9/11/15 sites all pad to 16; prove/verify differences are run-to-run noise at this scale.)

**Always-paid delta:** R=24 costs **+2.2 KiB per turn proof, forever** (~278 B per added
register); R=32 costs **+5.4 KiB** (~347 B per added register — the marginal register gets
DEARER past 24 because the 3-fill breaks: 24→32 adds 4 chip sites where 16→24 adds 2).
Against the metered baseline: a heap-resident field costs ~64.4 KiB on the turns that
TOUCH it (the real-turn umem proof) and zero on every other turn — registers are the L1
for hot scalars, the heap is where app state lives.

**Recommendation: R=24.**
  * The always-paid price is small and measured: +2.3% proof size per turn, forever — and
    22 app registers (after balance/nonce take r0/r1) retires the "14 doesn't seem like
    enough" concern with real headroom.
  * R=24 is the chunking sweet spot: the 31 pre-iroot limbs fill 4+9·3 EXACTLY, so the
    chain is 10 arity-4 sites + the lone arity-2 iroot tail — the cleanest chip realization
    of the three (R=16 and R=32 both carry mid-chain arity-2 sites).
  * R=32's further +3.2 KiB buys 8 more always-paid limbs at a WORSE per-register rate, for
    state that the heap economics says should be metered instead: a register only beats a
    heap field when it is touched on a large fraction of turns, and cold scalars belong in
    the heap (`umem` rows only when touched).
  * The decision stays cheap to revisit before the flag-day: the emission is parametric
    (`rotationProbeVmDescriptorR2 R`), so re-measuring any other R is one driver line.

## §3 — The cutover sequence (one motion, in order)

Pre-gates (ALL green before anything flips):

- [x] **The register-count decision** (§2b): MEASURED at R ∈ {16, 24, 32} (table above)
      — **CONFIRMED R=24 by ember, 2026-06-12 ("22 it is")**: 22 app registers after
      balance/nonce take r0/r1, +2.2 KiB always-paid per turn. The flag-day regen fixes
      `NUM_REGISTERS = 24`; the R-parametric emission (`rotationProbeVmDescriptorR2`)
      and `wireCommitR_binds` make this a parameter instantiation, not new design.

- [x] **Caveat operand widened (staged)** — the second wire-shape pre-gate: the in-circuit
      caveat operand is no longer slot-only. The rotated entry is **7 felts
      `[type_tag, domain_tag, key, p0..p3]`** (`SlotCaveatEntry`'s 6 + the domain tag; the
      key widens u8 → felt so HEAP KEYS are reachable); domain tags are the umem
      `domainCode` wire codes (registers 0 · heap 1; everything else REFUSES, fail closed);
      the manifest is 1 count + 4 entries = **29 felts**, bound by its own chained chip
      commitment (`caveatCommit`, arity-{2,4} chunking, 10 sites). Lean keystones
      (`EffectVmEmitRotationCaveat.lean`): **`caveat_operand_no_aliasing`** (a slot operand
      and a heap operand can NEVER collide — domain separation as a theorem),
      `caveatCommit_binds` (equal commits ⇒ equal manifests), and the end-to-end
      `rotationCaveatProbe_binds_published` at the CONFIRMED R=24 (probe layout: rotation
      block `0..42` · manifest `43..71` · chain `72..80` · `CAVEAT_COMMIT` 81 · width 82;
      probe proof measures ~107.9 KiB ≈ +11.4 KiB over the bare R=24 probe). Rust staged
      twins + teeth: `columns.rs::rotation::caveat`, `trace.rs::RotCaveatEntry`
      (fail-closed `from_felts`), `rotation_caveat_layout_matches_lean` byte pin,
      forged-domain-tag / tampered-heap-key refusal gauntlet (`descriptor_ir2.rs`).
      REMAINS (HORIZONLOG'd): the executor's runtime discharge of heap-keyed caveats
      (named premise `HeapCaveatRuntimeDischarge`) + the flag-day fold of the staged
      manifest into the live PI region (replaces `SLOT_CAVEAT_MANIFEST_BASE` 101..126).

- [x] **GATE 0**: `effect_vm_ir2_size_measure` at-or-under the v1 350.5 KiB
      baseline (per-effect; the staged probe's block-only shape measures ~tens of
      KiB — see the test print — but the GATE is the per-effect transfer figure).
      **GREEN**: v1 358,900 B (350.5 KiB) → IR-v2 123,292 B (120.4 KiB), ratio 0.344
      (-65.6%); re-confirmed this lane post-regen (the additive staging does not move it).
- [x] The 3-verb executor bridge (`RecordKernelState` → the ONE universal map)
      landed and soaked (`VerbCompression.lean:87-89` — "rides THE ONE ROTATION";
      first real-turn umem proof landed `93a34fa74`).
      **EXTENDED THIS LANE**: the per-turn ROTATION PRODUCERS now derive the
      witness-carried rotated limbs (`cells_root`, `iroot` MMR, `lifecycle`/`epoch`)
      from the real `RecordKernelState` — `turn/src/rotation_witness.rs` (the file
      §5 items 3-5 named as DELIBERATELY UNBUILT), built TOGETHER with the rotated
      trace builder that consumes them (`circuit/tests/effect_vm_rotation_flip.rs`).
- [ ] Lean adapters: cap-leaf value-codec · MMR boundary-derivation · guardAtom
      atoms (`UNIVERSAL-MAP-ROTATION.md` §3) — to whatever extent the rotation
      carries §2.2/§2.3 (detachable: the LAYOUT items §2.1/§2.4/§2.6 do not
      depend on them).
- [ ] `absent` map-op realization driven through a real nullifier witness
      (staged `MapKind::Insert` landed; the absent lane has its gauntet tests).

**LANE STATUS (the producers + trace builder + differential, staged-additive):** the
genuinely-new deferred long pole is DONE and GREEN — `turn/src/rotation_witness.rs`
(producers) + `circuit/tests/effect_vm_rotation_flip.rs` (rotated trace builder +
end-to-end prove+verify of `transferVmDescriptor2R24` at ~144.1 KiB + cell≡circuit
differential + anti-ghost teeth) land BESIDE v1 (v1 byte-identical, no VK bump, all 11
registry drift guards + 3 gate harnesses still green). The flip steps below are now the
MECHANICAL irreversible tail (registry-default + VK + cell context v8→v9 + executor PI +
v1 deletion) — the rotated path is proven green FIRST, exactly the cutover doc's safety
sequencing (§5.1: measure before the irreversible bump). **v1 is left DORMANT-BUT-PRESENT.**

The flip itself (ONE commit, regenerated, nothing hand-edited):

1. [ ] Re-anchor the per-effect Lean emit modules onto the rotated state block
       (the 25-slot absorption-ordered block replaces the 14-slot v1 block; the
       `EffectVmEmitRotation` probe is the validated reference shape — descriptors
       gain the 8-site chained commitment in place of the GROUP-4 tree; selector
       block dies into the verb/thin-main packing chosen by the regen).
2. [ ] ONE descriptor regeneration: `EmitAllJsonV2.lean` (or its successor)
       re-emits the full cohort against the rotated block; `EmitRotationV3.lean`'s
       manifest becomes the LIVE layout manifest.
3. [ ] Rust re-anchor: `columns.rs` live constants ← the manifest (the staged
       `rotation` module graduates to THE layout); `trace.rs` row population +
       `air.rs` constraint fan-out regenerate against the new width;
       `effect_vm_descriptors.rs` v1 registry replaced by the rotated registry
       (fingerprints all bump).
4. [ ] Cell/turn: `compute_canonical_state_commitment` context v8 → v9 = the
       rotated absorption order (cells root first, iroot last) — the cell-side
       commitment and the circuit-side commitment converge on ONE shape;
       executor PI assembly reads `pi::v3` slots as LIVE (VK_PI_LAYOUT_VERSION
       2→3 already staged, `CUSTOM_PROOFS_BASE` already moved).
5. [ ] VK/commitment bump + succession drill.
6. [ ] Graduation completes: `CutoverFallback` + the legacy AIR path die;
       RESERVED/retired-selector columns die.

Post-flip gauntlets (block the deploy, not the commit):

- [ ] differential gauntlets: cell ≡ circuit per map · per-effect AGREE against
      the rotated executor · the memory-argument adversarial suite (tampered
      read refuses).
- [ ] **the persvati workspace gauntlet** (`ssh persvati`, full
      `cargo test --workspace` + `lake build` on the build node) — REQUIRED
      before deploy.
- [ ] deploy when ember says deploy.

## §4 — Which pins bump at the flip

| pin | today | at the flip |
|---|---|---|
| `CANONICAL_COMMITMENT_CONTEXT` | v8 | v9 (rotated absorption order) |
| `VK_PI_LAYOUT_VERSION` | 3 (staged tail populated) | 3 live-read (verifier reads COMMITTED_HEIGHT from PI) |
| `pi::BASE_COUNT` | 201 frozen | superseded by the regenerated layout (PiV3 pins re-anchored) |
| v1 descriptor fingerprints (`ALL_DESCRIPTORS`) | frozen | ALL bump (regen) |
| `EFFECT_VM_WIDTH` 186 / state block 14 | frozen | dies (regen decides the thin-main packing; NOT 186+Δ — `EPOCH-DESIGN.md`) |
| `V3_STAGED_DESCRIPTORS` | 1 probe | the probe is subsumed by the live registry (delete or keep as reference gauntlet) |

## §5 — What remains UNDONE after this lane (the honest list)

1. ~~**The full-cohort regen at the rotated block** (§3 step 1-2) — the probe pins
   the SHAPE; the 26 per-effect descriptors still emit against the 186/14 layout.~~
   **DONE (staged), this lane + WIDENED to 34 (STEP 1, 2026-06-13)** —
   `EffectVmEmitRotationV3.lean::v3Registry` re-emits all **34** cohort members at the rotated
   R=24 block via the ONE parametric `rotateV3` (the 26 v2-graduated + the 8 LIVE-path effects
   STEP 1 added: grantCap · makeSovereign · createCell · factory · spawn · receiptArchive ·
   cellUnseal · emitEvent); the soundness keystones (`rotateV3_satisfiedVm_v1`,
   `rotV3_binds_published`) lift ONCE for all 34, axiom-clean; Rust twin
   `rotation-v3-staged-registry.tsv` is sha-pinned (`n == 34` cover guard) and the
   coverage/drift test walks every descriptor's absorption + chain + 4 PI pins. STAGED
   beside v1/v2 (no VK bump, the live wire untouched). RESIDUE: `RevokeCapability` (24) +
   `Custom` (8) still have no rotated descriptor (precise obstructions, §2c). The FLIP
   (§3 steps 1-6) replaces the v1 registry with this rotated one — still the main loop's act.
2. **The balance/nonce register-name assignment** (§2 note) — ember decision.
3. ~~**The cells_root producer**~~ **BUILT THIS LANE** (`turn/src/rotation_witness.rs::cells_root`):
   the turn-level boundary view over present cells (sorted-Poseidon2 root via
   `dregg_circuit::heap_root`, set-valued — `cells_root_is_set_valued`). Built
   TOGETHER with the rotated trace builder that consumes it
   (`circuit/tests/effect_vm_rotation_flip.rs`), so it is validated, not unvalidatable:
   the rotated transfer (`transferVmDescriptor2R24`) proves+verifies end-to-end on a
   real turn (~144.1 KiB) and the cell≡circuit differential asserts the producer's
   limb EQUALS the trace's before/after `cells_root` carrier.
4. ~~**The iroot producer**~~ **BUILT THIS LANE** (`rotation_witness.rs::iroot`): the
   left-leaning Poseidon2 MMR fold over the receipt log — the Rust twin of the Lean
   `mroot_injective`. The non-omission tooth is tested (`iroot_binds_the_whole_log`:
   tamper/truncate/extend/reorder each move the root); the differential binds the
   producer's iroot to the trace's after-block iroot carrier, and the anti-ghost
   gauntlet REFUSES a tampered iroot at prove time.
5. ~~**lifecycle/epoch carriers in the trace**~~ **BUILT THIS LANE**
   (`rotation_witness.rs::lifecycle_felt`/`epoch_felt`): the lifecycle limb folds the
   variant discriminant + payload so distinct states commit distinctly
   (`lifecycle_felt_separates_states`); the rotated trace builder populates them and
   the differential asserts producer == trace for both. The REGEN-TO-DEFAULT that
   moves these onto the LIVE wire (replacing the v1 columns) remains the flip's act
   (§3 steps 2-4) — staged-additive today, v1 untouched.
6. ~~**GATE 0 re-measure** after the regen (the staged probe measures the block
   shape only).~~ **MEASURED green, this lane**: the per-effect GATE figure is the
   transfer IR-v2 size (`effect_vm_ir2_size_measure`), which the staged additive regen
   does NOT move — v1 `350.5 KiB` → IR-v2 `120.4 KiB` (ratio 0.344, -65.6%), well under the
   350.5 KiB ceiling. The rotated cohort's own block-shape adds the +125-col appendix only
   when it graduates to the live wire (the flip), where it re-measures against the flipped
   per-effect baseline.
7. **The 3-verb circuit descriptors** (gated on the executor rotation —
   `UNIVERSAL-MAP-ROTATION.md` §2.3; never before it).
8. ~~**cell ≡ circuit rotated differential**~~ **LANDED THIS LANE (staged)**
   (`circuit/tests/effect_vm_rotation_flip.rs`): the producer's limbs derived from the
   real executed turn's `RecordKernelState` EQUAL the limbs the circuit trace carries
   — the welded scalars (`r0↔balance_lo` … `cap_root`) on the before block, the
   witness-carried limbs (`cells_root` · map roots · `lifecycle` · `epoch` ·
   `committed_height` · `iroot`) on both blocks, and the producer's
   independently-computed `wire_commit(before)` == the row-0 trace `STATE_COMMIT`
   carrier. The LIVE-WIRE differential (cell `compute_canonical_state_commitment` v9
   == circuit) lands with the cell-context bump at the flip (§4).
9. **Heap-caveat runtime discharge** — the executor leg of the widened operand:
   discharge heap-domain entries at run time the way `verify_slot_caveat_manifest`
   discharges slot entries (the semantics are already pinned: `tagHeapAtom` →
   `HeapAtom.lift k` → `evalHeap`, `EffectVmEmitRotationCaveat.lean` §5; the named
   premise is `HeapCaveatRuntimeDischarge`). At the flag-day the staged 29-felt
   manifest replaces the live 25-felt slot manifest in the regenerated PI region.
