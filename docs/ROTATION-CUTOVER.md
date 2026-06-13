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

- [ ] **GATE 0**: `effect_vm_ir2_size_measure` at-or-under the v1 350.5 KiB
      baseline (per-effect; the staged probe's block-only shape measures ~tens of
      KiB — see the test print — but the GATE is the per-effect transfer figure).
- [ ] The 3-verb executor bridge (`RecordKernelState` → the ONE universal map)
      landed and soaked (`VerbCompression.lean:87-89` — "rides THE ONE ROTATION";
      first real-turn umem proof landed `93a34fa74`).
- [ ] Lean adapters: cap-leaf value-codec · MMR boundary-derivation · guardAtom
      atoms (`UNIVERSAL-MAP-ROTATION.md` §3) — to whatever extent the rotation
      carries §2.2/§2.3 (detachable: the LAYOUT items §2.1/§2.4/§2.6 do not
      depend on them).
- [ ] `absent` map-op realization driven through a real nullifier witness
      (staged `MapKind::Insert` landed; the absent lane has its gauntet tests).

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

1. **The full-cohort regen at the rotated block** (§3 step 1-2) — the probe pins
   the SHAPE; the 26 per-effect descriptors still emit against the 186/14 layout.
2. **The balance/nonce register-name assignment** (§2 note) — ember decision.
3. **The cells_root producer**: the rotated block's `cells_root` limb needs the
   turn-level cells-root carrier wired into the per-turn witness (today the
   probe witnesses it as a free limb; the executor must supply it).
4. **The iroot producer**: the MMR root over the receipt log must be computed by
   the executor per turn (Lean MMR theory landed; `turn/` carrier missing).
5. **lifecycle/epoch carriers in the trace**: live `CellState` tracks them; the
   v1 trace does not — the regen adds the columns, the executor populates.
6. **GATE 0 re-measure** after the regen (the staged probe measures the block
   shape only).
7. **The 3-verb circuit descriptors** (gated on the executor rotation —
   `UNIVERSAL-MAP-ROTATION.md` §2.3; never before it).
8. **cell ≡ circuit rotated differential** (§3 post-flip gauntlets).
9. **Heap-caveat runtime discharge** — the executor leg of the widened operand:
   discharge heap-domain entries at run time the way `verify_slot_caveat_manifest`
   discharges slot entries (the semantics are already pinned: `tagHeapAtom` →
   `HeapAtom.lift k` → `evalHeap`, `EffectVmEmitRotationCaveat.lean` §5; the named
   premise is `HeapCaveatRuntimeDischarge`). At the flag-day the staged 29-felt
   manifest replaces the live 25-felt slot manifest in the regenerated PI region.
