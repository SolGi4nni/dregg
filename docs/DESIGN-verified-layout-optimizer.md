# The Verified Layout Optimizer — design ("the snarky we never finished")

**What this is.** A forward-design doc for the one layer of the verified-circuit stack dregg has never
built: a **verified allocator + optimizer** for the descriptor AIRs. dregg already EMITS constraint
descriptors as projections of proven Lean (the "descriptor circuit"). But the *column layout* those
descriptors read — which circuit column holds which committed limb — is **hand-carried as raw integers
across three independent copies**. There is no allocator that owns the layout, and no optimizer that makes
it cheap. This doc designs both, on one load-bearing idea: **translation validation** — let an *untrusted*
search propose an optimized AIR, then *check* the output and *prove a refinement* (the optimized AIR denotes
the same relation as the source AIR), so the search never needs to be trusted.

**Status legend.** BUILT = in-tree at HEAD, verified, file:line cited. PROPOSED = designed here, unbuilt.
Every "would"/"proposed" is design; every present-tense claim is checked against code.

---

## 1. What exists today — the hand-layout the optimizer replaces (BUILT)

### 1.1 The disease, stated precisely

The rotated-block descriptor geometry is hand-carried as raw column integers across **three** places that
must agree byte-for-byte, with the invariant that makes a layout *legal* — no two things write the same
column — held only as a comment:

- **The Rust producer** — `cell/src/commitment.rs::compute_rotated_pre_limbs`
  (`cell/src/commitment.rs:1061`) writes each committed root to literal lane arrays:
  `compute_authority_digest_8(cell).write_lanes(&mut pre, [24, 12, 13, 14, 15, 16, 17, 18])`
  (`cell/src/commitment.rs:1112`), cap at `[25, 52, 53, 54, 55, 56, 57, 58]` (`:1121`), nullifier at
  `[26, 68, …, 74]` (`:1130`), and so on — the positions are **hand-typed integer arrays**.
  `V9_NUM_PRE_LIMBS = 178` is declared here independently (`cell/src/commitment.rs:757`).
- **The Rust circuit** — `circuit/src/effect_vm/trace_rotated.rs` re-declares `NUM_PRE_LIMBS = 178`
  (`circuit/src/effect_vm/trace_rotated.rs:96`) and carries its own `B_*` position consts + `*_group_col`
  functions. A `#[test] rotated_layout_is_a_complete_disjoint_tiling` asserts the Rust positions tile
  `0..NUM_PRE_LIMBS` — a *test*, run after the fact, not a construction invariant.
- **The Lean emit** — `metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean` hand-carries the same
  positions as `*GroupCol` defs: `capRootGroupCol` (`:1492`), `heapRootGroupCol` (`:1556`),
  `fieldsRootGroupCol` (`:1641`), `nullifierRootGroupCol` (`:1687`), etc.

The revoked-root 178-limb migration (2026-07) paid the tuition: one added committed limb forced a 14-file
re-grind, a leftover-chunk design fork (the "170-leftover"), a cells/revoked column **overlap** bug, a
producer carrier-stride bug, and five stale hardcoded-limb assertions — all one disease, because
disjointness was an unchecked comment and the positions were three free-to-drift copies. This is the exact
pain `docs/CODEX-BRIEF-allocator-single-source.md` (Goal A) is chartered to kill.

### 1.2 The allocator core — already a verified object (Phase 1, BUILT)

`metatheory/Dregg2/Circuit/Emit/RotatedLayout.lean` makes the layout a first-class Lean object whose
**constructor carries the invariants**:

- `structure RotatedLayout` (`RotatedLayout.lean:38`) holds the abstract layout as data: singles, name-tagged
  faithful-8-felt `groups`, octet bases, the fields octet, the circuit-only cells completion, and pads.
- `structure Legal (L : RotatedLayout)` (`:66`) carries the three legality obligations as proof fields:
  `disjoint : L.occupied.Nodup` (**the invariant that was a comment** — `:68`), `inBounds` (every occupied
  column `< numPreLimbs`, `:70`), and `bodyAligned : (numPreLimbs - 4) % 3 = 0` (the arity-3 body-fold
  discipline whose violation was the 170-leftover fork, `:74`).
- `rotated178` (`:78`) is the current deployed geometry as an instance, grounded lane-for-lane in the
  producer. `rotated178_legal : Legal rotated178` discharges all three by `native_decide` (`:101`), and
  `rotated178_complete : rotated178.occupied.length = 178` (`:108`) upgrades `Nodup` to a **complete tiling**
  of `0..177` — no gaps, no reuse.
- `RotatedLayout.groupCol` (`:59`) is **the projection**: the single source a group's within-block column is
  read from. `RotatedLayout.groupTable` (`:122`) is the emit-ready `[[lane0, comp₁ .. comp₇]]` shape.

An ill-aligned or overlapping layout is **unconstructable as `Legal`**; a flag-day becomes a new instance +
its `native_decide` obligation, not a 14-file re-grind.

### 1.3 The producer/emit bridge — proven, non-invasive (Phase 2, BUILT + one named seam)

`metatheory/Dregg2/Circuit/Emit/RotatedLayoutBridge.lean` proves each deployed emit `*GroupCol` def **equals**
`rotated178.groupCol`'s projection at every lane: `capRootGroupCol_eq_layout` (`:23`),
`heapRootGroupCol_eq_layout` (`:27`), `fieldsRootGroupCol_eq_layout` (`:31`, the non-contiguous case
`fields = [36, 66, 67, 19, 20, 21, 22, 23]`), `nullifierRootGroupCol_eq_layout` (`:35`),
`commitmentsRootGroupCol_eq_layout` (`:39`), `revokedRootGroupCol_eq_layout` (`:43`),
`cellsRootGroupCol_eq_layout` (`:47`) — each by `fin_cases i <;> native_decide`. So `rotated178` is the
**proven model** of the emit's positions **without moving a single emitted byte**.

On the Rust side, `circuit/src/effect_vm/layout_generated.rs` is `@generated by metatheory/EmitLayoutManifest.lean`
and exports the **scalar** layout constants (`EFFECT_VM_WIDTH = 188`, `B_SPAN = 239`, `B_CAP_ROOT = 25`,
`B_NULLIFIER_ROOT_OFF = 26`, …). Note the named seam: this generated module emits the **scalars but not the
group position lists** — the producer's `write_lanes([…])` arrays and the circuit's `*_group_col` are still
test-pinned mirrors, not derived-by-construction from `rotated178.groupTable`. Closing that (emitting
`groupTable` into `layout_generated.rs` and projecting the producer/circuit from it) is a proof-backed pure
refactor, still open. This is the boundary between Phase 2 and everything above it.

**Net:** dregg uniquely has the *bottom* half of the verified-snarky stack — a verified EMIT (descriptors are
projections of proven Lean) and now a verified ALLOCATOR (`RotatedLayout` makes the layout a `Legal` object).
snarky/halo2/circom all have an allocator, but *unverified*. The missing layer is the one *above*: the
**optimizer** — and its whole value depends on it being **cheap without being trusted**.

---

## 2. The design — EMIT → untrusted search → translation validation → accept-iff-proven (PROPOSED)

The optimizer is a pipeline whose search half is untrusted and whose acceptance half is a Lean proof:

```
  source AIR d            (a descriptor from the live registry — a Satisfied2-denoting object)
       │
       ▼
  [ UNTRUSTED optimizer search ]   ← arbitrary heuristics / ML / aggressive rewrites; NOT trusted
       │   proposes d' + a witness map φ (how d's trace maps to d''s)
       ▼
  [ TRANSLATION VALIDATOR ]        ← TRUSTED Lean checker
       │   attempts to PROVE:  ∀ hash minit mfin maddrs t,
       │       Satisfied2 hash d' minit mfin maddrs (φ t)  ↔  Satisfied2 hash d minit mfin maddrs t
       │   (a refinement of the SOURCE denotation, cited below)
       ├── proof closes  ─────────►  ACCEPT d'  (ships; cost-model-cheaper by construction of the search)
       └── proof fails   ─────────►  REJECT d'  (a wrong optimization simply never ships — no VK regen)
```

The key property, and the reason the search need not be trusted: **acceptance is gated on a closed refinement
proof, not on believing the optimizer.** A miscompiled AIR fails to close its `Satisfied2`-equivalence and is
discarded. This is translation validation — the compiler is untrusted; each *output* is validated.

### 2.1 What the source denotation IS (the object refinement is proved over — BUILT)

The refinement is stated over the **live descriptor denotation**, not a toy:

- `structure Satisfied2 (hash) (d : EffectVmDescriptor2) (minit) (mfin) (maddrs) (t : VmTrace) : Prop`
  (`metatheory/Dregg2/Circuit/DescriptorIR2.lean:611`) is the multi-table accepting-trace Prop: every
  constraint holds on every row window (`rowConstraints`), every hash site / range tooth holds (`rowHashes`,
  `rowRanges`), and the memory/map-op tables are LogUp-disciplined and table-faithful (`memBalanced`,
  `memTableFaithful`, `mapTableFaithful`). This is a first-class, two-sided object — not a boolean.
- Two-sided legs already exist over it: `def descriptorRefines` (`CircuitSoundness.lean:235`) — every
  `Satisfied2` witness of `d` whose published commitments decode to `pre`/`post` forces `kstep pre post`
  (**soundness / rejects dishonest**) — and `def descriptorComplete` (`CircuitCompleteness.lean:123`) — an
  honest `kstep` has a realizable `Satisfied2` witness (**completeness / accepts honest**). Both take the
  `Poseidon2SpongeCR hash` carrier as a genuine antecedent, not a free lever.

So descriptor equivalence — `Satisfied2 hash (opt d) … t' ↔ Satisfied2 hash d … t` — is **expressible today
with no new denotation type.** The optimizer targets exactly this `Satisfied2` accept-set layer, where all
the machinery already lives.

### 2.2 The refinement theorem shape (PROPOSED — the general lemma; instances exist)

The general obligation the validator discharges for a proposed `(d', φ)`:

```lean
-- PROPOSED: the translation-validation obligation the checker proves per optimization
theorem tv_refines (d d' : EffectVmDescriptor2) (φ : VmTrace → VmTrace) (hOpt : Optimizes d d') :
    ∀ (hash : List ℤ → ℤ) (minit) (mfin) (maddrs) (t : VmTrace),
      Satisfied2 hash d' minit mfin maddrs (φ t) ↔ Satisfied2 hash d minit mfin maddrs t
```

Closing `tv_refines` means the optimized AIR **denotes the same relation** as the source: it accepts exactly
the honest traces the source accepts (completeness preserved, ⟸) and rejects exactly the dishonest ones
(soundness preserved, ⟹). The two directions are what make refinement *equivalence*, not one-way inclusion —
a subtle-but-critical point: a one-directional `d' ⟹ d` would let the optimizer silently *drop* accepting
traces (breaking honest provers); the ⟸ direction forbids that.

**This shape already has real, parametric instances in-tree** — the optimizer generalizes a pattern that is
already proved for the deployed rotation:

- `normalize_to_shape_sound` (`NormalizeToShapeSound.lean:217`) is the closest existing *general* TV lemma:
  normalizing a satisfying manifest `m` to a canonical shape yields `m'` that STILL satisfies the
  content-equal circuit, STILL publishes the same commitment, is `Canonical K`, and carries
  `SemanticsPreserved m m'` — a bona-fide equivalence-preserving transform, `#assert_axioms`-clean, whose
  sole crypto consumer is `publish_binds_content` (one `Poseidon2SpongeCR` application, `:241`).
- `v3OfFrozen d := graduateV1 (rotateV3FrozenAuthority d)` (`EffectVmEmitRotationV3.lean:3244`) is itself a
  *transform composed of a relocation and a table-ization*, and `rotV3Frozen_sound_v1`
  (`EffectVmEmitRotationV3.lean:3274`) ships a **parametric preservation proof** with it: a
  `Satisfied2 hash (v3OfFrozen d) …` witness yields the v1 denotation on every row, for **any** graduable `d`.
  This is precisely the "optimization + refinement proof travelling together" pattern the optimizer wants,
  proved once and reused across the whole registry.
- `graduateV1` (`EffectVmEmitV2.lean:158`) is the table-ization mechanism itself: it re-anchors a v1
  descriptor onto IR-v2 by turning **every hash site into a chip lookup** and every range tooth into a range
  lookup (`siteLookup` / `rangeLookup`). This is the exact CSE-class move — sharing hash computation on a
  bus — that an optimizer pass would drive, and it already ships with soundness.

---

## 3. The trust boundary

| Component | Status | In the TCB? |
|---|---|---|
| The optimizer **search** (heuristics, ML, aggressive rewrites) | PROPOSED, untrusted | **No** — a wrong proposal fails its proof and is rejected |
| The **translation validator** (the Lean checker that attempts `tv_refines`) | PROPOSED | **Yes** — but it is a proof *checker*: it only accepts a closed proof |
| The **refinement proof** for each accepted `d'` | PROPOSED per-pass | **Yes** — it IS the guarantee |
| The `Satisfied2` denotation + `descriptorRefines`/`descriptorComplete` legs | BUILT | Yes (already trusted today) |
| The STARK-proximity floor (`StarkSound`) | BUILT (named reduction) | Unchanged (§5) |
| The **cost model** (the search's objective) | PROPOSED | **No** — it is the objective, not the guarantee; a wrong cost model yields a slow-but-sound circuit, never an unsound one |

The single most important line: **the search moves from trusted to untrusted, and the checker + the
per-output refinement proof stay trusted.** That is the whole unlock. It is the same discipline the codebase
already runs — `#assert_axioms` gating (axioms ⊆ `{propext, Classical.choice, Quot.sound}`), `#guard`
non-vacuity, and the "false-pole tooth" (a *non*-equivalent rewrite must NOT be provable) — reused
off-the-shelf as the validator's acceptance gate.

---

## 4. The concrete first slice — the translation-validator on ONE real AIR (PROPOSED)

**Slice: the transfer / graduated-member AIR.** This is the right first target because the source denotation,
the graduation transform, and a per-row preservation proof already exist for it end-to-end — the slice is to
wrap them as a *validated single pass*, not to invent machinery.

Ground truth for the slice (all BUILT):

- `EffectVmEmitTransfer.transferVmDescriptor` is the v1 transfer AIR (the source `d`).
- `transferV3 := v3OfFrozen transferVmDescriptor` (`RotatedKernelRefinement.lean:82`) is the deployed
  optimized/graduated descriptor `d'`, with `transfer_graduable : graduable transferVmDescriptor = true`
  (`:89`) as the side condition.
- `rotV3Frozen_sound_v1` (`EffectVmEmitRotationV3.lean:3274`) already proves the ⟹ direction (optimized
  witness ⟹ source-row denotation) *parametrically*; `rotated_row_cellSpec` (`RotatedKernelRefinement.lean:183`)
  carries it all the way to the per-cell `CellTransferSpec` (limb moves, nonce ticks, frame freezes), with the
  table-faithfulness rolled into `RotTableSide` (`:110`) so there is no free chip/range lever.

**First-slice build plan (the smallest thing that proves the optimizer pattern as a *validated* pass):**

1. **New module `LayoutOptimize.lean` under `metatheory/Dregg2/Circuit/Emit/` (PROPOSED — not in the tree).** Define
   `structure OptResult` = a proposed `d'` + the witness map `φ` + the *proof obligation* it must close, and
   the general `def Optimizes (d d' : EffectVmDescriptor2) : Prop`. This is the validator's typed contract.
2. **New module `LayoutOptimizeTransfer.lean` under `metatheory/Dregg2/Circuit/Emit/` (PROPOSED — not in the tree).** Instantiate the
   pass for transfer: prove `tv_refines transferVmDescriptor transferV3 φ` for the graduation `φ` by
   **assembling the two directions from what exists** — ⟹ from `rotV3Frozen_sound_v1`, and ⟸
   (completeness-preservation) from the realizable-witness side (`descriptorComplete`'s constructor for the
   transfer family). The pass here is degenerate (the "optimization" is the *already-deployed* graduation), so
   the slice's job is to demonstrate the *validator wrapping* closes on a real AIR — de-risking the harness
   before a genuinely aggressive pass.
3. **The first genuinely-optimizing pass on the same slice: table-ize the rotated hash sites.** The transfer
   AIR's rotated main table carries inline Poseidon2 aux columns. `graduateV1`'s `siteLookup` already moves a
   hash site onto the shared chip bus with a soundness proof; the pass generalizes that from "graduation" to a
   *chosen-by-search* CSE that shares repeated hash computations, validated by `tv_refines`. This is the
   highest-value pass (the committed-width lever, §5) and the technique is already proven to preserve the
   denotation elsewhere.
4. **Untrusted-search stub (Rust or Lean `#eval`-driven, PROPOSED).** A tiny search that proposes candidate
   `d'`s by the cost objective; each candidate is handed to the Lean validator; only proof-closing candidates
   are emitted. The search lives *outside* the TCB — it can be replaced wholesale without touching soundness.

**Success test for the slice:** feed the transfer AIR through the pipeline, have the search propose a
width-reduced `d'`, and have the validator either close `tv_refines` (accept, emit) or fail (reject) — with a
deliberately-broken candidate (a non-equivalent rewrite) provably *rejected* (the false-pole tooth).

---

## 5. What the optimizer does NOT do (honest scope)

- **It does not move the STARK-proximity floor** — in either direction. `StarkSound` is a proven reduction to
  `RSProximityCore` (`StarkSoundReduction.lean`), and an optimized AIR gets its `StarkSound R'` through the
  *same* reduction instantiated for it. The TV equivalence preserves refinement/completeness through the
  transform; it neither worsens nor discharges the proximity floor. `StarkComplete`
  (`CircuitCompleteness.lean:147`) — the realizable dual — likewise transfers, not weakens.
- **It is orthogonal to circuit-level soundness discharges.** The transfer template's availability wraps and
  the wide/welded registry discharges are proved independently; the optimizer neither depends on nor perturbs
  them. The verified part is strictly the **equivalence between two same-kernel descriptors at the
  `Satisfied2` layer.**
- **It does not deploy by itself.** A descriptor-shrinking optimization that changes emitted bytes needs a
  producer change + a VK regen that re-keys the federation (`docs/CODEX-BRIEF-allocator-single-source.md`
  §0, §6). The optimizer *proves an optimization sound*; flipping the deployed descriptor to it is a separate,
  deliberate, ack-gated campaign. The refinement proof is what makes that flip *safe* to take, not automatic.

---

## 6. The hard parts (named, not papered)

1. **Refinement over a reordered/compressed column layout is the crux.** Relocation (permute columns) and
   compression (share/pack columns) both change the *witness*, so `φ : VmTrace → VmTrace` is non-trivial and
   `tv_refines` must prove the permuted/packed trace satisfies `d'` iff the original satisfies `d`. The
   bespoke `rotV3_sound_v1`/`rotated_row_cellSpec` pattern proves this for *one fixed* relocation; the general
   lemma `Satisfied2 (relocate π d) (permute π t) ↔ Satisfied2 d t` for an arbitrary column permutation `π`
   is **new mechanical work** — every conjunct of `Satisfied2` (rowConstraints, rowHashes, rowRanges, the four
   memory/map-table faithfulness fields) must be shown invariant under `π`. This is the single largest proof
   task.
2. **CSE / witness-introducing passes need a `∃`-witness-column-preserves-accept-set lemma.** Sharing a hash
   computation introduces an auxiliary column existentially witnessed by the honest prover. Raw material is
   present — `graduateV1`'s aux-column mechanism does exactly this shape — but the *general* "introducing a
   proven-functional aux column preserves the accept-set" lemma is a new foundational result.
3. **The `φ` witness map must itself be checked, not trusted.** If the search supplies a wrong `φ`, the proof
   should fail rather than the harness accepting a bogus map. `φ` must be a *checked* part of the `OptResult`,
   with its own well-formedness obligation — otherwise the trust boundary leaks.
4. **A "transform is non-trivial" check.** The false-pole tooth forbids proving a non-equivalence, but a
   *vacuous* pass (identity dressed up) could pass while achieving nothing. `LoadBearingLint`'s
   not-defeq-to-gate check is executor-spec-specific; the optimizer needs a small analogue asserting the pass
   actually changed committed width.
5. **`RotatedLayout` covers positions, not the whole AIR.** The allocator owns the rotated group *tiling*;
   `EmitLayoutManifest`/`layout_generated.rs` owns the *scalars*; neither owns constraint/table structure.
   Extending the optimizer past column relocation (to constraint-level CSE and degree rewrites) means
   reasoning about parts of the AIR the current allocator does not model. The vertical slice is honest about
   this: it optimizes the transfer AIR's *columns and hash sites*, not its full constraint graph.

---

## 7. Open questions

- **How aggressive can the untrusted search be before the validator becomes the bottleneck?** A search that
  proposes thousands of candidates needs each `tv_refines` to close fast (`native_decide`-friendly, or a
  reusable parametric lemma keyed on the pass class). If per-candidate proof cost is high, the search must be
  guided to *few, good* candidates — which pulls proof-search structure back toward the search half.
- **Where does the cost model live, and is it worth verifying?** §3 says the cost model is untrusted (it is
  only the objective). But a cost model that mis-ranks passes wastes the whole run. Does it stay a Rust
  heuristic, or become a checked `def cost : EffectVmDescriptor2 → Nat` so the search's ranking is at least
  reproducible? (It never needs a *soundness* proof — only reproducibility.)
- **When to generalize past the rotated-transfer slice to all-AIR authoring?** The seed's resolved call is
  "after the first optimizing pass proves the pattern on the slice." The open sub-question: does the general
  `relocate π` lemma (hard part #1) land *before* or *after* the second AIR family is attempted — i.e. is the
  general lemma the gating deliverable, or is a second bespoke-then-generalized instance the cheaper path to it?
- **Does the emit `groupTable` derivation (Phase 2's open seam, §1.3) block the optimizer, or run in
  parallel?** Emitting `rotated178.groupTable` into `layout_generated.rs` so the producer/circuit *project*
  from it is independent of the optimizer's refinement work, but a relocation pass that changes positions will
  want the producer to *follow* the layout automatically — so closing that seam is a natural precondition for
  the relocation-class passes (not for the table-ize pass).

---

## 8. Why this is the natural completion (not a speculative chain)

Every link is grounded: the allocator it builds on is **in-tree and verified** (`RotatedLayout`, `Legal`,
`rotated178_legal`); the invariants it enforces are **the bugs already hit** (the revoked-root disjointness
overlap); the source denotation is the **live `Satisfied2` object** with two-sided legs already proved; and
the refinement-with-transform pattern already ships parametrically for the deployed rotation
(`rotV3Frozen_sound_v1`, `normalize_to_shape_sound`). The optimizer is a *wiring job* for degree rewrites, a
*mechanical general lemma* for relocation, and *one foundational lemma* (raw material present) for CSE — with
an untrusted search bolted on top and gated by a proof. It is the layer that turns dregg's verified circuits
from *correct* into *cheap-and-correct*: the only verified snarky.

---

### Cross-references (verified to exist at HEAD)

- `docs/CODEX-BRIEF-allocator-single-source.md` — Goal A (the single-source allocator) and the hard
  byte-preservation constraints; this doc's §1 is that brief's motivating pain.
- `metatheory/Dregg2/Circuit/Emit/RotatedLayout.lean` · `.../RotatedLayoutBridge.lean` — the built allocator.
- `metatheory/Dregg2/Circuit/DescriptorIR2.lean` (`Satisfied2`) · `CircuitSoundness.lean` (`descriptorRefines`)
  · `CircuitCompleteness.lean` (`descriptorComplete`, `StarkComplete`) — the denotation + two-sided legs.
- `metatheory/Dregg2/Circuit/NormalizeToShapeSound.lean` — the closest existing general TV lemma.
- `metatheory/Dregg2/Circuit/Emit/EffectVmEmitV2.lean` (`graduateV1`) ·
  `.../EffectVmEmitRotationV3.lean` (`v3OfFrozen`, `rotV3Frozen_sound_v1`) ·
  `Dregg2/Circuit/RotatedKernelRefinement.lean` (`transferV3`, `rotated_row_cellSpec`) — the first-slice raw
  material.
- `circuit/src/effect_vm/{trace_rotated.rs,layout_generated.rs}` · `cell/src/commitment.rs` — the Rust
  hand-layout the allocator single-sources.
