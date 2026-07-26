# Codex take-home: land the verified layout allocator as the ONE source — and tidy the cruft

## §−1. REORIENT FIRST (this brief drifted; the code is the truth)

This brief was drafted 2026-07-15; the tree moves HARD (multiple lanes commit every few minutes — FRI
ledger, PQ, stark-kill, BFV). By the time you read it, its **specific numbers, file:line, and PI counts
are probably stale.** Treat this brief as *intent + constraints + gotchas*, NOT as ground truth. Before
acting, SHAPE from the record, STATE from code at HEAD:

- **The authoritative current record is `docs/DESIGN-verified-layout-optimizer.md`** — it was rewritten
  with file:line `BUILT` vs `PROPOSED` markers and is kept fresher than this brief. Read it first; §1.3's
  "named seam" IS Goal A. Where it and this brief disagree, the design doc + the actual code win.
- **The workstream was abandoned mid-stride and repaired-to-green** by a sweep-up (`cf84a9baa`, "ember
  apologizes: sweep-up commits") — it BUILDS GREEN at HEAD (verified 2026-07-17: `lake build
  Dregg2.Circuit.RotatedKernelRefinementAvailWideNarrow Dregg2.Circuit.Emit.RotatedLayoutBridge` clean, no
  `sorry`) but was orphaned from `REORIENT.md`/`HORIZONLOG.md`. Start from green; do NOT trust that the
  geometry constants below (`NUM_PRE_LIMBS=178`, the group tilings, PI=46/78) are still current — RE-DERIVE
  them from `RotatedLayout.lean` + `trace_rotated.rs` + `cell/src/commitment.rs` at HEAD.
- **First move: re-verify the baseline is green** (`lake build` the layout + narrow modules; `cargo test -p
  dregg-circuit` the layout tiling test) so you know you're starting from not-broken, and so any red you
  cause is yours.

Everything below is the durable intent. Verify each concrete fact against HEAD before you lean on it.

---

You are codex, deputized on a detail-dense, high-value job you're well suited to. This brief front-loads
*everything* — the history, the proven body, the goal, the mess, the hard constraints, the gotchas — so
you can reason broadly and choose your own path. Broad/rambling scope is fine; use judgment. The one
inviolable rule: **improve, don't degrade** (a "quick fix" is usually a debt hole), and **never launder a
gap as done** — model it or name it honestly, never a `sorry`/axiom/vacuous claim.

---

## 0. TL;DR

**Goal A (ship this):** make the rotated-block circuit column layout a *single verified source* that the
Rust producer, the Rust circuit AIR, and the Lean emit all DERIVE from — so a geometry flag-day becomes a
`def` + `native_decide`, not a 14-file hand re-grind. **Byte-preserving. No VK regen. No descriptor bytes
move.** The `check-descriptor-drift.sh` gate must stay green with NO `DREGG_VK_REGEN_ACK` needed.

**Also (you're empowered to):** reorganize/refactor the layout+narrow-graduation code, which is a
cruft-layered mess of parallel representations. Consolidate, simplify, delete dead scaffolding — WITHOUT
breaking any proof (`lake build` green, every `#assert_axioms` clean) or moving a deployed byte.

**Explicitly OUT of scope (do NOT do):** the tuple-narrowing *deployment* — the descriptor-shrinking
optimizer flip. Its soundness is fully PROVEN (see §3) but deploying it needs a producer change + a VK
regen that re-keys the federation. Leave that for a deliberate campaign. **Do not regen. Do not narrow the
deployed descriptors.**

---

## 1. Why this exists (the pain that motivates Goal A)

The rotated-block descriptor geometry (which circuit column holds which committed limb) is hand-carried as
raw integers across THREE places that must agree:
- the Rust **producer** — `cell/src/commitment.rs::compute_rotated_pre_limbs` (`write_lanes([26, 68..74])` …)
- the Rust **circuit** — `circuit/src/effect_vm/trace_rotated.rs` (the `B_*` consts + `*_group_col` fns)
- the Lean **emit** — `metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean` (`*RootGroupCol` defs)

The revoked-root 178-limb migration (2026-07) bled for exactly this: one added limb → a 14-file re-grind,
a leftover-chunk design fork, a cells/revoked column OVERLAP bug, a producer carrier-stride bug, and 5
stale hardcoded-limb assertions. **All one disease: the invariant that makes a layout legal — no two
things write the same column (disjointness) — was an unchecked comment, and the positions were three
independent copies free to drift.**

## 2. What's already PROVEN (do NOT re-derive — build ON these)

This session proved the layout foundation + a full narrow-graduation soundness tower. All axiom-clean
(`#assert_axioms ⊆ {propext, Classical.choice, Quot.sound}`), all built green. The files:

- `metatheory/Dregg2/Circuit/Emit/RotatedLayout.lean` — `structure RotatedLayout` + `structure Legal`
  (disjoint = `occupied.Nodup`, `inBounds`, `bodyAligned (n-4)%3=0`) as CONSTRUCTOR OBLIGATIONS. `rotated178`
  = the current 178-limb geometry as an instance; `rotated178_legal : Legal rotated178` by `native_decide`;
  `rotated178_complete` (occupied.length = 178 ⇒ complete 0..177 tiling). Plus `GroupName` + a `groupCol`
  projection + `groupTable` (emit-ready). **This is the allocator's Lean core. The disjointness invariant
  that was a comment is now a machine-checked theorem.**
- ⚑ **The bridge is retired because the goal it was a stepping-stone to LANDED.** A
  `RotatedLayoutBridge.lean` under `metatheory/Dregg2/Circuit/Emit/` used to prove all 7 deployed
  `*RootGroupCol` emit defs EQUAL `rotated178.groupCol` (`cap/heap/fields/nullifier/commitments/
  revoked/cells`) while the emit still hand-carried the positions. The emit now DERIVES them:
  `EffectVmEmitRotationV3.layoutGroupCol` (`:150`) is literally `(rotated178.groupCol name i).getD 0`
  and every `*GroupCol` is defined through it, so the equalities are `rfl` by construction and the
  bridge file was deleted rather than maintained.
- `circuit/src/effect_vm/trace_rotated.rs` — a Rust `#[test] rotated_layout_is_a_complete_disjoint_tiling`
  asserts the Rust positions (bound to the `B_*` consts) form a complete disjoint tiling of `0..NUM_PRE_LIMBS`.
- The narrow-graduation soundness tower (relevant only so you don't disturb it): `NarrowChip.lean`,
  `GraduateNarrow.lean`, `GraduateWideNarrow.lean`, `AvailWideMembersNarrow.lean`,
  `RotatedKernelRefinementAvailWideNarrow.lean`. These prove the *optimizer* (Goal B) is sound. **Leave
  them building; you may tidy their organization but not weaken a theorem.**

## 3. The concurrent layout-emit (another terminal built this — RECONCILE with it)

A sibling effort emits layout data Lean→Rust:
- `metatheory/EmitLayoutManifest.lean` (~6500 lines) — emits the SCALAR layout constants (`B_SPAN`,
  `EFFECT_VM_WIDTH`, octet bases, widths) as a generated Rust module.
- `circuit/src/effect_vm/layout_generated.rs` (~3100 lines) — the generated Rust (the `@generated` module
  the producer/circuit can read).
- Wired via `scripts/emit_descriptors.py` (the `EmitLayoutManifest` emitter + `split_layout` routing) —
  read that pipeline; it's the Lean→JSON/Rust source-of-truth loop, and the ACK-gated regen controls
  (`docs/VK-REGEN-CONTROLS.md`) live there.

**This overlaps `RotatedLayout`.** `EmitLayoutManifest` handles the *scalar* constants; `RotatedLayout`
handles the *group position tiling* + the *disjointness proof*. Neither alone is the whole layout. **A big
part of Goal A is unifying these into ONE coherent story** rather than two parallel "layouts."

## 4. GOAL A — concrete definition of "in place"

Make the layout a single source the three consumers DERIVE from. Concretely, some combination of:
1. The Lean emit's `*RootGroupCol` defs PROJECT from `rotated178.groupCol` (the bridge already proves them
   equal — so this is a proof-backed *pure refactor*; the emitted descriptor bytes MUST NOT change, verified
   by `scripts/check-descriptor-drift.sh` staying green with no ACK).
2. `rotated178` (the group tiling) is EMITTED into `layout_generated.rs` alongside `EmitLayoutManifest`'s
   scalars — so the Rust producer + circuit read the group positions from the generated module instead of
   hand-carrying `write_lanes([...])` / inline `B_*`.
3. The Rust producer (`compute_rotated_pre_limbs`) and circuit (`trace_rotated.rs` `*_group_col`) DERIVE
   from the generated layout, so they cannot drift from each other or from Lean.

The success test: **change the layout in ONE place (a `RotatedLayout` instance + its `native_decide`
`Legal` proof) and the producer + circuit + emit all follow, with the drift-check confirming byte-identity.**
You choose the exact mechanism; the above is the shape, not a mandate. If full derivation is too invasive
byte-safely, a proof-backed *checked-mirror* (the Rust positions are drift-checked against the emitted
`rotated178`) is an acceptable milestone — but say so honestly.

## 5. The TIDY mandate (you're empowered here — use taste)

The organization is genuinely confusing and cruft-layered. Candidates (your judgment on all):
- **Parallel "layout" representations** — `RotatedLayout` vs `EmitLayoutManifest` vs `layout_generated.rs`
  vs the hand-carried `B_*` consts vs the `*GroupCol` fns. Consolidate into a coherent single story.
- **The additive-twin sprawl** — the narrow-graduation work is a chain of `*Narrow` twin files
  (`GraduateNarrow`, `GraduateWideNarrow`, `AvailWideMembersNarrow`,
  `RotatedKernelRefinementAvailWideNarrow`) built beside their wide originals. If a cleaner factoring
  (parametric-over-a-width, or a shared lemma) collapses the duplication WITHOUT weakening any theorem,
  do it. If not, at least document the layering so it reads.
- **Dead scaffolding** — e.g. `descriptor_ir2.rs`'s `BUS_FACT`/`is_fact`/`fact_hist` is dead (declared,
  iterated, never inserted-into) — a known free cleanup, but it touches the chip AIR width so it's a
  descriptor/VK change → **defer it (it's not byte-safe), just note it.** Look for genuinely byte-safe dead
  code.
- **Stale comments** — this codebase has a documented habit of docstrings lying about state (e.g. a
  "STAGED / no VK bump" doc on a DEPLOYED registry; width `409` when it's 1668). Correct any you find; a
  doc-comment is a name, not a proof — make it match the code.

Refactor is IN scope, but every step must keep `lake build` green + `#assert_axioms` clean + the
drift-check green + zero deployed bytes moved.

## 6. HARD CONSTRAINTS (inviolable)

1. **No VK regen. No descriptor bytes move.** `scripts/check-descriptor-drift.sh` must pass with NO
   `DREGG_VK_REGEN_ACK`. If you can't do something byte-safely, name it as out-of-scope, don't force it.
2. **Proof tree stays green.** `lake build` clean on everything you touch; every `#assert_axioms` you
   touch stays ⊆ `{propext, Classical.choice, Quot.sound}`. NO `sorry`/`admit`/new `axiom`. Crypto/table
   soundness enters as a HYPOTHESIS, never an axiom.
3. **Don't break the deployed path.** The live per-turn proof rides the WIDE rotated descriptor
   (`WIDE_REGISTRY_STAGED_TSV`, `require_welded`, verified in `turn/src/executor/proof_verify.rs`). Don't
   perturb its bytes or its soundness.
4. **Verify by building, never by asserting.** "Green + I think it's done" is not verification — run the
   build, run the drift-check, run the Rust `cargo test -p dregg-circuit` layout test. Trust the checker.
5. **Commit named files, never `git add -A`** (the tree is co-tenant with other terminals). Sign
   `Co-Authored-By: <codex identity>`.

## 7. GOTCHAS + invariants (paid for in real debugging)

- **The disjointness invariant IS the whole point.** Every consolidation must preserve `Legal`
  (disjoint/in-bounds/58×3-aligned). If a refactor lets an illegal layout be constructed, it's wrong.
- **`fields` group is NON-contiguous** — `[36, 66, 67, 19, 20, 21, 22, 23]` (reuses headroom limbs 19..23).
  Don't assume contiguity anywhere.
- **`cells` completion (169..175) is circuit-only** — the producer leaves it ZERO; the circuit constrains
  it. It's occupied in the tiling but producer-zero.
- **`NUM_PRE_LIMBS = 178`** currently; declared in multiple Rust files independently (that duplication is
  part of the disease — consolidate it). The 8-felt ProofBind commit-teeth land at cols 1619..1623 (PI
  50..53) past the graduated host.
- **The `.custom 3` TableId trick** (if you touch TableIds): a fresh `TableId` case would break the
  deployed `wireId_injective`; `.custom 3` was reused because it already serializes to wire id 8. Don't
  add fresh cases in the `[5,∞)` range.
- **Wide vs narrow graduation:** `graduateV1Wide` uses the SAME `siteLookup` as `graduateV1` (differs only
  in per-width range teeth); the deployed wide descriptor = `wideAppend (graduateV1Wide (rotateV3FrozenAuthority d))`.
- **A known honest-TODO in the narrow tower** (do NOT try to "complete" it — it's Goal B): the EFF
  facet-selector tooth `effNarrow_rejects_wrong_facet`, and the narrow WIRE-object wrappers (welded/refused)
  + the producer/regen. Named residuals, not gaps to paper.

## 8. Build discipline (hbox is co-tenant)

- On hbox, run builds as `swarm-build <cmd>` (e.g. `swarm-build lake build Foo`) — it enforces a memory
  cgroup (concurrent Lean C-codegen OOM'd the box into a power-cycle). Never bare `taskset`/`lake` there.
- **hbox is shared: codex owns the datacake HOL build there** (`~/dev/datacake` poly/Holmake) — spare
  those procs, keep waves small when sharing.
- Local `lake build <module>` from `metatheory/` is fine for targeted checks; the emit closure builds even
  if unrelated soundness files are mid-flux.

## 9. Definition of done

- The layout is a single verified source producer + circuit + emit derive from (or a proof-backed
  drift-checked mirror, honestly labeled).
- `check-descriptor-drift.sh` green, NO ACK. `lake build` green. `cargo test -p dregg-circuit` layout test
  green. Every touched `#assert_axioms` clean.
- The parallel-layout cruft is consolidated or, where consolidation isn't byte-safe, documented so it
  reads.
- A short `docs/` note (or a rewrite of this one) describing the FINAL layout architecture — what's the one
  source, how the three consumers derive, and what's the flag-day procedure now.
- Every out-of-scope residual (Goal B: the optimizer deploy) named honestly, untouched.

Go broad, use taste, and leave the layout better-organized and single-sourced than you found it. ⚔️
