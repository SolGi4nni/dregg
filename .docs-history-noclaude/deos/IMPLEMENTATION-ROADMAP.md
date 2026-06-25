# THE deos IMPLEMENTATION ROADMAP

## The one document that orders everything we have designed into one buildable program — NOW, SOON, the circuit lane, and what we deliberately let breathe

This is the master sequence. Every named milestone below already has its own
executable design doc; this roadmap does **not** re-derive them — it **orders**
them, cites the doc each step executes, names the gate that proves each step,
and states the dependency that decides when it may begin. A reader (or an agent)
picks up step 1 and goes.

The through-line, in one breath: **the inspector substrate is shipped and live;
everything below is the migration of the live starbridge onto a reflexive,
persistent, rewindable, distributed spine — and the make-or-break first move is a
pure efficiency weld with a microbench number that gates the rest.**

---

## 1. WHERE WE ARE

The moldable-inspector substrate is **shipped and live**: the `Presentable`
spine + the seven presentation kinds + `Gadget`/`CommittingGadget` + `Spotter`
(L1) and inspector lanes L2–L10, the clickable cockpit gpui tabs, the
Smalltalk-liveness wave (inspect→act loop · live workspace · wonder room), the
rehydratable `ui_snapshot` camera, the opt-in servo-render `dregg://` tile, and
the node crash-recovery first-writer-wins fix — all landed (commits
`1d603a29f`…`3bbec7c34`, `983ff76bc`, `5659493da`…`167f20512`, `279033535`).
`Registry::present` is a pure, viewer-parametrized projection of real cells; the
dynamics `since(cursor)` delta stream and the `WitnessCursor`/`Liveness`
trichotomy exist. The substrate breathes the right shape.

**What it is not yet:** efficient under scale, self-hosting (UI state is still
~50 Rust fields, not cells), persistent (no `dregg-persist` dep — every launch is
a fresh demo image), rewindable-across-a-close, reflexively debuggable, or
distributed-branchable. Each of those is a migration **on top of** the live
substrate, and they have a strict order. That order is this document.

---

## 2. THE ORDERED PROGRAM — NOW

Buildable immediately against the live tree. Each step is `cargo check
-p starbridge-v2`-friendly where possible, gated on a stated verification, and
sequenced by a hard dependency. **The gate on M1+M2 is a microbench number;
nothing past M2 starts until that number holds.**

### M1+M2 — THE EFFICIENCY WELD (FIRST · the make-or-break gate)

> **Executes:** `docs/deos/EFFICIENCY-WELD-PLAN.md` (the executable §1–§5);
> `docs/deos/REFLEXIVE-MIGRATION.md` §2, §6.
> **Depends on:** nothing — pure weld over the live substrate.
> **Why first:** driving UI from cells (M3) before the projector is incremental
> only deepens the existing O(whole-ledger + whole-receipt-log)-per-interaction
> hole. Every interaction today re-projects the entire ledger to draw a 12-char
> corner hash. This is also where the **latent dynamics-completeness bug** gets
> closed (the `IncrementNonce`/`MakeSovereign` effects that mutate a cell without
> emitting a naming `WorldEvent` — a stale-projection hazard, EFFICIENCY-WELD §4.1).

The two halves, in order:

- **M1 — memoize `state_root` + kill the 15×+ re-sort (pure weld, no API change).**
  Cache `(height, receipt_head) → [u8;32]` on `World` (invalidate on the
  genesis-path ledger writers); route the ~30 render-hot `sorted_cells()`
  callsites through the already-maintained `self.cells` sorted cache.
  **Gate:** `cargo check`; `state_root_changes_when_state_changes` still green +
  new `state_root_memoized_within_same_height` green; `grep "sorted_cells(&self.world"`
  returns only non-render sites.

- **M2 — close the delta loop (THE efficiency-proving milestone).** Add
  `Cockpit.dynamics_cursor`; fold `dynamics().since(cursor)` into per-slice
  invalidation (the variant→invalidation table, EFFICIENCY-WELD §2.2); wrap the
  **unchanged-pure** `Registry::present` in a `(FocusTarget, viewer, WitnessCursor)`
  memo; audit + close dynamics-completeness; split the giant Render into sub-view
  Entities (`CellWorldView` at least).
  **GATE (the number everything after rides on):** a microbench asserts
  per-interaction cost is **O(changed-cells), not O(ledger)** —
  `time(65536) < K·time(16)` for small `K` (EFFICIENCY-WELD §3) — **and**
  `grep "since(" cockpit.rs` is nonzero. Record the number.

**This is INDEPENDENT of the stratified-fixpoint question** — M1/M2 project only
*domain* cells; no cell is both a projection input and its own view-state, so the
self-cycle cannot arise (EFFICIENCY-WELD §4.4). The fixpoint question is deferred
whole to M3.

### M3 — SELF-HOST UI STATE AS CELLS

> **Executes:** `docs/deos/REFLEXIVE-MIGRATION.md` §3 (the field partition + the
> `BufferCell` two-tier pattern generalized); the unit-delay verdict of
> `docs/deos/STRATIFIED-FIXPOINT.md` §7.3.
> **Depends on:** the M2 gate (without the memo, UI-as-cells deepens the hole).

Generalize the proven `BufferCell` two-tier split (free in-memory draft +
occasional cap-gated `SetField` commit) into `WorkspaceCell`/`ViewCell`/
`PanelCell`/`GadgetCell`; move the §3.1 cell-candidate fields (selection, tab,
moldable focus, replay cursor, breakpoints, …) onto cell-backed slots;
`render()` reads its camera-aim from cells. The Cockpit struct shrinks to a
handful of UI-cell handles + `world` Rc + `FocusHandle`.

**The reflexive self-cycle arrives here, and its verdict is already settled
(STRATIFIED-FIXPOINT):** ship **unit-delay (z⁻¹) as the default for the UI/view
strata** (S₃ and up) — the self-view reads the previous frame; always terminates;
imperceptible lag. Reserve the within-frame stratified fixpoint for the authority
strata only (S₁→S₂), where the firmament hands the strata for free (the cap-tower
*is* the dataflow stratification). Close the one carve-out — same-stratum mutual
negation — with a `CellId` tie-break + well-founded `undefined → "refused"`
fallback, implemented *with* the first authority-stratum fixpoint, not deferred.

**Gate:** a UI mutation emits a `WorldEvent` and repaints via the M2 delta-fold
*uniformly* with any domain-cell change; the Cockpit struct measurably shrinks; a
self-referential readout (inspector focused on its own `ViewCell`) terminates in
one frame.

### M4 — NATIVE WORLD PERSISTENCE (the `dregg-persist` weld)

> **Executes:** `docs/deos/WORLD-PERSISTENCE-PLAN.md` (the executable task list).
> **Depends on:** M3 for the *UI-subgraph* rider; the **domain-cell half is
> independent of M3 and may land in parallel with it.**

Lift `canonical_ledger_root` to a shared `pub fn` (one implementation, node +
World — WORLD-PERSISTENCE SEAM §1, a *Don't Launder a Load-Bearing Insecurity*
obligation); add the `dregg-persist` (redb) dep gated on `embedded-executor`; add
`store` + `commit_cursor` to `World`; persist genesis installs durably (SEAM §2);
dual-write at `commit_turn` recording `canonical_ledger_root` + the O(change)
`touched_cells`, **fail-closed** on a durable-write error; persist input `Turn`s
so `History` is rebuildable for rewind; `World::open(path)` runs the **exact node
recovery** (checkpoint ⊕ overlay via last-writer-wins `upsert_cell` → fail-closed
convergence check), inheriting `CrashRecovery.lean::recover_eq_replay` by reusing
the same overlay semantics; periodic + on-close durable checkpoints; an in-RAM
ledger-snapshot cache for cheap live scrubbing; boot `main.rs` from
`World::open(path)`. **The UI subgraph persists automatically once M3 lands** — UI
cells ride the same commit log; no separate mechanism.

**Gate:** close-and-reopen restores the exact image (domain — and UI post-M3);
`World::open` returns `Err(Divergent)` on a corrupt store (prove both true and
false — non-vacuity); a genesis-installed cell never touched by a turn survives;
`replay_to(j)` for `j < head` reconstructs a verified past image after reopen.

### M5 — THE FRACTAL META-DEBUG (mirror-caps · the stratified tower · Suspend)

> **Executes:** `docs/deos/FIRMAMENT-REFLEXIVE-SUBSTRATE.md` (Tasks A/B/C);
> `docs/deos/REFLEXIVE-MIGRATION.md` §4.
> **Depends on:** M3 (UI-as-cells, so the cockpit's own state is inspectable cells)
> and M2 (the memo, so nested replay is not O(history·ledger) per level).

Three composing pieces:
- **Task A — the mirror-cap kind.** Add `Target::Mirror{over, depth}` +
  `MirrorDepth{Structure ⊑ ReadState ⊑ Live}` to `dregg-firmament`; the rights
  lattice becomes `AuthRequired × MirrorDepth`; `Capability::attenuate` narrows on
  both axes through the *existing* `is_attenuation` meet. (Independent; first.)
- **Task B — the Suspend gate.** `World{suspended, pending}`, the `commit_turn`
  pre-check, `CommitOutcome::Queued`, `TurnQueued` event, and
  `suspend()`/`resume(Drain | Modified(ConditionalBatch))` draining in
  `execConditionalTurn` topo order. The continuation is a partial turn
  (`ConditionalBatch` whose `Slots` are unfilled — proven machinery). **Suspend =
  halt-the-live-loop** (ember-settled, §5 below), distinct from Snapshot's
  freeze-a-past-cursor. (Independent of A; parallel.)
- **Task C — `FocusTarget::{DebugFrame(MetaLevelId), World, Cockpit}` +
  `MetaDebugView impl Presentable` + the `MetaStack`** replacing the flat `Tab`
  siblings; the suspend-&-inspect button pushes a `MetaLevel` holding a `ReadState`
  mirror over the frozen-but-live head. (Depends on A; reuses B's suspend.)

"Debug the debugger" is then literally focusing the inspector on its own
`MetaDebugView` — recursion through the *same* `present()` dispatch, grounding at
the native gpui loop (no cap, cannot be suspended — the 3-Lisp floor).

**Gate:** the recursive focus terminates at the gpui floor; each meta-level
honestly stamps `Liveness` (paused-live ≠ frozen-past); a `Structure` mirror
refuses to widen to `ReadState`; a turn staged while suspended queues and does not
commit; `resume(modified)` edits *which* turns drain but each still passes the
full `commit_turn` gate.

### COCKPIT gpui TABS for the new modules (continuous, additive)

> **Executes:** the inspector-framework lanes still open in
> `docs/deos/INSPECTOR-FRAMEWORK.md` Part 3 (L2 predicate composer · L3 effect/turn
> builder · L4–L10), made clickable as cockpit tabs (the `3bbec7c34` pattern).
> **Depends on:** L1 only (shipped). Pure-additive; runs alongside M1–M5.

The inspector substrate's ~74 still-`None` census types (the predicate-caveat
language, federation-consensus, circuit internals) burn down here. Each lane is a
gpui-free, `cargo test`-able module a single agent builds; the cockpit tab is a
thin render of the model. **Gate per lane:** the model asserts in `cargo test`;
the tab renders the presentation set / arms the gadget through the verified
`IntentDraft → simulate → commit` spine.

### THE seL4 INTERACTIVE COCKPIT (the device track, independent)

> **Executes:** `docs/desktop-os-research/SEL4-INTERACTIVE-COCKPIT.md` (§2 input,
> §3 live-repaint) + `docs/deos/SEL4-PARITY-PLAN.md` rungs (i)–(ii).
> **Depends on:** nothing in the native track — this is INDEPENDENT of the
> stratified-fixpoint/projection work (SEL4-PARITY §intro). It meets the native
> track only at the very end (the gpui↔framebuffer Mode, kept-in-mind-but-later).

Three additive slices against a known-green build, then the live-turn rung:
1. **Consume input in cockpit mode + add a pointer.** Forward `Nav` into cockpit
   mode (drop the `main.rs:123` early return); add `pointer.rs` + a slot-31
   virtio-tablet (byte-for-byte copy of `keyboard.rs`; `EV_ABS` decode is a new
   arm, not a new primitive) + `apply_pointer` hit-test over the known `view.rs`
   rail geometry.
2. **Live-repaint-on-turn.** Implement the documented-but-empty executor-PD
   channel handler (`turn_in → exec → cells_out/receipt_out → notify`); write
   `deos-live.system` by copying `net.system`'s proven two-PD shared-DMA+channel
   topology; move the viewer's `IMAGE` from a `static` to a mapped `cells_out`
   region (`view.rs` unchanged — `ImageCell` layout identical).

**Gate:** press a key / click → the executor runs a REAL verified turn in its own
PD → the focused cell's balance/nonce/`state_root` re-paint on glass, live. No new
kernel/Microkit/virtio primitive at any step.

---

## 3. THE ORDERED PROGRAM — SOON

Needs the NOW spine first (persistence + the membrane + joint turns + the suspend
mechanism). Sequenced, but not yet started.

### DISTRIBUTED BRANCHING + BRANCH-AND-STITCH

> **Executes:** `docs/deos/BRANCH-AND-STITCH-PROTOCOL.md` (the two new turns) over
> the semantics of `docs/deos/DISTRIBUTED-TIMETRAVEL-SEMANTICS.md`.
> **Depends on:** M4 (persistence — branches fork off durable `WitnessCursor`s) +
> M5 (the membrane / cap-stratified nesting confinement) + the existing joint-turn
> (`FamilyBinding`) machinery + Settlement Soundness in the circuit lane (§4) for
> the stitch door's gate.

Two small turns, everything else composition:
- **`EnterVirtualization`** — a joint turn: parties co-sign to fork a *shared*,
  cap-confined, **honestly-typed** branch world (liveness-type `Virtual/Branch`,
  never `Main/Live`, by construction) off a past cursor, minting a typed
  branch-cap per party.
- **`Stitch`** — the lossy reconciliation primitive: I-confluent parts merge
  cleanly; conflicting parts force *explicit, typed* linear-logic drops; the
  result passes main's gate through the **Settlement Soundness door** (conserves ·
  current-authority-at-the-finalized-tip · no-conflict via nullifier collision).
  The correctness criterion is the pushout (patch theory tells us whether we built
  it right, it does not build it).

The nesting **is** the safety (firmament cap confinement); the single settlement
door **is** the soundness. This is where "fully distributed houyhnhnm" becomes
operable. **Gate:** a branch's side-effects provably cannot leak to main except
through the one gated door; a stitch of a since-revoked authority is rejected at
settlement.

### THE DOCUMENT LANGUAGE (Pijul-shaped, patch-theory)

> **Executes:** `docs/deos/DOCUMENT-LANGUAGE.md` (committed). It is the same
> event-structure/RCCS object of DISTRIBUTED-TIMETRAVEL-SEMANTICS in version-control
> clothes — patch theory as the correctness criterion for `Stitch` (BRANCH-AND-STITCH
> §3, the pushout principle). The one genuinely-new structural module is a **`dregg-doc`
> crate** (the Pijul-shaped patch core: `DocGraph` of alive/dead atoms, the `Patch`
> grammar, merge=pushout, **conflicts-as-first-class-states** = an antichain resolved by a
> later patch); everything else reuses the substrate (transclusion/backlinks/membrane/the
> turn spine/`Confluence.lean`/rhizomatic's 8-op algebra/the Presentable framework).
> **Depends on:** the cell/inspector substrate (L1, shipped); paired with branch-and-stitch
> (the patch is the stitch's morphism into the colimit). NOW: the `dregg-doc` skeleton +
> the I-confluent union path + wire content to the patch-history fold. SOON: conflict-
> states end-to-end through `Stitch` + the `ConflictView` gadget.

Build the patch-theoretic document type on the cell/inspector spine: a document
is a `Presentable` over a patch DAG; edits are patches (turns); merge is the
pushout; the lossy stitch is the universal-property quotient. **Hold the
*syntax*** — see §5; build the *substrate* (patches-as-cells, the merge pushout)
now, let the surface language emerge.

### WORKFLOW REFINEMENT (the `FlowRefine` conformance axis — cross-cutting)

> **Executes:** `docs/DREGGDL-REFINEMENT.md` + `metatheory/Dregg2/Deos/{FlowAlgebra,FlowRefine}.lean`
> (the PROVEN capability: `decideRefines` is a decidable, sound-and-complete simulation game; the
> flow algebra is right-skewed — the algebraic shadow of the *reactive* rung). A separate, already-
> proven *axis* — not missed, woven here.

Behavioral/policy *refinement* (does workflow A refine policy B, decidably) hooks the program at four
points, none of which is a new build so much as a wiring:
- **the settlement/stitch gate** — a `Stitch` must not only conserve (value) + pushout-merge
  (structure) but **refine the policy** main requires (behavior): `FlowRefine` is the third gate at the
  one settlement door (NOW-adjacent: it joins the `Stitch` design under SOON's branch-and-stitch);
- **the reactive rung = M2** — the right-skew flow algebra is the *algebraic shadow* of the online/
  reactive simulation that M2's incremental projection realizes operationally (same reactivity, two
  views — no extra work, a noted correspondence);
- **the document/workflow language** — a DreggDL workflow *is* an authored program-document; `FlowRefine`
  is its conformance check, and the moldable inspector gets a **refinement-game presentation** (folds
  into the DOCUMENT LANGUAGE lane);
- **the ARGUS "refines" bar** — it already rides §4's circuit lane (no-malleability + no-forgotten-
  precondition + *refines*), alongside Settlement Soundness.

So: a cross-cutting conformance axis, mostly *recognition + wiring* of a proven capability. Carried with
branch-and-stitch (the gate), the document language (the check), and the circuit lane (the bar).

### M6 — seL4 PERSIST-PD (`BlockCapBackend`)

> **Executes:** `docs/deos/REFLEXIVE-MIGRATION.md` §5.2 + `docs/deos/SEL4-PARITY-PLAN.md`
> rung (iii) + `SEL4-INTERACTIVE-COCKPIT.md`'s persist seam.
> **Depends on:** the seL4 live-repaint rung (NOW · the device track) for the
> executor→persist `commit_out` framing. Independently sequenced from the native
> M4 — they are the *same* durable store at two points on `n` (the same
> `CommitRecord` bytes).

The single named wall: `BlockCapBackend` — one `redb::StorageBackend` impl routing
the 5 ops (len/read/set_len/sync_data/write) through the seL4 virtio-blk block cap;
plus the `commit_out` framing + the persist-PD ELF link. The durable store above
it is host-green and **byte-identical** (~21 tests). **Gate:** the in-VM image
persists across a PD restart with the same `CommitRecord` bytes the host World
persists to local redb — the `n=1` collapse.

### THE FULL NODE IN seL4 (the heaviest wave, last)

> **Executes:** `docs/deos/SEL4-PARITY-PLAN.md` rung (iv).
> **Depends on:** M6 + the seL4 spine proving out. The producer-in-VM port is the
> genuinely-new, heaviest systems work — net-client→executor turn ingress + the
> blocklace/drainer over `no_std`+`alloc`. Sequence it last.

---

## 4. THE ORDERED PROGRAM — IN THE CIRCUIT LANE

ember's active circuit-soundness campaign (`project-circuit-soundness-apex`). This
lane runs in parallel with the desktop migration and is where
distributed-houyhnhnm bottoms out — it makes the SOON distributed-branching
*light-client-checkable*.

### THE SETTLEMENT SOUNDNESS THEOREM (the one thing to pursue)

> **Executes:** `docs/deos/DISTRIBUTED-TIMETRAVEL-SEMANTICS.md` §6.3 — the narrow,
> named, high-value construction (not a re-derivation of the whole event-structure
> axiomatization, which the existing proofs already discharge).

The theorem:

> **(Settlement Soundness.)** If a turn `T` settles on the finalized tip at height
> `h`, then every capability `T` exercised is honored by the tip's finalized
> revocation set at `h` — and the commitment at `h` binds that revocation set, so a
> light client accepting the settled batch can verify it.

It is a genuine **extension** of `AssuranceCase.lean::unfoolability_guarantee`
("accept ⟹ genuine transition") to "accept ⟹ genuine transition *whose authority
was live at settlement*." **Compose, don't re-derive:** `Revocation.lean`'s
topology-bounded revocation (the `localRevSet`/`honors`/`eventual_bounded_revocation`
spine) ∘ `FinalizedLightClient.lean`'s commitment ∘ the cap-bridge. It is the
`holeFill_binds_in_circuit` discipline applied to the late-bound **negative** fact
of revocation — exactly the stratified-negation-points-downward identity, with
*settlement as the stratum boundary*.

**The one binding to confirm FIRST** (it decides "compose" vs "extend-then-compose"):
does the finality gate already bind the **settlement-time revocation set** into the
finalized commitment? This is the kernel `RevocationSet` root (#139) in the
finalized leg. If already bound, Settlement Soundness is a composition; if not, the
bind is a small descriptor/commitment change that is a **floor under the proof and
comes first** (a *Don't Launder a Load-Bearing Insecurity* / floor-comes-first
obligation). This is the **next read** in the lane.

The two residual obligations to prove, not assume (DISTRIBUTED-TIMETRAVEL §4.4):
(1) settlement commits the revocation set it evaluated against; (2) the
propagation-delay bound lives *inside* the finality gate, so two honest nodes
cannot disagree about whether a since-revoked authority settled (the `n=1`
collapse makes this trivial; `n>1` is where it is load-bearing).

**Gate:** the composed theorem is `#assert_axioms`-clean and non-vacuous (a turn
exercising a since-revoked cap fails to settle — prove both the honored case
accepts and the revoked case rejects).

---

## 5. RESEARCH / LET-IT-BREATHE (deliberately not-now)

Named, with their closure understood, but deliberately *unscheduled* — building
them now would be premature:

- **The document-language *syntax*** — build the patch substrate (SOON); let the
  surface language *emerge* from use rather than designing it up front.
- **The full event-structure axiomatization** (the comonad / HoTT / Winskel-domain
  formalizations) — illuminating to *name* (they confirm the shape;
  DISTRIBUTED-TIMETRAVEL §6.4 step 5), **not load-bearing to build**. The pieces
  (`LaceMerge`, `CrashRecovery`, `Confluence`, `BlocklaceFinality`, `Revocation`)
  already discharge the load-bearing facts. Optional elegance, not a proof
  obligation.
- **The blocklace-substrate-pluggability question** — whether the durable
  spine/blocklace is swappable under the same event-structure semantics. A research
  question, not a current need.
- **Precise (vs. coarse) viewer-non-local affordance invalidation** — defer the
  per-viewer-precise affordance cache until profiling shows cap-edge churn is hot
  (EFFICIENCY-WELD §4.2); the coarse `invalidate_affordances_all()` is correct now.
- **The recorder double-ledger collapse** — stage, do not rip out under M4
  (WORLD-PERSISTENCE SEAM §2); a separate, later efficiency move once the durable
  log + genesis table fully subsume the replay tape.

---

## 6. THE DEPENDENCY GRAPH + THE FIRST CONCRETE COMMIT

### The graph

```
   [LIVE: inspector substrate L1–L10 · cockpit tabs · liveness wave · ui_snapshot]
                                   │
                                   ▼
   ┌──────────── M1+M2  THE EFFICIENCY WELD  (microbench GATE) ◀── start here
   │                       │
   │   (independent)       ├─────────────► M3  UI-AS-CELLS  (unit-delay default)
   │   COCKPIT gpui tabs   │                    │
   │   (L2…L10, additive)  │           ┌────────┼────────────┐
   │                       │           ▼        ▼            ▼
   │                       │      M4 PERSIST   M5 META-DEBUG (mirror-cap ·
   │                       │      (domain half  Suspend · MetaStack)
   │                       │       ∥ M3)            │
   │                       │           │            │
   │   ┌── seL4 INTERACTIVE COCKPIT ───┤            │
   │   │   (input · live-repaint;      │            │
   │   │    INDEPENDENT device track)  │            │
   │   │            │                  │            │
   ▼   ▼            ▼                  ▼            ▼
 ─────────────────  SOON  ───────────────────────────────────
   M6 seL4 persist-PD     DISTRIBUTED BRANCHING + branch-and-stitch
   (BlockCapBackend)        (EnterVirtualization + Stitch)
        │                          │            │
        ▼                          │            ▼
   FULL NODE in seL4               │      DOCUMENT LANGUAGE (Pijul/patch)
                                   │
   ── CIRCUIT LANE (parallel) ─────┘
   SETTLEMENT SOUNDNESS  =  Revocation ∘ FinalizedLightClient ∘ cap-bridge
   (gates the stitch door; confirm the #139 RevocationSet-root bind FIRST)
```

### The first concrete commit

**Start at M1's `state_root` memo** (EFFICIENCY-WELD §1.1, §5 step 1). Concretely:
add a `state_root_memo: StdCell<Option<(u64, [u8;32], [u8;32])>>` field to `World`
(`world.rs:71`), initialize it in both constructors, split the existing
`state_root` body into a private `compute_state_root`, rewrite `state_root` to
check/fill the memo keyed on `(height, receipt_head)`, and invalidate (`set(None)`)
in `install_genesis` + the three genesis-path ledger writers. Verify with `cargo
check -p starbridge-v2`, the existing `state_root_changes_when_state_changes`, and
a new `state_root_memoized_within_same_height`. That is the literal first edit; the
re-sort kill (step 2) and the M2 delta loop follow, and the M2 microbench number is
the gate out of the weld.

---

## 7. THE SETTLED ember-DECISIONS (do not re-litigate)

These are resolved; they are recorded here so a picking-up agent does not reopen
them:

- **Unit-delay (z⁻¹) everywhere by default for the UI/view strata** (S₃ and up);
  the within-frame stratified fixpoint is reserved for the authority strata only,
  where the firmament hands the strata for free (STRATIFIED-FIXPOINT §7.3). The
  reflexive fixpoint **is well-defined — yes, by attenuation**; the remaining
  choice is a per-stratum *cost* question, not a correctness one.
- **Suspend = halt-the-live-loop** (a `commit_turn` gate + a `pending` queue + the
  continuation reified as a partial turn), distinct from Snapshot =
  freeze-a-past-cursor (FIRMAMENT-REFLEXIVE-SUBSTRATE §3.1). Both exist; they are
  complementary axes.
- **An input-turns table** is the persisted-`Turn` decision: persist input turns
  alongside post-state records so close→reopen→scrub-to-any-past-turn holds
  (WORLD-PERSISTENCE §A.4 recommended path) — the rewindable image, not merely the
  resumable one.
- **Durable-write failure is fail-closed by default** (the World refuses to ack a
  commit it could not durably record), degraded-readonly being the explicit,
  banner-named opt-out (WORLD-PERSISTENCE §A.2.1).
- **Adopt `canonical_ledger_root` as the durable convergence root**, keeping BLAKE3
  `state_root` only as a fast memoized *view* tooth — two different roots with two
  different jobs, neither conflated, lifted to ONE shared implementation
  (WORLD-PERSISTENCE SEAM §1).
- **Same-stratum mutual negation is closed by a `CellId` tie-break + well-founded
  fallback**, implemented *with* the first authority-stratum fixpoint, never
  deferred (STRATIFIED-FIXPOINT §6.4, §7.3.3).
- **Settlement-time (not branch-time) authority evaluation** is the one behavioral
  rule that prevents the subtle revocation bug; settlement is the stratification /
  irreversible-commit boundary (DISTRIBUTED-TIMETRAVEL §4.2, §6.4).
- **The native World and the in-VM seL4 image are two points on `n`, not two
  systems** — the same executor, the same `CommitRecord`/chain gate, the same
  cells; parity is "realize the same image at `n=1`," not "port to a weaker
  platform" (SEL4-PARITY §1.6, §3).

---

*( ◕‿◕ ) a closing couplet, since the whole tower stands on one memoized stone:*

*the ledger need not be re-read whole each frame —*
*memoize the root, and the rest unfolds in order from that flame.*
