/-
# Dregg2.Apps.Compositor — THE VERIFIED COMPOSITOR (output-integrity = unfoolability on the scene).

**THE THESIS (`docs/DREGG-DESKTOP-OS.md §5).** dregg already proves a light client checking
`verify root = true` cannot be fooled by *the pale ghost* (a server lying about protocol state,
`AssuranceCase.unfoolability_guarantee`). The compositor asks the SAME question one hop further out:
**can the HUMAN at the glass be fooled?** The pale ghost on the display is a UI that paints pixels
claiming "cell C holds balance B" when C does not, OR steals the keystroke meant for C and routes it
to attacker A. **Output-integrity IS unfoolability applied to the display path.**

**THE COMPOSITOR IS A VERIFIED DREGG CELL.** Its state IS the scene graph — an ordered list of
surfaces, each `(owningCellId, regionRect, contentDigest, sourceStateRoot, zLayer, focusFlag)`.
Compositing is a TURN: a cell submits `present(region, contentDigest @ myStateRoot)` against the
compositor cell, and the executor's caveat gate enforces the scene invariants AS anti-ghost teeth via
the EXISTING `VerificationToolkit` machinery (the SAME pattern that welded 45+ effects —
`app_commit_iff_admit` + `app_violation_rejected` come for free from a well-formed `AppSpec`).

## The three scene-authority teeth (verifiable NOW, pure Lean, zero new axioms)

  * **T1 NON-OVERLAP** — a cell writes ONLY regions its capability authorizes: `granted ⊆ held` with
    `Rights = region-set`, on the SAME `is_attenuation` (`granted ⊆ held`) lattice the firmament uses
    (`sel4/dregg-firmament` `is_attenuation`; Lean `BiscuitGraph.attenuates = child.authority ⊆
    parent.authority`, `Agent.Mandate.keep ⊆ parent.keep`). Overpainting another cell's region is
    **UNSAT**: a present whose target region is not `⊆` the presenter's granted region-set is rejected.
  * **T2 LABEL-BINDING** — every surface's rendered label is a FUNCTION of `owningCellId +
    sourceStateRoot`, read BY THE COMPOSITOR from cell state, NOT supplied by the app (the executor
    knows the authority lineage — which factory minted it, sovereign-vs-hosted, attenuation depth, all
    unforgeable by the client). A present declaring a label ≠ `labelOf owner sourceStateRoot` is
    **UNSAT**. This is Nitpicker's floating label UPGRADED from a server courtesy to a verified
    state-root binding a light client can independently check.
  * **T3 FOCUS-EXCLUSIVITY** — at-most-one `focusFlag`; input routes only to it. A scene with two
    focus flags, or a present that delivers input to a non-focused cell, is **UNSAT** (EROS
    *traceability of volition* as a state invariant — only the USER selects focus, the input analogue
    of "only connectivity begets connectivity").

(T4 NO-INFERENCE — `present()` reads only its own region's prior contents — is the cap-scoped-read
double-buffering discipline; it is an info-flow property of the read path, NOT a scene-admission
predicate, so it is deliberately OUT of this admit-conjunction and stated as a separate note in §11.)

## How the rich scene folds into the scalar `AppSpec.admit` boundary (the `ToolAccessDelegation` move)

At the executor boundary a `present()` is the single scalar write `present_digest : old → new` on the
compositor cell's frame slot — `new` is the content digest the presenter is committing for its region.
The WHOLE scene structure — the prior surfaces (the region→owner map), the focus holder, the
presenter's granted region-set, the genuine owner-label — is **CLOSED OVER** into the toolkit's
`admit : Int → Int → Bool` at scene-snapshot time, EXACTLY as `ToolAccessDelegation.delegAdmit` closes
over `(toolId, rateLimit, deadline)` and `cwmSpec` closes over the charter DAG. The compositor knows
the presenter (it is the turn's actor, fixed per `present()` call), so a present builds a spec FOR
THIS (scene, presenter, targetRegion) presentation. A DIFFERENT presenter / region / label produces a
DIFFERENT baked `.admitTable`, so the teeth bite on GENUINELY-DISTINCT adversarial scenes, not
trivially-malformed ones — an overpaint by a real second cell, a real label-spoof, a real double-focus.

## Headline theorem

`output_integrity_eq_unfoolability_on_scene` — on the compositor cell carrying the scene caveats, the
PRODUCTION caveat-gated executor write COMMITS a `present()` IFF the scene invariants T1∧T2∧T3 admit it
(AND the presenter held authority over the compositor cell). The scene the user sees inherits the SAME
root-binding the ledger does: a present the scene-authority forbids does NOT commit (`= none`), so the
post-state root the light client verifies can only ever reflect a T1∧T2∧T3-respecting scene. This is
`VerificationToolkit.app_commit_iff_admit` instantiated — over the WHOLE `RecChainedState` post-state,
not a projection.

And the TEETH (`*_rejected`): an OVERPAINT (T1), a LABEL-SPOOF (T2), and a DOUBLE-FOCUS /
INPUT-MISROUTE (T3) are each rejected by the executor (`= none`). Plus the kernel keystones
(`*_conserves`/`*_no_amplify`/`*_authorized`): compositing moves NO balance and mints NO capability —
the compositor mediates AUTHORITY, never value.

**THE FRONTIER (honestly labeled, NOT solved here).** Binding the *scanned-out framebuffer* to the
cell's `contentDigest` (F1 last-hop frame attestation), IOMMU/DMA confinement of a malicious display
PD (F2), and a verified GPU/servo compositor (F3) are named hardware-trust assumptions in §5 — severe
problems with closure lanes, never walls. THIS module builds the T1–T3 *scene-authority* teeth that
ARE verifiable now (a CPU-composited software compositor cell, à la EROS/Nitpicker). It does NOT claim
the graphics crypto-floor. Direct lineage: EROS Trusted Window System (EWS, Shapiro et al. 2004) and
Nitpicker (Feske & Helmuth 2005, the ~1,500-LOC small-TCB existence proof).

`#assert_axioms`-clean. Pure, computable, `#eval`-able.
NEW file only — touches NO existing app, `VerificationToolkit.lean`, the executor, nor `Dregg2.lean`.
-/
import Dregg2.Apps.VerificationToolkit

namespace Dregg2.Apps.Compositor

open Dregg2.Exec
open Dregg2.Exec.EffectsState (caveatsAdmit fieldOf stateStep stateStepGuarded)
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Apps.VerificationToolkit
open Dregg2.Spec (execGraph)

/-! ## §1 — The scene graph: surfaces, regions, and the closed-over compositor view.

A `Surface` is one entry of the scene graph: a cell's owned rectangle, the content digest it is
showing, the source state-root that content is a projection of, its z-layer, and whether it holds
input focus. A region is modelled as a `RegionId` (an opaque rectangle identity — a tile id); a
present targets exactly one region and the non-overlap discipline is the region-set `⊆` lattice (two
surfaces may not own the same region). This is the executable shadow of the §5 scene-graph tuple
`(owningCellId, regionRect, contentDigest, sourceStateRoot, zLayer, focusFlag)`. -/

/-- An opaque region (rectangle / tile) identity. The compositor's regions partition the glass; a
surface owns a SET of regions; two surfaces' region-sets must be disjoint (T1 non-overlap). -/
abbrev RegionId := Nat

/-- One surface in the scene graph (§5's per-surface tuple). -/
structure Surface where
  /-- The cell that owns this surface — the authority lineage the compositor reads from cell state. -/
  owner          : CellId
  /-- The set of regions (tiles) this surface occupies. Non-overlap (T1) = these are pairwise
  disjoint across surfaces, and a present by `owner` may target only regions in `owner`'s set. -/
  regions        : List RegionId
  /-- The content digest currently shown in this surface (the projection of `sourceStateRoot`). -/
  contentDigest  : Int
  /-- The cell state-root this content is a genuine projection of (the light-client-checkable bind). -/
  sourceStateRoot : Int
  /-- The z-layer (stacking order). The trusted-path overlay lives at a layer no cell holds (§5 SAK). -/
  zLayer         : Int
  /-- Whether this surface currently holds input focus (T3: at-most-one across the scene). -/
  focusFlag      : Bool
  deriving Repr, DecidableEq

/-- The compositor's scene: the ordered list of surfaces. THIS is the verified dregg cell's state
(§5: "Its state IS the scene graph — an ordered list of surfaces"). -/
structure Scene where
  surfaces : List Surface
  deriving Repr, DecidableEq

/-! ## §2 — The genuine owner-label (T2): a FUNCTION of `owner + sourceStateRoot`, read by the
compositor, NOT the app.

The compositor renders each surface's label by HASHING the authority lineage `(owner, sourceStateRoot)`
— a value the app cannot forge because the executor, not the client, knows the owner and the committed
state-root. `labelOf owner root` is that pure function. T2 requires a present's DECLARED label to equal
`labelOf owner root` for the presenting owner; a label ≠ owner is rejected. (Here `labelOf` is a simple
injective-enough mixing function for the executable model; the real compositor uses Poseidon2 over the
structured provenance lattice — §8 CryptoPortal — but the BINDING DISCIPLINE is what T2 enforces and is
renderer-agnostic.) -/

/-- **`labelOf owner root`** — the genuine surface label the compositor renders for a surface owned by
`owner` projecting state-root `root`. A pure function of the authority lineage (T2's binding). The app
NEVER supplies this; the compositor computes it from cell state. -/
def labelOf (owner root : Int) : Int := owner * 1000003 + root

/-! ## §3 — The scene invariants T1, T2, T3 as decidable predicates over the closed-over scene.

Each is a `Bool` predicate the compositor decides from the scene it reads. They are folded into the
toolkit's scalar `admit` in §5. Decidable, computable, FAIL-CLOSED. -/

/-- `sublist xs ys` — every element of `xs` is in `ys` (the region-set `⊆` order; the SAME
`granted ⊆ held` shape as `BiscuitGraph.attenuates` / `Mandate.keep ⊆ parent.keep`). -/
def sublist (xs ys : List RegionId) : Bool := xs.all (fun x => ys.contains x)

/-- **T1 NON-OVERLAP (admission form).** A present by `presenter` targeting region-set `target` is
T1-admissible against scene `sc` iff: (a) `target ⊆ presenter`'s granted region-set (the presenter
writes only regions it owns — `granted ⊆ held`), AND (b) `target` is disjoint from EVERY OTHER
surface's regions (no overpaint of a region another cell owns). The closed-over scene supplies the
region→owner map; an overpaint = a `target` overlapping a foreign surface ⇒ `false`. -/
def t1NonOverlap (sc : Scene) (presenter : CellId) (target : List RegionId) : Bool :=
  -- (a) the presenter actually owns a surface, and target ⊆ its granted regions:
  (sc.surfaces.any (fun s => decide (s.owner = presenter) && sublist target s.regions))
  -- (b) target is disjoint from every FOREIGN surface's regions (no overpaint):
  && sc.surfaces.all (fun s =>
       decide (s.owner = presenter) || target.all (fun r => !s.regions.contains r))

/-- **T2 LABEL-BINDING (admission form).** A present by `presenter` whose surface projects
`sourceStateRoot` and DECLARES label `declaredLabel` is T2-admissible iff `declaredLabel = labelOf
presenter sourceStateRoot` — the label is the genuine owner-binding the compositor computes, not an
app-chosen string. A label ≠ owner ⇒ `false`. -/
def t2LabelBound (presenter : CellId) (sourceStateRoot declaredLabel : Int) : Bool :=
  decide (declaredLabel = labelOf (presenter : Int) sourceStateRoot)

/-- **T3 FOCUS-EXCLUSIVITY (admission form).** The scene `sc` is T3-admissible iff AT MOST ONE surface
holds `focusFlag` (`countFocus ≤ 1`). A double-focus scene ⇒ `false`. (Input-misroute is the dual,
checked in §6: a present claiming focus when the scene's focus holder is a DIFFERENT cell is rejected.) -/
def countFocus (sc : Scene) : Nat := (sc.surfaces.filter (·.focusFlag)).length

def t3FocusExclusive (sc : Scene) : Bool := decide (countFocus sc ≤ 1)

/-- **T3 input-routing (admission form).** A present by `presenter` that asserts input focus
(`claimsFocus = true`) is input-route-admissible against `sc` iff `presenter` IS the scene's unique
focus holder. Delivering input to a non-focused cell ⇒ `false`. When a present does not assert focus
(`claimsFocus = false`) this leg is vacuously satisfied (a non-input present). -/
def focusHolder (sc : Scene) : Option CellId :=
  (sc.surfaces.find? (·.focusFlag)).map (·.owner)

def t3InputRouted (sc : Scene) (presenter : CellId) (claimsFocus : Bool) : Bool :=
  !claimsFocus || (focusHolder sc == some presenter)

/-! ## §4 — The folded scene-admission predicate (the WHOLE scene authority at the scalar boundary).

A `present()` is the scalar write `present_digest : old → new`. The scene authority admits it iff
T1 ∧ T2 ∧ T3 all hold for the closed-over `(scene, presenter, target, sourceStateRoot, declaredLabel,
claimsFocus)`. This is exactly the toolkit's `admit : Int → Int → Bool` — all the rich scene structure
folded into the scalar boundary BEFORE it reaches the executor (the `ToolAccessDelegation.delegAdmit`
shape). The `(old, new)` digit transition is the frame advance; the scene authority is closed over. -/

/-- A `Present` bundles what a `present()` call presents: the targeted region-set, the source
state-root the content projects, the declared label, and whether it asserts input focus. The
content-digest transition `old → new` is the scalar slot move (the toolkit's `(old, new)`). -/
structure Present where
  /-- The region-set this present writes (T1: must be `⊆` the presenter's owned regions, disjoint
  from foreign surfaces). -/
  target          : List RegionId
  /-- The state-root the presented content is a projection of (T2: binds the label). -/
  sourceStateRoot : Int
  /-- The label the present declares (T2: must equal `labelOf presenter sourceStateRoot`). -/
  declaredLabel   : Int
  /-- Whether this present asserts input focus (T3: only the scene's unique focus holder may). -/
  claimsFocus     : Bool
  deriving Repr, DecidableEq

/-- **`sceneAdmit sc presenter p old new`** — does the scene authority admit the `present()` that
advances the compositor frame digest `old → new`, by `presenter`, presenting `p`, against the
closed-over scene `sc`? The conjunction T1 ∧ T2 ∧ T3 (non-overlap ∧ label-bound ∧ focus-exclusive ∧
input-routed) AND a genuine single-frame digest advance (`new ≠ old` — a present changes the frame).
Decidable, computable, FAIL-CLOSED on every conjunct. -/
def sceneAdmit (sc : Scene) (presenter : CellId) (p : Present) (old new : Int) : Bool :=
  t1NonOverlap sc presenter p.target                               -- T1: non-overlap / granted ⊆ held
    && t2LabelBound presenter p.sourceStateRoot p.declaredLabel    -- T2: label = function of owner
    && t3FocusExclusive sc                                         -- T3: at-most-one focus flag
    && t3InputRouted sc presenter p.claimsFocus                    -- T3: input routes only to focus
    && decide (new ≠ old)                                          -- a present genuinely advances the frame

/-! ## §5 — The compositor cell as a toolkit `AppSpec`.

The `AppSpec` installs an `.admitTable` baked from `sceneAdmit` on the `present_digest` slot. The grid
is the finite set of content digests the frame ranges over (the toolkit is fail-closed by absence
outside the grid — SOUND, never admits more than `sceneAdmit`). The `(sc, presenter, p)` are closed
into the spec, so the baked table is the scene authority FOR THIS PRESENTATION — exactly as
`ToolAccessDelegation.mandateSpec` closes `(g, now, tool)`. -/

/-- The compositor cell's frame-digest slot (the scalar state a `present()` advances). -/
def presentDigestSlot : FieldName := "present_digest"

/-- **`compositorSpec sc presenter p cell oldRange newRange`** — the compositor scene as a
`VerificationToolkit.AppSpec`: the `present_digest` slot, the compositor cell, the folded
`sceneAdmit sc presenter p` predicate, over the supplied digest grid. The toolkit bakes the
`.admitTable` and gives us commit-iff-admit + the rejection teeth + conservation + non-amplification
with NO re-proof. -/
def compositorSpec (sc : Scene) (presenter : CellId) (p : Present) (cell : CellId)
    (oldRange newRange : List Int) : AppSpec where
  slot     := presentDigestSlot
  cell     := cell
  admit    := sceneAdmit sc presenter p
  oldRange := oldRange
  newRange := newRange

/-- The compositor's `present_digest`-slot program is exactly an `.admitTable` baked from `sceneAdmit`. -/
theorem compositorSpec_caveats (sc : Scene) (presenter : CellId) (p : Present) (cell : CellId)
    (oldRange newRange : List Int) :
    (compositorSpec sc presenter p cell oldRange newRange).caveats
      = [ .admitTable presentDigestSlot
            (compositorSpec sc presenter p cell oldRange newRange).admitTable ] := rfl

/-! ## §6 — THE HEADLINE: output-integrity = unfoolability on the scene (toolkit-instantiated).

On the compositor cell carrying the scene caveats, the PRODUCTION caveat-gated executor write — i.e.
`execFullA (.setFieldA presenter cell "present_digest" new)`, which is DEFINITIONALLY `stateStepGuarded`
(`TurnExecutorFull.lean:3794`) — COMMITS (is `some`) IFF the scene authority T1∧T2∧T3 admits the
present AND the presenter holds authority over the compositor cell. The whole `RecChainedState`
post-state, not a projection: a committed present means BOTH the scene authority AND the authority gate
fired; any T1/T2/T3 violation means `= none`. So the post-state root a light client verifies can only
ever reflect a scene the user cannot be fooled by. -/

/-- **`setFieldA_is_stateStepGuarded`** — the production executor's `setFieldA` arm IS the caveat gate
over a NON-RESERVED field. The `execFullA` `setFieldA` arm is the reserved-slot-gated `stateStepDev`
(`stateStepDev = if reservedField f then none else stateStepGuarded`); the compositor only ever writes
the developer field `present_digest`, which is NOT a reserved protocol slot (`reservedField f = false`),
so the dev gate passes through to `stateStepGuarded`. The bridge that makes every toolkit theorem about
`stateStepGuarded` a theorem about `execFullA` for a non-reserved field. -/
theorem setFieldA_is_stateStepGuarded (s : RecChainedState) (actor cell : CellId) (f : FieldName)
    (v : Int) (hnr : Dregg2.Exec.EffectsState.reservedField f = false) :
    execFullA s (.setFieldA actor cell f v) = stateStepGuarded s f actor cell v := by
  show Dregg2.Exec.EffectsState.stateStepDev s f actor cell v = stateStepGuarded s f actor cell v
  unfold Dregg2.Exec.EffectsState.stateStepDev; rw [if_neg (by rw [hnr]; simp)]

/-- **`output_integrity_eq_unfoolability_on_scene` — THE HEADLINE.** On the compositor cell carrying
the scene caveats, with the committed frame digest `old` and the presented digest `new` on the grid,
the production caveat-gated executor COMMITS the `present()` IFF the scene authority admits it
(`sceneAdmit sc presenter p old new` — T1 non-overlap ∧ T2 label-bound ∧ T3 focus-exclusive ∧
input-routed) AND the presenter held authority. **Output-integrity = unfoolability applied to the
display path:** the scene the user sees inherits the executor's root-binding, so a present the
scene-authority forbids cannot enter the committed state a light client verifies. -/
theorem output_integrity_eq_unfoolability_on_scene
    (sc : Scene) (presenter : CellId) (p : Present) (cell : CellId)
    (oldRange newRange : List Int) (s : RecChainedState) (old new : Int)
    (hprog : s.kernel.slotCaveats cell
      = (compositorSpec sc presenter p cell oldRange newRange).caveats)
    (hcur : (compositorSpec sc presenter p cell oldRange newRange).committed s.kernel = old)
    (hold : old ∈ oldRange) (hnew : new ∈ newRange) :
    (execFullA s (.setFieldA presenter cell presentDigestSlot new)).isSome = true
      ↔ (sceneAdmit sc presenter p old new = true
          ∧ (stateStep s presentDigestSlot presenter cell (.int new)).isSome = true) := by
  rw [setFieldA_is_stateStepGuarded _ _ _ _ _
        (by decide : Dregg2.Exec.EffectsState.reservedField presentDigestSlot = false)]
  have h := app_commit_iff_admit (compositorSpec sc presenter p cell oldRange newRange) s hprog
    presenter new (by rw [hcur]; exact hold) hnew
  rw [hcur] at h
  exact h

/-! ## §7 — THE TEETH: overpaint (T1) / label-spoof (T2) / double-focus & input-misroute (T3) REJECTED.

Each is `app_violation_rejected` instantiated at a present whose `sceneAdmit` is FALSE, so the
production executor returns `none` — the present does not commit. Proven generically (any present whose
relevant invariant fails), then witnessed on genuinely-distinct adversarial scenes in §10. -/

/-- **`present_rejected` — the GENERIC tooth.** ANY present the scene authority rejects
(`sceneAdmit = false` — overpaint, label-spoof, double-focus, or input-misroute) is rejected by the
production executor: `execFullA (.setFieldA …) = none`. -/
theorem present_rejected
    (sc : Scene) (presenter : CellId) (p : Present) (cell : CellId)
    (oldRange newRange : List Int) (s : RecChainedState) (old new : Int)
    (hprog : s.kernel.slotCaveats cell
      = (compositorSpec sc presenter p cell oldRange newRange).caveats)
    (hcur : (compositorSpec sc presenter p cell oldRange newRange).committed s.kernel = old)
    (hold : old ∈ oldRange) (hnew : new ∈ newRange)
    (hbad : sceneAdmit sc presenter p old new = false) :
    execFullA s (.setFieldA presenter cell presentDigestSlot new) = none := by
  rw [setFieldA_is_stateStepGuarded _ _ _ _ _
        (by decide : Dregg2.Exec.EffectsState.reservedField presentDigestSlot = false)]
  exact app_violation_rejected (compositorSpec sc presenter p cell oldRange newRange) s hprog
    presenter new (by rw [hcur]; exact hold) hnew (by rw [hcur]; exact hbad)

/-- **`present_overpaint_rejected` — the T1 (NON-OVERLAP) tooth.** A present whose target region-set
overpaints — i.e. T1 fails (`t1NonOverlap sc presenter p.target = false`: the target is not `⊆` the
presenter's granted regions, OR it overlaps a foreign surface) — is rejected by the executor, EVEN with
a correct label and an exclusive focus. A cell cannot paint a region another cell owns. -/
theorem present_overpaint_rejected
    (sc : Scene) (presenter : CellId) (p : Present) (cell : CellId)
    (oldRange newRange : List Int) (s : RecChainedState) (old new : Int)
    (hprog : s.kernel.slotCaveats cell
      = (compositorSpec sc presenter p cell oldRange newRange).caveats)
    (hcur : (compositorSpec sc presenter p cell oldRange newRange).committed s.kernel = old)
    (hold : old ∈ oldRange) (hnew : new ∈ newRange)
    (hoverpaint : t1NonOverlap sc presenter p.target = false) :
    execFullA s (.setFieldA presenter cell presentDigestSlot new) = none := by
  refine present_rejected sc presenter p cell oldRange newRange s old new hprog hcur hold hnew ?_
  unfold sceneAdmit
  rw [hoverpaint]; simp

/-- **`present_label_spoof_rejected` — the T2 (LABEL-BINDING) tooth.** A present whose declared label
is NOT the genuine owner-binding (`t2LabelBound presenter p.sourceStateRoot p.declaredLabel = false`,
i.e. `declaredLabel ≠ labelOf presenter sourceStateRoot`) is rejected, EVEN with a valid region and an
exclusive focus. The pale ghost cannot paint a window labelled as a cell it is not. -/
theorem present_label_spoof_rejected
    (sc : Scene) (presenter : CellId) (p : Present) (cell : CellId)
    (oldRange newRange : List Int) (s : RecChainedState) (old new : Int)
    (hprog : s.kernel.slotCaveats cell
      = (compositorSpec sc presenter p cell oldRange newRange).caveats)
    (hcur : (compositorSpec sc presenter p cell oldRange newRange).committed s.kernel = old)
    (hold : old ∈ oldRange) (hnew : new ∈ newRange)
    (hspoof : t2LabelBound presenter p.sourceStateRoot p.declaredLabel = false) :
    execFullA s (.setFieldA presenter cell presentDigestSlot new) = none := by
  refine present_rejected sc presenter p cell oldRange newRange s old new hprog hcur hold hnew ?_
  unfold sceneAdmit
  rw [hspoof]; simp

/-- **`present_double_focus_rejected` — the T3 (FOCUS-EXCLUSIVITY) tooth.** A present against a scene
with TWO focus flags (`t3FocusExclusive sc = false`, `countFocus sc ≥ 2`) is rejected — no present can
commit into a scene that already routes input ambiguously. At-most-one focus is load-bearing. -/
theorem present_double_focus_rejected
    (sc : Scene) (presenter : CellId) (p : Present) (cell : CellId)
    (oldRange newRange : List Int) (s : RecChainedState) (old new : Int)
    (hprog : s.kernel.slotCaveats cell
      = (compositorSpec sc presenter p cell oldRange newRange).caveats)
    (hcur : (compositorSpec sc presenter p cell oldRange newRange).committed s.kernel = old)
    (hold : old ∈ oldRange) (hnew : new ∈ newRange)
    (hdouble : t3FocusExclusive sc = false) :
    execFullA s (.setFieldA presenter cell presentDigestSlot new) = none := by
  refine present_rejected sc presenter p cell oldRange newRange s old new hprog hcur hold hnew ?_
  unfold sceneAdmit
  rw [hdouble]; simp

/-- **`present_input_misroute_rejected` — the T3 (INPUT-ROUTING) tooth.** A present that ASSERTS input
focus (`p.claimsFocus = true`) but whose presenter is NOT the scene's unique focus holder
(`t3InputRouted sc presenter p.claimsFocus = false`) is rejected — input is delivered ONLY to the cell
the user demonstrably chose. A cell cannot steal a keystroke meant for the focused cell. -/
theorem present_input_misroute_rejected
    (sc : Scene) (presenter : CellId) (p : Present) (cell : CellId)
    (oldRange newRange : List Int) (s : RecChainedState) (old new : Int)
    (hprog : s.kernel.slotCaveats cell
      = (compositorSpec sc presenter p cell oldRange newRange).caveats)
    (hcur : (compositorSpec sc presenter p cell oldRange newRange).committed s.kernel = old)
    (hold : old ∈ oldRange) (hnew : new ∈ newRange)
    (hmisroute : t3InputRouted sc presenter p.claimsFocus = false) :
    execFullA s (.setFieldA presenter cell presentDigestSlot new) = none := by
  refine present_rejected sc presenter p cell oldRange newRange s old new hprog hcur hold hnew ?_
  unfold sceneAdmit
  rw [hmisroute]; simp

/-! ## §8 — The kernel keystones at the compositor boundary (re-exported, no re-proof).

A committed present moves NO balance (`present_digest ≠ balance`) and mints NO capability (the
caveat-gated metadata write never edits the cap table). So the compositor mediates AUTHORITY over the
scene, never value — it never becomes a second authority over state (§5: "the compositor NEVER becomes
a second authority"). These lift verbatim through the toolkit's `app_commit_*` carriers via the
`setFieldA = stateStepGuarded` bridge. -/

/-- A nominal scene/present/spec used only to instantiate the balance-neutral / no-amplify carriers
(they are independent of the scene content — the field is `present_digest ≠ balance` regardless). -/
private def anyScene : Scene := ⟨[]⟩
private def anyPresent : Present := ⟨[], 0, 0, false⟩

/-- **`present_conserves`.** A committed present preserves total balance — the frame-digest slot is not
the `balance` field, so compositing moves no money. -/
theorem present_conserves (cell presenter : CellId) (s s' : RecChainedState) (new : Int)
    (h : execFullA s (.setFieldA presenter cell presentDigestSlot new) = some s') :
    recTotal s'.kernel = recTotal s.kernel := by
  rw [setFieldA_is_stateStepGuarded _ _ _ _ _
        (by decide : Dregg2.Exec.EffectsState.reservedField presentDigestSlot = false)] at h
  exact app_commit_conserves (compositorSpec anyScene presenter anyPresent cell [] []) s s'
    presenter new (by decide : presentDigestSlot ≠ balanceField) h

/-- **`present_no_amplify`.** A committed present leaves the authority graph UNCHANGED — compositing
mints / amplifies NO capability. The compositor mediates authority over the scene without ever GRANTING
authority over state. -/
theorem present_no_amplify (cell presenter : CellId) (s s' : RecChainedState) (new : Int)
    (h : execFullA s (.setFieldA presenter cell presentDigestSlot new) = some s') :
    execGraph s'.kernel.caps = execGraph s.kernel.caps := by
  rw [setFieldA_is_stateStepGuarded _ _ _ _ _
        (by decide : Dregg2.Exec.EffectsState.reservedField presentDigestSlot = false)] at h
  exact app_commit_no_amplify (compositorSpec anyScene presenter anyPresent cell [] []) s s'
    presenter new h

/-- **`present_authorized`.** A committed present implies the presenter held authority over the
compositor cell — no unauthorized present ever commits. -/
theorem present_authorized (cell presenter : CellId) (s s' : RecChainedState) (new : Int)
    (h : execFullA s (.setFieldA presenter cell presentDigestSlot new) = some s') :
    EffectsState.stateAuthB s.kernel.caps presenter cell = true := by
  rw [setFieldA_is_stateStepGuarded _ _ _ _ _
        (by decide : Dregg2.Exec.EffectsState.reservedField presentDigestSlot = false)] at h
  exact app_commit_authorized (compositorSpec anyScene presenter anyPresent cell [] []) s s'
    presenter new h

/-- **`present_frame_advanced`.** After a committed present, the compositor frame digest reads back
exactly the presented value — the frame was actually committed (the present is recorded on-ledger). -/
theorem present_frame_advanced (cell presenter : CellId) (s s' : RecChainedState) (new : Int)
    (h : execFullA s (.setFieldA presenter cell presentDigestSlot new) = some s') :
    fieldOf presentDigestSlot (s'.kernel.cell cell) = new := by
  rw [setFieldA_is_stateStepGuarded _ _ _ _ _
        (by decide : Dregg2.Exec.EffectsState.reservedField presentDigestSlot = false)] at h
  exact app_commit_field_written (compositorSpec anyScene presenter anyPresent cell [] []) s s'
    presenter new h

/-! ## §9 — Axiom hygiene over the compositor core. -/

#assert_axioms setFieldA_is_stateStepGuarded
#assert_axioms output_integrity_eq_unfoolability_on_scene
#assert_axioms present_rejected
#assert_axioms present_overpaint_rejected
#assert_axioms present_label_spoof_rejected
#assert_axioms present_double_focus_rejected
#assert_axioms present_input_misroute_rejected
#assert_axioms present_conserves
#assert_axioms present_no_amplify
#assert_axioms present_authorized
#assert_axioms present_frame_advanced

/-! ## §10 — NON-VACUITY: a concrete two-surface scene + `#guard` teeth that BITE on the REAL executor.

THE SCENE. Two app cells composite side-by-side, plus a trusted-chrome surface:
  * cell `1` (a wallet) owns regions `{10, 11}`, projecting state-root `500`, HOLDS focus.
  * cell `2` (a browser) owns regions `{20, 21}`, projecting state-root `600`, NOT focused.
  * cell `9` (the trusted SAK chrome) owns region `{99}` at the top z-layer, NOT focused.

The compositor cell is cell `5`, carrying the baked `.admitTable` for the presentation under audit. We
exhibit, on `execFullA` (the production caveat-gated executor):
  * an HONEST present by the focused wallet (cell 1, its own region 10, genuine label, claims focus)
    COMMITS — the scene the user sees is the genuine projection (the COMMIT polarity);
  * an OVERPAINT (cell 2 the browser targeting region 10 the wallet owns) is REJECTED (T1 TOOTH);
  * a LABEL-SPOOF (cell 2 presenting its own region but DECLARING the wallet's label) is REJECTED
    (T2 TOOTH);
  * an INPUT-MISROUTE (the non-focused browser asserting focus to steal the keystroke) is REJECTED
    (T3 TOOTH);
  * a present against a DOUBLE-FOCUS scene (both wallet and browser flagged) is REJECTED (T3 TOOTH);
  * every committed present leaves total balance and the authority graph FIXED.

The adversarial scenes are GENUINELY DISTINCT (a real second cell overpainting, a real spoofed label, a
real focus theft, a real ambiguous scene), NOT trivially-malformed — exactly the don't-launder-vacuity
bar (the admit-predicate is witnessed BOTH true on the honest present AND false on each attack). -/

/-- The honest two-surface scene: wallet (cell 1, regions {10,11}, root 500, FOCUSED) +
browser (cell 2, regions {20,21}, root 600) + trusted chrome (cell 9, region {99}, top z). -/
def demoScene : Scene :=
  ⟨[ { owner := 1, regions := [10, 11], contentDigest := 1234, sourceStateRoot := 500,
       zLayer := 0, focusFlag := true }
   , { owner := 2, regions := [20, 21], contentDigest := 5678, sourceStateRoot := 600,
       zLayer := 0, focusFlag := false }
   , { owner := 9, regions := [99],     contentDigest := 9999, sourceStateRoot := 700,
       zLayer := 100, focusFlag := false } ]⟩

/-- A DOUBLE-FOCUS variant (both wallet and browser flagged) — an ambiguous-input scene (T3 violation). -/
def doubleFocusScene : Scene :=
  ⟨[ { owner := 1, regions := [10, 11], contentDigest := 1234, sourceStateRoot := 500,
       zLayer := 0, focusFlag := true }
   , { owner := 2, regions := [20, 21], contentDigest := 5678, sourceStateRoot := 600,
       zLayer := 0, focusFlag := true } ]⟩          -- ← TWO focus flags

/-- The genuine label the compositor renders for the wallet (cell 1) at its state-root 500. -/
def walletLabel : Int := labelOf 1 500          --  = 1 * 1000003 + 500 = 1000503

/-- HONEST present: wallet (cell 1) paints its OWN region 10, declares its GENUINE label, claims focus
(it IS the focus holder). -/
def honestPresent : Present := ⟨[10], 500, walletLabel, true⟩

/-- OVERPAINT present: browser (cell 2) targets region 10 — which the WALLET owns (T1 violation). -/
def overpaintPresent : Present := ⟨[10], 600, labelOf 2 600, false⟩

/-- LABEL-SPOOF present: browser (cell 2) paints its OWN region 20 but DECLARES the wallet's label
(T2 violation — the pale ghost claiming to be the wallet). -/
def labelSpoofPresent : Present := ⟨[20], 600, walletLabel, false⟩

/-- INPUT-MISROUTE present: browser (cell 2) paints its own region 20 with its own label, but ASSERTS
input focus — the browser is NOT the focus holder (T3 violation — keystroke theft). -/
def inputStealPresent : Present := ⟨[20], 600, labelOf 2 600, true⟩

-- ── The folded scene authority admits the honest present and rejects every attack (predicate level):
#guard walletLabel == 1000503
#guard sceneAdmit demoScene 1 honestPresent 0 1                 --  HONEST present admitted (T1∧T2∧T3 ✓)
#guard sceneAdmit demoScene 2 overpaintPresent 0 1 == false     --  OVERPAINT rejected (region 10 ∉ browser's — T1 TOOTH)
#guard sceneAdmit demoScene 2 labelSpoofPresent 0 1 == false    --  LABEL-SPOOF rejected (label ≠ owner — T2 TOOTH)
#guard sceneAdmit demoScene 2 inputStealPresent 0 1 == false    --  INPUT-MISROUTE rejected (browser ≠ focus — T3 TOOTH)
#guard sceneAdmit doubleFocusScene 1 honestPresent 0 1 == false --  DOUBLE-FOCUS scene rejects every present (T3 TOOTH)

-- ── Each individual invariant leg decides as claimed (the teeth are the named invariants, not luck):
#guard t1NonOverlap demoScene 1 [10]                            --  wallet owns region 10 ✓ (T1 holds for honest)
#guard t1NonOverlap demoScene 2 [10] == false                  --  browser does NOT own region 10 (T1 fails — overpaint)
#guard t2LabelBound 1 500 walletLabel                          --  wallet's genuine label binds ✓
#guard t2LabelBound 2 600 walletLabel == false                 --  browser declaring wallet's label fails ✓ (spoof)
#guard t3FocusExclusive demoScene                              --  honest scene: at-most-one focus ✓
#guard t3FocusExclusive doubleFocusScene == false              --  double-focus scene: two flags ✗
#guard countFocus demoScene == 1                               --  exactly one focus holder
#guard countFocus doubleFocusScene == 2                        --  two focus holders (ambiguous input)
#guard focusHolder demoScene == some 1                         --  the wallet (cell 1) holds focus
#guard t3InputRouted demoScene 2 true == false                 --  browser asserting focus mis-routes ✗
#guard t3InputRouted demoScene 1 true                          --  wallet (the focus holder) asserting focus ✓

-- ── The baked admit-table for the HONEST presentation holds the honest advance and excludes attacks:
#guard (compositorSpec demoScene 1 honestPresent 5 [0] [1]).admitTable.contains (0, 1)        --  honest advance present
#guard (compositorSpec demoScene 1 honestPresent 5 [0] [1]).admitTable.length == 1            --  exactly the one honest advance
-- ...and an attacking presentation bakes an EMPTY table (no present under it can commit):
#guard (compositorSpec demoScene 2 overpaintPresent 5 [0] [1]).admitTable.length == 0         --  overpaint ⇒ empty table
#guard (compositorSpec demoScene 2 labelSpoofPresent 5 [0] [1]).admitTable.length == 0        --  label-spoof ⇒ empty table
#guard (compositorSpec demoScene 2 inputStealPresent 5 [0] [1]).admitTable.length == 0        --  input-steal ⇒ empty table
#guard (compositorSpec doubleFocusScene 1 honestPresent 5 [0] [1]).admitTable.length == 0     --  double-focus ⇒ empty table

/-- The compositor cell (cell `5`) carrying the baked caveats for a given presentation, with the frame
digest committed at `frame`. The presenter HOLDS A SURFACE CAP on the compositor cell (an
`endpoint 5 [read, write]` — the firmament R0 surface-cap that authorizes it to present), so authority
is satisfied AND the SLOT-CAVEAT scene gate is the load-bearing admission leg: even an authorized-to-
present cell cannot OVERPAINT / SPOOF / STEAL-FOCUS, because the scene caveat — not the cap — decides
T1∧T2∧T3. (This is faithful to §5: a cell presents *against* the compositor cell, holding a granted
surface-cap; the scene authority is a SEPARATE gate the executor enforces on top.) -/
def compositorState (sc : Scene) (presenter : CellId) (p : Present) (frame : Int) : RecChainedState :=
  { kernel :=
      { accounts := {5}
        cell := fun c => if c = 5 then .record [("balance", .int 0), (presentDigestSlot, .int frame)]
                         else .record [("balance", .int 0)]
        -- the presenter holds a surface-cap (endpoint with write) on the compositor cell 5:
        caps := fun c => if c = presenter then [.endpoint 5 [.read, .write]] else []
        slotCaveats := fun c =>
          if c = 5 then (compositorSpec sc presenter p 5 [0] [1]).caveats else [] }
    log := [] }

/-- The committed frame digest of `compositorState … frame` reads back `frame` (the spec's `committed`
projection) — the precondition the headline/teeth need. -/
theorem compositorState_committed (sc : Scene) (presenter : CellId) (p : Present) (frame : Int) :
    (compositorSpec sc presenter p 5 [0] [1]).committed (compositorState sc presenter p frame).kernel
      = frame := by
  show fieldOf presentDigestSlot ((compositorState sc presenter p frame).kernel.cell 5) = frame
  simp [compositorState, fieldOf, presentDigestSlot, Value.scalar, Value.field]

-- ★ THE REAL EXECUTOR — THE COMMIT POLARITY: the honest present by the focused wallet COMMITS,
--   advancing the frame digest 0 → 1 (the scene the user sees is the genuine projection):
#guard ((execFullA (compositorState demoScene 1 honestPresent 0)
          (.setFieldA 1 5 presentDigestSlot 1)).isSome)                                       --  true (honest present commits)
#guard ((execFullA (compositorState demoScene 1 honestPresent 0)
          (.setFieldA 1 5 presentDigestSlot 1)).map
        (fun s => fieldOf presentDigestSlot (s.kernel.cell 5))) == some 1                      --  some 1 (frame advanced)

-- ★ THE T1 TOOTH on the real executor: the browser OVERPAINTING the wallet's region 10 is REJECTED:
#guard ((execFullA (compositorState demoScene 2 overpaintPresent 0)
          (.setFieldA 2 5 presentDigestSlot 1)).isSome) == false                              --  false (overpaint ⇒ none)
-- ★ THE T2 TOOTH: the browser SPOOFING the wallet's label is REJECTED:
#guard ((execFullA (compositorState demoScene 2 labelSpoofPresent 0)
          (.setFieldA 2 5 presentDigestSlot 1)).isSome) == false                              --  false (label-spoof ⇒ none)
-- ★ THE T3 TOOTH (input-misroute): the non-focused browser STEALING focus is REJECTED:
#guard ((execFullA (compositorState demoScene 2 inputStealPresent 0)
          (.setFieldA 2 5 presentDigestSlot 1)).isSome) == false                              --  false (input-misroute ⇒ none)
-- ★ THE T3 TOOTH (double-focus): a present against an ambiguous two-focus scene is REJECTED:
#guard ((execFullA (compositorState doubleFocusScene 1 honestPresent 0)
          (.setFieldA 1 5 presentDigestSlot 1)).isSome) == false                              --  false (double-focus ⇒ none)

-- ── Every committed present is balance-neutral (the frame slot is not `balance`) and metered on-ledger:
#guard ((execFullA (compositorState demoScene 1 honestPresent 0)
          (.setFieldA 1 5 presentDigestSlot 1)).map (fun s => recTotal s.kernel))
        == some (recTotal (compositorState demoScene 1 honestPresent 0).kernel)               --  conserved
#guard ((execFullA (compositorState demoScene 1 honestPresent 0)
          (.setFieldA 1 5 presentDigestSlot 1)).map (fun s => s.log.length)) == some 1         --  some 1 (present recorded on-ledger)

/-! ## §11 — Differential corpus (the Rust scene-admission mirror pins the SAME vector) + T4 note.

The honest presentation's admission decision vector over the `{0} × {1}` frame grid is the EXACT
vector a Rust `starbridge-compositor` differential test would pin (`src/lib.rs::scene_admit`). Drift on
either side fails: a Rust mirror change ≠ pinned literal ⇒ Rust test FAIL; a Lean `sceneAdmit` change ⇒
this `#guard` trips ⇒ forced re-pin. We pin BOTH the honest (true) and an attack (false) presentation so
the corpus is non-vacuous in BOTH polarities. -/

-- The honest presentation: the single grid cell (0 → 1) is admitted (true).
#guard AppDiffPinned (compositorSpec demoScene 1 honestPresent 5 [0] [1]) [true]
-- An overpaint presentation: the single grid cell is rejected (false) — the FALSE-polarity witness.
#guard AppDiffPinned (compositorSpec demoScene 2 overpaintPresent 5 [0] [1]) [false]

/-! ### T4 NO-INFERENCE (the read-path note — deliberately NOT in the admit-conjunction).

§5's T4 ("`present()` reads only its own region's prior contents — a cap-scoped read; double-buffered
shared surfaces kill the display covert channel, per EWS") is an INFORMATION-FLOW property of the READ
path, not a scene-ADMISSION predicate over the post-state. The toolkit's `admit` decides which writes
COMMIT; T4 governs which prior contents a present may OBSERVE. The compositor enforces T4 structurally
by giving each present a cap scoped to its OWN region's prior digest (a `senderAuthorized`/region-scoped
read), so a present cannot read a foreign surface's content — there is no admit-table cell for it to
gate. We state it here as the read-path discipline (the cap-scoping is the mechanism), and keep it OUT
of `sceneAdmit` so the admit-conjunction stays clean: T1∧T2∧T3 are the verifiable scene-AUTHORITY teeth,
exactly as the §6 brief specifies ("T1–T3 are the core"). The covert-channel elimination (double
buffering) is an implementation property of the host compositor, tracked with the F1/F2/F3 frontier.

### THE FRONTIER (honestly labeled — NOT claimed solved).

F1 (last-hop framebuffer→digest attestation), F2 (IOMMU/DMA confinement of a malicious display PD), and
F3 (verified GPU/servo compositing) are named hardware-trust assumptions (§5) — severe problems with
closure lanes, never walls. THIS module proves the T1–T3 SCENE-AUTHORITY teeth that ARE verifiable now
(the software-compositor-cell, à la EROS/Nitpicker). It does NOT bind scanned-out pixels to digests,
does NOT assume an IOMMU, and does NOT verify a GPU. The boundary is honest: the compositor mediates
AUTHORITY over the scene (verified here); the PIXELS it produces are the frontier. -/

end Dregg2.Apps.Compositor
