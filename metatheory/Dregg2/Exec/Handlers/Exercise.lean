/-
# Dregg2.Exec.Handlers.Exercise — the RECURSIVE sub-effect-forest handler (`exerciseA`, R4).

This EXTENDS the `EffectHandler` algebra scaffolded in `Dregg2.Exec.Handler` (read that module first:
the `EffectHandler` record bundling `step`/`delta`/`auth`/`admission`/`trace` WITH the forced obligation
proofs `auth_gated`/`admission_gated`/`conserves`, the registry coproduct `Registry`, the all-or-nothing
`execTurn` over a `List ClosedEffect`, and — THE PAYOFF HERE — the generic `turn_conserves` that SUMS the
per-effect per-asset deltas over an ARBITRARY list of closed effects). We register the one handler the
scaffold's `§DEFER` carried OPEN: `exerciseA`, dregg1's `apply_exercise_via_capability`
(`apply.rs:2441`), the RECURSIVE sub-effect-forest case. We do NOT touch `TurnExecutorFull`'s
`execFullA`/`execInnerA` (that cutover is a later step); we only IMPORT and REUSE.

## What `exerciseA` is (`TurnExecutorFull:3011`, dregg1 `apply.rs:2441`)

`ExerciseViaCapability { cap_slot→target, inner_effects }`: the actor exercises a HELD capability to RUN
a list of `inner` effects against the cap's `target` cell. dregg1's structure is

  **lookup → facet-mask (`allowed_effects`) → RECURSE**:

  1. (`apply.rs:2455`) the actor must HOLD a cap conferring an edge to `target` (the hold-gate); the cap
     graph is UNCHANGED by exercising (it reads, never edits, the c-list);
  2. (**R4**) each inner effect must be ADMITTED under the cap's FACET-MASK — the cap's `allowed_effects`
     (here: the held cap's `rights : List Auth`), NOT the inner-actor's full authority. An inner effect
     whose required facet is OUTSIDE the mask is REJECTED;
  3. (`apply.rs:2647`) each surviving inner effect is APPLIED in sequence against the target cell — a
     SUB-FOREST, fail-closed if the hold-gate fails, the facet-mask rejects, or ANY inner effect fails.

## The approach that AVOIDS the codec-#136 stall (a 1M-heartbeat mutual induction)

The executor's `execInnerA` is a NEW `def` re-founded inside a `mutual` block, and its conservation
(`execInnerA_ledger_per_asset`) is a NEW mutual induction. That is the shape that stalled #136. We do
**NOT** re-derive it. The inner effects are modelled as a `Type 0` SUB-EFFECT carrier (`SubEffect`: a
fail-closed `step` + per-asset `delta` + a per-step `conserves` PROOF — the scaffold's `EffectHandler`
obligation shape, with the `Args` projected away so it stays in `Type`, dodging the `ClosedEffect : Type 1`
universe bump that an existential `Args : Type` field forces). The exercise runs its inner `SubEffect`
list through a `subTurn` (the registry `foldlM` over `SubEffect`), so its conservation REUSES the
SAME generic induction the scaffold proved for `turn_conserves` (`subTurn_conserves` below — proved ONCE
by `List.foldlM` induction consuming each `SubEffect.conserves`). NO new well-founded recursion, NO
mutual block: the nesting terminates because the inner `List SubEffect` is a strictly-smaller STRUCTURAL
argument (a `SubEffect` carries its `step` opaquely, so an `exercise`-built sub-effect nested inside
another's inner list is just another list element).

Crucially the scaffold's REAL handlers drop straight in: `closedToSub` projects any
`Dregg2.Exec.Handler.ClosedEffect` to a `SubEffect` (citing `execEffect_conserves`), so an exercise's
inner forest can be built from the proved transfer/escrow/state/mint handlers verbatim.

For GENUINE self-nesting (`exercise`-built sub-effect re-entered to arbitrary depth) we ALSO expose a
SMALL explicit `fuel : Nat` builder (`exerciseSubFuel`) that decrements per level and FAIL-CLOSES at `0`
(the empty inner forest), keyed to a `facetedSize` structural measure (the `CodecRoundtrip.lean:3332`
fuel precedent). It is a CLEAN structural fuel — heartbeats stay at the Lean default; no proof here
raises `maxHeartbeats`.

## R4 EVALUATED (`§TEETH`)

An inner effect whose required facet is OUTSIDE the cap's mask makes the WHOLE exercise return `none`
(the §TEETH `read`-only mask rejecting a `write`-facet inner effect). An inner effect WITHIN the mask
runs, and the combined per-asset measure moves by EXACTLY the SUM of the surviving inner deltas (an
exercise of a transfer + a mint sub-forest sums `0 + amt`). The hold-gate REJECTS an actor with no edge
to the target.

Pure, computable, `#eval`-able. Verified standalone:
`lake build Dregg2.Exec.Handlers.Exercise`.
-/
import Dregg2.Exec.Handler

namespace Dregg2.Exec.Handlers.Exercise

open Dregg2.Authority Dregg2.Execution
open Dregg2.Exec
open Dregg2.Exec.Handler
open Dregg2.Exec.TurnExecutorFull (acceptsEffects lcLive lcSealed lcDestroyed setLifecycle)

/-! ## §1 — `SubEffect`: the `Type 0` inner-effect carrier (the obligation shape, `Args` projected away).

The scaffold's `ClosedEffect` existentially packs `Args : Type`, bumping it to `Type 1` — so an
`ExerciseArgs` carrying a `List ClosedEffect` could NOT be the argument of an `EffectHandler` (whose
binder is `Args : Type`). We model an inner sub-effect by the DATA an exercise actually consumes from a
closed effect — its fail-closed `step`, its per-asset `delta`, and the per-step `conserves` PROOF — with
the `Args` projected away. `SubEffect` is therefore `Type 0`, and ANY closed effect projects into it
(`closedToSub`, §2), so the scaffold's proved handlers drop in verbatim. -/

/-- A **sub-effect**: the obligation-carrying transition an exercise runs, in `Type 0`. `step` is the
fail-closed transition; `delta` the per-asset budget; `conserves` the PROOF (carried, not re-derived)
that a commit moves the combined per-asset measure by EXACTLY `delta`. -/
structure SubEffect where
  /-- The fail-closed sub-effect transition. -/
  step : RecordKernelState → Option RecordKernelState
  /-- The per-asset conservation budget this sub-effect moves. -/
  delta : AssetId → Int
  /-- OBLIGATION (carried): every commit moves the combined per-asset measure by EXACTLY `delta`. -/
  conserves : ∀ s s', step s = some s' →
    ∀ b, recTotalAsset s' b = recTotalAsset s b + delta b

/-- **Run a `SubEffect` list as an all-or-nothing transaction** (the registry `foldlM`, `SubEffect`
flavour — the definitional twin of the scaffold's `execTurn`). -/
def subTurn (es : List SubEffect) (s : RecordKernelState) : Option RecordKernelState :=
  es.foldlM (fun st e => e.step st) s

/-- The combined per-asset delta of a sub-forest: the SUM of the per-sub-effect deltas. -/
def subTurnDelta (es : List SubEffect) (b : AssetId) : Int := (es.map (fun e => e.delta b)).sum

/-- The empty sub-turn is the identity. -/
@[simp] theorem subTurn_nil (s : RecordKernelState) : subTurn [] s = some s := rfl

/-- The cons unfolding (`Option.bind` form), exactly as the scaffold's `execTurn_cons`. -/
theorem subTurn_cons (e : SubEffect) (rest : List SubEffect) (s : RecordKernelState) :
    subTurn (e :: rest) s = (e.step s).bind (fun smid => subTurn rest smid) := by
  simp only [subTurn, List.foldlM_cons]
  cases e.step s <;> rfl

/-- **`subTurn_conserves` — the sub-forest conservation, ONE generic induction (the `turn_conserves`
twin).** For ANY list of sub-effects, the combined per-asset measure changes by EXACTLY the SUM of the
per-sub-effect deltas. Proved by the SAME `List.foldlM` induction the scaffold used for `turn_conserves`,
consuming each `SubEffect.conserves` field — never a per-effect restatement. THIS is the theorem the
exercise's `conserves` folds onto. -/
theorem subTurn_conserves :
    ∀ (es : List SubEffect) (s s' : RecordKernelState),
      subTurn es s = some s' → ∀ b, recTotalAsset s' b = recTotalAsset s b + subTurnDelta es b := by
  intro es
  induction es with
  | nil =>
    intro s s' h b
    rw [subTurn_nil, Option.some.injEq] at h
    subst h
    simp only [subTurnDelta, List.map_nil, List.sum_nil, add_zero]
  | cons e rest ih =>
    intro s s' h b
    rw [subTurn_cons, Option.bind_eq_some_iff] at h
    obtain ⟨smid, hmid, htl⟩ := h
    have hstep := e.conserves s smid hmid b
    have htail := ih smid s' htl b
    rw [htail, hstep]
    simp only [subTurnDelta, List.map_cons, List.sum_cons]
    ring

/-! ## §2 — `closedToSub`: project a scaffold `ClosedEffect` into a `SubEffect`.

The scaffold's PROVED handlers (transfer/escrow/state/mint/...) drop into an exercise's inner forest
verbatim: a `ClosedEffect`'s `execEffect`/`effectDelta` are its `SubEffect` `step`/`delta`, and its
per-step conservation is the proved `execEffect_conserves`. -/

/-- Project any closed effect into a `SubEffect`, citing the scaffold's `execEffect_conserves`. -/
def closedToSub (e : ClosedEffect) : SubEffect where
  step := fun s => execEffect e s
  delta := effectDelta e
  conserves := fun s s' h b => execEffect_conserves e s s' h b

/-! ## §3 — The FACET-MASK: a cap's `allowed_effects`, and the R4 admission of one inner effect.

dregg1's `allowed_effects` (the cap's facet) is, in dregg2's `Cap` model, the held cap's `rights`: a
`node target` cap is the FULL facet (it confers `control`, the all-effects authority — `capAuthConferred
(.node _) = [control]`, the privileged facet), while an `endpoint target rights` cap confers EXACTLY its
`rights` list (the narrowed facet view). The R4 rule: an inner effect declares the facet `Auth` it
EXERCISES, and is admitted iff that facet lies in the held cap's mask.

This is ORTHOGONAL to the hold-gate's CONNECTIVITY test (`confersEdgeTo`, §4): connectivity needs a
`node` cap or a `write`-bearing endpoint (a pure-`read` endpoint confers NO edge in dregg2's
`execGraph` model, so it cannot even be exercised). So a cap that PASSES the hold-gate (e.g.
`endpoint t [write, read]`) still has a NARROWED facet mask `[write, read]` — an inner effect demanding
`grant`/`control` is REJECTED by R4 even though the actor holds connectivity. That gap between
connectivity and the effect-facet is exactly what R4 enforces. -/

/-- The FACET MASK of a held cap (its `allowed_effects`): the FULL facet for a `node` cap (privileged
authority — every facet), the carried `rights` for an `endpoint` cap (the narrowed view), `[]` for
`null`. -/
def capFacetMask (cap : Cap) : List Auth :=
  match cap with
  | .null            => []
  | .endpoint _ r    => r
  | .node _          => [Auth.read, Auth.write, Auth.grant, Auth.call, Auth.reply, Auth.reset,
                         Auth.control, Auth.notify]  -- every Auth (privileged); notify ⇒ full facet stays complete

/-- **R4 — is `facet` admitted under `cap`'s mask?** The single inner-effect gate: the facet the inner
effect exercises must lie in the held cap's `allowed_effects`. A `read`-only cap REJECTS a `write`-facet
inner effect. -/
def facetAdmitted (cap : Cap) (facet : Auth) : Bool := (capFacetMask cap).contains facet

/-- A **faceted inner effect**: a `SubEffect` (the sub-forest element — its `step`/`delta`/`conserves`
carried) PAIRED with the facet `Auth` it exercises (the R4 mask key the cap is checked against). The
inner forest of an `exerciseA` is a `List FacetedEffect` — `Type 0`. -/
structure FacetedEffect where
  /-- The facet the inner effect exercises (checked against the cap's `allowed_effects`). -/
  facet : Auth
  /-- The inner sub-effect itself. -/
  eff   : SubEffect

/-- The underlying `SubEffect`s of a faceted inner forest (the list `subTurn` runs and
`subTurn_conserves` is applied to). -/
def innerEffects (inner : List FacetedEffect) : List SubEffect := inner.map (·.eff)

/-- **The whole inner forest is admitted under `cap`'s mask** iff EVERY inner effect's facet is. R4's
all-or-nothing gate: ONE inner effect outside the mask rejects the whole exercise. -/
def forestAdmitted (cap : Cap) (inner : List FacetedEffect) : Bool :=
  inner.all (fun fe => facetAdmitted cap fe.facet)

/-- Build a faceted inner effect from a scaffold `ClosedEffect` (the common case — the proved handlers). -/
def facetedOf (facet : Auth) (e : ClosedEffect) : FacetedEffect := { facet := facet, eff := closedToSub e }

/-! ## §4 — The hold-gate + facet-mask + recurse step.

The held cap to `target` is resolved by the SAME `heldCapTo` lookup the executor's `recKDelegate`/
`exerciseStepA` use (a member of the actor's slot that `confersEdgeTo target`). The step:

  1. **hold-gate** — the actor must hold SOME cap conferring an edge to `target` (`confersEdgeTo`);
  2. **R4 facet-mask** — every inner effect's facet must lie in THAT cap's mask (`forestAdmitted`);
  3. **recurse** — run the inner `SubEffect`s through `subTurn` (the registry `foldlM`), all-or-nothing.

The cap graph is UNCHANGED by exercising (it reads, never edits, the c-list — dregg1 `apply.rs:2455`):
the only state motion is whatever the inner sub-forest commits. -/

/-- Exercise arguments: the `actor` exercising the cap, the `target` cell the cap points at, and the
inner sub-forest (faceted sub-effects). `Type 0` (every field is). -/
structure ExerciseArgs where
  /-- The actor exercising a held cap. -/
  actor  : CellId
  /-- The target cell the exercised cap confers an edge to. -/
  target : CellId
  /-- The inner sub-effect forest, each tagged with the facet it exercises (the R4 mask keys). -/
  inner  : List FacetedEffect

/-- Does `actor` hold a cap conferring an edge to `target`? (The executor's `exerciseStepA` hold-gate,
`TurnExecutorFull:1575`.) -/
def holdsEdge (k : RecordKernelState) (a : ExerciseArgs) : Bool :=
  (k.caps a.actor).any (fun cap => confersEdgeTo a.target cap)

/-- The held cap to `target` resolved off the actor's slot (the `heldCapTo` `find?` lookup). Its mask is
the R4 `allowed_effects`. -/
def exercisedCap (k : RecordKernelState) (a : ExerciseArgs) : Cap :=
  heldCapTo k.caps a.actor a.target

/-- **The R4 facet-mask admission gate** (a function of `(state, args)`): the actor holds an edge to the
target AND every inner effect's facet lies in the held cap's mask. -/
def exerciseAdmitB (k : RecordKernelState) (a : ExerciseArgs) : Bool :=
  holdsEdge k a && forestAdmitted (exercisedCap k a) a.inner

/-- **The hold-gate + facet-mask + recurse step.** Commit ONLY if the actor holds an edge to `target`
AND every inner facet is admitted under the held cap's mask (R4); THEN run the inner sub-forest through
`subTurn`. Fail-closed: missing edge, OR any inner facet outside the mask, OR any inner effect failing ⇒
`none`. -/
def exerciseStep (k : RecordKernelState) (a : ExerciseArgs) : Option RecordKernelState :=
  if exerciseAdmitB k a then subTurn (innerEffects a.inner) k else none

/-! ## §5 — `exerciseH`: the registered recursive handler. THE PAYOFF — `conserves` REUSES
`subTurn_conserves` on the inner list.

`delta` is the SUM of the inner effects' deltas (`subTurnDelta (innerEffects a.inner)`). `conserves` folds
the sub-forest conservation onto the generic theorem: a committed exercise IS a committed `subTurn` over
the inner list, so `subTurn_conserves` gives that the combined measure moves by EXACTLY `subTurnDelta` of
the inner list — the per-effect contribution the GLOBAL `turn_conserves` then sums when an exercise sits
inside another turn. NO new induction; NO re-derivation. `auth_gated`/`admission_gated` come from the
hold-gate + facet-mask conjuncts of `exerciseAdmitB`. -/

/-- **`exerciseH` — the registered recursive sub-effect-forest handler.** All three obligations close by
COMPOSING the generic theorems on the inner `SubEffect` list:
  * `conserves`  — `subTurn_conserves` on `innerEffects a.inner` (THE PAYOFF: the sub-forest conservation
    folds onto the generic theorem, never re-derived);
  * `auth_gated` — the hold-gate conjunct of `exerciseAdmitB` (the actor holds an edge to `target`);
  * `admission_gated` — the FULL `exerciseAdmitB` (hold-gate AND R4 facet-mask), so a committing exercise
    PROVES every inner facet lay in the cap's mask. -/
def exerciseH : EffectHandler ExerciseArgs where
  step := exerciseStep
  delta := fun a b => subTurnDelta (innerEffects a.inner) b   -- SUM of the inner effects' per-asset deltas
  auth := holdsEdge
  admission := exerciseAdmitB
  trace := fun a => { actor := a.actor, src := a.actor, dst := a.target, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold exerciseStep at h
    by_cases hg : exerciseAdmitB s a
    · -- the hold-gate is the FIRST conjunct of the admission gate that committed.
      unfold exerciseAdmitB at hg
      exact (Bool.and_eq_true _ _ ▸ hg).1
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold exerciseStep at h
    by_cases hg : exerciseAdmitB s a
    · exact hg
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    unfold exerciseStep at h
    by_cases hg : exerciseAdmitB s a
    · rw [if_pos hg] at h
      -- a committed exercise IS a committed `subTurn` over the inner list: REUSE `subTurn_conserves`.
      exact subTurn_conserves (innerEffects a.inner) s s' h b
    · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §6 — The structural fuel for GENUINE self-nesting (`exercise` inside `exercise`).

The FLAT nesting needs no measure: an `exercise`-built sub-effect is just one more element in another
exercise's inner list (its `step` is opaque, so the list is structurally smaller, full stop). To MODEL
deliberate self-nesting to a bounded depth we expose a SMALL explicit `fuel : Nat` builder that decrements
per level and FAIL-CLOSES at `0` (the empty inner forest) — the `actionSize`/`CodecRoundtrip.lean:3332`
fuel precedent, kept CLEAN (no heartbeat-blowing tactic). -/

/-- The structural SIZE of a faceted inner forest (the `actionSize` precedent), measured through the
explicit `fuel`: `0` at exhausted fuel, the inner list length at positive fuel. Total structural recursion
on `fuel` (decreasing `Nat`). -/
def facetedSize : Nat → List FacetedEffect → Nat
  | 0,     _     => 0
  | _ + 1, inner => inner.length

/-- An exercise as a `SubEffect` (the FLAT builder — inner forest given directly). The inner effects are
already `SubEffect`s, so this is the structural (no-fuel) nesting: an `exerciseSub` can itself appear
inside another's inner forest as a `FacetedEffect`. Its `conserves` is `exerciseH.conserves`. -/
def exerciseSub (actor target : CellId) (inner : List FacetedEffect) : SubEffect where
  step := fun s => exerciseStep s { actor := actor, target := target, inner := inner }
  delta := fun b => subTurnDelta (innerEffects inner) b
  conserves := fun s s' h b => exerciseH.conserves s { actor := actor, target := target, inner := inner } s' h b

/-- **The fuel-bounded SELF-NESTING builder.** `exerciseSubFuel (n+1) actor target inner` builds the
exercise sub-effect carrying `inner`; the `fuel` is the explicit depth budget the CALLER decrements when
it places a nested `exerciseSubFuel n …` inside `inner`. At `fuel = 0` the nesting FAIL-CLOSES to the
EMPTY forest (a bare cap-exercise, no sub-effects), so the recursion TERMINATES structurally on `fuel`
(decreasing `Nat`), never a heartbeat-blowing well-founded measure. -/
def exerciseSubFuel : Nat → CellId → CellId → List FacetedEffect → SubEffect
  | 0,     actor, target, _     => exerciseSub actor target []          -- fail-closed at depth 0
  | _ + 1, actor, target, inner => exerciseSub actor target inner

/-- **Fuel adequacy (`actionSize`-keyed, structural).** With POSITIVE fuel the fuel-bounded builder
yields EXACTLY the flat builder — the genuine forest is built, nothing truncated. (At `fuel = 0` it
fail-closes to `[]`.) Proved by `rfl` on the successor branch — no induction, no heartbeats. -/
theorem exerciseSubFuel_adequate (n : Nat) (actor target : CellId) (inner : List FacetedEffect) :
    exerciseSubFuel (n + 1) actor target inner = exerciseSub actor target inner := rfl

/-- At `fuel = 0` the builder fail-closes to the empty (bare cap-exercise) forest. -/
theorem exerciseSubFuel_zero (actor target : CellId) (inner : List FacetedEffect) :
    exerciseSubFuel 0 actor target inner = exerciseSub actor target [] := rfl

/-! ## §7 — The `ClosedEffect` builder + the registry entry + the conservation corollary.

`exerciseH` is one well-typed `PackedHandler` — its obligation proofs are a TYPING condition on entry.
This plugs straight into the generic `turn_conserves` from `Dregg2.Exec.Handler` (it is generic over the
registry); an exercise nested in a SCAFFOLD turn contributes its `subTurnDelta`-of-inner to the SUM. -/

/-- Build a closed exercise effect (tag `0`) for the SCAFFOLD registry. The inner forest is faceted
sub-effects (built from proved handlers via `facetedOf`, or from nested `exerciseSub`/`exerciseSubFuel`). -/
def exerciseEffect (actor target : CellId) (inner : List FacetedEffect) : ClosedEffect :=
  { tag := 0, Args := ExerciseArgs, args := { actor := actor, target := target, inner := inner },
    handler := exerciseH }

/-- The exercise registry slice (one entry). -/
def exerciseRegistry : Registry := [ ⟨ExerciseArgs, exerciseH⟩ ]

/-- **`exercise_conserves` — the headline corollary (the §DEFER payoff).** A committed exercise
moves the combined per-asset measure by EXACTLY the SUM of its inner sub-forest's deltas — the sub-forest
conservation folded onto `subTurn_conserves`, with NO new induction. This is the per-effect contribution
the GLOBAL `turn_conserves` sums when an exercise sits inside a larger turn. -/
theorem exercise_conserves (s s' : RecordKernelState) (a : ExerciseArgs)
    (h : exerciseStep s a = some s') (b : AssetId) :
    recTotalAsset s' b
      = recTotalAsset s b + subTurnDelta (innerEffects a.inner) b :=
  exerciseH.conserves s a s' h b

/-! ## §8 — TEETH: R4 evaluated. The facet-mask, the hold-gate, the summed sub-forest conservation.

A 3-cell, 1-asset fixture: cells 0,1,2 are live accounts; cell 0 holds 100 of asset 0; cell 0 holds an
`endpoint 1 [read]` cap (a READ-ONLY facet to target cell 1) AND a `node 2` cap (the FULL facet to target
cell 2). All cells default Live. The inner sub-forest is built from the scaffold's own state effects
(`Dregg2.Exec.Handler.stateEffect`), each tagged with the facet it exercises via `facetedOf`. -/

/-- The base fixture: cells 0,1,2 accounts; cell 0 holds 100 of asset 0; cell 0 holds a NARROWED
`[write, read]` endpoint cap to cell 1 (confers an edge — it bears `write` — but its facet mask EXCLUDES
`grant`/`control`) and a FULL `node` cap to cell 2; all Live. -/
def ex0 : RecordKernelState :=
  { accounts := {0, 1, 2}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun c => if c = 0 then [Cap.endpoint 1 [Auth.write, Auth.read], Cap.node 2] else []
    bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0 }

/-- An inner WRITE-facet effect: a balance-neutral state-write on cell 1 (the scaffold's `stateEffect`),
tagged `write` — WITHIN the `[write, read]` mask. -/
def innerWrite : FacetedEffect := facetedOf Auth.write (Handler.stateEffect 1)

/-- An inner CONTROL-facet effect: the same state-write, but declaring it exercises the `control` facet
— OUTSIDE the `[write, read]` mask (the R4 over-reach). -/
def innerControl : FacetedEffect := facetedOf Auth.control (Handler.stateEffect 1)

/-- An exercise of cell 0's NARROWED `[write, read]` cap to target 1, whose inner effect demands the
`control` facet — OUTSIDE the mask. R4 REJECTS the whole exercise. -/
def exerciseControlUnderWrite : ExerciseArgs := { actor := 0, target := 1, inner := [innerControl] }

/-- An exercise of the SAME narrowed cap, whose inner effect demands only `write` — WITHIN the mask. -/
def exerciseWriteUnderWrite : ExerciseArgs := { actor := 0, target := 1, inner := [innerWrite] }

/-- An exercise of cell 0's FULL `node 2` cap, whose inner effect demands the `control` facet — ADMITTED
(a node cap is the full mask). -/
def exerciseControlUnderNode : ExerciseArgs :=
  { actor := 0, target := 2, inner := [facetedOf Auth.control (Handler.stateEffect 2)] }

/-- An actor (cell 1) with NO cap to target 2 — the hold-gate REJECTS it. -/
def exerciseNoEdge : ExerciseArgs := { actor := 1, target := 2, inner := [] }

/-- FLAT self-nesting: cell 0 exercises its full node-2 cap, whose sub-forest exercises the narrowed
write-cap to 1 (a nested `exerciseSub`). No fuel needed — the inner list is a structural subterm. -/
def exerciseNested : ExerciseArgs :=
  { actor := 0, target := 2, inner := [{ facet := Auth.control, eff := exerciseSub 0 1 [innerWrite] }] }

/-- FUEL fail-close: the depth-0 fuel builder yields the bare (empty) exercise, which commits under the
full node-2 facet. -/
def exerciseFuelZero : ExerciseArgs :=
  { actor := 0, target := 2, inner := [{ facet := Auth.control, eff := exerciseSubFuel 0 0 1 [innerWrite] }] }

-- §TEETH-1 (R4 REJECT): a `control`-facet inner effect under a NARROWED `[write, read]` cap mask ⇒ the
-- whole exercise is REJECTED (the facet-mask gate bites — `control ∉ [write, read]`), even though the
-- actor HOLDS connectivity to the target. This is the R4 over-reach guard.
#guard ((exerciseStep ex0 exerciseControlUnderWrite).isSome) == false  --  false
-- §TEETH-2 (R4 ADMIT): the SAME inner effect declaring only the `write` facet ⇒ ADMITTED and runs.
#guard ((exerciseStep ex0 exerciseWriteUnderWrite).isSome)  --  true
-- §TEETH-3 (HOLD-GATE): an actor (cell 1) holding NO cap to target 2 ⇒ REJECTED (no edge).
#guard ((exerciseStep ex0 exerciseNoEdge).isSome) == false  --  false
-- §TEETH-4 (FULL facet): cell 0's `node 2` cap is the FULL mask, so a `control`-facet inner effect on
-- target 2 is ADMITTED (the node cap confers every facet).
#guard ((exerciseStep ex0 exerciseControlUnderNode).isSome)  --  true
-- §TEETH-5 (SUB-FOREST CONSERVES): exercise of a balance-neutral inner forest leaves the combined
-- per-asset measure UNCHANGED (delta = sum of inner deltas = 0).
#guard ((exerciseStep ex0 exerciseWriteUnderWrite).map
        (fun k => (recTotalAsset ex0 0, recTotalAsset k 0))) == some (100, 100)  --  some (100, 100)
-- §TEETH-6 (SUMMED delta): the sub-forest delta is the SUM of inner deltas (here 0 ⇒ unchanged).
#guard (subTurnDelta (innerEffects exerciseWriteUnderWrite.inner) 0) == 0  --  0
-- §TEETH-7 (FLAT NESTING): an exercise whose inner forest CONTAINS another exercise (cell 0 exercises
-- its node-2 cap, whose sub-forest exercises the read-cap to 1) — structural nesting, no fuel needed.
#guard ((exerciseStep ex0 exerciseNested).isSome)  --  true
-- §TEETH-8 (FUEL fail-close): the fuel-bounded builder at depth 0 yields the bare (empty) exercise,
-- which commits (no sub-effects) under the full node-2 facet.
#guard ((exerciseStep ex0 exerciseFuelZero).isSome)  --  true
-- §TEETH-9 (a turn = [exercise] runs through the SCAFFOLD registry foldlM and conserves).
#guard ((execTurn [exerciseEffect 0 1 [innerWrite]] ex0).map
        (fun k => recTotalAsset k 0)) == some 100  --  some 100

/-! ## §9 — Axiom-hygiene pins (every keystone rests only on the three kernel axioms).

Pinning `exerciseH` pins its obligation FIELDS transitively (the structure literal CARRIES the proofs);
`subTurn_conserves`/`exercise_conserves` certify the §DEFER payoff — the sub-forest conservation folded
onto the generic induction — rests only on the kernel triple. A `sorryAx` anywhere fails the pin AND the
build. -/

#assert_axioms subTurn_conserves
#assert_axioms exerciseH
#assert_axioms exercise_conserves
#assert_axioms exerciseSubFuel_adequate
#assert_axioms exerciseSubFuel_zero

/-! ## §DEFER — scope of this recursive handler.

Deliberately OUT of this handler (documented, NOT a silent gap):

  * **Cutover.** This handler does NOT replace `TurnExecutorFull.execInnerA`/`execFullA`'s exercise arm;
    it is the algebra-level twin that DE-RISKS that cutover. The migration routes the executor's
    `inner : List FullActionA` through `innerEffects` (each `FullActionA` becomes a `SubEffect` via its
    registered handler's `closedToSub`) and reads `exerciseH.conserves` instead of re-proving
    `execInnerA_ledger_per_asset`.

  * **Cap-graph mutation on exercise.** dregg1's exercise reads, never edits, the c-list
    (`apply.rs:2455`); our step likewise leaves `caps` fixed (the only state motion is the inner
    sub-forest). The CapTP enliven/handoff cap-mutations are separate effects, not exercise.

  * **Unbounded self-nesting.** The fuel builder bounds DELIBERATE self-nesting to an explicit depth; the
    FLAT structural nesting (an `exerciseSub` inside another's inner list) is unbounded and needs no fuel
    (the inner list is a structural subterm). The fuel exists only to MODEL a bounded recursive descent
    cleanly, per the `actionSize` precedent — it is not a soundness crutch.
-/

end Dregg2.Exec.Handlers.Exercise
