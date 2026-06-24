/-
# Dregg2.Exec.HandlerOpenFronts — explicit handler-executor open-front registry (Wave 7+).

POLICY: **no lurking holes**. Every unfinished `handler_refines_execFullA_*` / queue-defer front is
named here with an explicit open-hole theorem (or a tracked `HoleStatus`). Silent strengthening gaps
are forbidden — use these portals instead.

Run `#eval countOpenFronts` after each wave to watch the frontier shrink.
-/
import Dregg2.Exec.HandlerExecutor
import Dregg2.Circuit.Inst.ExerciseInnerTurn

namespace Dregg2.Exec.HandlerOpenFronts

open Dregg2.Exec.HandlerExecutor
open Dregg2.Circuit.Inst.ExerciseInnerTurn
open Dregg2.Exec.TurnExecutorFull

/-! ## §0 — front metadata. -/

inductive HoleWave
  | w7_flag_alignment
  | w7_exercise_r4
  | w7_spawn_metadata
  | w7_exercise_inner_fold
  deriving Repr, DecidableEq

structure OpenFront where
  id       : String
  wave     : HoleWave
  action?  : Option String
  note     : String
  deriving Repr

/-! ## §1 — inventory (every named handler gap; shrink this list). -/

-- CLOSED (this wave): `handler_makeSovereign` (handler ALIGNED to the `makeSovereignKernel`
-- commitment-rebind), `handler_receiptArchive` (ALIGNED to the `"lifecycle"` field write), and the
-- queue-allocate `actor ≠ cell` front (handler now stores owner = `actor`, so kernel agreement is
-- UNCONDITIONAL). Their `hole_*` theorems in `HandlerExecutor` are now genuine proofs,
-- and the `portal_*` re-exports below delegate to them. Removed from the open inventory.
-- CLOSED (this wave): `exercise_inner_turn_witness` — the inner `List FullActionA` emitted fold from
-- the hold post-state now refines `turnSpec` via `ExerciseInnerTurn.exercise_inner_emitted_refines_turnSpec`
-- (the `portal_exercise_inner_turn` re-export below delegates to it). Removed from the
-- open inventory.
-- CLOSED (F2b): the queue-ENQUEUE `actor ≠ cell` front died with the queue verb family — there is
-- no queue verb left to align (the factory story, `Apps/QueueFactory.lean`). Only the spawn
-- front remains.
-- CLOSED (P2 canonical-semantics): `exercise_r4_facet_mask` — `execFullA`'s `exerciseA` now ENFORCES
-- the R4 facet mask (`innerFacetsAdmittedA`) and the handler bridge tags each inner with its REAL
-- `requiredFacetA fa` (not blanket `Auth.control`), so the two facet gates are the SAME check. The
-- facet front is discharged (`ExerciseInnerTurn.exercise_r4_facet_mask`); only the
-- ORTHOGONAL inner-turn fold remains, carried as an explicit `hinner` hypothesis there.
-- CLOSED (census-D4): `spawn_factory_metadata` — the spawn cap-handoff + factory install are now
-- VERIFIED by the handler-executor lane. The born-empty `handler_refines_execFullA_{spawn,
-- createCellFromFactory}` refine against the shared `createCellA` core (dropping target/vk); the NEW
-- `handler_refines_execFullA_spawn_metadata` / `…_createCellFromFactory_metadata` refine against the
-- CHAINED steps `spawnChainA` / `createCellFromFactoryChainA` — which ARE `execFullA`'s ACTUAL `.spawnA` /
-- `.createCellFromFactoryA` arms (by `rfl`) — and deliver the FULL metadata OFF the commit via the typed
-- `HandlerFloors.{spawnMetadataFloor,factoryMetadataFloor}` (`PostFloorObligation`s, the §4c
-- clean-discharge case): the spawn child holds the actor's held cap to the parent target (least-amplifying)
-- + records parent + snapshots the c-list + is stamped fresh; the factory cell carries EXACTLY the
-- registered factory's `slotCaveats` (program) + the `factoryVkField`/`initialFields` install. The floors
-- BITE (`spawnMetadataFloor_overgrant_rejected` / `factoryMetadataFloor_unknown_factory_rejected`).
-- Removed from the open inventory. (The handler DISPATCH `toClosedEffect` still maps these onto the
-- born-empty `createCellH` for the conservation algebra; the metadata is verified directly against the
-- faithful chained arm — the same pattern as `…_spawn_fresh`/`…_refreshDelegation`, the refinement that
-- consumes the chained step, not the lossy dispatch.)
def openFronts : List OpenFront := [
  -- Wave 7: the exercise INNER-TURN fold boundary — CLOSED on the closable fragment; the residual is the
  -- PRECISE complement (the three FROZEN-FACE inner steps). The boundary kernel-equality between the
  -- handler's `subTurn (innerEffects …)` over `RecordKernelState` and the live `execInnerA` over
  -- `RecChainedState` (`execFullA`'s `.exerciseA` arm) is now PROVEN — `HandlerExecutor.
  -- exercise_inner_fold_kernel_agrees` (per-effect inter-executor agreement inducted over the forest;
  -- `portal_handler_exercise_safe` SHEDS the `hpost` boundary the previous portal carried). What remains
  -- OPEN is exactly the un-safe complement (`noFrozenFace fa = false`): an inner forest carrying a
  -- `refreshDelegationA` (handler omits the `delegationEpochAt` re-stamp the live `refreshDelegationChainA`
  -- applies — eval: handler 0 vs live 5), a `createCellFromFactoryA` (handler dispatch `= createCellH`,
  -- born EMPTY; live installs the factory's `slotCaveats`/`factoryVk`/`initialFields`), or a `spawnA`
  -- (handler `= createCellH`; live copies the held cap + records parent + snapshots c-list + stamps epoch).
  -- These are GENUINE semantic divergences — the handler inner step does strictly LESS than the live arm —
  -- the SAME gap the top-level `handler_refines_execFullA_{refreshDelegation,…_metadata}` route through the
  -- CHAINED arm to close. The clean fix (handler-algebra lane): route the exercise inner fold through those
  -- chained stamping/installing/handoff steps; then `noFrozenFace` is total and the front fully closes.
  ⟨"exercise_inner_fold_frozenface", .w7_exercise_inner_fold, some "exerciseA",
    "exercise_inner_fold boundary PROVEN on the noFrozenFace-safe fragment (exercise_inner_fold_kernel_agrees + portal_handler_exercise_safe shed hpost). Residual = the 3 frozen-face inner steps where the handler does strictly less than the live arm: refreshDelegationA (epoch re-stamp), createCellFromFactoryA (factory install), spawnA (cap handoff). Fix: route the exercise inner fold through the chained arms (handler-algebra lane)."⟩
]

def countOpenFronts : Nat := openFronts.length

/-! ## §2 — explicit open-hole portals (re-exported from keystones; FAIL `#assert_axioms` until proved). -/

section HolePortals

variable {s s' : RecChainedState}

/-- CLOSED: `makeSovereignA` handler ⊑ `execFullA` (commitment-rebind ALIGNED; proved). -/
theorem portal_handler_makeSovereign
    (actor cell : CellId) (hmem : cell ∈ s.kernel.accounts)
    (h : execHandlerOne (.makeSovereignA actor cell) s = some s') :
    ∃ s'', execFullA s (.makeSovereignA actor cell) = some s'' ∧ s''.kernel = s'.kernel :=
  handler_refines_execFullA_makeSovereign s s' actor cell hmem h

/-- CLOSED: `receiptArchiveA` handler ⊑ `execFullA` (`"lifecycle"` field ALIGNED; proved). -/
theorem portal_handler_receiptArchive
    (actor cell : CellId) (hmem : cell ∈ s.kernel.accounts)
    (h : execHandlerOne (.receiptArchiveA actor cell) s = some s') :
    ∃ s'', execFullA s (.receiptArchiveA actor cell) = some s'' ∧ s''.kernel = s'.kernel :=
  handler_refines_execFullA_receiptArchive s s' actor cell hmem h

-- F2b: the §6.6 queue-allocate portal died with the queue verb family (factory story:
-- `Apps/QueueFactory.lean`).

/-- HOLE W7: exercise inner emitted fold ⊑ `turnSpec`. -/
theorem portal_exercise_inner_turn
    (lookup : Dregg2.Circuit.TurnEmit.DescriptorLookup)
    (compress : ℤ → ℤ → ℤ) (stepRoot : Dregg2.Circuit.TurnWitness.StepWitness → ℤ)
    (hstep :
      ∀ (sw : Dregg2.Circuit.TurnWitness.StepWitness) (st st' : RecChainedState) (fa : FullActionA),
        Dregg2.Circuit.TurnEmit.stepEmittedSat lookup sw st st' fa →
          Dregg2.Circuit.ActionDispatch.fullActionStep st fa st')
    (holdPost post : RecChainedState) (inner : List FullActionA)
    (w : exerciseInnerTurnWitness lookup compress stepRoot holdPost post inner) :
    Dregg2.Circuit.ActionDispatch.turnSpec holdPost inner post :=
  exercise_inner_emitted_refines_turnSpec lookup compress stepRoot hstep holdPost post inner w

/-- **R4 facet-mask CLOSED** (P2 canonical-semantics): `execFullA`'s `exerciseA` now enforces the same
facet mask the handler bridge tags, so a handler-committed exercise refines `execFullA` on the same
kernel — given the orthogonal inner-turn fold (`hinner`). Delegates to
`ExerciseInnerTurn.exercise_r4_facet_mask`. -/
theorem portal_exercise_r4_facet_mask (actor target : CellId) (inner : List FullActionA)
    (hinner : ∃ s₁, execInnerA (Dregg2.Exec.HandlerExecutor.exerciseHoldState s actor) inner = some s₁ ∧
        s₁.kernel = s'.kernel)
    (h : execHandlerOne (.exerciseA actor target inner) s = some s') :
    ∃ s'', execFullA s (.exerciseA actor target inner) = some s'' ∧ s''.kernel = s'.kernel :=
  Dregg2.Exec.HandlerExecutor.handler_refines_execFullA_exercise s s' actor target inner hinner h

/-- **`portal_handler_exercise_fromWitness` — `hinner` SHED from the circuit inner-turn witness (the
WitnessExtractComposite pattern, ported to the HANDLER lane).** `handler_refines_execFullA_exercise`
carries `hinner` (the `execInnerA` inner fold reaching the handler's kernel) as an abstract existence
hypothesis. Here we DISCHARGE that hypothesis from the SAME circuit artifact the light-client extractor
threads: an emitted inner-turn witness `w` over the inner forest from the hold post-state, reaching a
`post` whose kernel matches the handler's commit (`hpost`). The chain is exactly the circuit's:
`exercise_inner_emitted_refines_turnSpec` reduces the emitted witness to `turnSpec`, then
`ActionDispatch.execInnerA_iff_turnSpec` converts `turnSpec` to `execInnerA … = some post` — which IS the
`hinner` existence (with `post` the witness). So the handler exercise refinement SHEDS the abstract
`hinner`: the caller supplies the circuit witness it ALREADY has (not a bare `execInnerA` claim) plus the
one genuinely-inter-executor boundary fact `post.kernel = s'.kernel`. The remaining `exercise_inner_fold`
front is now exactly that boundary equality (the handler `subTurn` ↔ live `execInnerA` agree at the
kernel) — narrowed from "supply `hinner`" to "supply the boundary kernel". -/
theorem portal_handler_exercise_fromWitness
    (actor target : CellId) (inner : List FullActionA)
    (lookup : Dregg2.Circuit.TurnEmit.DescriptorLookup)
    (compress : ℤ → ℤ → ℤ) (stepRoot : Dregg2.Circuit.TurnWitness.StepWitness → ℤ)
    (hstep :
      ∀ (sw : Dregg2.Circuit.TurnWitness.StepWitness) (st st' : RecChainedState) (fa : FullActionA),
        Dregg2.Circuit.TurnEmit.stepEmittedSat lookup sw st st' fa →
          Dregg2.Circuit.ActionDispatch.fullActionStep st fa st')
    (post : RecChainedState)
    (w : exerciseInnerTurnWitness lookup compress stepRoot
        (Dregg2.Exec.HandlerExecutor.exerciseHoldState s actor) post inner)
    (hpost : post.kernel = s'.kernel)
    (h : execHandlerOne (.exerciseA actor target inner) s = some s') :
    ∃ s'', execFullA s (.exerciseA actor target inner) = some s'' ∧ s''.kernel = s'.kernel := by
  -- (1) circuit: the emitted inner-turn witness refines `turnSpec` (same as the light-client extractor).
  have hturn : Dregg2.Circuit.ActionDispatch.turnSpec
      (Dregg2.Exec.HandlerExecutor.exerciseHoldState s actor) inner post :=
    exercise_inner_emitted_refines_turnSpec lookup compress stepRoot hstep
      (Dregg2.Exec.HandlerExecutor.exerciseHoldState s actor) post inner w
  -- (2) bridge: `turnSpec` → `execInnerA … = some post` (the inner fold ⟺ declarative spec).
  have hfold : execInnerA (Dregg2.Exec.HandlerExecutor.exerciseHoldState s actor) inner = some post :=
    (Dregg2.Circuit.ActionDispatch.execInnerA_iff_turnSpec
      (Dregg2.Exec.HandlerExecutor.exerciseHoldState s actor) post inner).mpr hturn
  -- (3) the shed `hinner`, with `post` the witness and the boundary kernel from `hpost`.
  exact Dregg2.Exec.HandlerExecutor.handler_refines_execFullA_exercise s s' actor target inner
    ⟨post, hfold, hpost⟩ h

/-- **`portal_handler_exercise_safe` — the boundary fact `hpost` SHED (`exercise_inner_fold` CLOSED on the
closable fragment).** The previous portal carried `hpost : post.kernel = s'.kernel` as a hypothesis — the
inter-executor boundary kernel-equality between the handler's `subTurn` inner fold and the live
`execInnerA`. That equality is now PROVEN (`HandlerExecutor.exercise_inner_fold_kernel_agrees`) on the
`noFrozenFace`-safe fragment: by per-effect inter-executor agreement (`handlerStep_agrees_execFullA_kernel`)
inducted over the forest, when the handler commit gives `s'.kernel` and the live fold gives `post`, the two
kernels coincide. So the caller no longer supplies the boundary kernel — only `hsafe` (the syntactic
closable-fragment guard) and the live fold `hfold` (or, downstream, the circuit witness `w` it already
threads, via `execInnerA_iff_turnSpec`). The residual is EXACTLY the un-safe complement: an inner forest
carrying a FROZEN-FACE `refreshDelegationA` / `createCellFromFactoryA` / `spawnA` (whose handler inner step
does strictly LESS than the live arm — epoch re-stamp / factory install / cap handoff). -/
theorem portal_handler_exercise_safe
    (actor target : CellId) (inner : List FullActionA) (post : RecChainedState)
    (hsafe : ∀ fa ∈ inner, Dregg2.Exec.HandlerExecutor.noFrozenFace fa = true)
    (hfold : execInnerA (Dregg2.Exec.HandlerExecutor.exerciseHoldState s actor) inner = some post)
    (h : execHandlerOne (.exerciseA actor target inner) s = some s') :
    ∃ s'', execFullA s (.exerciseA actor target inner) = some s'' ∧ s''.kernel = s'.kernel :=
  Dregg2.Exec.HandlerExecutor.handler_refines_execFullA_exercise_fromSafe s s' post actor target inner
    hsafe hfold h

end HolePortals

-- The frontier has exactly ONE GENUINELY-open handler front (drift-free: `countOpenFronts`
-- IS `openFronts.length`, so this catches any future add/remove). Non-vacuity: the registry is
-- non-empty (open work remains) yet bounded. The R4 facet-mask front is CLOSED
-- (the facet mask is enforced on `execFullA`, the canonical semantics; `portal_exercise_r4_facet_mask`),
-- the `exercise_inner_turn_witness` fold front is CLOSED (`portal_exercise_inner_turn`), and the
-- `spawn_factory_metadata` delegation/factory-install front is CLOSED (census-D4). The
-- `exercise_inner_fold` boundary is now PROVEN on the closable fragment (`exercise_inner_fold_kernel_agrees`
-- + `portal_handler_exercise_safe` shed `hpost`); the ONE remaining front is the PRECISE honest residual —
-- `exercise_inner_fold_frozenface`: an inner forest carrying a frozen-face `refreshDelegationA` /
-- `createCellFromFactoryA` / `spawnA`, where the handler inner step does strictly LESS than the live arm (a
-- GENUINE inter-executor divergence, verified; closable by routing the inner fold through the chained arms).
#guard countOpenFronts == openFronts.length
#guard countOpenFronts == 1
#guard ¬ openFronts.isEmpty
-- The closed `exercise_inner_turn_witness`, `exercise_r4_facet_mask` AND `spawn_factory_metadata` fronts
-- are not listed.
#guard (openFronts.filter (fun f => f.id == "exercise_inner_turn_witness")).isEmpty
#guard (openFronts.filter (fun f => f.id == "spawn_factory_metadata")).isEmpty

/-! ## §3 — axiom-hygiene pins for the genuine portals (the witness-threading shed + the PROVEN boundary
kernel-equality both rest on the kernel triple). -/
#assert_axioms portal_handler_exercise_fromWitness
#assert_axioms portal_handler_exercise_safe

end Dregg2.Exec.HandlerOpenFronts