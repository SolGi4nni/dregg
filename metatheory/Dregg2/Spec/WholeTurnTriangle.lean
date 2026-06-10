/-
# Dregg2.Spec.WholeTurnTriangle — the WHOLE-TURN (and cross-cell) functional+circuit triangle.

Per-EFFECT correctness is comprehensive: `Spec/FunctionalRefinement.lean` proves
`step k a = some k' ↔ (gate ∧ k' = spec k a)` for every effect family, `Circuit/ActionDispatch.lean`
gives the apex `fullActionStep st a st' ↔ execFullA st a = some st'` (each arm a transparent intent
spec via the leaf `execFullA_*_iff_spec` keystones), and `Circuit/CircuitSpecTriangle.lean` pins the
circuit to the intent for all 51 effects. The remaining GAP is COMPOSITION: a turn is a FOREST of
effects (the credential-gated `execFullForestG`), and a distributed turn coordinates MULTIPLE cells.

This module lifts the assurance from "each EFFECT is correct" to "each TURN is correct":

  * **§1–§3 — the WHOLE-TURN functional triangle (FULL BICONDITIONAL).** Define `turnSpecG`, the
    gated declarative FOLD of the per-effect `fullActionStep` intent spec over the call-forest's
    pre-order `(auth, action)` pairing, conjoining `gateOK na s = true` AT EACH NODE'S PRE-STATE (the
    same fail-closed gate the executor reads). Prove
        `execFullTurnG s zs = some s' ↔ turnSpecG s zs s'`   (the gated LINEAR triangle)
        `execFullForestG s f = some s' ↔ turnSpecG s (lowerForestG f) s'`   (the gated FOREST triangle)
    The `→` is whole-turn output-uniqueness (a committed turn pins the UNIQUE folded post-state AND
    that every gate passed at its running pre-state); the `←` is whole-turn completeness (gates+specs
    suffice for the turn to commit exactly that post-state). The inductive step is EXACTLY the
    per-effect keystones `execFullAGated_some_iff` + `fullActionStep_exec_iff` — no new effect work.

  * **§4 — gate-erasure + WHOLE-TURN ANTI-GHOST.** `turnSpecG` projects onto the ungated declarative
    `ActionDispatch.turnSpec` over the action-projection (the credential decoration is intent-orthogonal
    to the post-state): a committed gated turn's post-state IS the fold of the per-effect intent specs.
    The whole-turn anti-ghost tooth: a forest whose post-state ≠ the folded spec (`¬ turnSpecG`) is
    REJECTED — the executor never commits a turn-level ghost.

  * **§5 — the WHOLE-TURN CIRCUIT pin.** A verifying whole-turn witness pins
    `foldStepRoots … = recStateCommit s'.kernel` (the prover-folded post-root EQUALS the genuine §8
    full-state commitment of the folded post-state), bound to ONE authenticated per-turn state root —
    re-exported from `TurnCircuitCompose.turn_emitted_refines_exec_direct`, now sitting ON TOP of the
    `turnSpecG` functional triangle (the executor commit it consumes IS `turnSpecG`'s post-state).

  * **§6 — CROSS-CELL / JOINT.** A coordinated cross-cell turn computes the correct JOINT post-state
    with no cross-cell amplification/leakage: `coordinated_turn_joint_triangle` (refines the proved
    bilateral covenant step + conserves the joint total) and the N-ary `crossForest_*` keystones, with
    the distributed residue (the consensus-ordered Σ=0 linearization) carried as an
    EXPLICITLY NAMED hypothesis (`Σ_node δ = 0`), never `sorry`/`:= True`.

Discipline: transparent intent specs (`turnSpecG`/`turnSpec` fold `fullActionStep`, never `executorOp`),
full biconditionals, every theorem non-vacuous with a real whole-turn anti-ghost tooth,
`#assert_axioms`-clean. The §8 `AuthPortal.soundness` / cross-cell Σ=0 are NAMED carriers, never laws.
-/
import Dregg2.Circuit.ActionDispatch
import Dregg2.Circuit.TurnCircuitCompose
import Dregg2.Exec.FullForestAuth
import Dregg2.Exec.GatedForestCfg
import Dregg2.Exec.CoordinatedForestGLift

namespace Dregg2.Spec.WholeTurnTriangle

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Exec.FullForestAuth
open Dregg2.Authority
open Dregg2.Circuit.ActionDispatch
  (fullActionStep turnSpec fullActionStep_exec_iff execFullTurnA_iff_turnSpec turnSpec_ledger_per_asset)

/-! ## §1 — `turnSpecG`: the gated whole-turn declarative FOLD of the per-effect intent spec.

`turnSpecG s zs s'` is the left-to-right, all-or-nothing fold over the forest's pre-order
`(auth, action)` pairs (`lowerForestG f`). At EACH node it conjoins TWO transparent facts read on the
node's running PRE-state `s`:

  * `gateOK na s = true` — the 4-leg fail-closed credential+caveat+cap+revocation gate
    (`FullForestAuth.gateOK`), the WHO ∧ WHAT ∧ caveats ∧ NOT-REVOKED;
  * `fullActionStep s a s1` — the per-effect INTENT spec (`ActionDispatch.fullActionStep`, dispatching
    to the 31 leaf apex `*Spec`s — a transparent declarative post-state, NEVER `= executorOp`).

So `turnSpecG` is the composition of the per-effect intent specs UNDER the per-node gate. It is the
whole-turn analog of the per-effect triangle's RHS `(gate ∧ k' = spec k a)`. -/

section Spec
variable {Digest Proof : Type}
variable {Request Stmt Wit CellId Rights Ctx Gateway : Type}
variable [DecidableEq CellId] [SemilatticeInf Rights] [OrderTop Rights] [DecidableLE Rights]
variable {Bytes Tag : Type}
variable [instV : Dregg2.Laws.Verifiable Stmt Wit]
variable [instDT : DecidableEq Tag] [instMK : CaveatChain.MacKernel (CaveatChain.Key Tag) Bytes Tag]
variable [instAP : AuthPortal (Authorization Digest Proof) Ctx]

/-- The section's fully-applied gated-node auth carrier. We use the RAW `NodeAuth` structure
(positional, reducible) rather than the opaque `def NodeAuthS`, so that `List (NA × _)` exposes the
carrier type parameters (`Tag` etc.) for unification — letting `turnSpecG`'s instance arguments
(`DecidableEq Tag`/`MacKernel`/`AuthPortal`) synthesize at every application site. It is DEFEQ to
`FullForestAuth.NodeAuthS`/`NodeAuthC`, so `lowerForestG f : List (NA × FullActionA)` typechecks. -/
local notation "NA" => NodeAuth Digest Proof Request Stmt Wit CellId Rights Ctx Gateway Bytes Tag

/-- **`turnSpecG` — the gated whole-turn declarative fold.** The all-or-nothing pre-order fold over a
`(auth, action)` pair list: at each node BOTH the 4-leg `gateOK` holds on the running pre-state AND the
per-effect intent spec `fullActionStep` carries the step. Transparent: `fullActionStep` is the leaf
intent dispatcher, `gateOK` the fail-closed admission gate — neither is `= executor`. -/
def turnSpecG : RecChainedState → List (NA × FullActionA) → RecChainedState → Prop
  | s, [], s' => s = s'
  | s, (na, a) :: rest, s' =>
      ∃ s1, gateOK na s = true ∧ fullActionStep s a s1 ∧ turnSpecG s1 rest s'

@[simp] theorem turnSpecG_nil (s s' : RecChainedState) :
    turnSpecG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt) (Wit := Wit)
      (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway) (Bytes := Bytes)
      (Tag := Tag) s [] s' ↔ s = s' := Iff.rfl

theorem turnSpecG_cons (s s' : RecChainedState) (na : NA) (a : FullActionA)
    (rest : List (NA × FullActionA)) :
    turnSpecG s ((na, a) :: rest) s' ↔
      ∃ s1, gateOK na s = true ∧ fullActionStep s a s1 ∧ turnSpecG s1 rest s' := Iff.rfl

-- Force the §8 gate instances (`Verifiable`/`DecidableEq Tag`/`MacKernel`/`AuthPortal`) into every
-- subsequent theorem's context: their statements mention `turnSpecG` (whose gate legs need them) but
-- not the instances syntactically, so auto-include would otherwise drop them from the PROOF context.
include instV instDT instMK instAP

/-! ## §2 — the gated whole-turn LINEAR triangle (FULL BICONDITIONAL).

`execFullTurnG s zs = some s' ↔ turnSpecG s zs s'`. The inductive step is EXACTLY two existing
per-effect keystones, composed: `execFullAGated_some_iff` (the gated node commits IFF the gate passed
AND `execFullA` committed) and `fullActionStep_exec_iff` (`execFullA st a = some st1 ↔ fullActionStep
st a st1`). No new effect-level work — the whole-turn triangle is the FOLD of the per-effect triangles. -/

/-- **`execFullTurnG_iff_turnSpecG` — THE GATED WHOLE-TURN LINEAR TRIANGLE (FULL
BICONDITIONAL).** The gated linear turn executor commits EXACTLY the folded gated intent spec:
`execFullTurnG s zs = some s' ↔ turnSpecG s zs s'`. The `→` is whole-turn output-uniqueness — a
committed turn pins the UNIQUE folded post-state AND certifies the 4-leg gate passed at EVERY node's
running pre-state; the `←` is whole-turn completeness — the per-node gates+specs suffice for the turn
to commit exactly that post-state. Proved by induction on the pair list, the step being
`execFullAGated_some_iff` ∘ `fullActionStep_exec_iff`. NON-VACUOUS: a single forged credential, false
caveat, revoked nullifier, OR a tampered intermediate post-state breaks the corresponding conjunct. -/
theorem execFullTurnG_iff_turnSpecG (s s' : RecChainedState) (zs : List (NA × FullActionA)) :
    execFullTurnG s zs = some s' ↔ turnSpecG s zs s' := by
  induction zs generalizing s with
  | nil =>
      show (some s = some s') ↔ s = s'
      simp only [Option.some.injEq]
  | cons p rest ih =>
      obtain ⟨na, a⟩ := p
      rw [turnSpecG_cons]
      show (match execFullAGated s na a with
            | some s1 => execFullTurnG s1 rest
            | none    => none) = some s'
          ↔ ∃ s1, gateOK na s = true ∧ fullActionStep s a s1 ∧ turnSpecG s1 rest s'
      constructor
      · intro h
        cases hga : execFullAGated s na a with
        | none => rw [hga] at h; exact absurd h (by simp)
        | some s1 =>
            rw [hga] at h
            obtain ⟨hgate, hfa⟩ := (execFullAGated_some_iff s s1 na a).mp hga
            exact ⟨s1, hgate, (fullActionStep_exec_iff s s1 a).mp hfa, (ih s1).mp h⟩
      · rintro ⟨s1, hgate, hstep, htail⟩
        have hfa : execFullA s a = some s1 := (fullActionStep_exec_iff s s1 a).mpr hstep
        have hga : execFullAGated s na a = some s1 :=
          (execFullAGated_some_iff s s1 na a).mpr ⟨hgate, hfa⟩
        rw [hga]; exact (ih s1).mpr htail

/-- **`execFullTurnG_antighost_linear` — WHOLE-TURN ANTI-GHOST (linear).** Any candidate
post-state `s'' ` for which `turnSpecG s zs s''` FAILS is REJECTED: the gated turn executor never
commits a whole-turn ghost. Since `turnSpecG` is the unique folded intent spec under the gates, a
tampered turn-level post-state (a wrong intermediate, an extra cell touched, a skipped gate) cannot
come out of `execFullTurnG`. -/
theorem execFullTurnG_antighost_linear (s s'' : RecChainedState) (zs : List (NA × FullActionA))
    (hne : ¬ turnSpecG s zs s'') : execFullTurnG s zs ≠ some s'' := by
  intro h
  exact hne ((execFullTurnG_iff_turnSpecG s s'' zs).mp h)

/-! ## §3 — the gated whole-turn FOREST triangle (FULL BICONDITIONAL).

Lift the linear triangle to the credential-gated call-FOREST `execFullForestG` (the depth-first,
all-or-nothing, delegation-handoff tree the executor actually runs) via the proved bridge
`execFullForestG_eq_execFullTurnG : execFullForestG s f = execFullTurnG s (lowerForestG f)`. So the
WHOLE gated forest's post-state is the gated fold of the per-effect intent specs over its pre-order
`(auth, action)` flattening — including every EXECUTED delegation-handoff edge (the `recCDelegateAtten`
attenuated install `lowerForestG` emits per child). -/

/-- **`execFullForestG_iff_turnSpecG` — THE GATED WHOLE-TURN FOREST TRIANGLE (FULL
BICONDITIONAL).** The credential-gated call-forest executor commits EXACTLY the gated fold of the
per-effect intent specs over its pre-order lowering: `execFullForestG s f = some s' ↔ turnSpecG s
(lowerForestG f) s'`. The `→` pins the UNIQUE whole-FOREST post-state (every node's 4-leg gate passed
on its running pre-state ∧ every per-effect intent spec carried, at every nesting depth, across every
delegation handoff); the `←` is whole-forest completeness. This is the COMPOSITION keystone: the whole
turn is correct because each effect is correct AND the fold is the executor's. -/
theorem execFullForestG_iff_turnSpecG (s s' : RecChainedState)
    (f : FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag)) :
    execFullForestG s f = some s' ↔ turnSpecG s (lowerForestG f) s' := by
  rw [execFullForestG_eq_execFullTurnG]
  exact execFullTurnG_iff_turnSpecG s s' (lowerForestG f)

/-- **`execFullForestG_antighost` — WHOLE-FOREST ANTI-GHOST.** A whole call-forest whose
post-state `s''` is NOT the gated fold of the per-effect intent specs (`¬ turnSpecG s (lowerForestG f)
s''`) is REJECTED. The forest-level refinement pins the UNIQUE correct post-state — a tampered
whole-turn output (a wrong intermediate, an amplified delegation, an extra cell touched) cannot come
out of `execFullForestG`. -/
theorem execFullForestG_antighost (s s'' : RecChainedState)
    (f : FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag))
    (hne : ¬ turnSpecG s (lowerForestG f) s'') :
    execFullForestG s f ≠ some s'' := by
  intro h
  exact hne ((execFullForestG_iff_turnSpecG s s'' f).mp h)

/-! ## §4 — gate-erasure: the gated turn post-state IS the ungated fold of the per-effect specs.

`turnSpecG` projects onto `ActionDispatch.turnSpec` over the action-projection (the credential+caveat
decoration is intent-orthogonal to the post-state — it only NARROWS admission, it never changes a
committed post-state). So a committed gated turn's post-state is EXACTLY the ungated declarative fold
of the per-effect intent specs — the §8 gate adds the WHO/caveat/revocation precondition without
distorting the WHAT. -/

/-- **`turnSpecG_erases_turnSpec`.** Dropping the per-node gate from a gated turn-spec leaves
the ungated declarative fold of the per-effect intent specs over the action-projection: `turnSpecG s
zs s' → turnSpec s (zs.map Prod.snd) s'`. The credential gate is post-state-orthogonal: the WHAT the
turn computes is the SAME fold either way. -/
theorem turnSpecG_erases_turnSpec (s s' : RecChainedState) (zs : List (NA × FullActionA))
    (h : turnSpecG s zs s') : turnSpec s (zs.map Prod.snd) s' := by
  induction zs generalizing s with
  | nil =>
      have hss : s = s' := h
      subst hss
      show turnSpec s [] s
      rfl
  | cons p rest ih =>
      obtain ⟨na, a⟩ := p
      rw [turnSpecG_cons] at h
      obtain ⟨s1, _, hstep, htail⟩ := h
      show turnSpec s (a :: rest.map Prod.snd) s'
      exact ⟨s1, hstep, ih s1 htail⟩

/-- **`execFullForestG_post_is_intent_fold` (the headline whole-turn composition fact).** A
committed gated call-forest's post-state IS the ungated declarative fold of the per-effect intent specs
over its action-projection: `execFullForestG s f = some s' → turnSpec s ((lowerForestG f).map Prod.snd)
s'`. "Each effect is correct ∧ the executor folds them" ⇒ "the whole turn is correct": the post-state
is pinned to the composition of the per-effect intent specs. -/
theorem execFullForestG_post_is_intent_fold (s s' : RecChainedState)
    (f : FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag))
    (h : execFullForestG s f = some s') :
    turnSpec s ((lowerForestG f).map Prod.snd) s' :=
  turnSpecG_erases_turnSpec s s' (lowerForestG f)
    ((execFullForestG_iff_turnSpecG s s' f).mp h)

/-- **`execFullForestG_whole_turn_conserves` (whole-turn conservation off the intent fold).**
A committed gated call-forest moves the combined per-asset measure by EXACTLY the net per-asset delta
of its action-projection — read off the ungated `turnSpec_ledger_per_asset` through the composition
fact. The conservation VECTOR is end-to-end across the whole gated turn, pinned to the intent fold. -/
theorem execFullForestG_whole_turn_conserves (s s' : RecChainedState)
    (f : FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag)) (b : AssetId)
    (h : execFullForestG s f = some s') :
    recTotalAsset s'.kernel b
      = recTotalAsset s.kernel b
        + turnLedgerDeltaAsset ((lowerForestG f).map Prod.snd) b :=
  turnSpec_ledger_per_asset s s' ((lowerForestG f).map Prod.snd) b
    (execFullForestG_post_is_intent_fold s s' f h)

end Spec

/-! ## §5 — the WHOLE-TURN CIRCUIT pin (one authenticated state root).

The functional triangle (§1–§4) says the executor commits exactly the folded per-effect intent spec.
The circuit pin says a VERIFYING whole-turn witness binds that same composed post-state to ONE
authenticated per-turn state root. `TurnCircuitCompose.turn_emitted_refines_exec_direct` already
proves the COMPLETE stack: (1) the executor commits `execFullTurnA s acts = some s'`; (2) the
prover-folded post-root `foldStepRoots … = recStateCommit s'.kernel` (the §8 full-state commitment of
the post-state — a tampered post-root is rejected, `tampered_postRoot_rejects`); (3) the macaroon
auth-chain column is bound (`macaroonChainBinds`); (4) the multi-step wires are aligned
(`multiStepGlueAligned`). We re-export it as the whole-turn circuit pin SITTING ON the functional
triangle: the executor commit it consumes is precisely the `turnSpecG`/`turnSpec` post-state of §1–§4,
so the authenticated root pins `k' = turnSpec k turn` (the composed intent). -/

open Dregg2.Circuit.TurnCircuitCompose
  (macaroonChainBinds multiStepGlueAligned hole_turn_root_compress_binding
   turn_emitted_refines_exec_direct)
open Dregg2.Circuit.TurnEmit (DescriptorLookup TurnEmittedChain stepEmittedSat)
open Dregg2.Circuit.TurnWitness (StepWitness TurnWitness foldStepRoots)
open Dregg2.Circuit.StateCommit (recStateCommit)
open Dregg2.Circuit.ActionDispatch (fullActionStep)
open Dregg2.Exec.CircuitEmit (EmittedDescriptor)

/-- **`whole_turn_circuit_pins_intent_fold` — THE WHOLE-TURN CIRCUIT PIN (complete stack).**
A verifying whole-turn witness `w` (a `TurnEmittedChain` over the executed action list, with the
macaroon chain bound, the §8 root binding genuine, and the wires aligned) pins the composed intent:
the executor commits the folded post-state `s'`, AND the prover-folded post-root EQUALS the genuine
full-state commitment `recStateCommit s'.kernel` (ONE authenticated per-turn state root), AND the
macaroon/glue columns are load-bearing. Composed onto §1–§4: the `execFullTurnA s acts = some s'` it
exports is exactly the `turnSpec`/`turnSpecG` post-state of the whole-turn functional triangle, so the
authenticated root binds `k' = turnSpec k turn` — the §8 commitment is the NAMED carrier, everything
above it proved. Re-exports `turn_emitted_refines_exec_direct` (the complete no-fallback stack). -/
theorem whole_turn_circuit_pins_intent_fold
    (lookup : DescriptorLookup)
    (hstep :
      ∀ (sw : StepWitness) (st st' : RecChainedState) (fa : FullActionA),
        stepEmittedSat lookup sw st st' fa →
          Dregg2.Circuit.ActionDispatch.fullActionStep st fa st')
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compressN' : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ) (t : Turn)
    (baseAuth : ℤ) (steps : List EmittedDescriptor)
    (s s' : RecChainedState) (acts : List FullActionA) (w : TurnWitness)
    (compress : ℤ → ℤ → ℤ) (stepRoot : StepWitness → ℤ)
    (h : TurnEmittedChain lookup compress stepRoot s acts s' w)
    (hmac : macaroonChainBinds compress stepRoot baseAuth w)
    (hroot : hole_turn_root_compress_binding CH RH cmb compress compressN' compressN s s' t w)
    (hglue : multiStepGlueAligned steps w) :
    execFullTurnA s acts = some s' ∧
      foldStepRoots compress stepRoot w.preRoot w.steps
        = recStateCommit CH RH cmb compress compressN s'.kernel t ∧
      macaroonChainBinds compress stepRoot baseAuth w ∧
      multiStepGlueAligned steps w :=
  turn_emitted_refines_exec_direct lookup hstep CH RH cmb compressN' compressN t baseAuth steps
    s s' acts w compress stepRoot h hmac hroot hglue

/-! ## §6 — CROSS-CELL / COORDINATED (distributed) turns: the JOINT triangle.

A coordinated cross-cell turn runs over MULTIPLE cells. The within-cell `execFullForestG` fail-closes
a `.coordinated` caveat on a single snapshot (a cross-cell read cannot be faked on one cell —
`coordinated_intra_gate_failclosed`); the HONEST positive path is the bilateral pair
`execCoordinatedForestG` over two `RecChainedState` snapshots (`CoordinatedForestGLift.lean`). We tie
the gated whole-turn assurance to the cross-cell layer:

  * **JOINT triangle (PROVED where reachable).** A committed coordinated cross-cell turn refines the
    proved bilateral covenant step on the projected kernel views AND conserves the JOINT scalar total
    (`coordinated_forest_joint_recTotal_conserves`): the per-cell post-states compose into the correct
    joint post-state with NO cross-cell amplification (the covenant `φ` gates BOTH legs, fail-closed),
    and NO leakage (the joint total is preserved — value cannot be minted across the cut).

  * **N-ary joint (binding NAMED).** The N-ary cross-cell forest conserves the joint family
    total `Σ_node total (cells node)` GIVEN the consensus-ordered Σ=0 binding `Σ_node δ = 0` — an
    EXPLICITLY NAMED hypothesis (`CrossCellForest.crossForest_conserves`), load-bearing
    (`crossForest_needs_binding`), NEVER derived/`sorry`/`:= True`. The Granovetter no-amplify law
    holds unconditionally over the whole tree (`crossForest_no_amplify`).

WHAT IS PROVED vs CARRIED. Proved: the bilateral covenant-gated joint step computes the correct joint
post-state and conserves the joint total (no amplification/leakage), and the N-ary joint conservation
GIVEN the cross-cell Σ=0. CARRIED (named, not sorry'd): the distributed
consensus-ordered LINEARIZATION that establishes `Σ_node δ = 0` across independently-advancing cells
(which valid cross-cell history wins under Byzantine ordering) — a SEPARATE consensus obligation
(`Spec.JointViaHyper.hyperedge_is_validity_not_canonicity`: validity is a decidable proof-property;
canonicity is delegated to `Finality`). The §8 `AuthPortal.soundness` is likewise a NAMED carrier. -/

open Dregg2.Exec.CoordinatedForestGLift
  (BilateralForestStepG execCoordinatedForestG coordinated_forest_refines_bilateral
   coordinated_forest_joint_recTotal_conserves recChainedKernelView coordinated_intra_gate_failclosed)
open Dregg2.Exec.CoordinatedForestGate (execBilateralCoordinated)

/-- **`coordinated_turn_joint_triangle` — THE CROSS-CELL JOINT TRIANGLE.** A committed
coordinated cross-cell turn over a bilateral pair (1) refines the proved covenant-gated bilateral step
on the projected kernel views (the per-cell post-states are EXACTLY the bilateral covenant step's —
the cross-cell coordination is the proved equalizer, no amplification: the covenant `φ` gated BOTH
legs), AND (2) conserves the JOINT record total `recTotal A + recTotal B` (no value minted/leaked
across the cell cut). This is the distributed analog of the whole-turn triangle: the joint post-state
is the correct composition of the per-cell specs. -/
theorem coordinated_turn_joint_triangle (g : BilateralForestStepG)
    {sA' sB' : RecChainedState}
    (h : execCoordinatedForestG g = some (sA', sB')) :
    execBilateralCoordinated (recChainedKernelView g.pair.sA) (recChainedKernelView g.pair.sB) g.step
        = some (recChainedKernelView sA', recChainedKernelView sB')
      ∧ recTotal sA'.kernel + recTotal sB'.kernel
          = recTotal g.pair.sA.kernel + recTotal g.pair.sB.kernel :=
  ⟨coordinated_forest_refines_bilateral g h,
   coordinated_forest_joint_recTotal_conserves g h⟩

/-- **`coordinated_turn_no_intra_cross_read` — the cross-cell DISCIPLINE.** A `.coordinated`
(cross-cell) caveat fail-closes on a single-cell snapshot — a cross-cell read cannot be faked intra-
cell. So a coordinated turn CANNOT silently pass on one cell: it MUST route through the honest
bilateral pair path (`execCoordinatedForestG`), where the covenant gates both legs. This is what
forecloses the dregg1 `authorize.rs:1608` cross-cell hole at the whole-turn level. -/
theorem coordinated_turn_no_intra_cross_read (c : GatedCaveat) (s : RecChainedState)
    (hc : c.tier = .coordinated) (hno : c.cross = none) : c.holds s = false :=
  coordinated_intra_gate_failclosed c s hc hno

/-! ## §7 — NON-VACUITY TEETH (`#guard`) at the starbridge production carriers + axiom hygiene.

The gated whole-turn triangle is exercised on the concrete `StarbridgeGated` forests (the production
carriers): a good multi-node forest commits (turnSpecG holds at a real post-state), a forged-credential
/ false-caveat / amplifying-cap forest is rejected (the corresponding `turnSpecG` conjunct fails), and
the post-state is the intent fold (conservation). These ride `execFullForestG` directly, so the
`#guard`s witness the triangle's two directions are both non-trivial. -/

open Dregg2.Exec.StarbridgeGated

-- A good multi-node gated forest COMMITS ⇒ `turnSpecG fmaDeleg (lowerForestG goodFullForestG)` holds
-- at the committed post-state (the `→` direction is reached: a real whole-turn post-state exists).
#guard ((execFullForestG fmaDeleg goodFullForestG).isSome)
-- The whole-turn post-state is the INTENT FOLD: balance-neutral in every asset (conservation).
#guard (turnLedgerDeltaAsset ((lowerForestG goodFullForestG).map Prod.snd) 0) == 0
#guard (turnLedgerDeltaAsset ((lowerForestG goodFullForestG).map Prod.snd) 1) == 0
-- A FORGED-credential forest is REJECTED ⇒ NO `s''` has `turnSpecG … s''` (the WHO conjunct fails) —
-- so by `execFullForestG_antighost` the executor commits no whole-turn output. (The `←` has teeth.)
#guard ((execFullForestG fmaDeleg forgedCredForestG).isSome) == false
-- A FALSE-caveat forest is REJECTED (the caveat conjunct of `gateOK` fails on the running pre-state).
#guard ((execFullForestG fmaDeleg falseCaveatForestG).isSome) == false
-- A LAUNDERING forest (per-asset net nonzero) still COMMITS but its post-state is the intent fold:
-- a NONZERO per-asset delta — the conservation VECTOR catches it (a scalar measure could not).
#guard (turnLedgerDeltaAsset ((lowerForestG launderFullForestG).map Prod.snd) 0) == -50
#guard (turnLedgerDeltaAsset ((lowerForestG launderFullForestG).map Prod.snd) 1) == 50
-- A transfer forest commits; its single-effect intent fold is balance-neutral (asset 0).
#guard ((execFullForestG fma0 transferForestG).isSome)
#guard (turnLedgerDeltaAsset ((lowerForestG transferForestG).map Prod.snd) 0) == 0

/-! ## §8 — Axiom-hygiene tripwires. Every whole-turn/cross-cell keystone rests only on the kernel
axioms (no `sorryAx`); the §8 `AuthPortal.soundness` and cross-cell Σ=0 are NAMED carriers, not laws. -/

#assert_axioms execFullTurnG_iff_turnSpecG
#assert_axioms execFullTurnG_antighost_linear
#assert_axioms execFullForestG_iff_turnSpecG
#assert_axioms execFullForestG_antighost
#assert_axioms turnSpecG_erases_turnSpec
#assert_axioms execFullForestG_post_is_intent_fold
#assert_axioms execFullForestG_whole_turn_conserves
#assert_axioms whole_turn_circuit_pins_intent_fold
#assert_axioms coordinated_turn_joint_triangle
#assert_axioms coordinated_turn_no_intra_cross_read

end Dregg2.Spec.WholeTurnTriangle
