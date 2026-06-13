/-
# Dregg2.Exec.ForestMemoryProgram — the WHOLE-TURN / WHOLE-FOREST memory program.

`Exec/UniversalBridge.lean` proves the executor IS a memory program for each of the three
compressed verbs against its live executable step (`gwrite_is_memory_program` /
`move_is_memory_program` / `create_is_memory_program`): the TOTAL projection (`uproj`) of the
post-state equals the fold of the verb's emitted Blum trace over the pre-state projection. Those
are PER-STEP facts.

This module composes them to the WHOLE TURN — closing `docs/ASSURANCE-CRITIQUE.md` MEDIUM-8 ("the
whole-post-state binding is per-step (3 verbs) and is NOT yet composed to whole-turn") — and it is
the machinery `AssuranceCase.deployed_system_secure` uses to put the integrity-C(c2) leg over the
SAME forest `f` as the A/B/c1 legs (MEDIUM-7).

The keystone observation is that the memory-program property is CLOSED UNDER SEQUENTIAL
COMPOSITION: `foldl` distributes over `++` (`List.foldl_append`). So if a transition `s → s'`
folds trace `T₁` and `s' → s''` folds `T₂`, then `s → s''` folds `T₁ ++ T₂`. The whole-forest
trace is the concatenation, in execution order, of the per-node traces.

Three movements:

  1. **THE TRANSITION PROPERTY** (`MemProgTrans C s s'`): there is a Blum trace whose fold over the
     pre-state projection IS the post-state projection. Reflexive; closed under composition
     (`memprog_trans`). The per-verb keystones are exactly `MemProgTrans` witnesses for the three
     verbs (`memprog_of_gwrite`/`_move`/`_create`).

  2. **THE WHOLE-TURN COMPOSITION** (`execFullTurnG_is_memory_program`): for the gated LINEAR turn
     `execFullTurnG` — the pre-order `(auth, action)` lowering the gated tree reduces to — IF every
     committing step is a memory program (`EachStepMemProg`, the honestly-named per-arm coverage
     hypothesis), THEN the whole turn `s → s'` is a memory program. Threaded induction along the
     all-or-nothing fold, the SAME shape as `FullForestAuth.execFullTurnG_each_attests`.

  3. **THE WHOLE-FOREST LIFT** (`execFullForestG_is_memory_program`): read through the gated bridge
     `execFullForestG_eq_execFullTurnG`, the gated TREE executor `execFullForestG s f = some s'` is
     a memory program over the same `(s, f, s')` the running-entry guarantees (A/B/c1) bind.

Coverage / the named seam: the per-step hypothesis `EachStepMemProg` is DISCHARGEABLE exactly on
the arms the three keystones cover. The `setFieldA` arm is an EXACT covered verb — `execFullA` routes
it to `stateStepGuarded` (the gwrite step) verbatim — so `setFieldCovered`/`gwrite_step_memprog`
discharge it, and `forest_of_setFields_is_memory_program` is a NON-VACUOUS whole-forest instance: a
forest of caveat-gated field writes is, end-to-end, one memory program. Arms not yet welded to a
keystone enter as the explicit per-step hypothesis — the residual the critique asks to be named, not
laundered: `EachStepMemProg` is a Prop the caller must supply, never assumed here.

Axiom hygiene: `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} throughout; no `sorry`,
no `:= True`, no `native_decide`. The composition is pure list algebra over the existing keystones.
-/
import Dregg2.Exec.UniversalBridge
import Dregg2.Exec.FullForestAuth

namespace Dregg2.Exec.ForestMemoryProgram

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (FullActionA execFullA)
open Dregg2.Exec.EffectsState (stateStepGuarded)
open Dregg2.Exec.EffectsSupply (createCellStep)
open Dregg2.Authority
open Dregg2.Exec.UniversalBridge (UCodec uproj UOp gwriteTrace moveTrace createTrace
  gwrite_is_memory_program move_is_memory_program create_is_memory_program)
open Dregg2.Exec.FullForestAuth
open Dregg2.Crypto.MemoryChecking (step)

/-! ## §1 — THE TRANSITION PROPERTY: a state move that IS a memory program.

`MemProgTrans C s s'` packages the keystone shape — "some Blum trace folds the pre-projection to
the post-projection" — as a composable relation on states. The witness trace is existentially
hidden because the WHOLE-turn trace is a concatenation whose exact contents are bookkeeping; what
the integrity guarantee needs is that ONE exists (every post-state cell is the deterministic image
of a memory program the executor can emit from the pre-state alone). -/

/-- **`MemProgTrans C s s'`** — the transition `s → s'` is a memory program under codec `C`: there
is a universal-memory op trace `tr` whose `MemoryChecking.step`-fold over the projection of `s` is
the projection of `s'`. The composable form of the three `UniversalBridge` keystones. -/
def MemProgTrans (C : UCodec) (s s' : RecChainedState) : Prop :=
  ∃ tr : List UOp, uproj C s' = tr.foldl step (uproj C s)

/-- The empty trace witnesses the identity transition (`foldl step _ [] = id`). -/
theorem memprog_refl (C : UCodec) (s : RecChainedState) : MemProgTrans C s s :=
  ⟨[], rfl⟩

/-- **`memprog_trans`** — memory programs COMPOSE. If `s → s'` folds some trace and `s' → s''`
folds some trace, then `s → s''` folds their CONCATENATION (`List.foldl_append`). This is the whole
content of "compose the per-verb memory programs to a whole-turn memory program": sequential
execution concatenates traces, and the fold respects it. -/
theorem memprog_trans (C : UCodec) {s s' s'' : RecChainedState}
    (h1 : MemProgTrans C s s') (h2 : MemProgTrans C s' s'') : MemProgTrans C s s'' := by
  obtain ⟨tr1, h1⟩ := h1
  obtain ⟨tr2, h2⟩ := h2
  refine ⟨tr1 ++ tr2, ?_⟩
  rw [List.foldl_append, ← h1, h2]

/-! ## §2 — THE PER-VERB WITNESSES: each keystone is a `MemProgTrans`. -/

/-- The gwrite verb (caveat-gated field write `stateStepGuarded`) is a memory program transition. -/
theorem memprog_of_gwrite (C : UCodec) {s s' : RecChainedState} {f : FieldName}
    {actor target : CellId} {n : Int} (h : stateStepGuarded s f actor target n = some s') :
    MemProgTrans C s s' :=
  ⟨gwriteTrace C s f actor target n, gwrite_is_memory_program C h⟩

/-- The move verb (chained conserving transfer `recCexec`) is a memory program transition. -/
theorem memprog_of_move (C : UCodec) {s s' : RecChainedState} {t : Turn}
    (h : recCexec s t = some s') : MemProgTrans C s s' :=
  ⟨moveTrace C s t, move_is_memory_program C h⟩

/-- The create verb (bundle birth `createCellStep`) is a memory program transition. -/
theorem memprog_of_create (C : UCodec) {s s' : RecChainedState} {actor newCell : CellId} {bal : ℤ}
    (h : createCellStep s actor newCell bal = some s') : MemProgTrans C s s' :=
  ⟨createTrace C s actor newCell bal, create_is_memory_program C h⟩

section WholeTurn
variable {Digest Proof : Type}
variable {Request Stmt Wit CellId Rights Ctx Gateway : Type}
variable [DecidableEq CellId] [SemilatticeInf Rights] [OrderTop Rights] [DecidableLE Rights]
variable {Bytes Tag : Type}
variable [Dregg2.Laws.Verifiable Stmt Wit]
variable [DecidableEq Tag] [CaveatChain.MacKernel (CaveatChain.Key Tag) Bytes Tag]
variable [AuthPortal (Authorization Digest Proof) Ctx]

/-- The section's `(auth, action)` pair type — the element of the gated linear lowering. -/
abbrev TurnPair := NodeAuthS (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
  (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
  (Bytes := Bytes) (Tag := Tag) × FullActionA

/-- **`EachStepMemProg C zs`** — the per-step coverage hypothesis: for EVERY pre-order pair
`(na, a)` in the linear turn `zs`, AT WHATEVER STATE it executes on, a committing gated step is a
memory program. This is the honestly-named seam (the critique's MEDIUM-8 residual): it holds for the
covered verb arms (`setFieldA` → gwrite, etc.), and it is a Prop the caller must SUPPLY — never
assumed, never `True`. `forest_of_setFields_is_memory_program` discharges it for an all-`setFieldA`
turn, witnessing non-vacuity. -/
def EachStepMemProg (C : UCodec) (zs : List (TurnPair (Digest := Digest) (Proof := Proof)
    (Request := Request) (Stmt := Stmt) (Wit := Wit) (CellId := CellId) (Rights := Rights)
    (Ctx := Ctx) (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag))) : Prop :=
  ∀ p ∈ zs, ∀ sa sa' : RecChainedState,
    execFullAGated sa p.1 p.2 = some sa' → MemProgTrans C sa sa'

/-- A tail of an `EachStepMemProg` list still satisfies it (membership monotonicity). -/
theorem EachStepMemProg.tail {C : UCodec} {q : TurnPair (Digest := Digest) (Proof := Proof)
    (Request := Request) (Stmt := Stmt) (Wit := Wit) (CellId := CellId) (Rights := Rights)
    (Ctx := Ctx) (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag)}
    {rest : List (TurnPair (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag))}
    (h : EachStepMemProg C (q :: rest)) : EachStepMemProg C rest :=
  fun p hp sa sa' hstep => h p (List.mem_cons_of_mem _ hp) sa sa' hstep

/-- **`execFullTurnG_is_memory_program` (THE WHOLE-TURN COMPOSITION — MEDIUM-8).** For the gated
LINEAR turn (the pre-order `(auth, action)` fold the gated tree reduces to): IF the whole turn
commits (`execFullTurnG s zs = some s'`) AND every step is a memory program (`EachStepMemProg`),
THEN the whole turn `s → s'` is a memory program — the projection of the final post-state is the
fold of the CONCATENATED per-step traces over the projection of the initial pre-state. The per-verb
memory programs, composed end-to-end. Threaded along the all-or-nothing fold, the SAME induction as
`execFullTurnG_each_attests`, with `memprog_trans` welding adjacent steps. -/
theorem execFullTurnG_is_memory_program (C : UCodec) (s s' : RecChainedState)
    (zs : List (TurnPair (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag)))
    (hcov : EachStepMemProg C zs)
    (h : execFullTurnG s zs = some s') :
    MemProgTrans C s s' := by
  -- Revert the endpoint, the coverage hypothesis and the run, then induct on the turn so the IH is
  -- fully general in all three (`hcov` mentions `zs`, the induction subject — it must travel along).
  induction zs generalizing s s' with
  | nil =>
      -- empty turn: `execFullTurnG s [] = some s`, so `s = s'`.
      have : s = s' := by simpa [execFullTurnG] using h
      exact this ▸ memprog_refl C s
  | cons q rest ih =>
      obtain ⟨na, a⟩ := q
      rw [show execFullTurnG s ((na, a) :: rest)
            = (match execFullAGated s na a with
               | some s1 => execFullTurnG s1 rest
               | none    => none) from rfl] at h
      cases hga : execFullAGated s na a with
      | none => rw [hga] at h; exact absurd h (by simp)
      | some s1 =>
          rw [hga] at h
          -- head step is a memory program (coverage at the head pair, state `s`)…
          have hhead : MemProgTrans C s s1 :=
            hcov (na, a) List.mem_cons_self s s1 hga
          -- …and the tail composes by IH (run from `s1`, coverage restricted to the tail).
          have htail : MemProgTrans C s1 s' := ih s1 s' hcov.tail h
          exact memprog_trans C hhead htail

/-- **`execFullForestG_is_memory_program` (THE WHOLE-FOREST LIFT — MEDIUM-7/8).** The gated TREE
executor — the body behind the `dregg_exec_full_forest_auth` FFI the node invokes on every committed
turn — is a memory program over the SAME `(s, f, s')` the running-entry guarantees bind: a committed
`execFullForestG s f = some s'`, under per-step coverage of its pre-order lowering, has
`uproj C s' = (whole-forest trace).foldl step (uproj C s)`. So "a receipt binds the WHOLE post-state"
holds over the WHOLE TURN, not just one verb. Read through the gated bridge
`execFullForestG_eq_execFullTurnG` into the linear composition above. -/
theorem execFullForestG_is_memory_program (C : UCodec) (s s' : RecChainedState)
    (f : FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag))
    (hcov : EachStepMemProg C (lowerForestG f))
    (h : execFullForestG s f = some s') :
    MemProgTrans C s s' := by
  rw [execFullForestG_eq_execFullTurnG] at h
  exact execFullTurnG_is_memory_program C s s' (lowerForestG f) hcov h

end WholeTurn

/-! ## §3 — COVERAGE DISCHARGE + non-vacuity: the `setFieldA` (gwrite) arm.

The honest seam `EachStepMemProg` is DISCHARGEABLE on the covered arms. `setFieldA` is an EXACT
covered verb: `execFullA s (.setFieldA actor cell f v) = stateStepGuarded s f actor cell v` (the
gwrite step verbatim), so a committed gated `setFieldA` step IS a memory program. We discharge it,
then give a whole-forest non-vacuity instance — a forest of caveat-gated field writes is, end to
end, one memory program (NOT a vacuous frame agreement: the gwrite keystone moves the written cell). -/

section Coverage
variable {Digest Proof : Type}
variable {Request Stmt Wit CellId Rights Ctx Gateway : Type}
variable [DecidableEq CellId] [SemilatticeInf Rights] [OrderTop Rights] [DecidableLE Rights]
variable {Bytes Tag : Type}
variable [Dregg2.Laws.Verifiable Stmt Wit]
variable [DecidableEq Tag] [CaveatChain.MacKernel (CaveatChain.Key Tag) Bytes Tag]
variable [AuthPortal (Authorization Digest Proof) Ctx]

/-- **`gwrite_step_memprog`** — a committed GATED `setFieldA` step is a memory program. The gate
fires only IN FRONT of the unchanged `execFullA`, which routes `setFieldA` to `stateStepGuarded`
(the gwrite verb) byte-for-byte; so the post-state is exactly the gwrite step's, and the gwrite
keystone applies. The discharge that makes `EachStepMemProg` non-vacuous. -/
theorem gwrite_step_memprog (C : UCodec) {s s' : RecChainedState}
    {na : NodeAuthS (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag)}
    -- the ACTION layer is over the CONCRETE kernel cell/field types (`FullActionA` is not polymorphic
    -- in them — only the credential layer `na` carries the abstract section `CellId`/`Rights`).
    {actor cell : Dregg2.Exec.CellId} {f : Dregg2.Exec.FieldName} {v : Int}
    (h : execFullAGated s na (FullActionA.setFieldA actor cell f v) = some s') :
    MemProgTrans C s s' := by
  -- the gate passes and the underlying `execFullA` step committed (`execFullAGated_some_iff`)…
  have h2 : execFullA s (FullActionA.setFieldA actor cell f v) = some s' :=
    (execFullAGated_some_iff s s' na (FullActionA.setFieldA actor cell f v)).mp h |>.2
  -- …and that step IS `stateStepGuarded` (the gwrite verb), definitionally.
  have hg : stateStepGuarded s f actor cell v = some s' := h2
  exact memprog_of_gwrite C hg

/-- **`IsSetFieldPair p`** — a pre-order pair whose action is a `setFieldA`. The covered shape:
its second component (the `FullActionA`) is a field write, which `execFullA` routes to the gwrite
verb. -/
def IsSetFieldPair (p : TurnPair (Digest := Digest) (Proof := Proof) (Request := Request)
    (Stmt := Stmt) (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx)
    (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag)) : Prop :=
  ∃ (actor cell : Dregg2.Exec.CellId) (f : Dregg2.Exec.FieldName) (v : Int),
    p.2 = FullActionA.setFieldA actor cell f v

/-- **`eachStepMemProg_of_all_setField`** — if every pair of a linear turn is a `setFieldA` pair,
the per-step memory-program coverage hypothesis is DISCHARGED (each step is a gwrite). The bridge
from a syntactic covered-language condition to the semantic `EachStepMemProg`. -/
theorem eachStepMemProg_of_all_setField (C : UCodec)
    (zs : List (TurnPair (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag)))
    (hall : ∀ p ∈ zs, IsSetFieldPair p) :
    EachStepMemProg C zs := by
  intro p hp sa sa' hstep
  obtain ⟨actor, cell, f, v, hpa⟩ := hall p hp
  -- rewrite the action to its `setFieldA` shape and discharge by the gwrite step.
  rw [hpa] at hstep
  exact gwrite_step_memprog C hstep

/-- **`forest_of_setFields_is_memory_program` (NON-VACUITY).** A gated forest whose every pre-order
node carries a `setFieldA` action is, end-to-end, ONE memory program: `uproj C s' = (whole trace).
foldl step (uproj C s)`. So the whole-turn binding is not a vacuous abstraction — there is a concrete
forest language over which "a receipt binds the WHOLE post-state" holds for the WHOLE TURN. -/
theorem forest_of_setFields_is_memory_program (C : UCodec) (s s' : RecChainedState)
    (f : FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag))
    (hall : ∀ p ∈ lowerForestG f, IsSetFieldPair p)
    (h : execFullForestG s f = some s') :
    MemProgTrans C s s' :=
  execFullForestG_is_memory_program C s s' f
    (eachStepMemProg_of_all_setField C (lowerForestG f) hall) h

end Coverage

/-! ## §4 — axiom-hygiene pins. -/

#assert_axioms MemProgTrans
#assert_axioms memprog_refl
#assert_axioms memprog_trans
#assert_axioms memprog_of_gwrite
#assert_axioms memprog_of_move
#assert_axioms memprog_of_create
#assert_axioms execFullTurnG_is_memory_program
#assert_axioms execFullForestG_is_memory_program
#assert_axioms gwrite_step_memprog
#assert_axioms eachStepMemProg_of_all_setField
#assert_axioms forest_of_setFields_is_memory_program

end Dregg2.Exec.ForestMemoryProgram
