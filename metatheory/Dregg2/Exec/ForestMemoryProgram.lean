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

Axiom hygiene: `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} throughout.
The composition is pure list algebra over the existing keystones.
-/
import Dregg2.Exec.UniversalBridge
import Dregg2.Exec.FullForestAuth

namespace Dregg2.Exec.ForestMemoryProgram

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (FullActionA execFullA recCexecAsset acceptsEffects)
open Dregg2.Exec.EffectsState (stateStepGuarded stateStepDev_eq)
open Dregg2.Exec.EffectsSupply (createCellStep)
open Dregg2.Authority
open Dregg2.Exec.UniversalBridge (UCodec uproj UOp gwriteTrace moveTrace moveAssetTrace createTrace
  gwrite_is_memory_program move_is_memory_program create_is_memory_program
  writeOp step3_frame step3w_hit1 step3w_hit2 step3w_hit3 writeOp_addr_ne writeOp_addr_ne_tag
  receipt_append)
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

/-! ### The per-asset MOVE keystone — the arm `execFullA` ACTUALLY routes `.balanceA` to.

`UniversalBridge.move_is_memory_program` is over `recCexec` (the named `balance` FIELD), but
`execFullA (.balanceA t a) = recCexecAsset s t a` moves the genuine multi-asset `bal c a` LEDGER
(`recKExecAsset` / `recTransferBal`). So the whole-turn coverage discharge for the (single most
common) transfer arm needs the agreement theorem ON THE `.balA` plane — proved here, where
`recCexecAsset` is in scope (it is downstream of `UniversalBridge`, in `TurnExecutorFull`). The
emitted trace `moveAssetTrace` already lives in `UniversalBridge` (pure data, no executor dep). -/

/-- `recKExecAsset`'s full gate factoring (the per-asset analogue of `RecordKernel.recKExec_factors`):
a committed per-asset move pins the post-state `bal := recTransferBal …` and exposes `src ≠ dst`
(needed to discriminate the two `.balA` writes) + the live-account memberships. -/
theorem recKExecAsset_factors {k k' : RecordKernelState} {t : Turn} {a : AssetId}
    (h : recKExecAsset k t a = some k') :
    (authorizedB k.caps t = true ∧ 0 ≤ t.amt ∧ t.amt ≤ k.bal t.src a
        ∧ t.src ≠ t.dst ∧ t.src ∈ k.accounts ∧ t.dst ∈ k.accounts
        ∧ cellLifecycleLive k t.src = true) ∧
      k' = { k with bal := recTransferBal k.bal t.src t.dst a t.amt } := by
  unfold recKExecAsset at h
  by_cases hg : authorizedB k.caps t = true ∧ 0 ≤ t.amt ∧ t.amt ≤ k.bal t.src a
      ∧ t.src ≠ t.dst ∧ t.src ∈ k.accounts ∧ t.dst ∈ k.accounts
      ∧ cellLifecycleLive k t.src = true
  · rw [if_pos hg, Option.some.injEq] at h
    exact ⟨hg, h.symm⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`moveAsset_is_memory_program`** — THE BRIDGE KEYSTONE for the move verb ON THE `bal` LEDGER
PLANE: a committed chained per-asset transfer (`recCexecAsset`, moving the genuine multi-asset
`bal c a` ledger) is EXACTLY its emitted three-op memory program (`.balA` debit + `.balA` credit +
receipt append). The per-asset SIBLING of `move_is_memory_program` (over the named `balance` field);
THIS matches the deployed `.balanceA t a` dispatch (`recCexecAsset s t a`). The `.balA` plane is
codec-free and account-gate-free (the ledger is total), so the two ledger writes carry truthful
`prevVal = some (k.bal · a)`; off the moved asset and off the moved cells the trace frames. -/
theorem moveAsset_is_memory_program (C : UCodec) {s s' : RecChainedState} {t : Turn} {a : AssetId}
    (h : recCexecAsset s t a = some s') :
    uproj C s' = (moveAssetTrace C s t a).foldl step (uproj C s) := by
  -- factor the chained per-asset step (the `acceptsEffects` admission front + `recKExecAsset`).
  have hfac : ∃ k', recKExecAsset s.kernel t a = some k'
      ∧ s' = { kernel := k', log := t :: s.log } := by
    unfold recCexecAsset at h
    by_cases hadm : acceptsEffects s.kernel t.dst
    · rw [if_pos hadm] at h
      cases hk : recKExecAsset s.kernel t a with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; simp only [Option.some.injEq] at h
          exact ⟨k', rfl, h.symm⟩
    · rw [if_neg hadm] at h; exact absurd h (by simp)
  obtain ⟨k', hk, hpost⟩ := hfac
  obtain ⟨⟨-, -, -, hne, -, -, -⟩, hk'⟩ := recKExecAsset_factors hk
  subst hpost
  subst hk'
  funext addr
  obtain ⟨d, key⟩ := addr
  simp only [moveAssetTrace, List.foldl_cons, List.foldl_nil]
  by_cases hd : d = key.domain
  case neg =>
    rw [step3_frame (writeOp_addr_ne_tag hd) (writeOp_addr_ne_tag hd)
      (writeOp_addr_ne_tag hd)]
    show (if d = key.domain then _ else none) = (if d = key.domain then _ else none)
    rw [if_neg hd, if_neg hd]
  case pos =>
  subst hd
  -- the post-state ledger plane at a single (cell, asset): `recTransferBal` unfolds to the
  -- debit/credit/frame trichotomy at the moved asset `a`, and to the frame off `a`.
  have hbal : ∀ c b, recTransferBal s.kernel.bal t.src t.dst a t.amt c b
      = if b = a then
          (if c = t.src then s.kernel.bal c b - t.amt
           else if c = t.dst then s.kernel.bal c b + t.amt else s.kernel.bal c b)
        else s.kernel.bal c b := fun c b => rfl
  cases key with
  | balA c b =>
    by_cases hcsrc : c = t.src ∧ b = a
    · obtain ⟨rfl, rfl⟩ := hcsrc
      have hne2 : UniversalBridge.UKey.balA t.src b ≠ UniversalBridge.UKey.balA t.dst b := by
        intro hcon; injection hcon with h1 _; exact hne h1
      rw [step3w_hit1 hne2 (by simp)]
      show some (recTransferBal s.kernel.bal t.src t.dst b t.amt t.src b)
        = some (s.kernel.bal t.src b - t.amt)
      rw [hbal t.src b, if_pos rfl, if_pos rfl]
    · by_cases hcdst : c = t.dst ∧ b = a
      · obtain ⟨rfl, rfl⟩ := hcdst
        rw [step3w_hit2 (by simp)]
        show some (recTransferBal s.kernel.bal t.src t.dst b t.amt t.dst b)
          = some (s.kernel.bal t.dst b + t.amt)
        rw [hbal t.dst b, if_pos rfl, if_neg (Ne.symm hne), if_pos rfl]
      · have hne1 : UniversalBridge.UKey.balA c b ≠ UniversalBridge.UKey.balA t.src a := by
          intro hcon; injection hcon with h1 h2; exact hcsrc ⟨h1, h2⟩
        have hne2 : UniversalBridge.UKey.balA c b ≠ UniversalBridge.UKey.balA t.dst a := by
          intro hcon; injection hcon with h1 h2; exact hcdst ⟨h1, h2⟩
        rw [step3_frame (writeOp_addr_ne hne1) (writeOp_addr_ne hne2)
          (writeOp_addr_ne (by simp))]
        show some (recTransferBal s.kernel.bal t.src t.dst a t.amt c b) = some (s.kernel.bal c b)
        rw [hbal c b]
        by_cases hba : b = a
        · subst hba
          rw [if_pos rfl]
          have hcs : c ≠ t.src := fun hcs => hcsrc ⟨hcs, rfl⟩
          have hcd : c ≠ t.dst := fun hcd => hcdst ⟨hcd, rfl⟩
          rw [if_neg hcs, if_neg hcd]
        · rw [if_neg hba]
  | receipt i =>
    by_cases hi : i = s.log.length
    · subst hi
      rw [step3w_hit3]
      show ((t :: s.log).reverse[s.log.length]?).map C.receipt = _
      rw [receipt_append, if_pos rfl]
      rfl
    · have hne3 : UniversalBridge.UKey.receipt i ≠ UniversalBridge.UKey.receipt s.log.length := by
        intro hcon; injection hcon with h1; exact hi h1
      rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
        (writeOp_addr_ne hne3)]
      show ((t :: s.log).reverse[i]?).map C.receipt = (s.log.reverse[i]?).map C.receipt
      rw [receipt_append, if_neg hi]
  | exist c =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | field c g =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | hcell c kk =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | lifecycle c =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | deathCert c =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | cap hh i =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | delegate c =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | delegSnap c i =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | delegEpoch c =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | delegStamp c =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | caveat c i =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | factory vk =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | nullifier nn =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | revoked nn =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl
  | commitment nn =>
    rw [step3_frame (writeOp_addr_ne (by simp)) (writeOp_addr_ne (by simp))
      (writeOp_addr_ne (by simp))]; rfl

/-- The per-asset move verb (`recCexecAsset`, the live `.balanceA` arm) is a memory program
transition — the `MemProgTrans` witness the coverage discharge consumes. -/
theorem memprog_of_moveAsset (C : UCodec) {s s' : RecChainedState} {t : Turn} {a : AssetId}
    (h : recCexecAsset s t a = some s') : MemProgTrans C s s' :=
  ⟨moveAssetTrace C s t a, moveAsset_is_memory_program C h⟩

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

/-! ## §3 — COVERAGE DISCHARGE + non-vacuity: the `setFieldA` (gwrite) AND `balanceA` (move) arms.

The honest seam `EachStepMemProg` is DISCHARGEABLE on the covered arms. TWO arms are EXACT covered
verbs:
  * `setFieldA` → `execFullA s (.setFieldA actor cell f v) = stateStepGuarded s f actor cell v` (the
    gwrite step verbatim);
  * `balanceA`  → `execFullA s (.balanceA t a) = recCexecAsset s t a` (the per-asset move verbatim) —
    the single most common verb, and the one a *value*-bearing turn is built from.
A committed gated step of either IS a memory program. We discharge BOTH, then give whole-forest
non-vacuity instances (a forest of caveat-gated field writes, AND a forest of per-asset transfers,
each end-to-end ONE memory program — NOT a vacuous frame agreement: the keystones MOVE the touched
cells). So the §149 whole-turn integrity binding holds, with NO carried per-step hypothesis, over a
covered language that now includes the value-transfer arm — the headline transfer the assurance case
puts at the front of guarantee B/C. -/

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
  have hg : stateStepGuarded s f actor cell v = some s' := stateStepDev_eq h2
  exact memprog_of_gwrite C hg

/-- **`balanceA_step_memprog`** — a committed GATED `balanceA` (per-asset transfer) step is a memory
program. The gate fires only IN FRONT of the unchanged `execFullA`, which routes `.balanceA t a` to
`recCexecAsset s t a` (the per-asset move) byte-for-byte; so the post-state is exactly that move's,
and the new `moveAsset_is_memory_program` keystone applies. This is the discharge that adds the
VALUE-TRANSFER arm to the covered language — the headline verb the assurance case fronts. -/
theorem balanceA_step_memprog (C : UCodec) {s s' : RecChainedState}
    {na : NodeAuthS (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag)}
    {t : Dregg2.Exec.Turn} {a : Dregg2.Exec.AssetId}
    (h : execFullAGated s na (FullActionA.balanceA t a) = some s') :
    MemProgTrans C s s' := by
  -- the gate passes and the underlying `execFullA` step committed (`execFullAGated_some_iff`)…
  have h2 : execFullA s (FullActionA.balanceA t a) = some s' :=
    (execFullAGated_some_iff s s' na (FullActionA.balanceA t a)).mp h |>.2
  -- …and that step IS `recCexecAsset` (the per-asset move verb), definitionally.
  have hm : recCexecAsset s t a = some s' := h2
  exact memprog_of_moveAsset C hm

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

/-- **`IsBalancePair p`** — a pre-order pair whose action is a `balanceA` (per-asset transfer). The
covered VALUE arm: `execFullA` routes it to the per-asset move (`recCexecAsset`). -/
def IsBalancePair (p : TurnPair (Digest := Digest) (Proof := Proof) (Request := Request)
    (Stmt := Stmt) (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx)
    (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag)) : Prop :=
  ∃ (t : Dregg2.Exec.Turn) (a : Dregg2.Exec.AssetId), p.2 = FullActionA.balanceA t a

/-- **`IsCoveredPair p`** — a pre-order pair whose action is a COVERED verb: either a field write
(`setFieldA`, gwrite) OR a per-asset transfer (`balanceA`, move). The covered language the whole-turn
integrity binding discharges WITHOUT a carried hypothesis. Extends the gwrite-only `IsSetFieldPair`
with the value-transfer arm — so a turn mixing field writes and transfers (the realistic shape) is
covered, not just an all-`setFieldA` turn. -/
def IsCoveredPair (p : TurnPair (Digest := Digest) (Proof := Proof) (Request := Request)
    (Stmt := Stmt) (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx)
    (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag)) : Prop :=
  IsSetFieldPair p ∨ IsBalancePair p

/-- **`eachStepMemProg_of_all_covered`** — if every pair of a linear turn is a COVERED pair
(`setFieldA` ∨ `balanceA`), the per-step memory-program coverage hypothesis is DISCHARGED: each step
is a gwrite or a per-asset move, both memory programs. The bridge from the (now richer) covered
language to the semantic `EachStepMemProg` — the seam the whole-turn integrity guarantee carried is
discharged for any turn built from field writes and value transfers, with NO out-of-band premise. -/
theorem eachStepMemProg_of_all_covered (C : UCodec)
    (zs : List (TurnPair (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag)))
    (hall : ∀ p ∈ zs, IsCoveredPair p) :
    EachStepMemProg C zs := by
  intro p hp sa sa' hstep
  rcases hall p hp with hsf | hba
  · obtain ⟨actor, cell, f, v, hpa⟩ := hsf
    rw [hpa] at hstep
    exact gwrite_step_memprog C hstep
  · obtain ⟨t, a, hpa⟩ := hba
    rw [hpa] at hstep
    exact balanceA_step_memprog C hstep

/-- **`forest_of_covered_is_memory_program` (NON-VACUITY, the WIDENED covered language).** A gated
forest whose every pre-order node carries a COVERED action (field write OR per-asset transfer) is,
end-to-end, ONE memory program. So the whole-turn binding holds non-vacuously over a forest language
that MIXES the integrity field-write arm and the headline value-transfer arm — exactly the realistic
turn shape (a payment plus a metadata write), with no carried per-step hypothesis. -/
theorem forest_of_covered_is_memory_program (C : UCodec) (s s' : RecChainedState)
    (f : FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag))
    (hall : ∀ p ∈ lowerForestG f, IsCoveredPair p)
    (h : execFullForestG s f = some s') :
    MemProgTrans C s s' :=
  execFullForestG_is_memory_program C s s' f
    (eachStepMemProg_of_all_covered C (lowerForestG f) hall) h

end Coverage

/-! ## §3.5 — NON-VACUITY: the per-asset move keystone, fold-checked address-by-address.

A real little kernel (two live accounts, two assets, an authority cap), the `.balanceA` arm COMMITS,
and the fold of `moveAssetTrace` over the pre-projection equals the post-projection at the debited
cell, the credited cell, the UNTOUCHED OTHER ASSET of the same cell (the per-asset point a scalar
move cannot make), and the appended receipt — the executable shadow of `moveAsset_is_memory_program`,
mirroring `UniversalBridge`'s three-verb non-vacuity block for the ledger-plane move. -/
section NonVacuity
open Dregg2.Exec.UniversalBridge (uaddr)
open Dregg2.Authority (Cap)

private def Cmv : UCodec :=
  { val := fun v => match v with | .int i => i | _ => 0
  , cap := fun _ => 0, caveat := fun _ => 0, factory := fun _ => 0
  , receipt := fun t => (t.actor : ℤ) + 2 * t.src + 3 * t.dst + 5 * t.amt }

private def kmv : RecordKernelState :=
  { accounts := {1, 2}
  , cell := fun _ => .record []
  , caps := fun l => if l = 1 then [Cap.node 2] else []
  , bal := fun c a => if a = 0 then (if c = 1 then 10 else if c = 2 then 3 else 0)
                      else (if c = 1 then 7 else 0) }
private def smv0 : RecChainedState := { kernel := kmv, log := [] }
private def tmv : Dregg2.Exec.Turn := { actor := 1, src := 1, dst := 2, amt := 4 }
private def smv1 : RecChainedState := (recCexecAsset smv0 tmv 0).getD smv0
private def mvtr : List UOp := moveAssetTrace Cmv smv0 tmv 0

#guard (recCexecAsset smv0 tmv 0).isSome
#guard decide (uproj Cmv smv1 (uaddr (.balA 1 0))
  = (mvtr.foldl step (uproj Cmv smv0)) (uaddr (.balA 1 0)))
#guard decide (uproj Cmv smv1 (uaddr (.balA 2 0))
  = (mvtr.foldl step (uproj Cmv smv0)) (uaddr (.balA 2 0)))
-- the OTHER asset (1) of the moved cell is untouched — the per-asset point a scalar move can't make:
#guard decide (uproj Cmv smv1 (uaddr (.balA 1 1))
  = (mvtr.foldl step (uproj Cmv smv0)) (uaddr (.balA 1 1)))
#guard decide (uproj Cmv smv1 (uaddr (.receipt 0))
  = (mvtr.foldl step (uproj Cmv smv0)) (uaddr (.receipt 0)))
-- the ledger really moved at asset 0 (not vacuous frame agreement), and asset 1 held:
#guard decide (uproj Cmv smv1 (uaddr (.balA 1 0)) = some 6)   -- 10 − 4 at asset 0
#guard decide (uproj Cmv smv1 (uaddr (.balA 2 0)) = some 7)   -- 3 + 4 at asset 0
#guard decide (uproj Cmv smv1 (uaddr (.balA 1 1)) = some 7)   -- asset 1 untouched

end NonVacuity

/-! ## §4 — axiom-hygiene pins. -/

#assert_axioms MemProgTrans
#assert_axioms memprog_refl
#assert_axioms memprog_trans
#assert_axioms memprog_of_gwrite
#assert_axioms memprog_of_move
#assert_axioms memprog_of_create
-- the NEW per-asset MOVE keystone + its discharge (the value-transfer arm — `.balanceA`):
#assert_axioms recKExecAsset_factors
#assert_axioms moveAsset_is_memory_program
#assert_axioms memprog_of_moveAsset
#assert_axioms balanceA_step_memprog
#assert_axioms eachStepMemProg_of_all_covered
#assert_axioms forest_of_covered_is_memory_program
#assert_axioms execFullTurnG_is_memory_program
#assert_axioms execFullForestG_is_memory_program
#assert_axioms gwrite_step_memprog
#assert_axioms eachStepMemProg_of_all_setField
#assert_axioms forest_of_setFields_is_memory_program

end Dregg2.Exec.ForestMemoryProgram
