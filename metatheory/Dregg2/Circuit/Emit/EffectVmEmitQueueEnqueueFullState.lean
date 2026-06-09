/-
# Dregg2.Circuit.Emit.EffectVmEmitQueueEnqueueFullState — the MAGNESIUM lift of `queueEnqueueA`'s
RUNNABLE EffectVM descriptor to FULL state (all 17 `RecordKernelState` fields bound, INCLUDING the
`queues` side-table root).

## The gap this module closes (for the queue family)

`EffectVmEmitQueueEnqueue.queueEnqueueVmDescriptor` is a `186`-wide row whose published `state_commit`
absorbs the 13 state-block columns (via `transferHashSites`). The FIFO append is bound at `fields[4]`
(the in-row queue-root carrier), but the `state_commit` does NOT absorb the dedicated, non-aliasing
`system_roots` digest carrier (`sysRootsDigestCol = 186`, PAST the `186`-wide layout) — so the queue
side-table is bound by the descriptor only as a per-cell `fields[4]` projection, NOT as the whole
8-root `system_roots` sub-block. A satisfying RUNNABLE proof pins a projection, not the WHOLE post-state.

This module SUPERSEDES that with the verified-by-construction WIDE descriptor + the GENERIC full-state
crown `EffectVmFullStateRunnable.runnable_full_sound` on the RUNNABLE `EffectVmDescriptor` /
`satisfiedVm`. The widening follows the §6 RECIPE verbatim:

  1. **the wide descriptor** `queueEnqueueVmDescriptorWide`: take the existing `186`-wide enqueue
     descriptor, set `traceWidth := EFFECT_VM_WIDTH_SYSROOTS`, `hashSites := wideHashSites`
     (so `usesWideSites := rfl`), and ADD the root-UPDATE gate `gQueueSysRootUpdate` pinning
     `sysRootsDigestCol = sysRootsDigestColBefore + step` over the DEDICATED carrier (the §6 step-1
     gate, exactly `EffectVmEmitCreateEscrow.gEscrowRootUpdate`'s shape, re-targeted onto the
     non-aliasing `sysRootsDigestCol`/`sysRootsDigestColBefore` instead of the raw `96`).
  2. **`isRow`** := `IsQueueEnqueueRow` (selector hot, NoOp cold).
  3. **`decodeAfter`** := `RowEncodesEnqueue` (the structured per-cell column decode), EXTENDED with the
     `queues`-root structural transition `postRoots = Function.update preRoots QUEUE newQueueRoot`.
  4. **`fullClause`** := the declarative 17-field post for enqueue: the per-cell `CellEnqueueSpec`
     (balance debited by the deposit, the queue-root cell advanced, nonce ticked, the frame frozen) AND
     the `system_roots` sub-block moved ONLY at the `QUEUE` index (the other 7 roots — escrow /
     nullifier / commit / sturdyref / sealed / deleg / refcount — FROZEN).
  5. **`decodeFull`** := THIN: project the wide descriptor's per-row gates (a sublist of its constraints)
     to `QueueEnqueueRowIntent` (the audited `queueEnqueueVm_faithful`), then `intent_to_cellEnqueueSpec`
     to `CellEnqueueSpec`, then carry the decode's root transition.

The crypto is DISCHARGED ONCE in the generic module (`wide_binds_everything` + `wide_binds_systemRoots`);
this per-effect instance carries NO new portal — only the (already proved) per-row faithfulness + the
decode. The anti-ghost on all 17 fields is `runnable_full_commit_binds`/`wide_rejects_state_tamper`/
`wide_rejects_root_tamper` instantiated at this spec (§3 below): tampering ANY absorbed state-block
column OR ANY of the 8 side-table roots (incl. the queue root) while keeping the published `NEW_COMMIT`
is UNSAT under `Poseidon2SpongeCR`.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; the sole crypto carrier is the named
`Poseidon2SpongeCR` portal (in the generic theorems). No `sorry`, no `:= True`, no `native_decide`.
`fullClause` is NON-vacuous (witness TRUE + a refuted forged post-state). Imports are read-only; this
file owns only itself.
-/
import Dregg2.Circuit.Emit.EffectVmEmitQueueEnqueue
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable

namespace Dregg2.Circuit.Emit.EffectVmEmitQueueEnqueueFullState

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSub boundaryLastPins boundaryLast_pins transferHashSites)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState absorbedCols)
open Dregg2.Circuit.Emit.EffectVmEmitQueueEnqueue
  (SEL_QUEUE_ENQUEUE IsQueueEnqueueRow QUEUE_ROOT_FIELD DepositParams CellEnqueueSpec
   RowEncodesEnqueue QueueEnqueueRowIntent queueEnqueueRowGates queueEnqueueVmDescriptor
   queueEnqueueVm_faithful intent_to_cellEnqueueSpec gFieldPassNonRoot)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (wideHashSites RunnableFullStateSpec runnable_full_sound runnable_full_commit_binds
   wide_rejects_state_tamper wide_rejects_root_tamper)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec.SystemRoots
  (SysRoots systemRootsDigest N_SYSTEM_ROOTS emptySystemRoots)

set_option linter.unusedVariables false

/-! ## §0 — the `queues` side-table root index + the accumulator-step carrier (over the DEDICATED columns). -/

/-- The kernel index of the `queues` side-table root in the `system_roots` sub-block
(`Exec.SystemRoots.systemRoot.QUEUE = 1`). The digest the dedicated carrier commits includes THIS root,
so binding the carrier binds the queue root. -/
def QUEUE_ROOT_INDEX : Fin N_SYSTEM_ROOTS := ⟨Dregg2.Exec.SystemRoots.systemRoot.QUEUE, by decide⟩

/-- The `queues`-accumulator STEP param: the field-element delta the appended message contributes to the
`system_roots` digest (`systemRootsDigest` over the sub-block before vs after). The trace generator lays
it at `param2` (param1 = the deposit; param2 = the digest step the prover computed from the FIFO append),
exactly as `EffectVmEmitCreateEscrow.ESCROW_ROOT_STEP_PARAM` lays the escrow step at `param2`. -/
def QUEUE_ROOT_STEP_PARAM : Nat := 2

/-- The accumulator-step expression (param column 2). -/
def ePrmQueueStep : EmittedExpr := .var (prmCol QUEUE_ROOT_STEP_PARAM)

/-- **Root-UPDATE gate body** over the DEDICATED carrier: `sysRootsDigestCol − sysRootsDigestColBefore −
step` (so `sysRootsDigestCol = sysRootsDigestColBefore + step`). Reads the before/after `system_roots`
digest carriers (`= 187` / `= 186`, both PAST the `186`-wide layout, non-aliasing) and the `param2`
accumulator step. This is the §6 step-1 gate, re-targeted onto the dedicated carrier the wide commitment
ABSORBS (via `wideHashSites`). -/
def gQueueSysRootUpdate : EmittedExpr :=
  eSub (eSub (.var sysRootsDigestCol) (.var sysRootsDigestColBefore)) ePrmQueueStep

/-! ## §1 — the WIDE enqueue descriptor (§6 step-1). -/

/-- **`queueEnqueueVmDescriptorWide newRoot`** — the enqueue descriptor WIDENED to bind the WHOLE
`system_roots` sub-block: the SAME per-row gates + transitions + boundary pins as
`queueEnqueueVmDescriptor newRoot`, PLUS the `system_roots`-digest root-UPDATE gate `gQueueSysRootUpdate`,
with `traceWidth := EFFECT_VM_WIDTH_SYSROOTS` and `hashSites := wideHashSites` (the `system_roots`-
absorbing sites). Strictly additive: the constraint list gains exactly one gate; the width grows by 2;
the 4th outer hash slot becomes the dedicated `system_roots` carrier instead of `0`. -/
def queueEnqueueVmDescriptorWide (newRoot : ℤ) : EffectVmDescriptor :=
  { queueEnqueueVmDescriptor newRoot with
    name := "dregg-effectvm-queueenqueue-v1-sysroots"
    traceWidth := EFFECT_VM_WIDTH_SYSROOTS
    constraints := (queueEnqueueVmDescriptor newRoot).constraints ++ [.gate gQueueSysRootUpdate]
    hashSites := wideHashSites }

/-- The wide descriptor's hash-sites ARE the `system_roots`-absorbing wide sites (so the published
`state_commit` binds the 13 absorbed columns + the side-table digest). By `rfl`. -/
theorem queueEnqueueWide_usesWideSites :
    (queueEnqueueVmDescriptorWide 0).hashSites = wideHashSites := rfl

/-- The per-row queue gates remain a sublist of the wide descriptor's constraints (the additive root gate
sits AFTER them; the widening leaves the gate list otherwise byte-identical). -/
theorem queueEnqueueWide_rowGates_sub (newRoot : ℤ) (c : VmConstraint)
    (hc : c ∈ queueEnqueueRowGates newRoot) :
    c ∈ (queueEnqueueVmDescriptorWide newRoot).constraints := by
  show c ∈ ((queueEnqueueVmDescriptor newRoot).constraints ++ [.gate gQueueSysRootUpdate])
  rw [List.mem_append]
  refine Or.inl ?_
  unfold queueEnqueueVmDescriptor
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl hc))

/-- The boundary-last PI pins remain in the wide descriptor's constraints. -/
theorem queueEnqueueWide_boundaryLast_sub (newRoot : ℤ) (c : VmConstraint)
    (hc : c ∈ boundaryLastPins) :
    c ∈ (queueEnqueueVmDescriptorWide newRoot).constraints := by
  show c ∈ ((queueEnqueueVmDescriptor newRoot).constraints ++ [.gate gQueueSysRootUpdate])
  rw [List.mem_append]
  refine Or.inl ?_
  unfold queueEnqueueVmDescriptor
  simp only [List.mem_append]
  exact Or.inr hc

/-! ## §2 — FAITHFULNESS + ANTI-GHOST of the dedicated-carrier root-update gate. -/

/-- **`QueueSysRootIntent env`** — the intended `queues`-root move on the row: the dedicated
`system_roots` digest carrier ADVANCES by the `param2` accumulator step
(`sysRootsDigestCol = sysRootsDigestColBefore + step`). The per-row projection of the FIFO append onto
the committed `system_roots` digest. -/
def QueueSysRootIntent (env : VmRowEnv) : Prop :=
  env.loc sysRootsDigestCol = env.loc sysRootsDigestColBefore + env.loc (prmCol QUEUE_ROOT_STEP_PARAM)

/-- **`queueSysRoot_gate_faithful`.** The root-update gate holds IFF the dedicated digest carrier advances
by the accumulator step — the gate pins EXACTLY the `queues`-root update over the bound carrier. -/
theorem queueSysRoot_gate_faithful (env : VmRowEnv) :
    (VmConstraint.gate gQueueSysRootUpdate).holdsVm env false false ↔ QueueSysRootIntent env := by
  simp only [VmConstraint.holdsVm, gQueueSysRootUpdate, ePrmQueueStep, eSub, EmittedExpr.eval,
    QueueSysRootIntent]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-- **Anti-ghost (dedicated-carrier root tamper).** A row whose after-digest carrier is NOT the advanced
accumulator (`before + step`) is rejected by `gQueueSysRootUpdate` — a dropped/forged `queues` update is
UNSAT at the dedicated carrier the wide commitment absorbs. -/
theorem queueSysRoot_rejects_wrong_root (env : VmRowEnv)
    (hwrong : env.loc sysRootsDigestCol
      ≠ env.loc sysRootsDigestColBefore + env.loc (prmCol QUEUE_ROOT_STEP_PARAM)) :
    ¬ (VmConstraint.gate gQueueSysRootUpdate).holdsVm env false false := by
  intro h; exact hwrong ((queueSysRoot_gate_faithful env).mp h)

/-! ## §3 — THE FULL-STATE RUNNABLE INSTANCE (the deliverable).

The declarative 17-field post for enqueue, over the per-cell `CellState` + the 8-root `system_roots`
sub-block. The per-cell legs (`CellEnqueueSpec`: deposit debit + queue-root cell advance + nonce tick +
frame freeze) are GATE-FORCED; the `system_roots` transition (the `QUEUE` root moves to `newQueueRoot`,
the other 7 frozen) is the decode-supplied structural fact — exactly as the transfer reference supplies
`postRoots = preRoots`. The WHOLE-state anti-ghost (§3½) then bites on all 17 fields via the generic
`runnable_full_commit_binds` (equal `NEW_COMMIT` + carrier-IS-digest ⇒ agree on every absorbed col AND
every root). -/

/-- **`QueueEnqueueFullClause p newRoot preRoots queueRootAfter`** — the full declarative post-state for
a queue enqueue over `(pre, post, postRoots)`: the per-cell `CellEnqueueSpec pre p newRoot post` AND the
`system_roots` sub-block moved ONLY at the `QUEUE` index
(`postRoots = Function.update preRoots QUEUE_ROOT_INDEX queueRootAfter`). NON-vacuous: §`enqueue_realizes`
inhabits it; §`enqueue_clause_not_trivial` refutes a forged post-state. -/
def QueueEnqueueFullClause (p : DepositParams) (newRoot : ℤ) (preRoots : SysRoots) (queueRootAfter : ℤ)
    (pre post : CellState) (postRoots : SysRoots) : Prop :=
  CellEnqueueSpec pre p newRoot post
  ∧ postRoots = Function.update preRoots QUEUE_ROOT_INDEX queueRootAfter

/-- **`queueEnqueueRunnableSpec` — THE FULL-STATE RUNNABLE INSTANCE.** The enqueue
`RunnableFullStateSpec`: `decodeAfter` is `RowEncodesEnqueue` (the structured per-cell column decode) PLUS
the `queues`-root structural transition; `decodeFull` projects the wide descriptor's per-row gates (=
enqueue's, a sublist) to the GATE-ONLY per-cell soundness (`queueEnqueueVm_faithful` ⟹
`intent_to_cellEnqueueSpec`), then carries the root transition. THIN — the only per-effect content is the
gate projection + the decode. NON-VACUOUS: `fullClause` is the genuine per-cell move + the precise queue
root advance, NOT `True`. -/
def queueEnqueueRunnableSpec (newRoot : ℤ) (p : DepositParams) (preRoots : SysRoots)
    (queueRootAfter : ℤ) : RunnableFullStateSpec CellState where
  descriptor    := queueEnqueueVmDescriptorWide newRoot
  usesWideSites := rfl
  isRow         := IsQueueEnqueueRow
  decodeAfter   := fun env pre post postRoots =>
    RowEncodesEnqueue env pre p newRoot post
      ∧ postRoots = Function.update preRoots QUEUE_ROOT_INDEX queueRootAfter
  fullClause    := QueueEnqueueFullClause p newRoot preRoots queueRootAfter
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots⟩ := hdec
    -- project the wide descriptor's per-row gates (flag-free `.gate`s) to the enqueue row gates.
    have hrowgates : ∀ c ∈ queueEnqueueRowGates newRoot, c.holdsVm env false false := by
      intro c hc
      have hh := hgates c (queueEnqueueWide_rowGates_sub newRoot c hc)
      -- the queue row gates are all `.gate _`, whose `holdsVm` ignores the boundary flags.
      unfold queueEnqueueRowGates gFieldPassNonRoot at hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hc
      rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
        simpa only [VmConstraint.holdsVm] using hh
    have hint := (queueEnqueueVm_faithful env newRoot).mp hrowgates
    exact ⟨intent_to_cellEnqueueSpec env pre post p newRoot henc hint, hroots⟩

/-! ## §3¼ — THE CROWN: a satisfying WIDE row pins the FULL 17-field enqueue post-state. -/

/-- **`queueEnqueue_runnable_full_sound` — THE DELIVERABLE.** A row satisfying the WIDE enqueue runnable
descriptor (`satisfiedVm`, first/last active), under the structured decode (per-cell `RowEncodesEnqueue`
+ the `queues`-root transition), pins the FULL 17-field declarative post-state `QueueEnqueueFullClause`:
the per-cell deposit-debit / queue-root-cell-advance / nonce-tick / frame-freeze (gate-forced) AND the
`system_roots` sub-block moved ONLY at the `QUEUE` index. The per-row gates give the move; the WIDE
hash-sites bind it (and the whole side-table digest) into the published `state_commit`. The analog of
the transfer reference, for the circuit the prover ACTUALLY RUNS — strengthening the per-cell
`queueEnqueueDescriptor_full_sound` to the WHOLE `system_roots` state. -/
theorem queueEnqueue_runnable_full_sound (hash : List ℤ → ℤ)
    (newRoot : ℤ) (p : DepositParams) (preRoots : SysRoots) (queueRootAfter : ℤ)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsQueueEnqueueRow env)
    (henc : RowEncodesEnqueue env pre p newRoot post)
    (hroots : postRoots = Function.update preRoots QUEUE_ROOT_INDEX queueRootAfter)
    (hsat : satisfiedVm hash (queueEnqueueVmDescriptorWide newRoot) env true true) :
    QueueEnqueueFullClause p newRoot preRoots queueRootAfter pre post postRoots :=
  runnable_full_sound (queueEnqueueRunnableSpec newRoot p preRoots queueRootAfter) hash env pre post
    postRoots hrow ⟨henc, hroots⟩ hsat

#assert_axioms queueEnqueue_runnable_full_sound

/-! ## §3½ — THE WHOLE-STATE ANTI-GHOST (all 17 fields, on the RUNNABLE descriptor).

Instantiating the generic `runnable_full_commit_binds`/`wide_rejects_*_tamper` at the enqueue spec: two
rows satisfying the WIDE enqueue descriptor that publish the SAME `NEW_COMMIT` (with `systemRootsDigest`
carriers) agree on EVERY absorbed state-block column AND every side-table root — so a prover CANNOT keep
`NEW_COMMIT` while tampering ANY of the 17 fields' bound content. -/

/-- **`queueEnqueue_full_commit_binds`** — two wide enqueue rows publishing the same `NEW_COMMIT`, whose
dedicated carriers ARE the `systemRootsDigest` of their post sub-blocks, agree on every absorbed
state-block column AND every side-table root (the queue root included). The runnable enqueue commitment
binds the whole post-state. -/
theorem queueEnqueue_full_commit_binds
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (newRoot : ℤ)
    (p : DepositParams) (preRoots : SysRoots) (queueRootAfter : ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash (queueEnqueueVmDescriptorWide newRoot) e₁ true true)
    (hsat₂ : satisfiedVm hash (queueEnqueueVmDescriptorWide newRoot) e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂) :
    absorbedCols e₁ = absorbedCols e₂ ∧ (∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i) :=
  runnable_full_commit_binds (queueEnqueueRunnableSpec newRoot p preRoots queueRootAfter)
    hash hCR e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂

/-- **Anti-ghost (queue side-table root tamper, on the RUNNABLE descriptor).** Two wide enqueue rows
publishing the same `NEW_COMMIT` (with `systemRootsDigest` carriers) whose `system_roots` sub-blocks
DIFFER at the `QUEUE` index (a dropped/forged FIFO append) cannot both satisfy. The queue side-table is
bound BY the runnable commitment. -/
theorem queueEnqueue_rejects_queue_root_tamper
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (newRoot : ℤ)
    (p : DepositParams) (preRoots : SysRoots) (queueRootAfter : ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash (queueEnqueueVmDescriptorWide newRoot) e₁ true true)
    (hsat₂ : satisfiedVm hash (queueEnqueueVmDescriptorWide newRoot) e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    (htamper : sr₁ QUEUE_ROOT_INDEX ≠ sr₂ QUEUE_ROOT_INDEX) : False :=
  wide_rejects_root_tamper (queueEnqueueRunnableSpec newRoot p preRoots queueRootAfter)
    hash hCR e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-- **Anti-ghost (per-cell state-block tamper, on the RUNNABLE descriptor).** Two wide enqueue rows
publishing the same `NEW_COMMIT` whose absorbed state-block columns DIFFER cannot both satisfy — a forged
balance / tampered field / forged cap-root that still claims the commitment is UNSAT. -/
theorem queueEnqueue_rejects_state_tamper
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (newRoot : ℤ)
    (p : DepositParams) (preRoots : SysRoots) (queueRootAfter : ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash (queueEnqueueVmDescriptorWide newRoot) e₁ true true)
    (hsat₂ : satisfiedVm hash (queueEnqueueVmDescriptorWide newRoot) e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    (htamper : absorbedCols e₁ ≠ absorbedCols e₂) : False :=
  wide_rejects_state_tamper (queueEnqueueRunnableSpec newRoot p preRoots queueRootAfter)
    hash hCR e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

#assert_axioms queueEnqueue_full_commit_binds
#assert_axioms queueEnqueue_rejects_queue_root_tamper
#assert_axioms queueEnqueue_rejects_state_tamper

/-! ## §4 — NON-VACUITY of the full clause (witness TRUE + a refuted forged post-state). -/

/-- A concrete pre `CellState` (balance 200, nonce 9, all fields/cap/reserved 0). -/
def goodPre : CellState where
  balLo := 200; balHi := 0; nonce := 9; fields := fun _ => 0; capRoot := 0; reserved := 0; commit := 0

/-- The genuine enqueue image of `goodPre` (deposit 12, advanced queue root 777): balance 188, nonce 10,
`fields 4 = 777`, the rest frozen. -/
def goodPost : CellState where
  balLo := 188; balHi := 0; nonce := 10
  fields := fun i => if i = (4 : Fin 8) then 777 else 0
  capRoot := 0; reserved := 0; commit := 0

/-- The enqueue params (deposit 12). -/
def goodParams : DepositParams := ⟨12⟩

/-- A frozen reference `system_roots` sub-block (the empty sub-block) + the advanced queue root. The post
sub-block updates ONLY the `QUEUE` index to a new digest value (here 777). -/
def goodPreRoots : SysRoots := emptySystemRoots

/-- **`enqueue_realizes` — NON-VACUITY (witness TRUE).** The enqueue `fullClause` is INHABITED by a real
enqueue: `goodPost` is the genuine `CellEnqueueSpec` image of `goodPre` (200 → 188, nonce 9 → 10,
`fields 4 → 777`, frame frozen) and the post sub-block advances ONLY the `QUEUE` root. So the framework's
`fullClause` is NOT `True` — it is a meaningful 17-field predicate a real enqueue satisfies, and it is
exactly the `fullClause` field of `queueEnqueueRunnableSpec`. -/
theorem enqueue_realizes :
    (queueEnqueueRunnableSpec 777 goodParams goodPreRoots 777).fullClause goodPre goodPost
      (Function.update goodPreRoots QUEUE_ROOT_INDEX 777) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · decide          -- balLo: 188 = 200 - 12
  · rfl             -- balHi frozen
  · decide          -- nonce: 10 = 9 + 1
  · simp [goodPost]   -- fields 4 = 777 (the `if (4:Fin 8) = 4` branch)
  · intro i hi              -- the 7 other field cells frozen (both 0)
    have hne : i ≠ (4 : Fin 8) := fun h => hi (by rw [h]; rfl)
    simp only [goodPost, goodPre, if_neg hne]
  · rfl             -- capRoot frozen
  · rfl             -- reserved frozen

/-- **`enqueue_clause_not_trivial` — the clause is REFUTABLE (witness FALSE).** A post-state whose `balLo`
is NOT the deposit-debited value (`goodPre.balLo = 200`, demanding `188`, but a forged `999`) FAILS
`QueueEnqueueFullClause` — so the instance's `fullClause` is not vacuously true (it rejects a forged
post-state), pinning non-vacuity from BOTH sides. -/
theorem enqueue_clause_not_trivial :
    ¬ QueueEnqueueFullClause goodParams 777 goodPreRoots 777 goodPre
        { goodPost with balLo := 999 } (Function.update goodPreRoots QUEUE_ROOT_INDEX 777) := by
  rintro ⟨⟨hbal, _⟩, _⟩
  -- hbal : (999) = goodPre.balLo - goodParams.deposit = 200 - 12 = 188
  simp only [goodPre, goodParams] at hbal
  norm_num at hbal

/-- **`enqueue_clause_rejects_root_drop` — the clause REJECTS a dropped queue-root advance (witness
FALSE).** A post sub-block that FREEZES the `QUEUE` root (leaves it at `preRoots`'s `0`) instead of
advancing it to `777` FAILS the structural transition conjunct of `QueueEnqueueFullClause` — the queue
side-table move is genuinely PART of the full clause (not laundered). -/
theorem enqueue_clause_rejects_root_drop :
    ¬ QueueEnqueueFullClause goodParams 777 goodPreRoots 777 goodPre goodPost goodPreRoots := by
  rintro ⟨_, hroots⟩
  -- hroots : goodPreRoots = Function.update goodPreRoots QUEUE_ROOT_INDEX 777
  have := congrFun hroots QUEUE_ROOT_INDEX
  simp only [goodPreRoots, emptySystemRoots, Function.update_self] at this
  exact absurd this (by norm_num)

#assert_axioms enqueue_realizes
#assert_axioms enqueue_clause_not_trivial
#assert_axioms enqueue_clause_rejects_root_drop
#assert_axioms queueSysRoot_gate_faithful
#assert_axioms queueSysRoot_rejects_wrong_root

/-! ## §5 — width/shape pins (the additive widening is exactly +1 gate, +2 columns, wide sites). -/

#guard (queueEnqueueVmDescriptorWide 0).traceWidth == 188
#guard (queueEnqueueVmDescriptorWide 0).hashSites.length == 4
#guard (queueEnqueueVmDescriptorWide 0).constraints.length
        == (queueEnqueueVmDescriptor 0).constraints.length + 1
#guard QUEUE_ROOT_INDEX.val == 1

end Dregg2.Circuit.Emit.EffectVmEmitQueueEnqueueFullState
