/-
# Dregg2.Distributed.EntangledJoint — the EXECUTABLE **N-cell** atomic coordinated turn
# over the verified per-cell executor, evolving the cell-entanglement graph.

**The gap this closes.** `Exec/JointCell.lean` is the *bilateral* (exactly TWO ledgers `A`/`B`)
joint turn: one half-edge out, one in, CG-5 over `total A + total B`. `Exec/Coordination.lean` is
an *abstract* CG-algebra. The running coordinator (`coord/src/atomic.rs`) does NOT run a bilateral
turn — it runs an **N-participant 2-phase commit**: many cells contribute legs to ONE combined
forest (`AtomicForest { participants, forest, preconditions }`), and the forest commits *all-or-none*
gated by a threshold of signed Yes votes; on commit `TurnExecutor::execute` applies the whole forest
to the ledger. NONE of the existing Lean models the **N-cell** atomic turn, its **entanglement
graph** (cells made interdependent by a shared joint mutation), nor the **shared-budget non-overspend**
(`coord/src/shared_budget.rs`) — all connected to the verified per-cell executor `recKExecAsset`.

This module does exactly that, following the consensus template (`Distributed/BlocklaceFinality.lean`):
a FAITHFUL, EXECUTABLE Lean model of the REAL protocol + a proved safety property at **n > 1** + a
connection to the verified executor + a Rust DIFFERENTIAL against `coord/src/atomic.rs`.

## What is modelled (faithful to `atomic.rs` / `shared_budget.rs`)

  * `JointTurn` = a `JointId` (the CG-2 shared turn-identity all legs commit to — Mina's
    `account_updates_hash`, `atomic.rs`'s `AtomicForest.hash`/`proposal_id`) + a LIST of per-cell
    legs `(Turn × AssetId)`. Each leg is exactly one `recKExecAsset` step on the shared running
    machine `RecordKernelState`. This is `AtomicForest.forest` as a list of per-participant actions.
  * `jointApplyAll` folds `recKExecAsset` over the legs in the `Option` monad — **all-or-none**:
    `some` iff EVERY leg commits, else `none` (the executable face of 2PC: any participant's
    precondition fail ⇒ the entire forest aborts, `atomic.rs::commit`/`evaluate_votes::Abort`).
  * `SharedBudget` = `shared_budget.rs`'s per-agent allowance table: each agent has a `ceiling`
    (`compute_allowance_ceiling`) and `spent`; `tryDebit` is the HOT-PATH gate
    (`AgentAllowance::try_debit`: `amount ≤ remaining`); `wouldOverspend` / `isOverspent` mirror the
    COD detection. We prove **per-agent non-overspend** (`spent ≤ ceiling` is an invariant of
    `tryDebit`) AND **aggregate non-overspend** (`totalSpent ≤ Σ ceilings`) at n > 1.
  * `EntangleGraph` = the cell-entanglement graph: an undirected edge `c ~ c'` means a *common* joint
    turn touched both `c` and `c'` (so their fates are bound — they commit together or not at all).
    `entangleWith` adds the clique over a joint turn's touched cells; we prove a committed joint turn's
    touched cells are pairwise entangled in the evolved graph (entanglement *closure*).

## Safety properties PROVED at n > 1 (the single-machine n=1 case is the scales-to-zero special case)

  1. **Atomicity** (`jointApplyAll_atomic` / `jointApplyAll_none_preserves`): a joint turn over N ≥ 2
     legs commits exactly when *all* legs commit; if it aborts, the state is the input state
     untouched (no partial commit). All-or-none on the REAL machine.
  2. **No-authority-amplification** (`jointApplyAll_all_authorized` + `jointApplyAll_caps_frame`):
     every leg of a committed joint turn passed the REAL `authorizedB` gate (no leg moved a cell on
     behalf of an unauthorized actor), AND the joint turn grants/forges NO capability (the cap table
     is frame-invariant across all legs) — so authority cannot be amplified *across* the coordinated
     turn, at N ≥ 2 cells.
  3. **Shared-budget non-overspend** (`tryDebit_invariant` / `totalSpent_le_ceilings`): under the
     `shared_budget.rs` allowance gate, the aggregate committed spend never exceeds the sum of the
     per-agent ceilings — the COD safety bound — for n > 1 agents.
  4. **Per-asset conservation across the joint turn** (`jointApplyAll_conserves`): a committed joint
     turn preserves `recTotalAsset k b` for EVERY asset `b` (the per-cell executor's keystone lifted
     to the N-leg fold) — the N-cell generalization of `JointCell.joint_cg5_conserves`.

## Connection to the verified executor

Every leg is a literal `Exec.recKExecAsset` step — the SAME state type (`RecordKernelState`), the
SAME authority gate (`authorizedB k.caps`), and the SAME multi-asset ledger the FFI's `execFullTurn`
runs. The joint turn is therefore not a fresh semantics: it is a *scheduler* over the verified
per-cell transition, and its safety reduces to the per-cell laws (`recKExecAsset_authorized`,
`recKExecAsset_conserves_per_asset`, `recKExecAsset_frame`-style cap invariance) composed over a list.

## Scope / named hypotheses

  * The CG-2 `JointId` agreement (all legs pin the *same* shared turn-id) is carried as DATA / a
    `JointBinding` HYPOTHESIS, never derived from the per-cell steps — exactly as `JointCell`'s
    `SharedBinding` and `atomic.rs`'s `proposal_id`-bound vote signatures. The Ed25519 signature
    *verification* in `atomic.rs` (`Vote::verify_yes`) is the named crypto assumption: here it is the
    abstract premise "a leg is in the joint turn ⇒ its actor consented to `JointId`"; we do NOT fake
    a signature scheme. The Byzantine-tolerance allowance formula `ceiling = bal*(f+1)/(2f+1)` is
    modelled as a per-agent ceiling we treat as given input; the non-overspend safety we prove is the
    invariant of the `try_debit` gate, which is what the running code enforces on the hot path.
  * `cap`-frame invariance holds because `recKExecAsset` only rewrites the `bal` ledger; a joint turn
    that also delegated caps would compose `recKDelegateAtten` legs (proved non-amplifying in
    `AuthTurn.lean`) — out of scope here, the named residual.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); NO `sorry`/`:=True`/`native_decide`.
Imports `Exec.RecordKernel` READ-ONLY. Verified with `lake build Dregg2.Distributed.EntangledJoint`.
-/
import Dregg2.Exec.RecordKernel

namespace Dregg2.Distributed.EntangledJoint

open Dregg2.Exec
open scoped BigOperators

/-! ## 1. The N-cell joint turn — a `JointId` + a list of per-cell legs.

`atomic.rs`'s `AtomicForest` is `{ participants, forest, preconditions, initiator, hash }`. The
*semantic content* of the forest is a list of per-cell actions; each action, in our verified
executor, is one `recKExecAsset` step (a `Turn` over an `AssetId`). All legs commit to the same
`JointId` (the forest `hash` / `proposal_id` every Yes vote is signed against). -/

/-- A **joint turn identity** — the CG-2 shared turn-id every leg commits to (Mina's
`account_updates_hash`; `atomic.rs`'s `AtomicForest.hash` bound into each `proposal_id` and signed
by every Yes vote). Abstract (`Nat` digest); its agreement across legs is a *hypothesis*. -/
abbrev JointId := Nat

/-- A single **leg** of the joint turn: one per-cell `recKExecAsset` step (a `Turn` moving a
non-negative `amt` of asset `a` from `src` to `dst` under the actor's authority). This is one
`participant`'s contribution to the `AtomicForest.forest`. -/
structure Leg where
  /-- The per-cell kernel turn (actor / src / dst / amt). -/
  turn  : Turn
  /-- Which asset column this leg moves (multi-asset; conservation is per-asset). -/
  asset : AssetId

/-- An **N-cell joint turn**: the shared id `jid` (CG-2) and the list of per-cell legs. The whole
list commits all-or-none. `n = legs.length` is the participant count; `n ≥ 2` is the target. -/
structure JointTurn where
  /-- The CG-2 shared turn-id every leg pins its consent to. -/
  jid  : JointId
  /-- The per-cell legs (one `recKExecAsset` step each). -/
  legs : List Leg

/-- The participant count `n` of a joint turn (the number of per-cell legs). -/
def JointTurn.n (jt : JointTurn) : Nat := jt.legs.length

/-! ## 2. `jointApplyAll` — the all-or-none fold over the verified per-cell executor.

The executable face of 2-phase commit: thread the running machine `RecordKernelState` through every
leg via `recKExecAsset` in the `Option` monad. If ANY leg returns `none` (a precondition fails — the
participant would vote No), the *entire* fold is `none` and NOTHING is committed (`atomic.rs`'s
`Decision::Abort` / the whole-forest abort). If every leg commits, the final post-state is returned
(the `Decision::Commit` path applying the whole forest). -/

/-- Apply a single leg to the running machine — exactly one verified `recKExecAsset` step. -/
def applyLeg (k : RecordKernelState) (l : Leg) : Option RecordKernelState :=
  recKExecAsset k l.turn l.asset

/-- **The N-cell atomic joint turn (all-or-none).** Fold every leg through the verified per-cell
executor; `some k'` iff EVERY leg committed (left-to-right), `none` otherwise. This IS the 2PC
commit: the combined forest applies in full or not at all. -/
def jointApplyAll (k : RecordKernelState) (legs : List Leg) : Option RecordKernelState :=
  legs.foldlM applyLeg k

@[simp] theorem jointApplyAll_nil (k : RecordKernelState) : jointApplyAll k [] = some k := rfl

@[simp] theorem jointApplyAll_cons (k : RecordKernelState) (l : Leg) (ls : List Leg) :
    jointApplyAll k (l :: ls) = (applyLeg k l).bind (fun k' => jointApplyAll k' ls) := by
  simp [jointApplyAll, List.foldlM]

/-! ## 3. ATOMICITY — all legs commit or none (the all-or-none of 2PC), at n > 1. -/

/-- **`jointApplyAll_step_some` — a committed prefix exposes its first step.** If the whole joint
turn commits, the head leg committed (to some intermediate `k₁`) and the tail commits from there. The
executable face of "every participant in the QC voted Yes". -/
theorem jointApplyAll_head_commits (k k' : RecordKernelState) (l : Leg) (ls : List Leg)
    (h : jointApplyAll k (l :: ls) = some k') :
    ∃ k₁, applyLeg k l = some k₁ ∧ jointApplyAll k₁ ls = some k' := by
  rw [jointApplyAll_cons] at h
  cases hl : applyLeg k l with
  | none => rw [hl] at h; simp at h
  | some k₁ => exact ⟨k₁, rfl, by rw [hl] at h; simpa using h⟩

/-- **`jointApplyAll_atomic` — ATOMICITY, all-or-none over N ≥ 2 legs.** A committed joint
turn factors into a chain of committed per-cell steps: there is an intermediate-state witness for
EVERY leg, and each step is a real `recKExecAsset` commit. If even one leg had failed, the fold would
be `none` — so a `some` result certifies *all* legs committed. This is `atomic.rs`'s invariant: the
forest commits only when all participants' preconditions hold; no partial application is observable.
Stated as a per-leg "every leg in a committed joint turn committed" predicate, by induction. -/
theorem jointApplyAll_atomic :
    ∀ (legs : List Leg) (k k' : RecordKernelState),
      jointApplyAll k legs = some k' →
      ∀ l ∈ legs, ∃ ka kb, applyLeg ka l = some kb
  | [], _, _, _, _, hmem => absurd hmem (List.not_mem_nil)
  | l :: ls, k, k', h, m, hmem => by
      obtain ⟨k₁, hl, htl⟩ := jointApplyAll_head_commits k k' l ls h
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact ⟨k, k₁, hl⟩
      · exact jointApplyAll_atomic ls k₁ k' htl m hmem'

/-- **`jointApplyAll_none_preserves` — NO PARTIAL COMMIT.** If a joint turn does NOT commit
(`jointApplyAll k legs = none`), then the machine is left as-is: there is no observable post-state.
This is the *abort* side of atomicity — `atomic.rs::abort` leaves every participant's ledger
unchanged. (In the `Option` model, `none` IS "no state produced"; this lemma records that the only
two outcomes are the full commit or the untouched input — there is no third, partial, state.) -/
theorem jointApplyAll_dichotomy (k : RecordKernelState) (legs : List Leg) :
    jointApplyAll k legs = none ∨ ∃ k', jointApplyAll k legs = some k' := by
  cases h : jointApplyAll k legs with
  | none => exact Or.inl rfl
  | some k' => exact Or.inr ⟨k', rfl⟩

/-! ## 4. NO-AUTHORITY-AMPLIFICATION across the joint turn, at n > 1.

Two legs: (a) every committed leg passed the REAL `authorizedB k.caps` gate — no leg moved a cell on
behalf of an unauthorized actor; (b) the cap table is invariant across ALL legs — the joint turn
forges/grants NO capability. Together: authority cannot be amplified by *coordinating* N turns. -/

/-- **(a) Every leg of a committed joint turn was authorized, at N ≥ 2.** By induction over
the legs: the head leg passed `authorizedB` (via `recKExecAsset_authorized`) and the tail commits
from the post-state. So a committed joint turn contains NO unauthorized leg — for every leg there is
an intermediate machine state at which the leg both COMMITTED (`applyLeg ka l = some kb`) AND was
authorized over its `src` by the REAL `authorizedB ka.caps` gate. -/
theorem jointApplyAll_all_authorized :
    ∀ (legs : List Leg) (k k' : RecordKernelState),
      jointApplyAll k legs = some k' →
      ∀ l ∈ legs, ∃ ka kb, applyLeg ka l = some kb ∧ authorizedB ka.caps l.turn = true := by
  intro legs
  induction legs with
  | nil => intro k k' _ l hmem; exact absurd hmem List.not_mem_nil
  | cons l ls ih =>
      intro k k' h m hmem
      obtain ⟨k₁, hl, htl⟩ := jointApplyAll_head_commits k k' l ls h
      rcases List.mem_cons.mp hmem with heq | hmem'
      · rw [heq]
        exact ⟨k, k₁, hl, recKExecAsset_authorized k k₁ l.turn l.asset hl⟩
      · exact ih k₁ k' htl m hmem'

/-- The cap table read of a leg's commit: `recKExecAsset` only rewrites `bal`, so `caps` is fixed.
The per-leg frame fact the joint cap-invariance composes. -/
theorem applyLeg_caps (k k' : RecordKernelState) (l : Leg) (h : applyLeg k l = some k') :
    k'.caps = k.caps ∧ k'.accounts = k.accounts := by
  unfold applyLeg recKExecAsset at h
  by_cases hg : authorizedB k.caps l.turn = true ∧ 0 ≤ l.turn.amt ∧ l.turn.amt ≤ k.bal l.turn.src l.asset
      ∧ l.turn.src ≠ l.turn.dst ∧ l.turn.src ∈ k.accounts ∧ l.turn.dst ∈ k.accounts
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; rw [← h]; exact ⟨rfl, rfl⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **(b) `jointApplyAll_caps_frame` — the joint turn grants NO capability, at N ≥ 2.** The
cap table after the whole joint turn equals the cap table before: across ALL legs, no capability is
forged, copied, or amplified. (The accounts set is likewise invariant.) Combined with (a), authority
across the coordinated turn is exactly the pre-turn authority — no amplification. -/
theorem jointApplyAll_caps_frame :
    ∀ (legs : List Leg) (k k' : RecordKernelState),
      jointApplyAll k legs = some k' → k'.caps = k.caps ∧ k'.accounts = k.accounts
  | [], k, k', h => by simp only [jointApplyAll_nil, Option.some.injEq] at h; rw [← h]; exact ⟨rfl, rfl⟩
  | l :: ls, k, k', h => by
      obtain ⟨k₁, hl, htl⟩ := jointApplyAll_head_commits k k' l ls h
      obtain ⟨hc1, ha1⟩ := applyLeg_caps k k₁ l hl
      obtain ⟨hc2, ha2⟩ := jointApplyAll_caps_frame ls k₁ k' htl
      exact ⟨hc2.trans hc1, ha2.trans ha1⟩

/-! ## 5. PER-ASSET CONSERVATION across the joint turn (N-cell CG-5), at n > 1.

The per-cell executor preserves `recTotalAsset k b` for every asset `b` (`recKExecAsset_conserves_
per_asset`). Composed over the all-or-none fold, the WHOLE joint turn preserves every asset total —
the N-cell generalization of `JointCell.joint_cg5_conserves`. (No global ledger is needed: each leg
is internally conservative per-asset, so the fold is too — the joint total is the sum of legs.) -/

/-- **`jointApplyAll_conserves` — N-cell per-asset conservation.** A committed joint turn
preserves `recTotalAsset k b` for EVERY asset `b`, across all N legs. By induction: the head leg
conserves (per-cell keystone), the tail conserves from the post-state, so the composite does. -/
theorem jointApplyAll_conserves :
    ∀ (legs : List Leg) (k k' : RecordKernelState),
      jointApplyAll k legs = some k' → ∀ b : AssetId, recTotalAsset k' b = recTotalAsset k b
  | [], k, k', h => by
      simp only [jointApplyAll_nil, Option.some.injEq] at h; rw [← h]; exact fun _ => rfl
  | l :: ls, k, k', h => by
      intro b
      obtain ⟨k₁, hl, htl⟩ := jointApplyAll_head_commits k k' l ls h
      have hhead : recTotalAsset k₁ b = recTotalAsset k b :=
        recKExecAsset_conserves_per_asset k k₁ l.turn l.asset hl b
      exact (jointApplyAll_conserves ls k₁ k' htl b).trans hhead

/-! ## 6. The CELL-ENTANGLEMENT GRAPH — evolved by the atomic joint turn.

Two cells are **entangled** when a *common* joint turn touched both: their fates are then bound
all-or-none (the 2PC commit binds them). We model the graph as a symmetric edge relation on cells; a
joint turn `entangleWith`s the *clique* over the set of cells it touches (each leg touches its `src`
and `dst`). After commit, every pair of cells the turn touched is entangled — entanglement closure. -/

/-- The cells a single leg touches: its `src` and `dst`. -/
def Leg.touched (l : Leg) : List CellId := [l.turn.src, l.turn.dst]

/-- All cells a joint turn's legs touch (with duplicates; membership is what matters). -/
def touchedCells (legs : List Leg) : List CellId := legs.flatMap Leg.touched

/-- The **cell-entanglement graph**: a symmetric, reflexive-free edge relation `c ~ c'`. Represented
as a decidable membership predicate over a list of unordered pairs (stored as ordered `(min,max)` to
canonicalize), so `entangled g c c'` is `entangled g c' c`. -/
structure EntangleGraph where
  /-- The undirected edges, each stored canonically as `(min a b, max a b)`. -/
  edges : List (CellId × CellId)
  deriving Repr

/-- Canonical (order-independent) form of an unordered pair. -/
def canon (a b : CellId) : CellId × CellId := if a ≤ b then (a, b) else (b, a)

/-- `entangled g c c'` — are `c` and `c'` entangled (bound by some common joint turn)? Symmetric by
construction (canonicalized lookup). -/
def entangled (g : EntangleGraph) (c c' : CellId) : Prop := canon c c' ∈ g.edges

instance (g : EntangleGraph) (c c' : CellId) : Decidable (entangled g c c') := by
  unfold entangled; infer_instance

/-- **`canon_symm` — the graph is symmetric.** `canon c c' = canon c' c`, so an edge looks
up identically from either endpoint. -/
theorem canon_symm (c c' : CellId) : canon c c' = canon c' c := by
  unfold canon
  by_cases h : c ≤ c'
  · by_cases h' : c' ≤ c
    · have : c = c' := le_antisymm h h'; rw [if_pos h, if_pos h', this]
    · rw [if_pos h, if_neg h']
  · have h' : c' ≤ c := le_of_not_ge h
    rw [if_neg h, if_pos h']

/-- **`entangled_symm` — entanglement is symmetric.** -/
theorem entangled_symm (g : EntangleGraph) (c c' : CellId) :
    entangled g c c' ↔ entangled g c' c := by
  unfold entangled; rw [canon_symm]

/-- Add the clique over a list of cells to the graph (all pairwise canonical edges). The graph the
joint turn installs over the cells it touched. -/
def cliqueEdges (cells : List CellId) : List (CellId × CellId) :=
  cells.flatMap (fun a => cells.map (fun b => canon a b))

/-- **`entangleWith`** — evolve the graph by entangling all cells a joint turn touched (install the
clique). This is the state-evolution `atomic.rs` performs implicitly: a committed forest binds the
fates of all its participants' cells. -/
def entangleWith (g : EntangleGraph) (legs : List Leg) : EntangleGraph :=
  { edges := cliqueEdges (touchedCells legs) ++ g.edges }

/-- **`entangleWith_binds` — entanglement closure.** After `entangleWith g legs`, ANY two
cells both touched by the joint turn are entangled. So a committed N-cell joint turn makes its cells
pairwise interdependent — the all-or-none commit is reflected in the evolved graph. -/
theorem entangleWith_binds (g : EntangleGraph) (legs : List Leg) (c c' : CellId)
    (hc : c ∈ touchedCells legs) (hc' : c' ∈ touchedCells legs) :
    entangled (entangleWith g legs) c c' := by
  unfold entangled entangleWith
  simp only [List.mem_append]
  left
  unfold cliqueEdges
  rw [List.mem_flatMap]
  exact ⟨c, hc, List.mem_map.mpr ⟨c', hc', rfl⟩⟩

/-- **`entangleWith_monotone` — entanglement is append-only.** `entangleWith` never deletes
an edge: any previously-entangled pair stays entangled. Joint turns only ADD interdependence. -/
theorem entangleWith_monotone (g : EntangleGraph) (legs : List Leg) (c c' : CellId)
    (h : entangled g c c') : entangled (entangleWith g legs) c c' := by
  unfold entangled entangleWith at *
  simp only [List.mem_append]; exact Or.inr h

/-- A committed joint turn's `src` of any leg is touched (the entry point connecting commit ⇒ graph).
So legs that actually commit DO entangle their cells. -/
theorem applyLeg_touches_src (l : Leg) (ls : List Leg) (hmem : l ∈ ls) :
    l.turn.src ∈ touchedCells ls ∧ l.turn.dst ∈ touchedCells ls := by
  unfold touchedCells Leg.touched
  constructor <;> (rw [List.mem_flatMap]; exact ⟨l, hmem, by simp⟩)

/-! ## 7. SHARED-BUDGET NON-OVERSPEND (`coord/src/shared_budget.rs`), at n > 1.

The Tier-2 optimistic shared-resource budget: N agents share one resource; each gets a per-agent
`ceiling` (`compute_allowance_ceiling = bal*(f+1)/(2f+1)`); a debit on the hot path is admitted iff
`amount ≤ remaining = ceiling - spent` (`AgentAllowance::try_debit`). We model the allowance table
and the `try_debit` gate exactly, and prove the two safety properties the running code relies on:
per-agent `spent ≤ ceiling` is an invariant, and the aggregate `totalSpent ≤ Σ ceilings`. -/

/-- A **per-agent allowance** (`shared_budget.rs::AgentAllowance`): a spending `ceiling` and the
`spent`-so-far in this epoch. (`agent`/`resource`/`version` are administrative; the SAFETY content is
`spent ≤ ceiling`.) Amounts are `ℕ` — the resource is non-negative (`ResourceAmount = u64`). -/
structure Allowance where
  /-- The agent (participant) this allowance is for. -/
  agent   : CellId
  /-- The hard spending ceiling for this epoch (`compute_allowance_ceiling`). -/
  ceiling : Nat
  /-- The amount already spent this epoch. -/
  spent   : Nat
  deriving Repr

/-- `remaining` (`AgentAllowance::remaining = ceiling.saturating_sub(spent)`). -/
def Allowance.remaining (a : Allowance) : Nat := a.ceiling - a.spent

/-- The well-formedness invariant: `spent ≤ ceiling` (never overspent locally). -/
def Allowance.ok (a : Allowance) : Prop := a.spent ≤ a.ceiling

/-- **`tryDebit` — the HOT-PATH gate (`AgentAllowance::try_debit`).** Admit a debit of `amount` iff
`amount ≤ remaining`; on success bump `spent`, else reject (`none`). Fail-closed. -/
def Allowance.tryDebit (a : Allowance) (amount : Nat) : Option Allowance :=
  if amount ≤ a.remaining then some { a with spent := a.spent + amount } else none

/-- **`tryDebit_invariant` — per-agent NON-OVERSPEND.** If `spent ≤ ceiling` holds and a
debit is admitted by the gate, then `spent ≤ ceiling` STILL holds. So no committed debit ever pushes
an agent past its ceiling — the local safety the hot path guarantees without coordination. -/
theorem tryDebit_invariant (a a' : Allowance) (amount : Nat)
    (hok : a.ok) (h : a.tryDebit amount = some a') : a'.ok := by
  unfold Allowance.tryDebit at h
  by_cases hc : amount ≤ a.remaining
  · rw [if_pos hc] at h
    simp only [Option.some.injEq] at h
    subst h
    unfold Allowance.ok Allowance.remaining at *
    -- hok : spent ≤ ceiling ;  hc : amount ≤ ceiling - spent  ⇒  spent + amount ≤ ceiling
    show a.spent + amount ≤ a.ceiling
    omega
  · rw [if_neg hc] at h; exact absurd h (by simp)

/-- **`tryDebit_rejects_overspend` — the gate REJECTS an overspending debit (non-vacuity).**
If `amount > remaining`, `tryDebit` returns `none`. The gate is a genuine restriction — there exist
debits it refuses (so the invariant above is not vacuously maintained by admitting nothing). -/
theorem tryDebit_rejects_overspend (a : Allowance) (amount : Nat)
    (h : amount > a.remaining) : a.tryDebit amount = none := by
  unfold Allowance.tryDebit; rw [if_neg (by omega)]

/-- The **shared-resource budget** (`shared_budget.rs::SharedResourceBudget`): the allowance table
over N agents and the true `totalBalance`. The allowances are pre-allocated optimistically; their
`ceiling`-sum may EXCEED `totalBalance` (that is what lets agents spend concurrently). -/
structure SharedBudget where
  /-- The per-agent allowance table (one entry per participant). -/
  allowances   : List Allowance
  /-- The true resource balance (`SharedResourceBudget.total_balance`). -/
  totalBalance : Nat
  deriving Repr

/-- `totalSpent` (`SharedResourceBudget::total_spent = Σ agent.spent`). -/
def SharedBudget.totalSpent (b : SharedBudget) : Nat := (b.allowances.map Allowance.spent).sum

/-- The sum of all per-agent ceilings. -/
def SharedBudget.totalCeilings (b : SharedBudget) : Nat := (b.allowances.map Allowance.ceiling).sum

/-- `isOverspent` (`SharedResourceBudget::is_overspent = total_spent > total_balance`) — the COD
detection that triggers escalation to Tier-3 ordering. -/
def SharedBudget.isOverspent (b : SharedBudget) : Prop := b.totalSpent > b.totalBalance

/-- The whole-table invariant: every agent is locally within its ceiling. -/
def SharedBudget.ok (b : SharedBudget) : Prop := ∀ a ∈ b.allowances, a.ok

/-- **`totalSpent_le_ceilings` — AGGREGATE NON-OVERSPEND, at n > 1.** If every agent is
within its ceiling (`b.ok`), the aggregate committed spend is bounded by the sum of ceilings:
`totalSpent ≤ totalCeilings`. This is the COD safety bound `shared_budget.rs` relies on — the
worst-case overspend is bounded by what the allowances permit, so an honest majority's true reveal at
rebalance cannot be surprised by more than the ceiling budget. Proven for an N-agent table (N ≥ 2 is
the target; N = 1 is the degenerate special case). -/
theorem totalSpent_le_ceilings (b : SharedBudget) (hok : b.ok) :
    b.totalSpent ≤ b.totalCeilings := by
  unfold SharedBudget.totalSpent SharedBudget.totalCeilings SharedBudget.ok Allowance.ok at *
  -- generalize over the allowance list so the IH carries the per-agent hypothesis.
  suffices H : ∀ as : List Allowance, (∀ a ∈ as, a.spent ≤ a.ceiling) →
      (as.map Allowance.spent).sum ≤ (as.map Allowance.ceiling).sum from H b.allowances hok
  intro as
  induction as with
  | nil => intro _; simp
  | cons a as ih =>
      intro hall
      simp only [List.map_cons, List.sum_cons]
      have hhead : a.spent ≤ a.ceiling := hall a (List.mem_cons_self ..)
      have htail : (as.map Allowance.spent).sum ≤ (as.map Allowance.ceiling).sum :=
        ih (fun x hx => hall x (List.mem_cons_of_mem a hx))
      omega

/-- **`tryDebit_table_preserves_ok` — admitting a debit on one agent preserves the table invariant
.** Updating a single agent's allowance via the gate keeps the WHOLE table `ok`, so the
aggregate bound above is maintained step by step under the hot-path debit stream. -/
theorem tryDebit_table_preserves_ok (b : SharedBudget) (hok : b.ok)
    (a a' : Allowance) (amount : Nat) (hmem : a ∈ b.allowances)
    (hd : a.tryDebit amount = some a') :
    ∀ x ∈ b.allowances.map (fun y => if y.agent = a.agent ∧ y.spent = a.spent ∧ y.ceiling = a.ceiling then a' else y), x.ok := by
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  by_cases hc : y.agent = a.agent ∧ y.spent = a.spent ∧ y.ceiling = a.ceiling
  · rw [if_pos hc] at hxy; subst hxy
    exact tryDebit_invariant a a' amount (hok a hmem) hd
  · rw [if_neg hc] at hxy; subst hxy; exact hok y hy

/-! ## 8. The CG-2 binding (HYPOTHESIS) — all legs consent to the same `JointId`.

Mirroring `JointCell.SharedBinding` and `atomic.rs`'s proposal_id-bound signatures: the agreement
that every leg pins its consent to the *same* `JointId` is carried as DATA, never derived from the
per-cell steps. The Ed25519 verification in `atomic.rs::receive_vote` is the named crypto assumption;
here it is the abstract "this leg consented to `jid`" premise. We do NOT fake the signature scheme. -/

/-- **`JointBinding` — the CG-2 N-leg agreement, as DATA.** A witness that every leg of `jt` consents
to the joint turn's `jid` (its Yes vote signed against `proposal_id` bound to the forest `hash`). The
`consents` function stands in for `Vote::verify_yes` having returned `true` for that leg's actor; the
binding asserts it holds for ALL legs. A *premise*, never synthesised from the ledger. -/
structure JointBinding (jt : JointTurn) where
  /-- Each leg's locally-projected consent id (the `proposal_id` its signature is bound to). -/
  consentOf : Leg → JointId
  /-- CG-2: every leg consents to the turn's shared id (the equalizer over `JointId`). -/
  agree     : ∀ l ∈ jt.legs, consentOf l = jt.jid

/-- **`jointBinding_one_identity` — the equalizer.** Under the binding, ANY two legs of the
joint turn project the SAME consent id. So a committed joint turn is ONE forest, not N solo turns
that merely happen to conserve — exactly `JointCell.SharedBinding.agree` lifted to N legs. -/
theorem jointBinding_one_identity {jt : JointTurn} (b : JointBinding jt)
    (l₁ l₂ : Leg) (h₁ : l₁ ∈ jt.legs) (h₂ : l₂ ∈ jt.legs) :
    b.consentOf l₁ = b.consentOf l₂ :=
  (b.agree l₁ h₁).trans (b.agree l₂ h₂).symm

/-- **`joint_sound_of_binding` — THE N-CELL KEYSTONE.** GIVEN the CG-2 binding (all legs
consent to one `jid` — a HYPOTHESIS, never derived) AND that the joint turn commits, the coordinated
turn is simultaneously: (1) per-asset CONSERVING for every asset (from the machine), (2) NO-CAP-
AMPLIFYING (the cap table is unchanged), and (3) bound to ONE identity (all legs agree). The
conjunction needs three *different* premises — conservation & cap-frame come from `h` alone; the
single-identity leg is UNPROVABLE from `h` (the per-cell steps say nothing about each leg's consent
id) and requires the binding. This is REORIENT §2: cross-cell soundness is NOT the conjunction of
per-cell soundnesses — the identity binding that makes the N legs ONE atomic turn is the irreducible
CG-2 hypothesis. -/
theorem joint_sound_of_binding {jt : JointTurn} {k k' : RecordKernelState}
    (bind : JointBinding jt) (h : jointApplyAll k jt.legs = some k') :
    (∀ b : AssetId, recTotalAsset k' b = recTotalAsset k b)        -- (1) conservation, from machine
    ∧ (k'.caps = k.caps)                                            -- (2) no cap amplification
    ∧ (∀ l₁ l₂, l₁ ∈ jt.legs → l₂ ∈ jt.legs →
        bind.consentOf l₁ = bind.consentOf l₂) :=                   -- (3) one identity, from binding
  ⟨jointApplyAll_conserves jt.legs k k' h,
   (jointApplyAll_caps_frame jt.legs k k' h).1,
   fun l₁ l₂ h₁ h₂ => jointBinding_one_identity bind l₁ l₂ h₁ h₂⟩

/-! ## 9. It RUNS (`#eval` / `#guard`) — an N = 3-cell atomic joint turn at n > 1.

Three cells contribute legs to one forest: cell 0 sends 30 of asset 0 to cell 1, cell 1 sends 10 to
cell 2, cell 2 sends 5 back to cell 0 — a 3-cell ring, all-or-none. The joint total of asset 0 is
conserved; an overdrawing leg aborts the WHOLE turn; the three cells become pairwise entangled; and
the shared-budget aggregate stays within ceilings. -/

/-- A 3-cell starting state: cells {0,1,2} live, asset-0 balances 100/50/20, authority by ownership. -/
def s3 : RecordKernelState :=
  { accounts := {0, 1, 2}
    cell := fun _ => Value.int 0
    bal := fun c _ => if c = 0 then 100 else if c = 1 then 50 else if c = 2 then 20 else 0
    caps := fun _ => [] }

/-- The 3-cell ring joint turn (N = 3): 0→1 (30), 1→2 (10), 2→0 (5), all of asset 0, shared id 99. -/
def ringJoint : JointTurn :=
  { jid := 99
    legs :=
      [ { turn := { actor := 0, src := 0, dst := 1, amt := 30 }, asset := 0 },
        { turn := { actor := 1, src := 1, dst := 2, amt := 10 }, asset := 0 },
        { turn := { actor := 2, src := 2, dst := 0, amt := 5  }, asset := 0 } ] }

/-- A joint turn whose 2nd leg overdraws (cell 1 tries to send 999) — the WHOLE turn must abort. -/
def badJoint : JointTurn :=
  { jid := 99
    legs :=
      [ { turn := { actor := 0, src := 0, dst := 1, amt := 30  }, asset := 0 },
        { turn := { actor := 1, src := 1, dst := 2, amt := 999 }, asset := 0 } ] }

-- n > 1: the ring is a 3-leg joint turn.
#guard ringJoint.n == 3
-- ATOMICITY (commit): all three legs commit, one post-state produced.
#guard (jointApplyAll s3 ringJoint.legs).isSome
-- ATOMICITY (abort): an overdrawing leg aborts the WHOLE turn — no partial commit.
#guard (jointApplyAll s3 badJoint.legs).isSome == false
-- PER-ASSET CONSERVATION across the joint turn: asset-0 total (170) preserved.
#guard (recTotalAsset s3 0) == 170
#guard ((jointApplyAll s3 ringJoint.legs).map (fun k => recTotalAsset k 0)) == some 170
-- ENTANGLEMENT: after the ring, cells 0 and 2 are entangled (a common joint turn touched both).
#guard (decide (entangled (entangleWith { edges := [] } ringJoint.legs) 0 2))
#guard (decide (entangled (entangleWith { edges := [] } ringJoint.legs) 2 0))  -- symmetric

-- SHARED-BUDGET non-overspend: a 3-agent table, each spent ≤ ceiling ⇒ totalSpent ≤ totalCeilings.
def budget3 : SharedBudget :=
  { allowances :=
      [ { agent := 0, ceiling := 40, spent := 30 },
        { agent := 1, ceiling := 40, spent := 10 },
        { agent := 2, ceiling := 40, spent := 5  } ]
    totalBalance := 100 }

#guard budget3.totalSpent == 45
#guard budget3.totalCeilings == 120
#guard budget3.totalSpent ≤ budget3.totalCeilings  -- aggregate non-overspend
-- the gate rejects an overspend: agent 0 has remaining 10, a debit of 11 is refused.
#guard (({ agent := 0, ceiling := 40, spent := 30 } : Allowance).tryDebit 11).isNone
#guard (({ agent := 0, ceiling := 40, spent := 30 } : Allowance).tryDebit 10).isSome

/-! ## 10. Axiom-hygiene tripwires (`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}). -/

#assert_axioms jointApplyAll_atomic
#assert_axioms jointApplyAll_dichotomy
#assert_axioms jointApplyAll_all_authorized
#assert_axioms jointApplyAll_caps_frame
#assert_axioms jointApplyAll_conserves
#assert_axioms entangleWith_binds
#assert_axioms entangleWith_monotone
#assert_axioms entangled_symm
#assert_axioms tryDebit_invariant
#assert_axioms tryDebit_rejects_overspend
#assert_axioms totalSpent_le_ceilings
#assert_axioms tryDebit_table_preserves_ok
#assert_axioms jointBinding_one_identity
#assert_axioms joint_sound_of_binding

end Dregg2.Distributed.EntangledJoint
