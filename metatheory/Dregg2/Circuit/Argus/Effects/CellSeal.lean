/-
# Dregg2.Circuit.Argus.Effects.CellSeal — the cell LIFECYCLE-SEAL effect `cellSealA` (Live → Sealed)
welded into the Argus IR, as a FULL-STATE `Surface2` weld.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated it
on transfer/mint/burn/createEscrow. `Effects/BalanceA.lean` then welded a per-component effect to its
genuine standalone v2 `Surface2` descriptor (`balanceA_full_sound`), concluding the WHOLE 17-field
post-state. This module follows that STRONGER `BalanceA` surface for the different LIFECYCLE
primitive `cellSealA`, in a disjoint file (it imports the Argus IR + the audited `cellSealA` v2 instance +
the independent lifecycle spec, all read-only, and owns only its own declarations).

`cellSealA` is the Live→Sealed cell-lifecycle transition (`apply_cell_seal` → `Cell::seal`,
`apply.rs:4218`/`cell.rs:528`). The verified chained transition is `cellSealChainA`
(`TurnExecutorFull.lean:1654`), and `execFullA s (.cellSealA actor cell) = cellSealChainA s actor cell`
(`TurnExecutorFull.lean:3894`):

    cellSealChainA s actor cell
      = if stateAuthB s.kernel.caps actor cell = true ∧ acceptsEffects s.kernel cell = true then
          some { kernel := setLifecycle s.kernel cell lcSealed,
                 log    := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }
        else none

so a committed seal (i) FLIPS the `lifecycle` discriminant of `cell` to `lcSealed` (= `1`) via
`setLifecycle` (every other cell + every other RecordKernelState field FROZEN — it is balance-NEUTRAL,
`setLifecycle_balNeutral`), AND (ii) PREPENDS one self-targeted receipt row onto the chain log. The
admissibility gate is `stateAuthB` (self-authority over `cell`, the dregg1 `target == action_target`
self-lifecycle gate) AND `acceptsEffects` (only a LIVE cell may seal). Because the body touches the
`lifecycle` side-table, the IR move is the §A `setLifecycle` component-write primitive — NOT `setCell`
(transfer's) nor `setBal` (balanceA's). That is the structural contrast.

## THE KERNEL-vs-RUNTIME DIVERGENCE (carried explicitly — read this).

The Argus `interp` is a `RecordKernelState → Option RecordKernelState` transformer; `cellSealChainA` is a
`RecChainedState → Option RecChainedState` step — it ALSO prepends a receipt row to the `log`, and the
`log` lives in `RecChainedState`, NOT in `RecordKernelState`. So the IR term's `interp` cannot — and does
not — emit the log row; it captures EXACTLY the KERNEL side of the chained step (the `setLifecycle` flip).
This is the SAME chained-vs-raw boundary `BalanceA` carries (its `interp` is on the raw kernel; the chained
`execFullA` adds an `acceptsEffects` pre-gate + a log prepend), here named precisely:

  * `interp (cellSealStmt actor cell) k` produces the KERNEL post-state `setLifecycle k cell lcSealed`,
    gated on EXACTLY `cellSealChainA`'s two-conjunct guard read on `k` (`interp_cellSealStmt_eq_kernel`).
  * lifting to the chained `execFullA` (`interp_cellSealStmt_chained`) re-attaches the runtime receipt row
    `cellLifecycleReceipt actor cell :: s.log` — the runtime layer the kernel `interp` does not model. The
    welded conclusion (§4) then names the chained post-state `{ kernel := k', log := receipt :: s.log }`
    EXPLICITLY, so the receipt-log obligation is part of the welded statement (not papered).

## THE DESCRIPTOR — a GENUINE full-state v2 `Surface2`, NOT EffectVM-inherited.

`cellSealA` carries its OWN standalone v2 `EffectCommit2`/`Surface2` descriptor + full soundness
(`Dregg2/Circuit/Inst/cellSealA.lean`): `cellSealE` (the `EffectSpec2` whose touched component is the WHOLE
`lifecycle : CellId → Nat` function, a `funcComponent` full-function digest) and
`cellSealA_full_sound : satisfiedE2 … (cellSealE D hD) … ⟹ CellSealSpec` — a FULL 17-field declarative
post-state soundness (`Spec/celllifecycle.lean`'s `CellSealSpec`: lifecycle flips, the log grows by one
receipt, every OTHER kernel field frozen), keyed on the CHAINED executor `cellSealChainA`/`execFullA` via
the INDEPENDENT `cellSeal_iff_spec` (executor ⟺ spec, BOTH directions). This is the strictly-stronger
`BalanceA` surface (whole-state full-function digest), not the per-cell EffectVM/`cellProj` surface
transfer/delegate live on.

## Axiom hygiene

`#assert_axioms` on every headline theorem ⊆ {propext, Classical.choice, Quot.sound}; the
whole-function-digest assumption enters ONLY inside the reused `cellSealA_full_sound` (its
`Function.Injective D` hypothesis + the Poseidon-CR `RestIffNoLifecycle`/`logHashInjective` portals), not in
the welded conclusion's statement. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only; this
file owns only itself.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Inst.cellSealA
import Dregg2.Circuit.Spec.celllifecycle
import Dregg2.Circuit.Emit.EffectVmEmitCellSealFullState

namespace Dregg2.Circuit.Argus.Effects.CellSeal

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
-- `stateAuthB` (the self-lifecycle authority gate) lives in `Dregg2.Exec.EffectsState`; `acceptsEffects` is
-- in `TurnExecutorFull` (opened above). `Cap` (for the `Cap.node` cap literals in the §5 fixtures) lives in
-- `Dregg2.Authority`. (`open` is not transitive, so these are named even though the Inst/Spec deps use them.)
open Dregg2.Exec.EffectsState (stateAuthB)
open Dregg2.Authority (Cap)
open Dregg2.Circuit.Argus (RecStmt interp)
-- Broad opens mirroring `Inst/cellSealA.lean` so the standalone-descriptor names resolve unqualified:
-- `logHashInjective` lives in `StateCommit`; `Surface2`/`satisfiedE2`/`encodeE2` in `EffectCommit2`.
open Dregg2.Circuit.StateCommit (logHashInjective)
open Dregg2.Circuit.EffectCommit2 (Surface2 satisfiedE2 encodeE2)
open Dregg2.Circuit.Spec.CellLifecycle
  (CellSealGuard CellSealSpec sealLifecycleMap cellLifecycleReceipt cellSeal_iff_spec)
open Dregg2.Circuit.Inst.CellSealA (CellSealArgs cellSealE cellSealA_full_sound RestIffNoLifecycle)

/-! ## §1 — The cellSeal effect as an Argus IR term (gate, then the `setLifecycle` lifecycle flip).

`cellSealChainA`'s KERNEL side is `if <2-conjunct guard> then some (setLifecycle k cell lcSealed) else none`
(plus the runtime log prepend §3 carries). We capture the kernel side term-for-term: a `Bool` `cellSealGuard`
of the EXACT 2 conjuncts, then a `setLifecycle` whose leaf is `(setLifecycle k cell lcSealed).lifecycle` —
the post-`lifecycle` map `cellSealChainA` installs (= `sealLifecycleMap k cell`). The contrast with
transfer/balanceA is the move primitive: `setLifecycle` (rewrites the `lifecycle` side-table) over the
Live→Sealed flip, NOT `setCell`/`setBal`. -/

/-- The cellSeal admissibility gate as a `Bool` — exactly `cellSealChainA`'s `if` (the 2 conjuncts:
self-authority over `cell` via `stateAuthB`, and `cell` is Live via `acceptsEffects`). The self-lifecycle
gate (dregg1 `target == action_target`) + the state-machine gate (only a Live cell may seal). -/
def cellSealGuard (actor cell : CellId) (k : RecordKernelState) : Bool :=
  stateAuthB k.caps actor cell && acceptsEffects k cell

/-- **The cellSeal effect as an IR term: gate, then flip the cell's lifecycle to Sealed.** Mirrors
`transferStmt`/`balanceAStmt` (gate, then move) but the move is `setLifecycle` over the Live→Sealed flip —
the `lifecycle` side-table rewrite — NOT `setCell` (transfer's) or `setBal` (balanceA's). The `setLifecycle`
leaf is `(setLifecycle k cell lcSealed).lifecycle`, EXACTLY the post-`lifecycle` `cellSealChainA` installs on
the kernel (the runtime receipt-log row is re-attached in §3). -/
def cellSealStmt (actor cell : CellId) : RecStmt :=
  RecStmt.seq (RecStmt.guard (cellSealGuard actor cell))
    (RecStmt.setLifecycle (fun k => (setLifecycle k cell lcSealed).lifecycle))

/-! ## §2 — The cornerstone: `interp` of the cellSeal term IS the KERNEL side of `cellSealChainA`. -/

/-- The cellSeal `Bool` gate decodes to `cellSealChainA`'s admissibility proposition (the 2 conjuncts, in
the SAME order the chained step checks them — the `CellSealGuard` proposition). The analog of
`transferGuard_iff`/`balanceAGuard_iff`. -/
theorem cellSealGuard_iff (actor cell : CellId) (k : RecordKernelState) :
    cellSealGuard actor cell k = true ↔
      (stateAuthB k.caps actor cell = true ∧ acceptsEffects k cell = true) := by
  simp only [cellSealGuard, Bool.and_eq_true]

/-- **The cornerstone (kernel-side lifecycle flip).** `interp` of the cellSeal term IS the KERNEL side of the
verified chained transition `cellSealChainA` — on the same 2-conjunct guard, the term commits to exactly the
kernel state `setLifecycle k cell lcSealed` the chained step installs, and rejects on exactly the same gate.
This is the per-effect executor-refinement for the LIFECYCLE family, over the genuine `lifecycle` side-table
via `setLifecycle` (NOT the record-cell `setCell`/`setBal`). The runtime receipt-log prepend is re-attached
in §3 (the kernel-vs-runtime divergence this file carries). -/
theorem interp_cellSealStmt_eq_kernel (actor cell : CellId) (k : RecordKernelState) :
    interp (cellSealStmt actor cell) k
      = if cellSealGuard actor cell k = true then some (setLifecycle k cell lcSealed) else none := by
  simp only [cellSealStmt, interp]
  by_cases hg : cellSealGuard actor cell k = true
  · -- ADMIT: the guard's `interp` fires (`some k`); the `setLifecycle` move installs the post-`lifecycle`
    -- map of `setLifecycle k cell lcSealed`. `{ k with lifecycle := (setLifecycle k cell lcSealed).lifecycle }`
    -- IS `setLifecycle k cell lcSealed` (the lifecycle field IS that map; every other field is `k`'s), so the
    -- two `some (...)` agree DEFINITIONALLY (`rfl`) once both `if`s open on `hg`.
    rw [if_pos hg, if_pos hg]
    rfl
  · -- REJECT: the guard fails ⇒ `none.bind _ = none`; the goal's `if` closes on the negated guard.
    rw [if_neg hg, if_neg hg]
    rfl

#assert_axioms interp_cellSealStmt_eq_kernel

/-! ## §3 — Lifting the cornerstone to the CHAINED executor `cellSealChainA` / `execFullA`.

The standalone cellSeal descriptor (§4) is keyed on the CHAINED executor `cellSealChainA` / `execFullA` over
`RecChainedState` (kernel + receipt log) — the arm `execFullA s (.cellSealA actor cell) = cellSealChainA s
actor cell`. The §2 cornerstone is over the KERNEL side only. The chained layer is exactly the §2 kernel flip
PLUS the runtime receipt-log prepend `cellLifecycleReceipt actor cell :: s.log` — the runtime piece the
`RecordKernelState`-level `interp` structurally cannot emit. We bridge faithfully, naming the receipt-row
prepend EXPLICITLY in the chained post-state (the kernel-vs-runtime divergence). -/

/-- **`interp_cellSealStmt_chained` — the IR term's KERNEL executor, lifted to the chained `execFullA`.**
When the §2 cornerstone commits on the kernel (`interp (cellSealStmt actor cell) s.kernel = some k'`), the
unified action executor `execFullA s (.cellSealA actor cell)` commits to the chained state
`⟨k', cellLifecycleReceipt actor cell :: s.log⟩`. So the Argus term's KERNEL meaning lifts to the chained
executor the standalone descriptor speaks about, with the runtime receipt-log row (which the kernel `interp`
does not model) re-attached HERE — the explicit kernel-vs-runtime bridge. -/
theorem interp_cellSealStmt_chained
    (s : RecChainedState) (actor cell : CellId) (k' : RecordKernelState)
    (hexec : interp (cellSealStmt actor cell) s.kernel = some k') :
    execFullA s (.cellSealA actor cell)
      = some { kernel := k', log := cellLifecycleReceipt actor cell :: s.log } := by
  -- the §2 cornerstone turns the IR term into the kernel-side flip, gated on `cellSealGuard`.
  rw [interp_cellSealStmt_eq_kernel] at hexec
  -- `execFullA s (.cellSealA actor cell)` reduces to `cellSealChainA s actor cell`. Open BOTH on the same
  -- `cellSealGuard` (its decoded 2-conjunct guard IS `cellSealChainA`'s `if` condition).
  show cellSealChainA s actor cell = some { kernel := k', log := cellLifecycleReceipt actor cell :: s.log }
  unfold cellSealChainA
  by_cases hg : cellSealGuard actor cell s.kernel = true
  · -- ADMIT: `hexec` names `k' = setLifecycle s.kernel cell lcSealed`; the chained step commits to that
    -- kernel + the receipt-row prepend, which is `cellLifecycleReceipt actor cell :: s.log` by definition.
    rw [if_pos hg] at hexec
    rw [if_pos ((cellSealGuard_iff actor cell s.kernel).mp hg)]
    simp only [Option.some.injEq] at hexec
    subst hexec
    rfl
  · -- REJECT: contradictory — `hexec` would equate `none = some k'`.
    rw [if_neg hg] at hexec
    exact absurd hexec (by simp)

#assert_axioms interp_cellSealStmt_chained

/-! ## §4 — THE COMPILE WELD: a satisfying witness of cellSeal's OWN standalone full-state circuit agrees with
the FULL post-state the IR term's executor interpretation produces.

This welds against cellSeal's GENUINE standalone descriptor `cellSealCircuit S (cellSealE D hD)` (the v2
`Surface2` circuit whose soundness is `cellSealA_full_sound`), NOT an EffectVM `cellProj` row — see the
descriptor note in this file's header. The executor side is routed through §3 (`interp` ⟹ `execFullA`) and
the independent `cellSeal_iff_spec` (executor ⟺ `CellSealSpec`); the circuit side is the audited
`cellSealA_full_sound` (circuit ⟹ `CellSealSpec`). Both name the SAME `CellSealSpec`, so they PROVABLY agree
on the WHOLE 17-field state + the receipt log — strictly stronger than a per-cell weld. -/

/-- The Argus circuit interpretation of a `cellSeal` term: cellSeal's OWN audited standalone v2 `Surface2`
circuit step — the full-state arithmetization `satisfiedE2 S (cellSealE D hD) (encodeE2 …)` satisfied on the
encoded `(s, ⟨actor,cell⟩, s')` triple (the `EffectRefinement` hub's `effect2CircuitStep`, inlined here so
this module imports only `Inst.cellSealA`). Its soundness `cellSealA_full_sound` pins the complete
`CellSealSpec`. The `cellSeal`-keyed analog of `balanceACircuit`, in the descriptor universe where cellSeal
carries its OWN genuine full-state circuit (NOT EffectVM-inherited). -/
def cellSealCircuit (S : Surface2) (D : (CellId → Nat) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : CellSealArgs) (s' : RecChainedState) : Prop :=
  satisfiedE2 S (cellSealE D hD) (encodeE2 S (cellSealE D hD) s args s')

/-- **`cellSealSpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH satisfy
`CellSealSpec s actor cell ·` are equal. Rather than re-derive this field-by-field, we route through the
PROVEN executor⟺spec corner `cellSeal_iff_spec`: each `CellSealSpec` reconstructs the SAME committed value
`execFullA s (.cellSealA actor cell) = some ·`, and `some` is injective. This is exactly the sense in which
`CellSealSpec` is functional — it determines the post-state — so the circuit-side and executor-side spec
facts collapse to one welded post-state. -/
theorem cellSealSpec_unique {s s₁ s₂ : RecChainedState} {actor cell : CellId}
    (h₁ : CellSealSpec s actor cell s₁) (h₂ : CellSealSpec s actor cell s₂) : s₁ = s₂ := by
  have e₁ : execFullA s (.cellSealA actor cell) = some s₁ := (cellSeal_iff_spec s actor cell s₁).mpr h₁
  have e₂ : execFullA s (.cellSealA actor cell) = some s₂ := (cellSeal_iff_spec s actor cell s₂).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- **`cellSeal_compile_sound` — the welded soundness (cellSeal slice), against cellSeal's OWN descriptor.**

Suppose, for the Argus cellSeal term `cellSealStmt actor cell`:
  * the standalone cellSeal circuit `cellSealCircuit S D hD s ⟨actor,cell⟩ s'` (= `cellSealE`'s full-state v2
    arithmetization satisfied on the encoded triple) holds, under the realizable whole-function digest portals
    (`hRest : RestIffNoLifecycle S.RH`, `hLog : logHashInjective S.LH`, `hD : Function.Injective D`);
  * the IR term's KERNEL executor interpretation COMMITS: `interp (cellSealStmt actor cell) s.kernel = some k'`
    (`hexec`).

Then the chained post-state the circuit pins is EXACTLY the chained post-state the IR term's executor produces
once the runtime receipt-row is re-attached: `s' = { kernel := k', log := cellLifecycleReceipt actor cell ::
s.log }`. I.e. cellSeal's OWN circuit and the IR term AGREE on the WHOLE 17-field RecordKernelState
(`lifecycle` flipped to Sealed at `cell` by `setLifecycle`, every other field frozen) AND the receipt log —
the full `CellSealSpec`, not a per-cell projection. The receipt-log row is named EXPLICITLY in the conclusion,
so the kernel-vs-runtime divergence is part of the welded statement. So the circuit the prover runs for
cellSeal pins the complete chained state the IR term's executor produces. -/
theorem cellSeal_compile_sound
    (S : Surface2) (D : (CellId → Nat) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoLifecycle S.RH) (hLog : logHashInjective S.LH)
    (s s' : RecChainedState) (actor cell : CellId) (k' : RecordKernelState)
    (hcirc : cellSealCircuit S D hD s ⟨actor, cell⟩ s')
    (hexec : interp (cellSealStmt actor cell) s.kernel = some k') :
    s' = { kernel := k', log := cellLifecycleReceipt actor cell :: s.log } := by
  -- circuit side: cellSeal's OWN audited soundness forces the FULL `CellSealSpec` on `(s, ⟨actor,cell⟩, s')`.
  have hspec : CellSealSpec s actor cell s' :=
    cellSealA_full_sound S D hD hRest hLog s ⟨actor, cell⟩ s' hcirc
  -- executor side: the §3 chained lift gives `execFullA s (.cellSealA actor cell) = some ⟨k', receipt::log⟩`,
  -- and the independent executor⟺spec corner turns THAT into `CellSealSpec s actor cell ⟨k', receipt::log⟩`.
  have hspec' : CellSealSpec s actor cell { kernel := k', log := cellLifecycleReceipt actor cell :: s.log } :=
    (cellSeal_iff_spec s actor cell _).mp (interp_cellSealStmt_chained s actor cell k' hexec)
  -- both states satisfy the SAME spec ⇒ they are the same state (the spec pins every kernel field + the log).
  exact cellSealSpec_unique hspec hspec'

#assert_axioms cellSeal_compile_sound

/-! ## §5 — NON-VACUITY: the IR term SEALS the cell (lifecycle flip observable), preserves every
other field (frame), and the gate REJECTS forged / non-Live inputs (fail-closed).

The cornerstone/weld would be hollow if cellSeal never committed, if the flip were a no-op, or if the gate
admitted everything. The concrete chained fixture `fmaS` (`TurnExecutorFull.lean:6460`; cell 0 Live, actor 0
owns it by `Cap.node 0`) exercises a real seal; the rejection lemmas show each guard leg fails closed. -/

/-- A two-cell kernel for the §5 witnesses: cells 0 and 1 live accounts (lifecycle defaults to Live `0`),
cell 0 owned by actor 0 via `Cap.node 0` (so `stateAuthB ... 0 0` holds). Reuses the shape of the audited
`fmaS` fixture's kernel. -/
def kS0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun c => if c = 0 then [Cap.node 0, Cap.node 1] else []
    bal := fun _ _ => 0 }

/-- **NON-VACUITY (the SEAL is OBSERVABLE).** The committed seal FLIPS cell `0`'s lifecycle discriminant from
Live (`0`) to Sealed (`1`) — the cell transitions (the `setLifecycle` flip is real, not a no-op). -/
theorem cellSealStmt_seals :
    (interp (cellSealStmt 0 0) kS0).map (fun k => k.lifecycle 0) = some 1 := by
  rw [interp_cellSealStmt_eq_kernel]
  decide

/-- **NON-VACUITY (the cell ACTUALLY commits).** The seal of a Live, self-owned cell COMMITS (`isSome`) — the
2-conjunct gate admits. (Pins that the weld's `hexec` hypothesis is satisfiable.) -/
theorem cellSealStmt_commits :
    (interp (cellSealStmt 0 0) kS0).isSome = true := by
  rw [interp_cellSealStmt_eq_kernel]
  decide

/-- **NON-VACUITY (frame: a DIFFERENT cell is untouched).** Sealing cell `0` leaves cell `1`'s lifecycle at
Live (`0`) — `setLifecycle` rewrites ONLY the sealed cell's discriminant, confirming the flip is local (not a
global lifecycle collapse). The per-cell frame the full-state `CellSealSpec` pins, observed. -/
theorem cellSealStmt_other_cell_untouched :
    (interp (cellSealStmt 0 0) kS0).map (fun k => k.lifecycle 1) = some 0 := by
  rw [interp_cellSealStmt_eq_kernel]
  decide

/-- **NON-VACUITY (frame: `bal` is untouched).** Sealing cell `0` leaves the `(0,0)` ledger entry at `0` — the
seal is balance-NEUTRAL (`setLifecycle` writes only `lifecycle`, never `bal`), exactly the frozen-frame leg of
`CellSealSpec`. No value is conjured or destroyed by a lifecycle transition. -/
theorem cellSealStmt_bal_frozen :
    (interp (cellSealStmt 0 0) kS0).map (fun k => k.bal 0 0) = some 0 := by
  rw [interp_cellSealStmt_eq_kernel]
  decide

/-- **NON-VACUITY (fail-closed: no authority).** A seal attempted by actor `5`, who holds NO authority over
cell `0` (empty cap list), does NOT commit — the term returns `none` (the `stateAuthB` self-authority leg of
the gate fails). A stranger cannot seal a cell. -/
theorem cellSealStmt_rejects_unauthorized :
    interp (cellSealStmt 5 0) kS0 = none := by
  rw [interp_cellSealStmt_eq_kernel]
  decide

/-- **NON-VACUITY (fail-closed: already Sealed).** A seal attempted on a cell that is ALREADY Sealed
(lifecycle `1`, NOT Live) does NOT commit — the term returns `none` (the `acceptsEffects` state-machine leg
fails; sealing is idempotent-rejected, `AlreadySealed`). A Sealed cell cannot be re-sealed. -/
theorem cellSealStmt_rejects_already_sealed :
    interp (cellSealStmt 0 0) { kS0 with lifecycle := fun _ => lcSealed } = none := by
  rw [interp_cellSealStmt_eq_kernel]
  decide

#assert_axioms cellSealStmt_seals
#assert_axioms cellSealStmt_commits
#assert_axioms cellSealStmt_other_cell_untouched
#assert_axioms cellSealStmt_bal_frozen
#assert_axioms cellSealStmt_rejects_unauthorized
#assert_axioms cellSealStmt_rejects_already_sealed

end Dregg2.Circuit.Argus.Effects.CellSeal
