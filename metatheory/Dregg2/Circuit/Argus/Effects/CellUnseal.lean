/-
# Dregg2.Circuit.Argus.Effects.CellUnseal — the cell LIFECYCLE-UNSEAL effect `cellUnsealA`
(Sealed → Live) welded into the Argus IR, as a FULL-STATE `Surface2` weld.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated it
on transfer/mint/burn/createEscrow. `Effects/BalanceA.lean` then welded a per-component effect to its
genuine standalone v2 `Surface2` descriptor (`balanceA_full_sound`), concluding the WHOLE 17-field
post-state; `Effects/CellSeal.lean` carried that STRONGER surface for the symmetric LIFECYCLE-SEAL flip
(Live → Sealed). This module is the EXACT INVERSE — the LIFECYCLE-UNSEAL transition `cellUnsealA`
(Sealed → Live) — in a disjoint file (it imports the Argus IR + the audited `cellUnsealA` v2 instance +
the independent lifecycle spec, all read-only, and owns only its own declarations).

`cellUnsealA` is the Sealed→Live cell-lifecycle transition (`apply_cell_unseal` → `Cell::unseal`,
`apply.rs:4251`/`cell.rs:559`). The verified chained transition is `cellUnsealChainA`
(`TurnExecutorFull.lean:1663`), and `execFullA s (.cellUnsealA actor cell) = cellUnsealChainA s actor cell`
(`TurnExecutorFull.lean:3895`):

    cellUnsealChainA s actor cell
      = if stateAuthB s.kernel.caps actor cell = true ∧ s.kernel.lifecycle cell == lcSealed then
          some { kernel := setLifecycle s.kernel cell lcLive,
                 log    := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }
        else none

so a committed unseal (i) FLIPS the `lifecycle` discriminant of `cell` BACK to `lcLive` (= `0`) via
`setLifecycle` (every other cell + every other RecordKernelState field FROZEN — it is balance-NEUTRAL),
AND (ii) PREPENDS one self-targeted receipt row onto the chain log. Because the body touches the
`lifecycle` side-table, the IR move is the §A `setLifecycle` component-write primitive — NOT `setCell`
(transfer's) nor `setBal` (balanceA's), exactly as `CellSeal`.

## THE GUARD CONTRAST WITH CellSeal (the genuine inverse — read this).

`cellSealA`'s state-machine leg is `acceptsEffects` (= `lifecycle cell == lcLive`): only a LIVE cell may
seal. `cellUnsealA`'s is the INVERSE precondition — `lifecycle cell == lcSealed` (= `1`): only a SEALED
cell may unseal (dregg1's `NotSealed` otherwise). So the unseal guard is NOT phrased through
`acceptsEffects` at all; it reads the discriminant directly against `lcSealed`. `cellUnsealGuard` below
captures that EXACT 2-conjunct gate (`stateAuthB ∧ lifecycle == lcSealed`), the `CellUnsealGuard`
proposition the spec/instance/executor all share. This is the load-bearing structural difference from the
seal weld — and exactly why a SEALED-cell fixture (not a Live one) is needed to witness a commit (§5).

## THE KERNEL-vs-RUNTIME DIVERGENCE (carried explicitly — read this).

The Argus `interp` is a `RecordKernelState → Option RecordKernelState` transformer; `cellUnsealChainA` is a
`RecChainedState → Option RecChainedState` step — it ALSO prepends a receipt row to the `log`, and the
`log` lives in `RecChainedState`, NOT in `RecordKernelState`. So the IR term's `interp` cannot — and does
not — emit the log row; it captures EXACTLY the KERNEL side of the chained step (the `setLifecycle` flip).
This is the SAME chained-vs-raw boundary `CellSeal`/`BalanceA` carry, here named precisely:

  * `interp (cellUnsealStmt actor cell) k` produces the KERNEL post-state `setLifecycle k cell lcLive`,
    gated on EXACTLY `cellUnsealChainA`'s two-conjunct guard read on `k` (`interp_cellUnsealStmt_eq_kernel`).
  * lifting to the chained `execFullA` (`interp_cellUnsealStmt_chained`) re-attaches the runtime receipt row
    `cellLifecycleReceipt actor cell :: s.log` — the runtime layer the kernel `interp` does not model. The
    welded conclusion (§4) then names the chained post-state `{ kernel := k', log := receipt :: s.log }`
    EXPLICITLY, so the receipt-log obligation is part of the welded statement (not papered).

## THE DESCRIPTOR — a GENUINE full-state v2 `Surface2`, NOT EffectVM-inherited.

`cellUnsealA` carries its OWN standalone v2 `EffectCommit2`/`Surface2` descriptor + full soundness
(`Dregg2/Circuit/Inst/cellUnsealA.lean`): `cellUnsealE` (the `EffectSpec2` whose touched component is the
WHOLE `lifecycle : CellId → Nat` function, a `funcComponent` full-function digest) and
`cellUnsealA_full_sound : satisfiedE2 … (cellUnsealE D hD) … ⟹ CellUnsealSpec` — a FULL 17-field
declarative post-state soundness (`Spec/celllifecycle.lean`'s `CellUnsealSpec`: lifecycle flips back to
Live, the log grows by one receipt, every OTHER kernel field frozen), keyed on the CHAINED executor
`cellUnsealChainA`/`execFullA` via the INDEPENDENT `cellUnseal_iff_spec` (executor ⟺ spec, BOTH
directions). This is the strictly-stronger `BalanceA`/`CellSeal` surface (whole-state full-function
digest), not the per-cell EffectVM/`cellProj` surface transfer/delegate live on.

## Honesty

`#assert_axioms` on every headline theorem ⊆ {propext, Classical.choice, Quot.sound}; the
whole-function-digest assumption enters ONLY inside the reused `cellUnsealA_full_sound` (its
`Function.Injective D` hypothesis + the Poseidon-CR `RestIffNoLifecycle`/`logHashInjective` portals), not in
the welded conclusion's statement. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only; this
file owns only itself.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Inst.cellUnsealA
import Dregg2.Circuit.Spec.celllifecycle
import Dregg2.Circuit.Emit.EffectVmEmitCellUnseal

namespace Dregg2.Circuit.Argus.Effects.CellUnseal

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
-- `stateAuthB` lives in `Dregg2.Exec.EffectsState`; `Cap` (for the `Cap.node` cap literals in the §5
-- fixtures) lives in `Dregg2.Authority`. `open` is not transitive, so these are named explicitly even
-- though the Inst/Spec deps already use them.
open Dregg2.Exec.EffectsState (stateAuthB)
open Dregg2.Authority (Cap)
open Dregg2.Circuit.Argus (RecStmt interp)
-- Broad opens mirroring `Inst/cellUnsealA.lean` so the standalone-descriptor names resolve unqualified:
-- `logHashInjective` lives in `StateCommit`; `Surface2`/`satisfiedE2`/`encodeE2` in `EffectCommit2`.
open Dregg2.Circuit.StateCommit (logHashInjective)
open Dregg2.Circuit.EffectCommit2 (Surface2 satisfiedE2 encodeE2)
open Dregg2.Circuit.Spec.CellLifecycle
  (CellUnsealGuard CellUnsealSpec unsealLifecycleMap cellLifecycleReceipt cellUnseal_iff_spec)
open Dregg2.Circuit.Inst.CellUnsealA (CellUnsealArgs cellUnsealE cellUnsealA_full_sound RestIffNoLifecycle)

/-! ## §1 — The cellUnseal effect as an Argus IR term (gate, then the `setLifecycle` lifecycle flip).

`cellUnsealChainA`'s KERNEL side is `if <2-conjunct guard> then some (setLifecycle k cell lcLive) else
none` (plus the runtime log prepend §3 carries). We capture the kernel side term-for-term: a `Bool`
`cellUnsealGuard` of the EXACT 2 conjuncts, then a `setLifecycle` whose leaf is
`(setLifecycle k cell lcLive).lifecycle` — the post-`lifecycle` map `cellUnsealChainA` installs
(= `unsealLifecycleMap k cell`). The contrast with transfer/balanceA is the move primitive: `setLifecycle`
(rewrites the `lifecycle` side-table) over the Sealed→Live flip, NOT `setCell`/`setBal`; the contrast with
`cellSealA` is the GUARD (only a SEALED cell unseals — `lifecycle == lcSealed`, NOT `acceptsEffects`). -/

/-- The cellUnseal admissibility gate as a `Bool` — exactly `cellUnsealChainA`'s `if` (the 2 conjuncts:
self-authority over `cell` via `stateAuthB`, and `cell` is SEALED via `lifecycle cell == lcSealed`). The
self-lifecycle gate (dregg1 `target == action_target`) + the state-machine gate (only a Sealed cell may
unseal — `NotSealed` otherwise). NOTE the inverse precondition vs `cellSealGuard`: this reads
`== lcSealed` directly, NOT `acceptsEffects` (= `== lcLive`). -/
def cellUnsealGuard (actor cell : CellId) (k : RecordKernelState) : Bool :=
  stateAuthB k.caps actor cell && (k.lifecycle cell == lcSealed)

/-- **The cellUnseal effect as an IR term: gate, then flip the cell's lifecycle back to Live.** Mirrors
`cellSealStmt` (gate, then move) but the move is the INVERSE flip — `setLifecycle` over the Sealed→Live
transition — and the gate's state-machine leg is `== lcSealed` (only a Sealed cell unseals). The
`setLifecycle` leaf is `(setLifecycle k cell lcLive).lifecycle`, EXACTLY the post-`lifecycle`
`cellUnsealChainA` installs on the kernel (the runtime receipt-log row is re-attached in §3). -/
def cellUnsealStmt (actor cell : CellId) : RecStmt :=
  RecStmt.seq (RecStmt.guard (cellUnsealGuard actor cell))
    (RecStmt.setLifecycle (fun k => (setLifecycle k cell lcLive).lifecycle))

/-! ## §2 — The cornerstone: `interp` of the cellUnseal term IS the KERNEL side of `cellUnsealChainA`. -/

/-- The cellUnseal `Bool` gate decodes to `cellUnsealChainA`'s admissibility proposition (the 2 conjuncts,
in the SAME order the chained step checks them — the `CellUnsealGuard` proposition). The analog of
`transferGuard_iff`/`cellSealGuard_iff`. -/
theorem cellUnsealGuard_iff (actor cell : CellId) (k : RecordKernelState) :
    cellUnsealGuard actor cell k = true ↔
      (stateAuthB k.caps actor cell = true ∧ (k.lifecycle cell == lcSealed) = true) := by
  simp only [cellUnsealGuard, Bool.and_eq_true]

/-- **The cornerstone (kernel-side lifecycle flip).** `interp` of the cellUnseal term IS the KERNEL side of
the verified chained transition `cellUnsealChainA` — on the same 2-conjunct guard, the term commits to
exactly the kernel state `setLifecycle k cell lcLive` the chained step installs, and rejects on exactly the
same gate. This is the per-effect executor-refinement for the LIFECYCLE family (the inverse of the seal
flip), over the genuine `lifecycle` side-table via `setLifecycle` (NOT the record-cell `setCell`/`setBal`).
The runtime receipt-log prepend is re-attached in §3 (the kernel-vs-runtime divergence this file carries). -/
theorem interp_cellUnsealStmt_eq_kernel (actor cell : CellId) (k : RecordKernelState) :
    interp (cellUnsealStmt actor cell) k
      = if cellUnsealGuard actor cell k = true then some (setLifecycle k cell lcLive) else none := by
  simp only [cellUnsealStmt, interp]
  -- `cellUnsealGuard actor cell k : Bool` drives BOTH the guard `if` (inside the bind, Bool-coercion form)
  -- and the statement `if` (`= true` form). `split` on the guard value handles both occurrences uniformly;
  -- in each branch the bind reduces and the surviving `setLifecycle` move IS the record update by definition
  -- (`setLifecycle k cell lcLive = { k with lifecycle := fun c => if c = cell then lcLive else … }`), so the
  -- two sides close by `rfl`.
  by_cases hg : cellUnsealGuard actor cell k = true
  · -- ADMIT: the guard fires (`some k`); the `setLifecycle` move installs the post-`lifecycle` record update.
    simp only [hg, ite_true, Option.bind, setLifecycle]
  · -- REJECT: the guard fails ⇒ `none.bind _ = none`; the statement `if` closes on the negated guard.
    rw [Bool.not_eq_true] at hg
    simp only [hg, ite_false, Bool.false_eq_true, Option.bind, setLifecycle]

#assert_axioms interp_cellUnsealStmt_eq_kernel

/-! ## §3 — Lifting the cornerstone to the CHAINED executor `cellUnsealChainA` / `execFullA`.

The standalone cellUnseal descriptor (§4) is keyed on the CHAINED executor `cellUnsealChainA` / `execFullA`
over `RecChainedState` (kernel + receipt log) — the arm `execFullA s (.cellUnsealA actor cell) =
cellUnsealChainA s actor cell`. The §2 cornerstone is over the KERNEL side only. The chained layer is
exactly the §2 kernel flip PLUS the runtime receipt-log prepend `cellLifecycleReceipt actor cell :: s.log`
— the runtime piece the `RecordKernelState`-level `interp` structurally cannot emit. We bridge faithfully,
naming the receipt-row prepend EXPLICITLY in the chained post-state (the honest kernel-vs-runtime divergence
— NOT papered). -/

/-- **`interp_cellUnsealStmt_chained` — the IR term's KERNEL executor, lifted to the chained `execFullA`.**
When the §2 cornerstone commits on the kernel (`interp (cellUnsealStmt actor cell) s.kernel = some k'`), the
unified action executor `execFullA s (.cellUnsealA actor cell)` commits to the chained state
`⟨k', cellLifecycleReceipt actor cell :: s.log⟩`. So the Argus term's KERNEL meaning lifts to the chained
executor the standalone descriptor speaks about, with the runtime receipt-log row (which the kernel `interp`
does not model) re-attached HERE — the explicit kernel-vs-runtime bridge. -/
theorem interp_cellUnsealStmt_chained
    (s : RecChainedState) (actor cell : CellId) (k' : RecordKernelState)
    (hexec : interp (cellUnsealStmt actor cell) s.kernel = some k') :
    execFullA s (.cellUnsealA actor cell)
      = some { kernel := k', log := cellLifecycleReceipt actor cell :: s.log } := by
  -- the §2 cornerstone turns the IR term into the kernel-side flip, gated on `cellUnsealGuard`.
  rw [interp_cellUnsealStmt_eq_kernel] at hexec
  -- `execFullA s (.cellUnsealA actor cell)` reduces to `cellUnsealChainA s actor cell`. Open BOTH on the
  -- same `cellUnsealGuard` (its decoded 2-conjunct guard IS `cellUnsealChainA`'s `if` condition).
  show cellUnsealChainA s actor cell
      = some { kernel := k', log := cellLifecycleReceipt actor cell :: s.log }
  unfold cellUnsealChainA
  by_cases hg : cellUnsealGuard actor cell s.kernel = true
  · -- ADMIT: `hexec` names `k' = setLifecycle s.kernel cell lcLive`; the chained step commits to that
    -- kernel + the receipt-row prepend, which is `cellLifecycleReceipt actor cell :: s.log` by definition.
    rw [if_pos hg] at hexec
    rw [if_pos ((cellUnsealGuard_iff actor cell s.kernel).mp hg)]
    simp only [Option.some.injEq] at hexec
    subst hexec
    rfl
  · -- REJECT: contradictory — `hexec` would equate `none = some k'`.
    rw [if_neg hg] at hexec
    exact absurd hexec (by simp)

#assert_axioms interp_cellUnsealStmt_chained

/-! ## §4 — THE COMPILE WELD: a satisfying witness of cellUnseal's OWN standalone full-state circuit agrees
with the FULL post-state the IR term's executor interpretation produces.

This welds against cellUnseal's GENUINE standalone descriptor `cellUnsealCircuit S (cellUnsealE D hD)` (the
v2 `Surface2` circuit whose soundness is `cellUnsealA_full_sound`), NOT an EffectVM `cellProj` row — see the
descriptor note in this file's header. The executor side is routed through §3 (`interp` ⟹ `execFullA`) and
the independent `cellUnseal_iff_spec` (executor ⟺ `CellUnsealSpec`); the circuit side is the audited
`cellUnsealA_full_sound` (circuit ⟹ `CellUnsealSpec`). Both name the SAME `CellUnsealSpec`, so they PROVABLY
agree on the WHOLE 17-field state + the receipt log — strictly stronger than a per-cell weld. -/

/-- The Argus circuit interpretation of a `cellUnseal` term: cellUnseal's OWN audited standalone v2
`Surface2` circuit step — the full-state arithmetization `satisfiedE2 S (cellUnsealE D hD) (encodeE2 …)`
satisfied on the encoded `(s, ⟨actor,cell⟩, s')` triple (the `EffectRefinement` hub's `effect2CircuitStep`,
inlined here so this module imports only `Inst.cellUnsealA`). Its soundness `cellUnsealA_full_sound` pins the
complete `CellUnsealSpec`. The `cellUnseal`-keyed analog of `cellSealCircuit`, in the descriptor universe
where cellUnseal carries its OWN genuine full-state circuit (NOT EffectVM-inherited). -/
def cellUnsealCircuit (S : Surface2) (D : (CellId → Nat) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : CellUnsealArgs) (s' : RecChainedState) : Prop :=
  satisfiedE2 S (cellUnsealE D hD) (encodeE2 S (cellUnsealE D hD) s args s')

/-- **`cellUnsealSpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH satisfy
`CellUnsealSpec s actor cell ·` are equal. Rather than re-derive this field-by-field, we route through the
PROVEN executor⟺spec corner `cellUnseal_iff_spec`: each `CellUnsealSpec` reconstructs the SAME committed
value `execFullA s (.cellUnsealA actor cell) = some ·`, and `some` is injective. This is exactly the sense
in which `CellUnsealSpec` is functional — it determines the post-state — so the circuit-side and
executor-side spec facts collapse to one welded post-state. -/
theorem cellUnsealSpec_unique {s s₁ s₂ : RecChainedState} {actor cell : CellId}
    (h₁ : CellUnsealSpec s actor cell s₁) (h₂ : CellUnsealSpec s actor cell s₂) : s₁ = s₂ := by
  have e₁ : execFullA s (.cellUnsealA actor cell) = some s₁ := (cellUnseal_iff_spec s actor cell s₁).mpr h₁
  have e₂ : execFullA s (.cellUnsealA actor cell) = some s₂ := (cellUnseal_iff_spec s actor cell s₂).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- **`cellUnseal_compile_sound` — the welded soundness (cellUnseal slice), against cellUnseal's OWN
descriptor.**

Suppose, for the Argus cellUnseal term `cellUnsealStmt actor cell`:
  * the standalone cellUnseal circuit `cellUnsealCircuit S D hD s ⟨actor,cell⟩ s'` (= `cellUnsealE`'s
    full-state v2 arithmetization satisfied on the encoded triple) holds, under the realizable
    whole-function digest portals (`hRest : RestIffNoLifecycle S.RH`, `hLog : logHashInjective S.LH`,
    `hD : Function.Injective D`);
  * the IR term's KERNEL executor interpretation COMMITS:
    `interp (cellUnsealStmt actor cell) s.kernel = some k'` (`hexec`).

Then the chained post-state the circuit pins is EXACTLY the chained post-state the IR term's executor
produces once the runtime receipt-row is re-attached: `s' = { kernel := k', log :=
cellLifecycleReceipt actor cell :: s.log }`. I.e. cellUnseal's OWN circuit and the IR term AGREE on the
WHOLE 17-field RecordKernelState (`lifecycle` flipped back to Live at `cell` by `setLifecycle`, every other
field frozen) AND the receipt log — the full `CellUnsealSpec`, not a per-cell projection. The receipt-log
row is named EXPLICITLY in the conclusion, so the kernel-vs-runtime divergence is part of the welded
statement. So the circuit the prover runs for cellUnseal pins the complete chained state the IR term's
executor produces. -/
theorem cellUnseal_compile_sound
    (S : Surface2) (D : (CellId → Nat) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoLifecycle S.RH) (hLog : logHashInjective S.LH)
    (s s' : RecChainedState) (actor cell : CellId) (k' : RecordKernelState)
    (hcirc : cellUnsealCircuit S D hD s ⟨actor, cell⟩ s')
    (hexec : interp (cellUnsealStmt actor cell) s.kernel = some k') :
    s' = { kernel := k', log := cellLifecycleReceipt actor cell :: s.log } := by
  -- circuit side: cellUnseal's OWN audited soundness forces the FULL `CellUnsealSpec` on
  -- `(s, ⟨actor,cell⟩, s')`.
  have hspec : CellUnsealSpec s actor cell s' :=
    cellUnsealA_full_sound S D hD hRest hLog s ⟨actor, cell⟩ s' hcirc
  -- executor side: the §3 chained lift gives `execFullA s (.cellUnsealA actor cell) = some ⟨k', receipt::log⟩`,
  -- and the independent executor⟺spec corner turns THAT into `CellUnsealSpec s actor cell ⟨k', receipt::log⟩`.
  have hspec' : CellUnsealSpec s actor cell
      { kernel := k', log := cellLifecycleReceipt actor cell :: s.log } :=
    (cellUnseal_iff_spec s actor cell _).mp (interp_cellUnsealStmt_chained s actor cell k' hexec)
  -- both states satisfy the SAME spec ⇒ they are the same state (the spec pins every kernel field + the log).
  exact cellUnsealSpec_unique hspec hspec'

#assert_axioms cellUnseal_compile_sound

/-! ## §5 — NON-VACUITY: the IR term genuinely UNSEALS the cell (lifecycle flip observable), preserves every
other field (frame), and the gate REJECTS forged / non-Sealed inputs (fail-closed).

The cornerstone/weld would be hollow if cellUnseal never committed, if the flip were a no-op, or if the gate
admitted everything. A concrete kernel `kU0` with cell 0 ALREADY SEALED (lifecycle `lcSealed`) and owned by
actor 0 via `Cap.node 0` exercises a real unseal; the rejection lemmas show each guard leg fails closed —
including the genuine-inverse leg: a LIVE cell is REJECTED (only a Sealed cell unseals). -/

/-- A two-cell kernel for the §5 witnesses: cells 0 and 1 live accounts, cell 0 is ALREADY SEALED
(`lifecycle 0 = lcSealed`, every other cell Live `lcLive`) and owned by actor 0 via `Cap.node 0` (so
`stateAuthB ... 0 0` holds). The SEALED precondition is what makes the unseal gate admit — the genuine
inverse of `CellSeal`'s Live fixture. -/
def kU0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun c => if c = 0 then [Cap.node 0, Cap.node 1] else []
    bal := fun _ _ => 0
    lifecycle := fun c => if c = 0 then lcSealed else lcLive }

/-- **NON-VACUITY (the UNSEAL is OBSERVABLE).** The committed unseal FLIPS cell `0`'s lifecycle discriminant
from Sealed (`1`) back to Live (`0`) — the cell genuinely transitions (the `setLifecycle` flip is real, not
a no-op). -/
theorem cellUnsealStmt_unseals :
    (interp (cellUnsealStmt 0 0) kU0).map (fun k => k.lifecycle 0) = some lcLive := by
  rw [interp_cellUnsealStmt_eq_kernel]
  decide

/-- **NON-VACUITY (the cell ACTUALLY commits).** The unseal of a Sealed, self-owned cell COMMITS (`isSome`)
— the 2-conjunct gate genuinely admits. (Pins that the weld's `hexec` hypothesis is satisfiable.) -/
theorem cellUnsealStmt_commits :
    (interp (cellUnsealStmt 0 0) kU0).isSome = true := by
  rw [interp_cellUnsealStmt_eq_kernel]
  decide

/-- **NON-VACUITY (frame: a DIFFERENT cell is untouched).** Unsealing cell `0` leaves cell `1`'s lifecycle at
Live (`0`) — `setLifecycle` rewrites ONLY the unsealed cell's discriminant, confirming the flip is local (not
a global lifecycle collapse). The per-cell frame the full-state `CellUnsealSpec` pins, observed. -/
theorem cellUnsealStmt_other_cell_untouched :
    (interp (cellUnsealStmt 0 0) kU0).map (fun k => k.lifecycle 1) = some lcLive := by
  rw [interp_cellUnsealStmt_eq_kernel]
  decide

/-- **NON-VACUITY (frame: `bal` is untouched).** Unsealing cell `0` leaves the `(0,0)` ledger entry at `0`
— the unseal is balance-NEUTRAL (`setLifecycle` writes only `lifecycle`, never `bal`), exactly the
frozen-frame leg of `CellUnsealSpec`. No value is conjured or destroyed by a lifecycle transition. -/
theorem cellUnsealStmt_bal_frozen :
    (interp (cellUnsealStmt 0 0) kU0).map (fun k => k.bal 0 0) = some 0 := by
  rw [interp_cellUnsealStmt_eq_kernel]
  decide

/-- **NON-VACUITY (fail-closed: no authority).** An unseal attempted by actor `5`, who holds NO authority
over cell `0` (empty cap list), does NOT commit — the term returns `none` (the `stateAuthB` self-authority
leg of the gate fails). A stranger cannot unseal a cell. -/
theorem cellUnsealStmt_rejects_unauthorized :
    interp (cellUnsealStmt 5 0) kU0 = none := by
  rw [interp_cellUnsealStmt_eq_kernel]
  decide

/-- **NON-VACUITY (fail-closed: the genuine INVERSE leg — already Live).** An unseal attempted on a cell that
is ALREADY Live (`lifecycle 0 = lcLive`, NOT Sealed) does NOT commit — the term returns `none` (the
`lifecycle == lcSealed` state-machine leg fails; `NotSealed`). This is the load-bearing contrast with
`CellSeal`: a Live cell admits a SEAL but is REJECTED for an UNSEAL. A Live cell cannot be unsealed. -/
theorem cellUnsealStmt_rejects_already_live :
    interp (cellUnsealStmt 0 0) { kU0 with lifecycle := fun _ => lcLive } = none := by
  rw [interp_cellUnsealStmt_eq_kernel]
  decide

/-- **NON-VACUITY (fail-closed: a DESTROYED cell stays closed).** An unseal attempted on a cell that is
Destroyed (`lifecycle 0 = lcDestroyed`, neither Sealed nor Live) does NOT commit — the `== lcSealed` leg
fails. A terminal cell cannot be resurrected by unseal. -/
theorem cellUnsealStmt_rejects_destroyed :
    interp (cellUnsealStmt 0 0) { kU0 with lifecycle := fun _ => lcDestroyed } = none := by
  rw [interp_cellUnsealStmt_eq_kernel]
  decide

#assert_axioms cellUnsealStmt_unseals
#assert_axioms cellUnsealStmt_commits
#assert_axioms cellUnsealStmt_other_cell_untouched
#assert_axioms cellUnsealStmt_bal_frozen
#assert_axioms cellUnsealStmt_rejects_unauthorized
#assert_axioms cellUnsealStmt_rejects_already_live
#assert_axioms cellUnsealStmt_rejects_destroyed

end Dregg2.Circuit.Argus.Effects.CellUnseal
