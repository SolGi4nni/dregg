/-
# Dregg2.Circuit.Argus.Effects.MakeSovereign — the SOVEREIGN-COMMITMENT effect `makeSovereignA`
welded into the Argus IR, as a FULL-STATE (17-field) weld against the effect's OWN standalone
descriptor.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated
it on transfer/mint/burn. `Effects/BalanceA.lean` and `Effects/CellSeal.lean` then welded genuinely
different primitives to their OWN standalone full-state descriptors, each concluding the WHOLE 17-field
post-state. This module follows that STRONGER full-state surface for `makeSovereignA`, in a disjoint
file (it imports the Argus IR + the audited `makeSovereignA` instance + the independent sovereign-
commitment spec, all read-only, and owns only its own declarations).

## What the effect does — and the HINT-vs-MODEL correction (read this).

The task brief's effect hint said `makeSovereign` "REMOVES a cell from accounts (structural free)".
That is dregg1's RUST runtime behaviour (`Ledger::make_sovereign`, `cell/src/ledger.rs:1014`, does
`cells.remove(id)` + `sovereign_commitments.insert(id, …)` + drops the `bal` column). It is NOT what
the audited Lean executor models. The Lean kernel step (`makeSovereignKernel`,
`Exec/TurnExecutorFull.lean:1425`) is

    makeSovereignKernel k target = { k with cell := sovereignRebind k.cell target }

— a pure VALUE-REBIND on the per-cell `cell` map: at `target` the host-readable record is dropped
behind a 32-byte commitment record `[(commitmentField, .dig (stateCommitment (cell target)))]`, every
OTHER cell whole-preserved, and EVERY non-`cell` kernel field — INCLUDING `accounts` and `bal` — left
LITERALLY unchanged. The cell STAYS in `accounts` (proved off the spec by
`makeSovereignSpec_accounts_frame`); `bal` is a FRAME field (`makeSovereignKernel_recTotalAsset` is
`rfl`-balance-neutral). The Lean model collapses dregg1's THREE host mutations (`cells` /
`sovereign_commitments` / `bal`-drop) onto the single `cell` map (the commitment lands in the rebound
`cell` record; the readable record is dropped from `cell`; the per-asset `bal` ledger is a SEPARATE
domain the model correctly leaves untouched). See `Spec/sovereigncommitment.lean:22-37`.

**Consequence for the IR weld — NO structural-free primitive is needed.** Because the audited executor
does NOT shrink `accounts` (it rebinds `cell` at one index), the Argus body is a SINGLE-CELL `setCell`
move — the SAME write-primitive transfer/mint/burn use — whose leaf is the commitment-only record. The
IR's lack of an `accounts`-shrink / structural-free primitive is therefore NOT a missing primitive for
THIS effect; it is exactly the right shape. The `accounts`-removal "structural free" of the hint is a
KERNEL-vs-RUNTIME divergence (the Lean model is the authority the descriptor and node are proved
against), carried explicitly below as `makeSovereign_accounts_frame` (the IR term PRESERVES `accounts`,
contradicting the hint's "removes from accounts" — proved, not asserted).

## THE KERNEL-vs-RUNTIME DIVERGENCE (carried explicitly — read this).

The Argus `interp` is a `RecordKernelState → Option RecordKernelState` transformer; `makeSovereignStep`
is a `RecChainedState → Option RecChainedState` step — it ALSO prepends a self-targeted receipt row to
the `log`, and the `log` lives in `RecChainedState`, NOT in `RecordKernelState`. So the IR term's
`interp` cannot — and does not — emit the log row; it captures EXACTLY the KERNEL side of the chained
step (the `sovereignRebind` rebind on `cell`). This is the SAME chained-vs-raw boundary `CellSeal`
carries, here named precisely:

  * `interp (makeSovereignStmt actor cell) k` produces the KERNEL post-state `makeSovereignKernel k
    cell`, gated on EXACTLY `makeSovereignStep`'s single `stateAuthB` conjunct read on `k`
    (`interp_makeSovereignStmt_eq_kernel`).
  * lifting to the chained `execFullA` (`interp_makeSovereignStmt_chained`) re-attaches the runtime
    receipt row `{ actor, src := cell, dst := cell, amt := 0 } :: s.log` — the runtime layer the kernel
    `interp` does not model. The welded conclusion (§4) names the chained post-state
    `{ kernel := k', log := receipt :: s.log }` EXPLICITLY, so the receipt-log obligation is part of
    the welded statement (not papered).

## THE GUARD — a SINGLE `stateAuthB` conjunct (no membership / no lifecycle gate).

Unlike the generic `stateStep` field writes (which gate on `stateAuthB ∧ cell ∈ accounts ∧ cellLive`),
`makeSovereignStep` checks ONLY self-authority over `cell` (`stateAuthB`). There is NO `cell ∈
accounts` membership conjunct and NO lifecycle (R6) conjunct — the recorded executor truth (spec
header `:22-30`, `makeSovereignSpec_no_membership_gate` / `_no_lifecycle_gate`). The IR term's guard is
therefore the single `stateAuthB` conjunct, term-for-term; a guard that added the phantom conjuncts
would FAIL the cornerstone `←` direction. The §5 teeth pin this (a non-account, self-authored target
STILL commits).

## THE DESCRIPTOR — a GENUINE full-state v1 `EffectCommit` (17-field), NOT EffectVM-inherited.

`makeSovereignA` carries its OWN standalone full-state descriptor + soundness
(`Dregg2/Circuit/Inst/makeSovereignA.lean`): `makeSovereignE` (the `EffectSpec` whose touched set is
`{cell}`, expected leaf `sovereignRebind`, log grows by the one receipt row) and

    makeSovereignA_full_sound : satisfiedE S makeSovereignE (encodeE …) ⟹ MakeSovereignSpec

— a FULL 17-field declarative post-state soundness (`Spec/sovereigncommitment.lean`'s
`MakeSovereignSpec`: the commitment-rebind cell map, the log grows by one receipt, every OTHER kernel
field frozen), keyed on the CHAINED executor `makeSovereignStep`/`execFullA` via the INDEPENDENT
`execFullA_makeSovereignA_iff_spec` (executor ⟺ spec, BOTH directions).

⚑ DESCRIPTOR-UNIVERSE NOTE (honest): there is NO v2 `Surface2` makeSovereign descriptor (unlike
BalanceA/CellSeal, which carry a v2 whole-FUNCTION-digest soundness). `makeSovereignA`'s genuine
full-state crown jewel lives in the v1 `EffectCommit` framework (`satisfiedE`/`encodeE`/`CommitSurface`
— the four frame-forcing EQ-gate digests over `accounts`-keyed cell leaves). That v1 framework's
full-state soundness `effect_circuit_full_sound` carries two WELL-FORMEDNESS preconditions the v2
whole-function-digest path does not — `AccountsWF s.kernel` and `AccountsWF s'.kernel` (off-account
cells are `default`, so the `accounts`-keyed frame digest binds the whole cell map). We thread BOTH as
explicit hypotheses of the weld (the honest v1-surface cost), so the conclusion is the genuine full
`MakeSovereignSpec` — all 17 kernel fields + the receipt log.

## Honesty

`#assert_axioms` on every headline theorem ⊆ {propext, Classical.choice, Quot.sound}; the v1 CR /
digest-injectivity assumptions (`compressNInjective`/`cellLeafInjective`/`RestHashIffFrame`/
`logHashInjective`) enter ONLY inside the reused `makeSovereignA_full_sound`, not in the welded
conclusion's statement. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only; this file
owns only itself.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Inst.makeSovereignA
import Dregg2.Circuit.Spec.sovereigncommitment
import Dregg2.Circuit.Emit.EffectVmEmitMakeSovereignFullState

namespace Dregg2.Circuit.Argus.Effects.MakeSovereign

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Argus (RecStmt interp)
open Dregg2.Exec.EffectsState (stateAuthB)
open Dregg2.Authority (Cap)
-- Broad opens mirroring `Inst/makeSovereignA.lean` so the standalone-descriptor names resolve:
-- the v1 `CommitSurface`/`satisfiedE`/`encodeE` live in `EffectCommit`; the CR portals in `StateCommit`.
open Dregg2.Circuit.EffectCommit (CommitSurface satisfiedE encodeE)
open Dregg2.Circuit.StateCommit
  (AccountsWF compressNInjective cellLeafInjective RestHashIffFrame logHashInjective)
open Dregg2.Circuit.Spec.SovereignCommitment
  (MakeSovereignGuard MakeSovereignSpec execFullA_makeSovereignA_iff_spec)
open Dregg2.Circuit.Inst.MakeSovereignA (MakeSovereignArgs makeSovereignE makeSovereignA_full_sound)

/-! ## §1 — The makeSovereign effect as an Argus IR term (gate, then the `setCell` commitment-rebind).

`makeSovereignStep`'s KERNEL side is `if stateAuthB … then some (makeSovereignKernel k cell) else none`
(plus the runtime log prepend §3 carries). We capture the kernel side term-for-term: a `Bool`
`makeSovereignGuard` of the EXACT single `stateAuthB` conjunct, then a `setCell {cell}` whose leaf is
the commitment-only record `sovereignRebind` installs at `cell`. The contrast with cellSeal/balanceA is
the move primitive: `setCell` (rewrites the per-cell `cell` map) — the SAME primitive transfer uses,
because the audited executor REBINDS `cell` at one index rather than shrinking `accounts` (see header).
-/

/-- The makeSovereign admissibility gate as a `Bool` — exactly `makeSovereignStep`'s `if` (the SINGLE
conjunct: self-authority over `cell` via `stateAuthB`). Honestly NOT a 3-leg membership/lifecycle gate
(the recorded frame-gap: `makeSovereignA` admits a non-account, sealed/destroyed target — see header). -/
def makeSovereignGuard (actor cell : CellId) (k : RecordKernelState) : Bool :=
  stateAuthB k.caps actor cell

/-- **The makeSovereign effect as an IR term: gate, then rebind the cell behind its commitment.**
Mirrors `transferStmt`/`cellSealStmt` (gate, then move) but the move is `setCell {cell}` whose leaf is
the commitment-only record `[(commitmentField, .dig (stateCommitment (k.cell cell)))]` — EXACTLY the
post-`cell` map `makeSovereignKernel`/`sovereignRebind` installs at `cell` (the readable record is
dropped behind the commitment; the runtime receipt-log row is re-attached in §3). NO structural-free /
`accounts`-shrink primitive: the audited executor rebinds `cell`, it does not remove from `accounts`. -/
def makeSovereignStmt (actor cell : CellId) : RecStmt :=
  RecStmt.seq (RecStmt.guard (makeSovereignGuard actor cell))
    (RecStmt.setCell ({cell} : Finset CellId)
      (fun k _c => Value.record [(commitmentField, Value.dig (stateCommitment (k.cell cell)))]))

/-! ## §2 — The cornerstone: `interp` of the makeSovereign term IS the KERNEL side of `makeSovereignStep`. -/

/-- The makeSovereign `Bool` gate decodes to `makeSovereignStep`'s admissibility proposition (the single
`stateAuthB` conjunct — the `MakeSovereignGuard` proposition). The analog of `cellSealGuard_iff`, but a
SINGLE conjunct (no membership/lifecycle legs, the honest executor truth). -/
theorem makeSovereignGuard_iff (actor cell : CellId) (k : RecordKernelState) :
    makeSovereignGuard actor cell k = true ↔ stateAuthB k.caps actor cell = true := by
  simp only [makeSovereignGuard]

/-- The `setCell {cell}` commitment-rebind map is EXACTLY `sovereignRebind k.cell cell` (identity off
`{cell}`; at `cell` the commitment-only record). The `makeSovereignA` analog of `transferCellMap_eq` —
this is what makes the `setCell` move equal `makeSovereignKernel`'s post-`cell` map. -/
theorem makeSovereignCellMap_eq (cell : CellId) (k : RecordKernelState) :
    (fun c => if c ∈ ({cell} : Finset CellId)
                then Value.record [(commitmentField, Value.dig (stateCommitment (k.cell cell)))]
                else k.cell c)
      = sovereignRebind k.cell cell := by
  funext c
  unfold sovereignRebind
  by_cases hc : c = cell
  · simp only [hc, Finset.mem_singleton, if_pos]
  · simp only [Finset.mem_singleton, hc, if_false]

/-- The `setCell {cell}` post-kernel IS `makeSovereignKernel k cell` (the record update agrees because
the cell map agrees by `makeSovereignCellMap_eq`). -/
theorem makeSovereign_setCell_eq_kernel (cell : CellId) (k : RecordKernelState) :
    { k with cell := fun c => if c ∈ ({cell} : Finset CellId)
                then Value.record [(commitmentField, Value.dig (stateCommitment (k.cell cell)))]
                else k.cell c }
      = makeSovereignKernel k cell := by
  unfold makeSovereignKernel
  rw [makeSovereignCellMap_eq]

/-- **The cornerstone (kernel-side commitment-rebind).** `interp` of the makeSovereign term IS the
KERNEL side of the verified chained transition `makeSovereignStep` — on the same single `stateAuthB`
gate, the term commits to exactly the kernel state `makeSovereignKernel k cell` the chained step
installs, and rejects on exactly the same gate. This is the per-effect executor-refinement for the
SOVEREIGN-COMMITMENT family, over the per-cell `cell` map via `setCell` (the audited executor rebinds
`cell`; it does NOT shrink `accounts`). The runtime receipt-log prepend is re-attached in §3 (the
kernel-vs-runtime divergence this file carries). -/
theorem interp_makeSovereignStmt_eq_kernel (actor cell : CellId) (k : RecordKernelState) :
    interp (makeSovereignStmt actor cell) k
      = if makeSovereignGuard actor cell k = true then some (makeSovereignKernel k cell) else none := by
  simp only [makeSovereignStmt, interp]
  by_cases hg : makeSovereignGuard actor cell k = true
  · -- ADMIT: the guard's `interp` fires (`some k`) AND the RHS `if` opens (same condition `hg`); the
    -- `setCell {cell}` move installs the commitment-rebind map, which IS `makeSovereignKernel k cell`
    -- (same record update, by §2's map equality). `simp only [if_pos hg]` reduces BOTH `if`s (same cond).
    simp only [if_pos hg, Option.bind, makeSovereign_setCell_eq_kernel]
  · -- REJECT: the guard fails ⇒ LHS `none.bind _ = none` AND the RHS `if` closes (same condition `hg`).
    simp only [if_neg hg, Option.bind]

#assert_axioms interp_makeSovereignStmt_eq_kernel

/-! ## §3 — Lifting the cornerstone to the CHAINED executor `makeSovereignStep` / `execFullA`.

The standalone makeSovereign descriptor (§4) is keyed on the CHAINED executor `makeSovereignStep` /
`execFullA` over `RecChainedState` (kernel + receipt log) — the arm
`execFullA s (.makeSovereignA actor cell) = makeSovereignStep s actor cell` (defeq,
`execFullA_makeSovereignA_eq`). The §2 cornerstone is over the KERNEL side only. The chained layer is
exactly the §2 kernel rebind PLUS the runtime receipt-log prepend `{ actor, src := cell, dst := cell,
amt := 0 } :: s.log` — the runtime piece the `RecordKernelState`-level `interp` structurally cannot
emit. We bridge faithfully, naming the receipt-row prepend EXPLICITLY in the chained post-state (the
honest kernel-vs-runtime divergence — NOT papered). -/

/-- **`interp_makeSovereignStmt_chained` — the IR term's KERNEL executor, lifted to the chained
`execFullA`.** When the §2 cornerstone commits on the kernel (`interp (makeSovereignStmt actor cell)
s.kernel = some k'`), the unified action executor `execFullA s (.makeSovereignA actor cell)` commits to
the chained state `⟨k', { actor, src := cell, dst := cell, amt := 0 } :: s.log⟩`. So the Argus term's
KERNEL meaning lifts to the chained executor the standalone descriptor speaks about, with the runtime
receipt-log row (which the kernel `interp` does not model) re-attached HERE — the explicit
kernel-vs-runtime bridge. -/
theorem interp_makeSovereignStmt_chained
    (s : RecChainedState) (actor cell : CellId) (k' : RecordKernelState)
    (hexec : interp (makeSovereignStmt actor cell) s.kernel = some k') :
    execFullA s (.makeSovereignA actor cell)
      = some { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log } := by
  -- the §2 cornerstone turns the IR term into the kernel-side rebind, gated on `makeSovereignGuard`.
  rw [interp_makeSovereignStmt_eq_kernel] at hexec
  -- `execFullA s (.makeSovereignA actor cell)` reduces to `makeSovereignStep s actor cell`. Open BOTH
  -- on the same `stateAuthB` gate (the decoded single guard conjunct IS `makeSovereignStep`'s `if`).
  show makeSovereignStep s actor cell
      = some { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }
  unfold makeSovereignStep
  by_cases hg : makeSovereignGuard actor cell s.kernel = true
  · -- ADMIT: `hexec` names `k' = makeSovereignKernel s.kernel cell`; the chained step commits to that
    -- kernel + the receipt-row prepend.
    rw [if_pos hg] at hexec
    rw [if_pos ((makeSovereignGuard_iff actor cell s.kernel).mp hg)]
    simp only [Option.some.injEq] at hexec
    subst hexec
    rfl
  · -- REJECT: contradictory — `hexec` would equate `none = some k'`.
    rw [if_neg hg] at hexec
    exact absurd hexec (by simp)

#assert_axioms interp_makeSovereignStmt_chained

/-! ## §4 — THE COMPILE WELD: a satisfying witness of makeSovereign's OWN standalone full-state circuit
agrees with the FULL post-state the IR term's executor interpretation produces.

This welds against makeSovereign's GENUINE standalone descriptor `makeSovereignCircuit S makeSovereignE`
(the v1 `EffectCommit` full-state circuit whose soundness is `makeSovereignA_full_sound`), NOT an
EffectVM `cellProj` row — see the descriptor note in this file's header. The executor side is routed
through §3 (`interp` ⟹ `execFullA`) and the independent `execFullA_makeSovereignA_iff_spec` (executor ⟺
`MakeSovereignSpec`); the circuit side is the audited `makeSovereignA_full_sound` (circuit ⟹
`MakeSovereignSpec`). Both name the SAME `MakeSovereignSpec`, so they PROVABLY agree on the WHOLE
17-field state + the receipt log — strictly stronger than a per-cell weld. -/

/-- The Argus circuit interpretation of a `makeSovereign` term: makeSovereign's OWN audited standalone
v1 `EffectCommit` full-state circuit step — the four-EQ-gate arithmetization `satisfiedE S
makeSovereignE (encodeE …)` satisfied on the encoded `(s, ⟨actor,cell⟩, s')` triple. Its soundness
`makeSovereignA_full_sound` pins the complete `MakeSovereignSpec`. The `makeSovereign`-keyed analog of
`cellSealCircuit`, in the v1 descriptor universe where makeSovereign carries its OWN genuine full-state
circuit (NOT EffectVM-inherited; no v2 `Surface2` makeSovereign exists). -/
def makeSovereignCircuit (S : CommitSurface)
    (s : RecChainedState) (args : MakeSovereignArgs) (s' : RecChainedState) : Prop :=
  satisfiedE S makeSovereignE (encodeE S makeSovereignE s args s')

/-- **`makeSovereignSpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH
satisfy `MakeSovereignSpec s actor cell ·` are equal. Rather than re-derive this field-by-field, we
route through the PROVEN executor⟺spec corner `execFullA_makeSovereignA_iff_spec`: each
`MakeSovereignSpec` reconstructs the SAME committed value `execFullA s (.makeSovereignA actor cell) =
some ·`, and `some` is injective. This is exactly the sense in which `MakeSovereignSpec` is functional —
it determines the post-state — so the circuit-side and executor-side spec facts collapse to one welded
post-state. -/
theorem makeSovereignSpec_unique {s s₁ s₂ : RecChainedState} {actor cell : CellId}
    (h₁ : MakeSovereignSpec s actor cell s₁) (h₂ : MakeSovereignSpec s actor cell s₂) : s₁ = s₂ := by
  have e₁ : execFullA s (.makeSovereignA actor cell) = some s₁ :=
    (execFullA_makeSovereignA_iff_spec s actor cell s₁).mpr h₁
  have e₂ : execFullA s (.makeSovereignA actor cell) = some s₂ :=
    (execFullA_makeSovereignA_iff_spec s actor cell s₂).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- **`makeSovereign_compile_sound` — the welded soundness (makeSovereign slice), against
makeSovereign's OWN descriptor.**

Suppose, for the Argus makeSovereign term `makeSovereignStmt actor cell`:
  * the standalone makeSovereign circuit `makeSovereignCircuit S s ⟨actor,cell⟩ s'` (= `makeSovereignE`'s
    full-state v1 four-EQ-gate arithmetization satisfied on the encoded triple) holds, under the v1
    digest-injectivity portals (`hN : compressNInjective S.compressN`, `hL : cellLeafInjective S.CH`,
    `hRest : RestHashIffFrame S.RH`, `hLog : logHashInjective S.LH`) AND the framework's
    well-formedness preconditions `hwf : AccountsWF s.kernel`, `hwf' : AccountsWF s'.kernel` (the honest
    v1-surface cost — off-account cells are `default`, so the `accounts`-keyed frame digest binds the
    whole cell map);
  * the IR term's KERNEL executor interpretation COMMITS: `interp (makeSovereignStmt actor cell)
    s.kernel = some k'` (`hexec`).

Then the chained post-state the circuit pins is EXACTLY the chained post-state the IR term's executor
produces once the runtime receipt-row is re-attached: `s' = { kernel := k', log := { actor, src := cell,
dst := cell, amt := 0 } :: s.log }`. I.e. makeSovereign's OWN circuit and the IR term AGREE on the WHOLE
17-field RecordKernelState (`cell` rebound behind the commitment at `cell`, every other field — INCLUDING
`accounts` and `bal` — frozen) AND the receipt log — the full `MakeSovereignSpec`, not a per-cell
projection. The receipt-log row is named EXPLICITLY in the conclusion, so the kernel-vs-runtime
divergence is part of the welded statement. So the circuit the prover runs for makeSovereign pins the
complete chained state the IR term's executor produces. -/
theorem makeSovereign_compile_sound
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s s' : RecChainedState) (actor cell : CellId) (k' : RecordKernelState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (hcirc : makeSovereignCircuit S s ⟨actor, cell⟩ s')
    (hexec : interp (makeSovereignStmt actor cell) s.kernel = some k') :
    s' = { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log } := by
  -- circuit side: makeSovereign's OWN audited soundness forces the FULL `MakeSovereignSpec` on
  -- `(s, ⟨actor,cell⟩, s')` (the v1 four-EQ-gate framework + the apex bridge, under the WF preconditions).
  have hspec : MakeSovereignSpec s actor cell s' :=
    makeSovereignA_full_sound S hN hL hRest hLog s ⟨actor, cell⟩ s' hwf hwf' hcirc
  -- executor side: the §3 chained lift gives `execFullA s (.makeSovereignA actor cell) = some ⟨k',
  -- receipt::log⟩`, and the independent executor⟺spec corner turns THAT into `MakeSovereignSpec …`.
  have hspec' : MakeSovereignSpec s actor cell
      { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log } :=
    (execFullA_makeSovereignA_iff_spec s actor cell _).mp
      (interp_makeSovereignStmt_chained s actor cell k' hexec)
  -- both states satisfy the SAME spec ⇒ they are the same state (the spec pins every kernel field + log).
  exact makeSovereignSpec_unique hspec hspec'

#assert_axioms makeSovereign_compile_sound

/-! ## §5 — NON-VACUITY: the IR term genuinely REBINDS the cell (commitment observable, balance dropped),
PRESERVES `accounts` (the hint-vs-model divergence, proved), and the gate REJECTS forged inputs
(fail-closed) while ADMITTING a non-account target (the recorded frame-gap).

The cornerstone/weld would be hollow if makeSovereign never committed, if the rebind were a no-op, or if
the gate admitted everything (or, conversely, if it secretly carried a phantom membership gate). The
concrete kernel `kMS0` (cells 0,1 live accounts; cell 0 self-owned via `Cap.node 0`, carries a readable
record) exercises a real rebind; the rejection/admission lemmas pin the single real gate AND its
recorded gaps. -/

/-- A two-cell kernel for the §5 witnesses: cells 0 and 1 are live accounts, cell 0 owned by actor 0 via
`Cap.node 0` (so `stateAuthB ... 0 0` holds by ownership), cell 0 carries a rich readable record. -/
def kMS0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun c => if c = 0 then Value.record [("balance", .int 100), ("nonce", .int 3)]
                     else Value.record [("balance", .int 5)]
    caps := fun c => if c = 0 then [Cap.node 0] else []
    bal := fun _ _ => 0 }

/-- **NON-VACUITY (the cell ACTUALLY commits).** The rebind of a self-owned cell COMMITS (`isSome`) —
the single `stateAuthB` gate genuinely admits. (Pins that the weld's `hexec` hypothesis is satisfiable.) -/
theorem makeSovereignStmt_commits :
    (interp (makeSovereignStmt 0 0) kMS0).isSome = true := by
  rw [interp_makeSovereignStmt_eq_kernel]
  decide

/-- **NON-VACUITY (the REBIND is OBSERVABLE — balance dropped behind the commitment).** After the
committed rebind, reading the `balance` scalar of cell `0` returns `none` — the host-readable record was
dropped behind the 32-byte commitment (a FLAG model would leave `balance` readable; this is the
distinguishing fidelity of the value-rebind, the same teeth `makeSovereignStep_balance_unreadable`
proves on the executor). -/
theorem makeSovereignStmt_balance_unreadable :
    (interp (makeSovereignStmt 0 0) kMS0).map (fun k => (k.cell 0).scalar "balance") = some none := by
  rw [interp_makeSovereignStmt_eq_kernel]
  decide

/-- **NON-VACUITY (the COMMITMENT is OBSERVABLE).** After the committed rebind, cell `0` carries a
`commitment` field (the digest binding the WHOLE pre-state value) — the rebind genuinely installs the
commitment record, not a no-op. -/
theorem makeSovereignStmt_commitment_present :
    (interp (makeSovereignStmt 0 0) kMS0).map (fun k => ((k.cell 0).field "commitment").isSome)
      = some true := by
  rw [interp_makeSovereignStmt_eq_kernel]
  decide

/-- **⚑ THE HINT-vs-MODEL DIVERGENCE, PROVED — `accounts` is PRESERVED, NOT shrunk.** The task hint said
makeSovereign "REMOVES a cell from accounts (structural free)". The audited Lean executor does the
OPPOSITE: after the committed rebind, `accounts` is byte-for-byte the pre-state `{0,1}` — the cell is
NOT removed. This is the kernel-vs-runtime divergence carried as a proved fact (the IR term needs NO
structural-free / `accounts`-shrink primitive; it rebinds `cell`). -/
theorem makeSovereign_accounts_frame :
    (interp (makeSovereignStmt 0 0) kMS0).map (fun k => k.accounts) = some kMS0.accounts := by
  rw [interp_makeSovereignStmt_eq_kernel]
  decide

/-- **NON-VACUITY (frame: a DIFFERENT cell is untouched).** Rebinding cell `0` leaves cell `1`'s
`balance` readable as `5` — `setCell {cell}` rewrites ONLY the target cell, confirming the rebind is
local (not a global cell-map collapse). The per-cell frame the full-state `MakeSovereignSpec` pins. -/
theorem makeSovereignStmt_other_cell_untouched :
    (interp (makeSovereignStmt 0 0) kMS0).map (fun k => (k.cell 1).scalar "balance") = some (some 5) := by
  rw [interp_makeSovereignStmt_eq_kernel]
  decide

/-- **NON-VACUITY (frame: `bal` is untouched).** Rebinding cell `0` leaves the `(0,0)` per-asset ledger
entry at `0` — the rebind is a host-representation move, never the per-asset supply (`setCell` writes
only `cell`, never `bal`). Exactly the frozen-`bal` leg of `MakeSovereignSpec`; no value is conjured or
destroyed by making a cell sovereign. -/
theorem makeSovereignStmt_bal_frozen :
    (interp (makeSovereignStmt 0 0) kMS0).map (fun k => k.bal 0 0) = some 0 := by
  rw [interp_makeSovereignStmt_eq_kernel]
  decide

/-- **NON-VACUITY (fail-closed: no authority).** A rebind attempted by actor `5`, who holds NO authority
over cell `0` (empty cap list), does NOT commit — the term returns `none` (the single `stateAuthB`
self-authority gate fails). A stranger cannot make a cell sovereign. -/
theorem makeSovereignStmt_rejects_unauthorized :
    interp (makeSovereignStmt 5 0) kMS0 = none := by
  rw [interp_makeSovereignStmt_eq_kernel]
  decide

/-- **⚑ RECORDED FRAME-GAP, PROVED — a NON-ACCOUNT, self-authored target STILL commits.** Cell `7` is
NOT in `accounts` ({0,1}), yet a self-authored (`actor = cell = 7`, authority by ownership) rebind
COMMITS — `makeSovereignStep` has NO `cell ∈ accounts` membership gate (contrast `setFieldA`, which
would reject). This pins the guard's honest single-conjunct shape (the same gap
`makeSovereignSpec_no_membership_gate` records on the spec); a guard that added the phantom membership
conjunct would make this `none`. -/
theorem makeSovereignStmt_no_membership_gate :
    (interp (makeSovereignStmt 7 7) kMS0).isSome = true := by
  rw [interp_makeSovereignStmt_eq_kernel]
  decide

#assert_axioms makeSovereignStmt_commits
#assert_axioms makeSovereignStmt_balance_unreadable
#assert_axioms makeSovereignStmt_commitment_present
#assert_axioms makeSovereign_accounts_frame
#assert_axioms makeSovereignStmt_other_cell_untouched
#assert_axioms makeSovereignStmt_bal_frozen
#assert_axioms makeSovereignStmt_rejects_unauthorized
#assert_axioms makeSovereignStmt_no_membership_gate

end Dregg2.Circuit.Argus.Effects.MakeSovereign
