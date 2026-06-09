/-
# Dregg2.Circuit.Argus.Effects.Refusal — the CELL-STATE-AUDIT effect `refusalA` (the cross-cell
SetState refusal commitment) welded into the Argus IR, as a FULL-STATE weld.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated
it on transfer/mint/burn/createEscrow. `Effects/BalanceA.lean` then welded a per-component effect to a
genuine standalone full-state descriptor (`balanceA_full_sound`), concluding the WHOLE 17-field
post-state, and `Effects/CellSeal.lean` followed that surface for the LIFECYCLE family. This module
follows the SAME strong full-state surface for the genuinely different AUDIT-WRITE primitive `refusalA`,
in a disjoint file (it imports the Argus IR + the audited `refusalA` v1 instance + the independent
cell-state-audit spec, all read-only, and owns only its own declarations).

`refusalA` is dregg1's cross-cell SetState **refusal commitment**: the live executor's `.refusalA` arm
writes ONLY `cell`'s `"refusal"` audit slot (inside the `cell : CellId → Value` record map) to `1`, a
one-shot proof-of-non-action flag (a `Monotonic` chain row — `EffectsState.refusal_is_monotonic`). It is
BALANCE-NEUTRAL (no `bal` move), CAP-NEUTRAL (no authority amplification), and freezes the other 15
kernel components + every other cell's whole record. The verified executor arm is DEFINITIONALLY the bare
authority-gated field write (`Spec/cellstateaudit.lean`'s `execFullA_refusalA_eq`):

    execFullA s (.refusalA actor cell) = stateStep s refusalField actor cell (.int 1)

and `stateStep` (`EffectsState.lean:205`) commits IFF its three-leg admissibility gate holds —

    stateAuthB s.kernel.caps actor cell = true   -- (1) AUTHORITY (dregg1's cross-cell SetState leg)
  ∧ cell ∈ s.kernel.accounts                      -- (2) MEMBERSHIP (`cell` a live account)
  ∧ cellLive s.kernel cell = true                 -- (3) LIVENESS (R6: `cell` admits effects)

— writing `cell`'s `"refusal"` slot to `1` (via `writeField`, touching ONLY that cell's record in the
`cell` map) and prepending one self-targeted receipt row to the chain log. Because the move touches the
per-cell RECORD map, the IR body's move is the §`setCell` primitive (over the single touched cell `{cell}`)
with leaf `setField refusalField (k.cell c) (.int 1)` — NOT `setBal` (balanceA's) nor `setLifecycle`
(cellSeal's, which writes the `lifecycle` SIDE-TABLE). That is the structural contrast: cellSeal flips a
`CellId → Nat` side-table; refusal writes a non-`balance` slot of the `CellId → Value` record map.

## THE DESCRIPTOR — a GENUINE full-state v1 `EffectCommit` soundness (the HONEST surface contrast).

Unlike balanceA/cellSeal (whose standalone descriptors live in the v2 `EffectCommit2`/`Surface2`
universe), `refusalA`'s genuine standalone circuit⟺spec crown jewel lives in the **v1 `EffectCommit`**
universe (`Dregg2/Circuit/Inst/refusalA.lean`): `refusalE` (the `EffectSpec` whose touched set is the
singleton `{cell}`, expected leaf `auditCellMap … refusalField`, with a single `propBit` guard column for
the three-leg `auditGuard`) and

    refusalA_full_sound : satisfiedE S refusalE (encodeE S refusalE s args s') ⟹ RefusalSpec …

a FULL 17-field declarative post-state soundness (`Spec/cellstateaudit.lean`'s `RefusalSpec`: the audit
slot flips, the log grows by one receipt, every OTHER kernel field frozen), keyed on the CHAINED executor
`execFullA` via the INDEPENDENT `execFullA_refusalA_iff_spec` (executor ⟺ spec, BOTH directions). This is
STILL the strong full-state surface BalanceA prefers (the conclusion is the WHOLE post-state, not a
per-cell `cellProj` projection) — it just rides the v1 sponge framework (`CommitSurface`/`satisfiedE`/
`encodeE`/`effect_circuit_full_sound`) rather than the v2 one, because that is the descriptor `refusalA`
genuinely carries. There is a SEPARATE per-cell EffectVM row (`Emit/EffectVmEmitRefusal`) that TICKS the
cell nonce, but its own header records "the refusal SOUNDNESS lives ONLY in `refusalA_full_sound`" — so we
weld against the full-state one, and note the EffectVM nonce-tick as a divergence belonging to a DIFFERENT
universe we do not weld here (carried in the structured report, NOT papered).

## THE KERNEL-vs-RUNTIME DIVERGENCE (carried explicitly — read this).

The Argus `interp` is a `RecordKernelState → Option RecordKernelState` transformer; the executor arm
`stateStep`/`execFullA` is a `RecChainedState → Option RecChainedState` step — it ALSO prepends a receipt
row to the `log`, and the `log` lives in `RecChainedState`, NOT in `RecordKernelState`. So the IR term's
`interp` cannot — and does not — emit the log row; it captures EXACTLY the KERNEL side of the chained step
(the `"refusal" := 1` record-slot write). This is the SAME chained-vs-raw boundary CellSeal carries, here
named precisely:

  * `interp (refusalStmt actor cell) k` produces the KERNEL post-state `writeField k refusalField cell
    (.int 1)` (its `cell` map is `auditCellMap k cell refusalField`, every other kernel field frozen),
    gated on EXACTLY `stateStep`'s three-leg guard read on `k` (`interp_refusalStmt_eq_kernel`).
  * lifting to the chained `execFullA` (`interp_refusalStmt_chained`) re-attaches the runtime receipt row
    `{ actor, src := cell, dst := cell, amt := 0 } :: s.log` — the runtime layer the kernel `interp` does
    not model. The welded conclusion (§4) then names the chained post-state `{ kernel := k', log :=
    receipt :: s.log }` EXPLICITLY, so the receipt-log obligation is part of the welded statement.

## Honesty

`#assert_axioms` on every headline theorem ⊆ {propext, Classical.choice, Quot.sound}; the Poseidon-CR /
sponge-injectivity assumptions enter ONLY inside the reused `refusalA_full_sound` (its
`compressNInjective`/`cellLeafInjective`/`RestHashIffFrame`/`logHashInjective` portals + `AccountsWF` on
both kernels), NOT in the welded conclusion's statement. No `sorry`, no `:= True`, no `native_decide`.
Imports are read-only; this file owns only itself.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Inst.refusalA
import Dregg2.Circuit.Spec.cellstateaudit
import Dregg2.Circuit.Emit.EffectVmEmitRefusalFullState

namespace Dregg2.Circuit.Argus.Effects.Refusal

open Dregg2.Exec
open Dregg2.Exec.EffectsState
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Argus (RecStmt interp)
-- The v1 `EffectCommit` framework + the sponge-injectivity portals (mirroring `Inst/refusalA.lean`).
open Dregg2.Circuit.StateCommit
  (AccountsWF compressNInjective cellLeafInjective RestHashIffFrame logHashInjective)
open Dregg2.Circuit.EffectCommit (CommitSurface EffectSpec satisfiedE encodeE)
-- The independent full-state spec + executor⟺spec corner.
open Dregg2.Circuit.Spec.CellStateAudit
  (auditGuard auditCellMap auditCellMap_eq_writeField RefusalSpec execFullA_refusalA_eq
   execFullA_refusalA_iff_spec)
-- The audited v1 instance: the `EffectSpec`, its args, and the crown-jewel full soundness.
open Dregg2.Circuit.Inst.RefusalA (RefusalArgs refusalE refusalA_full_sound)

/-! ## §1 — The refusal effect as an Argus IR term (gate, then the `setCell` audit-slot write).

`stateStep`'s KERNEL side is `if <3-conjunct guard> then some (writeField k refusalField cell (.int 1))
else none` (plus the runtime log prepend §3 carries). We capture the kernel side term-for-term: a `Bool`
`refusalGuard` of the EXACT three conjuncts, then a `setCell {cell}` whose leaf writes the `"refusal"`
slot of `cell`'s record to `1`. The contrast with transfer/balanceA/cellSeal is the touched object: the
per-cell RECORD map (`setCell`), at a NON-`balance` audit slot, not the `bal` ledger or the `lifecycle`
side-table. -/

/-- The refusal admissibility gate as a `Bool` — exactly `stateStep`'s `if` (the three legs: AUTHORITY
over `cell` via `stateAuthB` — dregg1's cross-cell SetState refusal leg; `cell` a live account
MEMBERSHIP; `cell`'s lifecycle admits effects LIVENESS, the R6 gate). This is the SAME gate the
independent spec exposes as the `Prop` `auditGuard`. -/
def refusalGuard (actor cell : CellId) (k : RecordKernelState) : Bool :=
  stateAuthB k.caps actor cell
    && decide (cell ∈ k.accounts)
    && cellLive k cell

/-- **The refusal effect as an IR term: gate, then write the `"refusal"` audit slot of `cell` to `1`.**
Mirrors `transferStmt`/`balanceAStmt`/`cellSealStmt` (gate, then move) but the move is `setCell {cell}`
over the audit-slot write `setField refusalField (k.cell c) (.int 1)` — a NON-`balance` field of the
per-cell RECORD map — NOT `setBal` (balanceA's ledger) nor `setLifecycle` (cellSeal's side-table). The
`setCell` leaf is EXACTLY the per-cell map `writeField k refusalField cell (.int 1)` installs (the runtime
receipt-log row is re-attached in §3). -/
def refusalStmt (actor cell : CellId) : RecStmt :=
  RecStmt.seq (RecStmt.guard (refusalGuard actor cell))
    (RecStmt.setCell ({cell} : Finset CellId)
      (fun k c => setField refusalField (k.cell c) (.int 1)))

/-! ## §2 — The cornerstone: `interp` of the refusal term IS the KERNEL side of the executor arm. -/

/-- The refusal `Bool` gate decodes to `stateStep`'s admissibility proposition (the three conjuncts, in
the SAME order the executor `if` checks them — the `auditGuard` proposition). The analog of
`transferGuard_iff` / `cellSealGuard_iff`. -/
theorem refusalGuard_iff (actor cell : CellId) (k : RecordKernelState) :
    refusalGuard actor cell k = true ↔
      (stateAuthB k.caps actor cell = true ∧ cell ∈ k.accounts ∧ cellLive k cell = true) := by
  simp only [refusalGuard, Bool.and_eq_true, decide_eq_true_eq]
  tauto

/-- The `setCell {cell}` audit map is exactly `writeField … refusalField … (.int 1)` (identity off the
single cell). The refusal analog of `transferCellMap_eq` / `creditCellMap_eq`: the post-`cell` map the IR
move installs IS the executor's `writeField` post-cell map (so the kernel post-states coincide as whole
records, not just on the `cell` field). -/
theorem refusalCellMap_eq (cell : CellId) (k : RecordKernelState) :
    { k with cell := fun c => if c ∈ ({cell} : Finset CellId)
                                then setField refusalField (k.cell c) (.int 1) else k.cell c }
      = writeField k refusalField cell (.int 1) := by
  unfold writeField
  congr 1
  funext c
  by_cases hc : c = cell
  · simp [hc]
  · simp [Finset.mem_singleton, hc]

/-- **The cornerstone (kernel-side audit write).** `interp` of the refusal term IS the KERNEL side of the
verified executor arm — on the same three-leg guard, the term commits to exactly the kernel state
`writeField k refusalField cell (.int 1)` the executor installs, and rejects on exactly the same gate.
This is the per-effect executor-refinement for the AUDIT-WRITE family, over the per-cell RECORD map via
`setCell` at a NON-`balance` slot (NOT `setBal`/`setLifecycle`). The runtime receipt-log prepend is
re-attached in §3 (the kernel-vs-runtime divergence this file carries). -/
theorem interp_refusalStmt_eq_kernel (actor cell : CellId) (k : RecordKernelState) :
    interp (refusalStmt actor cell) k
      = if refusalGuard actor cell k = true then some (writeField k refusalField cell (.int 1))
        else none := by
  simp only [refusalStmt, interp]
  by_cases hg : refusalGuard actor cell k = true
  · -- ADMIT: the guard's `interp` fires (`some k`) on BOTH sides; the `setCell {cell}` move installs the
    -- per-cell map, which IS `writeField k refusalField cell (.int 1)` (whole record, by `refusalCellMap_eq`).
    simp only [if_pos hg, Option.bind]
    rw [refusalCellMap_eq]
  · -- REJECT: the guard fails ⇒ `none.bind _ = none` on BOTH sides.
    simp only [if_neg hg, Option.bind]

#assert_axioms interp_refusalStmt_eq_kernel

/-! ## §3 — Lifting the cornerstone to the CHAINED executor `execFullA`.

The standalone refusal descriptor (§4) is keyed on the CHAINED executor `execFullA` over `RecChainedState`
(kernel + receipt log) — the arm `execFullA s (.refusalA actor cell) = stateStep s refusalField actor cell
(.int 1)` (`execFullA_refusalA_eq`, by `rfl`). The §2 cornerstone is over the KERNEL side only. The chained
layer is exactly the §2 kernel write PLUS the runtime receipt-log prepend `{ actor, src := cell, dst :=
cell, amt := 0 } :: s.log` — the runtime piece the `RecordKernelState`-level `interp` structurally cannot
emit. We bridge faithfully, naming the receipt-row prepend EXPLICITLY in the chained post-state (the honest
kernel-vs-runtime divergence — NOT papered). -/

/-- The self-targeted receipt row a committed refusal prepends to the chain log (the SAME literal
`stateStep` installs). Named so the chained post-state's `log` clause is the genuine row. -/
def refusalReceipt (cell : CellId) : Turn :=
  { actor := cell, src := cell, dst := cell, amt := 0 }

/-- **`interp_refusalStmt_chained` — the IR term's KERNEL executor, lifted to the chained `execFullA`.**
When the §2 cornerstone commits on the kernel (`interp (refusalStmt actor cell) s.kernel = some k'`), the
unified action executor `execFullA s (.refusalA actor cell)` commits to the chained state `⟨k', { actor,
src := cell, dst := cell, amt := 0 } :: s.log⟩`. So the Argus term's KERNEL meaning lifts to the chained
executor the standalone descriptor speaks about, with the runtime receipt-log row (which the kernel
`interp` does not model) re-attached HERE — the explicit kernel-vs-runtime bridge. -/
theorem interp_refusalStmt_chained
    (s : RecChainedState) (actor cell : CellId) (k' : RecordKernelState)
    (hexec : interp (refusalStmt actor cell) s.kernel = some k') :
    execFullA s (.refusalA actor cell)
      = some { kernel := k',
               log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log } := by
  -- the §2 cornerstone turns the IR term into the kernel-side write, gated on `refusalGuard`.
  rw [interp_refusalStmt_eq_kernel] at hexec
  -- `execFullA s (.refusalA actor cell)` reduces to `stateStep s refusalField actor cell (.int 1)`. Open
  -- BOTH on the same `refusalGuard` (its decoded 3-conjunct guard IS `stateStep`'s `if` condition).
  rw [execFullA_refusalA_eq]
  unfold stateStep
  by_cases hg : refusalGuard actor cell s.kernel = true
  · -- ADMIT: `hexec` names `k' = writeField s.kernel refusalField cell (.int 1)`; the chained step commits
    -- to that kernel + the receipt-row prepend.
    rw [if_pos hg] at hexec
    rw [if_pos ((refusalGuard_iff actor cell s.kernel).mp hg)]
    simp only [Option.some.injEq] at hexec
    subst hexec
    rfl
  · -- REJECT: contradictory — `hexec` would equate `none = some k'`.
    rw [if_neg hg] at hexec
    exact absurd hexec (by simp)

#assert_axioms interp_refusalStmt_chained

/-! ## §4 — THE COMPILE WELD: a satisfying witness of refusal's OWN standalone full-state circuit agrees
with the FULL post-state the IR term's executor interpretation produces.

This welds against refusal's GENUINE standalone v1 descriptor `refusalCircuit S s ⟨actor,cell⟩ s'` (the
full-state arithmetization whose soundness is `refusalA_full_sound`), NOT an EffectVM `cellProj` row — see
the descriptor note in this file's header. The executor side is routed through §3 (`interp` ⟹ `execFullA`)
and the independent `execFullA_refusalA_iff_spec` (executor ⟺ `RefusalSpec`); the circuit side is the
audited `refusalA_full_sound` (circuit ⟹ `RefusalSpec`). Both name the SAME `RefusalSpec`, so they PROVABLY
agree on the WHOLE 17-field state + the receipt log — strictly stronger than a per-cell weld. -/

/-- The Argus circuit interpretation of a `refusal` term: refusal's OWN audited standalone v1
`EffectCommit` full-state circuit step — the full-state sponge arithmetization `satisfiedE S refusalE
(encodeE …)` satisfied on the encoded `(s, ⟨actor,cell⟩, s')` triple. Its soundness `refusalA_full_sound`
pins the complete `RefusalSpec`. The `refusal`-keyed analog of `cellSealCircuit`/`balanceACircuit`, in the
v1 descriptor universe where refusal carries its OWN genuine full-state circuit. -/
def refusalCircuit (S : CommitSurface) (s : RecChainedState) (args : RefusalArgs)
    (s' : RecChainedState) : Prop :=
  satisfiedE S refusalE (encodeE S refusalE s args s')

/-- **`refusalSpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH satisfy
`RefusalSpec s actor cell ·` are equal. Rather than re-derive this field-by-field, we route through the
PROVEN executor⟺spec corner `execFullA_refusalA_iff_spec`: each `RefusalSpec` reconstructs the SAME
committed value `execFullA s (.refusalA actor cell) = some ·`, and `some` is injective. This is exactly the
sense in which `RefusalSpec` is functional — it determines the post-state — so the circuit-side and
executor-side spec facts collapse to one welded post-state. -/
theorem refusalSpec_unique {s s₁ s₂ : RecChainedState} {actor cell : CellId}
    (h₁ : RefusalSpec s actor cell s₁) (h₂ : RefusalSpec s actor cell s₂) : s₁ = s₂ := by
  have e₁ : execFullA s (.refusalA actor cell) = some s₁ :=
    (execFullA_refusalA_iff_spec s actor cell s₁).mpr h₁
  have e₂ : execFullA s (.refusalA actor cell) = some s₂ :=
    (execFullA_refusalA_iff_spec s actor cell s₂).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- **`refusal_compile_sound` — the welded soundness (refusal slice), against refusal's OWN descriptor.**

Suppose, for the Argus refusal term `refusalStmt actor cell`:
  * the standalone refusal circuit `refusalCircuit S s ⟨actor,cell⟩ s'` (= `refusalE`'s full-state v1
    arithmetization satisfied on the encoded triple) holds, under the realizable Poseidon sponge portals
    (`hN : compressNInjective S.compressN`, `hL : cellLeafInjective S.CH`, `hRest : RestHashIffFrame S.RH`,
    `hLog : logHashInjective S.LH`) and `AccountsWF` on BOTH kernels (`hwf`, `hwf'`);
  * the IR term's KERNEL executor interpretation COMMITS: `interp (refusalStmt actor cell) s.kernel =
    some k'` (`hexec`).

Then the chained post-state the circuit pins is EXACTLY the chained post-state the IR term's executor
produces once the runtime receipt-row is re-attached: `s' = { kernel := k', log := { actor, src := cell,
dst := cell, amt := 0 } :: s.log }`. I.e. refusal's OWN circuit and the IR term AGREE on the WHOLE 17-field
RecordKernelState (the `"refusal"` slot of `cell` set to `1`, every other field — `bal`, `caps`,
`nullifiers`, the `lifecycle` side-table, every other cell — frozen) AND the receipt log — the full
`RefusalSpec`, not a per-cell projection. The receipt-log row is named EXPLICITLY in the conclusion, so the
kernel-vs-runtime divergence is part of the welded statement. So the circuit the prover runs for refusal
pins the complete chained state the IR term's executor produces. -/
theorem refusal_compile_sound
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s s' : RecChainedState) (actor cell : CellId) (k' : RecordKernelState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (hcirc : refusalCircuit S s ⟨actor, cell⟩ s')
    (hexec : interp (refusalStmt actor cell) s.kernel = some k') :
    s' = { kernel := k',
           log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log } := by
  -- circuit side: refusal's OWN audited soundness forces the FULL `RefusalSpec` on `(s, ⟨actor,cell⟩, s')`.
  have hspec : RefusalSpec s actor cell s' :=
    refusalA_full_sound S hN hL hRest hLog s ⟨actor, cell⟩ s' hwf hwf' hcirc
  -- executor side: the §3 chained lift gives `execFullA s (.refusalA actor cell) = some ⟨k', receipt::log⟩`,
  -- and the independent executor⟺spec corner turns THAT into `RefusalSpec s actor cell ⟨k', receipt::log⟩`.
  have hspec' : RefusalSpec s actor cell
      { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log } :=
    (execFullA_refusalA_iff_spec s actor cell _).mp (interp_refusalStmt_chained s actor cell k' hexec)
  -- both states satisfy the SAME spec ⇒ they are the same state (the spec pins every kernel field + the log).
  exact refusalSpec_unique hspec hspec'

#assert_axioms refusal_compile_sound

/-! ## §5 — NON-VACUITY: the IR term genuinely STAMPS the refusal (slot write observable), preserves every
other field (frame), and the gate REJECTS forged / non-account / non-Live inputs (fail-closed).

The cornerstone/weld would be hollow if refusal never committed, if the write were a no-op, or if the gate
admitted everything. A concrete two-cell kernel `kR0` (cells 0,1 live; cell 0 owned by actor 0 via
`Cap.node 0`, balance 42) exercises a real refusal write; the rejection lemmas show each guard leg fails
closed. -/

/-- A two-cell kernel for the §5 witnesses: cells 0 and 1 live accounts (lifecycle defaults to Live `0`),
cell 0 owned by actor 0 via `Cap.node 0` (so `stateAuthB … 0 0` holds), cell 0 holding `42` in its
`balance` slot. -/
def kR0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 42)]
    caps := fun c => if c = 0 then [Dregg2.Authority.Cap.node 0, Dregg2.Authority.Cap.node 1] else []
    bal := fun _ _ => 0 }

/-- **NON-VACUITY (the REFUSAL is OBSERVABLE).** The committed refusal STAMPS cell `0`'s `"refusal"` audit
slot to `1` (before: the slot is absent, read as `0`) — the cross-cell SetState refusal commitment
genuinely lands (the `setCell` audit write is real, not a no-op). -/
theorem refusalStmt_stamps :
    (interp (refusalStmt 0 0) kR0).map (fun k => fieldOf "refusal" (k.cell 0)) = some 1 := by
  rw [interp_refusalStmt_eq_kernel]
  decide

/-- **NON-VACUITY (the cell ACTUALLY commits).** The refusal of a Live, self-owned cell COMMITS (`isSome`)
— the three-leg gate genuinely admits. (Pins that the weld's `hexec` hypothesis is satisfiable.) -/
theorem refusalStmt_commits :
    (interp (refusalStmt 0 0) kR0).isSome = true := by
  rw [interp_refusalStmt_eq_kernel]
  decide

/-- **NON-VACUITY (frame: `balance` slot untouched — balance-Δ=0).** Stamping the refusal leaves cell `0`'s
`"balance"` record slot at `42` — the refusal is balance-NEUTRAL (`setField refusalField` writes a slot
DISTINCT from `balance`), exactly the frozen-balance leg of `RefusalSpec`. No value is conjured or
destroyed by a refusal commitment. -/
theorem refusalStmt_balance_frozen :
    (interp (refusalStmt 0 0) kR0).map (fun k => fieldOf "balance" (k.cell 0)) = some 42 := by
  rw [interp_refusalStmt_eq_kernel]
  decide

/-- **NON-VACUITY (frame: a DIFFERENT cell is untouched).** Stamping cell `0`'s refusal leaves cell `1`'s
`"refusal"` slot ABSENT (read as `0`) — `setCell {0}` rewrites ONLY the refusing cell's record, confirming
the write is local (not a global slot collapse). The per-cell frame the full-state `RefusalSpec` pins,
observed. -/
theorem refusalStmt_other_cell_untouched :
    (interp (refusalStmt 0 0) kR0).map (fun k => fieldOf "refusal" (k.cell 1)) = some 0 := by
  rw [interp_refusalStmt_eq_kernel]
  decide

/-- **NON-VACUITY (fail-closed: no authority).** A refusal attempted by actor `5`, who holds NO authority
over cell `0` (empty cap list), does NOT commit — the term returns `none` (the `stateAuthB` cross-cell
SetState authority leg fails). A stranger cannot stamp a refusal into a cell. -/
theorem refusalStmt_rejects_unauthorized :
    interp (refusalStmt 5 0) kR0 = none := by
  rw [interp_refusalStmt_eq_kernel]
  decide

/-- **NON-VACUITY (fail-closed: non-account target).** A refusal targeting a cell NOT in `accounts` (cell
`7`) does NOT commit — the term returns `none` (the MEMBERSHIP leg fails). (Actor `7` owns cell `7` by the
empty-caps `stateAuthB` self-rule, so this isolates the membership leg from the authority leg.) -/
theorem refusalStmt_rejects_nonaccount :
    interp (refusalStmt 7 7) kR0 = none := by
  rw [interp_refusalStmt_eq_kernel]
  decide

/-- **NON-VACUITY (fail-closed: non-Live target).** A refusal into a cell that is NOT Live (lifecycle
discriminant flipped to Sealed `1`) does NOT commit — the term returns `none` (the `cellLive` R6 leg fails;
a refusal commitment cannot be stamped into a dead cell). -/
theorem refusalStmt_rejects_nonlive :
    interp (refusalStmt 0 0) { kR0 with lifecycle := fun _ => 1 } = none := by
  rw [interp_refusalStmt_eq_kernel]
  decide

#assert_axioms refusalStmt_stamps
#assert_axioms refusalStmt_commits
#assert_axioms refusalStmt_balance_frozen
#assert_axioms refusalStmt_other_cell_untouched
#assert_axioms refusalStmt_rejects_unauthorized
#assert_axioms refusalStmt_rejects_nonaccount
#assert_axioms refusalStmt_rejects_nonlive

end Dregg2.Circuit.Argus.Effects.Refusal
