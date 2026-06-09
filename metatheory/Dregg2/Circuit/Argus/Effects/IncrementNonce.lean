/-
# Dregg2.Circuit.Argus.Effects.IncrementNonce — the MONOTONE NONCE-BUMP effect `incrementNonceA`
welded into the Argus IR.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated
it on transfer/mint/burn/createEscrow; `Effects/BalanceA.lean` welded a per-asset move against the v2
`Surface2` FULL-STATE descriptor, and `Effects/Seal.lean` welded a LIST side-table effect against its
own v2 `Surface2` full-state descriptor with the receipt-log prepend carried as the explicit kernel-vs-
runtime divergence. This module welds the genuinely DIFFERENT **per-cell metadata field-write** primitive
`incrementNonceA` (the monotone nonce bump), in a disjoint file (it imports the Argus IR + the audited
`incrementNonceA` v1 `EffectCommit` instance + the cell-state-monotone spec read-only, and owns only its
own declarations).

`incrementNonceA` is the metadata constructor of the FULL op-set executor `execFullA`
(`execFullA s (.incrementNonceA actor cell n) = stateStep s nonceField actor cell (.int n)`,
`TurnExecutorFull.lean:3797`). The verified chained kernel mutator is `stateStep`
(`EffectsState.lean:205`):

    stateStep s nonceField actor cell (.int n)
      = if stateAuthB s.kernel.caps actor cell = true ∧ cell ∈ s.kernel.accounts
           ∧ cellLive s.kernel cell = true then
          some { kernel := writeField s.kernel nonceField cell (.int n),
                 log    := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }
        else none

so a committed bump WRITES `cell`'s `nonce` RECORD field to exactly `n` (`writeField`, touching ONLY
that cell's `nonce` slot, every other cell + every other field FROZEN), prepends one self-targeted
receipt row to the log, and freezes all 16 non-`cell` kernel components. The IR body's move is therefore
the §A **`setCell`** primitive (the per-cell record write — like transfer's, NOT `setBal`/the list
side-tables), with the cell-leaf the declarative `incNonceCellMap` (`cell`'s `nonce` ↦ `n`). That is the
structural contrast carried: the gate is the 3-leg `stateStep` admissibility (authority · membership ·
**lifecycle-liveness/R6** — a write into a Sealed/Destroyed cell FAILS CLOSED), and the move is a
single-cell `nonce`-slot field write.

## THE DESCRIPTOR (a FULL-STATE weld — the STRONG surface, like BalanceA/Seal).

`incrementNonceA` carries its OWN genuine standalone circuit⟺spec crown jewel: in the v1 `EffectCommit`
universe (`Dregg2/Circuit/Inst/incrementNonceA.lean`) the `incrementNonceE` (the `EffectSpec` whose
touched set is `{cell}`, whose expected leaf is `incNonceCellMap`, and whose log GROWS by the
self-targeted row) has soundness

    incrementNonceA_full_sound : satisfiedE S incrementNonceE (encodeE S incrementNonceE s args s')
                                   ⟹ IncrementNonceSpec s actor cell n s'

— a FULL **17-kernel-field + receipt-log** declarative post-state soundness (the four frame-forcing EQ
gates bind the whole frame ∧ the touched cell ∧ the log), whose executor corner is the independent
`execFullA_incrementNonce_iff_spec` (`Spec/cellstatemonotone.lean`). So — exactly like BalanceA/Seal —
this module welds the FULL-STATE `incrementNonceA_full_sound` DIRECTLY against the Argus term, concluding
the WHOLE `IncrementNonceSpec` agreement (strictly stronger than the per-cell EffectVM weld
`Emit/EffectVmEmitIncrementNonce.incNonceDescriptor_classA` would give).

The HONEST chained-vs-kernel divergence carried explicitly (the task's `divergence` field, NOT papered):
the Argus `RecStmt`/`interp` runs on the bare `RecordKernelState`, so the cornerstone (§2) pins the
KERNEL fragment of the bump — the `nonce`-slot `writeField` — and is then LIFTED (§3) to the chained
`execFullA`/`stateStep` over `RecChainedState`, where the chained layer adds exactly the **receipt-log
prepend** (`{actor, cell, cell, 0} :: s.log`). That log-prepend is the kernel-vs-runtime divergence,
carried as an explicit equality leg in the §3 lift (`interp_incrementNonceStmt_chained`), exactly as
`Seal`/`BalanceA` carry their chained-layer addenda.

### THE NONCE-PROLOGUE DIVERGENCE (the hint's systemic concern) — why it does NOT enter THIS weld.

The runtime EffectVM row for `incrementNonce` (the v2 `Emit` descriptor) ticks an ON-TRACE per-cell
SEQUENCE nonce (`state.NONCE += 1` via the global gate), which the cell-record `nonce` field write is
DISTINCT from — the `incNonceDescriptor_classA` capstone carries that on-trace-seq-nonce-tick vs
record-nonce-write as a NAMED residual, and a parallel closer is handling the systemic turn-prologue
single-tick reconciliation (`Argus.Nonce`). This module does NOT weld the v2 per-cell EffectVM row; it
welds the v1 FULL-STATE `IncrementNonceSpec`, where the nonce semantics is the FAITHFUL record-field
write (`cell`'s `nonce` ↦ `n`), captured EXACTLY by `incNonceCellMap` — NO collapsed nonce field, NO
turn-prologue tick reconciliation in the statement. So the only divergence the welded conclusion carries
is the §3 receipt-log prepend; the nonce-prologue concern is OUT of scope here (reported honestly, not
faked into the weld).

## Honesty

`#assert_axioms` on every headline theorem ⊆ {propext, Classical.choice, Quot.sound}; the Poseidon-CR /
cell-leaf / rest-frame / log-hash injectivity assumptions enter ONLY inside the reused
`incrementNonceA_full_sound` (its `compressNInjective`/`cellLeafInjective`/`RestHashIffFrame`/
`logHashInjective` portal hypotheses + the `AccountsWF` well-formedness side-conditions), not in the
welded conclusion's statement. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only; this
file owns only itself. Build: `lake build Dregg2.Circuit.Argus.Effects.IncrementNonce`.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Inst.incrementNonceA
import Dregg2.Circuit.Spec.cellstatemonotone
import Dregg2.Circuit.Emit.EffectVmEmitIncrementNonceFullState

namespace Dregg2.Circuit.Argus.Effects.IncrementNonce

open Dregg2.Exec
open Dregg2.Exec.EffectsState
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Argus (RecStmt interp)
-- Broad opens mirroring `Inst/incrementNonceA.lean` / `Spec/cellstatemonotone.lean` so the standalone-
-- descriptor + spec + executor-corner names resolve unqualified: the CR/frame/log carriers in
-- `StateCommit`; the v1 framework `CommitSurface`/`satisfiedE`/`encodeE` in `EffectCommit`; the v1
-- `incrementNonceE` descriptor + its `incrementNonceA_full_sound` (FULL `IncrementNonceSpec`) in
-- `Inst.IncrementNonceA`; the independent declarative spec + executor corner + the cell-write helper in
-- `Spec.CellStateMonotone`.
open Dregg2.Circuit.StateCommit
  (compressNInjective cellLeafInjective RestHashIffFrame logHashInjective AccountsWF)
open Dregg2.Circuit.EffectCommit (CommitSurface satisfiedE encodeE)
open Dregg2.Circuit.Inst.IncrementNonceA (IncrementNonceArgs incrementNonceE incrementNonceA_full_sound)
open Dregg2.Circuit.Spec.CellStateMonotone
  (IncrementNonceSpec incNonceGuard incNonceCellMap incNonceCellMap_eq_writeField
   incrementNonce_cellWrite_correct execFullA_incrementNonce_iff_spec)

/-! ## §1 — The incrementNonceA effect as an Argus IR term (gate, then the `setCell` `nonce`-slot write).

`stateStep`'s kernel content is `if <3-conjunct guard> then writeField k nonceField cell (.int n)`. We
capture it term-for-term over the bare `RecordKernelState`: a `Bool` `guard` of the EXACT 3 conjuncts
(authority over `cell` · `cell` a live account · `cell`'s lifecycle admits effects — the R6 gate), then
a `setCell {cell}` whose leaf is the declarative `incNonceCellMap` (`cell`'s `nonce` slot ↦ `n`, every
other cell whole). The contrast with the seal/escrow list side-tables is the move primitive: `setCell`
(rewrites one cell's record) over the `nonce`-slot field write, NOT `setSealedBoxes`/`setEscrows`/`setBal`. -/

/-- The incrementNonceA admissibility gate as a `Bool` — exactly `stateStep`'s `if` (the 3 conjuncts:
authority over `cell` via `stateAuthB`, `cell` a live account, and `cell`'s lifecycle admits effects via
`cellLive` — the R6 lifecycle gate). The metadata-domain analog of `transferGuard`/`balanceAGuard`. -/
def incrementNonceGuardB (actor cell : CellId) (k : RecordKernelState) : Bool :=
  stateAuthB k.caps actor cell
    && decide (cell ∈ k.accounts)
    && cellLive k cell

/-- **The incrementNonceA effect as an IR term: gate, then write `cell`'s `nonce` slot.** Mirrors
`transferStmt` (gate, then a `setCell` move) but the cell-leaf is the metadata field write
`incNonceCellMap` — `cell`'s `nonce` ↦ `n`, every other cell whole — NOT `recTransfer` (transfer's
balance move). The `setCell {cell}` leaf is `incNonceCellMap k cell n`, EXACTLY the post-cell map
`stateStep`'s `writeField nonceField` installs. -/
def incrementNonceStmt (actor cell : CellId) (n : Int) : RecStmt :=
  RecStmt.seq (RecStmt.guard (incrementNonceGuardB actor cell))
    (RecStmt.setCell ({cell} : Finset CellId) (fun k c => incNonceCellMap k cell n c))

/-! ## §2 — The cornerstone: `interp` of the incrementNonceA term IS the KERNEL fragment of `stateStep`.

The Argus `interp` runs on the bare `RecordKernelState`. `stateStep`'s kernel post is exactly
`writeField k nonceField cell (.int n)` under the 3-conjunct guard. We pin that the IR term commits to
PRECISELY that kernel state (or rejects in lock-step). This is the metadata analog of
`interp_transferStmt_eq_recKExec` / `interp_sealStmt_eq_sealKernel`. -/

/-- The kernel fragment of a committed `stateStep`/`incrementNonceA`: the `nonce`-slot `writeField` on
the bare kernel, nothing else (the receipt-log prepend lives at the chained layer — §3). Named
declaratively so the cornerstone target is the genuine kernel move (no `stateStep` term in the body). -/
def incNonceKernel (actor cell : CellId) (n : Int) (k : RecordKernelState) :
    Option RecordKernelState :=
  if stateAuthB k.caps actor cell = true ∧ cell ∈ k.accounts ∧ cellLive k cell = true then
    some (writeField k nonceField cell (.int n))
  else none

/-- The incrementNonceA `Bool` gate decodes to `stateStep`'s 3-conjunct admissibility proposition (the
SAME conjuncts the kernel `if` checks). The metadata analog of `transferGuard_iff`/`balanceAGuard_iff`. -/
theorem incrementNonceGuardB_iff (actor cell : CellId) (k : RecordKernelState) :
    incrementNonceGuardB actor cell k = true ↔
      (stateAuthB k.caps actor cell = true ∧ cell ∈ k.accounts ∧ cellLive k cell = true) := by
  simp only [incrementNonceGuardB, Bool.and_eq_true, decide_eq_true_eq]
  tauto

/-- **The `setCell {cell}` `nonce` write map collapses to `incNonceCellMap k cell n`** (the single-cell
map of `stateStep`'s kernel post). The `setCell` interp lays `fun c => if c ∈ {cell} then incNonceCellMap
k cell n c else k.cell c`; off `{cell}` the map is the identity — `incNonceCellMap`'s `else` — so the
`{cell}`-membership guard is redundant. The metadata analog of `transferCellMap_eq`. -/
theorem incNonceCellMap_setCell_eq (cell : CellId) (n : Int) (k : RecordKernelState) :
    (fun c => if c ∈ ({cell} : Finset CellId) then incNonceCellMap k cell n c else k.cell c)
      = incNonceCellMap k cell n := by
  funext c
  by_cases hc : c = cell
  · simp only [hc, Finset.mem_singleton, if_pos]
  · have hcs : c ∉ ({cell} : Finset CellId) := by simp only [Finset.mem_singleton]; exact hc
    rw [if_neg hcs]
    simp only [incNonceCellMap, if_neg hc]

/-- **`incNonceKernel`'s commit value IS `stateStep`'s kernel post** (`= writeField k nonceField cell
(.int n)`), restated as the `{ k with cell := incNonceCellMap k cell n }` record-update so the cornerstone
matches the `setCell` interp shape by `rfl`. The `incNonceCellMap` map IS `(writeField nonceField).cell`
(`incNonceCellMap_eq_writeField`), and `writeField` touches only `.cell`, so the two are defeq. -/
theorem writeField_nonce_eq (cell : CellId) (n : Int) (k : RecordKernelState) :
    writeField k nonceField cell (.int n) = { k with cell := incNonceCellMap k cell n } := rfl

/-- **The cornerstone (metadata field write, kernel fragment).** `interp` of the incrementNonceA term IS
the kernel step `incNonceKernel` — the same partial function, by construction, exactly as the transfer/
seal cornerstones, now over a single-cell `nonce`-slot field write via `setCell`/`incNonceCellMap` (NOT
the per-asset `setBal` or the list side-tables). The executor IS the meaning of the term. -/
theorem interp_incrementNonceStmt_eq_incNonceKernel (actor cell : CellId) (n : Int)
    (k : RecordKernelState) :
    interp (incrementNonceStmt actor cell n) k = incNonceKernel actor cell n k := by
  simp only [incrementNonceStmt, interp]
  unfold incNonceKernel
  by_cases hg : incrementNonceGuardB actor cell k = true
  · -- ADMIT: the guard's `interp` fires (`some k`); the `setCell` move lays the `nonce`-slot map, which
    -- IS `(writeField nonceField).cell` (`incNonceCellMap_setCell_eq`), so the post-record is exactly
    -- `writeField k nonceField cell (.int n)`. The RHS `if` opens on the decoded 3-conjunct Prop.
    rw [if_pos hg]
    simp only [Option.bind]
    rw [if_pos ((incrementNonceGuardB_iff actor cell k).mp hg)]
    -- the laid `.cell` map collapses to `incNonceCellMap k cell n` (`incNonceCellMap_setCell_eq`); restate
    -- `stateStep`'s kernel post `writeField …` as the SAME `{ k with cell := incNonceCellMap k cell n }`
    -- record-update (`writeField_nonce_eq`). Both records are then syntactically identical (`rfl`).
    show (some { k with cell := fun c => if c ∈ ({cell} : Finset CellId)
                          then incNonceCellMap k cell n c else k.cell c }) = _
    rw [incNonceCellMap_setCell_eq, writeField_nonce_eq]
  · -- REJECT: the guard fails ⇒ `none.bind _ = none`; the RHS `if` closes on the (negated) decoded Prop.
    rw [if_neg hg]
    simp only [Option.bind]
    rw [if_neg (fun hp => hg ((incrementNonceGuardB_iff actor cell k).mpr hp))]

#assert_axioms interp_incrementNonceStmt_eq_incNonceKernel

/-! ## §3 — Lifting the cornerstone to the CHAINED executor `stateStep` / `execFullA`.

The standalone descriptor (§4) is keyed on the CHAINED executor `execFullA` / `stateStep` over
`RecChainedState` (kernel + receipt log) — the arm `execFullA s (.incrementNonceA actor cell n) =
stateStep s nonceField actor cell (.int n)`. The §2 cornerstone is over the bare KERNEL step
`incNonceKernel`. The chained layer is exactly `incNonceKernel` PLUS the receipt-log prepend
`{actor, cell, cell, 0} :: s.log` (a self-targeted metadata-advance row). We bridge faithfully, CARRYING
that log-prepend as an explicit equality leg — the honest kernel-vs-chained (kernel-vs-runtime)
divergence, NOT papered. -/

/-- **`interp_incrementNonceStmt_chained` — the IR term's executor, lifted to the chained `execFullA`.**
When the §2 cornerstone commits on the kernel (`interp (incrementNonceStmt actor cell n) st.kernel =
some k'`), the unified action executor `execFullA st (.incrementNonceA actor cell n)` commits to the
chained state `⟨k', {actor, cell, cell, 0} :: st.log⟩`. So the Argus term's kernel meaning lifts to the
chained executor the standalone descriptor speaks about, with the receipt-log prepend made EXPLICIT — the
one place the chained runtime does more than the bare-kernel Argus term (the carried divergence). -/
theorem interp_incrementNonceStmt_chained
    (st : RecChainedState) (actor cell : CellId) (n : Int) (k' : RecordKernelState)
    (hexec : interp (incrementNonceStmt actor cell n) st.kernel = some k') :
    execFullA st (.incrementNonceA actor cell n)
      = some { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := 0 } :: st.log } := by
  -- the §2 cornerstone turns the IR term into the kernel step `incNonceKernel`.
  rw [interp_incrementNonceStmt_eq_incNonceKernel] at hexec
  -- `execFullA st (.incrementNonceA …)` reduces to `stateStep st nonceField actor cell (.int n)`; unfold
  -- both and split on the SAME 3-conjunct guard. On admit, `incNonceKernel` named the kernel post as
  -- `some k'`, and the chained post adds exactly the receipt row; on reject both are `none`.
  show stateStep st nonceField actor cell (.int n)
        = some { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := 0 } :: st.log }
  unfold stateStep incNonceKernel at *
  by_cases hg : stateAuthB st.kernel.caps actor cell = true ∧ cell ∈ st.kernel.accounts
      ∧ cellLive st.kernel cell = true
  · rw [if_pos hg] at hexec ⊢
    simp only [Option.some.injEq] at hexec
    rw [← hexec]
  · rw [if_neg hg] at hexec
    exact absurd hexec (by simp)

#assert_axioms interp_incrementNonceStmt_chained

/-! ## §4 — THE COMPILE WELD: a satisfying witness of incrementNonceA's OWN standalone circuit agrees
with the FULL post-state the IR term's executor interpretation produces.

This welds against incrementNonceA's GENUINE standalone descriptor `incrementNonceE` (the v1
`EffectCommit` full-state circuit whose soundness is `incrementNonceA_full_sound`), the BalanceA/Seal
pattern. The executor side is routed through §3 (`interp` ⟹ `execFullA`) and the independent
`execFullA_incrementNonce_iff_spec` (executor ⟺ `IncrementNonceSpec`); the circuit side is the audited
`incrementNonceA_full_sound` (circuit ⟹ `IncrementNonceSpec`). Both name the SAME `IncrementNonceSpec`,
so they PROVABLY agree on the WHOLE 17-kernel-field state (the `nonce`-slot bump + all 16 frozen fields)
AND the receipt log — strictly stronger than a per-cell EffectVM weld. -/

/-- The Argus circuit interpretation of an `incrementNonceA` term: incrementNonceA's OWN audited
standalone v1 `EffectCommit` full-state circuit step — the four-frame-EQ arithmetization
`satisfiedE S incrementNonceE (encodeE …)` satisfied on the encoded `(s, args, s')` triple, with
`args := ⟨actor, cell, n⟩`. Its soundness `incrementNonceA_full_sound` pins the complete
`IncrementNonceSpec`. The `incrementNonceA`-keyed analog of `BalanceA`'s `balanceACircuit` / `Seal`'s
`sealCircuit`, in the v1 descriptor universe where incrementNonceA carries its OWN genuine full-state
circuit. -/
def incrementNonceCircuit (S : CommitSurface) (s : RecChainedState) (actor cell : CellId) (n : Int)
    (s' : RecChainedState) : Prop :=
  satisfiedE S incrementNonceE
    (encodeE S incrementNonceE s ({ actor := actor, cell := cell, n := n } : IncrementNonceArgs) s')

/-- **`incrementNonceSpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH
satisfy `IncrementNonceSpec s actor cell n ·` are equal. Rather than re-derive this field-by-field, we
route through the PROVEN executor⟺spec corner `execFullA_incrementNonce_iff_spec`: each
`IncrementNonceSpec` reconstructs the SAME committed value `execFullA s (.incrementNonceA actor cell n) =
some ·`, and `some` is injective. This is exactly the sense in which `IncrementNonceSpec` is functional —
it determines the post-state — so the circuit-side and executor-side spec facts collapse to one welded
post-state. -/
theorem incrementNonceSpec_unique {s s₁ s₂ : RecChainedState} {actor cell : CellId} {n : Int}
    (h₁ : IncrementNonceSpec s actor cell n s₁) (h₂ : IncrementNonceSpec s actor cell n s₂) :
    s₁ = s₂ := by
  have e₁ : execFullA s (.incrementNonceA actor cell n) = some s₁ :=
    (execFullA_incrementNonce_iff_spec s actor cell n s₁).mpr h₁
  have e₂ : execFullA s (.incrementNonceA actor cell n) = some s₂ :=
    (execFullA_incrementNonce_iff_spec s actor cell n s₂).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- **`incrementNonce_compile_sound` — the welded soundness (incrementNonceA slice), against
incrementNonceA's OWN descriptor.**

Suppose, for the Argus incrementNonceA term `incrementNonceStmt actor cell n`:
  * the standalone incrementNonceA circuit `incrementNonceCircuit S s actor cell n s'` (= `incrementNonceE`'s
    full-state v1 four-frame-EQ arithmetization satisfied on the encoded triple) holds, under the
    realizable portals (`hN : compressNInjective S.compressN` — the sponge over leaves; `hL :
    cellLeafInjective S.CH` — the per-cell leaf binds its whole `Value`; `hRest : RestHashIffFrame S.RH`
    — the 16-non-`cell`-field rest hash; `hLog : logHashInjective S.LH` — the growing receipt log) and the
    well-formedness side-conditions (`hwf : AccountsWF s.kernel`, `hwf' : AccountsWF s'.kernel`);
  * the IR term's EXECUTOR interpretation COMMITS on the kernel: `interp (incrementNonceStmt actor cell n)
    s.kernel = some k'` (`hexec`).

Then the chained post-state the circuit pins is EXACTLY the chained post-state the IR term's executor
produces: `s' = { kernel := k', log := {actor, cell, cell, 0} :: s.log }`. I.e. incrementNonceA's OWN
circuit and the IR term AGREE on the WHOLE 17-kernel-field state (`cell`'s `nonce` slot ↦ `n`, every other
cell whole, all 16 non-`cell` components — INCLUDING `bal` and `caps` — frozen) AND the receipt log (grown
by exactly the one self-targeted row — the §3 carried kernel-vs-chained divergence). So the circuit the
prover runs for incrementNonceA pins the complete state the IR term's executor produces. -/
theorem incrementNonce_compile_sound
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s s' : RecChainedState) (actor cell : CellId) (n : Int) (k' : RecordKernelState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (hcirc : incrementNonceCircuit S s actor cell n s')
    (hexec : interp (incrementNonceStmt actor cell n) s.kernel = some k') :
    s' = { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log } := by
  -- circuit side: incrementNonceA's OWN audited soundness forces the FULL `IncrementNonceSpec` on
  -- `(s, ⟨actor,cell,n⟩, s')`.
  have hspec : IncrementNonceSpec s actor cell n s' :=
    incrementNonceA_full_sound S hN hL hRest hLog s
      ({ actor := actor, cell := cell, n := n } : IncrementNonceArgs) s' hwf hwf' hcirc
  -- executor side: the §3 chained lift gives `execFullA s (.incrementNonceA …) = some ⟨k', row :: log⟩`,
  -- and the independent executor⟺spec corner turns THAT into `IncrementNonceSpec s actor cell n ⟨k', …⟩`.
  have hspec' : IncrementNonceSpec s actor cell n
      { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log } :=
    (execFullA_incrementNonce_iff_spec s actor cell n _).mp
      (interp_incrementNonceStmt_chained s actor cell n k' hexec)
  -- both states satisfy the SAME spec ⇒ they are the same state (the spec pins every kernel field + log).
  exact incrementNonceSpec_unique hspec hspec'

#assert_axioms incrementNonce_compile_sound

/-! ## §5 — NON-VACUITY: the IR term genuinely BUMPS the nonce (observable), FREEZES the value/caps, and
the gate REJECTS forged inputs (fail-closed on each leg).

The cornerstone/weld would be hollow if incrementNonceA never committed, if the bump were a no-op, if it
silently moved value/caps, or if the gate admitted everything. A concrete two-account kernel `kN0` (cells
0,1 live; cell 0 holds a `nonce` slot at `5` and a `balance` at `30`) exercises a real bump; the rejection
lemmas show each guard leg fails closed. -/

/-- A concrete kernel for the witnesses: cells 0 and 1 are live accounts (lifecycle defaults Live `0`),
cell 0's record carries `balance = 30` and `nonce = 5`; cell 1 is empty. -/
def kN0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun c => if c = 0 then .record [("balance", .int 30), ("nonce", .int 5)]
                     else .record [("balance", .int 0)]
    caps := fun _ => [] }

/-- **NON-VACUITY (the BUMP is OBSERVABLE).** The committed bump writes cell `0`'s `nonce` slot to exactly
`7` (here `n = 7`) — a real, observable metadata advance (the `setCell`/`incNonceCellMap` write lands). -/
theorem incrementNonceStmt_bumps :
    (interp (incrementNonceStmt 0 0 7) kN0).map (fun k => fieldOf nonceField (k.cell 0)) = some 7 := by
  rw [interp_incrementNonceStmt_eq_incNonceKernel]
  decide

/-- **NON-VACUITY (the VALUE is FROZEN — regime balance-Δ=0).** The committed bump leaves cell `0`'s
`balance` field at `30` — a metadata bump moves NO value (the `nonce` write touches only the `nonce`
slot). The anti-ghost tooth on the conserved balance dimension. -/
theorem incrementNonceStmt_freezes_balance :
    (interp (incrementNonceStmt 0 0 7) kN0).map (fun k => balOf (k.cell 0)) = some 30 := by
  rw [interp_incrementNonceStmt_eq_incNonceKernel]
  decide

/-- **NON-VACUITY (OTHER cells FROZEN).** The bump of cell `0` leaves cell `1`'s record untouched
(`balance` still `0`) — the write is single-cell, every other cell whole. -/
theorem incrementNonceStmt_freezes_other_cell :
    (interp (incrementNonceStmt 0 0 7) kN0).map (fun k => balOf (k.cell 1)) = some 0 := by
  rw [interp_incrementNonceStmt_eq_incNonceKernel]
  decide

/-- **NON-VACUITY (fail-closed: unauthorized).** A bump by an actor with NO authority over `cell` does
NOT commit — the term returns `none` (the AUTHORITY leg of the gate fails). Here cell `0`'s cap table is
empty, so actor `2` holds no authority over a DIFFERENT target cell `1` (the `stateAuthB` self-targeted
gate over `cell 1` is closed). No nonce is advanced without authority. -/
theorem incrementNonceStmt_rejects_unauthorized :
    interp (incrementNonceStmt 2 1 7) kN0 = none := by
  rw [interp_incrementNonceStmt_eq_incNonceKernel]
  decide

/-- **NON-VACUITY (fail-closed: non-account).** A bump targeting a `cell` that is NOT a live account
(here cell `9`, outside `accounts = {0,1}`) does NOT commit — the MEMBERSHIP leg fails. -/
theorem incrementNonceStmt_rejects_nonaccount :
    interp (incrementNonceStmt 9 9 7) kN0 = none := by
  rw [interp_incrementNonceStmt_eq_incNonceKernel]
  decide

/-- A SEALED-cell kernel: `kN0` with cell `0`'s lifecycle flipped to Sealed (`1`) — every other field as
`kN0` (cell `0` still an account, still cap-empty, still holding its `nonce`/`balance`). -/
def kN0Sealed : RecordKernelState :=
  { kN0 with lifecycle := fun c => if c = 0 then 1 else kN0.lifecycle c }

/-- **NON-VACUITY (fail-closed: R6 lifecycle).** A bump into a SEALED cell (`cell 0`, lifecycle `1`) does
NOT commit — the LIVENESS leg (`cellLive`, the R6 gate) fails. This is the executor-level lifecycle
enforcement the bare-kernel cornerstone preserves: a nonce write into a sealed cell is REJECTED, even
though the actor would be authorized and the cell is an account. -/
theorem incrementNonceStmt_rejects_sealed :
    interp (incrementNonceStmt 0 0 7) kN0Sealed = none := by
  rw [interp_incrementNonceStmt_eq_incNonceKernel]
  decide

#assert_axioms incrementNonceStmt_bumps
#assert_axioms incrementNonceStmt_freezes_balance
#assert_axioms incrementNonceStmt_freezes_other_cell
#assert_axioms incrementNonceStmt_rejects_unauthorized
#assert_axioms incrementNonceStmt_rejects_nonaccount
#assert_axioms incrementNonceStmt_rejects_sealed

end Dregg2.Circuit.Argus.Effects.IncrementNonce
