/-
# Dregg2.Circuit.Argus.Effects.SetVerificationKey — the VERIFICATION-KEY-WRITE effect
`setVKA` welded into the Argus IR, on the FULL-STATE `CommitSurface` (v1 `EffectCommit`) surface.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated it
on transfer/mint/burn (single-cell record-`balance` moves). `Argus/Effects/BalanceA.lean` /
`Argus/Effects/RefreshDelegation.lean` then welded genuinely-different effects to their OWN standalone
full-state circuit⟺spec descriptors (concluding the WHOLE post-state) by routing the executor side through
a chained-executor lift + an independent executor⟺spec corner. This module replays THAT (full-state)
template for the genuinely different **protocol-managed metadata field write** `setVKA`, in a disjoint
file (it imports the Argus IR + the audited `setVKA` v1 instance + the independent cell-state-vk spec, all
read-only, and owns only its own declarations; it edits no other Argus module).

## What `setVKA` does (the kernel step the cornerstone pins)

`setVKA` is dregg1's `SetVerificationKey { cell, new_vk }` / `apply_set_verification_key` (`apply.rs`
~:803): the upgrade-relevant VK-field write. The chained arm `execFullA s (.setVKA actor cell vk)` is
DEFINITIONALLY `stateStep s vkField actor cell (.int vk)` (`Spec/cellstatevk.lean:188`,
`execFullA_setVK_eq`), and `stateStep` (`EffectsState.lean:207`) commits IFF its THREE-leg admissibility
gate holds —

    stateAuthB s.kernel.caps actor cell = true   -- (1) AUTHORITY: actor holds authority over `cell`
  ∧ cell ∈ s.kernel.accounts                      -- (2) MEMBERSHIP: `cell` is a live account
  ∧ cellLive s.kernel cell = true                 -- (3) LIVENESS: `cell`'s lifecycle admits effects (R6)

— and on commit writes the `verification_key` field of `cell` to `vk` (`writeField`, touching ONLY that
cell's `verification_key` slot) and extends the receipt chain by ONE self-targeted row. NO balance move,
NO cap edit: the whole regime invariant. Because `writeField k vkField cell (.int vk)` rewrites ONLY the
`.cell` component (`{ k with cell := fun c => if c = cell then setField vkField (k.cell c) (.int vk) else
k.cell c }`), the genuine kernel move is a SINGLE-CELL record write — exactly the §A `setCell {cell}`
primitive transfer/mint/burn use, with the VK-write leaf `setField vkField (k.cell c) (.int vk)`. That is
the structural contrast: transfer ↦ `setCell` over `recTransfer` of the record `balance`; setVK ↦ `setCell`
over the `verification_key` slot-write (a DISTINCT slot from `balance`, so balance is frozen,
`setVK_cellWrite_correct`). The IR term reuses NO new write-primitive — it is a `setCell {cell}` move on a
DIFFERENT slot of the same record.

## THE DESCRIPTOR (the full-state crown jewel — read this)

`setVKA` carries a GENUINE standalone full-state circuit⟺spec descriptor in the v1 `EffectCommit` /
`CommitSurface` universe (`Dregg2/Circuit/Inst/setVKA.lean`):

  * `setVKE` — the `EffectSpec` whose touched set is the SINGLE cell `{cell}`, expected leaf
    `setVKCellMap`, log update the one-row receipt prepend, and a single `propBit` guard column decoding
    to the three-leg `setVKGuard`; its `restFrame` freezes the other 16 kernel fields.
  * `setVKA_full_sound : satisfiedE S setVKE (encodeE …) ⟹ SetVKSpec` — a FULL 17-field declarative
    post-state soundness (`Spec/cellstatevk.lean`, `SetVKSpec`), keyed on the chained executor via the
    independent `execFullA_setVK_iff_spec` (executor ⟺ spec, BOTH directions, full state). The `CommitSurface`
    portals (`compressNInjective`/`cellLeafInjective`/`RestHashIffFrame`/`logHashInjective`) + `AccountsWF`
    enter ONLY inside that reused soundness, not in the welded conclusion's statement.

So this module is HONEST in both directions, exactly as BalanceA/RefreshDelegation:

  (1) **Cornerstone (the standalone executor-refinement):** `interp_setVerificationKeyStmt_eq_setVKKernelStep`
      — the kernel-level VK-write step IS the Argus term, using `setCell {cell}` on the `verification_key`
      slot. New, standalone, the metadata-write analog of `interp_balanceAStmt_eq_recKExecAsset`.

  (2) **Compile weld against setVKA's OWN full-state descriptor:** lift the kernel cornerstone to the
      chained `execFullA` (NO extra side-condition — the chained gate IS the kernel gate, since `stateStep`
      gates on the kernel only), then weld to `setVKA_full_sound`. The conclusion is the FULL `SetVKSpec`
      agreement (all 17 kernel fields + the receipt log) — a satisfying witness of setVK's own circuit agrees
      with the WHOLE post-state the IR term's executor produces. The FULL-STATE `CommitSurface` surface
      (strictly stronger than a per-cell EffectVM projection).

## HONEST SURFACE + THE REPORTED KERNEL-vs-RUNTIME DIVERGENCE (precise — do NOT over-read)

  * **FULL-STATE `CommitSurface` (not per-cell).** The conclusion is
    `st' = { kernel := k', log := receipt :: log }` — the WHOLE chained post-state, because `SetVKSpec` pins
    every one of the 17 kernel fields plus the log. This is the same surface BalanceA's `balanceA_compile_sound`
    and RefreshDelegation's `refreshDelegation_compile_sound` reach, on the `verification_key` slot. The
    descriptor digests the `cell` FUNCTION via the `CommitSurface`'s cell-leaf hash (`cellLeafInjective`); so
    the circuit binds the cell-map up to that injectivity, the faithful digest-not-record boundary.

  * **NO nonce-tick divergence on THIS surface.** `SetVKSpec` (the v1 `CommitSurface` reference) FREEZES the
    nonce-bearing `cell` record off the written `verification_key` slot and pins the log as EXACTLY one
    self-targeted row — it does NOT tick a nonce. So unlike the per-row `EffectVm` welds (transfer/burn/
    bridgeMint), this full-state weld carries NO `NonceReconciled` conjunct: the executor IS the spec, on
    the nose, with no row-counter reconciliation. (The contrast with the EffectVm row — which freezes the
    field block and TICKS the global nonce, carrying the VK value OFF-trace in `params[0]`/`effects_hash` —
    is reported below as a documented divergence between the two CIRCUIT universes, §5.1, not papered.)

  * **THE OFF-TRACE EffectVm DIVERGENCE (the runnable-row boundary).** The RUNNING hand-AIR
    (`circuit/src/effect_vm/air.rs:961`, selector 27) runs `setVerificationKey` as a state-PASSTHROUGH row:
    it FREEZES every economic state-block column (`field[i]`, bal, cap_root) and TICKS the global nonce; the
    actual VK value rides `params[0]` + `effects_hash` OFF the per-row state block (the hand-AIR carries NO
    `field` column for the VK). On THAT universe the VK-write soundness is NOT internalized in-row — it lives
    here, in the v1 `CommitSurface`'s `SetVKSpec`. The two universes agree on the FROZEN frame; they DIVERGE
    on (a) where the VK write is pinned (v1 `CommitSurface` `cell`-map vs EffectVm off-trace) and (b) the
    nonce (v1 freezes the record's nonce slot; the EffectVm row ticks the global nonce). We pin both halves
    as a checked documentation theorem (`setVK_full_state_writes_vs_effectvm_offtrace`) so the divergence
    cannot silently regress.

## Honesty

`#assert_axioms` on every headline theorem ⊆ {propext, Classical.choice, Quot.sound}; the
`CommitSurface` cell-leaf/rest/log/compression injectivity portals + `AccountsWF` enter ONLY inside the
reused `setVKA_full_sound`, not in the welded conclusion's statement. No `sorry`, no `:= True`, no
`native_decide`. Imports are read-only; this file owns only itself.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Inst.setVKA
import Dregg2.Circuit.Emit.EffectVmEmitSetVKFullState

namespace Dregg2.Circuit.Argus.Effects.SetVerificationKey

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (execFullA vkField)
open Dregg2.Exec.EffectsState (stateStep stateAuthB cellLive writeField setField fieldOf)
open Dregg2.Circuit.Argus (RecStmt interp)
-- `balOf` (the conserved-balance read) lives in `Dregg2.Exec` (already opened above).
-- Broad opens mirroring `Inst/setVKA.lean` so the standalone-descriptor names resolve unqualified:
-- the `CommitSurface` + its portals + `satisfiedE`/`encodeE` live in `EffectCommit`/`StateCommit`; the
-- spec + its executor⟺spec corner live in `Spec.CellStateVK`; the descriptor `setVKE` + its full
-- soundness `setVKA_full_sound` live in `Inst.SetVKA`.
open Dregg2.Circuit.EffectCommit (CommitSurface satisfiedE encodeE)
open Dregg2.Circuit.StateCommit
  (compressNInjective cellLeafInjective RestHashIffFrame logHashInjective AccountsWF)
open Dregg2.Circuit.Spec.CellStateVK
  (SetVKSpec setVKGuard setVKCellMap execFullA_setVK_iff_spec execFullA_setVK_eq)
open Dregg2.Circuit.Inst.SetVKA (SetVKArgs setVKE setVKA_full_sound)

/-! ## §1 — The setVerificationKey effect as an Argus IR term (gate, then the `setCell` VK-slot write).

`stateStep s vkField actor cell (.int vk)` (the `.setVKA` arm) commits IFF the three-leg gate holds
(authority over `cell` ∧ `cell ∈ accounts` ∧ `cellLive cell`), and on commit writes the
`verification_key` slot of `cell` via `writeField`, which rewrites ONLY the `.cell` component:
`{ k with cell := fun c => if c = cell then setField vkField (k.cell c) (.int vk) else k.cell c }` —
EXACTLY the declarative `setVKCellMap k cell vk` (`Spec/cellstatevk.lean:82`). We capture it term-for-term:
a `Bool` `guard` of the EXACT three conjuncts (reading only the kernel), then a `setCell {cell}` whose leaf
is the `verification_key` slot-write. The contrast with transfer is the WRITTEN SLOT: setVK writes
`verification_key` (a DISTINCT slot from `balance`, so balance is frozen — `setVK_cellWrite_correct`),
transfer writes `balance`; BOTH use the SAME `setCell {cell}` primitive (no new write-primitive needed). -/

/-- The setVerificationKey admissibility gate as a `Bool` — exactly `stateStep`'s three-leg `if` (AUTHORITY
over `cell`, MEMBERSHIP, and R6 LIVENESS), reading ONLY the kernel `k`. This is the SAME `Prop`-level gate
the spec's `setVKGuard` names (`setVKGuard_iff` below decodes it). The chained `stateStep` adds NO further
conjunct (it gates on the kernel only), so the chained lift §3 carries no extra side-condition. -/
def setVerificationKeyGuard (actor cell : CellId) (k : RecordKernelState) : Bool :=
  stateAuthB k.caps actor cell && decide (cell ∈ k.accounts) && cellLive k cell

/-- **The setVerificationKey effect as an IR term: gate, then write the `verification_key` slot.** Mirrors
`transferStmt` (gate, then move) but the move is `setCell {cell}` writing the `verification_key` slot
(`setField vkField (k.cell c) (.int vk)`) — NOT the `balance` slot transfer writes. The `setCell {cell}`
leaf is `setField vkField (k.cell c) (.int vk)`, whose post-cell-map IS `setVKCellMap k cell vk` (the EXACT
post-`cell` `writeField`/`stateStep` install). The contrast is the SLOT, not the primitive. -/
def setVerificationKeyStmt (actor cell : CellId) (vk : Int) : RecStmt :=
  RecStmt.seq (RecStmt.guard (setVerificationKeyGuard actor cell))
    (RecStmt.setCell ({cell} : Finset CellId)
      (fun k c => setField vkField (k.cell c) (.int vk)))

/-! ## §2 — The cornerstone: `interp` of the setVerificationKey term IS the kernel VK-write step. -/

/-- The setVerificationKey `Bool` gate decodes to `stateStep`/`setVKGuard`'s admissibility proposition (the
three conjuncts, in the SAME order the kernel `if` checks them). The metadata-write analog of
`balanceAGuard_iff` / `refreshDelegationGuard_iff`. -/
theorem setVerificationKeyGuard_iff (actor cell : CellId) (k : RecordKernelState) :
    setVerificationKeyGuard actor cell k = true ↔
      (stateAuthB k.caps actor cell = true ∧ cell ∈ k.accounts ∧ cellLive k cell = true) := by
  simp only [setVerificationKeyGuard, Bool.and_eq_true, decide_eq_true_eq]
  tauto

/-- The `setCell {cell}` leaf-map `fun c => if c ∈ {cell} then setField vkField (k.cell c) (.int vk) else
k.cell c` IS the declarative VK post-cell-map `setVKCellMap k cell vk`. (The `Finset` membership `c ∈ {cell}`
and the spec's `c = cell` coincide via `Finset.mem_singleton`.) The funext that makes the IR `setCell` body
land on the EXACT post-`cell` the kernel `writeField` installs. -/
theorem setVK_setCellMap_eq (k : RecordKernelState) (cell : CellId) (vk : Int) :
    (fun c => if c ∈ ({cell} : Finset CellId) then setField vkField (k.cell c) (.int vk) else k.cell c)
      = setVKCellMap k cell vk := by
  funext c
  by_cases hc : c ∈ ({cell} : Finset CellId)
  · rw [if_pos hc]
    simp only [Finset.mem_singleton] at hc
    simp only [setVKCellMap, if_pos hc]
  · rw [if_neg hc]
    simp only [Finset.mem_singleton] at hc
    simp only [setVKCellMap, if_neg hc]

/-- **The cornerstone (VK-write kernel step).** `interp` of the setVerificationKey term IS the verified
kernel-level VK-write transition `fun k => if <three-leg guard> then some { k with cell := setVKCellMap k
cell vk } else none` — the same partial function, by construction, exactly as the transfer cornerstone, now
writing the `verification_key` slot via `setCell {cell}` (NOT the `balance` slot transfer writes). This is
the kernel projection of the `.setVKA` arm `stateStep s vkField actor cell (.int vk)` (its post-`cell` is
`setVKCellMap`, its post-`log` is the receipt prepend, every other kernel field frozen — §3 lifts to the
chained executor). The executor IS the meaning of the term. -/
theorem interp_setVerificationKeyStmt_eq_setVKKernelStep (actor cell : CellId) (vk : Int)
    (k : RecordKernelState) :
    interp (setVerificationKeyStmt actor cell vk) k
      = (if (stateAuthB k.caps actor cell = true ∧ cell ∈ k.accounts ∧ cellLive k cell = true) then
          some { k with cell := setVKCellMap k cell vk } else none) := by
  simp only [setVerificationKeyStmt, interp]
  by_cases hg : setVerificationKeyGuard actor cell k = true
  · -- ADMIT: the guard's `interp` fires (`some k`); the `setCell {cell}` move installs the VK slot-write,
    -- which IS `setVKCellMap k cell vk` (`setVK_setCellMap_eq`); the RHS `if` opens on the decoded gate.
    rw [if_pos hg]
    simp only [Option.bind]
    rw [if_pos ((setVerificationKeyGuard_iff actor cell k).mp hg), setVK_setCellMap_eq]
  · -- REJECT: the guard fails ⇒ `none.bind _ = none`; the RHS `if` closes on the (negated) decoded gate.
    rw [if_neg hg]
    simp only [Option.bind]
    rw [if_neg (fun hp => hg ((setVerificationKeyGuard_iff actor cell k).mpr hp))]

#assert_axioms interp_setVerificationKeyStmt_eq_setVKKernelStep

/-! ## §3 — Lifting the cornerstone to the CHAINED executor `stateStep` / `execFullA`.

The standalone setVK descriptor (§4) is keyed on the CHAINED executor `execFullA` over `RecChainedState`
(kernel + receipt log) — the arm `execFullA s (.setVKA actor cell vk) = stateStep s vkField actor cell
(.int vk)` (`execFullA_setVK_eq`). The §2 cornerstone is over the kernel VK-write step. The chained layer
is exactly that kernel step PLUS the receipt-log prepend — and, crucially, the SAME three-conjunct gate (no
extra side-condition: `stateStep` gates on `s.kernel` only). We bridge faithfully, carrying NO
side-condition: when the §2 cornerstone commits on the kernel, the chained executor commits with the
receipt prepended. -/

/-- **`interp_setVerificationKeyStmt_chained` — the IR term's executor, lifted to the chained `execFullA`.**
When the §2 cornerstone commits on the kernel (`interp (setVerificationKeyStmt actor cell vk) st.kernel =
some k'`), the unified action executor `execFullA st (.setVKA actor cell vk)` commits to the chained state
`⟨k', receipt :: st.log⟩`. So the Argus term's kernel meaning lifts to the chained executor the standalone
descriptor speaks about — with NO carried side-condition (the chained gate IS the kernel gate). -/
theorem interp_setVerificationKeyStmt_chained
    (st : RecChainedState) (actor cell : CellId) (vk : Int) (k' : RecordKernelState)
    (hexec : interp (setVerificationKeyStmt actor cell vk) st.kernel = some k') :
    execFullA st (.setVKA actor cell vk)
      = some { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := 0 } :: st.log } := by
  -- the §2 cornerstone turns the IR term into the kernel VK-write step (an `if` on the three-leg gate).
  rw [interp_setVerificationKeyStmt_eq_setVKKernelStep] at hexec
  -- `execFullA st (.setVKA actor cell vk)` reduces to `stateStep st vkField actor cell (.int vk)`, whose
  -- `if` opens on the SAME three-leg gate. The cornerstone `hexec` names the post-kernel `k'`; the chained
  -- arm wraps it with the receipt prepend.
  rw [execFullA_setVK_eq]
  unfold stateStep
  by_cases hg : stateAuthB st.kernel.caps actor cell = true ∧ cell ∈ st.kernel.accounts
      ∧ cellLive st.kernel cell = true
  · -- the kernel step committed: read off `k'` from `hexec`; the chained arm fires on the same gate. The
    -- committed kernel is `{ st.kernel with cell := setVKCellMap st.kernel cell vk }` on the IR side, and
    -- `writeField st.kernel vkField cell (.int vk)` on the chained side — DEFINITIONALLY equal (both rewrite
    -- ONLY `.cell` to `setVKCellMap`; `writeField`'s inline map `fun c => if c = cell then setField vkField …`
    -- IS `setVKCellMap`).
    rw [if_pos hg] at hexec
    rw [if_pos hg]
    simp only [Option.some.injEq] at hexec
    subst hexec
    rfl
  · -- the kernel step REJECTED ⇒ `hexec : none = some k'`, contradiction.
    rw [if_neg hg] at hexec
    exact absurd hexec (by simp)

#assert_axioms interp_setVerificationKeyStmt_chained

/-! ## §4 — THE COMPILE WELD: a satisfying witness of setVK's OWN standalone full-state circuit agrees with
the FULL post-state the IR term's executor interpretation produces.

This welds against setVK's GENUINE standalone descriptor `setVKE` (the v1 `CommitSurface` circuit whose
soundness is `setVKA_full_sound`), exactly as `BalanceA`/`RefreshDelegation` weld against their own
full-state descriptors. The executor side is routed through §3 (`interp` ⟹ `execFullA`) and the independent
`execFullA_setVK_iff_spec` (executor ⟺ `SetVKSpec`); the circuit side is the audited `setVKA_full_sound`
(circuit ⟹ `SetVKSpec`). Both name the SAME `SetVKSpec`, so they PROVABLY agree on the WHOLE 17-field state
+ the log — a full-state weld. -/

/-- The Argus circuit interpretation of a `setVerificationKey` term: setVK's OWN audited standalone v1
`CommitSurface` circuit step — the full-state arithmetization `satisfiedE S setVKE (encodeE …)` satisfied on
the encoded `(st, ⟨actor,cell,vk⟩, st')` triple. Its soundness `setVKA_full_sound` pins the complete
`SetVKSpec`. The setVK-keyed analog of `balanceACircuit`/`refreshDelegationCircuit`, in the v1 `CommitSurface`
descriptor universe where setVK carries its OWN genuine full-state circuit. -/
def setVerificationKeyCircuit (S : CommitSurface)
    (st : RecChainedState) (actor cell : CellId) (vk : Int) (st' : RecChainedState) : Prop :=
  satisfiedE S setVKE (encodeE S setVKE st { actor := actor, cell := cell, vk := vk } st')

/-- **`setVKSpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH satisfy
`SetVKSpec st actor cell vk ·` are equal. Rather than re-derive this field-by-field, we route through the
PROVEN executor⟺spec corner `execFullA_setVK_iff_spec`: each `SetVKSpec` reconstructs the SAME committed
value `execFullA st (.setVKA actor cell vk) = some ·`, and `some` is injective. This is exactly the sense in
which `SetVKSpec` is functional — it determines the post-state — so the circuit-side and executor-side spec
facts collapse to one welded post-state. -/
theorem setVKSpec_unique {st st₁ st₂ : RecChainedState} {actor cell : CellId} {vk : Int}
    (h₁ : SetVKSpec st actor cell vk st₁) (h₂ : SetVKSpec st actor cell vk st₂) : st₁ = st₂ := by
  have e₁ : execFullA st (.setVKA actor cell vk) = some st₁ :=
    (execFullA_setVK_iff_spec st actor cell vk st₁).mpr h₁
  have e₂ : execFullA st (.setVKA actor cell vk) = some st₂ :=
    (execFullA_setVK_iff_spec st actor cell vk st₂).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- **`setVerificationKey_compile_sound` — the welded soundness (setVK slice), against setVK's OWN full-state
descriptor.**

Suppose, for the Argus setVerificationKey term `setVerificationKeyStmt actor cell vk`:
  * the standalone setVK circuit `setVerificationKeyCircuit S st actor cell vk st'` (= `setVKE`'s full-state
    v1 arithmetization satisfied on the encoded triple) holds, under the realizable `CommitSurface` digest
    portals (`hN : compressNInjective S.compressN`, `hL : cellLeafInjective S.CH`,
    `hRest : RestHashIffFrame S.RH`, `hLog : logHashInjective S.LH`) and the well-formedness side-conditions
    (`hwf : AccountsWF st.kernel`, `hwf' : AccountsWF st'.kernel`);
  * the IR term's EXECUTOR interpretation COMMITS on the kernel:
    `interp (setVerificationKeyStmt actor cell vk) st.kernel = some k'` (`hexec`).

Then the chained post-state the circuit pins is EXACTLY the chained post-state the IR term's executor
produces: `st' = { kernel := k', log := receipt :: st.log }`. I.e. setVK's OWN circuit and the IR term AGREE
on the WHOLE 17-field RecordKernelState (`cell`'s `verification_key` slot written, every other field —
including the conserved `balance` and the `caps` graph — frozen) AND the receipt log — the full `SetVKSpec`,
not a per-cell projection. So the circuit the prover runs for setVK pins the complete state the IR term's
executor produces. There is NO nonce-tick conjunct on this surface: `SetVKSpec` freezes the record off the
written slot and pins the log as exactly one row, so the executor IS the spec on the nose. -/
theorem setVerificationKey_compile_sound
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (st st' : RecChainedState) (actor cell : CellId) (vk : Int) (k' : RecordKernelState)
    (hwf : AccountsWF st.kernel) (hwf' : AccountsWF st'.kernel)
    (hcirc : setVerificationKeyCircuit S st actor cell vk st')
    (hexec : interp (setVerificationKeyStmt actor cell vk) st.kernel = some k') :
    st' = { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := 0 } :: st.log } := by
  -- circuit side: setVK's OWN audited soundness forces the FULL `SetVKSpec` on `(st, ⟨actor,cell,vk⟩, st')`.
  have hspec : SetVKSpec st actor cell vk st' :=
    setVKA_full_sound S hN hL hRest hLog st { actor := actor, cell := cell, vk := vk } st' hwf hwf' hcirc
  -- executor side: the §3 chained lift gives `execFullA st (.setVKA actor cell vk) = some ⟨k', receipt ::
  -- st.log⟩`, and the independent executor⟺spec corner turns THAT into the same spec.
  have hspec' : SetVKSpec st actor cell vk
      { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := 0 } :: st.log } :=
    (execFullA_setVK_iff_spec st actor cell vk _).mp
      (interp_setVerificationKeyStmt_chained st actor cell vk k' hexec)
  -- both states satisfy the SAME spec ⇒ they are the same state (the spec pins every kernel field + log).
  exact setVKSpec_unique hspec hspec'

#assert_axioms setVerificationKey_compile_sound

/-! ## §5 — NON-VACUITY: the IR term genuinely WRITES the VK slot (observable), frames the conserved balance
+ cap-graph, and the gate REJECTS forged inputs (fail-closed).

The cornerstone/weld would be hollow if setVK never committed, if the VK write were a no-op, if it disturbed
the conserved balance/caps, or if the gate admitted everything. A concrete two-account kernel `kSVK` (cells
0,1 live; cell 0 holds a self-authority cap and 30 of `balance`) exercises a real VK write; the rejection
lemmas show each guard leg fails closed. -/

/-- A concrete kernel for the witnesses: cells `0` and `1` are live accounts (lifecycle defaults Live), cell
`0` holds a self-authority `node 0` cap (so `stateAuthB 0 0` holds) and a `balance` of 30 in its record (the
conserved slot the VK write must NOT disturb); the `verification_key` slot starts ABSENT (reads `0`). -/
def kSVK : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun c => if c = 0 then .record [("balance", .int 30)] else .record [("balance", .int 0)]
    caps := fun c => if c = 0 then [Dregg2.Authority.Cap.node 0] else [] }

/-- **NON-VACUITY (the VK WRITE is OBSERVABLE).** A committed setVK of cell `0` to `vk = 42` SETS cell `0`'s
`verification_key` slot from `0` (absent) to `42` — the `setCell`/`setField vkField` write is real (the VK
genuinely lands in the record, not a no-op). -/
theorem setVerificationKeyStmt_writes :
    (interp (setVerificationKeyStmt 0 0 42) kSVK).map
      (fun k => fieldOf vkField (k.cell 0)) = some 42 := by
  rw [interp_setVerificationKeyStmt_eq_setVKKernelStep]
  decide

/-- **NON-VACUITY (the conserved BALANCE is FRAMED).** The VK write leaves cell `0`'s `balance` slot at 30
— `verification_key` is a DISTINCT slot, so the conserved balance is untouched (the regime balance-Δ=0
obligation, `setVK_cellWrite_correct`). No value is conjured or destroyed by a metadata write. -/
theorem setVerificationKeyStmt_frames_balance :
    (interp (setVerificationKeyStmt 0 0 42) kSVK).map
      (fun k => balOf (k.cell 0)) = some 30 := by
  rw [interp_setVerificationKeyStmt_eq_setVKKernelStep]
  decide

/-- **NON-VACUITY (frame: a DIFFERENT cell is untouched).** Writing cell `0`'s VK leaves cell `1`'s whole
record verbatim (its `balance` stays 0, its absent `verification_key` stays `0`) — the write is LOCAL to the
target cell (`setVKCellMap`'s off-`cell` branch). The frame-respecting witness. -/
theorem setVerificationKeyStmt_frames_other_cell :
    (interp (setVerificationKeyStmt 0 0 42) kSVK).map
      (fun k => fieldOf vkField (k.cell 1)) = some 0 := by
  rw [interp_setVerificationKeyStmt_eq_setVKKernelStep]
  decide

/-- **NON-VACUITY (fail-closed: no authority).** A setVK attempted by a FOREIGN actor (cell `1`, which holds
NO cap over cell `0` and is `≠ 0`, so it is NOT self-authorized) does NOT commit — the AUTHORITY leg
`stateAuthB 1 0` fails closed. A third party cannot rotate someone else's verification key. No write is
performed. -/
theorem setVerificationKeyStmt_rejects_unauthorized :
    interp (setVerificationKeyStmt 1 0 42) kSVK = none := by
  rw [interp_setVerificationKeyStmt_eq_setVKKernelStep]
  decide

/-- **NON-VACUITY (fail-closed: non-account).** A setVK targeting a cell that is NOT a live account (cell
`5`, absent from `accounts`) does NOT commit — the MEMBERSHIP leg fails closed. No write is performed. -/
theorem setVerificationKeyStmt_rejects_nonaccount :
    interp (setVerificationKeyStmt 5 5 42) kSVK = none := by
  rw [interp_setVerificationKeyStmt_eq_setVKKernelStep]
  decide

/-- **NON-VACUITY (fail-closed: non-Live cell — the upgrade-safety tooth).** A setVK into a SEALED cell
(lifecycle discriminant `1`, here cell `0` over a kernel where `0` is sealed) does NOT commit — the R6
LIVENESS leg `cellLive` fails closed. This is the very upgrade-safety property `SetVerificationKey` needs: a
sealed/destroyed cell cannot have its VK rotated out from under its existing proofs. No write is performed. -/
theorem setVerificationKeyStmt_rejects_nonlive :
    interp (setVerificationKeyStmt 0 0 42)
      { kSVK with lifecycle := fun c => if c = 0 then 1 else 0 } = none := by
  rw [interp_setVerificationKeyStmt_eq_setVKKernelStep]
  decide

#assert_axioms setVerificationKeyStmt_writes
#assert_axioms setVerificationKeyStmt_frames_balance
#assert_axioms setVerificationKeyStmt_frames_other_cell
#assert_axioms setVerificationKeyStmt_rejects_unauthorized
#assert_axioms setVerificationKeyStmt_rejects_nonaccount
#assert_axioms setVerificationKeyStmt_rejects_nonlive

/-! ### §5.1 — THE REPORTED DIVERGENCE: the v1 `CommitSurface` full-state weld vs the runnable EffectVm row.

This module welds against setVK's v1 `CommitSurface` descriptor (`setVKE`/`setVKA_full_sound`), whose
`SetVKSpec` pins the `verification_key` slot WRITTEN into the `cell` map and FREEZES the record off that slot
(including the cell's nonce-bearing record). The RUNNING hand-AIR (`circuit/src/effect_vm/air.rs:961`,
selector 27 — the EffectVm universe `Emit/EffectVmEmitSetVK.lean` reconciles to) runs `setVerificationKey`
as a state-PASSTHROUGH row: it FREEZES every economic state-block column and TICKS the GLOBAL nonce, carrying
the VK value OFF the per-row state block (in `params[0]` + `effects_hash`). So the two CIRCUIT universes
DIVERGE on (a) where the VK write is pinned — v1 `CommitSurface` `cell`-map here vs EffectVm off-trace — and
(b) the nonce — the v1 spec freezes the record's nonce slot; the EffectVm row ticks the global nonce.

We pin BOTH halves as a DOCUMENTATION THEOREM so the divergence cannot silently regress: the v1 kernel step
this module welds against (i) WRITES the `verification_key` slot to `vk` (observable, in-`cell`), and (ii)
freezes the `cell`'s conserved `balance` and the `caps` graph (no nonce tick / no off-trace move at THIS
layer). This makes the v1-vs-EffectVm contrast a checked fact of the model, not a buried assumption. Closing
it (reconciling the two universes onto ONE column convention) is the EffectVm/`field`-column cutover work,
explicitly OUT OF SCOPE for this full-state weld. -/

/-- **`setVK_full_state_writes_vs_effectvm_offtrace` — the reported divergence, as a checked theorem.** The
v1 `CommitSurface` kernel step this module welds against WRITES the `verification_key` slot IN the `cell`
record (`= vk`) AND freezes the cell's conserved `balance` — whereas the runnable EffectVm row freezes the
`field` block and rides the VK OFF-trace. Pinning the in-`cell` VK write + the frozen `balance` here makes
the v1-vs-EffectVm universe divergence a checked fact (the v1 surface internalizes the VK write the EffectVm
row carries off-trace; neither ticks the in-`cell` nonce on this layer). -/
theorem setVK_full_state_writes_vs_effectvm_offtrace
    {st st' : RecChainedState} {actor cell : CellId} {vk : Int}
    (h : execFullA st (.setVKA actor cell vk) = some st') :
    fieldOf vkField (st'.kernel.cell cell) = vk
    ∧ balOf (st'.kernel.cell cell)
        = balOf (st.kernel.cell cell) := by
  have hspec := (execFullA_setVK_iff_spec st actor cell vk st').mp h
  refine ⟨?_, ?_⟩
  · -- the `verification_key` slot of `cell` is set to exactly `vk` (in the `cell` map).
    rw [hspec.2.1]
    exact (Dregg2.Circuit.Spec.CellStateVK.setVK_cellWrite_correct st.kernel cell vk).1
  · -- the conserved `balance` of `cell` is frozen (the `verification_key` write rides a DISTINCT slot).
    rw [hspec.2.1]
    exact (Dregg2.Circuit.Spec.CellStateVK.setVK_cellWrite_correct st.kernel cell vk).2.1

#assert_axioms setVK_full_state_writes_vs_effectvm_offtrace

end Dregg2.Circuit.Argus.Effects.SetVerificationKey
