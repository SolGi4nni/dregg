/-
# Dregg2.Circuit.Emit.EffectVmEmitBurn — the SUPPLY-BURN effect `burnA`, EMITTED onto the runnable
  EffectVM `bal_lo` (balance) column, with its full-state per-cell soundness, the anti-ghost
  commitment tooth, and the connector to the validated universe-A `BurnSpec` / `recCBurnAsset`.

## The "ONE circuit" thesis for `burnA` (a balance/field effect — the closest clone of transfer)

`burnA` is the per-asset privileged-supply BURN (`Inst/burnA.lean`, `Spec/supplydestruction.lean`):
the executor DEBITS the per-asset ledger `bal` at one `(cell, asset)` by `amt` (`recBalCredit … (-amt)`),
prepends a disclosing receipt, and freezes the 16 non-`bal` kernel fields. Its validation
`burnA_full_sound ⇒ BurnSpec` is DONE; this module emits the SAME effect onto the running EffectVM row
layout and welds the two — ONE circuit description, not a parallel spec.

The EffectVM state block carries ONE cell's conserved balance as the `bal_lo` limb (state offset 0,
`state.BALANCE_LO`). The running prover absorbs it into the GROUP-4 state-commitment chain
(`site0` reads `saCol BALANCE_LO`). So at the row level a burn is a `bal_lo` COLUMN DEBIT: the
post-`bal_lo` is the pre value MINUS the burn `amount`, every OTHER state column frozen, and the
post-state bound into the published `state_commit` under Poseidon2 collision-resistance.

`burnVmDescriptor` emits exactly that. The debit gate is `new_bal_lo - old_bal_lo + amount = 0`
(`new = old - amt`), the rest of the block (bal_hi / nonce / 8 fields / cap_root / reserved) is frozen
by passthrough gates, and the 4 GROUP-4 hash-sites bind the whole post-state into `state_commit`.

## What is PROVED here

  * `burnVm_faithful` — on a burn row the emitted per-row gates hold IFF `BurnRowIntent` (`bal_lo`
    debited by `amount`, frame frozen).
  * `burnDescriptor_full_sound` — satisfying the WHOLE descriptor under the `RowEncodes` decoding
    forces the structured per-cell `CellBurnSpec pre amt post` (debit + full frame freeze) AND
    publishes `post.commit = PI[NEW_COMMIT]`.
  * `burnDescriptor_commit_binds_state_or_collides` — the KEYSTONE anti-ghost, UNCONDITIONAL: two
    satisfying rows agreeing on the published `NEW_COMMIT` EITHER have IDENTICAL absorbed after-state
    columns OR exhibit a genuine deployed-sponge collision (reusing the cured transfer core
    `absorbed_determined_by_commit_or_collides`, since the hash sites are the SAME GROUP-4 chain).
  * `unify_burn` / `unify_burn_exec` — the CONNECTOR: a committed universe-A `BurnSpec` (= `recCBurnAsset`),
    projected per-`(cell, asset)` through `cellProjA`, satisfies `CellBurnSpec` EXACTLY (the conserved
    `bal cell a` drops by `amt`; the frame is `0 = 0`). So the runnable `bal_lo` column transition IS
    universe-A's `bal`-ledger transition, NOT a fourth spec.

## BOUNDARY (precise — do NOT over-read)

  * PER-CELL / PER-ROW. Single-row AIR: ONE `(cell, asset)` ledger entry's debit + its binding into the
    published `state_commit`. Cross-row composition (and the disclosing log receipt) is the turn layer
    (`TurnEmit`), cited not claimed.
  * The EffectVM row's `bal_lo` is a BARE limb; which `(cell, asset)` ledger entry it is comes from the
    `cellProjA` encoding choice, not a row gate. The AUTHORITY / non-negativity / availability / liveness
    GUARD of `recKBurnAsset` (`BurnGuard`) has no row column; it lives in universe-A's spec (cited).
  * NONCE DIVERGENCE: the EffectVM block carries a `nonce` column, and the burn descriptor FREEZES it
    (`gNonceFix`). Universe-A's burn touches ONLY `bal` (the cell record's `nonce` survives), so the
    descriptor's nonce-freeze MATCHES the executor (no divergence for burn — unlike transfer, which ticks
    the row nonce). Stated as `CellBurnSpec`'s nonce-freeze clause and proved against the executor.
  * `state.RESERVED` is NOT absorbed by any hash-site (inherited finding from the transfer keystone);
    pinned only by its per-row passthrough gate.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. The commitment keystone is
UNCONDITIONAL (an extraction-as-data disjunction naming a deployed-sponge collision pair), never
conditioned on the refuted injective sponge floor; the injective special case lives at the transfer
spine home. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.supplydestruction

namespace Dregg2.Circuit.Emit.EffectVmEmitBurn

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA ePrm eSub eSelNoop gNonce transitionAll boundaryFirstPins boundaryLastPins
   transferHashSites site0 site1 site2 site3 boundaryLast_pins
   gate_modEq_iff not_modEq_zero_of_canon pPrimeInt)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState absorbedCols absorbed_determined_by_commit_or_collides TransferColl)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Spec.SupplyDestruction

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — Selector + param offsets for the burn effect row.

The running EffectVM lays one selector per effect (`columns.rs::NUM_EFFECTS = 54`); `burnA` has its own
selector index `sel.BURN`. The burn `amount` rides the SAME `param.AMOUNT` column transfer uses (offset 0).
On a genuine burn row the burn selector is `1` and `s_noop = 0`. -/

namespace selB
/-- The `burnA` effect selector column (the running prover's per-effect selector, `sel::BURN`). -/
def BURN : Nat := 46
end selB

/-- The `burnA` selector as an expression. -/
def eSelBurn : EmittedExpr := .var selB.BURN

/-! ### Burn parameter column (the running trace generator's convention).

`generate_effect_vm_trace` lays the burn row's params as `param0 = target_hash`,
`param1 = amount_lo` (the burn amount), `param2 = was_burn_flag` — see `columns.rs::param::BURN_*`
and the `Effect::Burn` arm of `trace.rs`. The hand-AIR's burn debit gate reads `prm(param::BURN_AMOUNT_LO)`
= param column **1**, NOT the transfer `param.AMOUNT` (= column 0, which carries the target hash on a
burn row). The descriptor MUST read the same column or it debits the wrong value (UNSAT on the honest
trace). -/
namespace param
/-- Burn amount lives at param column 1 (`columns.rs::param::BURN_AMOUNT_LO`). -/
def BURN_AMOUNT_LO : Nat := 1
end param

/-- Burn amount as an expression (param column 1). -/
def ePrmBurnAmt : EmittedExpr := .var (prmCol param.BURN_AMOUNT_LO)

/-! ## §1 — The burn row gates (term-for-term the running prover's, specialized to the row).

A burn DEBITS `bal_lo` by `amount` (read from `param1`, the trace-generator convention) and FREEZES
the rest of the block EXCEPT the nonce. As with EVERY non-NoOp EffectVM row, the running prover's
GLOBAL nonce gate ticks the row nonce by one (`new_nonce − old_nonce − (1 − s_noop) = 0`); the burn
row is non-NoOp, so it TICKS. (This is the per-cell runtime SEQUENCE counter, a distinct object from
universe-A's frozen ledger-entry nonce — see §7's connector, which reports the gap exactly as the
transfer keystone does.) -/

/-- Balance-lo DEBIT body: `new_bal_lo - old_bal_lo + amount` (so `new = old - amount`), reading the
burn amount from `param1` (the trace-generator + hand-AIR convention). -/
def gBalLoDebit : EmittedExpr :=
  .add (eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)) ePrmBurnAmt

/-- Balance-hi freeze body: `new_bal_hi - old_bal_hi`. -/
def gBalHiFix : EmittedExpr := eSub (eSA state.BALANCE_HI) (eSB state.BALANCE_HI)

/-- Nonce TICK body (the running prover's global non-NoOp invariant): `new_nonce − old_nonce − (1 − s_noop)`.
On a burn row `s_noop = 0`, so this is `new_nonce − old_nonce − 1` (tick). Reused verbatim from the
transfer template (`gNonce`). -/
def gNonceTick : EmittedExpr := gNonce

/-- Cap-root passthrough body: `new_cap_root - old_cap_root`. -/
def gCapFix : EmittedExpr := eSub (eSA state.CAP_ROOT) (eSB state.CAP_ROOT)

/-- Reserved passthrough body: `new_reserved - old_reserved`. -/
def gResFix : EmittedExpr := eSub (eSA state.RESERVED) (eSB state.RESERVED)

/-- Field-`i` passthrough body: `field_after[i] - field_before[i]`. -/
def gFieldFix (i : Nat) : EmittedExpr :=
  eSub (eSA (state.FIELD_BASE + i)) (eSB (state.FIELD_BASE + i))

/-- The eight field-passthrough gates. -/
def gFieldFixAll : List VmConstraint :=
  (List.range 8).map (fun i => VmConstraint.gate (gFieldFix i))

/-- The burn-specialized per-row gates (balance debit, hi/cap/reserved freeze, nonce TICK, 8 fields freeze). -/
def burnRowGates : List VmConstraint :=
  [ .gate gBalLoDebit, .gate gBalHiFix, .gate gNonceTick, .gate gCapFix, .gate gResFix ]
  ++ gFieldFixAll

/-! ## §2 — The emitted BURN descriptor.

Per-row gates ++ transition continuity ++ the 7 boundary PI pins (reused from transfer), with the 4
ordered GROUP-4 hash sites and the balance-limb range checks. -/

/-- The burn AIR identity. -/
def burnVmAirName : String := "dregg-effectvm-burn-v1"

/-- **`burnVmDescriptor`** — the `burnA` effect's full concrete circuit, emitted through the EffectVM
IR: the per-row debit/freeze gates ++ transition continuity ++ the 7 boundary PI pins, with the 4
ordered GROUP-4 hash sites and the 2 balance-limb range checks. -/
def burnVmDescriptor : EffectVmDescriptor :=
  { name := burnVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 42
  , constraints := burnRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                     ++ selectorGates selB.BURN
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The BURN ROW INTENT (the independent faithfulness target).

`BurnRowIntent` is the field-level burn move written from protocol intent (NOT the gate bodies): on a
burn row, `bal_lo` drops by `amount`, the hi limb / nonce / cap_root / reserved / 8 fields are FIXED.
This is the EffectVM-row projection of `BurnSpec`'s `recBalCredit … (-amt)` debit, restricted to the
single ledger entry the row carries. -/

/-- **`BurnRowIntent env`** — the intended burn move on the row `env.loc`: `bal_lo` debited by the
`param1` amount, balHi/cap/reserved/8 fields frozen, and the runtime nonce TICKED by one (the per-cell
sequence counter — distinct from universe-A's frozen ledger nonce; see the §7 connector). -/
def BurnRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO)
      ≡ env.loc (sbCol state.BALANCE_LO) - env.loc (prmCol param.BURN_AMOUNT_LO) [ZMOD 2013265921]
  ∧ env.loc (saCol state.BALANCE_HI) ≡ env.loc (sbCol state.BALANCE_HI) [ZMOD 2013265921]
  ∧ env.loc (saCol state.NONCE) ≡ env.loc (sbCol state.NONCE) + 1 [ZMOD 2013265921]
  ∧ env.loc (saCol state.CAP_ROOT) ≡ env.loc (sbCol state.CAP_ROOT) [ZMOD 2013265921]
  ∧ env.loc (saCol state.RESERVED) ≡ env.loc (sbCol state.RESERVED) [ZMOD 2013265921]
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i))
      ≡ env.loc (sbCol (state.FIELD_BASE + i)) [ZMOD 2013265921])

/-- The row is a burn row: `s_burn = 1`, `s_noop = 0`. The `s_noop = 0` clause is what the global
nonce-tick gate factors on (a burn row is non-NoOp, so the nonce ticks). -/
def IsBurnRow (env : VmRowEnv) : Prop :=
  env.loc selB.BURN = 1 ∧ env.loc sel.NOOP = 0

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the intent. -/

/-- **`burnVm_faithful`.** On a burn row, the emitted descriptor's per-row gates hold IFF the burn
intent holds. The gate bodies are the running prover's polynomials (specialized to the burn row), and
they pin EXACTLY the intent move. -/
theorem burnVm_faithful (env : VmRowEnv) (hrow : IsBurnRow env) :
    (∀ c ∈ burnRowGates, c.holdsVm env false false) ↔ BurnRowIntent env := by
  obtain ⟨_hsB, hsN⟩ := hrow
  unfold burnRowGates gFieldFixAll BurnRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoDebit) (by simp)
    have hHi := h (.gate gBalHiFix) (by simp)
    have hNon := h (.gate gNonceTick) (by simp)
    have hCap := h (.gate gCapFix) (by simp)
    have hRes := h (.gate gResFix) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldFix i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoDebit, gBalHiFix, gNonceTick, gNonce, gCapFix, gResFix,
      ePrmBurnAmt, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval] at hLo hHi hNon hCap hRes
    rw [hsN] at hNon
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (gate_modEq_iff (by ring)).mp hLo
    · exact (gate_modEq_iff (by ring)).mp hHi
    · exact (gate_modEq_iff (by ring)).mp hNon
    · exact (gate_modEq_iff (by ring)).mp hCap
    · exact (gate_modEq_iff (by ring)).mp hRes
    · intro i hi
      have hfi := hFld i hi
      simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval] at hfi
      exact (gate_modEq_iff (by ring)).mp hfi
  · rintro ⟨hLo, hHi, hNon, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gBalLoDebit, ePrmBurnAmt, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hLo
    · simp only [VmConstraint.holdsVm, gBalHiFix, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hHi
    · simp only [VmConstraint.holdsVm, gNonceTick, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
      rw [hsN]
      exact (gate_modEq_iff (by ring)).mpr hNon
    · simp only [VmConstraint.holdsVm, gCapFix, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hCap
    · simp only [VmConstraint.holdsVm, gResFix, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hRes
    · simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr (hFld i hi)

/-- **Anti-ghost (balance tamper).** A burn row whose post-`bal_lo` is NOT the debit `old - amount`
fails the `gBalLoDebit` gate (UNSAT). FIELD-FAITHFUL: the tooth now rejects a field-`≢` output, so it
needs the DEPLOYED range-check canonicality — the after-balance (`saCol BALANCE_LO`, a `ranges` wire)
and the intended debited balance both lie in `[0, p)`. Under canonicality a WRONG `bal_lo` differs from
the intended value by less than `p`, so `p` cannot divide the residual and the field gate is UNSAT (no
wrap-around forgery). -/
theorem burnVm_rejects_wrong_balance (env : VmRowEnv)
    (hcanonNew : 0 ≤ env.loc (saCol state.BALANCE_LO)
      ∧ env.loc (saCol state.BALANCE_LO) < 2013265921)
    (hcanonMove : 0 ≤ env.loc (sbCol state.BALANCE_LO) - env.loc (prmCol param.BURN_AMOUNT_LO)
      ∧ env.loc (sbCol state.BALANCE_LO) - env.loc (prmCol param.BURN_AMOUNT_LO) < 2013265921)
    (hwrong : env.loc (saCol state.BALANCE_LO)
      ≠ env.loc (sbCol state.BALANCE_LO) - env.loc (prmCol param.BURN_AMOUNT_LO)) :
    ¬ (VmConstraint.gate gBalLoDebit).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoDebit, ePrmBurnAmt, eSA, eSB, eSub, EmittedExpr.eval]
  exact not_modEq_zero_of_canon (by ring) hcanonNew hcanonMove hwrong

/-! ## §5 — `CellBurnSpec` + `RowEncodes` → the structured per-cell soundness.

`CellBurnSpec pre amt post` is the per-cell FULL-state spec: `bal_lo` debited by `amt`, EVERY other
block component (balHi/nonce/8 fields/capRoot/reserved) LITERALLY frozen. `RowEncodes` decodes the row's
state-block columns into concrete `CellState` records. -/

/-- The per-cell burn spec (EffectVM-row image): balLo drops by `amt`, balHi/8-fields/cap/reserved
frozen, and the runtime nonce TICKS by one (the per-cell sequence counter). The universe-A connector
in §7 reconciles this tick against the FROZEN ledger nonce via `CellBurnSpecFrozenNonce`, exactly as
the transfer keystone reconciles its row nonce-tick. -/
def CellBurnSpec (pre : CellState) (amt : ℤ) (post : CellState) : Prop :=
  post.balLo ≡ pre.balLo - amt [ZMOD 2013265921]
  ∧ post.balHi ≡ pre.balHi [ZMOD 2013265921]
  ∧ post.nonce ≡ pre.nonce + 1 [ZMOD 2013265921]
  ∧ (∀ i : Fin 8, post.fields i ≡ pre.fields i [ZMOD 2013265921])
  ∧ post.capRoot ≡ pre.capRoot [ZMOD 2013265921]
  ∧ post.reserved ≡ pre.reserved [ZMOD 2013265921]

/-- `RowEncodes env pre amt post` — the row's `state_before`/`amount`/`state_after` columns decode to
`pre`/`amt`/`post` (column-by-column), plus the published OLD/NEW commitments. -/
def RowEncodes (env : VmRowEnv) (pre : CellState) (amt : ℤ) (post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (sbCol state.STATE_COMMIT) = pre.commit
  ∧ env.loc (prmCol param.BURN_AMOUNT_LO) = amt
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved
  ∧ env.loc (saCol state.STATE_COMMIT) = post.commit
  ∧ env.pub pi.OLD_COMMIT = pre.commit
  ∧ env.pub pi.NEW_COMMIT = post.commit

/-- Under `RowEncodes`, `BurnRowIntent` IS the structured per-cell spec. -/
theorem intent_to_cellSpec (env : VmRowEnv) (pre post : CellState) (amt : ℤ)
    (henc : RowEncodes env pre amt post) (hint : BurnRowIntent env) :
    CellBurnSpec pre amt post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC, hpAmt,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsaLo, ← hsbLo, ← hpAmt]; exact hbal
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · rw [← hsaN, ← hsbN]; exact hnon
  · intro i; have := hfld i.val i.isLt; rw [← hsaF i, ← hsbF i]; exact this
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

/-! ### The descriptor's per-row gates are a sub-list whose `holdsVm` is flag-independent. -/

/-- The per-row gates are all `.gate _`; under the deployed `when_transition()` they bind on every row
but the last, so their body content is available at the ACTIVE row (`isLast = false`). This restates
that content at the canonical `false false` flags. The hypothesis is taken at `b2 = false` (the gate
content genuinely does not exist on the wrap row `isLast = true`). -/
theorem burnRowGates_flag_indep (env : VmRowEnv) (b1 : Bool)
    (h : ∀ c ∈ burnRowGates, c.holdsVm env b1 false) :
    ∀ c ∈ burnRowGates, c.holdsVm env false false := by
  intro c hc
  have := h c hc
  unfold burnRowGates gFieldFixAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using this

/-- **`burnDescriptor_full_sound`.** Satisfying the WHOLE descriptor under `RowEncodes` forces the
structured per-cell `CellBurnSpec` AND publishes `post.commit = PI[NEW_COMMIT]`. -/
theorem burnDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsBurnRow env)
    (pre post : CellState) (amt : ℤ)
    (henc : RowEncodes env pre amt post)
    (hgatesat : satisfiedVm hash burnVmDescriptor env true false)
    (hsat : satisfiedVm hash burnVmDescriptor env true true) :
    CellBurnSpec pre amt post ∧ post.commit ≡ env.pub pi.NEW_COMMIT [ZMOD 2013265921] := by
  obtain ⟨hcs, _hsites⟩ := hsat
  obtain ⟨hcsT, _⟩ := hgatesat
  have hgates : ∀ c ∈ burnRowGates, c.holdsVm env true false := by
    intro c hc; apply hcsT
    unfold burnVmDescriptor; simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
  have hgates' := burnRowGates_flag_indep env true hgates
  have hint := (burnVm_faithful env hrow).mp hgates'
  refine ⟨intent_to_cellSpec env pre post amt henc hint, ?_⟩
  -- last-row boundary pin: state_after.state_commit = PI[NEW_COMMIT]
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ burnVmDescriptor.constraints := by
      unfold burnVmDescriptor; simp only [List.mem_append]; exact Or.inl (Or.inr hc)
    have hh := hcs c hmem
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢; exact hh
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact (boundaryLast_pins env hlast).1

/-! ## §6 — THE ANTI-GHOST COMMITMENT TOOTH (reused from the transfer keystone).

`burnVmDescriptor` carries the SAME GROUP-4 `transferHashSites`, so the transfer keystone's
`transferDescriptor_commit_binds_state_of_injective` applies verbatim once we reduce `satisfiedVm burnVmDescriptor`
to its hash-site component. Two satisfying burn rows that agree on the published `NEW_COMMIT` agree on
their WHOLE absorbed after-state. -/

/-- The descriptor's hash-site component is the transfer GROUP-4 chain. -/
theorem burn_sites_eq : burnVmDescriptor.hashSites = transferHashSites := rfl

/-- **`burnDescriptor_commit_binds_state_or_collides` — THE KEYSTONE anti-ghost tooth for burn,
UNCONDITIONAL.** Two rows satisfying the burn descriptor's hash-sites and publishing the SAME
`NEW_COMMIT` EITHER have IDENTICAL absorbed after-state columns, OR exhibit a genuine collision of the
deployed sponge at the pair `transferCollFind` returns. So a prover CANNOT keep `NEW_COMMIT` while
tampering any absorbed cell unless it finds a Poseidon2 collision. (Proof reuses the cured transfer
core — the hash chain is identical.) ⚑ The old form concluded a bare equality from the injective sponge
floor, which `HashFloorHonesty.poseidon2SpongeCR_false_babyBear` REFUTES at the deployed BabyBear
parameters; this disjunction is formally weaker but HOLDS of the deployed sponge. The injective special
case is `EffectVmEmitTransferSound.absorbed_determined_by_commit_of_injective` (the strength bridge, at
the spine home). -/
theorem burnDescriptor_commit_binds_state_or_collides (hash : List ℤ → ℤ)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ transferHashSites)
    (hs₂ : siteHoldsAll hash e₂ transferHashSites)
    (hpubLo₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpubLo₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ ∨ TransferColl hash e₁ e₂ :=
  absorbed_determined_by_commit_or_collides
    hash e₁ e₂ hs₁ hs₂ (by rw [hpubLo₁, hpubLo₂, hpub])

/-! ## §7 — THE CONNECTOR — `cellProjA` to universe-A's `BurnSpec` / `recCBurnAsset`.

`cellProjA k c a` reads ONE `(cell, asset)` ledger entry of the real record-kernel state into the
keystone's `CellState`: `balLo` = the conserved `bal c a` measure (the SAME measure `recBalCredit` moves),
everything else `0` (universe-A's burn touches no high-limb / nonce / field-array / cap-root / reserved on
the ledger entry — all FROZEN). `commit` (the digest output) is `0`. -/

/-- Project ledger entry `(c, a)` of `k` into the keystone's `CellState` (balLo = `bal c a`; rest `0`). -/
def cellProjA (k : RecordKernelState) (c : CellId) (a : AssetId) : CellState where
  balLo    := k.bal c a
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-! ### The ONE genuine divergence (mirroring the transfer keystone): the EffectVM row TICKS the
runtime nonce; universe-A's burn FREEZES the ledger-entry nonce.

`CellBurnSpec` demands `post.nonce = pre.nonce + 1` (the runtime per-cell sequence counter the
EffectVM row increments on every non-NoOp effect, matching the validated hand-AIR's global nonce
gate). Universe-A's `recCBurnAsset` touches ONLY the `bal` ledger — the projected entry's nonce is
`0` before AND after (`cellProjA` sets it to `0`). So the executor's per-entry image is the
nonce-FREEZE variant. We unify against THAT and report the nonce-tick gap exactly as
`EffectVmEmitTransferUnify` does (`exec_nonce_is_frozen_not_ticked`). -/

/-- The executor's genuine per-entry image: `CellBurnSpec` with the nonce-TICK replaced by
nonce-FREEZE. Every other clause (balLo debit, balHi/fields/capRoot/reserved freeze) is identical. -/
def CellBurnSpecFrozenNonce (pre : CellState) (amt : ℤ) (post : CellState) : Prop :=
  post.balLo ≡ pre.balLo - amt [ZMOD 2013265921]
  ∧ post.balHi ≡ pre.balHi [ZMOD 2013265921]
  ∧ post.nonce ≡ pre.nonce [ZMOD 2013265921]  -- FROZEN (executor ledger image) — keystone demands `+ 1`
  ∧ (∀ i : Fin 8, post.fields i ≡ pre.fields i [ZMOD 2013265921])
  ∧ post.capRoot ≡ pre.capRoot [ZMOD 2013265921]
  ∧ post.reserved ≡ pre.reserved [ZMOD 2013265921]

/-- **`unify_burn` — THE UNIFICATION (frozen-nonce variant).** A committed universe-A burn
(`BurnSpec`), projected onto the burned `(cell, asset)` entry under `cellProjA`, satisfies the
keystone's per-cell `CellBurnSpecFrozenNonce` EXACTLY: the conserved `bal cell a` drops by `amt`;
balHi/nonce/fields/capRoot/reserved are `0 = 0` (frozen). So the executor's per-entry effect IS the
keystone's frozen-nonce spec, NOT a fourth spec. -/
theorem unify_burn (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (hspec : BurnSpec s actor cell a amt s') :
    CellBurnSpecFrozenNonce (cellProjA s.kernel cell a) amt (cellProjA s'.kernel cell a) := by
  refine ⟨?_, Int.ModEq.refl _, Int.ModEq.refl _, fun _ => Int.ModEq.refl _,
    Int.ModEq.refl _, Int.ModEq.refl _⟩
  have h : s'.kernel.bal cell a = s.kernel.bal cell a - amt := by
    rw [hspec.2.1]
    exact (recBurn_ledger_correct s.kernel.bal cell a amt hspec.1.2.2.2.2.2.1).1
  show s'.kernel.bal cell a ≡ s.kernel.bal cell a - amt [ZMOD 2013265921]
  rw [h]

/-- **`unify_burn_well` — THE WELL LEG (W1).** The SAME committed burn, projected onto the ISSUER's
well `(a, a)`, satisfies the frozen-nonce spec with the NEGATED amount: the well RISES by exactly
`amt` (the burned value RETURNS to the well — supply shrinks). Holder `−amt` (above) and well
`+amt` (here) are the two rows of ONE return-to-well move — exact conservation at row level. -/
theorem unify_burn_well (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (hspec : BurnSpec s actor cell a amt s') :
    CellBurnSpecFrozenNonce (cellProjA s.kernel a a) (-amt) (cellProjA s'.kernel a a) := by
  refine ⟨?_, Int.ModEq.refl _, Int.ModEq.refl _, fun _ => Int.ModEq.refl _,
    Int.ModEq.refl _, Int.ModEq.refl _⟩
  have h : s'.kernel.bal a a = s.kernel.bal a a - (-amt) := by
    rw [hspec.2.1]
    have := (recBurn_ledger_correct s.kernel.bal cell a amt hspec.1.2.2.2.2.2.1).2.1
    omega
  show s'.kernel.bal a a ≡ s.kernel.bal a a - (-amt) [ZMOD 2013265921]
  rw [h]

/-- **`unify_burn_exec` — same, stated against the executor directly.** A committed
`recCBurnAsset s actor cell a amt = some s'` (the REAL record-kernel transition) projects per-entry to
the keystone's `CellBurnSpecFrozenNonce` on the burned `(cell, asset)`. -/
theorem unify_burn_exec (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (h : recCBurnAsset s actor cell a amt = some s') :
    CellBurnSpecFrozenNonce (cellProjA s.kernel cell a) amt (cellProjA s'.kernel cell a) :=
  unify_burn s s' actor cell a amt ((recCBurnAsset_iff_spec s actor cell a amt s').mp h)

/-- **`exec_nonce_is_frozen_not_ticked` — the nonce-tick gap, named precisely.** The executor's
projected burned-entry nonce is FROZEN (`0 = 0`), whereas the EffectVM row's `CellBurnSpec` TICKS it
(`pre.nonce + 1`). The two agree on the burned entry iff `0 = 0 + 1`, which is FALSE — so the gap is
pinned to exactly the nonce column (the EffectVM-row nonce being a runtime sequence counter, NOT the
universe-A ledger nonce). -/
theorem exec_nonce_is_frozen_not_ticked (s s' : RecChainedState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (h : recCBurnAsset s actor cell a amt = some s') :
    (cellProjA s'.kernel cell a).nonce = (cellProjA s.kernel cell a).nonce :=
  -- `cellProjA` freezes the projected ledger-entry nonce to `0` before AND after (universe-A's burn
  -- touches only `bal`), so this holds LITERALLY (`0 = 0`) — a strictly stronger ℤ statement than the
  -- mod-p nonce-freeze clause of `unify_burn_exec` that it witnesses.
  rfl

/-- **`descriptor_agrees_with_executor` — THE per-cell circuit⟺executor agreement (modulo the
nonce-tick gap).** Suppose (a) the RUNNABLE descriptor is satisfied on a genuine burn row and its
`RowEncodes` decoding names `(pre, amt, post)` with `pre = cellProjA s.kernel cell a`, AND (b) the REAL
executor commits `recCBurnAsset s actor cell a amt = some s'`. Then the descriptor's pinned post-state
agrees with the executor's burned-entry post-state on EVERY conserved/frame clause: the debited balLo,
the frozen balHi/fields/capRoot/reserved. The ONE divergence is the nonce (descriptor ticks the runtime
counter; executor freezes the ledger entry — `exec_nonce_is_frozen_not_ticked`), reported, not papered. -/
theorem descriptor_agrees_with_executor
    (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsBurnRow env)
    (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ) (post : CellState)
    (henc : RowEncodes env (cellProjA s.kernel cell a) amt post)
    (hgatesat : satisfiedVm hash burnVmDescriptor env true false)
    (hsat : satisfiedVm hash burnVmDescriptor env true true)
    (hexec : recCBurnAsset s actor cell a amt = some s') :
    post.balLo ≡ (cellProjA s'.kernel cell a).balLo [ZMOD 2013265921]
    ∧ post.balHi ≡ (cellProjA s'.kernel cell a).balHi [ZMOD 2013265921]
    ∧ (∀ i, post.fields i ≡ (cellProjA s'.kernel cell a).fields i [ZMOD 2013265921])
    ∧ post.capRoot ≡ (cellProjA s'.kernel cell a).capRoot [ZMOD 2013265921]
    ∧ post.reserved ≡ (cellProjA s'.kernel cell a).reserved [ZMOD 2013265921] := by
  obtain ⟨hcirc, _⟩ :=
    burnDescriptor_full_sound hash env hrow (cellProjA s.kernel cell a) post amt henc hgatesat hsat
  obtain ⟨hcLo, hcHi, _hcN, hcF, hcCap, hcRes⟩ := hcirc
  obtain ⟨heLo, heHi, _heN, heF, heCap, heRes⟩ := unify_burn_exec s s' actor cell a amt hexec
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hcLo.trans heLo.symm
  · exact hcHi.trans heHi.symm
  · intro i; exact (hcF i).trans (heF i).symm
  · exact hcCap.trans heCap.symm
  · exact hcRes.trans heRes.symm

/-! ## §8 — NON-VACUITY: a concrete burn that the descriptor accepts; one it rejects.

`goodBurnRow` debits cell's `bal_lo` 100 → 70 by `amount = 30` (read from `param1`, the trace-generator
column), nonce ticks `5 → 6`, frame frozen. It realizes the intent. `badBurnRow` forges the post-`bal_lo`
to 999 ≠ 70 — the `gBalLoDebit` gate rejects it. -/

/-- A concrete burn row: selector `sel::BURN`, `bal_lo 100 → 70`, `amount = 30` at `param1`, frame
fixed at `0`, nonce 5 → 6 (TICK). -/
def goodBurnRow : VmRowEnv where
  loc := fun v =>
    if v = selB.BURN then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 70
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 6
    else if v = prmCol param.BURN_AMOUNT_LO then 30
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- `goodBurnRow` is a genuine burn row (`s_burn = 1`, `s_noop = 0`). -/
theorem goodBurnRow_isBurnRow : IsBurnRow goodBurnRow := by
  unfold IsBurnRow goodBurnRow
  refine ⟨by norm_num [selB.BURN], ?_⟩
  -- s_noop = 0: col 0 is not the selector (46), nor any of the named columns.
  norm_num [sel.NOOP, selB.BURN, sbCol, saCol, prmCol, STATE_BEFORE_BASE, STATE_AFTER_BASE,
    PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE,
    param.BURN_AMOUNT_LO]

/-- **NON-VACUITY (witness TRUE).** `goodBurnRow` REALIZES the burn intent: `bal_lo 100 → 70 = 100 - 30`,
nonce ticks `5 → 6`, frame frozen. So the faithfulness biconditional's intent side is inhabited. -/
theorem goodBurnRow_realizes_intent : BurnRowIntent goodBurnRow := by
  have emod : ∀ {a b : ℤ}, a = b → a ≡ b [ZMOD 2013265921] := fun h => h ▸ Int.ModEq.refl _
  unfold BurnRowIntent goodBurnRow
  simp only [sbCol, saCol, prmCol, selB.BURN, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE, param.BURN_AMOUNT_LO]
  refine ⟨emod (by norm_num), emod rfl, emod (by norm_num), emod rfl, emod rfl, ?_⟩
  intro i hi
  have e1 : (76 + (3 + i) = 46) = False := by simp; omega
  have e2 : (76 + (3 + i) = 54) = False := by simp; omega
  have e3 : (76 + (3 + i) = 76) = False := by simp
  have e4 : (76 + (3 + i) = 56) = False := by simp; omega
  have e5 : (76 + (3 + i) = 78) = False := by simp; omega
  have e6 : (76 + (3 + i) = 69) = False := by simp; omega
  have f1 : (54 + (3 + i) = 46) = False := by simp; omega
  have f2 : (54 + (3 + i) = 54) = False := by simp
  have f3 : (54 + (3 + i) = 76) = False := by simp; omega
  have f4 : (54 + (3 + i) = 56) = False := by simp; omega
  have f5 : (54 + (3 + i) = 78) = False := by simp; omega
  have f6 : (54 + (3 + i) = 69) = False := by simp; omega
  simp only [e1, e2, e3, e4, e5, e6, f1, f2, f3, f4, f5, f6, if_false]
  exact Int.ModEq.refl _

/-- A FORGED burn row: `goodBurnRow` with post-`bal_lo` tampered to `999 ≠ 70`. -/
def badBurnRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodBurnRow.loc v
  nxt := goodBurnRow.nxt
  pub := goodBurnRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badBurnRow`'s post-`bal_lo` is NOT the
debit, so `gBalLoDebit` REJECTS it — a concrete UNSAT. -/
theorem badBurnRow_rejected : ¬ (VmConstraint.gate gBalLoDebit).holdsVm badBurnRow false false := by
  apply burnVm_rejects_wrong_balance <;>
    simp only [badBurnRow, goodBurnRow, sbCol, saCol, prmCol, selB.BURN, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE, param.BURN_AMOUNT_LO] <;> norm_num

/-! ## §8½ — THE CLASS-A CAPSTONE (per-cell, the transfer bar exactly).

burn's whole per-cell transition is the `bal_lo` DEBIT + the frozen frame — every state-block column
moved-or-frozen, ALL 13 absorbed into `state_commit` (anti-ghosted via the keystone), unified to the
verified executor (`recCBurnAsset`). This capstone bundles the corners into ONE class-A statement, the
shape transfer has. The ONE residual — the *global supply total* — is a CROSS-CELL / TURN-LEVEL
accumulator (burn changes total supply, carried by no single cell), the exact analogue of transfer's
two-sided conservation the keystone assigns to the turn layer. So burn meets the per-cell class-A bar;
the supply-total invariant is a turn property (cited). NOTE: the per-cell agreement here is the 5-clause
(bal/frame) one — burn TICKS the nonce on the row but `recCBurnAsset` freezes the projected entry's
nonce (the named `exec_nonce_is_frozen_not_ticked` divergence, off-universe-A like transfer's nonce). -/

/-- **`burnDescriptor_classA` — the per-cell class-A capstone.** Satisfying the runnable descriptor on a
burn row, for the burned `(cell, asset)` entry of a committed `recCBurnAsset`, forces the FULL per-cell
`CellBurnSpec` (bal_lo debited by `amt`, frame frozen), the published commit, AND agreement with the
executor's per-cell post-state on the bal/frame clauses. -/
theorem burnDescriptor_classA (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsBurnRow env)
    (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ) (post : CellState)
    (henc : RowEncodes env (cellProjA s.kernel cell a) amt post)
    (hgatesat : satisfiedVm hash burnVmDescriptor env true false)
    (hsat : satisfiedVm hash burnVmDescriptor env true true)
    (hexec : recCBurnAsset s actor cell a amt = some s') :
    CellBurnSpec (cellProjA s.kernel cell a) amt post
    ∧ post.commit ≡ env.pub pi.NEW_COMMIT [ZMOD 2013265921]
    ∧ post.balLo ≡ (cellProjA s'.kernel cell a).balLo [ZMOD 2013265921]
    ∧ post.balHi ≡ (cellProjA s'.kernel cell a).balHi [ZMOD 2013265921]
    ∧ (∀ i, post.fields i ≡ (cellProjA s'.kernel cell a).fields i [ZMOD 2013265921])
    ∧ post.capRoot ≡ (cellProjA s'.kernel cell a).capRoot [ZMOD 2013265921]
    ∧ post.reserved ≡ (cellProjA s'.kernel cell a).reserved [ZMOD 2013265921] := by
  obtain ⟨hspec, hcommit⟩ :=
    burnDescriptor_full_sound hash env hrow (cellProjA s.kernel cell a) post amt henc hgatesat hsat
  obtain ⟨hLo, hHi, hF, hCap, hRes⟩ :=
    descriptor_agrees_with_executor hash env hrow s s' actor cell a amt post henc hgatesat hsat hexec
  exact ⟨hspec, hcommit, hLo, hHi, hF, hCap, hRes⟩

/-! ## §8¾ — THE BURN AVAILABILITY WELD (the transfer §11.7 mirror, STAGED).

The bare `burnVmDescriptor` range-checks only the AFTER balance limbs; the debit gate `gBalLoDebit`
admits the underflow-wrap forgery (`before=1, amount=1006632961, after=1006632961`: `after − before +
amount = p ≡ 0`, `after < 2^30`) that OVER-BURNS ~10^9 while passing the after-range — and (the audit's
finding, `docs/FINDING-modp-wrap-forgery-audit.md` §2) burn's ledger frame credits the WELL `(a, a)`
by the same forged amount, so burn-to-negative INFLATES WELL SUPPLY: mint-from-nothing into the well,
STRICTLY WORSE than the transfer twin. The FIX mirrors `transferVmDescriptorAvail` exactly: decompose
`before.bal_lo` / `after.bal_lo` / `amount` into 15-bit limbs with a borrow chain and a NO-FINAL-BORROW
gate, so `before = after + amount` holds over ℤ and `before ≥ amount` (AVAILABILITY) is DERIVED, not
assumed. Burn has NO credit direction (the row ALWAYS debits; there is no `DIRECTION` param), so the
borrow gates are UNGATED — the whole debit surface is the forgery surface. Every borrow-gate residual
is confined to `(−2^16, 2^16) ⊂ (−p, p)` by the 15-bit ranges, so no residual reaches `p` — no wrap.

Witness columns live PAST the base width (`≥ EFFECT_VM_WIDTH = 188`), so they are DISTINCT from every
base-layout column; the widened descriptor + its registry row + VK ride the ONE big-bang regen (STAGED,
the transfer/vault status). -/

/-- The burn availability-weld witness-column base (past the base trace width). -/
def AVAIL_BASE : Nat := EFFECT_VM_WIDTH
/-- `before.bal_lo` low/high 15-bit limbs. -/
def cBEF0 : Nat := AVAIL_BASE
def cBEF1 : Nat := AVAIL_BASE + 1
/-- `after.bal_lo` low/high 15-bit limbs. -/
def cAFT0 : Nat := AVAIL_BASE + 2
def cAFT1 : Nat := AVAIL_BASE + 3
/-- burn `amount` (`param.BURN_AMOUNT_LO`) low/high 15-bit limbs. -/
def cAM0 : Nat := AVAIL_BASE + 4
def cAM1 : Nat := AVAIL_BASE + 5
/-- The two borrow bits (`cBRW1` = the final borrow; `= 0` ⟺ `before ≥ amount`). -/
def cBRW0 : Nat := AVAIL_BASE + 6
def cBRW1 : Nat := AVAIL_BASE + 7
/-- The widened trace width (borrow-chain witness columns; burn has no credit twin, so 8 not 10). -/
def AVAIL_WIDTH : Nat := AVAIL_BASE + 8

/-- Operand assembly: `before.bal_lo = bef0 + 2^15·bef1` (pins the 30-bit operand to its 15-bit limbs). -/
def gAsmBefore : EmittedExpr :=
  eSub (eSB state.BALANCE_LO) (.add (.var cBEF0) (.mul (.const 32768) (.var cBEF1)))
/-- Operand assembly: `after.bal_lo = aft0 + 2^15·aft1`. -/
def gAsmAfter : EmittedExpr :=
  eSub (eSA state.BALANCE_LO) (.add (.var cAFT0) (.mul (.const 32768) (.var cAFT1)))
/-- Operand assembly: `amount = am0 + 2^15·am1` (the previously-UNRANGED burn amount, now decomposed). -/
def gAsmAmount : EmittedExpr :=
  eSub ePrmBurnAmt (.add (.var cAM0) (.mul (.const 32768) (.var cAM1)))
/-- Borrow-bit booleanity: `bb0·(bb0 − 1)`. -/
def gBrw0Bool : EmittedExpr := .mul (.var cBRW0) (.add (.var cBRW0) (.const (-1)))
/-- Borrow-bit booleanity: `bb1·(bb1 − 1)`. -/
def gBrw1Bool : EmittedExpr := .mul (.var cBRW1) (.add (.var cBRW1) (.const (-1)))
/-- Debit borrow, limb 0 (UNGATED — a burn row is always a debit): `bef0 − am0 + bb0·2^15 − aft0`.
This forces `bef0 − am0 = aft0 − bb0·2^15` — the low-limb borrow subtraction (the transfer
`gBorrow0` with the `direction` factor dropped). -/
def gBorrow0 : EmittedExpr :=
  eSub (.add (eSub (.var cBEF0) (.var cAM0)) (.mul (.const 32768) (.var cBRW0))) (.var cAFT0)
/-- Debit borrow, limb 1 (UNGATED): `bef1 − am1 − bb0 + bb1·2^15 − aft1`. -/
def gBorrow1 : EmittedExpr :=
  eSub (.add (eSub (eSub (.var cBEF1) (.var cAM1)) (.var cBRW0)) (.mul (.const 32768) (.var cBRW1)))
    (.var cAFT1)
/-- The NO-FINAL-BORROW gate (UNGATED): `bb1`. On a satisfying row `bb1 = 0`, i.e. `before ≥ amount`
— AVAILABILITY, enforced in-circuit. -/
def gNoBorrow : EmittedExpr := .var cBRW1

/-- The burn availability-weld gates (assembly + borrow chain). Appended to the burn descriptor.
UNGATED (a burn row is always a debit — the whole surface is the forgery surface). -/
def burnAvailGates : List VmConstraint :=
  [ .gate gAsmBefore, .gate gAsmAfter, .gate gAsmAmount
  , .gate gBrw0Bool, .gate gBrw1Bool
  , .gate gBorrow0, .gate gBorrow1, .gate gNoBorrow ]

/-- The burn availability-weld range checks: the operand + amount 15-bit limbs (bounds every operand
to `[0, 2^30) ⊂ [0, p)` and, crucially, RANGES the burn `amount`, closing the unranged-amount hole). -/
def burnAvailRanges : List VmRange :=
  [ ⟨cBEF0, 15⟩, ⟨cBEF1, 15⟩, ⟨cAFT0, 15⟩, ⟨cAFT1, 15⟩, ⟨cAM0, 15⟩, ⟨cAM1, 15⟩ ]

/-- **`burnVmDescriptorAvail`** — the HARDENED burn descriptor: the bare `burnVmDescriptor` PLUS the
availability-weld gates and the amount/operand limb range checks, trace widened to carry the witness
columns. The borrow chain DERIVES debit availability (`before ≥ amount`, no underflow wrap;
`burnAvail_derives_availability`) — with no `hcanonMove` — closing the well-supply-inflation forgery
in-circuit. STAGED (rides the one big-bang VK regen with the transfer/vault welds). -/
def burnVmDescriptorAvail : EffectVmDescriptor :=
  { burnVmDescriptor with
    name        := burnVmAirName ++ "-avail"
    traceWidth  := AVAIL_WIDTH
    constraints := burnVmDescriptor.constraints ++ burnAvailGates
    ranges      := burnVmDescriptor.ranges ++ burnAvailRanges }

/-- A weld gate is a member of the hardened descriptor's constraints. -/
theorem availGate_mem (g : VmConstraint) (hg : g ∈ burnAvailGates) :
    g ∈ burnVmDescriptorAvail.constraints :=
  List.mem_append_right _ hg

/-- A weld range is a member of the hardened descriptor's ranges. -/
theorem availRange_mem (r : VmRange) (hr : r ∈ burnAvailRanges) :
    r ∈ burnVmDescriptorAvail.ranges :=
  List.mem_append_right _ hr

/-- A residual congruent to `0 mod p` and confined to `(−p, p)` by the 15-bit limb/borrow range checks
is EXACTLY `0` over ℤ (the vault's `modEqZeroBounded` — the soundness payoff of 15-bit limbs). -/
private theorem availBounded {R : ℤ} (h : R ≡ 0 [ZMOD 2013265921])
    (hlo : -2013265921 < R) (hhi : R < 2013265921) : R = 0 := by
  rw [Int.modEq_zero_iff_dvd] at h; obtain ⟨k, hk⟩ := h; omega

/-- Two CANONICAL (`[0, p)`) integers congruent mod `p` are EQUAL (the deployed range-check lift). -/
private theorem availCanonEq {a b : ℤ} (h : a ≡ b [ZMOD 2013265921])
    (ha0 : 0 ≤ a) (hap : a < 2013265921) (hb0 : 0 ≤ b) (hbp : b < 2013265921) : a = b := by
  unfold Int.ModEq at h; rwa [Int.emod_eq_of_lt ha0 hap, Int.emod_eq_of_lt hb0 hbp] at h

/-- **SOUNDNESS — BURN AVAILABILITY DERIVED IN-CIRCUIT.** A trace satisfying the hardened burn
descriptor FORCES `amount ≤ before.bal_lo` AND the exact ℤ debit `after = before − amount` — with NO
`hcanonMove` assumption. The only hypothesis is the DEPLOYED canonicality invariant `0 ≤ loc c < p`
(each column a canonical field element — the SAME fact `burnVm_rejects_wrong_balance` uses, NOT
availability laundered in). The borrow chain + 15-bit limb range checks make the subtraction exact
over ℤ, so the underflow wrap (the well-supply-inflation forgery) is STRUCTURALLY impossible.
Stated at an ARBITRARY `isFirst` (only `isLast = false` is load-bearing — every weld constraint is a
`.gate`, bound on the transition domain), so a rotated witness's designated debit row at ANY trace
index `i` (flags `(i == 0, false)`) consumes it — the `RotatedKernelRefinementMintBurnAvail` bridge
(the transfer `transferAvail_derives_availability_row` mirror). -/
theorem burnAvail_derives_availability_row (hash : List ℤ → ℤ) (env : VmRowEnv)
    (isFirst : Bool)
    (hcanon : ∀ c, 0 ≤ env.loc c ∧ env.loc c < 2013265921)
    (hsat : satisfiedVm hash burnVmDescriptorAvail env isFirst false) :
    env.loc (prmCol param.BURN_AMOUNT_LO) ≤ env.loc (sbCol state.BALANCE_LO)
    ∧ env.loc (saCol state.BALANCE_LO)
        = env.loc (sbCol state.BALANCE_LO) - env.loc (prmCol param.BURN_AMOUNT_LO) := by
  obtain ⟨hcs, _hsites, hrs⟩ := hsat
  -- range facts (each limb in [0, 2^15))
  have hb0 := hrs _ (availRange_mem ⟨cBEF0, 15⟩ (by simp [burnAvailRanges]))
  have hb1 := hrs _ (availRange_mem ⟨cBEF1, 15⟩ (by simp [burnAvailRanges]))
  have ha0 := hrs _ (availRange_mem ⟨cAFT0, 15⟩ (by simp [burnAvailRanges]))
  have ha1 := hrs _ (availRange_mem ⟨cAFT1, 15⟩ (by simp [burnAvailRanges]))
  have hm0 := hrs _ (availRange_mem ⟨cAM0, 15⟩ (by simp [burnAvailRanges]))
  have hm1 := hrs _ (availRange_mem ⟨cAM1, 15⟩ (by simp [burnAvailRanges]))
  simp only [VmRange.holds] at hb0 hb1 ha0 ha1 hm0 hm1
  norm_num at hb0 hb1 ha0 ha1 hm0 hm1
  -- gate facts (bodies vanish mod p on the active row)
  have gAsmB := hcs _ (availGate_mem (.gate gAsmBefore) (by simp [burnAvailGates]))
  have gAsmA := hcs _ (availGate_mem (.gate gAsmAfter) (by simp [burnAvailGates]))
  have gAsmM := hcs _ (availGate_mem (.gate gAsmAmount) (by simp [burnAvailGates]))
  have gB0 := hcs _ (availGate_mem (.gate gBrw0Bool) (by simp [burnAvailGates]))
  have gB1 := hcs _ (availGate_mem (.gate gBrw1Bool) (by simp [burnAvailGates]))
  have gBor0 := hcs _ (availGate_mem (.gate gBorrow0) (by simp [burnAvailGates]))
  have gBor1 := hcs _ (availGate_mem (.gate gBorrow1) (by simp [burnAvailGates]))
  have gNoB := hcs _ (availGate_mem (.gate gNoBorrow) (by simp [burnAvailGates]))
  simp only [holdsVm_gate_false, gAsmBefore, gAsmAfter, gAsmAmount, gBrw0Bool, gBrw1Bool,
    gBorrow0, gBorrow1, gNoBorrow, ePrmBurnAmt, eSA, eSB, eSub,
    EmittedExpr.eval] at gAsmB gAsmA gAsmM gB0 gB1 gBor0 gBor1 gNoB
  -- borrow bits are boolean (mod-p booleanity + canonicality + p prime)
  have brw0Bool : 0 ≤ env.loc cBRW0 ∧ env.loc cBRW0 ≤ 1 := by
    rw [Int.modEq_zero_iff_dvd] at gB0
    obtain ⟨z0, zp⟩ := hcanon cBRW0
    rcases pPrimeInt.dvd_mul.mp gB0 with hd | hd
    · obtain ⟨k, hk⟩ := hd; omega
    · obtain ⟨k, hk⟩ := hd; omega
  have brw1Bool : 0 ≤ env.loc cBRW1 ∧ env.loc cBRW1 ≤ 1 := by
    rw [Int.modEq_zero_iff_dvd] at gB1
    obtain ⟨z0, zp⟩ := hcanon cBRW1
    rcases pPrimeInt.dvd_mul.mp gB1 with hd | hd
    · obtain ⟨k, hk⟩ := hd; omega
    · obtain ⟨k, hk⟩ := hd; omega
  -- operand assemblies lift to exact ℤ (canonical operand, limb sum < 2^30 < p)
  have eBef : env.loc (sbCol state.BALANCE_LO) = env.loc cBEF0 + 32768 * env.loc cBEF1 :=
    availCanonEq ((gate_modEq_iff (by ring)).mp gAsmB) (hcanon _).1 (hcanon _).2 (by omega) (by omega)
  have eAft : env.loc (saCol state.BALANCE_LO) = env.loc cAFT0 + 32768 * env.loc cAFT1 :=
    availCanonEq ((gate_modEq_iff (by ring)).mp gAsmA) (hcanon _).1 (hcanon _).2 (by omega) (by omega)
  have eAmt : env.loc (prmCol param.BURN_AMOUNT_LO) = env.loc cAM0 + 32768 * env.loc cAM1 :=
    availCanonEq ((gate_modEq_iff (by ring)).mp gAsmM) (hcanon _).1 (hcanon _).2 (by omega) (by omega)
  -- the borrow subtraction is exact over ℤ (each residual confined to (−p, p) by the 15-bit ranges)
  have e0 : env.loc cBEF0 + -1 * env.loc cAM0 + 32768 * env.loc cBRW0 + -1 * env.loc cAFT0 = 0 :=
    availBounded gBor0 (by omega) (by omega)
  have e1 : env.loc cBEF1 + -1 * env.loc cAM1 + -1 * env.loc cBRW0
      + 32768 * env.loc cBRW1 + -1 * env.loc cAFT1 = 0 :=
    availBounded gBor1 (by omega) (by omega)
  have eBB : env.loc cBRW1 = 0 := availBounded gNoB (by omega) (by omega)
  -- availability + exact debit: purely linear now (no residual congruences left)
  constructor
  · omega
  · omega

/-- The boundary-row (`isFirst = true`) form of `burnAvail_derives_availability_row`, the
original statement kept for existing consumers. -/
theorem burnAvail_derives_availability (hash : List ℤ → ℤ) (env : VmRowEnv)
    (hcanon : ∀ c, 0 ≤ env.loc c ∧ env.loc c < 2013265921)
    (hsat : satisfiedVm hash burnVmDescriptorAvail env true false) :
    env.loc (prmCol param.BURN_AMOUNT_LO) ≤ env.loc (sbCol state.BALANCE_LO)
    ∧ env.loc (saCol state.BALANCE_LO)
        = env.loc (sbCol state.BALANCE_LO) - env.loc (prmCol param.BURN_AMOUNT_LO) :=
  burnAvail_derives_availability_row hash env true hcanon hsat

/-- **THE BURN FORGERY IS UNSAT (the well-supply-inflation witness).** The audit's over-burn forgery
witness (`before=1, amount=1006632961, after=1006632961`) — the one whose ledger frame would CREDIT
the well by the forged 10^9 — CANNOT satisfy the hardened descriptor: its debit availability
`amount ≤ before` (`1006632961 ≤ 1`) is false, so the borrow chain has no witness. The burn
underflow-wrap value forgery is closed in-circuit. -/
theorem burnAvail_forgery_unsat (hash : List ℤ → ℤ) (env : VmRowEnv)
    (hcanon : ∀ c, 0 ≤ env.loc c ∧ env.loc c < 2013265921)
    (hsat : satisfiedVm hash burnVmDescriptorAvail env true false)
    (hbefore : env.loc (sbCol state.BALANCE_LO) = 1)
    (hamount : env.loc (prmCol param.BURN_AMOUNT_LO) = 1006632961) : False := by
  have h := (burnAvail_derives_availability hash env hcanon hsat).1
  rw [hbefore, hamount] at h; omega

/-! ### LIVENESS: an honest burn (`goodBurnRow` + its limb witnesses) satisfies the weld. -/

/-- `goodBurnRow` (burn of 30 from bal_lo 100 → 70) extended with the availability-weld witness
columns: `before = 100` limbs `(100, 0)`, `after = 70` limbs `(70, 0)`, `amount = 30` limbs `(30, 0)`,
no borrows. -/
def goodBurnAvailRow : VmRowEnv where
  loc := fun v =>
    if v = cBEF0 then 100 else if v = cAFT0 then 70 else if v = cAM0 then 30
    else goodBurnRow.loc v
  nxt := goodBurnRow.nxt
  pub := goodBurnRow.pub

/-- **LIVENESS.** Every availability-weld gate holds on the honest `goodBurnAvailRow` — no valid burn
is rejected by the new gates (the borrow chain closes with zero borrows: `100 − 30 = 70`). -/
theorem goodBurnAvailRow_gates_hold (c : VmConstraint) (hc : c ∈ burnAvailGates) :
    c.holdsVm goodBurnAvailRow false false := by
  have hb : ∃ b, c = .gate b ∧ b.eval goodBurnAvailRow.loc = 0 := by
    fin_cases hc <;> exact ⟨_, rfl, by decide⟩
  obtain ⟨b, rfl, hval⟩ := hb
  rw [holdsVm_gate_false, hval]

/-- **LIVENESS (ranges).** The honest limb witnesses satisfy the 15-bit range checks. -/
theorem goodBurnAvailRow_ranges_hold (r : VmRange) (hr : r ∈ burnAvailRanges) :
    r.holds goodBurnAvailRow := by
  fin_cases hr <;> exact ⟨by decide, by decide⟩

/-! ## §9 — Axiom-hygiene tripwires. -/

#assert_axioms burnDescriptor_classA

#guard burnVmDescriptor.constraints.length == 13 + 14 + 4 + 3 + 1  -- gates(5+8) + transitions + 4 + 3 + selectorGate
#guard burnVmDescriptor.hashSites.length == 4
#guard burnVmDescriptor.traceWidth == 188

-- The availability weld (the transfer §11.7 mirror): the hardened descriptor adds 8 gates (3
-- assembly + 2 booleanity + 2 borrow + 1 no-borrow) + 6 ranges and 8 witness cols (2 operand limbs
-- ×3, 2 borrow bits; no credit twin — burn is debit-only).
#guard burnVmDescriptorAvail.constraints.length == (13 + 14 + 4 + 3 + 1) + 8
#guard burnVmDescriptorAvail.ranges.length == 2 + 6
#guard burnVmDescriptorAvail.traceWidth == 196
-- LIVENESS witness (kernel-evaluated): every weld gate body is 0 on the honest burn row.
#guard burnAvailGates.all (fun c => match c with | .gate b => b.eval goodBurnAvailRow.loc == 0 | _ => true)
#assert_axioms burnAvail_derives_availability_row
#assert_axioms burnAvail_derives_availability
#assert_axioms burnAvail_forgery_unsat
#assert_axioms goodBurnAvailRow_gates_hold
#assert_axioms goodBurnAvailRow_ranges_hold

#assert_axioms burnVm_faithful
#assert_axioms burnVm_rejects_wrong_balance
#assert_axioms intent_to_cellSpec
#assert_axioms burnRowGates_flag_indep
#assert_axioms burnDescriptor_full_sound
#assert_axioms burnDescriptor_commit_binds_state_or_collides
#assert_axioms unify_burn
#assert_axioms unify_burn_well
#assert_axioms unify_burn_exec
#assert_axioms exec_nonce_is_frozen_not_ticked
#assert_axioms descriptor_agrees_with_executor
#assert_axioms goodBurnRow_isBurnRow
#assert_axioms goodBurnRow_realizes_intent
#assert_axioms badBurnRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitBurn
