/-
# Dregg2.Circuit.Emit.EffectVmEmitMint — the SUPPLY-MINT effect `mintA`, EMITTED onto the runnable
  EffectVM `bal_lo` (balance) column, with its full-state per-cell soundness, the anti-ghost commitment
  tooth, and the connector to the validated universe-A `MintASpec` / `recCMintAsset`.

## The "ONE circuit" thesis for `mintA` (the credit twin of burn)

`mintA` is the per-asset privileged-supply MINT (`Spec/supplycreation.lean`): the executor CREDITS the
per-asset ledger `bal` at one `(cell, asset)` by `amt` (`recBalCredit … amt`), prepends a disclosing
receipt, and freezes the 16 non-`bal` kernel fields. Its validation `execMintA_iff_spec` is DONE; this
module emits the SAME effect onto the EffectVM row and welds the two.

The EffectVM block carries the conserved balance as the `bal_lo` limb. A mint is a `bal_lo` COLUMN
CREDIT: post-`bal_lo` = pre PLUS `value_lo` (`param1`), the sequence nonce TICKED (`+1`, the runtime
non-NoOp invariant), the economic frame frozen, the post-state bound into `state_commit` via the
GROUP-4 hash chain. `mintVmDescriptor` emits exactly that (credit gate `new_bal_lo - old_bal_lo -
param1 = 0`, the nonce-tick gate, the frame frozen).

## What is PROVED

  * `mintVm_faithful` — emitted per-row gates ⟺ `MintRowIntent` (credit + frame freeze).
  * `mintDescriptor_full_sound` — satisfying the descriptor under `RowEncodes` forces `CellMintSpec`
    AND publishes `post.commit = PI[NEW_COMMIT]`.
  * `mintDescriptor_commit_binds_state` — anti-ghost (reuses the transfer keystone; same hash chain).
  * `unify_mint` / `unify_mint_exec` — a committed `MintASpec` (= `recCMintAsset`), projected per
    `(cell, asset)`, satisfies `CellMintSpec` EXACTLY (the conserved `bal cell a` rises by `amt`; frame
    `0 = 0`). The runnable column transition IS universe-A's `bal`-ledger transition.

## BOUNDARY

  * PER-CELL / PER-ROW (single ledger entry's credit + commitment binding). Cross-row composition + the
    disclosing log receipt = the turn layer, cited.
  * The `(cell, asset)` index + the `mintAdmit` authority/non-negativity/liveness GUARD have no row
    column; they live in universe-A's spec (cited).
  * NONCE: the descriptor TICKS the on-trace sequence nonce (`after = before + 1`, the runtime
    `new_state.nonce += 1` on every non-NoOp row — like burn/transfer); universe-A's `recCMintAsset`
    FREEZES the ledger nonce. The §7 connector reconciles this exactly as burn (`CellMintSpecFrozenNonce`
    + `exec_nonce_is_frozen_not_ticked`), the net being the turn prologue's single tick. (RECONCILED
    with the runtime in the cutover — the earlier descriptor wrongly froze the nonce + read the credit
    from `param0`.)
  * CREDIT COLUMN: the runtime credits `param1 = value_lo` (`air.rs` `bm_val_lo = p1`), not `param0`
    (= MINT_HASH); the descriptor reads `param1`.
  * `state.RESERVED` not absorbed by any hash-site (inherited transfer-keystone finding).

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 CR = NAMED hypothesis.
Imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.supplycreation

namespace Dregg2.Circuit.Emit.EffectVmEmitMint

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA ePrm eSub gNonce eSelNoop transitionAll boundaryFirstPins boundaryLastPins
   transferHashSites boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState absorbedCols)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Spec.SupplyCreation

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0½ — Field-faithful (`Int.ModEq` mod the BabyBear prime `p = 2013265921`) lift helpers.

`VmConstraint.holdsVm` now asserts the gate residual is `≡ 0 [ZMOD p]` (the DEPLOYED field), not `= 0`
over ℤ. These three mechanical helpers move between a gate residual `r ≡ 0` and the equivalent
column relation `a ≡ b` (with `r = a - b`, discharged by `ring`), and lift an honest ℤ equality into
the field. No canonicality is needed for the POSITIVE direction: a field-valid canonical trace can
have ℤ residual `= p ≠ 0`, so the row intent/spec are stated mod `p` — that IS the faithful claim.
(The NEGATIVE teeth keep their ℤ inequalities and carry EXPLICIT canonicality to reject in the field.) -/

/-- An honest ℤ equality lifts into the field. -/
private theorem eq_lift {a b : ℤ} (h : a = b) : a ≡ b [ZMOD 2013265921] := by rw [h]

/-- A gate residual `r ≡ 0` (with `r = a - b`) IS the column relation `a ≡ b` in the field. -/
private theorem intent_of_res {r a b : ℤ} (hr : r = a - b) (h : r ≡ 0 [ZMOD 2013265921]) :
    a ≡ b [ZMOD 2013265921] := by
  rw [Int.modEq_zero_iff_dvd] at h
  rw [hr] at h
  rw [Int.modEq_iff_dvd]
  omega

/-- Conversely, the field column relation `a ≡ b` forces the gate residual `r ≡ 0` (with `r = a - b`). -/
private theorem gate_of_res {r a b : ℤ} (hr : r = a - b) (h : a ≡ b [ZMOD 2013265921]) :
    r ≡ 0 [ZMOD 2013265921] := by
  rw [Int.modEq_iff_dvd] at h
  rw [hr, Int.modEq_zero_iff_dvd]
  omega

/-! ## §0 — Selector + value column for the BridgeMint effect row.

RECONCILED WITH THE RUNTIME (`circuit/src/effect_vm/{trace,air}.rs`, the cutover model-found seam).
The runtime's `Effect::BridgeMint { mint_hash, value_lo, .. }` writes `param0 = mint_hash`,
`param1 = value_lo`, CREDITS `new_bal_lo = old_bal_lo + value_lo (= p1)`, GATES by `s_bridgemint`
(`sel::BRIDGE_MINT = 40`), and TICKS the nonce (`new_state.nonce += 1`). The earlier descriptor read
the credit from `param.AMOUNT = param0` (the runtime's MINT_HASH), froze the nonce, and named the
selector `4`. The credit→param1 and nonce-tick are corrected here (the selector constant is
descriptive only — it appears in no gate, only the row predicate + witness — and is set to the
runtime value too). The rotated BridgeMint registry leg (`mintV3`) carries the same corrections
(`EffectVmEmitRotationV3.mintTickFace`). -/

namespace selM
/-- The `BridgeMint` effect selector column (runtime `sel::BRIDGE_MINT = 40`). The earlier `4` was a
descriptive mismodel; it appears in no gate (only `IsMintRow` + the witness), so this is a
non-load-bearing reconcile. -/
def MINT : Nat := 40
end selM

def eSelMint : EmittedExpr := .var selM.MINT

/-- The runtime value column for the credit: `param1` (value_lo) — `air.rs` `bm_val_lo = p1`. NOT
`param.AMOUNT = param0` (the runtime's MINT_HASH). (Runtime `param::NEW_VALUE = 1`; the param
namespace carries only `AMOUNT`/`DIRECTION`, so this is a LOCAL constant naming the value column.) -/
def VALUE_LO : Nat := 1

/-! ## §1 — The mint row gates (credit on bal_lo at `param1`, nonce TICK, frame freeze). -/

/-- Balance-lo CREDIT body reading the RUNTIME value column `param1` (value_lo):
`new_bal_lo - old_bal_lo - param1` (so `new = old + value_lo`). -/
def gBalLoCredit : EmittedExpr :=
  .add (eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)) (.mul (.const (-1)) (ePrm VALUE_LO))

def gBalHiFix : EmittedExpr := eSub (eSA state.BALANCE_HI) (eSB state.BALANCE_HI)
def gCapFix : EmittedExpr := eSub (eSA state.CAP_ROOT) (eSB state.CAP_ROOT)
def gResFix : EmittedExpr := eSub (eSA state.RESERVED) (eSB state.RESERVED)
def gFieldFix (i : Nat) : EmittedExpr := eSub (eSA (state.FIELD_BASE + i)) (eSB (state.FIELD_BASE + i))

def gFieldFixAll : List VmConstraint :=
  (List.range 8).map (fun i => VmConstraint.gate (gFieldFix i))

/-- The BridgeMint-specialized per-row gates: balance credit (at `param1`), nonce TICK (the
transfer/noteSpend `gNonce` gate), frame freeze. -/
def mintRowGates : List VmConstraint :=
  [ .gate gBalLoCredit, .gate gBalHiFix, .gate gNonce, .gate gCapFix, .gate gResFix ]
  ++ gFieldFixAll

/-! ## §2 — The emitted MINT descriptor. -/

def mintVmAirName : String := "dregg-effectvm-mint-v1"

/-- **`mintVmDescriptor`** — the `mintA` effect's full concrete circuit (credit/freeze gates ++
transitions ++ boundary PI pins, GROUP-4 hash sites, balance range checks). -/
def mintVmDescriptor : EffectVmDescriptor :=
  { name := mintVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 42
  , constraints := mintRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The MINT ROW INTENT. -/

/-- **`MintRowIntent env`** — on an active BridgeMint row: `bal_lo` rises by `param1` (value_lo), the
nonce TICKS (`after = before + 1`, the runtime `new_state.nonce += 1`), the rest of the block frozen.
(Like burn — its economic twin — the runtime ticks the on-trace sequence nonce on every non-NoOp row;
the executor's frozen ledger nonce is reconciled at the §7 connector.) -/
def MintRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO)
      ≡ env.loc (sbCol state.BALANCE_LO) + env.loc (prmCol VALUE_LO) [ZMOD 2013265921]
  ∧ env.loc (saCol state.BALANCE_HI) ≡ env.loc (sbCol state.BALANCE_HI) [ZMOD 2013265921]
  ∧ env.loc (saCol state.NONCE) ≡ env.loc (sbCol state.NONCE) + 1 [ZMOD 2013265921]
  ∧ env.loc (saCol state.CAP_ROOT) ≡ env.loc (sbCol state.CAP_ROOT) [ZMOD 2013265921]
  ∧ env.loc (saCol state.RESERVED) ≡ env.loc (sbCol state.RESERVED) [ZMOD 2013265921]
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i))
      ≡ env.loc (sbCol (state.FIELD_BASE + i)) [ZMOD 2013265921])

/-- The row is a BridgeMint row: `s_bridge_mint = 1`, `s_noop = 0`. The `s_noop = 0` clause is what
the nonce-tick gate factors on (a BridgeMint row is non-NoOp, so the nonce ticks). -/
def IsMintRow (env : VmRowEnv) : Prop :=
  env.loc selM.MINT = 1 ∧ env.loc sel.NOOP = 0

/-! ## §4 — FAITHFULNESS (on an active BridgeMint row, as burn). -/

/-- **`mintVm_faithful`.** On a BridgeMint row the emitted gates hold IFF the mint intent holds. The
`IsMintRow` premise (`s_noop = 0`) resolves the tick gate to `after_nonce = before_nonce + 1`,
exactly as `burnVm_faithful`. -/
theorem mintVm_faithful (env : VmRowEnv) (hrow : IsMintRow env) :
    (∀ c ∈ mintRowGates, c.holdsVm env false false) ↔ MintRowIntent env := by
  obtain ⟨_hsM, hsN⟩ := hrow
  unfold mintRowGates gFieldFixAll MintRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoCredit) (by simp)
    have hHi := h (.gate gBalHiFix) (by simp)
    have hNon := h (.gate gNonce) (by simp)
    have hCap := h (.gate gCapFix) (by simp)
    have hRes := h (.gate gResFix) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldFix i)) := by
      intro i hi; apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]; exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoCredit, gBalHiFix, gNonce, gCapFix, gResFix,
      eSA, eSB, ePrm, eSub, eSelNoop, EmittedExpr.eval] at hLo hHi hNon hCap hRes
    rw [hsN] at hNon
    refine ⟨intent_of_res (by ring) hLo, intent_of_res (by ring) hHi, intent_of_res (by ring) hNon,
      intent_of_res (by ring) hCap, intent_of_res (by ring) hRes, ?_⟩
    intro i hi
    have := hFld i hi
    simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval] at this
    exact intent_of_res (by ring) this
  · rintro ⟨hLo, hHi, hNon, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gBalLoCredit, eSA, eSB, ePrm, eSub, EmittedExpr.eval]
      exact gate_of_res (by ring) hLo
    · simp only [VmConstraint.holdsVm, gBalHiFix, eSA, eSB, eSub, EmittedExpr.eval]
      exact gate_of_res (by ring) hHi
    · simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
      rw [hsN]; exact gate_of_res (by ring) hNon
    · simp only [VmConstraint.holdsVm, gCapFix, eSA, eSB, eSub, EmittedExpr.eval]
      exact gate_of_res (by ring) hCap
    · simp only [VmConstraint.holdsVm, gResFix, eSA, eSB, eSub, EmittedExpr.eval]
      exact gate_of_res (by ring) hRes
    · simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval]
      exact gate_of_res (by ring) (hFld i hi)

/-- **Anti-ghost (balance tamper).** A BridgeMint row whose post-`bal_lo` is NOT `old + value_lo`
(`param1`) fails the `gBalLoCredit` gate (UNSAT). Under the field-faithful denotation the gate residual
is checked mod `p = 2013265921`, so an ℤ-tampered post-balance is rejected ONLY when it cannot alias the
credit through a field wrap. We carry the EXPLICIT canonicality the deployed range-checks supply — the
post-limb `bal_lo` and the (non-overflowing) credit `old + value_lo` both live in `[0, p)` (`Mint`'s
descriptor DOES carry `⟨saCol BALANCE_LO, 30⟩`, discharged downstream; the row-level tooth takes them as
NAMED hypotheses). With no wrap the residual is pinned to `0`, so `p ∣ residual → residual = 0`,
contradicting the tamper (`omega`; the residual is linear, so no primality is needed — unlike the
product-shaped `selectorGate_rejects_wrong_selector`). The tooth is KEPT, not dropped. -/
theorem mintVm_rejects_wrong_balance (env : VmRowEnv)
    (hcaLo : 0 ≤ env.loc (saCol state.BALANCE_LO))
    (hcaLo' : env.loc (saCol state.BALANCE_LO) < 2013265921)
    (hcSum : 0 ≤ env.loc (sbCol state.BALANCE_LO) + env.loc (prmCol VALUE_LO))
    (hcSum' : env.loc (sbCol state.BALANCE_LO) + env.loc (prmCol VALUE_LO) < 2013265921)
    (hwrong : env.loc (saCol state.BALANCE_LO)
      ≠ env.loc (sbCol state.BALANCE_LO) + env.loc (prmCol VALUE_LO)) :
    ¬ (VmConstraint.gate gBalLoCredit).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoCredit, eSA, eSB, ePrm, eSub, EmittedExpr.eval]
  intro h
  rw [Int.modEq_zero_iff_dvd] at h
  obtain ⟨k, hk⟩ := h
  apply hwrong
  omega

/-- **Anti-ghost (wrong nonce delta).** On a BridgeMint row a forged nonce delta
(`after_nonce ≠ before_nonce + 1` — e.g. the passthrough the FREEZE descriptor wrongly accepted)
fails the tick gate (`gNonce`) and is UNSAT. Field-faithful: the tick residual is checked mod `p`, so
we carry the EXPLICIT canonicality (post-nonce and the ticked pre-nonce both in `[0, p)`, the deployed
sequence-counter range) that pins the residual to `0` under `p ∣ residual`, contradicting the forged
delta (`omega`, linear residual — no primality). -/
theorem mintVm_rejects_wrong_nonce_delta (env : VmRowEnv) (hrow : IsMintRow env)
    (hcaN : 0 ≤ env.loc (saCol state.NONCE))
    (hcaN' : env.loc (saCol state.NONCE) < 2013265921)
    (hcbN : 0 ≤ env.loc (sbCol state.NONCE) + 1)
    (hcbN' : env.loc (sbCol state.NONCE) + 1 < 2013265921)
    (hwrong : env.loc (saCol state.NONCE) ≠ env.loc (sbCol state.NONCE) + 1) :
    ¬ (VmConstraint.gate gNonce).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
  rw [hrow.2]
  intro h
  rw [Int.modEq_zero_iff_dvd] at h
  obtain ⟨k, hk⟩ := h
  apply hwrong
  omega

/-! ## §5 — `CellMintSpec` + `RowEncodes` → structured per-cell soundness. -/

/-- The per-cell mint spec (EffectVM-row image): balLo rises by `amt` (the runtime `value_lo` at
`param1`), the on-trace sequence nonce TICKS (`post.nonce = pre.nonce + 1`, the runtime
`new_state.nonce += 1`), the whole rest of the block frozen. Like burn, the runtime row ticks the
sequence nonce; the executor's frozen ledger nonce is the §7 connector's reconcile. -/
def CellMintSpec (pre : CellState) (amt : ℤ) (post : CellState) : Prop :=
  post.balLo ≡ pre.balLo + amt [ZMOD 2013265921]
  ∧ post.balHi ≡ pre.balHi [ZMOD 2013265921]
  ∧ post.nonce ≡ pre.nonce + 1 [ZMOD 2013265921]
  ∧ (∀ i : Fin 8, post.fields i ≡ pre.fields i [ZMOD 2013265921])
  ∧ post.capRoot ≡ pre.capRoot [ZMOD 2013265921]
  ∧ post.reserved ≡ pre.reserved [ZMOD 2013265921]

def RowEncodes (env : VmRowEnv) (pre : CellState) (amt : ℤ) (post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (sbCol state.STATE_COMMIT) = pre.commit
  ∧ env.loc (prmCol VALUE_LO) = amt
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved
  ∧ env.loc (saCol state.STATE_COMMIT) = post.commit
  ∧ env.pub pi.OLD_COMMIT = pre.commit
  ∧ env.pub pi.NEW_COMMIT = post.commit

theorem intent_to_cellSpec (env : VmRowEnv) (pre post : CellState) (amt : ℤ)
    (henc : RowEncodes env pre amt post) (hint : MintRowIntent env) :
    CellMintSpec pre amt post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC, hpAmt,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hpAmt, ← hsaLo, ← hsbLo]; exact hbal
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · rw [← hsaN, ← hsbN]; exact hnon
  · intro i; rw [← hsaF i, ← hsbF i]; exact hfld i.val i.isLt
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

/-- The mint row-gates are `.gate`s; under the deployed `when_transition()` they bind on every row
but the last, so their body content is available at the ACTIVE row (`isLast = false`). This restates
that content at the canonical `false false` flags. It is NOT flag-INDEPENDENT (the unfaithful claim):
the gate content genuinely does not exist on the wrap row (`isLast = true`), so the hypothesis is
taken at `b2 = false`. -/
theorem mintRowGates_flag_indep (env : VmRowEnv) (b1 : Bool)
    (h : ∀ c ∈ mintRowGates, c.holdsVm env b1 false) :
    ∀ c ∈ mintRowGates, c.holdsVm env false false := by
  intro c hc
  have := h c hc
  unfold mintRowGates gFieldFixAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using this

/-- **`mintDescriptor_full_sound`.** Satisfying the WHOLE descriptor under `RowEncodes` forces the
structured per-cell `CellMintSpec` AND publishes `post.commit = PI[NEW_COMMIT]`. -/
theorem mintDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsMintRow env)
    (pre post : CellState) (amt : ℤ)
    (henc : RowEncodes env pre amt post)
    (hgatesat : satisfiedVm hash mintVmDescriptor env true false)
    (hsat : satisfiedVm hash mintVmDescriptor env true true) :
    CellMintSpec pre amt post ∧ post.commit ≡ env.pub pi.NEW_COMMIT [ZMOD 2013265921] := by
  obtain ⟨hcs, _hsites⟩ := hsat
  obtain ⟨hcsT, _⟩ := hgatesat
  have hgates : ∀ c ∈ mintRowGates, c.holdsVm env true false := by
    intro c hc; apply hcsT
    unfold mintVmDescriptor; simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl hc))
  have hgates' := mintRowGates_flag_indep env true hgates
  have hint := (mintVm_faithful env hrow).mp hgates'
  refine ⟨intent_to_cellSpec env pre post amt henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ mintVmDescriptor.constraints := by
      unfold mintVmDescriptor; simp only [List.mem_append]; exact Or.inr hc
    have hh := hcs c hmem
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢; exact hh
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact (boundaryLast_pins env hlast).1

/-! ## §6 — ANTI-GHOST COMMITMENT TOOTH (reused from the transfer keystone, same hash chain). -/

theorem mint_sites_eq : mintVmDescriptor.hashSites = transferHashSites := rfl

/-- **`mintDescriptor_commit_binds_state` — the anti-ghost tooth for mint.** Two rows satisfying the
mint descriptor's hash-sites and publishing the SAME `NEW_COMMIT` have IDENTICAL absorbed after-state. -/
theorem mintDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ transferHashSites)
    (hs₂ : siteHoldsAll hash e₂ transferHashSites)
    (hpubLo₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpubLo₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ :=
  Dregg2.Circuit.Emit.EffectVmEmitTransferSound.absorbed_determined_by_commit
    hash hCR e₁ e₂ hs₁ hs₂ (by rw [hpubLo₁, hpubLo₂, hpub])

/-! ## §7 — THE CONNECTOR — `cellProjA` to universe-A's `MintASpec` / `recCMintAsset`. -/

/-- Project ledger entry `(c, a)` of `k` into the keystone's `CellState` (balLo = `bal c a`; rest `0`). -/
def cellProjA (k : RecordKernelState) (c : CellId) (a : AssetId) : CellState where
  balLo    := k.bal c a
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-! ### The ONE genuine divergence (mirroring burn + the transfer keystone): the EffectVM row TICKS
the runtime nonce; universe-A's mint FREEZES the ledger-entry nonce.

`CellMintSpec` demands `post.nonce = pre.nonce + 1` (the runtime per-cell sequence counter the
EffectVM row increments on every non-NoOp effect, matching the validated hand-AIR's `s_bridgemint`
row + the global nonce gate). Universe-A's `recCMintAsset` touches ONLY the `bal` ledger — the
projected entry's nonce is `0` before AND after (`cellProjA` sets it to `0`). So the executor's
per-entry image is the nonce-FREEZE variant. We unify against THAT and name the gap exactly, as
`EffectVmEmitBurn` does (`exec_nonce_is_frozen_not_ticked`). -/

/-- The executor's genuine per-entry image: `CellMintSpec` with the nonce-TICK replaced by
nonce-FREEZE. Every other clause (balLo credit, balHi/fields/capRoot/reserved freeze) is identical. -/
def CellMintSpecFrozenNonce (pre : CellState) (amt : ℤ) (post : CellState) : Prop :=
  post.balLo ≡ pre.balLo + amt [ZMOD 2013265921]
  ∧ post.balHi ≡ pre.balHi [ZMOD 2013265921]
  ∧ post.nonce ≡ pre.nonce [ZMOD 2013265921]   -- FROZEN (executor ledger image) — the row spec demands `+ 1`
  ∧ (∀ i : Fin 8, post.fields i ≡ pre.fields i [ZMOD 2013265921])
  ∧ post.capRoot ≡ pre.capRoot [ZMOD 2013265921]
  ∧ post.reserved ≡ pre.reserved [ZMOD 2013265921]

/-- **`unify_mint` — THE UNIFICATION (the recipient leg, frozen-nonce variant).** A committed
universe-A mint (`MintASpec`, W1: the issuer-move), projected onto the RECIPIENT's `(cell, a)` entry
under `cellProjA`, satisfies `CellMintSpecFrozenNonce` EXACTLY: the recipient's `bal cell a` rises by
`amt`; frame `0 = 0`. So the executor's per-entry effect IS the keystone's frozen-nonce spec at the
recipient, NOT a fourth spec. The WELL leg — the issuer's row falling by the same `amt`, which is
what makes the sum exact — is `unify_mint_well` below. -/
theorem unify_mint (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (hspec : MintASpec s actor cell a amt s') :
    CellMintSpecFrozenNonce (cellProjA s.kernel cell a) amt (cellProjA s'.kernel cell a) := by
  refine ⟨?_, Int.ModEq.refl _, Int.ModEq.refl _, fun _ => Int.ModEq.refl _,
    Int.ModEq.refl _, Int.ModEq.refl _⟩
  show s'.kernel.bal cell a ≡ s.kernel.bal cell a + amt [ZMOD 2013265921]
  have heq : s'.kernel.bal cell a = s.kernel.bal cell a + amt := by
    rw [hspec.2.1]
    exact (recTransferBal_mint_correct s.kernel.bal cell a amt hspec.1.2.2.2.2.1).2.1
  rw [heq]

/-- **`unify_mint_well` — THE WELL LEG (W1).** The SAME committed mint, projected onto the ISSUER's
well `(a, a)`, satisfies the frozen-nonce spec with the NEGATED amount: the well falls by exactly
`amt` (the negative-capable well carries −supply). Recipient `+amt` (above) and well `−amt` (here)
are the two rows of ONE issuer-move — their sum is the exact-conservation content at row level. -/
theorem unify_mint_well (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (hspec : MintASpec s actor cell a amt s') :
    CellMintSpecFrozenNonce (cellProjA s.kernel a a) (-amt) (cellProjA s'.kernel a a) := by
  refine ⟨?_, Int.ModEq.refl _, Int.ModEq.refl _, fun _ => Int.ModEq.refl _,
    Int.ModEq.refl _, Int.ModEq.refl _⟩
  show s'.kernel.bal a a ≡ s.kernel.bal a a + (-amt) [ZMOD 2013265921]
  have heq : s'.kernel.bal a a = s.kernel.bal a a + (-amt) := by
    rw [hspec.2.1]
    have := (recTransferBal_mint_correct s.kernel.bal cell a amt hspec.1.2.2.2.2.1).1
    omega
  rw [heq]

/-- **`unify_mint_exec` — same, against the executor.** -/
theorem unify_mint_exec (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (h : recCMintAsset s actor cell a amt = some s') :
    CellMintSpecFrozenNonce (cellProjA s.kernel cell a) amt (cellProjA s'.kernel cell a) :=
  unify_mint s s' actor cell a amt ((recCMintAsset_iff_spec s actor cell a amt s').mp h)

/-- **`unify_mint_well_exec` — the well leg, against the executor.** -/
theorem unify_mint_well_exec (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (h : recCMintAsset s actor cell a amt = some s') :
    CellMintSpecFrozenNonce (cellProjA s.kernel a a) (-amt) (cellProjA s'.kernel a a) :=
  unify_mint_well s s' actor cell a amt ((recCMintAsset_iff_spec s actor cell a amt s').mp h)

/-- **`exec_nonce_is_frozen_not_ticked` — the nonce-tick gap, named precisely.** The executor's
projected minted-entry nonce is FROZEN (`0 = 0`), whereas the EffectVM row's `CellMintSpec` TICKS it
(`pre.nonce + 1`). The two agree on the minted entry iff `0 = 0 + 1`, which is FALSE — so the gap is
pinned to exactly the nonce column (the EffectVM-row nonce being a runtime sequence counter, NOT the
universe-A ledger nonce), exactly as burn reports it. -/
theorem exec_nonce_is_frozen_not_ticked (s s' : RecChainedState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (h : recCMintAsset s actor cell a amt = some s') :
    (cellProjA s'.kernel cell a).nonce ≡ (cellProjA s.kernel cell a).nonce [ZMOD 2013265921] :=
  (unify_mint_exec s s' actor cell a amt h).2.2.1

/-- **`descriptor_agrees_with_executor` — per-cell circuit⟺executor agreement (modulo the nonce-tick
gap).** The descriptor's pinned post-state agrees with the executor's minted-entry post-state on EVERY
conserved/frame clause (the credit + the frozen balHi/fields/capRoot/reserved). The ONE divergence is
the nonce (descriptor ticks the runtime counter; executor freezes the ledger entry —
`exec_nonce_is_frozen_not_ticked`), reported not papered, exactly as burn. -/
theorem descriptor_agrees_with_executor
    (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsMintRow env)
    (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ) (post : CellState)
    (henc : RowEncodes env (cellProjA s.kernel cell a) amt post)
    (hgatesat : satisfiedVm hash mintVmDescriptor env true false)
    (hsat : satisfiedVm hash mintVmDescriptor env true true)
    (hexec : recCMintAsset s actor cell a amt = some s') :
    post.balLo ≡ (cellProjA s'.kernel cell a).balLo [ZMOD 2013265921]
    ∧ post.balHi ≡ (cellProjA s'.kernel cell a).balHi [ZMOD 2013265921]
    ∧ (∀ i, post.fields i ≡ (cellProjA s'.kernel cell a).fields i [ZMOD 2013265921])
    ∧ post.capRoot ≡ (cellProjA s'.kernel cell a).capRoot [ZMOD 2013265921]
    ∧ post.reserved ≡ (cellProjA s'.kernel cell a).reserved [ZMOD 2013265921] := by
  obtain ⟨hcirc, _⟩ :=
    mintDescriptor_full_sound hash env hrow (cellProjA s.kernel cell a) post amt henc hgatesat hsat
  obtain ⟨hcLo, hcHi, _hcN, hcF, hcCap, hcRes⟩ := hcirc
  obtain ⟨heLo, heHi, _heN, heF, heCap, heRes⟩ := unify_mint_exec s s' actor cell a amt hexec
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hcLo.trans heLo.symm
  · exact hcHi.trans heHi.symm
  · intro i; exact (hcF i).trans (heF i).symm
  · exact hcCap.trans heCap.symm
  · exact hcRes.trans heRes.symm

/-! ## §8 — NON-VACUITY. -/

/-- A concrete BridgeMint row: selector `sel::BRIDGE_MINT = 40`, `bal_lo 100 → 130`, `value_lo = 30`
at `param1`, frame fixed, nonce 5 → 6 (TICK). -/
def goodMintRow : VmRowEnv where
  loc := fun v =>
    if v = selM.MINT then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 130
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 6
    else if v = prmCol VALUE_LO then 30
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- `goodMintRow` is a genuine BridgeMint row (`s_bridge_mint = 1`, `s_noop = 0`). -/
theorem goodMintRow_isMintRow : IsMintRow goodMintRow := by
  unfold IsMintRow goodMintRow
  refine ⟨by norm_num [selM.MINT], ?_⟩
  -- s_noop = 0: col 0 (NOOP) is not the selector (40), nor any of the named columns.
  norm_num [sel.NOOP, selM.MINT, sbCol, saCol, prmCol, STATE_BEFORE_BASE, STATE_AFTER_BASE,
    PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE, VALUE_LO]

/-- **NON-VACUITY (witness TRUE).** `goodMintRow` REALIZES the mint intent: `bal_lo 100 → 130 =
100 + 30` (`value_lo` at `param1`), nonce ticks `5 → 6`, frame frozen. -/
theorem goodMintRow_realizes_intent : MintRowIntent goodMintRow := by
  unfold MintRowIntent
  refine ⟨eq_lift ?_, eq_lift ?_, eq_lift ?_, eq_lift ?_, eq_lift ?_, ?_⟩
  · norm_num [goodMintRow, sbCol, saCol, prmCol, selM.MINT, STATE_BEFORE_BASE, STATE_AFTER_BASE,
      PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE, VALUE_LO]
  · norm_num [goodMintRow, sbCol, saCol, prmCol, selM.MINT, STATE_BEFORE_BASE, STATE_AFTER_BASE,
      PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI,
      state.NONCE, VALUE_LO]
  · norm_num [goodMintRow, sbCol, saCol, prmCol, selM.MINT, STATE_BEFORE_BASE, STATE_AFTER_BASE,
      PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE, VALUE_LO]
  · norm_num [goodMintRow, sbCol, saCol, prmCol, selM.MINT, STATE_BEFORE_BASE, STATE_AFTER_BASE,
      PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE,
      state.CAP_ROOT, VALUE_LO]
  · norm_num [goodMintRow, sbCol, saCol, prmCol, selM.MINT, STATE_BEFORE_BASE, STATE_AFTER_BASE,
      PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE,
      state.RESERVED, VALUE_LO]
  · intro i hi
    refine eq_lift ?_
    simp only [goodMintRow, sbCol, saCol, prmCol, selM.MINT, STATE_BEFORE_BASE, STATE_AFTER_BASE,
      PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI,
      state.NONCE, state.CAP_ROOT, state.RESERVED, state.FIELD_BASE, VALUE_LO]
    have e1 : (76 + (3 + i) = 40) = False := by simp; omega
    have e2 : (76 + (3 + i) = 54) = False := by simp; omega
    have e3 : (76 + (3 + i) = 76) = False := by simp
    have e4 : (76 + (3 + i) = 56) = False := by simp; omega
    have e5 : (76 + (3 + i) = 78) = False := by simp; omega
    have e6 : (76 + (3 + i) = 69) = False := by simp; omega
    have f1 : (54 + (3 + i) = 40) = False := by simp; omega
    have f2 : (54 + (3 + i) = 54) = False := by simp
    have f3 : (54 + (3 + i) = 76) = False := by simp; omega
    have f4 : (54 + (3 + i) = 56) = False := by simp; omega
    have f5 : (54 + (3 + i) = 78) = False := by simp; omega
    have f6 : (54 + (3 + i) = 69) = False := by simp; omega
    simp only [e1, e2, e3, e4, e5, e6, f1, f2, f3, f4, f5, f6, if_false]

/-- A FORGED mint row: `goodMintRow` with post-`bal_lo` tampered to `999 ≠ 130`. -/
def badMintRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodMintRow.loc v
  nxt := goodMintRow.nxt
  pub := goodMintRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badMintRow`'s post-`bal_lo` is NOT the
credit, so `gBalLoCredit` REJECTS it. -/
theorem badMintRow_rejected : ¬ (VmConstraint.gate gBalLoCredit).holdsVm badMintRow false false := by
  apply mintVm_rejects_wrong_balance <;>
    norm_num [badMintRow, goodMintRow, sbCol, saCol, prmCol, selM.MINT, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE, VALUE_LO]

/-! ## §8½ — THE CLASS-A CAPSTONE (per-cell, the transfer bar exactly).

mint's whole per-cell transition is the `bal_lo` CREDIT + the frozen frame — every state-block column
moved-or-frozen, ALL 13 absorbed into `state_commit` (anti-ghosted via the transfer keystone), and
unified to the verified executor (`recCMintAsset`). This capstone bundles the three corners into ONE
class-A statement (full per-cell post-state from the descriptor + anti-ghost on all of it + executor
agreement), exactly the shape `transferDescriptor_full_sound` + `…_commit_binds_state` +
`unify_*_exec` give for transfer.

The ONE residual — the *global supply total* — is NOT a per-cell state-block column; it is a
CROSS-CELL / TURN-LEVEL accumulator (mint by definition changes the total supply, which no single cell
carries). This is the EXACT analogue of transfer's two-sided conservation (sender-debit ⟺
receiver-credit), which the keystone's BOUNDARY assigns to the turn-composition layer, NOT the
per-row theorem. So mint meets the per-cell class-A bar transfer set; the supply-total invariant is a
turn property (cited, not papered), not a per-cell gap. -/

/-- **`mintDescriptor_classA` — the per-cell class-A capstone.** Satisfying the runnable descriptor under
`RowEncodes`, for the minted `(cell, asset)` entry of a committed `recCMintAsset`, forces: (a) the FULL
per-cell `CellMintSpec` (bal_lo credited by `amt`, nonce TICKED, the frame frozen); (b) the post-state
published as `PI[NEW_COMMIT]`; and (c) AGREEMENT with the executor's per-cell post-state on every
conserved/frame clause (the ONE nonce-tick divergence is `exec_nonce_is_frozen_not_ticked`, named).
The anti-ghost (`mintDescriptor_commit_binds_state`) covers all 13 absorbed columns. This is the
transfer/burn class-A bar, per cell. -/
theorem mintDescriptor_classA (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsMintRow env)
    (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ) (post : CellState)
    (henc : RowEncodes env (cellProjA s.kernel cell a) amt post)
    (hgatesat : satisfiedVm hash mintVmDescriptor env true false)
    (hsat : satisfiedVm hash mintVmDescriptor env true true)
    (hexec : recCMintAsset s actor cell a amt = some s') :
    CellMintSpec (cellProjA s.kernel cell a) amt post
    ∧ post.commit ≡ env.pub pi.NEW_COMMIT [ZMOD 2013265921]
    ∧ post.balLo ≡ (cellProjA s'.kernel cell a).balLo [ZMOD 2013265921]
    ∧ post.balHi ≡ (cellProjA s'.kernel cell a).balHi [ZMOD 2013265921]
    ∧ (∀ i, post.fields i ≡ (cellProjA s'.kernel cell a).fields i [ZMOD 2013265921])
    ∧ post.capRoot ≡ (cellProjA s'.kernel cell a).capRoot [ZMOD 2013265921]
    ∧ post.reserved ≡ (cellProjA s'.kernel cell a).reserved [ZMOD 2013265921] := by
  obtain ⟨hspec, hcommit⟩ :=
    mintDescriptor_full_sound hash env hrow (cellProjA s.kernel cell a) post amt henc hgatesat hsat
  obtain ⟨hLo, hHi, hF, hCap, hRes⟩ :=
    descriptor_agrees_with_executor hash env hrow s s' actor cell a amt post henc hgatesat hsat hexec
  exact ⟨hspec, hcommit, hLo, hHi, hF, hCap, hRes⟩

/-! ## §9 — Axiom-hygiene tripwires. -/

#assert_axioms mintDescriptor_classA

#guard mintVmDescriptor.constraints.length == 13 + 14 + 4 + 3
#guard mintVmDescriptor.hashSites.length == 4
#guard mintVmDescriptor.traceWidth == 188
-- The credit reads `param1` (the runtime value_lo), not `param0` (= `param.AMOUNT`, the MINT_HASH);
-- the selector is the runtime `sel::BRIDGE_MINT = 40`.
#guard VALUE_LO == 1
#guard VALUE_LO ≠ param.AMOUNT
#guard selM.MINT == 40

#assert_axioms mintVm_faithful
#assert_axioms mintVm_rejects_wrong_balance
#assert_axioms mintVm_rejects_wrong_nonce_delta
#assert_axioms intent_to_cellSpec
#assert_axioms mintRowGates_flag_indep
#assert_axioms mintDescriptor_full_sound
#assert_axioms mintDescriptor_commit_binds_state
#assert_axioms unify_mint
#assert_axioms unify_mint_well
#assert_axioms unify_mint_exec
#assert_axioms unify_mint_well_exec
#assert_axioms exec_nonce_is_frozen_not_ticked
#assert_axioms descriptor_agrees_with_executor
#assert_axioms goodMintRow_isMintRow
#assert_axioms goodMintRow_realizes_intent
#assert_axioms badMintRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitMint
