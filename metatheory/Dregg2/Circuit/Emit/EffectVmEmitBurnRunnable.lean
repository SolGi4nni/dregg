/-
# Dregg2.Circuit.Emit.EffectVmEmitBurnRunnable — BURN lifted to FULL-STATE on the RUNNABLE descriptor.

`EffectVmEmitBurn` proved the per-cell soundness `burnDescriptor_full_sound` (a satisfying burn row forces
`CellBurnSpec` + publishes `NEW_COMMIT`) on the 186-wide `burnVmDescriptor`. But that descriptor's published
`state_commit` absorbs only the 13 state-block columns — NOT the `system_roots` sub-block, so it remains the
dominant Class-C projection (`EffectVmFullStateRunnable` header): a satisfying RUNNABLE proof pins a
projection, not the WHOLE 17-field post-state.

This module amplifies burn to full-state via the VALIDATED RECIPE (`EffectVmFullStateRunnable.lean` §6,
exactly as `transferRunnableSpec` is the worked reference):

  * **the wide descriptor** `burnVmDescriptorWide` — `burnVmDescriptor` with `traceWidth :=
    EFFECT_VM_WIDTH_SYSROOTS` and `hashSites := wideHashSites`. The per-row/transition/boundary gate list is
    BYTE-IDENTICAL (`burnWide_constraints_eq`); only the width grows by 2 and site 3's spare `.zero` 4th slot
    becomes the `sysRootsDigestCol` carrier.
  * **`burnGates_give_cellSpec`** — the GATE-ONLY per-cell soundness (no hash-site hypothesis): the per-row
    gates of `burnVmDescriptor`, on a burn row decoded by `RowEncodes`, force `CellBurnSpec`. This is
    `burnDescriptor_full_sound`'s per-cell body with the hash-site/boundary layer DROPPED — it factors through
    `burnVm_faithful` (`burnRowGates ⟺ BurnRowIntent`) + `intent_to_cellSpec`, NEITHER of which reads sites.
  * **`burnRunnableSpec`** — the `RunnableFullStateSpec CellState` instance. Burn touches NO side-table, so
    its `system_roots` sub-block is FROZEN: `fullClause = CellBurnSpec ∧ postRoots = preRoots`.
  * **`burn_runnable_full_sound`** — instantiating the GENERIC `runnable_full_sound`: a row satisfying
    `burnVmDescriptorWide` (the RUNNABLE wide descriptor), under the decode, pins the FULL 17-field post —
    the per-cell `CellBurnSpec` (balance debit + frame freeze incl. the runtime nonce tick) AND the 8
    side-table roots FROZEN. The crypto/anti-ghost on all 17 fields falls out of the generic teeth
    (instantiated at `burnRunnableSpec` in §4) — tamper ANY column or root ⇒ UNSAT.

## HONEST NOTES (recorded for the audit wave, per the task brief)

  * PRECONDITION GAP — as the per-cell `EffectVmEmitBurn` BOUNDARY already states, the burn `(cell,
    asset)` index + the AUTHORITY / non-negativity / availability / liveness GUARD (`BurnGuard`) of
    `recCBurnAsset` have NO row column: they are executor-side preconditions NOT in-circuit conjuncts of
    `burnVmDescriptor`. This module lifts the EXISTING gate set to full-state; it does NOT add those guards
    (the named, deferred systematic audit wave).

  * NONCE — `burnVmDescriptor` TICKS the runtime per-cell nonce (the running prover's global non-NoOp
    invariant); universe-A's burn freezes the LEDGER-entry nonce. `CellBurnSpec` (hence this `fullClause`)
    pins the runtime-tick — the genuine RUNNABLE row transition. The executor-image reconciliation is
    `EffectVmEmitBurn.exec_nonce_is_frozen_not_ticked` (the runtime-counter vs ledger-nonce gap, already
    named there, unchanged by this lift).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. The sole crypto carrier is the
NAMED `Poseidon2SpongeCR` portal, entering ONLY through the generic `runnable_full_sound` / the §4 anti-ghost.
No `sorry`, no `:= True`, no `native_decide`. Imports are read-only; this module owns only its declarations.
-/
import Dregg2.Circuit.Emit.EffectVmEmitBurn
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable

namespace Dregg2.Circuit.Emit.EffectVmEmitBurnRunnable

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState absorbedCols)
open Dregg2.Circuit.Emit.EffectVmEmitBurn
  (burnVmDescriptor burnRowGates burnRowGates_flag_indep burnVm_faithful intent_to_cellSpec
   CellBurnSpec RowEncodes BurnRowIntent IsBurnRow burnVmAirName
   goodBurnRow goodBurnRow_isBurnRow goodBurnRow_realizes_intent)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (wideHashSites RunnableFullStateSpec runnable_full_sound
   wide_rejects_state_tamper wide_rejects_root_tamper)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest emptySystemRoots N_SYSTEM_ROOTS)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — The WIDE burn descriptor (`system_roots`-absorbing). -/

/-- **`burnVmDescriptorWide`** — `burnVmDescriptor` WIDENED: the SAME per-row debit/freeze gates +
transitions + boundary PI pins, but `traceWidth := EFFECT_VM_WIDTH_SYSROOTS` and `hashSites :=
wideHashSites` (the `system_roots`-absorbing sites). Strictly additive over `burnVmDescriptor`: the
constraint list is byte-identical; only the width grows by 2 and site 3's spare `.zero` 4th slot becomes the
`sysRootsDigestCol` carrier (so the published `state_commit` now absorbs the — frozen — side-table digest).
`usesWideSites := rfl`. -/
def burnVmDescriptorWide : EffectVmDescriptor :=
  { burnVmDescriptor with
    name := burnVmAirName ++ "-sysroots"
    traceWidth := EFFECT_VM_WIDTH_SYSROOTS
    hashSites := wideHashSites }

/-- The wide burn descriptor's constraints ARE burn's (the width/site swap leaves the
per-row/transition/boundary gate list untouched). -/
theorem burnWide_constraints_eq :
    burnVmDescriptorWide.constraints = burnVmDescriptor.constraints := rfl

/-! ## §2 — The GATE-ONLY per-cell soundness (the THIN per-effect content of `decodeFull`). -/

/-- **`burnGates_give_cellSpec` — gate-only per-cell soundness (no hash-site hypothesis).** The per-row
gates of `burnVmDescriptor` (a constraint-list segment), on a burn row decoded by `RowEncodes`, force
`CellBurnSpec`. This is the body of `burnDescriptor_full_sound` with the hash-site/boundary layer DROPPED —
the per-cell debit/freeze/tick factors through `burnVm_faithful` (`burnRowGates ⟺ BurnRowIntent`) +
`intent_to_cellSpec`, NEITHER of which reads the sites. So the runnable per-cell soundness depends ONLY on
the gates (the sites bind the COMMITMENT — §1/§4 of the generic module — not the per-cell spec). The burn
row hypothesis `IsBurnRow` is carried (the global nonce-tick gate factors on `s_noop = 0`). -/
theorem burnGates_give_cellSpec (env : VmRowEnv) (pre post : CellState) (amt : ℤ)
    (hrow : IsBurnRow env) (henc : RowEncodes env pre amt post)
    (hgates : ∀ c ∈ burnVmDescriptor.constraints, c.holdsVm env true true) :
    CellBurnSpec pre amt post := by
  have hrowgates : ∀ c ∈ burnRowGates, c.holdsVm env true true := by
    intro c hc
    apply hgates
    unfold burnVmDescriptor
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
  have hrowgates' := burnRowGates_flag_indep env true true hrowgates
  exact intent_to_cellSpec env pre post amt henc ((burnVm_faithful env hrow).mp hrowgates')

/-! ## §3 — THE RUNNABLE FULL-STATE INSTANCE. -/

/-- **`BurnFullClause`** — the full declarative post-state for burn over `(pre, post, postRoots)`: the
per-cell `CellBurnSpec` (balance debited by `amt`, balHi/8-fields/cap/reserved frozen, runtime nonce ticked)
AND the `system_roots` sub-block FROZEN (burn touches no side-table). `amt` is the fixed burn amount;
`preRoots` is the frozen reference sub-block. Non-vacuous: §`goodBurn_realizes` inhabits it. -/
def BurnFullClause (amt : ℤ) (preRoots : SysRoots)
    (pre post : CellState) (postRoots : SysRoots) : Prop :=
  CellBurnSpec pre amt post ∧ postRoots = preRoots

/-- **`burnRunnableSpec` — the FULL-state RUNNABLE instance for burn.** `decodeAfter` is `RowEncodes` PLUS
the frozen-roots witness; `decodeFull` projects the wide descriptor's per-row gates (= burn's) to the
GATE-ONLY `burnGates_give_cellSpec`, then carries the frozen-roots fact. THIN — the only per-effect content
is the (proved here, hash-site-free) `burnGates_give_cellSpec` + the frozen-roots decode. NON-VACUOUS:
`fullClause` is the genuine per-cell debit + the frozen sub-block, NOT `True`. The `isRow := IsBurnRow`
hypothesis is exactly what `burnGates_give_cellSpec` consumes (the nonce-tick gate's `s_noop = 0` factor). -/
def burnRunnableSpec (amt : ℤ) (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := burnVmDescriptorWide
  usesWideSites := rfl
  isRow         := IsBurnRow
  decodeAfter   := fun env pre post postRoots =>
    RowEncodes env pre amt post ∧ postRoots = preRoots
  fullClause    := BurnFullClause amt preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots⟩ := hdec
    exact ⟨burnGates_give_cellSpec env pre post amt hrow henc (burnWide_constraints_eq ▸ hgates), hroots⟩

/-- **`burn_runnable_full_sound` — THE DELIVERABLE (full-state on the RUNNABLE descriptor).** A row
satisfying `burnVmDescriptorWide` — the WIDE descriptor the prover RUNS (`satisfiedVm`, first/last active) —
under the structured decode, pins the FULL 17-field declarative post-state: the per-cell `CellBurnSpec`
(balance debit, frame freeze, runtime nonce tick) AND the 8 side-table roots FROZEN (`postRoots = preRoots`).
The crypto is discharged ONCE in the generic `runnable_full_sound`; burn supplies only the THIN `decodeFull`.
Strictly stronger than `burnDescriptor_full_sound` (which binds only the 13-column projection): the wide
`state_commit` absorbs the `system_roots` digest, so a tamper of ANY of the 17 fields' content is UNSAT
(§4). -/
theorem burn_runnable_full_sound (amt : ℤ) (preRoots : SysRoots) (hash : List ℤ → ℤ)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsBurnRow env)
    (henc : RowEncodes env pre amt post)
    (hroots : postRoots = preRoots)
    (hsat : satisfiedVm hash burnVmDescriptorWide env true true) :
    CellBurnSpec pre amt post ∧ postRoots = preRoots :=
  runnable_full_sound (burnRunnableSpec amt preRoots) hash env pre post postRoots hrow
    ⟨henc, hroots⟩ hsat

#assert_axioms burn_runnable_full_sound

/-! ## §4 — ANTI-GHOST on all 17 fields (instantiating the generic teeth at `burnRunnableSpec`). -/

/-- **`burn_rejects_state_tamper` — per-cell-block anti-ghost.** Two wide burn rows publishing the same
`NEW_COMMIT` whose absorbed state-block columns DIFFER cannot both satisfy. -/
theorem burn_rejects_state_tamper (amt : ℤ) (preRoots : SysRoots)
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash burnVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash burnVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    (htamper : absorbedCols e₁ ≠ absorbedCols e₂) : False :=
  wide_rejects_state_tamper (burnRunnableSpec amt preRoots) hash hCR e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-- **`burn_rejects_root_tamper` — side-table anti-ghost (the gap's headline tooth, now on burn).** Two
wide burn rows publishing the same `NEW_COMMIT` (with `systemRootsDigest` carriers) whose side-table
sub-blocks DIFFER at some index `i` cannot both satisfy. The side-table state is bound BY the runnable burn
commitment — the Class-C disease cured for burn. -/
theorem burn_rejects_root_tamper (amt : ℤ) (preRoots : SysRoots)
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash burnVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash burnVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) : False :=
  wide_rejects_root_tamper (burnRunnableSpec amt preRoots) hash hCR e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

#assert_axioms burn_rejects_state_tamper
#assert_axioms burn_rejects_root_tamper

/-! ## §5 — NON-VACUITY: the full clause is inhabited by a real burn, and refutable.

`goodBurnRow` (from `EffectVmEmitBurn`) realizes the burn intent (`100 → 70` debit, nonce `5 → 6`). We
decode it to a concrete `(pre, post)` `CellState` pair and confirm the full clause's `CellBurnSpec` is
satisfied (witness TRUE), and refute a forged post-state (witness FALSE). -/

/-- The pre-state `goodBurnRow` encodes: bal_lo 100, nonce 5, everything else 0. -/
def goodBurnPre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

/-- The post-state `goodBurnRow` encodes: bal_lo 70 (debit by 30), nonce 6 (runtime tick), frame frozen. -/
def goodBurnPost : CellState :=
  { balLo := 70, balHi := 0, nonce := 6, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

/-- A frozen reference sub-block (the empty `system_roots`, since burn touches no side-table). -/
def goodBurnPreRoots : SysRoots := emptySystemRoots

/-- **`goodBurn_realizes` — NON-VACUITY (witness TRUE).** The burn `fullClause` is INHABITED by a real
burn: `goodBurnPost` is the genuine debit image of `goodBurnPre` (`100 → 70`, frame frozen, runtime nonce
ticked `5 → 6`) and the roots are frozen. So the framework's `fullClause` is NOT `True` for burn. -/
theorem goodBurn_realizes :
    (burnRunnableSpec 30 goodBurnPreRoots).fullClause goodBurnPre goodBurnPost goodBurnPreRoots :=
  ⟨⟨by norm_num [goodBurnPre, goodBurnPost], rfl, by norm_num [goodBurnPre, goodBurnPost],
     fun _ => rfl, rfl, rfl⟩, rfl⟩

/-- **`burnFullClause_not_trivial` — the clause is REFUTABLE (witness FALSE).** A post-state whose
`bal_lo` is NOT the debit (`goodBurnPre.balLo = 100`, demanding `70`, but a forged `999`) FAILS
`BurnFullClause` — so the clause is not vacuously true. -/
theorem burnFullClause_not_trivial :
    ¬ BurnFullClause 30 goodBurnPreRoots goodBurnPre
        { goodBurnPost with balLo := 999 } goodBurnPreRoots := by
  rintro ⟨⟨hbal, _⟩, _⟩
  simp only [goodBurnPre] at hbal
  norm_num at hbal

#assert_axioms goodBurn_realizes
#assert_axioms burnFullClause_not_trivial

/-! ## §6 — axiom-hygiene tripwires + structural pins. -/

#guard burnVmDescriptorWide.traceWidth == 188
#guard burnVmDescriptorWide.hashSites.length == 4
#guard burnVmDescriptorWide.constraints.length == burnVmDescriptor.constraints.length

#assert_axioms burnWide_constraints_eq
#assert_axioms burnGates_give_cellSpec

end Dregg2.Circuit.Emit.EffectVmEmitBurnRunnable
