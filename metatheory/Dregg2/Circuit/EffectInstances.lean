/-
# Dregg2.Circuit.EffectInstances — VALIDATING the generic `EffectCommit` framework.

`Dregg2.Circuit.EffectCommit` abstracts the full-state circuit⟺spec crown jewel ONCE: a satisfying
`satisfiedE` witness pins the WHOLE post-state via `effect_circuit_full_sound`, carrying only the
realizable Poseidon CR portals + `AccountsWF` + a per-effect `GuardDecodes`. `StateCommit` (Transfer)
and `SetFieldCommit` (setFieldA) each proved that crown jewel BESPOKE (~500 lines apiece).

THIS module is the VALIDATION: it re-derives BOTH known-good instances THROUGH the framework. It
produces an `EffectSpec` value for each, discharges the per-effect obligations (`GuardDecodes`,
`GuardEncodes`, the `apex ↔ BespokeSpec` bridge), and re-obtains the crown-jewel soundness
(`TransferSpec` / `SetFieldSpec`) by composing `effect_circuit_full_sound` with the apex bridge. If
this lands green + axiom-clean, the framework is instantiable and the per-effect recipe is the
TEMPLATE for the other ~29 effects.

ADDITIVE: this file does NOT edit `EffectCommit`/`StateCommit`/`SetFieldCommit`/`Transfer`/
`cellstatefield`/`Dregg2.lean`. It only IMPORTS them.

## What the instantiation exposed (the per-effect recipe, confirmed)

  1. an `EffectSpec Σ Args` value (≈ 8 fields);
  2. `GuardDecodes` — transported from the effect's existing per-gate `*_iff` lemmas (the guard gates,
     on the guard witness, decode to the guard predicate);
  3. `GuardEncodes` — the `←` (the guard predicate encodes to satisfied guard gates);
  4. `apex ↔ BespokeSpec` — a `funext` on `touchedCellMap` (the touched cells coincide with the
     bespoke post-cell helper off `T`) + an And-reassoc of the 16 frame clauses (DEFEQ for Transfer,
     a genuine reassoc for `setFieldA` whose `SetFieldSpec` lists the frame in a different order).

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Circuit.EffectCommit
import Dregg2.Circuit.Transfer
import Dregg2.Circuit.SetFieldCommit
import Dregg2.Circuit.Spec.cellstatefield

namespace Dregg2.Circuit.EffectInstances

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.Transfer (TransferSpec admitGuard)
open Dregg2.Circuit.SetFieldCommit
open Dregg2.Circuit.Spec.CellStateField (SetFieldSpec SetFieldGuard setFieldCellMap)
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.EffectsState (setField caveatsAdmit stateAuthB cellLive)

set_option linter.dupNamespace false

/-! ## §1 — the `transferE` instance.

`Transfer` over `RecordKernelState` with a FROZEN log (`getLog := fun _ => []`, `logUpdate := none`).
The touched set is `{src, dst}`, the expected leaf map is `recTransfer`, and the guard gates are the
SIX bit gates of `transferCircuit` (NOT debit/credit/conserve — those are the framework's `cETouched`
job, subsumed by the whole-`Value` touched-cell binding). -/

/-- The `StateView` for Transfer: read the kernel as-is, the (frozen) receipt log as empty. -/
def transferView : StateView RecordKernelState :=
  { toKernel := id, getLog := fun _ => [] }

/-- The six BIT gates of `transferCircuit` (authority / non-neg / availability / distinctness /
src-live / dst-live), reading wires `5..10 < 11`. The arithmetic debit/credit/conserve gates are NOT
guard gates here — the framework's `cETouched` binds the whole moved-cell `Value`s, which subsumes
the balance debit/credit. -/
def transferGuardGates : ConstraintSystem :=
  [Transfer.cTAuth, Transfer.cTNonneg, Transfer.cTAvail, Transfer.cTDistinct, Transfer.cTSrcLive,
    Transfer.cTDstLive]

/-- **`transferGuardLocal`** — every Transfer guard gate reads only wires `< 11`, so two assignments
agreeing on all wires `< 11` agree on the guard sub-system's satisfaction. The six gates are
`.var i = .const 1` for `i ∈ {5,…,10}`, each `< 11`. -/
theorem transferGuardLocal (a b : Assignment) (hab : ∀ w, w < 11 → a w = b w) :
    satisfied transferGuardGates a ↔ satisfied transferGuardGates b := by
  unfold satisfied transferGuardGates
  have h5 := hab 5 (by decide)
  have h6 := hab 6 (by decide)
  have h7 := hab 7 (by decide)
  have h8 := hab 8 (by decide)
  have h9 := hab 9 (by decide)
  have h10 := hab 10 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
        · simp only [Constraint.holds, Transfer.cTAuth, Transfer.cTNonneg, Transfer.cTAvail,
            Transfer.cTDistinct, Transfer.cTSrcLive, Transfer.cTDstLive, Transfer.vTAuth,
            Transfer.vTNonneg, Transfer.vTAvail, Transfer.vTDistinct, Transfer.vTSrcLive,
            Transfer.vTDstLive, Expr.eval, h5, h6, h7, h8, h9, h10] at hcc ⊢
          exact hcc

/-- **`transferE`** — the `EffectSpec` for Transfer, supplied to the generic framework. -/
def transferE : EffectSpec RecordKernelState Turn where
  view         := transferView
  touched      := fun _ t => {t.src, t.dst}
  expectedLeaf := fun k t => recTransfer k.cell t.src t.dst t.amt
  logUpdate    := none
  guardGates   := transferGuardGates
  guardProp    := fun k t => Transfer.admitGuard k t
  guardWidth   := 11
  guardEncode  := fun k t k' => Transfer.encodeT k t k'
  guardLocal   := transferGuardLocal
  guardWidth_le := by decide

/-! ### §1a — the per-effect guard obligations (transported from Transfer's `t*_iff` lemmas). -/

/-- **`GuardDecodes transferE`** — the six bit gates on `encodeT` decode to `admitGuard`. Each
conjunct is the `.mp` of the corresponding Transfer per-gate iff (`tauth_iff`/…). -/
theorem transferGuardDecodes : GuardDecodes transferE := by
  intro k t k' hsat
  -- reduce the `transferE` projections to their values, then extract each gate by membership.
  change satisfied transferGuardGates (Transfer.encodeT k t k') at hsat
  show admitGuard k t
  unfold satisfied transferGuardGates at hsat
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Transfer.tauth_iff k t k').mp     (hsat Transfer.cTAuth     (by simp))
  · exact (Transfer.tnonneg_iff k t k').mp   (hsat Transfer.cTNonneg   (by simp))
  · exact (Transfer.tavail_iff k t k').mp    (hsat Transfer.cTAvail    (by simp))
  · exact (Transfer.tdistinct_iff k t k').mp (hsat Transfer.cTDistinct (by simp))
  · exact (Transfer.tsrclive_iff k t k').mp  (hsat Transfer.cTSrcLive  (by simp))
  · exact (Transfer.tdstlive_iff k t k').mp  (hsat Transfer.cTDstLive  (by simp))

/-- **`GuardEncodes transferE`** — `admitGuard` encodes to the six satisfied bit gates (the `←` of
each per-gate iff), for the completeness direction. -/
theorem transferGuardEncodes : GuardEncodes transferE := by
  rintro k t k' ⟨hauth, hnn, hav, hne, hsl, hdl⟩
  show satisfied transferGuardGates (Transfer.encodeT k t k')
  intro c hc
  simp only [transferGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (Transfer.tauth_iff k t k').mpr hauth
  · exact (Transfer.tnonneg_iff k t k').mpr hnn
  · exact (Transfer.tavail_iff k t k').mpr hav
  · exact (Transfer.tdistinct_iff k t k').mpr hne
  · exact (Transfer.tsrclive_iff k t k').mpr hsl
  · exact (Transfer.tdstlive_iff k t k').mpr hdl

/-! ### §1b — the apex ↔ `TransferSpec` bridge. -/

/-- The framework's `touchedCellMap` over `{src,dst}` with `recTransfer` IS `recTransfer` itself:
off `{src,dst}`, `recTransfer` is the identity (its `else` branch), so the `if c ∈ {src,dst}` guard
is redundant. The funext that makes the apex's post-cell clause equal `TransferSpec`'s. -/
theorem transfer_touchedCellMap_eq (k : RecordKernelState) (t : Turn) :
    touchedCellMap k.cell {t.src, t.dst} (recTransfer k.cell t.src t.dst t.amt)
      = recTransfer k.cell t.src t.dst t.amt := by
  funext c
  unfold touchedCellMap
  by_cases hc : c ∈ ({t.src, t.dst} : Finset CellId)
  · rw [if_pos hc]
  · rw [if_neg hc]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    obtain ⟨hcs, hcd⟩ := hc
    simp only [recTransfer, if_neg hcs, if_neg hcd]

/-- **`apex_iff_transferSpec`** — the framework's derived `apex` for `transferE` is EXACTLY
`TransferSpec`. The guard conjunct coincides (`admitGuard`); the post-cell clause is the
`touchedCellMap` collapsed to `recTransfer`; the log clause is `[] = []` (trivial, frozen); the
16-field `kernelFrame` is `TransferSpec`'s 16 frame clauses in the SAME order (defeq under `id`). -/
theorem apex_iff_transferSpec (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    transferE.apex k t k' ↔ TransferSpec k t k' := by
  -- `transferE`'s view/touched/expectedLeaf/logUpdate reduce definitionally; the apex's post-cell
  -- clause's `touchedCellMap` collapses to `recTransfer` (transfer_touchedCellMap_eq); the apex's
  -- log clause is `[] = []` (frozen). Unfold both sides to the bare conjunctions.
  show (admitGuard k t
        ∧ k'.cell = touchedCellMap k.cell {t.src, t.dst} (recTransfer k.cell t.src t.dst t.amt)
        ∧ ([] : List Turn) = [] ∧ kernelFrame k k') ↔ TransferSpec k t k'
  rw [transfer_touchedCellMap_eq]
  unfold TransferSpec kernelFrame
  constructor
  · rintro ⟨hg, hcell, _hlog, hframe⟩
    exact ⟨hg, hcell, hframe⟩
  · rintro ⟨hg, hcell, hframe⟩
    exact ⟨hg, hcell, rfl, hframe⟩

/-! ### §1c — THE VALIDATION: `transferE_full_sound` through the framework.

Compose the GENERIC `effect_circuit_full_sound` (specialized to `transferE`) with the apex bridge.
The conclusion is `TransferSpec k t k'` — re-derived END-TO-END through the abstract framework, NOT
the bespoke `StateCommit.transfer_circuit_full_sound`. The portal set MIRRORS StateCommit's
soundness: `compressNInjective compressN`, `cellLeafInjective CH`, `RestHashIffFrame RH`,
`logHashInjective LH` (the frozen-log effect's log gate is the trivial `LH [] = LH []`, so the log
CR portal is consumed but vacuously discharged), + `AccountsWF` on both states.

NB the framework drops StateCommit's `compressInjective compress` portal: the 2-to-1 `movedDigest`
node hash is replaced by the SPONGE `touchedDigest` over `T` (bound by `compressNInjective` alone). -/

/-- **`transferE_full_sound` — the VALIDATION (Transfer through the framework).** A satisfying
generic full-state witness for `transferE` proves the complete declarative `TransferSpec`. -/
theorem transferE_full_sound
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (k : RecordKernelState) (t : Turn) (k' : RecordKernelState)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (h : satisfiedE S transferE (encodeE S transferE k t k')) :
    TransferSpec k t k' := by
  have hapex : transferE.apex k t k' :=
    effect_circuit_full_sound S transferE hN hL hRest hLog transferGuardDecodes k t k'
      hwf hwf' h
  exact (apex_iff_transferSpec k t k').mp hapex

#assert_axioms transferGuardLocal
#assert_axioms transferGuardDecodes
#assert_axioms transferGuardEncodes
#assert_axioms apex_iff_transferSpec
#assert_axioms transferE_full_sound

/-! ## §2 — the `setFieldE` instance.

`setFieldA` over `RecChainedState` with a GROWING log (`getLog := (·.log)`, `logUpdate := some …`).
The touched set is the SINGLE target cell `{cell}`, the expected leaf map is `setFieldCellMap`, and
the guard gates are the FOUR bit gates of `setFieldCircuit` (caveat / authority / membership /
liveness), reading wires `0..3 < 4`. The receipt row appended is `⟨actor, cell, cell, 0⟩`.

The differences from `transferE` the framework absorbed cleanly: (1) `logUpdate := some` (the log
GROWS, exercising the `cELog` gate non-trivially — Transfer's frozen log made it `LH [] = LH []`);
(2) `|T| = 1` (the touched sponge over a singleton — `FrameDigestBindsCells` is generic in `|T|`);
(3) the `apex ↔ SetFieldSpec` bridge needs a genuine And-REASSOC (SetFieldSpec lists `bal` 4 slots
later than `kernelFrame` does), not the defeq that sufficed for Transfer. -/

/-- The effect arguments of a `setFieldA`: the acting principal, the target cell, the written slot,
and the written value. (The framework's `Args` for this effect.) -/
structure SetFieldArgs where
  actor : CellId
  cell  : CellId
  f     : FieldName
  v     : Int

/-- The `StateView` for `setFieldA`: read the chained state's kernel and its receipt log. -/
def setFieldView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The four BIT gates of `setFieldCircuit` (caveat / authority / membership / liveness), reading
wires `0..3 < 4`. The four frame-forcing EQ gates (`cSFRest`/`cSFFrame`/`cSFTarget`/`cSFLog`) are the
framework's `cERest`/`cEFrame`/`cETouched`/`cELog` job, NOT guard gates. -/
def setFieldGuardGates : ConstraintSystem :=
  [cSFCaveat, cSFAuth, cSFMem, cSFLive]

/-- A FIXED trivial commitment surface used only to lay out the four guard bits (wires `0..3`). The
guard bit columns of `encodeSF` are pure `propBit (…)` of the guard predicates — INDEPENDENT of the
surface primitives — so any fixed surface yields the same guard wires, and the existing `sf*_iff`
lemmas (universally quantified over the surface) apply at this one. -/
def sfTrivCH : CellId → Value → ℤ := fun _ _ => 0
def sfTrivRH : RecordKernelState → ℤ := fun _ => 0
def sfTrivCmb : ℤ → ℤ → ℤ := fun _ _ => 0
def sfTrivCompressN : List ℤ → ℤ := fun _ => 0
def sfTrivLH : List Turn → ℤ := fun _ => 0

/-- The guard-bit witness generator: `encodeSF` at the trivial surface lays out the four guard bits
(and zeroes the surface-dependent digest columns, which the framework never reads on guard wires). -/
def setFieldGuardEncode (s : RecChainedState) (a : SetFieldArgs) (_s' : RecChainedState) :
    Assignment :=
  encodeSF sfTrivCH sfTrivRH sfTrivCmb sfTrivCompressN sfTrivLH s a.actor a.cell a.f a.v _s'

/-- **`setFieldGuardLocal`** — every `setFieldA` guard gate reads only wires `< 4` (the bit columns
`0..3`), so two assignments agreeing on all wires `< 4` agree on the guard sub-system's satisfaction.
The four gates are `.var i = .const 1` for `i ∈ {0,1,2,3}`, each `< 4`. -/
theorem setFieldGuardLocal (a b : Assignment) (hab : ∀ w, w < 4 → a w = b w) :
    satisfied setFieldGuardGates a ↔ satisfied setFieldGuardGates b := by
  unfold satisfied setFieldGuardGates
  have h0 := hab 0 (by decide)
  have h1 := hab 1 (by decide)
  have h2 := hab 2 (by decide)
  have h3 := hab 3 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;>
        · simp only [Constraint.holds, cSFCaveat, cSFAuth, cSFMem, cSFLive, vSFCaveat, vSFAuth,
            vSFMem, vSFLive, Expr.eval, h0, h1, h2, h3] at hcc ⊢
          exact hcc

/-- **`setFieldE`** — the `EffectSpec` for `setFieldA`, supplied to the generic framework. -/
def setFieldE : EffectSpec RecChainedState SetFieldArgs where
  view         := setFieldView
  touched      := fun _ a => {a.cell}
  expectedLeaf := fun s a => setFieldCellMap s.kernel.cell a.cell a.f a.v
  logUpdate    := some (fun s a =>
    { actor := a.actor, src := a.cell, dst := a.cell, amt := 0 } :: s.log)
  guardGates   := setFieldGuardGates
  guardProp    := fun s a => SetFieldGuard s a.actor a.cell a.f a.v
  guardWidth   := 4
  guardEncode  := setFieldGuardEncode
  guardLocal   := setFieldGuardLocal
  guardWidth_le := by decide

/-! ### §2a — the per-effect guard obligations (transported from SetFieldCommit's `sf*_iff` lemmas
instantiated at the trivial guard surface). -/

/-- **`GuardDecodes setFieldE`** — the four bit gates on the guard witness decode to `SetFieldGuard`.
Each conjunct is the `.mp` of the corresponding `sf*_iff` (at the trivial surface). -/
theorem setFieldGuardDecodes : GuardDecodes setFieldE := by
  rintro s a s' hsat
  -- reduce the `setFieldE` projections; `setFieldGuardEncode` IS `encodeSF` at the trivial surface.
  change satisfied setFieldGuardGates
    (encodeSF sfTrivCH sfTrivRH sfTrivCmb sfTrivCompressN sfTrivLH s a.actor a.cell a.f a.v s') at hsat
  show SetFieldGuard s a.actor a.cell a.f a.v
  unfold satisfied setFieldGuardGates at hsat
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (sfcaveat_iff sfTrivCH sfTrivRH sfTrivCmb sfTrivCompressN sfTrivLH s a.actor a.cell a.f a.v
      s').mp (hsat cSFCaveat (by simp))
  · exact (sfauth_iff sfTrivCH sfTrivRH sfTrivCmb sfTrivCompressN sfTrivLH s a.actor a.cell a.f a.v
      s').mp (hsat cSFAuth (by simp))
  · exact (sfmem_iff sfTrivCH sfTrivRH sfTrivCmb sfTrivCompressN sfTrivLH s a.actor a.cell a.f a.v
      s').mp (hsat cSFMem (by simp))
  · exact (sflive_iff sfTrivCH sfTrivRH sfTrivCmb sfTrivCompressN sfTrivLH s a.actor a.cell a.f a.v
      s').mp (hsat cSFLive (by simp))

/-- **`GuardEncodes setFieldE`** — `SetFieldGuard` encodes to the four satisfied bit gates (the `←` of
each `sf*_iff`), for the completeness direction. -/
theorem setFieldGuardEncodes : GuardEncodes setFieldE := by
  rintro s a s' ⟨hcav, hauth, hmem, hlive⟩
  show satisfied setFieldGuardGates
    (encodeSF sfTrivCH sfTrivRH sfTrivCmb sfTrivCompressN sfTrivLH s a.actor a.cell a.f a.v s')
  intro c hc
  simp only [setFieldGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact (sfcaveat_iff sfTrivCH sfTrivRH sfTrivCmb sfTrivCompressN sfTrivLH s a.actor a.cell a.f a.v
      s').mpr hcav
  · exact (sfauth_iff sfTrivCH sfTrivRH sfTrivCmb sfTrivCompressN sfTrivLH s a.actor a.cell a.f a.v
      s').mpr hauth
  · exact (sfmem_iff sfTrivCH sfTrivRH sfTrivCmb sfTrivCompressN sfTrivLH s a.actor a.cell a.f a.v
      s').mpr hmem
  · exact (sflive_iff sfTrivCH sfTrivRH sfTrivCmb sfTrivCompressN sfTrivLH s a.actor a.cell a.f a.v
      s').mpr hlive

/-! ### §2b — the apex ↔ `SetFieldSpec` bridge. -/

/-- The framework's `touchedCellMap` over `{cell}` with `setFieldCellMap` IS `setFieldCellMap`
itself: off `{cell}`, `setFieldCellMap` is the identity (its `else` branch), so the `if c ∈ {cell}`
guard is redundant. The funext that makes the apex's post-cell clause equal `SetFieldSpec`'s. -/
theorem setField_touchedCellMap_eq (base : CellId → Value) (cell : CellId) (f : FieldName) (v : Int) :
    touchedCellMap base {cell} (setFieldCellMap base cell f v) = setFieldCellMap base cell f v := by
  funext c
  unfold touchedCellMap
  by_cases hc : c ∈ ({cell} : Finset CellId)
  · rw [if_pos hc]
  · rw [if_neg hc]
    simp only [Finset.mem_singleton] at hc
    simp only [setFieldCellMap, if_neg hc]

/-- **`apex_iff_setFieldSpec`** — the framework's derived `apex` for `setFieldE` is EXACTLY
`SetFieldSpec`. The guard conjunct coincides (`SetFieldGuard`); the post-cell clause is the
`touchedCellMap` collapsed to `setFieldCellMap`; the log clause is the one-row chain extension; the
16-field `kernelFrame` REASSOCIATES to `SetFieldSpec`'s 16 frame clauses (whose `bal` sits four slots
later than `kernelFrame` lists it — hence a genuine reassoc, not a defeq). -/
theorem apex_iff_setFieldSpec (s : RecChainedState) (a : SetFieldArgs) (s' : RecChainedState) :
    setFieldE.apex s a s' ↔ SetFieldSpec s a.actor a.cell a.f a.v s' := by
  -- `setFieldE`'s view/touched/expectedLeaf/logUpdate reduce definitionally; the apex's post-cell
  -- clause's `touchedCellMap` collapses to `setFieldCellMap`.
  show (SetFieldGuard s a.actor a.cell a.f a.v
        ∧ s'.kernel.cell
            = touchedCellMap s.kernel.cell {a.cell} (setFieldCellMap s.kernel.cell a.cell a.f a.v)
        ∧ s'.log = { actor := a.actor, src := a.cell, dst := a.cell, amt := 0 } :: s.log
        ∧ kernelFrame s.kernel s'.kernel) ↔ SetFieldSpec s a.actor a.cell a.f a.v s'
  rw [setField_touchedCellMap_eq]
  unfold SetFieldSpec kernelFrame
  constructor
  · -- kernelFrame order: accounts caps bal escrows nullifiers revoked commitments queues swiss …
    rintro ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    -- SetFieldSpec order: accounts caps escrows nullifiers revoked commitments bal queues swiss …
    exact ⟨hg, hcell, hlog, hAcc, hCaps, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hcell, hlog, hAcc, hCaps, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §2c — THE VALIDATION: `setFieldE_full_sound` through the framework.

Compose the GENERIC `effect_circuit_full_sound` (specialized to `setFieldE`) with the apex bridge.
The conclusion is `SetFieldSpec s actor cell f v s'` — re-derived END-TO-END through the abstract
framework, NOT the bespoke `SetFieldCommit.setfield_circuit_full_sound`. The portal set is IDENTICAL
to `transferE_full_sound`'s (and to SetFieldCommit's): `compressNInjective`, `cellLeafInjective`,
`RestHashIffFrame`, `logHashInjective` — here the log CR portal does REAL work (the growing log
exercises `cELog` non-trivially) — + `AccountsWF` on both kernels. -/

/-- **`setFieldE_full_sound` — the VALIDATION (`setFieldA` through the framework).** A satisfying
generic full-state witness for `setFieldE` proves the complete declarative `SetFieldSpec`. -/
theorem setFieldE_full_sound
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (a : SetFieldArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S setFieldE (encodeE S setFieldE s a s')) :
    SetFieldSpec s a.actor a.cell a.f a.v s' := by
  have hapex : setFieldE.apex s a s' :=
    effect_circuit_full_sound S setFieldE hN hL hRest hLog setFieldGuardDecodes s a s'
      hwf hwf' h
  exact (apex_iff_setFieldSpec s a s').mp hapex

#assert_axioms setFieldGuardLocal
#assert_axioms setFieldGuardDecodes
#assert_axioms setFieldGuardEncodes
#assert_axioms apex_iff_setFieldSpec
#assert_axioms setFieldE_full_sound

end Dregg2.Circuit.EffectInstances
