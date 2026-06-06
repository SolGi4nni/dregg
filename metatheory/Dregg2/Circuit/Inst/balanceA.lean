/-
# Dregg2.Circuit.Inst.balanceA — the v2 `EffectCommit2` instance for the per-asset value-movement
effect `balanceA` (`bal-func`).

`balanceA` over `RecChainedState`: the action executor `execFullA` dispatches `.balanceA t a` to the
chained per-asset executor `recCexecAsset s t a`, which rewrites ONLY the `bal : CellId → AssetId → ℤ`
ledger's `a` column (debit `t.src`, credit `t.dst`, via `recTransferBal`) and prepends `t` to the
receipt log; every other RecordKernelState field is untouched. The touched component is therefore the
WHOLE `bal` function (a `funcComponent`, FULL-function digest — the realizable bar of
`cellLeafInjective`/`listLeafInjective`); the log GROWS by `t :: s.log`; the frame is the 16 non-`bal`
kernel fields (`RestIffNoBal`).

This is the v2 analog of the `mintE` template in `EffectInstances2` (mint also touches `bal` as a
`funcComponent` with a growing log). The ONLY effect-specific differences are: the args carry a `Turn`
plus an `AssetId`; the guard `Prop` is `admitGuardA` (the 6-conjunct admissibility predicate); and the
predicted `bal` is `recTransferBal` (the debit/credit movement) rather than `recBalCredit`.

The chain of soundness:

    satisfiedE2 ⟶ (effect2_circuit_full_sound) ⟶ apex ⟶ (apex_iff_balanceASpec) ⟶ BalanceMovementSpec

so a satisfying full-state witness for `balanceAE` proves the COMPLETE independent declarative spec
`BalanceMovementSpec` (the executor⟺spec corner is proved in `Spec.balancemovement`; this is the
circuit⟺spec corner, closing the triangle for value-movement THROUGH the v2 framework).

ADDITIVE: imports `EffectCommit2` + `Spec.balancemovement`; edits none of them.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.balancemovement

namespace Dregg2.Circuit.Inst.BalanceA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.Spec.BalanceMovement
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`mkBitGuard`, copied from `EffectInstances2`).

The `balanceA` spec exposes its guard as a `Prop` (`admitGuardA` — the 6-conjunct admissibility
predicate), not a per-gate circuit, so we commit it as ONE `propBit` column at wire `0`
(`guardWidth = 1`) and decode via `propBit = 1 ↔ p`. This is the `Prop`-level-guard pattern of the
`mintE`/`noteSpendE` templates. -/

/-- The guard wire (the single `propBit` column). -/
abbrev vBitGuard : Var := 0

/-- The single guard gate: `propBit (guardProp) = 1`. -/
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

/-- `propBit p = 1 ↔ p` (the decode lemma). -/
theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `balanceAE` instance (touched component = `bal`).

The args carry the `Turn` (which holds `src`/`dst`/`amt`) and the `AssetId` of the moved column. The
touched component is the per-asset ledger `bal` (a `funcComponent` over the WHOLE function); the log
GROWS by `t :: s.log`; the frame is the 16 non-`bal` kernel fields (`RestIffNoBal`). -/

/-- The balance-movement effect arguments: the `Turn` (src/dst/amt) and the moved asset column. -/
structure BalanceArgs where
  t : Turn
  a : AssetId

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The balance-movement guard as a `Prop` (the spec's `admitGuardA`). -/
def balanceGuardProp (s : RecChainedState) (args : BalanceArgs) : Prop :=
  admitGuardA s.kernel args.t args.a

instance (s : RecChainedState) (args : BalanceArgs) : Decidable (balanceGuardProp s args) := by
  unfold balanceGuardProp admitGuardA
  exact inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The balance-movement guard's witness generator: the single `propBit` column at wire `0`. -/
def balanceGuardEncode (s : RecChainedState) (args : BalanceArgs) (_s' : RecChainedState) : Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (balanceGuardProp s args) else 0

/-- The balance-movement guard sub-system: the single `propBit` gate. -/
def balanceGuardGates : ConstraintSystem := [cBitGuard]

/-- **`balanceGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem balanceGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied balanceGuardGates a ↔ satisfied balanceGuardGates b := by
  unfold satisfied balanceGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- The `bal` component digest: an injective whole-function hash `D` (carried `Function.Injective D` —
the realizable Poseidon-CR bar). The SPEC-predicted post `bal` is the per-asset debit/credit movement
`recTransferBal s.bal t.src t.dst a t.amt`. -/
def balComponent (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState BalanceArgs :=
  funcComponent (β := CellId → AssetId → ℤ) (·.bal) D hD
    (fun s args => recTransferBal s.kernel.bal args.t.src args.t.dst args.a args.t.amt)

/-- **`balanceAE`** — the `EffectSpec2` for `balanceA`, supplied to the v2 framework. -/
def balanceAE (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    EffectSpec2 RecChainedState BalanceArgs where
  view         := chainView
  active       := balComponent D hD
  logUpdate    := some (fun s args => args.t :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.escrows = k.escrows ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.queues = k.queues ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes)
  guardGates   := balanceGuardGates
  guardProp    := balanceGuardProp
  guardWidth   := 1
  guardEncode  := balanceGuardEncode
  guardLocal   := balanceGuardLocal
  guardWidth_le := by decide

/-! ### §1a — the per-effect obligations for `balanceAE`. -/

/-- **`GuardDecodes2 (balanceAE …)`** — the single bit gate on the guard witness decodes to
`admitGuardA`. -/
theorem balanceGuardDecodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    GuardDecodes2 (balanceAE D hD) := by
  intro s args s' hsat
  change satisfied balanceGuardGates (balanceGuardEncode s args s') at hsat
  show balanceGuardProp s args
  have hg := hsat cBitGuard (by simp [balanceGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, balanceGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes2 (balanceAE …)`** — `admitGuardA` encodes to the satisfied bit gate. -/
theorem balanceGuardEncodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    GuardEncodes2 (balanceAE D hD) := by
  intro s args s' hg
  show satisfied balanceGuardGates (balanceGuardEncode s args s')
  intro c hc
  simp only [balanceGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, balanceGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-- The `balanceAE` rest-frame portal (the `→`): `RestIffNoBal RH`'s soundness side. -/
theorem balanceRestFrameDecodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) :
    RestFrameDecodes2 S (balanceAE D hD) := fun k k' h => (hRest k k').mp h

/-! ### §1b — the apex ↔ `BalanceMovementSpec` bridge.

The framework's derived `apex` for `balanceAE` is EXACTLY `BalanceMovementSpec`. The guard is
`admitGuardA`; the component `postClause` is the FULL `bal = recTransferBal …` equality; the log is
`t :: s.log`; and the `restFrame` is the 16 non-`bal` frame clauses — and `BalanceMovementSpec`'s frame
is in the SAME field order (`accounts cell caps escrows nullifiers revoked commitments queues swiss
slotCaveats factories lifecycle deathCert delegate delegations sealedBoxes`), so the bridge is a
field-by-field pass-through. -/

/-- **`apex_iff_balanceASpec`** — the framework's derived `apex` for `balanceAE` is EXACTLY
`BalanceMovementSpec`. -/
theorem apex_iff_balanceASpec (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState) :
    (balanceAE D hD).apex s args s' ↔ BalanceMovementSpec s args.t args.a s' := by
  show (balanceGuardProp s args
        ∧ s'.kernel.bal = recTransferBal s.kernel.bal args.t.src args.t.dst args.a args.t.amt
        ∧ s'.log = args.t :: s.log
        ∧ ((balanceAE D hD).restFrame s.kernel s'.kernel))
       ↔ BalanceMovementSpec s args.t args.a s'
  unfold BalanceMovementSpec balanceGuardProp balanceAE
  constructor
  · rintro ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §1c — THE INSTANCE: `balanceA_full_sound ⇒ BalanceMovementSpec` through the framework. -/

/-- **`balanceA_full_sound` — the v2 instance (balanceA through the framework).** A satisfying v2
full-state witness for `balanceAE` proves the COMPLETE independent declarative `BalanceMovementSpec`
(all 17 kernel fields + log are pinned). Portals: `RestIffNoBal RH` (the `bal`-omitting rest frame),
`logHashInjective LH` (the growing log), `Function.Injective D` (the `bal` component's whole-function
digest — the realizable Poseidon-CR bar). This is the circuit⟺spec corner of the value-movement
triangle, closed through the v2 framework. -/
theorem balanceA_full_sound
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (balanceAE D hD) (encodeE2 S (balanceAE D hD) s args s')) :
    BalanceMovementSpec s args.t args.a s' := by
  have hapex : (balanceAE D hD).apex s args s' :=
    effect2_circuit_full_sound S (balanceAE D hD)
      (balanceRestFrameDecodes S D hD hRest) hLog (balanceGuardDecodes D hD) s args s' h
  exact (apex_iff_balanceASpec D hD s args s').mp hapex


/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def balanceAEWire : EffectSpec2 RecChainedState BalanceArgs where
  view         := chainView
  active      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := balanceGuardGates
  guardProp    := balanceGuardProp
  guardWidth   := 1
  guardEncode  := balanceGuardEncode
  guardLocal   := balanceGuardLocal
  guardWidth_le := by decide

def balanceAAirName : String := "dregg-balanceA-v2"

def balanceAEmitted : EmittedDescriptor := emittedEffect2 balanceAAirName balanceAEWire

#guard balanceAEmitted.name == balanceAAirName

/-! ## §2 — axiom-hygiene tripwires. -/

#assert_axioms balanceGuardLocal
#assert_axioms balanceGuardDecodes
#assert_axioms balanceGuardEncodes
#assert_axioms apex_iff_balanceASpec
#assert_axioms balanceA_full_sound

end Dregg2.Circuit.Inst.BalanceA
