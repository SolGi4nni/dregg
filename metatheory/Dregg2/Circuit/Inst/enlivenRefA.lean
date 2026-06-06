/-
# Dregg2.Circuit.Inst.enlivenRefA — the v2 (`EffectCommit2`) instance for the CapTP sturdy-ref ENLIVEN
  `enlivenRefA` (the swiss-table ENLIVEN arm of `execFullA`).

`enlivenRefA sw actor exporter claimed` VALIDATES a presented swiss number, checks non-amplification of
the bearer's `claimed` rights against the entry's exported `rights`, and BUMPS the entry's `refcount`
via `replaceSwiss`. GATED on `EnlivenGuard` (AUTHORITY ∧ MEMBERSHIP ∧ NON-AMPLIFICATION).

Through the v2 framework (`EffectCommit2`):
  * touched component = `swiss` (`listComponent`, FULL-list digest);
  * the log GROWS by the authority receipt;
  * the guard is the 3-conjunct `EnlivenGuard`, committed as ONE `propBit` column;
  * the frame is the 16 non-`swiss` kernel fields (`RestIffNoSwiss`).

`enlivenRefA_full_sound` CONCLUDES the bespoke `Spec.SwissEnliven.EnlivenSpec` THROUGH the framework.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Circuit.Spec.swissenliven

namespace Dregg2.Circuit.Inst.EnlivenRefA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Spec.SwissEnliven
open Dregg2.Circuit.Spec.SwissFrame
open Dregg2.Authority (Auth)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system. -/

abbrev vBitGuard : Var := 0

def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `RestIffNoSwiss` portal. -/

def RestIffNoSwiss (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.escrows = k.escrows ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.queues = k.queues
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes)

/-! ## §2 — the `enlivenRefA` instance (touched component = `swiss`). -/

structure EnlivenArgs where
  sw       : Nat
  actor    : CellId
  exporter : CellId
  claimed  : List Auth

def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

def enlivenGuardProp (s : RecChainedState) (args : EnlivenArgs) : Prop :=
  EnlivenGuard s args.sw args.actor args.exporter args.claimed

instance (s : RecChainedState) (args : EnlivenArgs) : Decidable (enlivenGuardProp s args) := by
  unfold enlivenGuardProp EnlivenGuard
  exact inferInstanceAs (Decidable (_ ∧ ∃ _ : SwissRecord, _))

def enlivenGuardEncode (s : RecChainedState) (args : EnlivenArgs) (_s' : RecChainedState) : Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (enlivenGuardProp s args) else 0

def enlivenGuardGates : ConstraintSystem := [cBitGuard]

theorem enlivenGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied enlivenGuardGates a ↔ satisfied enlivenGuardGates b := by
  unfold satisfied enlivenGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

def enlivenSwissPostClause (s : RecChainedState) (args : EnlivenArgs) : List SwissRecord :=
  match enlivenSwissUpdate s.kernel.swiss args.sw args.claimed with
  | some ss => ss
  | none    => s.kernel.swiss

def swissComponent (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState EnlivenArgs :=
  listComponent (·.swiss) LE cN hN hLE enlivenSwissPostClause

def enlivenE (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    EffectSpec2 RecChainedState EnlivenArgs where
  view         := chainView
  active       := swissComponent LE cN hN hLE
  logUpdate    := some (fun s args => enlivenReceipt args.actor args.exporter :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.escrows = k.escrows ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.queues = k.queues
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes)
  guardGates   := enlivenGuardGates
  guardProp    := enlivenGuardProp
  guardWidth   := 1
  guardEncode  := enlivenGuardEncode
  guardLocal   := enlivenGuardLocal
  guardWidth_le := by decide

/-! ### §2a — per-effect obligations. -/

theorem enlivenGuardDecodes (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardDecodes2 (enlivenE LE cN hN hLE) := by
  intro s args s' hsat
  change satisfied enlivenGuardGates (enlivenGuardEncode s args s') at hsat
  show enlivenGuardProp s args
  have hg := hsat cBitGuard (by simp [enlivenGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, enlivenGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

theorem enlivenGuardEncodes (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardEncodes2 (enlivenE LE cN hN hLE) := by
  intro s args s' hg
  show satisfied enlivenGuardGates (enlivenGuardEncode s args s')
  intro c hc
  simp only [enlivenGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, enlivenGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

theorem enlivenRestFrameDecodes (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (hRest : RestIffNoSwiss S.RH) :
    RestFrameDecodes2 S (enlivenE LE cN hN hLE) := fun k k' h => (hRest k k').mp h

/-! ### §2b — apex ↔ `EnlivenSpec` bridge. -/

theorem apex_iff_enlivenSpec (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : EnlivenArgs) (s' : RecChainedState) :
    (enlivenE LE cN hN hLE).apex s args s'
      ↔ EnlivenSpec s args.sw args.actor args.exporter args.claimed s' := by
  show (enlivenGuardProp s args
        ∧ s'.kernel.swiss = enlivenSwissPostClause s args
        ∧ s'.log = enlivenReceipt args.actor args.exporter :: s.log
        ∧ ((enlivenE LE cN hN hLE).restFrame s.kernel s'.kernel))
       ↔ EnlivenSpec s args.sw args.actor args.exporter args.claimed s'
  unfold EnlivenSpec enlivenGuardProp enlivenSwissPostClause enlivenE
  constructor
  · rintro ⟨hg, hsw, hlog, hAcc, hCell, hCaps, hEsc, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    obtain ⟨e, hf, hr⟩ := hg.2
    have hk := (enlivenSwissUpdate_eq_k s.kernel args.sw args.claimed s'.kernel.swiss).mp <|
      by simpa [enlivenSwissPostClause, enlivenSwissUpdate_some] using hsw
    refine ⟨hg, s'.kernel, hk, ?_⟩
    cases s'; simp [hlog]
  · rintro ⟨hg, k', hk, hs'⟩
    rcases withSwiss_preserves_rest s.kernel k'.swiss with
      ⟨hAcc, hCell, hCaps, hEsc, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif, hDC, hDel, hDgs, hSB⟩
    obtain ⟨e, hf, hr⟩ := hg.2
    have hupd := enlivenSwissUpdate_some s.kernel.swiss args.sw args.claimed e hf hr
    have hk' := swissEnlivenK_eq_withSwiss hk
    have hsw := (enlivenSwissUpdate_eq_k s.kernel args.sw args.claimed k'.swiss).mpr hk'
    cases s'
    subst hs'
    simp [enlivenSwissPostClause, hsw, hupd]
    exact ⟨hg, rfl, rfl, ⟨hAcc, hCell, hCaps, hEsc, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩⟩

/-! ### §2c — THE VALIDATION. -/

theorem enlivenRefA_full_sound
    (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoSwiss S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : EnlivenArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (enlivenE LE cN hN hLE) (encodeE2 S (enlivenE LE cN hN hLE) s args s')) :
    EnlivenSpec s args.sw args.actor args.exporter args.claimed s' := by
  have hapex : (enlivenE LE cN hN hLE).apex s args s' :=
    effect2_circuit_full_sound S (enlivenE LE cN hN hLE)
      (enlivenRestFrameDecodes S LE cN hN hLE hRest) hLog (enlivenGuardDecodes LE cN hN hLE)
      s args s' h
  exact (apex_iff_enlivenSpec LE cN hN hLE s args s').mp hapex

/-! ## §3 — axiom-hygiene tripwires. -/

#assert_axioms enlivenGuardLocal
#assert_axioms enlivenGuardDecodes
#assert_axioms enlivenGuardEncodes
#assert_axioms apex_iff_enlivenSpec
#assert_axioms enlivenRefA_full_sound

end Dregg2.Circuit.Inst.EnlivenRefA