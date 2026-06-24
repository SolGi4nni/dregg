/-
# Dregg2.Circuit.Inst.revokeDelegationFullA — the v2-DUAL (`EffectCommit2Dual`) instance for the FAITHFUL
  delegation-revoke `revokeDelegationA` (cap-edge `removeEdge` + the dregg1 epoch step).

`revokeDelegationA parent child` does the FULL `apply_revoke_delegation` (`recCRevokeDelegationFull`): the
shared cap-edge `removeEdge` (leg 1) COMPOSED with the freshness epoch step (legs 2+3 — bump the PARENT's
`delegationEpoch`, clear the CHILD's `delegations` snapshot + reset its `delegationEpochAt` stamp). The bare
`revokeDelegationE` (`Inst/revokeDelegationA.lean`) binds ONLY `caps` and FRAMES the three delegation
registries unchanged — so it concludes only the WEAK `RevokeSpec`, and the epoch step had to ride a CARRIED
`RevokeDelegationEpochResidual`. This instance CLOSES that: a SECOND forced component
(`delegationStepComponent`) binds the PRODUCT `(delegationEpoch, delegations, delegationEpochAt)` to its
epoch-stepped value via an injective whole-function digest (the SAME `funcComponent` bar `spawnE`'s
`delegationsComp` uses for the birth-stamp), reading the stepped maps off the SAME before-kernel. So the
deployed dual descriptor ALONE forces the STRENGTHENED `RevokeDelegationFullSpec`: the freshness step is
gate-forced, no residual. A forge that drops the cap edge but skips the epoch bump / snapshot clear FAILS
the product `postClause` and is UNSAT.

This mirrors `spawnE`/`refreshDelegationE`, whose `delegationEpochAt` stamps moved from a framed/residual
face into a forced PRODUCT component — the same mechanism, now applied to the revoke epoch step. VK-NOTE:
the descriptor gains a second committed component (the epoch-triple digest folds into the state-commit),
so the deployed VK for `revokeDelegationA` changes (no devnet — fine).

ADDITIVE: imports `EffectCommit2Dual` + the authority-revocation spec; edits NEITHER. Follows the
`cellDestroyA` dual template (`Inst/cellDestroyA.lean`).
-/
import Dregg2.Circuit.EffectCommit2Dual
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.authorityrevocation

namespace Dregg2.Circuit.Inst.RevokeDelegationFullA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.EffectCommit2Dual
open Dregg2.Circuit.Spec.AuthorityRevocation
open Dregg2.Authority (Caps Cap Auth)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard (`True` — revocation is unconditional, as in `revokeDelegationE`). -/

abbrev vBitGuard : Var := 0
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the rest portal: omit `caps` AND the three delegation registries (the touched fields).

`revokeDelegationFullA` touches `caps` (component 1) and `(delegationEpoch, delegations,
delegationEpochAt)` (component 2). The rest hash binds the THIRTEEN remaining kernel fields, BIDIRECTIONAL,
omitting all four touched. The 1-line mirror of `RestIffNoCaps`, additionally dropping the epoch triple. -/

/-- **`RestIffNoCapsEpoch RH`** — the rest hash binds the 13 non-touched components (BIDIRECTIONAL),
omitting `caps` and the three delegation registries (the touched fields of `revokeDelegationFullA`). -/
def RestIffNoCapsEpoch (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.cell = k.cell
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.bal = k.bal
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate
      ∧ k'.heaps = k.heaps)

/-! ## §2 — the `revokeDelegationFullE` instance (touched components = `caps` + the epoch triple). -/

structure RevokeArgs where
  holder : CellId
  t      : CellId

def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

def revokeGuardProp (_s : RecChainedState) (_args : RevokeArgs) : Prop :=
  True

instance (s : RecChainedState) (args : RevokeArgs) : Decidable (revokeGuardProp s args) := by
  unfold revokeGuardProp; exact inferInstanceAs (Decidable True)

def revokeGuardEncode (s : RecChainedState) (args : RevokeArgs) (_s' : RecChainedState) : Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (revokeGuardProp s args) else 0

def revokeGuardGates : ConstraintSystem := [cBitGuard]

theorem revokeGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied revokeGuardGates a ↔ satisfied revokeGuardGates b := by
  unfold satisfied revokeGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-! ### The stepped epoch maps (the values the spec asserts — read off the before-kernel). -/

/-- The parent's `delegationEpoch` bumped `+1` (leg 2). -/
def revokeEpochMap (k : RecordKernelState) (parent : CellId) : CellId → Nat :=
  fun c => if c = parent then k.delegationEpoch c + 1 else k.delegationEpoch c

/-- The child's `delegations` snapshot cleared to `[]` (leg 3a). -/
def revokeDelegationsMap (k : RecordKernelState) (child : CellId) : CellId → List Cap :=
  fun c => if c = child then [] else k.delegations c

/-- The child's `delegationEpochAt` stamp reset to `0` (leg 3b). -/
def revokeEpochAtMap (k : RecordKernelState) (child : CellId) : CellId → Nat :=
  fun c => if c = child then 0 else k.delegationEpochAt c

/-- The `caps` component digest — the declarative cap-graph `removeEdgeCaps … parent child` (leg 1,
identical to the bare `revokeDelegationE`). -/
def capsComponent (D : Caps → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState RevokeArgs :=
  funcComponent (β := Caps) (·.caps) D hD
    (fun s args => removeEdgeCaps s.kernel.caps args.holder args.t)

/-- **`delegationStepComponent`** — the FAITHFUL epoch-step component binding the THREE delegation
registries as ONE injective PRODUCT digest: the parent's bumped `delegationEpoch`, the child's cleared
`delegations` snapshot, AND the child's reset `delegationEpochAt` stamp. The expected value reads all three
stepped maps out of the SAME before-kernel (`revokeEpochMap`/`revokeDelegationsMap`/`revokeEpochAtMap`), so
the digest FORCES the epoch step on the committed post — a genuine force at the whole-kernel descriptor
layer (the SAME mechanism `spawnE`'s `delegationsComp` uses for the birth stamp), NOT a freely-witnessed
param. A revoke that drops the cap edge but leaves the epoch frozen / the snapshot un-cleared FAILS the
product clause. -/
def delegationStepComponent
    (D : (CellId → Nat) × (CellId → List Cap) × (CellId → Nat) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState RevokeArgs :=
  funcComponent (β := (CellId → Nat) × (CellId → List Cap) × (CellId → Nat))
    (fun k => (k.delegationEpoch, k.delegations, k.delegationEpochAt)) D hD
    (fun s args => (revokeEpochMap s.kernel args.holder,
                    revokeDelegationsMap s.kernel args.t,
                    revokeEpochAtMap s.kernel args.t))

/-- **`revokeDelegationFullE`** — the `EffectSpec2Dual` for `revokeDelegationA`: cap-edge `removeEdge`
(`active1`) + the forced epoch step (`active2`), supplied to the v2-dual framework. -/
def revokeDelegationFullE (D : Caps → ℤ) (hD : Function.Injective D)
    (DStep : (CellId → Nat) × (CellId → List Cap) × (CellId → Nat) → ℤ)
    (hDStep : Function.Injective DStep) :
    EffectSpec2Dual RecChainedState RevokeArgs where
  view         := chainView
  active1      := capsComponent D hD
  active2      := delegationStepComponent DStep hDStep
  logUpdate    := some (fun s args => authReceipt args.holder :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.bal = k.bal
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate
      ∧ k'.heaps = k.heaps)
  guardGates   := revokeGuardGates
  guardProp    := revokeGuardProp
  guardWidth   := 1
  guardEncode  := revokeGuardEncode
  guardLocal   := revokeGuardLocal
  guardWidth_le := by decide

/-! ### §2a — the per-effect obligations for `revokeDelegationFullE`. -/

theorem revokeGuardDecodes (D : Caps → ℤ) (hD : Function.Injective D)
    (DStep : (CellId → Nat) × (CellId → List Cap) × (CellId → Nat) → ℤ)
    (hDStep : Function.Injective DStep) :
    GuardDecodes2Dual (revokeDelegationFullE D hD DStep hDStep) := by
  intro s args s' hsat
  change satisfied revokeGuardGates (revokeGuardEncode s args s') at hsat
  show revokeGuardProp s args
  have hg := hsat cBitGuard (by simp [revokeGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, revokeGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

theorem revokeGuardEncodes (D : Caps → ℤ) (hD : Function.Injective D)
    (DStep : (CellId → Nat) × (CellId → List Cap) × (CellId → Nat) → ℤ)
    (hDStep : Function.Injective DStep) :
    GuardEncodes2Dual (revokeDelegationFullE D hD DStep hDStep) := by
  intro s args s' hg
  show satisfied revokeGuardGates (revokeGuardEncode s args s')
  intro c hc
  simp only [revokeGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, revokeGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

theorem revokeRestFrameDecodes (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (DStep : (CellId → Nat) × (CellId → List Cap) × (CellId → Nat) → ℤ)
    (hDStep : Function.Injective DStep)
    (hRest : RestIffNoCapsEpoch S.RH) :
    RestFrameDecodes2Dual S (revokeDelegationFullE D hD DStep hDStep) := fun k k' h => (hRest k k').mp h

/-! ### §2b — the apex ↔ STRENGTHENED `RevokeDelegationFullSpec` bridge.

The dual apex's five conjuncts (`guardProp = True`, the `caps` component, the epoch-triple PRODUCT
component, the log, the 13-field restFrame) repackage ONE-TO-ONE into `RevokeDelegationFullSpec`. The
PRODUCT clause `(post.delegationEpoch, post.delegations, post.delegationEpochAt) = (revokeEpochMap …,
revokeDelegationsMap …, revokeEpochAtMap …)` splits (via `Prod.ext_iff`) into the three epoch-step clauses
the spec asserts at its tail. -/

/-- **`apex_iff_revokeDelegationFullSpec`** — the dual apex for `revokeDelegationFullE` is EXACTLY
`RevokeDelegationFullSpec`: the cap-edge `removeEdge`, the forced epoch step (parent +1, child snapshot
cleared + stamp reset), the receipt-log advance, the 13-field frame. -/
theorem apex_iff_revokeDelegationFullSpec (D : Caps → ℤ) (hD : Function.Injective D)
    (DStep : (CellId → Nat) × (CellId → List Cap) × (CellId → Nat) → ℤ)
    (hDStep : Function.Injective DStep)
    (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState) :
    (revokeDelegationFullE D hD DStep hDStep).apex s args s' ↔
      RevokeDelegationFullSpec s args.holder args.t s' := by
  show (revokeGuardProp s args
        ∧ s'.kernel.caps = removeEdgeCaps s.kernel.caps args.holder args.t
        ∧ (s'.kernel.delegationEpoch, s'.kernel.delegations, s'.kernel.delegationEpochAt)
            = (revokeEpochMap s.kernel args.holder,
               revokeDelegationsMap s.kernel args.t,
               revokeEpochAtMap s.kernel args.t)
        ∧ s'.log = authReceipt args.holder :: s.log
        ∧ ((revokeDelegationFullE D hD DStep hDStep).restFrame s.kernel s'.kernel))
       ↔ RevokeDelegationFullSpec s args.holder args.t s'
  unfold RevokeDelegationFullSpec revokeGuardProp revokeDelegationFullE
    revokeEpochMap revokeDelegationsMap revokeEpochAtMap
  constructor
  · rintro ⟨hg, hcaps, hstep, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hSC, hFac, hLif,
      hDC, hDel, hHp⟩
    rw [Prod.ext_iff, Prod.ext_iff] at hstep
    obtain ⟨hde, hdels, hdea⟩ := hstep
    exact ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hSC, hFac, hLif,
      hDC, hDel, hHp, hde, hdels, hdea⟩
  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hSC, hFac, hLif,
      hDC, hDel, hHp, hde, hdels, hdea⟩
    refine ⟨hg, hcaps, ?_, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hSC, hFac, hLif,
      hDC, hDel, hHp⟩
    rw [Prod.ext_iff, Prod.ext_iff]
    exact ⟨hde, hdels, hdea⟩

/-! ### §2c — THE VALIDATION: `revokeDelegationFull_full_sound ⇒ RevokeDelegationFullSpec`. -/

/-- **`revokeDelegationFull_full_sound` — the VALIDATION (FAITHFUL delegation-revoke through the v2-dual
framework).** A satisfying v2-dual full-state witness for `revokeDelegationFullE` proves the STRENGTHENED
declarative `RevokeDelegationFullSpec`: the cap edge removed AND the freshness epoch step performed (parent
`+1`, child snapshot cleared, stamp reset). The epoch step is FORCED by the second component's injective
product digest — NO carried residual. Portals: `RestIffNoCapsEpoch RH` (the caps+epoch-omitting rest
frame), `logHashInjective LH` (the growing log), `Function.Injective D`/`DStep` (the two component digests,
the realizable Poseidon-CR bar). CONCLUDES `Spec.AuthorityRevocation.RevokeDelegationFullSpec` THROUGH the
generic `effect2dual_circuit_full_sound`. -/
theorem revokeDelegationFull_full_sound
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (DStep : (CellId → Nat) × (CellId → List Cap) × (CellId → Nat) → ℤ)
    (hDStep : Function.Injective DStep)
    (hRest : RestIffNoCapsEpoch S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState)
    (h : satisfiedE2Dual S (revokeDelegationFullE D hD DStep hDStep)
        (encodeE2Dual S (revokeDelegationFullE D hD DStep hDStep) s args s')) :
    RevokeDelegationFullSpec s args.holder args.t s' := by
  have hapex : (revokeDelegationFullE D hD DStep hDStep).apex s args s' :=
    effect2dual_circuit_full_sound S (revokeDelegationFullE D hD DStep hDStep)
      (revokeRestFrameDecodes S D hD DStep hDStep hRest) hLog
      (revokeGuardDecodes D hD DStep hDStep) s args s' h
  exact (apex_iff_revokeDelegationFullSpec D hD DStep hDStep s args s').mp hapex

/-- **TOOTH — `revokeDelegationFull_rejects_frozen_epoch`.** A claimed revoke post-state whose epoch
triple is NOT the genuine step (e.g. the parent epoch left FROZEN, or the child snapshot un-cleared — the
freshness-forgery that leaves a revoked child looking current) violates the product `postClause` and has
NO satisfying witness on the encoded dual triple: the descriptor REJECTS a forged-freshness revoke. -/
theorem revokeDelegationFull_rejects_frozen_epoch
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (DStep : (CellId → Nat) × (CellId → List Cap) × (CellId → Nat) → ℤ)
    (hDStep : Function.Injective DStep)
    (hRest : RestIffNoCapsEpoch S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState)
    (hfrozen : (s'.kernel.delegationEpoch, s'.kernel.delegations, s'.kernel.delegationEpochAt)
      ≠ (revokeEpochMap s.kernel args.holder,
         revokeDelegationsMap s.kernel args.t,
         revokeEpochAtMap s.kernel args.t)) :
    ¬ satisfiedE2Dual S (revokeDelegationFullE D hD DStep hDStep)
        (encodeE2Dual S (revokeDelegationFullE D hD DStep hDStep) s args s') := by
  intro h
  have hspec := revokeDelegationFull_full_sound S D hD DStep hDStep hRest hLog s args s' h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hde, hdels, hdea⟩ := hspec
  exact hfrozen (by rw [Prod.ext_iff, Prod.ext_iff]; exact ⟨hde, hdels, hdea⟩)

/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def revokeDelegationFullEWire : EffectSpec2Dual RecChainedState RevokeArgs where
  view         := chainView
  active1      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  active2      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := revokeGuardGates
  guardProp    := revokeGuardProp
  guardWidth   := 1
  guardEncode  := revokeGuardEncode
  guardLocal   := revokeGuardLocal
  guardWidth_le := by decide

def revokeDelegationFullAAirName : String := "dregg-revokeDelegationA-full-v2"

def revokeDelegationFullAEmitted : EmittedDescriptor :=
  emittedEffect2Dual revokeDelegationFullAAirName revokeDelegationFullEWire

#guard revokeDelegationFullAEmitted.name == revokeDelegationFullAAirName

/-! ## §3 — axiom-hygiene tripwires. -/

#assert_axioms revokeGuardLocal
#assert_axioms revokeGuardDecodes
#assert_axioms revokeGuardEncodes
#assert_axioms apex_iff_revokeDelegationFullSpec
#assert_axioms revokeDelegationFull_full_sound
#assert_axioms revokeDelegationFull_rejects_frozen_epoch

end Dregg2.Circuit.Inst.RevokeDelegationFullA
