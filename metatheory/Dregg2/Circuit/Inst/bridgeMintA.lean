/-
# Dregg2.Circuit.Inst.bridgeMintA — the v2 (`EffectCommit2`) instance for the bridge-inbound-mint
effect `bridgeMintA` (touched component = `bal`, a `funcComponent`).

`bridgeMintA actor cell a value` is dregg1's two-phase cross-chain bridge, INBOUND leg: when the other
chain confirms a lock, this chain MINTS the asset into the recipient cell — a SINGLE-cell, single-asset
`bal` CREDIT, with the disclosed mint receipt prepended to the log and every other kernel field frozen.
It is "essentially `mintE` with a different guard/disclosed value": the touched component is the per-asset
ledger `bal` (a `funcComponent`, FULL-function digest = the realizable injective whole-value hash bar of
`cellLeafInjective`); the log GROWS by the inbound-mint receipt; the frame is the 16 non-`bal` kernel
fields (`RestIffNoBal` — the SAME omit-`bal` portal mint/burn/balanceA use).

This file is a THIN v2 instance (the worked `mintE` template in `EffectInstances2.lean`, retargeted to
the INDEPENDENT bespoke spec `Spec.BridgeInboundMint.InboundMintSpec`). The generic crown-jewel theorems
(`effect2_circuit_full_sound`, the anti-ghost teeth, emission) are proved ONCE in `EffectCommit2`; we
supply the per-effect `EffectSpec2`, the single-bit `GuardDecodes2`, and the apex↔bespoke bridge, then
COMPOSE to re-obtain the bespoke `InboundMintSpec` THROUGH the framework.

## What lands

  * `bridgeMintE`               — the `EffectSpec2 RecChainedState BridgeMintArgs` (touched = `bal`).
  * `bridgeMintGuardDecodes`    — the single `propBit` gate decodes to `inboundMintAdmit`.
  * `bridgeMintGuardEncodes`    — the `←` (completeness).
  * `apex_iff_inboundMintSpec`  — the framework's derived `apex` IS EXACTLY `InboundMintSpec`.
  * `bridgeMintA_full_sound`    — THE DELIVERABLE: a satisfying v2 full-state witness proves the complete
    declarative `InboundMintSpec` THROUGH `effect2_circuit_full_sound`. All 17 kernel components + log
    pinned; a tampered field is rejected by the framework's anti-ghost teeth.

Portals (carried Prop hypotheses, NEVER `axiom`): `RestIffNoBal RH` (the `bal`-omitting rest frame),
`logHashInjective LH` (the growing log), `Function.Injective D` (the `bal` component's whole-function
digest — the realizable Poseidon-CR bar). NO `AccountsWF` (the touched thing is not the cell map), NO
`postRoot = …` ghost.

ADDITIVE: imports `EffectInstances2` (for the validated v2 glue + `chainView`/`balComponent`/the bit
guard) and the bespoke spec; edits neither, nor any framework/`StateCommit`/`Dregg2.lean`.
-/
import Dregg2.Circuit.EffectInstances2
import Dregg2.Circuit.Spec.bridgeinboundmint

namespace Dregg2.Circuit.Inst.BridgeMintA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.EffectInstances2
open Dregg2.Circuit.Spec.BridgeInboundMint
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §1 — the `bridgeMintE` instance (touched component = `bal`).

`bridgeMintA` over `RecChainedState`: the touched component is the per-asset ledger `bal` (a
`funcComponent` whose digest is an injective whole-function hash — the realizable bar of
`cellLeafInjective`, REUSED verbatim from the validated `EffectInstances2.balComponent`); the log GROWS
by the inbound-mint receipt; the frame is the 16 non-`bal` kernel fields (`RestIffNoBal`). -/

/-- The bridge-inbound-mint effect arguments: actor, target cell, asset, disclosed mint amount. -/
structure BridgeMintArgs where
  actor : CellId
  cell  : CellId
  a     : AssetId
  value : ℤ

/-- The bridge-inbound-mint guard as a `Prop` (the spec's `inboundMintAdmit`): privileged supply
authority ∧ non-negativity ∧ destination-cell liveness. -/
def bridgeMintGuardProp (s : RecChainedState) (args : BridgeMintArgs) : Prop :=
  inboundMintAdmit s.kernel args.actor args.cell args.a args.value

instance (s : RecChainedState) (args : BridgeMintArgs) : Decidable (bridgeMintGuardProp s args) := by
  unfold bridgeMintGuardProp inboundMintAdmit; exact inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The guard's witness generator: lay the single `propBit` column at wire `0` (`vBitGuard`), reusing
the validated single-bit guard sub-system. -/
def bridgeMintGuardEncode (s : RecChainedState) (args : BridgeMintArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (bridgeMintGuardProp s args) else 0

/-- The guard sub-system: the single `propBit` gate (`cBitGuard`, reused from `EffectInstances2`). -/
def bridgeMintGuardGates : ConstraintSystem := [cBitGuard]

/-- **`bridgeMintGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem bridgeMintGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied bridgeMintGuardGates a ↔ satisfied bridgeMintGuardGates b := by
  unfold satisfied bridgeMintGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- **`bridgeMintE`** — the `EffectSpec2` for `bridgeMintA`, supplied to the v2 framework. The touched
component is `bal` via the validated `balComponent` (FULL-function credit `recBalCredit …`); the log
grows by the inbound-mint receipt `inboundMintReceipt`; the frame is the 16 non-`bal` clauses. -/
def bridgeMintE (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    EffectSpec2 RecChainedState BridgeMintArgs where
  view         := chainView
  active       := funcComponent (β := CellId → AssetId → ℤ) (·.bal) D hD
                    (fun s args => recTransferBal s.kernel.bal args.a args.cell args.a args.value)
  logUpdate    := some (fun s args => inboundMintReceipt args.actor args.cell args.a args.value :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt
      ∧ k'.heaps = k.heaps)
  guardGates   := bridgeMintGuardGates
  guardProp    := bridgeMintGuardProp
  guardWidth   := 1
  guardEncode  := bridgeMintGuardEncode
  guardLocal   := bridgeMintGuardLocal
  guardWidth_le := by decide

/-! ### §1a — the per-effect obligations for `bridgeMintE`. -/

/-- **`GuardDecodes2 (bridgeMintE …)`** — the single bit gate on the guard witness decodes to
`inboundMintAdmit`. -/
theorem bridgeMintGuardDecodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    GuardDecodes2 (bridgeMintE D hD) := by
  intro s args s' hsat
  change satisfied bridgeMintGuardGates (bridgeMintGuardEncode s args s') at hsat
  show bridgeMintGuardProp s args
  have hg := hsat cBitGuard (by simp [bridgeMintGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, bridgeMintGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes2 (bridgeMintE …)`** — `inboundMintAdmit` encodes to the satisfied bit gate. -/
theorem bridgeMintGuardEncodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    GuardEncodes2 (bridgeMintE D hD) := by
  intro s args s' hg
  show satisfied bridgeMintGuardGates (bridgeMintGuardEncode s args s')
  intro c hc
  simp only [bridgeMintGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, bridgeMintGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-- The `bridgeMintE` rest-frame portal (the `→`): `RestIffNoBal RH`'s soundness side (`bal` is the
touched field, so the omit-`bal` portal is the right one — REUSED, no new portal). -/
theorem bridgeMintRestFrameDecodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) :
    RestFrameDecodes2 S (bridgeMintE D hD) := fun k k' h => (hRest k k').mp h

/-! ### §1b — the apex ↔ `InboundMintSpec` bridge. -/

/-- **`apex_iff_inboundMintSpec`** — the framework's derived `apex` for `bridgeMintE` is EXACTLY
`InboundMintSpec`. The guard is `inboundMintAdmit`; the component `postClause` is the FULL `bal`-credit
equality `recBalCredit …`; the log is the inbound-mint receipt prepended to the chain; the `restFrame`
is the 16 non-`bal` frame clauses in `InboundMintSpec`'s order (which matches `bridgeMintE.restFrame`
exactly). -/
theorem apex_iff_inboundMintSpec (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : BridgeMintArgs) (s' : RecChainedState) :
    (bridgeMintE D hD).apex s args s'
      ↔ InboundMintSpec s args.actor args.cell args.a args.value s' := by
  -- unfold the apex's four conjuncts to the bare components.
  show (bridgeMintGuardProp s args
        ∧ s'.kernel.bal = recTransferBal s.kernel.bal args.a args.cell args.a args.value
        ∧ s'.log = inboundMintReceipt args.actor args.cell args.a args.value :: s.log
        ∧ ((bridgeMintE D hD).restFrame s.kernel s'.kernel))
       ↔ InboundMintSpec s args.actor args.cell args.a args.value s'
  unfold InboundMintSpec bridgeMintGuardProp bridgeMintE
  constructor
  · rintro ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §1c — THE DELIVERABLE: `bridgeMintA_full_sound ⇒ InboundMintSpec` through the framework. -/

/-- **`bridgeMintA_full_sound` — THE DELIVERABLE (bridge-inbound-mint through the v2 framework).** A
satisfying v2 full-state witness for `bridgeMintE` proves the complete declarative bespoke
`InboundMintSpec` — all 17 kernel components + the log are pinned (a tampered field is rejected by the
framework's anti-ghost teeth `effectCircuit2_rejects_{frame_tamper,wrong_component,log_forge}`). The
proof COMPOSES `effect2_circuit_full_sound` with the `apex_iff_inboundMintSpec` bridge. Portals:
`RestIffNoBal RH` (the `bal`-omitting rest frame), `logHashInjective LH` (the growing log),
`Function.Injective D` (the `bal` component's whole-function digest — the realizable Poseidon-CR bar). -/
theorem bridgeMintA_full_sound
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BridgeMintArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (bridgeMintE D hD) (encodeE2 S (bridgeMintE D hD) s args s')) :
    InboundMintSpec s args.actor args.cell args.a args.value s' := by
  have hapex : (bridgeMintE D hD).apex s args s' :=
    effect2_circuit_full_sound S (bridgeMintE D hD)
      (bridgeMintRestFrameDecodes S D hD hRest) hLog (bridgeMintGuardDecodes D hD) s args s' h
  exact (apex_iff_inboundMintSpec D hD s args s').mp hapex

/-! ## §2 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms bridgeMintGuardLocal
#assert_axioms bridgeMintGuardDecodes
#assert_axioms bridgeMintGuardEncodes
#assert_axioms apex_iff_inboundMintSpec
#assert_axioms bridgeMintA_full_sound

end Dregg2.Circuit.Inst.BridgeMintA
