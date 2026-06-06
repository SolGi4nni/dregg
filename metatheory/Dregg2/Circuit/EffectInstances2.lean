/-
# Dregg2.Circuit.EffectInstances2 — VALIDATING the v2 (`EffectCommit2`) framework.

`Dregg2.Circuit.EffectCommit2` abstracts the v2 full-state circuit⟺spec crown jewel for SINGLE-component
non-`cell` effects ONCE: a satisfying `satisfiedE2` witness pins the WHOLE post-state via
`effect2_circuit_full_sound`, carrying only the per-effect `RestIffNo*` portal + `logHashInjective` + a
per-effect `GuardDecodes2` (the touched component's `binds`/`encodes` are FIELDS of its
`ActiveComponent`, discharged by the smart constructor from the realizable Poseidon-CR set).

THIS module is the VALIDATION — the v2 analog of `EffectInstances` for v1. It builds TWO representatives
THROUGH the v2 framework and re-obtains their bespoke full-state soundness:

  * `mintE`       — touched component = `bal` (a `funcComponent`, FULL-function digest); FROZEN log is
    GROWN (mint prepends a receipt); bridge to `Spec.SupplyCreation.MintASpec`.
  * `noteSpendE`  — touched component = `nullifiers` (a `listComponent`, FULL-list digest); GROWING log;
    bridge to `Spec.NoteNullifier.NoteSpendSpec`.

If `mintE_full_sound ⇒ MintASpec` and `noteSpendE_full_sound ⇒ NoteSpendSpec` land green + axiom-clean,
the v2 framework is instantiable and the per-effect recipe is the TEMPLATE for the ~25 non-cell effects.

The guard sub-system here is a SINGLE BIT gate (`mkBitGuard`): the mint/noteSpend specs expose their
guard as a `Prop` (`mintAdmit`/`noteSpendGuard`), not a per-gate circuit, so we commit it as one
`propBit` column and decode via `propBit = 1 ↔ p`. (v1's `transferE`/`setFieldE` transported MANY
per-gate `*_iff` lemmas; v2's representatives have a `Prop`-level guard, so one bit suffices — the
swarm copies whichever matches its effect.)

ADDITIVE: imports `EffectCommit2` + the two specs; edits none of them.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Circuit.EffectCommit2

namespace Dregg2.Circuit.EffectInstances2

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Spec.SupplyCreation
open Dregg2.Circuit.Spec.NoteNullifier
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`mkBitGuard`).

A `Prop`-level guard committed as ONE `propBit` column at wire `0` (guardWidth = 1). The gate
`cBitGuard : .var 0 = .const 1` holds under the encoder IFF the guard predicate holds (`propBit = 1 ↔
p`). The swarm copies this for any effect whose spec exposes a `Prop` guard. -/

/-- The guard wire (the single `propBit` column). -/
abbrev vBitGuard : Var := 0

/-- The single guard gate: `propBit (guardProp) = 1`. -/
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

/-- `propBit p = 1 ↔ p` (the decode lemma). -/
theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `mintE` instance (touched component = `bal`).

`mintA` over `RecChainedState`: the touched component is the per-asset ledger `bal` (a `funcComponent`
whose digest is an injective whole-function hash — the realizable bar of `cellLeafInjective`); the log
GROWS by the mint receipt; the frame is the 16 non-`bal` kernel fields (`RestIffNoBal`). -/

/-- The mint effect arguments: actor, target cell, asset, amount. -/
structure MintArgs where
  actor : CellId
  cell  : CellId
  a     : AssetId
  amt   : ℤ

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The mint guard as a `Prop` (the spec's `mintAdmit`). -/
def mintGuardProp (s : RecChainedState) (args : MintArgs) : Prop :=
  mintAdmit s.kernel args.actor args.cell args.amt

instance (s : RecChainedState) (args : MintArgs) : Decidable (mintGuardProp s args) := by
  unfold mintGuardProp mintAdmit; exact inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The mint guard's witness generator: lay the single `propBit` column at wire `0`. -/
def mintGuardEncode (s : RecChainedState) (args : MintArgs) (_s' : RecChainedState) : Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (mintGuardProp s args) else 0

/-- The mint guard sub-system: the single `propBit` gate. -/
def mintGuardGates : ConstraintSystem := [cBitGuard]

/-- **`mintGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem mintGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied mintGuardGates a ↔ satisfied mintGuardGates b := by
  unfold satisfied mintGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- The `bal` component digest: an injective whole-function hash (carried `Function.Injective D`). -/
def balComponent (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState MintArgs :=
  funcComponent (β := CellId → AssetId → ℤ) (·.bal) D hD
    (fun s args => recBalCredit s.kernel.bal args.cell args.a args.amt)

/-- **`mintE`** — the `EffectSpec2` for `mintA`, supplied to the v2 framework. -/
def mintE (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    EffectSpec2 RecChainedState MintArgs where
  view         := chainView
  active       := balComponent D hD
  logUpdate    := some (fun s args => mintReceipt args.actor args.cell args.amt :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.escrows = k.escrows ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.queues = k.queues ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes)
  guardGates   := mintGuardGates
  guardProp    := mintGuardProp
  guardWidth   := 1
  guardEncode  := mintGuardEncode
  guardLocal   := mintGuardLocal
  guardWidth_le := by decide

/-! ### §1a — the per-effect obligations for `mintE`. -/

/-- **`GuardDecodes2 (mintE …)`** — the single bit gate on the guard witness decodes to `mintAdmit`. -/
theorem mintGuardDecodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    GuardDecodes2 (mintE D hD) := by
  intro s args s' hsat
  change satisfied mintGuardGates (mintGuardEncode s args s') at hsat
  show mintGuardProp s args
  have hg := hsat cBitGuard (by simp [mintGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, mintGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes2 (mintE …)`** — `mintAdmit` encodes to the satisfied bit gate. -/
theorem mintGuardEncodes (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    GuardEncodes2 (mintE D hD) := by
  intro s args s' hg
  show satisfied mintGuardGates (mintGuardEncode s args s')
  intro c hc
  simp only [mintGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, mintGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-- The `mintE` rest-frame portal (the `→`): `RestIffNoBal RH`'s soundness side. -/
theorem mintRestFrameDecodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) :
    RestFrameDecodes2 S (mintE D hD) := fun k k' h => (hRest k k').mp h

/-! ### §1b — the apex ↔ `MintASpec` bridge. -/

/-- **`apex_iff_mintASpec`** — the framework's derived `apex` for `mintE` is EXACTLY `MintASpec`. The
guard is `mintAdmit`; the component `postClause` is the FULL `bal`-credit equality; the log is the
receipt-prepended chain; the `restFrame` is the 16 non-`bal` frame clauses in `MintASpec`'s order. -/
theorem apex_iff_mintASpec (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : MintArgs) (s' : RecChainedState) :
    (mintE D hD).apex s args s' ↔ MintASpec s args.actor args.cell args.a args.amt s' := by
  -- unfold the apex's four conjuncts to the bare components.
  show (mintGuardProp s args
        ∧ s'.kernel.bal = recBalCredit s.kernel.bal args.cell args.a args.amt
        ∧ s'.log = mintReceipt args.actor args.cell args.amt :: s.log
        ∧ ((mintE D hD).restFrame s.kernel s'.kernel)) ↔ MintASpec s args.actor args.cell args.a args.amt s'
  unfold MintASpec mintGuardProp mintE
  constructor
  · rintro ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §1c — THE VALIDATION: `mintE_full_sound ⇒ MintASpec` through the framework. -/

/-- **`mintE_full_sound` — the VALIDATION (mint through the v2 framework).** A satisfying v2 full-state
witness for `mintE` proves the complete declarative `MintASpec`. Portals: `RestIffNoBal RH` (the
`bal`-omitting rest frame), `logHashInjective LH` (the growing log), `Function.Injective D` (the `bal`
component's whole-function digest — the realizable Poseidon-CR bar). -/
theorem mintE_full_sound
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : MintArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (mintE D hD) (encodeE2 S (mintE D hD) s args s')) :
    MintASpec s args.actor args.cell args.a args.amt s' := by
  have hapex : (mintE D hD).apex s args s' :=
    effect2_circuit_full_sound S (mintE D hD)
      (mintRestFrameDecodes S D hD hRest) hLog (mintGuardDecodes D hD) s args s' h
  exact (apex_iff_mintASpec D hD s args s').mp hapex

#assert_axioms mintGuardLocal
#assert_axioms mintGuardDecodes
#assert_axioms mintGuardEncodes
#assert_axioms apex_iff_mintASpec
#assert_axioms mintE_full_sound

/-! ## §2 — the `noteSpendE` instance (touched component = `nullifiers`).

`noteSpendA` over `RecChainedState`: the touched component is the `nullifiers` list side-table (a
`listComponent` whose digest is the `ListCommit.listDigest` sponge — its `binds` is `ListDigestBindsList`,
FULL-list equality, so a drop/reorder is rejected); the log GROWS by the note-spend receipt; the frame is
the 16 non-`nullifiers` kernel fields (`RestIffNoNullifiers`). -/

/-- The note-spend effect arguments: the nullifier and the acting principal. -/
structure NoteSpendArgs where
  nf    : Nat
  actor : CellId

/-- The note-spend guard as a `Prop` (the spec's `noteSpendGuard`). -/
def noteSpendGuardProp (s : RecChainedState) (args : NoteSpendArgs) : Prop :=
  noteSpendGuard s args.nf

instance (s : RecChainedState) (args : NoteSpendArgs) : Decidable (noteSpendGuardProp s args) := by
  unfold noteSpendGuardProp noteSpendGuard; exact inferInstanceAs (Decidable (¬ _))

/-- The note-spend guard's witness generator: the single `propBit` column at wire `0`. -/
def noteSpendGuardEncode (s : RecChainedState) (args : NoteSpendArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (noteSpendGuardProp s args) else 0

/-- The note-spend guard sub-system: the single `propBit` gate. -/
def noteSpendGuardGates : ConstraintSystem := [cBitGuard]

/-- **`noteSpendGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem noteSpendGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied noteSpendGuardGates a ↔ satisfied noteSpendGuardGates b := by
  unfold satisfied noteSpendGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- The `nullifiers` list component: digest = `listDigest LE cN` over the nullifier list. The carriers
(`compressNInjective cN` + `listLeafInjective LE`) are consumed in the `listComponent` smart ctor. -/
def nullComponent (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState NoteSpendArgs :=
  listComponent (·.nullifiers) LE cN hN hLE (fun s args => args.nf :: s.kernel.nullifiers)

/-- **`noteSpendE`** — the `EffectSpec2` for `noteSpendA`, supplied to the v2 framework. -/
def noteSpendE (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    EffectSpec2 RecChainedState NoteSpendArgs where
  view         := chainView
  active       := nullComponent LE cN hN hLE
  logUpdate    := some (fun s args => noteSpendReceipt args.actor :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.escrows = k.escrows ∧ k'.bal = k.bal ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.queues = k.queues ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes)
  guardGates   := noteSpendGuardGates
  guardProp    := noteSpendGuardProp
  guardWidth   := 1
  guardEncode  := noteSpendGuardEncode
  guardLocal   := noteSpendGuardLocal
  guardWidth_le := by decide

/-! ### §2a — the per-effect obligations for `noteSpendE`. -/

/-- **`GuardDecodes2 (noteSpendE …)`** — the single bit gate decodes to `noteSpendGuard`. -/
theorem noteSpendGuardDecodes (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardDecodes2 (noteSpendE LE cN hN hLE) := by
  intro s args s' hsat
  change satisfied noteSpendGuardGates (noteSpendGuardEncode s args s') at hsat
  show noteSpendGuardProp s args
  have hg := hsat cBitGuard (by simp [noteSpendGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, noteSpendGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes2 (noteSpendE …)`** — `noteSpendGuard` encodes to the satisfied bit gate. -/
theorem noteSpendGuardEncodes (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardEncodes2 (noteSpendE LE cN hN hLE) := by
  intro s args s' hg
  show satisfied noteSpendGuardGates (noteSpendGuardEncode s args s')
  intro c hc
  simp only [noteSpendGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, noteSpendGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-- The `noteSpendE` rest-frame portal (the `→`): `RestIffNoNullifiers RH`'s soundness side. -/
theorem noteSpendRestFrameDecodes (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (hRest : RestIffNoNullifiers S.RH) :
    RestFrameDecodes2 S (noteSpendE LE cN hN hLE) := fun k k' h => (hRest k k').mp h

/-! ### §2b — the apex ↔ `NoteSpendSpec` bridge. -/

/-- **`apex_iff_noteSpendSpec`** — the framework's derived `apex` for `noteSpendE` is EXACTLY
`NoteSpendSpec`. The guard is `noteSpendGuard`; the component `postClause` is the FULL nullifier-list
equality (`nf :: pre`); the log is the receipt-prepended chain; the `restFrame` is the 16
non-`nullifiers` frame clauses in `NoteSpendSpec`'s order. -/
theorem apex_iff_noteSpendSpec (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : NoteSpendArgs) (s' : RecChainedState) :
    (noteSpendE LE cN hN hLE).apex s args s' ↔ NoteSpendSpec s args.nf args.actor s' := by
  show (noteSpendGuardProp s args
        ∧ s'.kernel.nullifiers = args.nf :: s.kernel.nullifiers
        ∧ s'.log = noteSpendReceipt args.actor :: s.log
        ∧ ((noteSpendE LE cN hN hLE).restFrame s.kernel s'.kernel))
       ↔ NoteSpendSpec s args.nf args.actor s'
  unfold NoteSpendSpec noteSpendGuardProp noteSpendE
  constructor
  · rintro ⟨hg, hnull, hlog, hAcc, hCell, hCaps, hEsc, hBal, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    -- NoteSpendSpec order: accounts cell caps escrows revoked commitments bal queues swiss …
    exact ⟨hg, hnull, hlog, hAcc, hCell, hCaps, hEsc, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hnull, hlog, hAcc, hCell, hCaps, hEsc, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hnull, hlog, hAcc, hCell, hCaps, hEsc, hBal, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §2c — THE VALIDATION: `noteSpendE_full_sound ⇒ NoteSpendSpec` through the framework. -/

/-- **`noteSpendE_full_sound` — the VALIDATION (note-spend through the v2 framework).** A satisfying v2
full-state witness for `noteSpendE` proves the complete declarative `NoteSpendSpec`. Portals:
`RestIffNoNullifiers RH`, `logHashInjective LH`, `compressNInjective cN` + `listLeafInjective LE` (the
`nullifiers` list-component carriers — the realizable Poseidon-CR set). -/
theorem noteSpendE_full_sound
    (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoNullifiers S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : NoteSpendArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (noteSpendE LE cN hN hLE) (encodeE2 S (noteSpendE LE cN hN hLE) s args s')) :
    NoteSpendSpec s args.nf args.actor s' := by
  have hapex : (noteSpendE LE cN hN hLE).apex s args s' :=
    effect2_circuit_full_sound S (noteSpendE LE cN hN hLE)
      (noteSpendRestFrameDecodes S LE cN hN hLE hRest) hLog (noteSpendGuardDecodes LE cN hN hLE)
      s args s' h
  exact (apex_iff_noteSpendSpec LE cN hN hLE s args s').mp hapex

#assert_axioms noteSpendGuardLocal
#assert_axioms noteSpendGuardDecodes
#assert_axioms noteSpendGuardEncodes
#assert_axioms apex_iff_noteSpendSpec
#assert_axioms noteSpendE_full_sound

end Dregg2.Circuit.EffectInstances2
