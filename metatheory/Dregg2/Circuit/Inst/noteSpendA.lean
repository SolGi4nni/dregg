/-
# Dregg2.Circuit.Inst.noteSpendA — the v2 (`EffectCommit2`) instance for the note-NULLIFIER SPEND.

`noteSpendA` is the GROW-UNDER-GATE dual of `noteCreateA`: a `noteCreate` GROWS the `commitments` set
UNCONDITIONALLY, but a `noteSpend` GROWS the `nullifiers` set under a DOUBLE-SPEND GATE — fail-closed if
the nullifier is already present (`apply_note_spend`, dregg1 `apply.rs:945`: "double-spend: nullifier
already in note_nullifiers set"). So this instance is NEAR-IDENTICAL to the worked `noteCreateA`
template (`Dregg2/Circuit/Inst/noteCreateA.lean`), with the touched component swapped from `commitments`
to `nullifiers` and the TRIVIAL `Prop`-guard `noteCreateAdmit = True` swapped for the REAL fail-closed
anti-replay guard `noteSpendGuard st nf = nf ∉ st.kernel.nullifiers`.

Through the v2 framework (`EffectCommit2`):
  * touched component = `nullifiers` (a `listComponent`, FULL-list digest `ListCommit.listDigest`; its
    `binds` is `ListDigestBindsList` — FULL-list equality, so a drop/reorder of an existing nullifier is
    REJECTED, not just "grew by `nf`" — anti-replay teeth at the circuit level);
  * the log GROWS by the note-spend receipt (`noteSpendReceipt actor = escrowReceiptA actor`, a self-Turn
    on `actor` with zero amount — note effects move SETS, never balance);
  * the frame is the 16 non-`nullifiers` kernel fields, bound by the REUSED `RestIffNoNullifiers` portal
    ALREADY present in `EffectCommit2` (§1) — NOT a new `RestIffNo*` (this is the portal the v2 framework
    shipped for exactly `noteSpendA`).

`noteSpendA_full_sound` CONCLUDES the bespoke `Spec.NoteNullifier.NoteSpendSpec` THROUGH the framework:
`effect2_circuit_full_sound` gives the derived `apex`, and `apex_iff_noteSpendSpec` rewrites it to the
bespoke spec. The bridge needs an And-reassoc (unlike noteCreate's direct identity match): the v2
`RestIffNoNullifiers` restFrame orders the 16 frame fields as `…escrows BAL revoked commitments…`,
whereas `NoteSpendSpec`'s frame orders them `…escrows REVOKED commitments BAL…`; both directions
re-pack the SAME 19 conjuncts. (The executor corner of this triangle is
`execFullA_noteSpend_iff_spec`.)

ADDITIVE: imports `EffectCommit2` + the bespoke spec `Dregg2.Circuit.Spec.notenullifier`; edits NEITHER
`EffectCommit2`/`EffectInstances2`/`StateCommit` NOR any `Spec/*` file NOR `Dregg2.lean`.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.notenullifier

namespace Dregg2.Circuit.Inst.NoteSpendA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Spec.NoteNullifier
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`mkBitGuard`), copied from the validated template.

`noteSpendA`'s guard is the REAL fail-closed anti-replay `noteSpendGuard st nf = nf ∉ st.kernel.nullifiers`
(unlike `noteCreateA`'s trivial `True`). We commit it as ONE `propBit` column at wire `0`
(guardWidth = 1) and decode via `propBit p = 1 ↔ p` — the bit gate is guard-AGNOSTIC (the same shape that
carries `noteCreateAdmit = True` and `BurnGuard`'s 4-conjunction also carries this membership-negation).
The circuit-level reflection: a double-spend (`nf ∈ nullifiers`) makes `propBit (noteSpendGuard) = 0`, so
the single gate `propBit = 1` is UNSATISFIABLE — the fail-closed gate having teeth in the witness. -/

/-- The guard wire (the single `propBit` column). -/
abbrev vBitGuard : Var := 0

/-- The single guard gate: `propBit (guardProp) = 1`. -/
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

/-- `propBit p = 1 ↔ p` (the decode lemma). -/
theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `noteSpendA` instance (touched component = `nullifiers`).

The rest-frame portal is the REUSED `EffectCommit2.RestIffNoNullifiers` (already present in the framework
for exactly this effect); we do NOT add a new `RestIffNo*`. -/

/-- The note-spend effect arguments: the consumed nullifier, the acting principal, and the §8
spending-proof witness bit (`spendProof`). The proof bit is a circuit GUARD input, exactly as
committed-escrow carries `hidingProof` — a fail-closed §8-portal shadow, so the circuit constrains
the proof gate the same way the executor does. -/
structure NoteSpendArgs where
  nf         : Nat
  actor      : CellId
  spendProof : Bool

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The note-spend guard as a `Prop` (the spec's fail-closed anti-replay `noteSpendGuard`). The §8
spending-proof witness is pinned `true` here: the circuit AIR models the COMMITTED-case nullifier
set-transition (a satisfying note-spend witness is one whose §8 STARK spending proof — a SEPARATE AIR,
`note_spending_air.rs` — already verified), so the circuit corner of the triangle concludes the
`spendProof = true` branch of `NoteSpendSpec`. -/
def noteSpendGuardProp (s : RecChainedState) (args : NoteSpendArgs) : Prop :=
  noteSpendGuard s args.nf args.spendProof

instance (s : RecChainedState) (args : NoteSpendArgs) : Decidable (noteSpendGuardProp s args) := by
  unfold noteSpendGuardProp noteSpendGuard; exact inferInstanceAs (Decidable (_ ∧ _ ∉ _))

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
(`compressNInjective cN` + `listLeafInjective LE`) are consumed in the `listComponent` smart ctor. The
spec'd post-shape is the FULL list `nf :: pre.nullifiers` — a drop/reorder of a prior nullifier is
REJECTED by `ListDigestBindsList` (anti-replay teeth at the circuit level). -/
def nullsComponent (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState NoteSpendArgs :=
  listComponent (·.nullifiers) LE cN hN hLE (fun s args => args.nf :: s.kernel.nullifiers)

/-- **`noteSpendE`** — the `EffectSpec2` for `noteSpendA`, supplied to the v2 framework. -/
def noteSpendE (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    EffectSpec2 RecChainedState NoteSpendArgs where
  view         := chainView
  active       := nullsComponent LE cN hN hLE
  logUpdate    := some (fun s args => noteSpendReceipt args.actor :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.bal = k.bal ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt)
  guardGates   := noteSpendGuardGates
  guardProp    := noteSpendGuardProp
  guardWidth   := 1
  guardEncode  := noteSpendGuardEncode
  guardLocal   := noteSpendGuardLocal
  guardWidth_le := by decide

/-! ### §1a — the per-effect obligations for `noteSpendE`. -/

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

/-- The `noteSpendE` rest-frame portal (the `→`): `RestIffNoNullifiers RH`'s soundness side (the REUSED
`nullifiers`-omitting rest frame the v2 framework ships for this effect). -/
theorem noteSpendRestFrameDecodes (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (hRest : RestIffNoNullifiers S.RH) :
    RestFrameDecodes2 S (noteSpendE LE cN hN hLE) := fun k k' h => (hRest k k').mp h

/-! ### §1b — the apex ↔ `NoteSpendSpec` bridge.

An And-reassoc match (NOT a direct identity, unlike noteCreate): the v2 `restFrame` field order is the
`RestIffNoNullifiers` order (`accounts cell caps escrows BAL revoked commitments queues swiss slotCaveats
factories lifecycle deathCert delegate delegations sealedBoxes`), while `NoteSpendSpec`'s frame order is
`accounts cell caps escrows REVOKED commitments BAL queues …` — the `bal`/`revoked`/`commitments` triple
appears in a DIFFERENT order. Both directions re-pack the SAME 19 conjuncts (guard ∧ nullifiers ∧ log ∧
the 16 frame fields), so `rintro` + a reordered `exact` discharges each direction. -/

/-- **`apex_iff_noteSpendSpec`** — the framework's derived `apex` for `noteSpendE` is EXACTLY
`NoteSpendSpec`. The guard is `noteSpendGuard`; the component `postClause` is the FULL nullifier-list
equality (`nf :: pre`); the log is the receipt-prepended chain; the `restFrame` is the 16
non-`nullifiers` frame clauses (re-associated into `NoteSpendSpec`'s order). -/
theorem apex_iff_noteSpendSpec (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : NoteSpendArgs) (s' : RecChainedState) :
    (noteSpendE LE cN hN hLE).apex s args s' ↔ NoteSpendSpec s args.nf args.actor args.spendProof s' := by
  show (noteSpendGuardProp s args
        ∧ s'.kernel.nullifiers = args.nf :: s.kernel.nullifiers
        ∧ s'.log = noteSpendReceipt args.actor :: s.log
        ∧ ((noteSpendE LE cN hN hLE).restFrame s.kernel s'.kernel))
       ↔ NoteSpendSpec s args.nf args.actor args.spendProof s'
  unfold NoteSpendSpec noteSpendGuardProp noteSpendE
  constructor
  · rintro ⟨hg, hnull, hlog, hAcc, hCell, hCaps, hBal, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hnull, hlog, hAcc, hCell, hCaps, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hnull, hlog, hAcc, hCell, hCaps, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hnull, hlog, hAcc, hCell, hCaps, hBal, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §1c — THE VALIDATION: `noteSpendA_full_sound ⇒ NoteSpendSpec` through the framework. -/

/-- **`noteSpendA_full_sound` — the VALIDATION (note-spend through the v2 framework).** A satisfying v2
full-state witness for `noteSpendE` proves the complete declarative bespoke `NoteSpendSpec`. Portals:
`RestIffNoNullifiers RH` (the `nullifiers`-omitting rest frame, REUSED from the framework),
`logHashInjective LH` (the growing log), `compressNInjective cN` + `listLeafInjective LE` (the
`nullifiers` list-component carriers — the realizable Poseidon-CR set). This CONCLUDES the bespoke
note-nullifier spec (`Spec.NoteNullifier.NoteSpendSpec`, executor corner `execFullA_noteSpend_iff_spec`)
THROUGH the generic `effect2_circuit_full_sound` — the circuit⟺spec corner of the note-nullifier
triangle. -/
theorem noteSpendA_full_sound
    (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoNullifiers S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : NoteSpendArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (noteSpendE LE cN hN hLE) (encodeE2 S (noteSpendE LE cN hN hLE) s args s')) :
    NoteSpendSpec s args.nf args.actor args.spendProof s' := by
  have hapex : (noteSpendE LE cN hN hLE).apex s args s' :=
    effect2_circuit_full_sound S (noteSpendE LE cN hN hLE)
      (noteSpendRestFrameDecodes S LE cN hN hLE hRest) hLog (noteSpendGuardDecodes LE cN hN hLE)
      s args s' h
  exact (apex_iff_noteSpendSpec LE cN hN hLE s args s').mp hapex


/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def noteSpendEWire : EffectSpec2 RecChainedState NoteSpendArgs where
  view         := chainView
  active      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := noteSpendGuardGates
  guardProp    := noteSpendGuardProp
  guardWidth   := 1
  guardEncode  := noteSpendGuardEncode
  guardLocal   := noteSpendGuardLocal
  guardWidth_le := by decide

def noteSpendAAirName : String := "dregg-noteSpendA-v2"

def noteSpendAEmitted : EmittedDescriptor := emittedEffect2 noteSpendAAirName noteSpendEWire

#guard noteSpendAEmitted.name == noteSpendAAirName

/-! ## §2 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms noteSpendGuardLocal
#assert_axioms noteSpendGuardDecodes
#assert_axioms noteSpendGuardEncodes
#assert_axioms apex_iff_noteSpendSpec
#assert_axioms noteSpendA_full_sound

end Dregg2.Circuit.Inst.NoteSpendA
