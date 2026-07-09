/-
# Dregg2.Circuit.Inst.noteCreateA — the v2 (`EffectCommit2`) instance for the note-commitment PUBLISH.

`noteCreateA` is the GROW-ONLY dual of `noteSpendA`: a `noteSpend` GROWS the `nullifiers` set under a
double-spend GATE (fail-closed on a repeated nullifier), but a `noteCreate` GROWS the `commitments`
SET with NO guard at all — the commitment set is APPEND-ONLY and a fresh commitment cannot conflict
(`apply_note_create`, dregg1). So this instance is NEAR-IDENTICAL to the worked `noteSpendE` template in
`EffectInstances2.lean`, with the touched component swapped from `nullifiers` to `commitments` and the
`Prop`-guard swapped from `noteSpendGuard` (fail-closed membership) to `noteCreateAdmit = True` (the
explicit, always-satisfiable "no double-check" guard).

Through the v2 framework (`EffectCommit2`):
  * touched component = `commitments` (a `listComponent`, FULL-list digest `ListCommit.listDigest`; its
    `binds` is `ListDigestBindsList` — FULL-list equality, so a drop/reorder of an existing commitment is
    REJECTED, not just "grew by `cm`");
  * the log GROWS by the note-create receipt (`noteCreateReceipt actor = escrowReceiptA actor`);
  * the frame is the 16 non-`commitments` kernel fields (`RestIffNoCommitments`, ADDED here — the v1
    `RestHashIffFrame` with `commitments` omitted; the swarm adds one `RestIffNo*` per touched field).

`noteCreateA_full_sound` CONCLUDES the bespoke `Spec.NoteCommitment.NoteCreateASpec` THROUGH the
framework: `effect2_circuit_full_sound` gives the derived `apex`, and `apex_iff_noteCreateASpec`
(a DIRECT identity match — the `restFrame` order is verbatim `NoteCreateASpec`'s frame order, unlike
the noteSpend bridge which had to reassoc) rewrites it to the bespoke spec.

ADDITIVE: imports `EffectCommit2` + the bespoke spec `Dregg2.Circuit.Spec.notecommitment`; edits NEITHER
`EffectCommit2`/`EffectInstances2`/`StateCommit` NOR any `Spec/*` file NOR `Dregg2.lean`.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.notecommitment

namespace Dregg2.Circuit.Inst.NoteCreateA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Spec.NoteCommitment
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`mkBitGuard`), copied from the validated template.

`noteCreateA`'s guard is the TRIVIAL `noteCreateAdmit = True` — the note-commitment publish is
UNCONDITIONAL (append-only commitment set, no double-check). We still commit it as ONE `propBit` column
at wire `0` (guardWidth = 1) so the instance shape matches the framework's guard sub-system uniformly;
`propBit True = 1` always, so the single gate `propBit (guardProp) = 1` is always satisfiable — the
circuit-level reflection of "always commits". -/

/-- The guard wire (the single `propBit` column). -/
abbrev vBitGuard : Var := 0

/-- The single guard gate: `propBit (guardProp) = 1`. -/
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

/-- `propBit p = 1 ↔ p` (the decode lemma). -/
theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `RestIffNoCommitments` portal (the v1 `RestHashIffFrame` minus `commitments`).

The realizable injective-rest-hash portal for the effect that touches the `commitments` list: the rest
hash binds the 16 non-`commitments` components (BIDIRECTIONAL), OMITTING `commitments` (the touched
field of `noteCreateA`). This is the 1-line mirror of `EffectCommit2.RestIffNoNullifiers`, swapping the
omitted field from `nullifiers` to `commitments`. Carried Prop hypothesis (realizable — a Poseidon hash
of a canonical serialization of the named fields), never an axiom. -/

/-- **`RestIffNoCommitments RH`** — the rest hash binds the 16 non-`commitments` components
(BIDIRECTIONAL), omitting `commitments` (the touched field of `noteCreateA`). -/
def RestIffNoCommitments (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.bal = k.bal
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt
      ∧ k'.heaps = k.heaps
      ∧ k'.nullifierRoot = k.nullifierRoot ∧ k'.revokedRoot = k.revokedRoot)

/-! ## §2 — the `noteCreateA` instance (touched component = `commitments`). -/

/-- The note-create effect arguments: the commitment and the acting principal. -/
structure NoteCreateArgs where
  cm    : Nat
  actor : CellId

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The note-create guard as a `Prop` (the spec's TRIVIAL `noteCreateAdmit = True`). -/
def noteCreateGuardProp (_s : RecChainedState) (_args : NoteCreateArgs) : Prop :=
  noteCreateAdmit

instance (s : RecChainedState) (args : NoteCreateArgs) : Decidable (noteCreateGuardProp s args) := by
  unfold noteCreateGuardProp noteCreateAdmit; exact inferInstanceAs (Decidable True)

/-- The note-create guard's witness generator: the single `propBit` column at wire `0`. -/
def noteCreateGuardEncode (s : RecChainedState) (args : NoteCreateArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (noteCreateGuardProp s args) else 0

/-- The note-create guard sub-system: the single `propBit` gate. -/
def noteCreateGuardGates : ConstraintSystem := [cBitGuard]

/-- **`noteCreateGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem noteCreateGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied noteCreateGuardGates a ↔ satisfied noteCreateGuardGates b := by
  unfold satisfied noteCreateGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- The `commitments` list component: digest = `listDigest LE cN` over the commitment list. The carriers
(`compressNInjective cN` + `listLeafInjective LE`) are consumed in the `listComponent` smart ctor. The
spec'd post-shape is the FULL list `cm :: pre.commitments` — a drop/reorder of a prior commitment is
REJECTED by `ListDigestBindsList`. -/
def commitsComponent (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState NoteCreateArgs :=
  listComponent (·.commitments) LE cN hN hLE (fun s args => args.cm :: s.kernel.commitments)

/-- **`noteCreateE`** — the `EffectSpec2` for `noteCreateA`, supplied to the v2 framework. -/
def noteCreateE (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    EffectSpec2 RecChainedState NoteCreateArgs where
  view         := chainView
  active       := commitsComponent LE cN hN hLE
  logUpdate    := some (fun s args => noteCreateReceipt args.actor :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.bal = k.bal
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt
      ∧ k'.heaps = k.heaps
      ∧ k'.nullifierRoot = k.nullifierRoot ∧ k'.revokedRoot = k.revokedRoot)
  guardGates   := noteCreateGuardGates
  guardProp    := noteCreateGuardProp
  guardWidth   := 1
  guardEncode  := noteCreateGuardEncode
  guardLocal   := noteCreateGuardLocal
  guardWidth_le := by decide

/-! ### §2a — the per-effect obligations for `noteCreateE`. -/

/-- **`GuardDecodes2 (noteCreateE …)`** — the single bit gate decodes to `noteCreateAdmit`. -/
theorem noteCreateGuardDecodes (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardDecodes2 (noteCreateE LE cN hN hLE) := by
  intro s args s' hsat
  change satisfied noteCreateGuardGates (noteCreateGuardEncode s args s') at hsat
  show noteCreateGuardProp s args
  have hg := hsat cBitGuard (by simp [noteCreateGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, noteCreateGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes2 (noteCreateE …)`** — `noteCreateAdmit` encodes to the satisfied bit gate. -/
theorem noteCreateGuardEncodes (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardEncodes2 (noteCreateE LE cN hN hLE) := by
  intro s args s' hg
  show satisfied noteCreateGuardGates (noteCreateGuardEncode s args s')
  intro c hc
  simp only [noteCreateGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, noteCreateGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-- The `noteCreateE` rest-frame portal (the `→`): `RestIffNoCommitments RH`'s soundness side. -/
theorem noteCreateRestFrameDecodes (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (hRest : RestIffNoCommitments S.RH) :
    RestFrameDecodes2 S (noteCreateE LE cN hN hLE) := fun k k' h => (hRest k k').mp h

/-! ### §2b — the apex ↔ `NoteCreateASpec` bridge.

A DIRECT identity match (no And-reassoc): the `restFrame` field order is VERBATIM `NoteCreateASpec`'s
frame order (`accounts cell caps escrows nullifiers revoked bal queues swiss slotCaveats factories
lifecycle deathCert delegate delegations sealedBoxes`), and the guard / component / log clauses line up
one-to-one. So both directions are a flat re-packaging of the same 19 conjuncts. -/

/-- **`apex_iff_noteCreateASpec`** — the framework's derived `apex` for `noteCreateE` is EXACTLY
`NoteCreateASpec`. The guard is `noteCreateAdmit`; the component `postClause` is the FULL commitment-list
equality (`cm :: pre`); the log is the receipt-prepended chain; the `restFrame` is the 16
non-`commitments` frame clauses in `NoteCreateASpec`'s order. -/
theorem apex_iff_noteCreateASpec (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : NoteCreateArgs) (s' : RecChainedState) :
    (noteCreateE LE cN hN hLE).apex s args s' ↔ NoteCreateASpec s args.cm args.actor s' := by
  show (noteCreateGuardProp s args
        ∧ s'.kernel.commitments = args.cm :: s.kernel.commitments
        ∧ s'.log = noteCreateReceipt args.actor :: s.log
        ∧ ((noteCreateE LE cN hN hLE).restFrame s.kernel s'.kernel))
       ↔ NoteCreateASpec s args.cm args.actor s'
  unfold NoteCreateASpec noteCreateGuardProp noteCreateE
  constructor
  · rintro ⟨hg, hcom, hlog, hAcc, hCell, hCaps, hNul, hRev, hBal, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB, hNR, hRR⟩
    exact ⟨hg, hcom, hlog, hAcc, hCell, hCaps, hNul, hRev, hBal, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB, hNR, hRR⟩
  · rintro ⟨hg, hcom, hlog, hAcc, hCell, hCaps, hNul, hRev, hBal, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB, hNR, hRR⟩
    exact ⟨hg, hcom, hlog, hAcc, hCell, hCaps, hNul, hRev, hBal, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB, hNR, hRR⟩

/-! ### §2c — THE DELIVERABLE: `noteCreateA_full_sound ⇒ NoteCreateASpec` through the framework. -/

/-- **`noteCreateA_full_sound` — the v2 instance (note-create through the framework).** A satisfying v2
full-state witness for `noteCreateE` proves the complete declarative bespoke `NoteCreateASpec`. Portals:
`RestIffNoCommitments RH` (the `commitments`-omitting rest frame), `logHashInjective LH` (the growing
log), `compressNInjective cN` + `listLeafInjective LE` (the `commitments` list-component carriers — the
realizable Poseidon-CR set). This CONCLUDES the bespoke note-commitment spec through the generic
`effect2_circuit_full_sound`, the circuit⟺spec corner of the note-commitment triangle. -/
theorem noteCreateA_full_sound
    (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoCommitments S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : NoteCreateArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (noteCreateE LE cN hN hLE) (encodeE2 S (noteCreateE LE cN hN hLE) s args s')) :
    NoteCreateASpec s args.cm args.actor s' := by
  have hapex : (noteCreateE LE cN hN hLE).apex s args s' :=
    effect2_circuit_full_sound S (noteCreateE LE cN hN hLE)
      (noteCreateRestFrameDecodes S LE cN hN hLE hRest) hLog (noteCreateGuardDecodes LE cN hN hLE)
      s args s' h
  exact (apex_iff_noteCreateASpec LE cN hN hLE s args s').mp hapex

#assert_axioms noteCreateGuardLocal
#assert_axioms noteCreateGuardDecodes
#assert_axioms noteCreateGuardEncodes
#assert_axioms apex_iff_noteCreateASpec

/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def noteCreateEWire : EffectSpec2 RecChainedState NoteCreateArgs where
  view         := chainView
  active      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := noteCreateGuardGates
  guardProp    := noteCreateGuardProp
  guardWidth   := 1
  guardEncode  := noteCreateGuardEncode
  guardLocal   := noteCreateGuardLocal
  guardWidth_le := by decide

def noteCreateAAirName : String := "dregg-noteCreateA-v2"

def noteCreateAEmitted : EmittedDescriptor := emittedEffect2 noteCreateAAirName noteCreateEWire

#guard noteCreateAEmitted.name == noteCreateAAirName

#assert_axioms noteCreateA_full_sound

end Dregg2.Circuit.Inst.NoteCreateA
