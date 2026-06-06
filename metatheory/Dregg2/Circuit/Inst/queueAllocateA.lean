/-
# Dregg2.Circuit.Inst.queueAllocateA — the v2 (`EffectCommit2`) instance for the FIFO-queue ALLOCATE.

`queueAllocateA` is the freshly-allocated FIFO ring-buffer constructor of `FullActionA`: a
balance-NEUTRAL allocate that PREPENDS one fresh `QueueRecord` (`owner := actor`, empty buffer, the
given capacity) onto the `queues` side-table under a two-leg admissibility guard (authority over the
representing cell ∧ id FRESHNESS), advances the chained `log` by the allocate receipt, and FREEZES the
other 16 kernel fields. It is NEAR-IDENTICAL to the `noteCreateA` worked template
(`Dregg2/Circuit/Inst/noteCreateA.lean`) — the SAME `listComponent` shape (a `List`-side-table whose
digest is the FULL-list `ListCommit.listDigest`, so a drop/reorder of an existing queue is REJECTED, not
just "grew by the new record"), the SAME growing log, the SAME `RestIffNo<touched>` frame portal —
differing ONLY in (1) the touched list is `queues` (`List QueueRecord`) rather than `commitments`
(`List Nat`), so the leaf encoder is `LE : QueueRecord → ℤ`; (2) the spec-predicted post-list prepends
the `freshQueue` record (not a bare `cm`); (3) the guard is the 2-conjunct `allocateGuard`
(state-authority ∧ id-freshness) rather than the trivial `noteCreateAdmit = True`; and (4) the receipt +
bridge target are the allocate's (`allocateReceipt`, `QueueAllocateSpec`).

THE VALIDATION: `queueAllocateA_full_sound ⇒ QueueAllocateSpec` THROUGH the framework. A satisfying v2
full-state witness for `queueAllocateE` proves the complete declarative `QueueAllocateSpec` (the apex
truth in `Dregg2/Circuit/Spec/queuefifocore.lean`, whose executor corner is
`execFullA_queueAllocateA_iff_spec`).

ADDITIVE: imports `EffectCommit2` + the queue-fifo-core spec; edits NEITHER of them NOR `Dregg2.lean`.
Follows the `noteCreateA` template EXACTLY + the recipe in `Dregg2/Circuit/CONTRIBUTING.md`.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.queuefifocore

namespace Dregg2.Circuit.Inst.QueueAllocateA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Spec.QueueFifoCore
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`mkBitGuard`, copied from the validated template).

The allocate spec exposes its guard as a `Prop` (`allocateGuard` = state-authority ∧ id-freshness), not
a per-gate circuit, so we commit it as ONE `propBit` column at wire `0` (guardWidth = 1) and decode via
`propBit = 1 ↔ p`. (Identical to `noteCreateA`/`burnA`; the bit gate is guard-agnostic, so the 2-conjunct
`allocateGuard` fits the same shape.) -/

/-- The guard wire (the single `propBit` column). -/
abbrev vBitGuard : Var := 0

/-- The single guard gate: `propBit (guardProp) = 1`. -/
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

/-- `propBit p = 1 ↔ p` (the decode lemma). -/
theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `RestIffNoQueues` portal (the v1 `RestHashIffFrame` minus `queues`).

The realizable injective-rest-hash portal for the effect that touches the `queues` list: the rest hash
binds the 16 non-`queues` components (BIDIRECTIONAL), OMITTING `queues` (the touched field of
`queueAllocateA`). This is the 1-line mirror of `EffectCommit2.RestIffNoNullifiers`, swapping the omitted
field from `nullifiers` to `queues`. Carried Prop hypothesis (realizable — a Poseidon hash of a canonical
serialization of the named fields), never an axiom. The frame field order is VERBATIM
`QueueAllocateSpec`'s frame order (`accounts cell caps escrows nullifiers revoked commitments bal swiss
slotCaveats factories lifecycle deathCert delegate delegations sealedBoxes`). -/

/-- **`RestIffNoQueues RH`** — the rest hash binds the 16 non-`queues` components (BIDIRECTIONAL),
omitting `queues` (the touched field of `queueAllocateA`). -/
def RestIffNoQueues (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.escrows = k.escrows ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes)

/-! ## §2 — the `queueAllocateA` instance (touched component = `queues`). -/

/-- The allocate effect arguments: queue id, acting principal, representing cell, capacity. -/
structure AllocateArgs where
  id    : Nat
  actor : CellId
  cell  : CellId
  cap   : Nat

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The allocate guard as a `Prop` (the spec's `allocateGuard` = state-authority ∧ id-freshness). -/
def allocateGuardProp (s : RecChainedState) (args : AllocateArgs) : Prop :=
  allocateGuard s.kernel args.id args.actor args.cell

instance (s : RecChainedState) (args : AllocateArgs) : Decidable (allocateGuardProp s args) := by
  unfold allocateGuardProp allocateGuard; exact inferInstanceAs (Decidable (_ ∧ _))

/-- The allocate guard's witness generator: lay the single `propBit` column at wire `0`. -/
def allocateGuardEncode (s : RecChainedState) (args : AllocateArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (allocateGuardProp s args) else 0

/-- The allocate guard sub-system: the single `propBit` gate. -/
def allocateGuardGates : ConstraintSystem := [cBitGuard]

/-- **`allocateGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem allocateGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied allocateGuardGates a ↔ satisfied allocateGuardGates b := by
  unfold satisfied allocateGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- The `queues` list component: digest = `listDigest LE cN` over the queue side-table. The carriers
(`compressNInjective cN` + `listLeafInjective LE`) are consumed in the `listComponent` smart ctor. The
spec'd post-shape is the FULL list `freshQueue id actor cap :: pre.queues` — a drop/reorder of a prior
queue record is REJECTED by `ListDigestBindsList`. -/
def queuesComponent (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState AllocateArgs :=
  listComponent (·.queues) LE cN hN hLE
    (fun s args => freshQueue args.id args.actor args.cap :: s.kernel.queues)

/-- **`queueAllocateE`** — the `EffectSpec2` for `queueAllocateA`, supplied to the v2 framework. -/
def queueAllocateE (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    EffectSpec2 RecChainedState AllocateArgs where
  view         := chainView
  active       := queuesComponent LE cN hN hLE
  logUpdate    := some (fun s args => allocateReceipt args.actor args.cell :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.escrows = k.escrows ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes)
  guardGates   := allocateGuardGates
  guardProp    := allocateGuardProp
  guardWidth   := 1
  guardEncode  := allocateGuardEncode
  guardLocal   := allocateGuardLocal
  guardWidth_le := by decide

/-! ### §2a — the per-effect obligations for `queueAllocateE`. -/

/-- **`GuardDecodes2 (queueAllocateE …)`** — the single bit gate decodes to `allocateGuard`. -/
theorem allocateGuardDecodes (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardDecodes2 (queueAllocateE LE cN hN hLE) := by
  intro s args s' hsat
  change satisfied allocateGuardGates (allocateGuardEncode s args s') at hsat
  show allocateGuardProp s args
  have hg := hsat cBitGuard (by simp [allocateGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, allocateGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes2 (queueAllocateE …)`** — `allocateGuard` encodes to the satisfied bit gate. -/
theorem allocateGuardEncodes (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardEncodes2 (queueAllocateE LE cN hN hLE) := by
  intro s args s' hg
  show satisfied allocateGuardGates (allocateGuardEncode s args s')
  intro c hc
  simp only [allocateGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, allocateGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-- The `queueAllocateE` rest-frame portal (the `→`): `RestIffNoQueues RH`'s soundness side. -/
theorem allocateRestFrameDecodes (S : Surface2) (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (hRest : RestIffNoQueues S.RH) :
    RestFrameDecodes2 S (queueAllocateE LE cN hN hLE) := fun k k' h => (hRest k k').mp h

/-! ### §2b — the apex ↔ `QueueAllocateSpec` bridge.

A DIRECT identity match (no And-reassoc): the `restFrame` field order is VERBATIM `QueueAllocateSpec`'s
frame order (`accounts cell caps escrows nullifiers revoked commitments bal swiss slotCaveats factories
lifecycle deathCert delegate delegations sealedBoxes`), and the guard / component / log clauses line up
one-to-one. So both directions are a flat re-packaging of the same 19 conjuncts. -/

/-- **`apex_iff_queueAllocateSpec`** — the framework's derived `apex` for `queueAllocateE` is EXACTLY
`QueueAllocateSpec`. The guard is `allocateGuard`; the component `postClause` is the FULL queue-list
equality (`freshQueue id actor cap :: pre`); the log is the receipt-prepended chain; the `restFrame` is
the 16 non-`queues` frame clauses in `QueueAllocateSpec`'s order. -/
theorem apex_iff_queueAllocateSpec (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : AllocateArgs) (s' : RecChainedState) :
    (queueAllocateE LE cN hN hLE).apex s args s'
      ↔ QueueAllocateSpec s args.id args.actor args.cell args.cap s' := by
  show (allocateGuardProp s args
        ∧ s'.kernel.queues = freshQueue args.id args.actor args.cap :: s.kernel.queues
        ∧ s'.log = allocateReceipt args.actor args.cell :: s.log
        ∧ ((queueAllocateE LE cN hN hLE).restFrame s.kernel s'.kernel))
       ↔ QueueAllocateSpec s args.id args.actor args.cell args.cap s'
  unfold QueueAllocateSpec allocateGuardProp queueAllocateE
  constructor
  · rintro ⟨hg, hq, hlog, hAcc, hCell, hCaps, hEsc, hNul, hRev, hCom, hBal, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hq, hlog, hAcc, hCell, hCaps, hEsc, hNul, hRev, hCom, hBal, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hq, hlog, hAcc, hCell, hCaps, hEsc, hNul, hRev, hCom, hBal, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hq, hlog, hAcc, hCell, hCaps, hEsc, hNul, hRev, hCom, hBal, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §2c — THE VALIDATION: `queueAllocateA_full_sound ⇒ QueueAllocateSpec` through the framework. -/

/-- **`queueAllocateA_full_sound` — the VALIDATION (queue-allocate through the v2 framework).** A
satisfying v2 full-state witness for `queueAllocateE` proves the complete declarative bespoke
`QueueAllocateSpec`. Portals: `RestIffNoQueues RH` (the `queues`-omitting rest frame), `logHashInjective
LH` (the growing log), `compressNInjective cN` + `listLeafInjective LE` (the `queues` list-component
carriers — the realizable Poseidon-CR set). This CONCLUDES the bespoke queue-fifo-core spec through the
generic `effect2_circuit_full_sound`, the circuit⟺spec corner of the queue-allocate triangle (whose
executor corner is `execFullA_queueAllocateA_iff_spec`). -/
theorem queueAllocateA_full_sound
    (S : Surface2) (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoQueues S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : AllocateArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (queueAllocateE LE cN hN hLE)
          (encodeE2 S (queueAllocateE LE cN hN hLE) s args s')) :
    QueueAllocateSpec s args.id args.actor args.cell args.cap s' := by
  have hapex : (queueAllocateE LE cN hN hLE).apex s args s' :=
    effect2_circuit_full_sound S (queueAllocateE LE cN hN hLE)
      (allocateRestFrameDecodes S LE cN hN hLE hRest) hLog (allocateGuardDecodes LE cN hN hLE)
      s args s' h
  exact (apex_iff_queueAllocateSpec LE cN hN hLE s args s').mp hapex


/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def queueAllocateEWire : EffectSpec2 RecChainedState AllocateArgs where
  view         := chainView
  active      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := allocateGuardGates
  guardProp    := allocateGuardProp
  guardWidth   := 1
  guardEncode  := allocateGuardEncode
  guardLocal   := allocateGuardLocal
  guardWidth_le := by decide

def queueAllocateAAirName : String := "dregg-queueAllocateA-v2"

def queueAllocateAEmitted : EmittedDescriptor := emittedEffect2 queueAllocateAAirName queueAllocateEWire

#guard queueAllocateAEmitted.name == queueAllocateAAirName

/-! ## §3 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms allocateGuardLocal
#assert_axioms allocateGuardDecodes
#assert_axioms allocateGuardEncodes
#assert_axioms apex_iff_queueAllocateSpec
#assert_axioms queueAllocateA_full_sound

end Dregg2.Circuit.Inst.QueueAllocateA
