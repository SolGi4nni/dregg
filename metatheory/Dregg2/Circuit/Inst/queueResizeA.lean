/-
# Dregg2.Circuit.Inst.queueResizeA — the v2 (`EffectCommit2`) instance for the FIFO queue RE-CAP effect.

`queueResizeA` is the balance-NEUTRAL `queue-fifo-core` constructor of `FullActionA` that RE-CAPS an
existing FIFO queue record: it touches ONLY the `queues` side-table (the witnessed record replaced in
place via `replaceQueue`, buffer UNCHANGED — a capacity-only re-cap) and the chained `log` (a clock
receipt, `amt := 0`); the other 16 kernel fields are the FRAME. Through the v2 framework
(`EffectCommit2`):

  * touched component = `queues` (a `listComponent`, FULL-list digest `ListCommit.listDigest` over the
    `QueueRecord` list; its `binds` is `ListDigestBindsList` — FULL-list equality, so a drop/reorder of
    any OTHER queue record is REJECTED, not just "the re-capped record changed");
  * the log GROWS by the resize receipt (`resizeReceipt actor cell`, a zero-amount clock row);
  * the frame is the 16 non-`queues` kernel fields (`RestIffNoQueues`, ADDED here — the v1
    `RestHashIffFrame` with `queues` omitted; the swarm adds one `RestIffNo*` per touched field).

## The spec-shape wrinkle (read this — it is the load-bearing design decision)

The bespoke `QueueResizeSpec` (in `Dregg2/Circuit/Spec/queuefifocore.lean`, executor corner
`execFullA_queueResizeA_iff_spec`) does NOT pin `queues` by a bare list equality. Its `queues` clause is
a UNIVERSALLY-QUANTIFIED CONDITIONAL:

    ∀ q, findQueue st.kernel.queues id = some q →
           st'.kernel.queues = replaceQueue st.kernel.queues id { q with capacity := newCap }

i.e. it constrains the post-list ONLY on the (guard-guaranteed) branch where the queue EXISTS, and says
nothing on the absent branch. This is a SUBSET / WEAKER relation than the full list-equality the
`listComponent`'s `postClause` delivers. So per `CONTRIBUTING.md` recipe step (5), we make the
component's `expectedList` the canonical post-list (the `findQueue`-match RHS) and prove the
ONE-DIRECTIONAL bridge `apex ⇒ QueueResizeSpec` — the apex's FULL list equality IMPLIES the spec's
conditional clause (on the `some` branch the match reduces to exactly the spec's `replaceQueue …`). The
reverse direction does NOT hold (the spec is silent on the absent branch), and `queueResizeA_full_sound`
needs only the soundness `⇒`, so this is faithful, not a downgrade: a satisfying circuit witness pins
the WHOLE post-`queues` list (a tampered third record is rejected), which is STRONGER than the bespoke
spec demands, and we conclude the bespoke spec from it.

`queueResizeA_full_sound` CONCLUDES the bespoke `Spec.QueueFifoCore.QueueResizeSpec` THROUGH the
framework: `effect2_circuit_full_sound` gives the derived `apex`, and `apex_implies_queueResizeSpec`
rewrites it (And-reassoc + the `findQueue`-match reduction) to the bespoke spec.

ADDITIVE: imports `EffectCommit2` + the bespoke spec `Dregg2.Circuit.Spec.queuefifocore`; edits NEITHER
`EffectCommit2`/`EffectInstances2`/`StateCommit` NOR any `Spec/*` file NOR `Dregg2.lean`.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.queuefifocore

namespace Dregg2.Circuit.Inst.QueueResizeA

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

/-! ## §0 — the single-bit guard sub-system (`mkBitGuard`), copied from the validated template.

`queueResizeA`'s guard is the spec's `resizeGuard` — a 3-conjunct `Prop` (authority over the
representing cell ∧ lifecycle-liveness ∧ `∃ q, findQueue queues id = some q ∧ q.buffer.length ≤ newCap`,
the queue-exists + no-shrink-below-occupancy bound). We commit it as ONE `propBit` column at wire `0`
(guardWidth = 1) and decode via `propBit = 1 ↔ p`. (Identical bit-gate shape to `burnE`/`noteSpendE`;
the bit gate is guard-agnostic, so the 3-conjunct `resizeGuard` fits the same shape.) -/

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
`queueResizeA`). This is the 1-line mirror of `EffectCommit2.RestIffNoBal`, swapping the omitted field
from `bal` to `queues`. Carried Prop hypothesis (realizable — a Poseidon hash of a canonical
serialization of the named fields), never an axiom. -/

/-- **`RestIffNoQueues RH`** — the rest hash binds the 16 non-`queues` components (BIDIRECTIONAL),
omitting `queues` (the touched field of `queueResizeA`). -/
def RestIffNoQueues (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.escrows = k.escrows ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes)

/-! ## §2 — the `queueResizeA` instance (touched component = `queues`). -/

/-- The resize effect arguments: queue id, the new capacity, the acting principal, the representing
cell. -/
structure ResizeArgs where
  id     : Nat
  newCap : Nat
  actor  : CellId
  cell   : CellId

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The resize guard as a `Prop` (the spec's `resizeGuard`). -/
def resizeGuardProp (s : RecChainedState) (args : ResizeArgs) : Prop :=
  resizeGuard s.kernel args.id args.newCap args.actor args.cell

instance (s : RecChainedState) (args : ResizeArgs) : Decidable (resizeGuardProp s args) := by
  unfold resizeGuardProp resizeGuard
  exact inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The resize guard's witness generator: the single `propBit` column at wire `0`. -/
def resizeGuardEncode (s : RecChainedState) (args : ResizeArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (resizeGuardProp s args) else 0

/-- The resize guard sub-system: the single `propBit` gate. -/
def resizeGuardGates : ConstraintSystem := [cBitGuard]

/-- **`resizeGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem resizeGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied resizeGuardGates a ↔ satisfied resizeGuardGates b := by
  unfold satisfied resizeGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- The canonical post-`queues` list a committed resize produces: on the (guard-guaranteed) branch where
the queue EXISTS, the witnessed record is re-capped in place via `replaceQueue` (buffer untouched);
otherwise the list is unchanged (the absent branch never fires under the guard). This is the
component's `expectedList` — a PURE function of pre+args (no executor body), matching `queueResizeK`'s
post-`queues` on the live branch. -/
def resizePostQueues (s : RecChainedState) (args : ResizeArgs) : List QueueRecord :=
  match findQueue s.kernel.queues args.id with
  | some q => replaceQueue s.kernel.queues args.id { q with capacity := args.newCap }
  | none   => s.kernel.queues

/-- The `queues` list component: digest = `listDigest LE cN` over the queue-record list. The carriers
(`compressNInjective cN` + `listLeafInjective LE`) are consumed in the `listComponent` smart ctor (`LE :
QueueRecord → ℤ` is the realizable Poseidon-CR leaf over the record's canonical serialization, the same
CR bar as `noteCreate`'s `LE : Nat → ℤ`). The spec'd post-shape is the FULL list `resizePostQueues` — a
drop/reorder of any OTHER queue record is REJECTED by `ListDigestBindsList`. -/
def queuesComponent (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState ResizeArgs :=
  listComponent (·.queues) LE cN hN hLE resizePostQueues

/-- **`queueResizeE`** — the `EffectSpec2` for `queueResizeA`, supplied to the v2 framework. -/
def queueResizeE (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    EffectSpec2 RecChainedState ResizeArgs where
  view         := chainView
  active       := queuesComponent LE cN hN hLE
  logUpdate    := some (fun s args => resizeReceipt args.actor args.cell :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.escrows = k.escrows ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes)
  guardGates   := resizeGuardGates
  guardProp    := resizeGuardProp
  guardWidth   := 1
  guardEncode  := resizeGuardEncode
  guardLocal   := resizeGuardLocal
  guardWidth_le := by decide

/-! ### §2a — the per-effect obligations for `queueResizeE`. -/

/-- **`GuardDecodes2 (queueResizeE …)`** — the single bit gate decodes to `resizeGuard`. -/
theorem resizeGuardDecodes (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardDecodes2 (queueResizeE LE cN hN hLE) := by
  intro s args s' hsat
  change satisfied resizeGuardGates (resizeGuardEncode s args s') at hsat
  show resizeGuardProp s args
  have hg := hsat cBitGuard (by simp [resizeGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, resizeGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes2 (queueResizeE …)`** — `resizeGuard` encodes to the satisfied bit gate. -/
theorem resizeGuardEncodes (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardEncodes2 (queueResizeE LE cN hN hLE) := by
  intro s args s' hg
  show satisfied resizeGuardGates (resizeGuardEncode s args s')
  intro c hc
  simp only [resizeGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, resizeGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-- The `queueResizeE` rest-frame portal (the `→`): `RestIffNoQueues RH`'s soundness side. -/
theorem resizeRestFrameDecodes (S : Surface2) (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (hRest : RestIffNoQueues S.RH) :
    RestFrameDecodes2 S (queueResizeE LE cN hN hLE) := fun k k' h => (hRest k k').mp h

/-! ### §2b — the apex ⇒ `QueueResizeSpec` bridge (ONE-DIRECTIONAL; see the header wrinkle).

The framework's derived `apex` for `queueResizeE` pins:
  * guard      = `resizeGuard` (verbatim the spec's guard);
  * component  = the FULL list equality `st'.kernel.queues = resizePostQueues s args`;
  * log        = `resizeReceipt actor cell :: s.log`;
  * restFrame  = the 16 non-`queues` frame clauses.
The spec's `queues` clause is the WEAKER conditional `∀ q, findQueue … = some q → st'.kernel.queues =
replaceQueue …`. We prove apex ⇒ spec: on the `some q` branch the apex's full-list RHS `resizePostQueues`
REDUCES (by `findQueue … = some q`) to exactly `replaceQueue … { q with capacity := newCap }`, so the
conditional clause follows; the remaining 16 frame clauses + log + guard match verbatim (And-reassoc). -/

/-- **`apex_implies_queueResizeSpec`** — the framework's derived `apex` for `queueResizeE` IMPLIES the
bespoke `QueueResizeSpec`. (One-directional: the apex's full-list `queues` equality is STRONGER than the
spec's conditional `queues` clause; the reverse does not hold because the spec is silent on the
queue-absent branch.) -/
theorem apex_implies_queueResizeSpec (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : ResizeArgs) (s' : RecChainedState)
    (h : (queueResizeE LE cN hN hLE).apex s args s') :
    QueueResizeSpec s args.id args.newCap args.actor args.cell s' := by
  -- unfold the apex's four conjuncts to the bare components.
  have h' : resizeGuardProp s args
        ∧ s'.kernel.queues = resizePostQueues s args
        ∧ s'.log = resizeReceipt args.actor args.cell :: s.log
        ∧ ((queueResizeE LE cN hN hLE).restFrame s.kernel s'.kernel) := h
  obtain ⟨hg, hq, hlog, hAcc, hCell, hCaps, hEsc, hNul, hRev, hCom, hBal, hSw, hSC, hFac, hLif,
    hDC, hDel, hDgs, hSB⟩ := h'
  refine ⟨hg, ?_, hlog, hAcc, hCell, hCaps, hEsc, hNul, hRev, hCom, hBal, hSw, hSC, hFac, hLif,
    hDC, hDel, hDgs, hSB⟩
  -- the spec's conditional `queues` clause: on any `q` with `findQueue … = some q`, the apex's full-list
  -- RHS `resizePostQueues` reduces (via that lookup) to exactly `replaceQueue … { q with capacity := … }`.
  intro q hfind
  rw [hq, resizePostQueues, hfind]

/-! ### §2c — THE DELIVERABLE: `queueResizeA_full_sound ⇒ QueueResizeSpec` through the framework. -/

/-- **`queueResizeA_full_sound` — the v2 instance (queue re-cap through the framework).** A satisfying v2
full-state witness for `queueResizeE` proves the complete declarative bespoke `QueueResizeSpec`. Portals:
`RestIffNoQueues RH` (the `queues`-omitting rest frame), `logHashInjective LH` (the growing log),
`compressNInjective cN` + `listLeafInjective LE` (the `queues` list-component carriers — the realizable
Poseidon-CR set over the `QueueRecord` list). This CONCLUDES the bespoke queue-fifo-core resize spec
through the generic `effect2_circuit_full_sound`, the circuit⟺spec corner of the queue-resize triangle
(whose executor corner is `Spec.QueueFifoCore.execFullA_queueResizeA_iff_spec`). -/
theorem queueResizeA_full_sound
    (S : Surface2) (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoQueues S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : ResizeArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (queueResizeE LE cN hN hLE) (encodeE2 S (queueResizeE LE cN hN hLE) s args s')) :
    QueueResizeSpec s args.id args.newCap args.actor args.cell s' := by
  have hapex : (queueResizeE LE cN hN hLE).apex s args s' :=
    effect2_circuit_full_sound S (queueResizeE LE cN hN hLE)
      (resizeRestFrameDecodes S LE cN hN hLE hRest) hLog (resizeGuardDecodes LE cN hN hLE)
      s args s' h
  exact apex_implies_queueResizeSpec LE cN hN hLE s args s' hapex


/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def queueResizeEWire : EffectSpec2 RecChainedState ResizeArgs where
  view         := chainView
  active      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := resizeGuardGates
  guardProp    := resizeGuardProp
  guardWidth   := 1
  guardEncode  := resizeGuardEncode
  guardLocal   := resizeGuardLocal
  guardWidth_le := by decide

def queueResizeAAirName : String := "dregg-queueResizeA-v2"

def queueResizeAEmitted : EmittedDescriptor := emittedEffect2 queueResizeAAirName queueResizeEWire

#guard queueResizeAEmitted.name == queueResizeAAirName

/-! ## §3 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms resizeGuardLocal
#assert_axioms resizeGuardDecodes
#assert_axioms resizeGuardEncodes
#assert_axioms apex_implies_queueResizeSpec
#assert_axioms queueResizeA_full_sound

end Dregg2.Circuit.Inst.QueueResizeA
