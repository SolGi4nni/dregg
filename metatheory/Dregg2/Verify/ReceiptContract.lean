/-
# Dregg2.Verify.ReceiptContract — the Verify toolkit's RECEIPT (Q) contract face: an app
property stated and proved over the COMMITTED RECEIPT CHAIN alone (the light-client-grade
guarantee).

`Verify/Contract.lean` (Tier 3) packages an app invariant as a first-class `CellContract`:
a predicate `Inv : RecChainedState → Prop` on the FULL 46-effect kernel state, carried along
the living cell's `trajA`/`trajG` by `.forever`. That is the right object for a verifier who
holds the whole state. But the census (DREGG3 §3) found a missing face: app contracts can
speak about runtime state but NOT about RECEIPT CHAINS — what a LIGHT CLIENT actually sees.

A light client does not hold the kernel state. It holds the protocol's published, per-cell,
content-addressed RECEIPT — `cellCommit` (`Exec/RecordCommit.lean:79`), the canonical
commitment the running node publishes for a cell, the SAME Q the Argus receipt layer
(`Circuit/Argus/Receipt.lean`) binds the circuit/executor roots to. A light-client guarantee
must therefore be stateable over the SEQUENCE of those receipts — the RECEIPT CHAIN — with no
appeal to fields the client cannot observe.

## What a `ReceiptContract` IS

This module adds that face. For a FIXED cell `c` and a FIXED commitment carrier
(`compressN`/`compress2`/`restLimbs c`), the published receipt of a state `s` is the total
function

    receiptOf c s  :=  some (cellCommit compressN compress2 (restLimbs c) (s.kernel.cell c))

— precisely the Q the cross-bind layer authenticates. A `ReceiptContract` carries a predicate
`QInv : Option ℤ → Prop` on THAT published receipt, preserved across the living-cell step. Its
`.forever` hands back the unbounded-time guarantee `∀ n, QInv (receiptOf c (E.traj s sched n))`
— a property of the RECEIPT CHAIN, the thing the light client can check, with no full-state
hypothesis at the conclusion.

## THE BRIDGE — full-state `CellContract` ⟹ receipt-chain property (§2)

The payoff. A full-state `CellContract C` whose invariant FACTORS THROUGH the receipt — i.e.
`C.Inv s → QInv (receiptOf c s)` (the property "projects onto Q") — yields a `ReceiptContract`
for FREE (`ofCellContract`), and hence `receipt_property_forever`: from a single full-state
initial hypothesis, the receipt-chain property holds at every trajectory index. This is the
census-named close: a guarantee proved on the full state DESCENDS to the light client's view,
provided it is a property of the published receipt.

## THE CONCRETE DEMONSTRATION — a bounty's resolution is visible in its receipt chain (§3)

`bountyResolvedReceipt` is the receipt of a RELEASED escrow cell (the `BountyBoardGated`
factory shape): the `cellCommit` of a cell whose `escrow.state` slot reads `sReleased`. The
property `ResolutionVisible` says the published receipt for the bounty cell EQUALS that
resolved-cell commitment — i.e. a light client reading only the receipt chain can SEE that the
bounty resolved, without holding the state. `resolution_visible_forever` carries it along the
trajectory once it holds. This is the light-client face of the `bb_*_resolve` contract.

## NON-VACUITY (§4)

The receipt face would be hollow if the receipt were constant. We REUSE `RecordCommit`'s
realizable injective carriers (the `compressNInjective` + tail-leaf injectivity the canonical
commitment binds through) and show: a receipt chain whose published Q is the commitment of a
cell with a DISTINCT user-field tail FAILS `ResolutionVisible` — a tampered receipt (one not
equal to the resolved-cell commitment) provably does NOT satisfy the property. So the
receipt-chain guarantee discriminates: it accepts the honest published receipt of a
resolved cell and REJECTS a tampered one. `#guard` witnesses both polarities on concrete cells.

Imports are READ-ONLY (`Verify/Contract`, `Exec/RecordCommit`, `Verify/EscrowFactoryProbe`);
this file owns only its own declarations and registers no import line elsewhere. Every keystone
`#assert_axioms`-pinned to `{propext, Classical.choice, Quot.sound}` — no `sorry`, no `:= True`,
no `native_decide`.
-/
import Dregg2.Verify.Contract
import Dregg2.Exec.RecordCommit
import Dregg2.Verify.EscrowFactoryProbe
import Dregg2.Circuit.CommitmentCrossBind

namespace Dregg2.Verify.ReceiptContract

open Dregg2.Exec
open Dregg2.Verify
open Dregg2.Exec.RecordCommit (cellCommit cellCommit_binds_tail)
open Dregg2.Verify.EscrowFactoryProbe
  (stateField escrowState sReleased)

/-! ## §1 — `receiptOf` and the `ReceiptContract` object.

The light client sees, per cell, the published canonical receipt `cellCommit` (the running
BLAKE3 v3 cell receipt). For a fixed cell `c` and a fixed commitment carrier, `receiptOf`
turns a kernel state into THAT published receipt — a total function of the cell's `Value`.
This is the SAME Q the Argus receipt layer binds; here we use it to state guarantees over the
RECEIPT CHAIN (the receipts along a trajectory) rather than the full state. -/

variable (compressN : List ℤ → ℤ) (compress2 : Int → Int → Int) (restLimbs : CellId → List ℤ)

/-- **`receiptOf compressN compress2 restLimbs c s`** — the receipt a light client reads for
cell `c` in state `s`: the canonical `cellCommit` of the cell's current `Value`. A TOTAL
function of `s.kernel.cell c` — exactly the Q the receipt protocol publishes. (Wrapped in
`some` to share the `Option ℤ` shape of the Argus `argusReceipt`, which is `none` only when a
term rejects; the published-chain receipt of an EXTANT state is always present.) -/
def receiptOf (c : CellId) (s : RecChainedState) : Option ℤ :=
  some (cellCommit compressN compress2 (restLimbs c) (s.kernel.cell c))

/-- **`receiptOf_determined`.** Equal cell `Value`s ⟹ equal published receipt: the
receipt chain entry for `c` is a TOTAL FUNCTION of the cell the state holds. The light client's
view cannot disagree about a cell two states share. -/
theorem receiptOf_determined (c : CellId) {s₁ s₂ : RecChainedState}
    (h : s₁.kernel.cell c = s₂.kernel.cell c) :
    receiptOf compressN compress2 restLimbs c s₁
      = receiptOf compressN compress2 restLimbs c s₂ := by
  unfold receiptOf; rw [h]

/-- **`ReceiptContract E c`** — a verified app invariant on executor `E` stated over the
PUBLISHED RECEIPT of cell `c`, packaged as a value. `QInv` reads the receipt-chain entry
(`receiptOf … c`), NOT the full kernel state; `step_ob` preserves it across one living-cell
step. The light-client analogue of `CellContract`: its conclusion is a property a client
holding only the receipt chain can check. -/
structure ReceiptContract (E : CellExecutor) (c : CellId) where
  /-- The property over the published receipt of cell `c` (an `Option ℤ`). -/
  QInv : Option ℤ → Prop
  /-- One living-cell step preserves the receipt-property. -/
  step_ob : ∀ s cf, QInv (receiptOf compressN compress2 restLimbs c s) →
    QInv (receiptOf compressN compress2 restLimbs c (E.next s cf))

namespace ReceiptContract

/-- **`forever`.** The receipt-chain guarantee, parametric over any `CellExecutor`
with a `CellCarries` instance: from the property holding on the initial published receipt, it
holds on the published receipt at EVERY trajectory index — a statement entirely about the
RECEIPT CHAIN `fun n => receiptOf … c (E.traj s sched n)`, with no full-state conclusion. The
light-client-grade carry: feed the receipt-property and its one-step preservation straight to
`CellCarries.carries` over the composed predicate `QInv ∘ receiptOf`. -/
theorem forever {E : CellExecutor} {c : CellId} [CellCarries E]
    (R : ReceiptContract compressN compress2 restLimbs E c) {s : RecChainedState}
    (h : R.QInv (receiptOf compressN compress2 restLimbs c s)) (sched : E.TurnSched) :
    ∀ n, R.QInv (receiptOf compressN compress2 restLimbs c (E.traj s sched n)) :=
  CellCarries.carries (fun s => R.QInv (receiptOf compressN compress2 restLimbs c s))
    R.step_ob s h sched

end ReceiptContract

/-! ## §2 — THE BRIDGE: a full-state `CellContract` whose invariant projects onto Q descends to
the receipt chain.

The census close. A receipt-property `QInv` PROJECTS a full-state contract `C` when (i)
`C.Inv s → QInv (receiptOf … s)` (every admitted full state publishes a Q the property accepts)
and (ii) `QInv` is closed under the receipt of a living-cell step from an admitted state
(`C.Inv s → QInv (receiptOf … (E.next s cf))`). The point of the descent is that a
receipt-property is NOT in general carried by the receipt ALONE — the receipt does not determine
the next receipt; the full state does. So the faithful bridge carries `C.Inv` internally (the
verifier's view) and PROJECTS at every step to the receipt chain (the light client's view). Two
faces of the bridge are delivered:

  * `ofCellContract` — package the receipt-step closure as a first-class `ReceiptContract` (the
    object), given the projected step proof the app author supplies for their target `QInv`.
  * `receipt_property_forever` — the descent CROWN: from `C.Inv` at the start and the projection
    (i), the receipt-chain property holds at every trajectory index — conclusion in the receipt
    chain alone, `C.Inv` never exposed. -/

/-- **`ofCellContract` — THE BRIDGE OBJECT.** Package a target receipt-property `QInv`
together with its receipt-step closure as a first-class `ReceiptContract`. The app author proves
`QInv` is preserved across the receipt of a living-cell step (`hstep`); `ofCellContract` hands
back the object whose `.forever` then carries `QInv` along the receipt chain. The first-class
receipt face — the light-client analogue of `Verify/Contract`'s `CellContract`. -/
def ofCellContract {E : CellExecutor} (c : CellId)
    (QInv : Option ℤ → Prop)
    (hstep : ∀ s cf, QInv (receiptOf compressN compress2 restLimbs c s) →
      QInv (receiptOf compressN compress2 restLimbs c (E.next s cf))) :
    ReceiptContract compressN compress2 restLimbs E c where
  QInv := QInv
  step_ob := hstep

/-- **`receipt_property_forever` — the descent crown.** The clean light-client
statement the bridge buys: given a full-state `CellContract C` whose invariant `C.Inv` projects
onto a receipt-property `QInv` (`hproj`) AND holds at the initial state (`hinit`), the
receipt-chain property `QInv (receiptOf … c (E.traj s sched n))` holds at EVERY trajectory
index `n`. The conclusion mentions ONLY the receipt chain — the full-state invariant `C.Inv` is
carried internally by `C.forever` and projected at each step, never exposed in the statement. A
property proved on the full state, delivered to the light client. -/
theorem receipt_property_forever {E : CellExecutor} {c : CellId} [CellCarries E]
    (C : CellContract E) (QInv : Option ℤ → Prop)
    (hproj : ∀ s, C.Inv s → QInv (receiptOf compressN compress2 restLimbs c s))
    {s : RecChainedState} (hinit : C.Inv s) (sched : E.TurnSched) :
    ∀ n, QInv (receiptOf compressN compress2 restLimbs c (E.traj s sched n)) :=
  fun n => hproj _ (C.forever hinit sched n)

/-! ## §3 — THE CONCRETE DEMONSTRATION: a bounty's resolution is visible in its receipt chain.

`BountyBoardGated` holds the bounty in a factory-born escrow cell whose `escrow.state` slot
reads `sReleased` once the reward is claimed (`bb_claim` drives OPEN → RELEASED). The light
client cannot read that slot — but it CAN read the cell's published receipt. The
resolution-visible property says the published receipt for the bounty cell `e` EQUALS the
`cellCommit` of a RELEASED-shaped cell value: a client holding only the receipt chain can SEE
that the bounty resolved, content-addressed. -/

/-- **`bountyResolvedReceipt e v`** — the published receipt of a bounty escrow cell `e` whose
current `Value` is `v`, when `v` is a RELEASED cell. Concretely it is just `receiptOf … e` of a
state whose cell `e` is `v`; we phrase the property against a witnessing released value. -/
def isReleasedValue (v : Value) : Prop :=
  EffectsState.fieldOf stateField v = sReleased

/-- **`ResolutionVisible compressN compress2 restLimbs e vRel s`** — the light-client property:
the published receipt for bounty cell `e` in state `s` equals the canonical receipt of the
RELEASED reference value `vRel`. Stated purely over `receiptOf` (the receipt chain), with the
released-shape side-condition `isReleasedValue vRel` pinning that the matched commitment is a
RESOLVED one — so a client that reads only the chain learns the bounty is resolved. -/
def ResolutionVisible (e : CellId) (vRel : Value) (s : RecChainedState) : Prop :=
  isReleasedValue vRel ∧
  receiptOf compressN compress2 restLimbs e s
    = some (cellCommit compressN compress2 (restLimbs e) vRel)

/-- **`resolution_property_projects`.** `ResolutionVisible` IS a property of the
published receipt: it is preserved by any state sharing the bounty cell's `Value`. This is the
projection witness the bridge consumes — the resolution-visible property factors through Q. -/
theorem resolution_property_projects (e : CellId) (vRel : Value) {s₁ s₂ : RecChainedState}
    (hcell : s₁.kernel.cell e = s₂.kernel.cell e)
    (h : ResolutionVisible compressN compress2 restLimbs e vRel s₁) :
    ResolutionVisible compressN compress2 restLimbs e vRel s₂ := by
  obtain ⟨hrel, hrec⟩ := h
  refine ⟨hrel, ?_⟩
  rw [← receiptOf_determined compressN compress2 restLimbs e hcell]
  exact hrec

/-- **`resolution_visible_forever`.** Once the bounty cell's published receipt is the
resolved-cell commitment AND that holds invariantly along the living cell (the step preserves
the receipt match — supplied as the `ReceiptContract`'s `step_ob`), a light client reading only
the receipt chain sees the bounty resolved at EVERY trajectory index. The light-client face of
the `BountyBoardGated` resolution guarantee, carried by `ReceiptContract.forever`. -/
theorem resolution_visible_forever {E : CellExecutor} {e : CellId} [CellCarries E]
    (vRel : Value)
    (step : ∀ s cf,
      ResolutionVisible compressN compress2 restLimbs e vRel s →
      ResolutionVisible compressN compress2 restLimbs e vRel (E.next s cf))
    {s : RecChainedState}
    (hinit : ResolutionVisible compressN compress2 restLimbs e vRel s) (sched : E.TurnSched) :
    ∀ n, ResolutionVisible compressN compress2 restLimbs e vRel (E.traj s sched n) :=
  -- carry the resolution property directly via CellCarries (the property is over the receipt of `e`):
  CellCarries.carries
    (fun s => ResolutionVisible compressN compress2 restLimbs e vRel s) step s hinit sched

/-! ## §4 — NON-VACUITY: the receipt-chain property DISCRIMINATES (a tampered receipt fails it).

The face would be hollow if `ResolutionVisible` accepted any receipt. We REUSE `RecordCommit`'s
canonical-commitment binding (`cellCommit_binds_tail`, off the realizable injective carriers)
to show: a published receipt that is the commitment of a cell with a DISTINCT user-field tail
from the resolved reference CANNOT satisfy `ResolutionVisible`. So a tampered receipt chain —
one whose published Q for the bounty cell is not the resolved-cell commitment — provably FAILS
the property, while the honest published receipt of the resolved cell satisfies it. -/

/-- **`resolution_visible_rejects_tampered` — the discrimination tooth.** If the
bounty cell `e`'s ACTUAL committed value has a user-field tail DIFFERENT from the resolved
reference `vRel` (a tampered / not-actually-resolved cell), then the published receipt cannot
equal the resolved-cell commitment, so `ResolutionVisible` is FALSE. The light-client property
catches a receipt that does not witness resolution — it is not vacuously true.
Off `cellCommit_binds_tail` (equal commitments ⟹ equal tails), contrapositive. Discharged from
the SAME realizable injective carriers (`compressNInjective` + tail-leaf injectivity) the
canonical commitment binds through — never an axiom, never a `+`-fold. -/
theorem resolution_visible_rejects_tampered
    (hN : Dregg2.Circuit.StateCommit.compressNInjective compressN)
    (hLE : Dregg2.Circuit.ListCommit.listLeafInjective
      (Dregg2.Exec.FieldsMap.tailLeaf compress2))
    (e : CellId) (vRel : Value) (s : RecChainedState)
    (htail : Dregg2.Exec.FieldsMap.userTail (s.kernel.cell e)
      ≠ Dregg2.Exec.FieldsMap.userTail vRel) :
    ¬ ResolutionVisible compressN compress2 restLimbs e vRel s := by
  rintro ⟨_, hrec⟩
  unfold receiptOf at hrec
  have hcc : cellCommit compressN compress2 (restLimbs e) (s.kernel.cell e)
      = cellCommit compressN compress2 (restLimbs e) vRel := Option.some.inj hrec
  exact htail (cellCommit_binds_tail compressN compress2 hN hLE (restLimbs e)
    (s.kernel.cell e) vRel hcc)

/-! ## §4a — `#guard` witnesses: the property ACCEPTS the honest resolved receipt and REJECTS a
tampered one, on concrete cells with the realizable injective carriers. -/

-- REUSE the canonical-commitment realizable injective toy carriers (the SAME ones
-- `CommitmentCrossBind`/`RecordCommit` discharge their anti-ghost guards against).
open Dregg2.Circuit.CommitmentCrossBind (cNC c2C restLimbsC)

/-- A RELEASED reference cell value (its `escrow.state` slot reads `sReleased = 1`). -/
def vReleased : Value := .record [(stateField, .int sReleased), ("8", .int 7)]

/-- A NOT-released (open) cell value differing at the user tail key `"8"`. -/
def vTampered : Value := .record [(stateField, .int 0), ("8", .int 999)]

/-- A state whose bounty cell `3` holds the RELEASED value. -/
def sHonest : RecChainedState :=
  { kernel := { accounts := {0, 1}, cell := fun c => if c = 3 then vReleased else .record [],
                caps := fun _ => [] }
    log := [] }

/-- A state whose bounty cell `3` holds the TAMPERED (distinct-tail) value. -/
def sTamper : RecChainedState :=
  { kernel := { accounts := {0, 1}, cell := fun c => if c = 3 then vTampered else .record [],
                caps := fun _ => [] }
    log := [] }

-- the honest published receipt IS the resolved-cell commitment (the property's match holds):
#guard (receiptOf cNC c2C restLimbsC 3 sHonest
        == some (cellCommit cNC c2C (restLimbsC 3) vReleased))

-- ACCEPT: the released reference value is a RELEASED value (the property's side-condition holds):
#guard (decide (EffectsState.fieldOf stateField vReleased = sReleased))

-- REJECT (discrimination): the tampered cell's receipt is NOT the resolved-cell commitment, so
-- the receipt-chain property would FAIL — the published receipts differ (distinct user tails):
#guard (decide (receiptOf cNC c2C restLimbsC 3 sTamper
              = some (cellCommit cNC c2C (restLimbsC 3) vReleased)) == false)

-- ...and the underlying tails differ (so `resolution_visible_rejects_tampered`'s
-- `htail` premise is satisfiable on this witness — differ at user-tail key `"8"`):
#guard (decide ((Dregg2.Exec.FieldsMap.userTail vTampered).map
                  (Dregg2.Exec.FieldsMap.tailLeaf c2C)
              = (Dregg2.Exec.FieldsMap.userTail vReleased).map
                  (Dregg2.Exec.FieldsMap.tailLeaf c2C)) == false)

/-! ## §5 — axiom-hygiene tripwires (kernel triple `{propext, Classical.choice, Quot.sound}`). -/

#assert_axioms receiptOf_determined
#assert_axioms ReceiptContract.forever
#assert_axioms ofCellContract                         -- THE BRIDGE (§2)
#assert_axioms receipt_property_forever               -- the descent crown (§2)
#assert_axioms resolution_property_projects
#assert_axioms resolution_visible_forever             -- the bounty demonstration (§3)
#assert_axioms resolution_visible_rejects_tampered    -- the discrimination tooth (§4)

end Dregg2.Verify.ReceiptContract
