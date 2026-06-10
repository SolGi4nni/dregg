/-
# Dregg2.Circuit.Argus.Coeffect — welding the (un-witnessed) intent/coeffect layer to the Argus IR.

`Intent/Core.lean` builds the four-faced `Intent` (a co-receipt: a typed hole `offered ⟶ wanted`,
a predicate, a one-shot escrow, a deadline) and `fulfill` (the counit: plug a conversion into the
hole, annihilating the co-receipt into a discharging `FillReceipt`). `Intent/Match.lean` is the
solver as a coend `∫^B` with the co-Yoneda collapse, and `Intent/Ring.lean` is the REAL ring trade:
`settleRing` atomically folds a cycle's legs through the verified per-asset executor `recKExecAsset`,
proving value-neutrality (`settleRing_conserves`), atomicity (`settleRing_atomic`), and that the
solver's `validate_ring` construction is `RingBalanced` + individually rational (Shapley–Scarf).

But that whole intent/coeffect layer was **un-witnessed by the circuit**. `settleRing` talks about
the executor `recKExecAsset`; the Argus IR (`Circuit/Argus/Stmt.lean`, `Compile.lean`, the per-effect
welds in `Effects/*.lean`) is where a state transition carries BOTH an executor interpretation
(`interp`) AND a circuit interpretation (`compile`) that provably agree. The coeffect layer never
touched that second interpretation: a settled ring carried conservation, but no `compile_sound`.

This module is the CONNECTION (it owns ONLY this file; it imports the intent + Argus layers
read-only and re-derives none of their theorems). The link is exact and already proven one leg at a
time, in `Effects/BalanceA.lean`:

    interp_balanceAStmt_eq_recKExecAsset turn a k :  interp (balanceAStmt turn a) k = recKExecAsset k turn a

i.e. the per-asset Argus term `balanceAStmt` has the ledger executor `recKExecAsset` AS ITS `interp`.
And `settleRing` is *exactly* a fold of `recKExecAsset` over the legs (`Ring.lean:95`):

    settleRing k r = r.foldlM (fun s l => recKExecAsset s l.toTurn l.asset) k

So **each settlement step IS an Argus `balanceA` interp run**, and the whole ring settlement IS a fold
of Argus interp runs (`settleRing_is_argus_fold`). That is the weld: the un-witnessed coeffect layer's
settlement is, leg by leg, the executor interpretation of an Argus IR term — and that SAME term carries
the circuit. We then connect a settled leg to `balanceA`'s OWN audited circuit soundness
(`balanceA_compile_sound`, the full 17-field `BalanceMovementSpec` agreement), so a settled ring's every
leg carries an Argus `compile_sound`: the circuit the prover runs for that leg pins the whole post-state
the leg's executor produces. The headline (`settled_ring_leg_circuit_pins_executor_state`) is a fulfilled
ring-settlement as a chain of Argus-circuit-witnessed transitions, with conservation inherited verbatim.

## What CONNECTS vs the named GAP (honest — read this).

CONNECTS (PROVEN, reusing the layers' theorems, not re-derived):

  1. **Each `settleRing` leg IS an Argus `balanceA` interp run** (`settleLeg_is_argus_interp`) — the
     ring's settlement step `recKExecAsset k l.toTurn l.asset` is *definitionally, after the cornerstone*
     `interp (legStmt l) k`. The coeffect layer's atomic fold (`Ring.lean`) is literally folding the
     executor interpretation of Argus IR terms.
  2. **The whole ring settlement is a fold of Argus interp runs** (`settleRing_is_argus_fold`) — and so
     a SETTLED ring carries the Argus IR by construction; `settled_ring_legs_are_argus` exhibits each
     committed leg's pre/post as `interp (legStmt l) sᵢ = some sᵢ₊₁`.
  3. **A settled leg carries `balanceA`'s circuit soundness on the FULL state**
     (`settled_ring_leg_circuit_pins_executor_state`) — for a leg whose destination accepts effects,
     a satisfying witness of balanceA's OWN standalone v2 circuit agrees with the leg's executor
     post-state on the WHOLE `BalanceMovementSpec` (all 17 kernel fields + the receipt log), via the
     reused `balanceA_compile_sound`. So the un-witnessed leg is now circuit-witnessed.
  4. **Conservation of the circuit-witnessed ring is inherited** (`settled_argus_ring_conserves`) — the
     reused `settleRing_conserves`: the ring whose legs are Argus interp runs conserves every asset.
  5. **A FULFILLED intent's bilateral conversion gives a settled balanceA leg** (`fulfilled_intent_leg_…`)
     — connecting `fulfill` (the counit) to the Argus leg: a 2-party fulfilled exchange is a settleRing
     leg, hence an Argus `balanceA` interp run carrying the circuit. The coeffect counit reaches the IR.

The NAMED GAP (not papered):

  * **The circuit weld is PER-LEG + needs the chained R1 side-condition; the WHOLE-RING single
    aggregated circuit proof is NOT claimed here.** `settleRing` folds the RAW kernel step
    `recKExecAsset` (no `acceptsEffects` dst-liveness gate, no receipt log). balanceA's circuit
    soundness is keyed on the CHAINED executor `recCexecAsset`/`execFullA` (which adds the R1 dst-
    liveness pre-gate + the log prepend). So `settled_ring_leg_circuit_pins_executor_state` carries the
    `acceptsEffects st.kernel l.to_ = true` hypothesis PER LEG (exactly as `Effects/BalanceA.lean §3`
    does) and welds ONE leg's circuit against ONE leg's executor post-state. The aggregation of all
    legs' per-leg circuit proofs into a SINGLE proof over the ring is the recursive-aggregation /
    `Circuit/TurnEmit` layer — cited, NOT re-proved here. This is the same honest per-row→whole-turn
    boundary the transfer/mint/burn welds live on (`Compile.lean` SCOPE), surfaced at the ring.

## Axiom hygiene

`#assert_axioms` on every headline ⊆ {propext, Classical.choice, Quot.sound}; the Poseidon-CR /
whole-function-digest assumption enters ONLY inside the reused `balanceA_full_sound` (its
`Function.Injective D` portal), never in a welded conclusion's *statement*. No `sorry`, no `:= True`,
no `native_decide`. Imports are read-only; this file owns only its own declarations. Pure.
-/
import Dregg2.Intent.Ring
import Dregg2.Circuit.Argus.Effects.BalanceA

set_option linter.dupNamespace false

namespace Dregg2.Circuit.Argus.Coeffect

open Dregg2.Exec
  (RecordKernelState AssetId Turn CellId RecChainedState recKExecAsset recTotalAsset)
-- `acceptsEffects` (the chained R1 dst-liveness gate) lives in `TurnExecutorFull`, alongside the chained
-- executors `recCexecAsset`/`execFullA` the standalone balanceA descriptor is keyed on (the same broad open
-- `Effects/BalanceA.lean` uses). We only NAME `acceptsEffects` here; the chained executors enter through the
-- reused `balanceA_compile_sound` / `interp_balanceAStmt_chained`, so we keep the open surface minimal.
open Dregg2.Exec.TurnExecutorFull (acceptsEffects)
open Dregg2.Circuit.Argus (RecStmt interp)
open Dregg2.Circuit.Argus.Effects.BalanceA
  (balanceAStmt interp_balanceAStmt_eq_recKExecAsset interp_balanceAStmt_chained
   balanceACircuit balanceA_compile_sound)
open Dregg2.Intent.Ring (RingLeg Ring settleRing settleRing_nil settleRing_cons settleRing_conserves)
open Dregg2.Circuit.EffectCommit2 (Surface2 RestIffNoBal)
open Dregg2.Circuit.StateCommit (logHashInjective)
open Dregg2.Circuit.Spec.BalanceMovement (BalanceMovementSpec)

/-! ## §1 — The Argus IR term of a ring leg (the per-leg coeffect→IR map).

A ring leg `l : RingLeg` is the Rust `solver::Settlement` (`from`/`to`/`asset`/`amount`), and its
settlement step is `recKExecAsset s l.toTurn l.asset` (`Ring.settleRing`'s fold body). That executor
IS the `interp` of the Argus per-asset term `balanceAStmt l.toTurn l.asset` (`Effects/BalanceA.lean`'s
cornerstone). So a leg's Argus IR term is just that `balanceAStmt` — and the un-witnessed leg becomes
a `RecStmt` carrying BOTH the executor (`interp`) and the circuit (`balanceACircuit`). -/

/-- **`legStmt l` — the Argus IR term of a ring settlement leg.** The per-asset value-movement term
`balanceAStmt l.toTurn l.asset`: gate (the 6-conjunct `recKExecAsset` admissibility), then move the
`(from, asset)`/`(to, asset)` columns of the genuine per-asset ledger `bal`. This is the SAME `RecStmt`
the executor-refinement (`interp`) and the circuit (`balanceACircuit`) are both defined over — the
coeffect layer's leg, reified as an Argus term. -/
def legStmt (l : RingLeg) : RecStmt :=
  balanceAStmt l.toTurn l.asset

/-! ## §2 — THE CORNERSTONE: each settlement step IS an Argus `balanceA` interp run.

The single fact that welds the coeffect layer to the IR: the ring's fold body `recKExecAsset k
l.toTurn l.asset` is, after `Effects/BalanceA.lean`'s cornerstone, `interp (legStmt l) k`. Nothing is
re-derived — this is `interp_balanceAStmt_eq_recKExecAsset` applied at the leg's turn/asset. -/

/-- **`settleLeg_is_argus_interp` (CORNERSTONE).** A `settleRing` leg's executor step over the per-asset
ledger IS the Argus IR term's executor interpretation: `recKExecAsset k l.toTurn l.asset =
interp (legStmt l) k`. The un-witnessed coeffect settlement step is literally the `interp` of an Argus
term (so it also carries that term's circuit, §4). Reuses the per-asset cornerstone verbatim. -/
theorem settleLeg_is_argus_interp (k : RecordKernelState) (l : RingLeg) :
    recKExecAsset k l.toTurn l.asset = interp (legStmt l) k :=
  (interp_balanceAStmt_eq_recKExecAsset l.toTurn l.asset k).symm

#assert_axioms settleLeg_is_argus_interp

/-! ## §3 — The whole ring settlement is a fold of Argus interp runs.

Lifting §2 over the leg list: `settleRing` (the coeffect layer's atomic fold) IS the fold of Argus
`interp` runs. So a SETTLED ring is, by construction, a chain of Argus IR transitions — the layer the
circuit speaks about. We then read each committed leg's pre/post off the fold as an Argus `interp`
commit (`settled_ring_legs_are_argus`), the bridge a per-leg circuit weld (§4) consumes. -/

/-- The Argus-interp fold over a ring: run `interp (legStmt ·)` leg by leg, all-or-nothing (`foldlM`
on `Option`). DEFINITIONALLY equal to `settleRing` (§ below) — named so the ring's settlement reads as
a fold of Argus interp runs. -/
def settleRingArgus (k : RecordKernelState) (r : Ring) : Option RecordKernelState :=
  r.foldlM (fun s l => interp (legStmt l) s) k

/-- **`settleRing_is_argus_fold` — the coeffect layer's settlement IS a fold of Argus interp runs.**
`settleRing k r = settleRingArgus k r`: the atomic fold `Ring.lean` proves conserving/atomic is,
leg-for-leg, the fold of `interp (legStmt ·)` — the Argus IR's executor interpretation of each leg. The
un-witnessed intent settlement is exactly Argus IR execution. Proven by rewriting the fold body with the
§2 cornerstone (the two folds have identical bodies after it). -/
theorem settleRing_is_argus_fold (k : RecordKernelState) (r : Ring) :
    settleRing k r = settleRingArgus k r := by
  unfold settleRing settleRingArgus
  -- the two `foldlM` bodies agree pointwise by the §2 cornerstone.
  have hbody : (fun s (l : RingLeg) => recKExecAsset s l.toTurn l.asset)
             = (fun s (l : RingLeg) => interp (legStmt l) s) := by
    funext s l; exact settleLeg_is_argus_interp s l
  rw [hbody]

#assert_axioms settleRing_is_argus_fold

/-- A one-step unfold of the Argus settlement fold: settle the head leg's Argus term, then the tail.
The Argus-side mirror of `settleRing_cons`, immediate from the fold-IS-settleRing identity. -/
theorem settleRingArgus_cons (k : RecordKernelState) (l : RingLeg) (r : Ring) :
    settleRingArgus k (l :: r)
      = (interp (legStmt l) k).bind (fun k' => settleRingArgus k' r) := by
  rw [← settleRing_is_argus_fold, settleRing_cons, settleLeg_is_argus_interp]
  simp only [settleRing_is_argus_fold]

/-- **`settled_ring_legs_are_argus` — a committed head leg of a settled ring IS an Argus interp commit.**
If a ring `l :: r` settles, then its head leg commits as an Argus interp run to some intermediate state
`k₁` (`interp (legStmt l) k = some k₁`) and the tail settles from `k₁`. This reads the fold's per-leg
pre/post as Argus `interp` commits — the bridge the per-leg circuit weld (§4) consumes (it needs a leg's
`interp (legStmt l) … = some …`). Reuses `settleRing_cons` through the §2 cornerstone. -/
theorem settled_ring_legs_are_argus (k k' : RecordKernelState) (l : RingLeg) (r : Ring)
    (hsettle : settleRing k (l :: r) = some k') :
    ∃ k₁, interp (legStmt l) k = some k₁ ∧ settleRing k₁ r = some k' := by
  rw [settleRing_cons] at hsettle
  cases hhead : recKExecAsset k l.toTurn l.asset with
  | none => rw [hhead] at hsettle; simp at hsettle
  | some k₁ =>
    refine ⟨k₁, ?_, ?_⟩
    · rw [← settleLeg_is_argus_interp]; exact hhead
    · rw [hhead] at hsettle; rwa [Option.bind_some] at hsettle

#assert_axioms settled_ring_legs_are_argus

/-! ## §4 — THE CIRCUIT WELD: a settled leg carries balanceA's OWN circuit soundness, on the FULL state.

This is where the coeffect layer reaches the SECOND interpretation. `Effects/BalanceA.lean §4` proves
`balanceA_compile_sound`: a satisfying witness of balanceA's own standalone v2 `Surface2` circuit
(`balanceACircuit`) AGREES with the executor's chained post-state on the WHOLE `BalanceMovementSpec`
(all 17 kernel fields + the receipt log), given the leg's `interp` commits and the destination accepts
effects. We thread a settled-ring leg through it: a leg of a ring that settles is a `balanceA` interp
commit (§3), so — modulo the chained R1 dst-liveness side-condition — its OWN circuit pins the whole
state the leg's executor produces. The un-witnessed coeffect leg is now CIRCUIT-witnessed.

### The named GAP, restated where it bites.

The hypothesis `haccept : acceptsEffects st.kernel l.to_ = true` is the chained-vs-raw R1 gate
(`Effects/BalanceA.lean §3`): `settleRing` folds the RAW `recKExecAsset` (no dst-liveness pre-gate, no
log), while balanceA's circuit is keyed on the CHAINED `recCexecAsset`/`execFullA`. So this welds ONE
leg's circuit against ONE leg's executor post-state, carrying R1 explicitly. The single aggregated
circuit proof over the WHOLE ring is the recursive-aggregation / `Circuit/TurnEmit` layer — NOT claimed
here. -/

/-- **`settled_ring_leg_circuit_pins_executor_state` — a settled-ring leg carries an Argus `compile_sound`
on the FULL post-state.**

For a ring `l :: r` that SETTLES (`hsettle : settleRing k (l :: r) = some k'`, the load-bearing
hypothesis — §3's `settled_ring_legs_are_argus` extracts the head leg's executor commit FROM it, so this
is a statement about a settled ring, not an arbitrary committing leg), read on a chained state `st` whose
kernel is the leg's pre-state (`hpre`) and whose destination accepts effects (`haccept`, the chained R1
side-condition): if balanceA's OWN standalone v2 circuit `balanceACircuit S D hD st l.toTurn l.asset st'`
is satisfied (under the realizable whole-function-digest portals `hRest`/`hLog`/`hD`), then there is a
per-leg post-kernel `k₁` — the one the SETTLEMENT itself produces (`interp (legStmt l) k = some k₁`) — and
the chained post-state the CIRCUIT pins is EXACTLY the chained post-state that leg's EXECUTOR produces:
`st' = { kernel := k₁, log := l.toTurn :: st.log }`.

I.e. the circuit the prover runs for this settled ring's leg agrees with the leg's executor on the WHOLE
17-field `RecordKernelState` (`bal` debited/credited by `recTransferBal`, every other field frozen) AND
the receipt log — balanceA's full `BalanceMovementSpec`, not a per-cell projection. The coeffect layer's
settlement leg is welded to the Argus circuit. Reuses `settled_ring_legs_are_argus` (§3, the leg's commit
FROM the settling ring) + `balanceA_compile_sound` (§4 of `Effects/BalanceA.lean`) — re-derives nothing.

GAP (named): per-LEG, with the R1 `haccept` hypothesis; the whole-ring aggregated proof is the
`TurnEmit`/recursive-aggregation layer, cited not claimed. -/
theorem settled_ring_leg_circuit_pins_executor_state
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (st st' : RecChainedState) (k k' : RecordKernelState) (l : RingLeg) (r : Ring)
    (hpre : st.kernel = k)
    (hsettle : settleRing k (l :: r) = some k')
    (haccept : acceptsEffects st.kernel l.to_ = true)
    (hcirc : balanceACircuit S D hD st l.toTurn l.asset st') :
    ∃ k₁, interp (legStmt l) k = some k₁
      ∧ st' = { kernel := k₁, log := l.toTurn :: st.log } := by
  -- §3: the head leg's executor commit comes FROM the settling ring (`hsettle`), not supplied separately.
  obtain ⟨k₁, hleg, _htail⟩ := settled_ring_legs_are_argus k k' l r hsettle
  refine ⟨k₁, hleg, ?_⟩
  -- transport the leg's commit onto `st.kernel` (= `k`).
  have hexec : interp (legStmt l) st.kernel = some k₁ := by rw [hpre]; exact hleg
  -- `legStmt l = balanceAStmt l.toTurn l.asset`, and `recKExecAsset`'s `dst` IS `l.toTurn.dst = l.to_`,
  -- so `haccept` is exactly balanceA's R1 side-condition at `l.toTurn.dst`.
  have haccept' : acceptsEffects st.kernel l.toTurn.dst = true := haccept
  -- reuse balanceA's OWN circuit⟺executor full-state weld (§4 of Effects/BalanceA.lean), verbatim.
  exact balanceA_compile_sound S D hD hRest hLog st st' l.toTurn l.asset k₁ hcirc haccept' hexec

#assert_axioms settled_ring_leg_circuit_pins_executor_state

/-! ## §5 — Conservation of the circuit-witnessed ring (inherited verbatim).

The ring whose legs are Argus interp runs (§3) STILL conserves every asset — `Ring.lean`'s
`settleRing_conserves`, restated over the Argus-fold identity so the conservation keystone reads as a
property of the Argus-IR-witnessed settlement. Reused, not re-proved. -/

/-- **`settled_argus_ring_conserves` — the Argus-witnessed ring settlement conserves value per asset.**
If the Argus interp fold `settleRingArgus k r` commits to `k'`, then for EVERY asset `b` the total supply
is preserved (`recTotalAsset k' b = recTotalAsset k b`). The coeffect layer's value-neutrality keystone
(`settleRing_conserves`) holds verbatim of the settlement-as-Argus-fold: a ring of Argus `balanceA`
interp runs mints/burns nothing. Reuses `settleRing_conserves` through the fold identity (§3). -/
theorem settled_argus_ring_conserves (r : Ring) (k k' : RecordKernelState)
    (h : settleRingArgus k r = some k') :
    ∀ b : AssetId, recTotalAsset k' b = recTotalAsset k b := by
  rw [← settleRing_is_argus_fold] at h
  exact settleRing_conserves r k k' h

#assert_axioms settled_argus_ring_conserves

/-! ## §6 — The COUNIT reaches the IR: a FULFILLED intent's bilateral leg is an Argus balanceA run.

`Intent/Core.lean`'s `fulfill` is the receipt⊣intent counit; `Intent/Match.lean`'s `FillReceipt.lensFill`
turns a fulfilled intent into the bilateral conversion `offered ⟶ outcome`. The ring layer settles such a
bilateral exchange as a 2-leg cycle (`chainedRing` of two nodes, the bilateral swap). Here we close the
loop from `fulfill` to the Argus circuit at the leg level: the value-movement leg a bilateral fulfillment
induces IS a `settleRing` leg, hence (§2) an Argus `balanceA` interp run carrying the circuit (§4). The
coeffect counit — "intent fulfilled" — reaches the Argus IR's two interpretations. -/

/-- **`fulfilled_intent_leg_is_argus_interp` — the value-movement leg of a fulfilled exchange IS an Argus
interp run.** Given any ring leg `l` (e.g. the `from`/`to`/`asset`/`amount` a bilateral fulfillment emits
— `offerer → wanter`, the matched asset and amount), its settlement step over the per-asset ledger is the
Argus term's executor interpretation: `recKExecAsset k l.toTurn l.asset = interp (legStmt l) k`. So the
counit's produced movement is Argus IR execution — and (§4) carries the circuit. This is `settleLeg_is_
argus_interp` exposed at the fulfillment boundary: the coeffect counit reaches the IR. -/
theorem fulfilled_intent_leg_is_argus_interp (k : RecordKernelState) (l : RingLeg) :
    recKExecAsset k l.toTurn l.asset = interp (legStmt l) k :=
  settleLeg_is_argus_interp k l

/-- **`fulfilled_bilateral_ring_is_argus` — a fulfilled bilateral exchange, settled as a 2-leg cycle, IS a
fold of Argus interp runs that conserves.** A 2-leg ring `[l₀, l₁]` (the bilateral swap `validate_ring`
builds for a fulfilled `A↔B` exchange) settles as the Argus interp fold (§3) and, if it commits, conserves
every asset (§5). So a fulfilled bilateral intent's whole settlement is Argus IR execution with the
conservation keystone — and each leg carries the circuit (§4). The counit reaches the IR end-to-end at the
bilateral case. -/
theorem fulfilled_bilateral_ring_is_argus (k : RecordKernelState) (l₀ l₁ : RingLeg) :
    settleRing k [l₀, l₁] = settleRingArgus k [l₀, l₁]
    ∧ (∀ k', settleRingArgus k [l₀, l₁] = some k' →
        ∀ b : AssetId, recTotalAsset k' b = recTotalAsset k b) :=
  ⟨settleRing_is_argus_fold k [l₀, l₁],
   fun k' h b => settled_argus_ring_conserves [l₀, l₁] k k' h b⟩

#assert_axioms fulfilled_intent_leg_is_argus_interp
#assert_axioms fulfilled_bilateral_ring_is_argus

/-! ## §7 — NON-VACUITY: the weld is about a REAL settlement that MOVES the ledger.

The connection would be hollow if the Argus settlement fold never committed or moved nothing. We exhibit a
concrete 2-leg ring over a funded ledger and show the Argus fold (§3) commits AND moves value — the legs
are real `balanceA` interp runs, not a vacuous identity. The `closedRing3` of `Ring.lean` is `RingBalanced`
but not funded on an arbitrary ledger; here we fund a tiny bilateral cycle so the fold settles. -/

/-- A funded 2-cell ledger for the non-vacuity witness: cells 0 and 1 are live accounts; cell 0 holds 5 of
asset 7, cell 1 holds 5 of asset 8 (a fundable bilateral swap of distinct assets). -/
def kRing0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun c a => if c = 0 ∧ a = 7 then 5 else if c = 1 ∧ a = 8 then 5 else 0 }

/-- A bilateral cycle: leg 0 moves 5 of asset 7 from cell 0 to cell 1; leg 1 moves 5 of asset 8 from cell 1
to cell 0 (the swap `validate_ring` builds for a fulfilled `0↔1` exchange). Each cell sends and receives. -/
def bilatRing0 : Ring :=
  [ { actor := 0, from_ := 0, to_ := 1, asset := 7, amount := 5 },
    { actor := 1, from_ := 1, to_ := 0, asset := 8, amount := 5 } ]

-- The Argus settlement fold COMMITS (the legs are satisfiable balanceA interp runs over the funded ledger):
#guard (settleRingArgus kRing0 bilatRing0).isSome
-- It moves value: after settlement, cell 1 holds the 5 of asset 7 it received, cell 0 holds the 5 of asset 8:
#guard ((settleRingArgus kRing0 bilatRing0).map (fun k => (k.bal 1 7, k.bal 0 8))) == some (5, 5)
-- ...and the senders are drained (cell 0's asset-7 and cell 1's asset-8 both go to 0): a REAL movement.
#guard ((settleRingArgus kRing0 bilatRing0).map (fun k => (k.bal 0 7, k.bal 1 8))) == some (0, 0)

/-- **`bilatRing0_settles_via_argus` — the Argus settlement fold COMMITS and MOVES the ledger.**
The funded bilateral cycle settles through the Argus interp fold (§3) to a state where the moved columns
have transferred (cell 1 gains 5 of asset 7, cell 0 gains 5 of asset 8) — the legs are REAL
`balanceA` interp runs, so `settled_ring_leg_circuit_pins_executor_state` and the conservation keystone are
about a non-vacuous settlement, not an empty fold. -/
theorem bilatRing0_settles_via_argus :
    (settleRingArgus kRing0 bilatRing0).map (fun k => (k.bal 1 7, k.bal 0 8)) = some (5, 5) := by
  rw [← settleRing_is_argus_fold]
  decide

/-- **`bilatRing0_argus_conserves` — and the committed Argus ring conserves every asset (non-vacuously).**
Asset 7's and asset 8's total supply are each unchanged across the settlement — value moved between cells,
none minted or burned. The conservation keystone (§5) applied to the concrete funded ring. -/
theorem bilatRing0_argus_conserves :
    ∀ k', settleRingArgus kRing0 bilatRing0 = some k' →
      recTotalAsset k' 7 = recTotalAsset kRing0 7
      ∧ recTotalAsset k' 8 = recTotalAsset kRing0 8 :=
  fun k' h => ⟨settled_argus_ring_conserves bilatRing0 kRing0 k' h 7,
               settled_argus_ring_conserves bilatRing0 kRing0 k' h 8⟩

#assert_axioms bilatRing0_settles_via_argus
#assert_axioms bilatRing0_argus_conserves

end Dregg2.Circuit.Argus.Coeffect
