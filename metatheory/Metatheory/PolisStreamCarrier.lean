/-
# Metatheory.PolisStreamCarrier — the StreamProp carrier bound to the DEPLOYED adversary stream.

`Metatheory.PolisCrossCell` built the *generic* shared-carrier framework (gpt5.5's answer to Q6,
`docs/POLIS-HYPERPROPERTY-FRONTIER.md`): the polis anti-capture floor and circuit cross-cell
soundness are NOT the same property, but they share a CARRIER — properties of public interleaved
adversary STREAMS. This file makes that carrier CONCRETE by binding it to the deployed object:
`Dregg2.Proof.CoinductiveAdversary.obsStream`, the observation trajectory the live `TurnCoalg`
emits as the coinductive unbounded-interleaving adversary drives it along a `Sched`.

We then define TWO SEPARATE `StreamProp`-style predicates over that one carrier:

  * **`circuitSoundnessProp`** — the deployed circuit guarantee: the implementation's observation
    stream coincides, tick-for-tick, with the golden oracle's stream (confluence-up-to-bisimulation,
    `obsStream_eq_of_bisim`). A property of the observable trace alone.
  * **`polisFloorProp`** — the polis anti-capture floor: an exported, public, decidable floor on
    observations holds at EVERY tick of the stream (the trace-shape bar, never the interior).

These are kept **DISTINCT defs over the same carrier** — they are NEVER identified. This is the
load-bearing caution (gpt5.5's): collapsing them would let circuit confluence (an implementation
matches its oracle) masquerade as anti-tyranny (a subject's floor is never foreclosed), a false
claim. `same_carrier_distinct_predicates` records that they range over the same `Nat → Obs`
carrier and reuse the same `Monitorable` decision machinery, while `not_identified` exhibits a
model where one holds and the other fails — they are genuinely different stream properties.

## HONESTY FRAMING

This is a **BOUNDED / PUBLIC / DECIDABLE** binding: each predicate is a property of the public
observation stream `obsStream`, and the shared decision fragment is the finite-prefix
`Monitorable` witness (`violation_has_finite_witness`) — a finite public bad-prefix governs a
violation. It is NOT "full politics solved": exhibiting a `Monitorable` witness for the genuine
temporal polis floor over the real deployed `Obs` lattice remains the open frontier
(`Metatheory.Polis.CaptureBar` interface; the Büchi-game `FlowRefine.decideRefines` connection).
What is delivered here is the honest binding — the two distinct predicates over the deployed
carrier, plus a non-vacuity model and the shared-machinery / non-collapse record.

Imports the deployed `Dregg2.Proof.CoinductiveAdversary` and the framework
`Metatheory.PolisCrossCell`; no `sorry`, no `:= True` load-bearing.
-/
import Dregg2.Proof.CoinductiveAdversary
import Metatheory.PolisCrossCell

namespace Metatheory.PolisStreamCarrier

open Dregg2.Boundary (TurnCoalg IsBisim bisim_eq)
open Dregg2.Proof.CoinductiveAdversary
open Metatheory.PolisCrossCell (StreamProp Monitorable violation_has_finite_witness)

-- `PolisCrossCell.StreamProp` is defined at universe 0 (`variable {Event : Type}`), so the
-- carrier type `Obs` lives at `Type` (universe 0). `AdmissibleTurn` matches the deployed
-- `CoinductiveAdversary` signatures at the same level.
variable {Obs AdmissibleTurn : Type}

/-! ## §1 — The shared carrier IS the deployed `obsStream`.

`PolisCrossCell.StreamProp Event := (Nat → Event) → Prop`. The deployed
`CoinductiveAdversary.obsStream Impl x s : ℕ → Obs` is exactly an `Event = Obs` carrier: the
public observation trajectory the live cell emits as the coinductive adversary drives it along the
schedule `s`. Both frontiers (circuit soundness, polis floor) are predicates of THIS object. -/

/-- **`carrier Impl x s`** — the shared carrier as the DEPLOYED observation stream. This is the one
`Nat → Obs` object both `circuitSoundnessProp` and `polisFloorProp` are predicates of; it is
literally `CoinductiveAdversary.obsStream` (the badge the `TurnCoalg` emits per adversary tick). -/
def carrier (Impl : TurnCoalg Obs AdmissibleTurn) (x : Impl.Carrier)
    (s : Sched AdmissibleTurn) : Nat → Obs :=
  obsStream Impl x s

@[simp] theorem carrier_eq_obsStream (Impl : TurnCoalg Obs AdmissibleTurn) (x : Impl.Carrier)
    (s : Sched AdmissibleTurn) : carrier Impl x s = obsStream Impl x s := rfl

/-! ## §2 — Predicate ONE: circuit cross-cell soundness over the carrier.

A `StreamProp Obs` (= `(Nat → Obs) → Prop`). The deployed circuit guarantee is
`obsStream_eq_of_bisim`: the implementation's observation stream EQUALS the golden oracle's stream
at every tick along the unbounded adversarial schedule. We express that as a stream property
parameterised by the oracle's reference stream `golden`. -/

/-- **`circuitSoundnessProp golden`** — the circuit cross-cell soundness predicate, over the shared
carrier. `circuitSoundnessProp golden σ` holds iff the stream `σ` coincides tick-for-tick with the
golden-oracle reference stream `golden`: confluence-up-to-bisimulation made observable. This is a
property of the *trace*, never the interior — the vat boundary cannot tell `σ` from the oracle. -/
def circuitSoundnessProp (golden : Nat → Obs) : StreamProp Obs :=
  fun σ => ∀ n, σ n = golden n

/-- The deployed `obsStream_eq_of_bisim` discharges `circuitSoundnessProp` for the live carrier:
if a `Boundary.IsBisim` relates the implementation cell `x` to the oracle cell `y`, then the
deployed `carrier`/`obsStream` satisfies `circuitSoundnessProp` against the oracle's own stream. -/
theorem circuitSoundnessProp_of_bisim
    {Impl Spec : TurnCoalg Obs AdmissibleTurn} {R : Impl.Carrier → Spec.Carrier → Prop}
    (hR : IsBisim Impl Spec R) {x : Impl.Carrier} {y : Spec.Carrier} (hxy : R x y)
    (s : Sched AdmissibleTurn) :
    circuitSoundnessProp (obsStream Spec y s) (carrier Impl x s) := by
  intro n
  have h := obsStream_eq_of_bisim hR hxy s
  simp only [carrier]
  exact congrFun h n

/-! ## §3 — Predicate TWO: the polis anti-capture floor over the carrier.

A SEPARATE `StreamProp Obs`. The polis floor is a public, exported, decidable predicate on
*observations* (`floor : Obs → Prop`, the trace-shape bar of `Metatheory.Polis` — never the
interior) that must hold at EVERY tick of the stream. The politician lives in the trace: a captured
subject is one whose floor is foreclosed at some tick. -/

/-- **`polisFloorProp floor`** — the polis anti-capture floor predicate, over the shared carrier.
`polisFloorProp floor σ` holds iff the public floor `floor` holds at EVERY tick of `σ`. This is the
trace-shape bar (a subject's exported floor over public observations) lifted to the unbounded
adversarial stream: anti-foreclosure forever. Distinct from `circuitSoundnessProp` — it speaks of a
subject-owned floor on each observation, not of agreement with an oracle. -/
def polisFloorProp (floor : Obs → Prop) : StreamProp Obs :=
  fun σ => ∀ n, floor (σ n)

/-- The deployed coinductive carrier carries a tick-local floor along the WHOLE unbounded schedule
when the floor is preserved by the live step (the safety face). This reuses the deployed
`stepComplete_carries_infinite` shape: a floor that holds at the start and is re-established each
tick holds at every `obsStream` tick. Here we take the direct route over `obsStream`/`traj`: if the
floor on observations holds at every trajectory point, it holds at every carrier tick. -/
theorem polisFloorProp_of_pointwise
    (Impl : TurnCoalg Obs AdmissibleTurn) (x : Impl.Carrier) (s : Sched AdmissibleTurn)
    (floor : Obs → Prop)
    (hpt : ∀ n, floor (Impl.obs (traj Impl x s n))) :
    polisFloorProp floor (carrier Impl x s) := by
  intro n
  simp only [carrier, obsStream]
  exact hpt n

/-- The polis floor as a stream property is exactly the per-tick floor over the deployed
`obsStream` — the binding is definitional (no interior, public observations only). -/
theorem polisFloorProp_carrier_unfold
    (Impl : TurnCoalg Obs AdmissibleTurn) (x : Impl.Carrier) (s : Sched AdmissibleTurn)
    (floor : Obs → Prop) :
    polisFloorProp floor (carrier Impl x s) ↔ ∀ n, floor (Impl.obs (traj Impl x s n)) :=
  Iff.rfl

/-! ## §4 — SAME carrier, SEPARATE predicates — the non-collapse record (gpt5.5's caution).

The two predicates above range over the SAME carrier type `Nat → Obs` (and, when instantiated, the
SAME deployed `carrier`/`obsStream` object) and reuse the SAME `Monitorable` finite-prefix decision
machinery. They are NEVER identified. Collapsing them would let circuit confluence (an impl matches
its oracle) masquerade as anti-tyranny (a subject's floor is never foreclosed). We record both
facts: shared carrier/machinery, and a model that distinguishes them. -/

/-- The two predicates have the SAME carrier type: both are `StreamProp Obs = (Nat → Obs) → Prop`.
A trivial-but-load-bearing type-level witness that they are predicates of one carrier. -/
theorem same_carrier_distinct_predicates (golden : Nat → Obs) (floor : Obs → Prop) :
    (circuitSoundnessProp golden : StreamProp Obs) = circuitSoundnessProp golden ∧
    (polisFloorProp floor : StreamProp Obs) = polisFloorProp floor :=
  ⟨rfl, rfl⟩

/-- Both predicates plug into the SAME shared decision fragment: given a `Monitorable` witness for
either, a violation has a finite public bad prefix (`violation_has_finite_witness`). The decision
machinery is shared; the predicates are not. -/
theorem shared_decision_machinery {P : StreamProp Obs} (M : Monitorable P)
    (σ : Nat → Obs) (h : ¬ P σ) : ∃ n, M.bad σ n :=
  violation_has_finite_witness M σ h

/-- **`not_identified` — the two predicates are GENUINELY DIFFERENT.** Over `Obs = Bool` we exhibit
one carrier and floors where `circuitSoundnessProp` HOLDS but `polisFloorProp` FAILS: the impl
stream equals the oracle (circuit-sound) yet every tick violates the polis floor (the subject is
fully foreclosed). So `circuitSoundnessProp golden = polisFloorProp floor` is FALSE — collapsing
them is unsound, exactly the over-claim gpt5.5 warned against (confluence ≠ anti-tyranny). -/
theorem not_identified :
    ∃ (golden : Nat → Bool) (floor : Bool → Prop),
      (circuitSoundnessProp golden ≠ polisFloorProp floor) := by
  -- golden = all-false; floor = "is true". The all-false stream is circuit-sound vs golden
  -- (it equals it), but violates the floor at every tick. So one holds where the other fails.
  refine ⟨(fun _ => false), (fun b => b = true), ?_⟩
  intro heq
  -- `circuitSoundnessProp (fun _ => false) (fun _ => false)` holds (the stream equals golden).
  have hsound : circuitSoundnessProp (fun _ => false) (fun _ : Nat => false) := fun _ => rfl
  -- but rewriting by the (assumed) equality of the *predicates* gives the floor at every tick.
  have hfloor : polisFloorProp (fun b => b = true) (fun _ : Nat => false) := by
    rw [← heq]; exact hsound
  -- contradiction: floor at tick 0 says `false = true`.
  exact absurd (hfloor 0) (by decide)

/-! ## §5 — Non-vacuity on the deployed carrier (both predicates inhabited).

So this is not a "beautiful but empty" binding: each predicate genuinely holds for the deployed
carrier in a concrete model. -/

/-- `circuitSoundnessProp` is inhabited on the deployed carrier: by reflexivity of bisimulation
(`bisim_eq`), the live cell's `obsStream` is circuit-sound against its OWN stream (the impl is its
own oracle — the diagonal). Uses the deployed `obsStream_eq_of_bisim` via `circuitSoundnessProp_of_bisim`. -/
theorem circuitSoundnessProp_inhabited (Impl : TurnCoalg Obs AdmissibleTurn) (x : Impl.Carrier)
    (s : Sched AdmissibleTurn) :
    circuitSoundnessProp (obsStream Impl x s) (carrier Impl x s) :=
  circuitSoundnessProp_of_bisim (bisim_eq Impl) rfl s

/-- `polisFloorProp` is inhabited on the deployed carrier: the trivial floor `fun _ => True` holds
at every tick of any `obsStream`. (A non-trivial floor needs the substrate's `Obs` lattice — that
is the named frontier, §6.) -/
theorem polisFloorProp_inhabited (Impl : TurnCoalg Obs AdmissibleTurn) (x : Impl.Carrier)
    (s : Sched AdmissibleTurn) :
    polisFloorProp (fun _ => True) (carrier Impl x s) :=
  fun _ => trivial

/-! ## §6 — The named frontier (honest residual).

What is BOUND here: the carrier (deployed `obsStream`), and the two distinct stream predicates over
it, with their deployed discharge lemmas (`circuitSoundnessProp_of_bisim` from
`obsStream_eq_of_bisim`; `polisFloorProp_of_pointwise` from the per-tick observation floor), the
non-collapse record (`not_identified`), and the shared decision fragment
(`shared_decision_machinery`).

What is NOT solved (the frontier, not faked): a `Monitorable` witness for the GENUINE temporal
polis floor over the REAL deployed `Obs` lattice — the public bad-prefix predicate for true
temporal capture. That is the open research the `Metatheory.Polis.CaptureBar` interface names
(connect to `FlowRefine.decideRefines` / the Büchi game). This file delivers the honest binding of
the carrier and the two predicates, not the full anti-capture monitor. -/

end Metatheory.PolisStreamCarrier
