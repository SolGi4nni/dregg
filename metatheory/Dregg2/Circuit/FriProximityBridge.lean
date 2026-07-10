/-
# `Dregg2.Circuit.FriProximityBridge` — DEBT-A #3: the missing bridge between the TWO
`FriProximity` Props (geometric vs. operational).

## The gap this closes

Two different `Prop`s share the name `FriProximity`, and — until this file — no term connected
them. `AirSoundness.lean` did not even `import FriSoundness`.

  * **GEOMETRIC** (`FriSoundness.FriProximity S d f := closeN S.C d f`): the oracle `f` is
    `d`-close to the low-degree Reed-Solomon code `S.C`. PROVED (`friProximity_discharge`) and
    instantiated at the DEPLOYED BabyBear field + rate `1/8` (`BabyBearFriDeployed`,
    `deployedRate_friProximity`).
  * **OPERATIONAL** (`AirSoundness.FriProximity applyEff verifyLD openTr`): acceptance of the
    low-degree verifier forces the OPENED TRACE to satisfy the transition constraints. This is
    exactly what `AirSoundness.circuit_sound_via_fri` CONSUMES to yield `CircuitSound`.

`friProximity_bridge` produces the operational Prop from the geometric one plus two EXPLICIT,
VISIBLE hypotheses — the codeword-side content (`hcode_sat`) and the Merkle/HashCR plumbing
(`hplumb`) — and `circuit_sound_via_bridge` composes it through `circuit_sound_via_fri` to
`CircuitSound`, with the FRI half supplied at the DEPLOYED field/rate in `deployedRate_circuit_sound`.

## What `air_binds_of_proximity` delivers (the PROVED codeword-side half)

`FriSoundness.air_binds_of_proximity (hp : FriProximity S d f) (constraint) (hconstr : ∀ g ∈ S.C,
constraint g) : ∃ g ∈ S.C, (disagree f g).card ≤ d ∧ constraint g`. It does NOT prove any
constraint on its own; it TRANSPORTS a property that holds on EVERY codeword (`hconstr`) onto a
SPECIFIC codeword `g` near the oracle `f` (within `d`). At `d = 0` the near codeword IS the oracle
(`disagree = ∅ ⇒ f = g`), so it yields exactly: the constraints that hold on all codewords hold on
the committed oracle codeword. `constraint g := satisfiesTransition applyEff (traceOf g).1 …` makes
`hconstr` our `hcode_sat`.

## Honest scope + the fix to the stated `hcode_sat`

The brick-3 lane stated `hcode_sat` with conclusion `satisfiesTransition applyEff (openTr com).1
(openTr com).2` — the bound codeword `g` UNUSED in the conclusion. That statement is DEGENERATE:
`g` unused ⇒ `hFRI`/`air_binds` unused ⇒ the bridge holds by handing `hcode_sat` straight to the
goal, and `hcode_sat` reduces to a bare `∀ com, satisfiesTransition applyEff (openTr com)…` (the
code is a submodule, always inhabited by `0`). That would be exactly the forbidden
"holds-by-unfolding" `hcode_sat`. This file makes the codeword LOAD-BEARING: `hcode_sat` is stated
on the DECODED codeword `traceOf g`, and the link `openTr com = traceOf (oracle com)` is the
SEPARATE, explicit `hplumb` (Merkle-binding: the opened trace IS the committed oracle's trace, an
appeal to `Poseidon2SpongeCR`/`HashCR` per `AirSoundness.committed_trace_pinned`).

## The residual (what remains assumed)

`friProximity_bridge` is PROVED. Its inputs are three EXPLICIT hypotheses:
  1. `hFRI` — the geometric proximity, PROVED and dischargeable at the deployed field/rate
     (`deployedRate_friProximity`);
  2. `hplumb` — `openTr com = traceOf (oracle com)` (Merkle binding ⇒ `HashCR`/`Poseidon2SpongeCR`);
  3. `hcode_sat` — every low-degree codeword decodes to a transition-satisfying trace (the
     genuine codeword-side obligation half (ii) `AirChecksSatisfied` discharges for the ARITHMETIC
     arms of the deployed descriptor).
No `…Hard` carrier, no `:= True`, no tautology-by-definition.

## ⚠ ARITY CAVEAT (not deployed-arity soundness)

The FRI setup `hFRI` is discharged at is a degree-`2` Reed-Solomon code whose fold is **2-to-1**
(`FriGeom`'s `σ`/`q`). The DEPLOYED p3 FRI folds **8-to-1** (`max_log_arity = 3`,
`plonky3_prover.rs:98`). Matching the deployed rate `1/8` AND the deployed 8-to-1 fold needs a
degree-`2^(m-2)` code whose folding closure is a separate, UNWRITTEN proof. So even a PROVED bridge
composed with a deployed-FIELD+RATE FRI half does NOT give deployed-ARITY soundness. This file
claims the bridge and the field/rate composition; it does NOT claim deployed-arity FRI soundness.

## Teeth

  * RESPECTING: an honest constant `traceOf` (every codeword ↦ the honest row `⟨0,1,1⟩`) makes the
    bridge FIRE to the operational `FriProximity` and thence `CircuitSound` (`respecting_*`).
  * BITING: `hcode_sat` is LOAD-BEARING — a `traceOf` that decodes the codeword `0 ∈ C` to a lying
    row `⟨0,1,5⟩` (`5 ≠ 0 + 1`) FALSIFIES `hcode_sat` (`hcode_sat_load_bearing`), so it is a real
    obligation, not free by unfolding.

Sibling `Dregg2/Crypto/MlDsaSignReal.lean` is modified in the working tree — that is another lane's
file; FLAGGED, not owned here.
-/
import Dregg2.Circuit.FriSoundness
import Dregg2.Circuit.AirSoundness
import Dregg2.Circuit.BabyBearFriDeployed

namespace Dregg2.Circuit.FriProximityBridge

open Dregg2.Circuit.FriSoundness
  (FriProximity closeN closeN_zero_iff_mem air_binds_of_proximity FriSetup disagree
   disagree_eq_empty_iff)
open Dregg2.Circuit.AirSoundness (Step satisfiesTransition airChecks circuit_sound_via_fri)
open Dregg2.Crypto.TurnSoundness (CircuitSound)
open Dregg2.Circuit.BabyBearFriDeployed
  (friSetupDeployedRate deployedRate_friProximity fHonestParam omega16)
open Dregg2.Circuit.BabyBearFriField (BabyBear)

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {State Effect Proof Commitment : Type*}

/-! ## §1 — THE BRIDGE.

`friProximity_bridge` turns the GEOMETRIC `FriProximity` (per accepting transcript) into the
OPERATIONAL `AirSoundness.FriProximity`, under the two explicit hypotheses `hplumb` (Merkle
binding) and `hcode_sat` (codeword ⇒ constraint-satisfying decoded trace). -/

/-- **`friProximity_bridge` — the DEBT-A #3 bridge, PROVED.** For a commitment-indexed FRI setup
`S`, oracle `oracle`, and trace-decoder `traceOf`:
  * `hFRI` : every accepting transcript's oracle is `0`-close to `(S com).C` (the geometric
    `FriProximity`, dischargeable at the deployed field/rate);
  * `hplumb` : the opened trace IS the trace decoded from the committed oracle
    (`openTr com = traceOf (oracle com)` — Merkle binding, `HashCR`/`Poseidon2SpongeCR`);
  * `hcode_sat` : every codeword `g ∈ (S com).C` decodes to a trace satisfying the transition
    constraints (the codeword-side obligation, i.e. `hconstr` of `air_binds_of_proximity`);
then the operational `AirSoundness.FriProximity applyEff verifyLD openTr` holds. The `g` in
`hcode_sat` is LOAD-BEARING (the conclusion is `satisfiesTransition … (traceOf g) …`, not a bare
`openTr`-only statement), so `hFRI` is genuinely used: it identifies the oracle with a codeword. -/
theorem friProximity_bridge
    (applyEff : Effect → State → State)
    (verifyLD : Proof → Commitment → Prop)
    (openTr : Commitment → Step State Effect × List (Step State Effect))
    (S : Commitment → FriSetup F ι κ)
    (oracle : Commitment → (ι → F))
    (traceOf : (ι → F) → Step State Effect × List (Step State Effect))
    (hFRI : ∀ π com, verifyLD π com → FriProximity (S com) 0 (oracle com))
    (hplumb : ∀ com, openTr com = traceOf (oracle com))
    (hcode_sat : ∀ com, ∀ g ∈ (S com).C,
        satisfiesTransition applyEff (traceOf g).1 (traceOf g).2) :
    AirSoundness.FriProximity applyEff verifyLD openTr := by
  intro π com hv
  -- FRI proximity ⇒ a codeword `g` near the oracle carries the codeword-side constraint.
  obtain ⟨g, _hg, hdis, hsat⟩ :=
    air_binds_of_proximity (S com) (hFRI π com hv)
      (fun f => satisfiesTransition applyEff (traceOf f).1 (traceOf f).2)
      (hcode_sat com)
  -- `d = 0`: zero disagreement ⇒ the near codeword IS the committed oracle.
  have hog : oracle com = g :=
    disagree_eq_empty_iff.mp (Finset.card_eq_zero.mp (Nat.le_zero.mp hdis))
  -- transport through the Merkle plumbing: opened trace = decoded oracle = decoded codeword.
  rw [hplumb com, hog]
  exact hsat

/-! ## §2 — Composition to `CircuitSound` (through `circuit_sound_via_fri`). -/

/-- **`circuit_sound_via_bridge` — the full `CircuitSound`, via the bridge.** Composing
`friProximity_bridge` with `AirSoundness.circuit_sound_via_fri`: the AIR-realized checker
`airChecks verifyLD openTr` satisfies `CircuitSound applyEff` under the SAME three explicit
hypotheses. This is the honest through-line: geometric FRI proximity (`hFRI`) + Merkle binding
(`hplumb`) + codeword-side AIR satisfaction (`hcode_sat`) ⇒ every accepted proof forces
`new = applyEff eff old`. -/
theorem circuit_sound_via_bridge
    (applyEff : Effect → State → State)
    (verifyLD : Proof → Commitment → Prop)
    (openTr : Commitment → Step State Effect × List (Step State Effect))
    (S : Commitment → FriSetup F ι κ)
    (oracle : Commitment → (ι → F))
    (traceOf : (ι → F) → Step State Effect × List (Step State Effect))
    (hFRI : ∀ π com, verifyLD π com → FriProximity (S com) 0 (oracle com))
    (hplumb : ∀ com, openTr com = traceOf (oracle com))
    (hcode_sat : ∀ com, ∀ g ∈ (S com).C,
        satisfiesTransition applyEff (traceOf g).1 (traceOf g).2) :
    CircuitSound applyEff (airChecks verifyLD openTr) :=
  circuit_sound_via_fri applyEff verifyLD openTr
    (friProximity_bridge applyEff verifyLD openTr S oracle traceOf hFRI hplumb hcode_sat)

/-! ## §3 — The FRI half at the DEPLOYED BabyBear field + rate `1/8`.

Here `hFRI` is DISCHARGED (not assumed) by `deployedRate_friProximity`: the geometric proximity is
supplied at the deployed field (BabyBear) and deployed rate (`1/8`, `m = 3`, `|L| = 16`), for the
honest codeword oracle. Only `hplumb` (Merkle) and `hcode_sat` (codeword ⇒ trace) remain as explicit
premises. ⚠ This is deployed FIELD + RATE, NOT deployed ARITY — the fold here is 2-to-1; deployed p3
folds 8-to-1 (see the module header). -/

/-- **`deployedRate_circuit_sound` — `CircuitSound` with the FRI half PROVED at the deployed
field/rate.** `S`/`oracle` are the deployed-rate setup and honest codeword; `hFRI` is discharged
outright by `deployedRate_friProximity`. Remaining explicit premises: `hplumb` (Merkle binding) and
`hcode_sat` (the codeword-side AIR obligation). NOT deployed-arity (2-to-1 fold, header caveat). -/
theorem deployedRate_circuit_sound
    (applyEff : Effect → State → State)
    (verifyLD : Proof → Commitment → Prop)
    (openTr : Commitment → Step State Effect × List (Step State Effect))
    (traceOf : (Fin (2 ^ 4) → BabyBear) → Step State Effect × List (Step State Effect))
    (hplumb : ∀ com, openTr com = traceOf (fHonestParam 3 omega16))
    (hcode_sat : ∀ (_com : Commitment), ∀ g ∈ friSetupDeployedRate.C,
        satisfiesTransition applyEff (traceOf g).1 (traceOf g).2) :
    CircuitSound applyEff (airChecks verifyLD openTr) :=
  circuit_sound_via_bridge applyEff verifyLD openTr
    (fun _ => friSetupDeployedRate) (fun _ => fHonestParam 3 omega16) traceOf
    (fun _ _ _ => deployedRate_friProximity) hplumb hcode_sat

#assert_axioms friProximity_bridge
#assert_axioms circuit_sound_via_bridge
#assert_axioms deployedRate_circuit_sound

/-! ## §4 — TEETH (both polarities load-bearing). -/

section Teeth

/-- The toy effect-VM: an additive counter (matches `AirSoundness`'s `toyApply`). -/
def toyApply : ℕ → ℕ → ℕ := fun e s => s + e

/-- An honest constant decoder: every codeword ↦ the honest single row `⟨0,1,1⟩` (`1 = 0 + 1`). -/
def traceHonest : (Fin (2 ^ 4) → BabyBear) → Step ℕ ℕ × List (Step ℕ ℕ) :=
  fun _ => (⟨0, 1, 1⟩, [])

/-- The honest decoder satisfies `hcode_sat`: the honest row satisfies the transition constraints
(step gate `1 = toyApply 1 0`, empty carry) for EVERY codeword. -/
theorem traceHonest_code_sat :
    ∀ (_com : Unit), ∀ g ∈ friSetupDeployedRate.C,
      satisfiesTransition toyApply (traceHonest g).1 (traceHonest g).2 := by
  intro _ g _
  exact ⟨rfl, trivial⟩

/-- **RESPECTING INSTANCE — the bridge FIRES.** With the deployed-rate FRI half, an arbitrary
verifier/commitment plumbing pointing at the honest decoder, and `traceHonest_code_sat`, the
operational `AirSoundness.FriProximity` holds — the honest chain produces the consumed interface. -/
theorem respecting_fires
    (verifyLD : Proof → Unit → Prop)
    (openTr : Unit → Step ℕ ℕ × List (Step ℕ ℕ))
    (hplumb : ∀ com, openTr com = traceHonest (fHonestParam 3 omega16)) :
    AirSoundness.FriProximity toyApply verifyLD openTr :=
  friProximity_bridge toyApply verifyLD openTr
    (fun _ => friSetupDeployedRate) (fun _ => fHonestParam 3 omega16) traceHonest
    (fun _ _ _ => deployedRate_friProximity) hplumb traceHonest_code_sat

/-- …and thence `CircuitSound` fires on the honest instance. -/
theorem respecting_circuit_sound
    (verifyLD : Proof → Unit → Prop)
    (openTr : Unit → Step ℕ ℕ × List (Step ℕ ℕ))
    (hplumb : ∀ com, openTr com = traceHonest (fHonestParam 3 omega16)) :
    CircuitSound toyApply (airChecks verifyLD openTr) :=
  circuit_sound_via_fri toyApply verifyLD openTr (respecting_fires verifyLD openTr hplumb)

/-- A LYING decoder: every codeword ↦ the row `⟨0,1,5⟩` (`5 ≠ 0 + 1`), violating the step gate. -/
def traceLying : (Fin (2 ^ 4) → BabyBear) → Step ℕ ℕ × List (Step ℕ ℕ) :=
  fun _ => (⟨0, 1, 5⟩, [])

/-- **BITING TOOTH — `hcode_sat` is LOAD-BEARING.** The lying decoder does NOT satisfy `hcode_sat`:
at the codeword `0 ∈ (S).C` (`Submodule.zero_mem`) it decodes to `⟨0,1,5⟩`, whose step gate
`5 = toyApply 1 0 = 1` is FALSE. So `hcode_sat` is a genuine obligation — NOT free by unfolding, and
a bridge instance with a lying decoder cannot be assembled. -/
theorem hcode_sat_load_bearing :
    ¬ (∀ (_com : Unit), ∀ g ∈ friSetupDeployedRate.C,
        satisfiesTransition toyApply (traceLying g).1 (traceLying g).2) := by
  intro h
  have hsat := h () 0 (Submodule.zero_mem _)
  -- satisfiesTransition toyApply ⟨0,1,5⟩ [] ⇒ step gate 5 = 0 + 1, impossible.
  obtain ⟨hstep, _⟩ := hsat
  have : (5 : ℕ) = toyApply 1 0 := hstep
  simp [toyApply] at this

end Teeth

#assert_axioms traceHonest_code_sat
#assert_axioms respecting_fires
#assert_axioms respecting_circuit_sound
#assert_axioms hcode_sat_load_bearing

end Dregg2.Circuit.FriProximityBridge
