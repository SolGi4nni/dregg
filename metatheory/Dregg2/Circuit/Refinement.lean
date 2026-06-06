/-
# Dregg2.Circuit.Refinement — the circuit as the bottom of the l4v refinement tower.

The codebase already has a refinement tower over the EXECUTABLE kernel: `Spec.ExecRefinement`
(`Exec ⊑ Spec`), `Proof.Refine`/`Proof.LTS` (`Exec ⊑ Abstract`, the forward-simulation square). This
module adds the CIRCUIT as a new, lowest layer and proves — in the l4v sense — that **the circuit's
algebraic statement is a SOUND AND COMPLETE refinement of the protocol's dynamic behaviour**:

    circuit  ⟺  spec  ⟺  executor          (over (pre-state, turn, post-state) triples)

Refinement here is RELATIONAL (a refinement of step-relations), the natural shape for a circuit whose
acceptance IS a relation on encoded `(k, t, k')` triples — distinct from `ExecRefinement`'s
state-abstraction simulation, and composing on top of it.

The payoff (why refinement is the l4v technique): a safety property proven ONCE on the abstract
declarative `spec` transfers DOWN, for free, to the executable kernel AND to the arithmetic circuit
(`Refines.preserves`). We exhibit this concretely with two-party CONSERVATION: proven on `TransferSpec`,
it governs every circuit-accepted step — the "no value forged" guarantee descends to the algebra.

The circuit⟺spec direction carries exactly the realizable Poseidon collision-resistance portals
(`compressInjective`/`compressNInjective`/`cellLeafInjective`/`RestHashIffFrame`) + the
`AccountsWF` well-formedness invariant (PROVED preserved in `StateCommit`) — NOT the impossible
sum-injectivity that the de-portaling removed. No `sorry`/`admit`/`native_decide`/`axiom`.
-/
import Dregg2.Circuit.StateCommit
import Dregg2.Circuit.Lookup

namespace Dregg2.Circuit.Refinement

open Dregg2.Circuit
open Dregg2.Circuit.Lookup
open Dregg2.Exec
open Dregg2.Circuit.Transfer
open Dregg2.Circuit.StateCommit
open Dregg2.Exec.CircuitEmit

/-! ## §1 — Relational refinement (the framework). -/

/-- A step relation: pre-state, action, post-state. -/
abbrev StepRel (P A Q : Type) := P → A → Q → Prop

/-- **`Refines impl spec`** — forward simulation: every `impl` step is a `spec` step (`impl ⊑ spec`).
The concrete system admits no behaviour the abstract one forbids. -/
def Refines {P A Q : Type} (impl spec : StepRel P A Q) : Prop := ∀ p a q, impl p a q → spec p a q

/-- **`Equiv impl spec`** — mutual refinement: the two relations coincide on every triple. This is the
strong relation a SOUND ∧ COMPLETE arithmetization achieves (soundness = `impl ⊑ spec`, completeness =
`spec ⊑ impl`). -/
def Equiv {P A Q : Type} (impl spec : StepRel P A Q) : Prop := ∀ p a q, impl p a q ↔ spec p a q

theorem Equiv.toRefines {P A Q} {impl spec : StepRel P A Q} (h : Equiv impl spec) :
    Refines impl spec := fun p a q hi => (h p a q).mp hi

theorem Equiv.toRefines' {P A Q} {impl spec : StepRel P A Q} (h : Equiv impl spec) :
    Refines spec impl := fun p a q hs => (h p a q).mpr hs

theorem Refines.trans {P A Q} {r s t : StepRel P A Q}
    (h1 : Refines r s) (h2 : Refines s t) : Refines r t :=
  fun p a q hr => h2 p a q (h1 p a q hr)

theorem Equiv.symm {P A Q} {impl spec : StepRel P A Q} (h : Equiv impl spec) : Equiv spec impl :=
  fun p a q => (h p a q).symm

theorem Equiv.trans {P A Q} {r s t : StepRel P A Q}
    (h1 : Equiv r s) (h2 : Equiv s t) : Equiv r t :=
  fun p a q => (h1 p a q).trans (h2 p a q)

/-- **`Refines.preserves` — THE l4v PAYOFF.** A post-state safety predicate proven on the ABSTRACT
`spec` transfers, for free, to every `impl` step. Prove safety once upstream; it governs every concrete
refinement below. -/
theorem Refines.preserves {P A Q} {impl spec : StepRel P A Q} (h : Refines impl spec)
    {Safe : P → A → Q → Prop} (hsafe : ∀ p a q, spec p a q → Safe p a q) :
    ∀ p a q, impl p a q → Safe p a q :=
  fun p a q hi => hsafe p a q (h p a q hi)

/-! ## §2 — The three layers as step-relations (over `RecordKernelState`/`Turn`). -/

/-- The EXECUTABLE protocol step: the record kernel commits the turn. -/
def execStep : StepRel RecordKernelState Turn RecordKernelState :=
  fun k t k' => recKExec k t = some k'

/-- The ABSTRACT declarative spec step (the independent full-state reference). -/
def specStep : StepRel RecordKernelState Turn RecordKernelState :=
  fun k t k' => TransferSpec k t k'

section Circuit
variable (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ) (cmb : ℤ → ℤ → ℤ)
  (compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)

/-- The CIRCUIT step: the full-state arithmetization is satisfied on the encoded triple. -/
abbrev circuitStep : StepRel RecordKernelState Turn RecordKernelState :=
  fun k t k' => satisfiedS cmb compress (encodeS CH RH cmb compress compressN k t k')

/-! ## §3 — The refinements (PROVED). -/

/-- **`exec_equiv_spec` — the EXECUTABLE kernel and the abstract spec coincide** (l4v data refinement,
both directions): `recKExec_iff_spec`. The executor admits exactly the spec'd transitions. -/
theorem exec_equiv_spec : Equiv execStep specStep :=
  fun k t k' => recKExec_iff_spec k t k'

/-- **`circuit_refines_spec` — SOUNDNESS as refinement.** Every WELL-FORMED circuit-accepted step is a
spec step: the algebraic statement admits no behaviour the protocol forbids (`circuit ⊑ spec`). Carries
the realizable Poseidon-CR portals + `AccountsWF` on the two endpoints (the reachable-state invariant
`StateCommit` proves preserved). -/
theorem circuit_refines_spec
    (hCompress : compressInjective compress) (hCompressN : compressNInjective compressN)
    (hLeaf : cellLeafInjective CH) (hRest : RestHashIffFrame RH) :
    Refines
      (fun k t k' => AccountsWF k ∧ AccountsWF k' ∧ circuitStep CH RH cmb compress compressN k t k')
      specStep :=
  fun k t k' h =>
    transfer_circuit_full_sound CH RH cmb compress compressN
      hCompress hCompressN hLeaf hRest k t k' h.1 h.2.1 h.2.2

/-- **`spec_refines_circuit` — COMPLETENESS as refinement.** Every spec step is circuit-accepted: all
protocol-acceptable behaviours are circuit-acceptable (`spec ⊑ circuit`). Needs only the rest-hash
characterization (completeness builds the digests; it never inverts a hash). -/
theorem spec_refines_circuit (hRest : RestHashIffFrame RH) :
    Refines specStep (circuitStep CH RH cmb compress compressN) :=
  fun k t k' h => transfer_circuit_full_complete CH RH cmb compress compressN hRest k t k' h

/-- **`circuit_refines_exec` — the headline.** Composing soundness with `spec ⟺ executor`: every
well-formed circuit-accepted step is a genuine EXECUTABLE protocol step. The circuit's algebraic
statement is a sound refinement of the dynamic behaviour the kernel actually runs. -/
theorem circuit_refines_exec
    (hCompress : compressInjective compress) (hCompressN : compressNInjective compressN)
    (hLeaf : cellLeafInjective CH) (hRest : RestHashIffFrame RH) :
    Refines
      (fun k t k' => AccountsWF k ∧ AccountsWF k' ∧ circuitStep CH RH cmb compress compressN k t k')
      execStep :=
  Refines.trans (circuit_refines_spec CH RH cmb compress compressN hCompress hCompressN hLeaf hRest)
    exec_equiv_spec.toRefines'

/-! ## §4 — The payoff: CONSERVATION proven on the spec governs the circuit. -/

/-- Two-party conservation: the moved cells' post-balances sum to their pre-balances (no value forged
or destroyed across the transfer). A safety predicate on the `(pre, post)` pair. -/
def Conserves (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) : Prop :=
  balOf (k'.cell t.src) + balOf (k'.cell t.dst) = balOf (k.cell t.src) + balOf (k.cell t.dst)

/-- Conservation holds of every SPEC step — proved once, upstream, from `recTransfer_correct`
(debit ∧ credit). -/
theorem specStep_conserves : ∀ k t k', specStep k t k' → Conserves k t k' := by
  intro k t k' h
  obtain ⟨hg, hcell, _⟩ := h
  obtain ⟨_, _, _, hne, _, _⟩ := hg
  obtain ⟨hdeb, hcre, _⟩ := recTransfer_correct k.cell t.src t.dst t.amt hne
  unfold Conserves
  rw [hcell, hdeb, hcre]; ring

/-- **`circuit_conserves` — the descent.** Conservation, proven on the abstract spec, governs EVERY
well-formed circuit-accepted step (via `circuit_refines_spec` + `Refines.preserves`). The "no value
forged" guarantee descends from the declarative spec all the way to the arithmetic circuit — for free,
by refinement. This is the l4v technique paying off on the crown-jewel circuit. -/
theorem circuit_conserves
    (hCompress : compressInjective compress) (hCompressN : compressNInjective compressN)
    (hLeaf : cellLeafInjective CH) (hRest : RestHashIffFrame RH)
    (k : RecordKernelState) (t : Turn) (k' : RecordKernelState)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hsat : circuitStep CH RH cmb compress compressN k t k') :
    Conserves k t k' :=
  (circuit_refines_spec CH RH cmb compress compressN hCompress hCompressN hLeaf hRest).preserves
    specStep_conserves k t k' ⟨hwf, hwf', hsat⟩

/-! ## §5 — Emitted wire form: the polynomial gates the Rust prover checks. -/

/-- The EMITTED polynomial step (the 12 gates `lean_descriptor_air` enforces — no `StateCommitSat`). -/
abbrev emittedArithStep : StepRel RecordKernelState Turn RecordKernelState :=
  fun k t k' => satisfiedEmitted emittedState (encodeS CH RH cmb compress compressN k t k')

/-- **`emitted_equiv_arith`** — the emitted wire form denotes EXACTLY `satisfied stateCircuit` on the
encoded witness. The Plonky3 prover checks this polynomial layer; `StateCommitSat` is the witness-
generator's root-binding obligation (opaque hash algebra, discharged by CR portals). -/
theorem emitted_equiv_arith (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    emittedArithStep CH RH cmb compress compressN k t k'
      ↔ satisfied stateCircuit (encodeS CH RH cmb compress compressN k t k') := by
  unfold emittedArithStep
  exact (emitStateFaithful (encodeS CH RH cmb compress compressN k t k')).symm

/-- Every full `circuitStep` implies the emitted polynomial step (the root-binding conjunct is extra). -/
theorem circuitStep_implies_emitted (k : RecordKernelState) (t : Turn) (k' : RecordKernelState)
    (h : circuitStep CH RH cmb compress compressN k t k') :
    emittedArithStep CH RH cmb compress compressN k t k' := by
  unfold circuitStep satisfiedS at h
  obtain ⟨hsc, _⟩ := h
  exact (emitted_equiv_arith CH RH cmb compress compressN k t k').mpr hsc

/-! ## §6 — Field-sound `CircuitL` layer: lookups refine the polynomial gates. -/

/-- Balance-wire range checks bundled with `stateCircuit` (the semantic `CircuitL` form). -/
def stateCircuitL : CircuitL :=
  { gates := stateCircuit
  , lookups := stateRanges.map (fun r => rangeCheck (.var r.wire) r.bits) }

/-- The field-sound full-state step: `stateCircuit` gates PLUS balance-wire range lookups. -/
abbrev circuitLArithStep : StepRel RecordKernelState Turn RecordKernelState :=
  fun k t k' =>
    stateCircuitL.satisfied (encodeS CH RH cmb compress compressN k t k')

/-- **`circuitL_refines_arith`** — range lookups RESTRICT witnesses: every `CircuitL` step satisfies
the bare polynomial gates. No field-wraparound forgeries pass the lookup layer. -/
theorem circuitL_refines_arith (k : RecordKernelState) (t : Turn) (k' : RecordKernelState)
    (h : circuitLArithStep CH RH cmb compress compressN k t k') :
    satisfied stateCircuit (encodeS CH RH cmb compress compressN k t k') := by
  unfold circuitLArithStep stateCircuitL CircuitL.satisfied at h
  obtain ⟨hgates, _⟩ := h
  exact hgates

/-- **`circuitLArith_refines_emitted`** — the lookup layer refines through to the emitted wire form. -/
theorem circuitLArith_refines_emitted (k : RecordKernelState) (t : Turn) (k' : RecordKernelState)
    (h : circuitLArithStep CH RH cmb compress compressN k t k') :
    emittedArithStep CH RH cmb compress compressN k t k' := by
  exact (emitted_equiv_arith CH RH cmb compress compressN k t k').mpr
    (circuitL_refines_arith CH RH cmb compress compressN k t k' h)

/-- **`circuitL_refines_spec`** — field-sound polynomial satisfaction + well-formedness ⇒ spec step.
Needs `StateCommitSat` separately for the full `circuitStep` soundness theorem. -/
theorem circuitL_refines_spec
    (hCompress : compressInjective compress) (hCompressN : compressNInjective compressN)
    (hLeaf : cellLeafInjective CH) (hRest : RestHashIffFrame RH) :
    Refines
      (fun k t k' => AccountsWF k ∧ AccountsWF k' ∧
        circuitLArithStep CH RH cmb compress compressN k t k' ∧
        StateCommitSat cmb compress (encodeS CH RH cmb compress compressN k t k'))
      specStep :=
  fun k t k' ⟨hwf, hwf', hL, hroot⟩ =>
    circuit_refines_spec CH RH cmb compress compressN hCompress hCompressN hLeaf hRest k t k'
      ⟨hwf, hwf', ⟨circuitL_refines_arith CH RH cmb compress compressN k t k' hL, hroot⟩⟩

end Circuit

/-! ## §7 — Axiom-hygiene tripwires. -/

#assert_axioms exec_equiv_spec
#assert_axioms circuit_refines_spec
#assert_axioms spec_refines_circuit
#assert_axioms circuit_refines_exec
#assert_axioms specStep_conserves
#assert_axioms circuit_conserves
#assert_axioms emitted_equiv_arith
#assert_axioms circuitStep_implies_emitted
#assert_axioms circuitL_refines_arith
#assert_axioms circuitLArith_refines_emitted
#assert_axioms circuitL_refines_spec

end Dregg2.Circuit.Refinement
