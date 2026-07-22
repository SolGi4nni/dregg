/-
# Dregg2.Logic.ProofFheSharedOpening -- one checked opening, two backends

This module closes a concrete proof/FHE coherence triangle for the bounded
Boolean source shared by `FiniteLogicDescriptorIR2` and the executable BFV
model.  A `TypedSource n` carries the atom-bound proof.  An `Opening n` carries
one raw integer for each source atom.  The proof descriptor reads those raw
integers, while the FHE program reads the Boolean decoding of exactly the same
opening.

The boundary is fail-closed: an opening is admitted only when every raw value
is exactly zero or one.  On that canonical domain, the live descriptor
polynomial and the Boolean-ring FHE evaluation are the same ring element, and
the live proof relation accepts exactly when the FHE result is one.  Outside
that domain both sides reject; no reduction modulo the field is used to turn a
noncanonical integer into a Boolean.

This is a theorem-level common-input bridge.  It does not claim that ciphertext
serialization or the Rust BFV implementation refines `Opening`, and it does
not add an FHE security, noise, or timing theorem.

Pure.  No axioms.
-/

import Dregg2.Logic.FiniteLogicDescriptorIR2
import Dregg2.Logic.FheLogicBfvModel
import Dregg2.Tactics

namespace Dregg2.Logic.ProofFheSharedOpening

set_option autoImplicit false

namespace Proof

open Dregg2.Logic.FiniteLogicDescriptorIR2

abbrev Source := Cert.Source
abbrev eval := Cert.eval
abbrev atomsBelow := Dregg2.Logic.FiniteLogicDescriptorIR2.atomsBelow
abbrev sourcePoly := Dregg2.Logic.FiniteLogicDescriptorIR2.sourcePoly
abbrev bitInt := Dregg2.Logic.FiniteLogicDescriptorIR2.bitInt
abbrev rowOf := Dregg2.Logic.FiniteLogicDescriptorIR2.rowOf
abbrev traceOf := Dregg2.Logic.FiniteLogicDescriptorIR2.traceOf
abbrev CanonicalLogicSatisfied2 :=
  Dregg2.Logic.FiniteLogicDescriptorIR2.CanonicalLogicSatisfied2

end Proof

namespace Fhe

abbrev Program := Dregg2.Logic.FheLogicBfvModel.BooleanProgram

end Fhe

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (VmTrace envAt zeroAsg)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Logic.FiniteLogicDescriptorIR2
open Dregg2.Logic.FheLogicBfvModel

/-! ## 1. A shared typed source and raw opening -/

/-- A source whose every atom is represented in an `n`-slot opening. -/
structure TypedSource (n : Nat) where
  formula : Proof.Source
  bounded : Proof.atomsBelow n formula = true

/-- The common raw input to proof and FHE compilation.  `Fin n` prevents a
missing or surplus named slot from being smuggled through this typed boundary. -/
structure Opening (n : Nat) where
  word : Fin n -> Int

/-- The admitted domain is deliberately integer-exact, not equality modulo the
BabyBear modulus. -/
def Opening.Canonical {n : Nat} (opening : Opening n) : Prop :=
  forall slot, opening.word slot = 0 \/ opening.word slot = 1

/-- Boolean view of the raw opening.  Names outside the typed source boundary
are false; `TypedSource.bounded` proves that compiled programs never read them. -/
def Opening.boolEnv {n : Nat} (opening : Opening n) (name : Nat) : Bool :=
  if hname : name < n then decide (opening.word (Fin.mk name hname) = 1) else false

/-- Raw proof assignment.  Unlike `boolEnv`, this does not coerce a malformed
word to a bit; the proof descriptor sees the original integer. -/
def Opening.assignment {n : Nat} (opening : Opening n) : Assignment :=
  fun name => if hname : name < n then opening.word <| Fin.mk name hname else 0

/-- The actual one-row proof trace built from the raw common opening. -/
def Opening.proofTrace {n : Nat} (opening : Opening n) : VmTrace :=
  { rows := [opening.assignment], pub := zeroAsg, tf := fun _ => [] }

instance {n : Nat} (opening : Opening n) : Decidable opening.Canonical := by
  unfold Opening.Canonical
  infer_instance

/-- Fail-closed admission for an FHE consumer. -/
def Opening.decode? {n : Nat} (opening : Opening n) : Option (Nat -> Bool) :=
  if opening.Canonical then some opening.boolEnv else none

theorem Opening.decode?_eq_none_iff {n : Nat} (opening : Opening n) :
    opening.decode? = none <-> Not opening.Canonical := by
  simp [Opening.decode?]

theorem Opening.decode?_eq_some_iff {n : Nat} (opening : Opening n)
    (env : Nat -> Bool) :
    opening.decode? = some env <->
      opening.Canonical /\ env = opening.boolEnv := by
  by_cases hcanonical : opening.Canonical
  · simp [Opening.decode?, hcanonical, eq_comm]
  · simp [Opening.decode?, hcanonical]

/-- On the admitted domain, the raw proof row is exactly the integer encoding
of the FHE Boolean environment. -/
theorem Opening.assignment_eq_rowOf {n : Nat} (opening : Opening n)
    (hcanonical : opening.Canonical) :
    opening.assignment = Proof.rowOf opening.boolEnv := by
  funext name
  by_cases hname : name < n
  · rcases hcanonical (Fin.mk name hname) with hzero | hone
    · simp [Opening.assignment, Opening.boolEnv,
        Dregg2.Logic.FiniteLogicDescriptorIR2.rowOf,
        Dregg2.Logic.FiniteLogicDescriptorIR2.bitInt, hname, hzero]
    · simp [Opening.assignment, Opening.boolEnv,
        Dregg2.Logic.FiniteLogicDescriptorIR2.rowOf,
        Dregg2.Logic.FiniteLogicDescriptorIR2.bitInt, hname, hone]
  · simp [Opening.assignment, Opening.boolEnv,
      Dregg2.Logic.FiniteLogicDescriptorIR2.rowOf,
      Dregg2.Logic.FiniteLogicDescriptorIR2.bitInt, hname]

theorem Opening.proofTrace_eq_traceOf {n : Nat} (opening : Opening n)
    (hcanonical : opening.Canonical) :
    opening.proofTrace = Proof.traceOf opening.boolEnv := by
  simp [Opening.proofTrace,
    Dregg2.Logic.FiniteLogicDescriptorIR2.traceOf,
    Opening.assignment_eq_rowOf opening hcanonical]

/-! ## 2. One structural lowering to the BFV Boolean program -/

def lowerFhe : Proof.Source -> Fhe.Program
  | .atom name => .input name
  | .top => .constant true
  | .bot => .constant false
  | .not formula => .not (lowerFhe formula)
  | .and left right => .and (lowerFhe left) (lowerFhe right)
  | .or left right => .or (lowerFhe left) (lowerFhe right)

theorem lowerFhe_evalBool (env : Nat -> Bool) (source : Proof.Source) :
    (lowerFhe source).evalBool env = Proof.eval env source := by
  induction source <;>
    simp [lowerFhe, FheLogicBfvModel.BooleanProgram.evalBool,
      Proof.eval, Dregg2.Logic.CompilationCertificateBundle.Source.eval, *]

/-! ## 3. Exact descriptor/FHE denotation coherence -/

/-- The live descriptor polynomial, evaluated on the raw proof trace and then
cast to any commutative ring, equals the BFV Boolean-ring evaluation over the
same canonical opening. -/
theorem descriptorDenotation_eq_fheRing {R : Type*} [CommRing R]
    {n : Nat} (source : TypedSource n) (opening : Opening n)
    (hcanonical : opening.Canonical) :
    ((Proof.sourcePoly source.formula).eval
        (envAt opening.proofTrace 0) : R) =
      (lowerFhe source.formula).evalRing (R := R) opening.boolEnv := by
  rw [opening.proofTrace_eq_traceOf hcanonical]
  rw [sourcePoly_eval_rowOf n source.formula opening.boolEnv source.bounded]
  rw [BooleanProgram.evalRing_correct, lowerFhe_evalBool]
  cases heval : Proof.eval opening.boolEnv source.formula <;>
    simp [Dregg2.Logic.FiniteLogicDescriptorIR2.bitInt,
      Dregg2.Logic.FheLogicBfvModel.encodeBool, heval]

/-! ## 4. The same-opening acceptance theorem -/

/-- One shared source/opening package. -/
structure Instance (n : Nat) where
  source : TypedSource n
  opening : Opening n

/-- The proof-side relation uses the raw opening trace.  Canonicality is part of
the relation rather than an ambient convention. -/
def ProofAccepts {n : Nat} (input : Instance n) : Prop :=
  input.opening.Canonical /\
    Proof.CanonicalLogicSatisfied2 (fun _ => 0) n input.source.formula
      (fun _ => 0) (fun _ => ((0 : Int), 0)) [] input.opening.proofTrace

/-- The FHE-side observation.  A noncanonical opening has no ciphertext-level
meaning in this bridge and therefore returns `none` before ring evaluation. -/
def fheOutput? {n : Nat} (input : Instance n) : Option (ZMod 2013265921) :=
  match input.opening.decode? with
  | some env => some ((lowerFhe input.source.formula).evalRing
      (R := ZMod 2013265921) env)
  | none => none

theorem proofAccepts_iff_sourceTrue {n : Nat} (input : Instance n) :
    ProofAccepts input <->
      input.opening.Canonical /\
        Proof.eval input.opening.boolEnv input.source.formula = true := by
  constructor
  · rintro ⟨hcanonical, hsat⟩
    have htrace := input.opening.proofTrace_eq_traceOf hcanonical
    have hsat' :
        Proof.CanonicalLogicSatisfied2 (fun _ => 0) n input.source.formula
          (fun _ => 0) (fun _ => ((0 : Int), 0)) []
          (Proof.traceOf input.opening.boolEnv) := by
      simpa [htrace] using hsat
    exact ⟨hcanonical,
      (canonical_trace_iff (fun _ => 0) n input.source.formula
        input.opening.boolEnv input.source.bounded).mp hsat'⟩
  · rintro ⟨hcanonical, htrue⟩
    refine ⟨hcanonical, ?_⟩
    rw [input.opening.proofTrace_eq_traceOf hcanonical]
    exact source_complete (fun _ => 0) n input.source.formula
      input.opening.boolEnv input.source.bounded htrue

theorem fheOutput?_eq_some_one_iff {n : Nat} (input : Instance n) :
    fheOutput? input = some 1 <->
      input.opening.Canonical /\
        Proof.eval input.opening.boolEnv input.source.formula = true := by
  by_cases hcanonical : input.opening.Canonical
  · simp only [fheOutput?, Opening.decode?, hcanonical, if_true,
      Option.some.injEq, true_and]
    rw [BooleanProgram.evalRing_correct, lowerFhe_evalBool]
    cases heval : Proof.eval input.opening.boolEnv input.source.formula <;>
      norm_num [Dregg2.Logic.FheLogicBfvModel.encodeBool, heval]
  · simp [fheOutput?, Opening.decode?, hcanonical]

/-- A proof and a BFV evaluation over the shared canonical opening accept
exactly the same instances. -/
theorem proofAccepts_iff_fheOutput_one {n : Nat} (input : Instance n) :
    ProofAccepts input <-> fheOutput? input = some 1 := by
  rw [proofAccepts_iff_sourceTrue, fheOutput?_eq_some_one_iff]

/-- Exact FHE boundary: `none` means precisely that some raw word was not an
integer bit. -/
theorem fheOutput?_eq_none_iff {n : Nat} (input : Instance n) :
    fheOutput? input = none <-> Not input.opening.Canonical := by
  by_cases hcanonical : input.opening.Canonical <;>
    simp [fheOutput?, Opening.decode?, hcanonical]

/-- Exact joint reject boundary.  The proof relation cannot accept and the FHE
compiler produces no value for every noncanonical shared opening. -/
theorem noncanonical_rejected {n : Nat} (input : Instance n)
    (hnoncanonical : Not input.opening.Canonical) :
    Not (ProofAccepts input) /\ fheOutput? input = none := by
  constructor
  · intro haccept
    exact hnoncanonical haccept.1
  · exact (fheOutput?_eq_none_iff input).2 hnoncanonical

/-! ## 5. Nontrivial accepted and rejected examples -/

/-- `a0 and (not a1 or a2)`, sharing every connective with the live demo. -/
def demoSource : TypedSource 3 :=
  { formula := .and (.atom 0) (.or (.not (.atom 1)) (.atom 2))
  , bounded := by decide }

def demoOpening : Opening 3 :=
  { word := fun slot => if slot = 0 then 1 else 0 }

def demoInstance : Instance 3 := { source := demoSource, opening := demoOpening }

theorem demoOpening_canonical : demoOpening.Canonical := by decide

theorem demo_source_true :
    Proof.eval demoOpening.boolEnv demoSource.formula = true := by decide

theorem demo_proof_accepts : ProofAccepts demoInstance := by
  exact (proofAccepts_iff_sourceTrue demoInstance).2
    ⟨demoOpening_canonical, demo_source_true⟩

theorem demo_fhe_output : fheOutput? demoInstance = some 1 := by
  exact (proofAccepts_iff_fheOutput_one demoInstance).mp demo_proof_accepts

/-- Slot one contains `2`: the shared boundary rejects it rather than silently
decoding it as false or reducing it modulo the proof field. -/
def noncanonicalOpening : Opening 3 :=
  { word := fun slot => if slot = 1 then 2 else if slot = 0 then 1 else 0 }

def noncanonicalInstance : Instance 3 :=
  { source := demoSource, opening := noncanonicalOpening }

theorem noncanonicalOpening_not_canonical :
    Not noncanonicalOpening.Canonical := by decide

theorem noncanonical_example_rejected :
    Not (ProofAccepts noncanonicalInstance) /\
      fheOutput? noncanonicalInstance = none := by
  exact noncanonical_rejected noncanonicalInstance
    noncanonicalOpening_not_canonical

#assert_all_clean [
  Opening.decode?_eq_none_iff,
  Opening.decode?_eq_some_iff,
  Opening.assignment_eq_rowOf,
  Opening.proofTrace_eq_traceOf,
  lowerFhe_evalBool,
  descriptorDenotation_eq_fheRing,
  proofAccepts_iff_sourceTrue,
  fheOutput?_eq_some_one_iff,
  proofAccepts_iff_fheOutput_one,
  fheOutput?_eq_none_iff,
  noncanonical_rejected,
  demoOpening_canonical,
  demo_source_true,
  demo_proof_accepts,
  demo_fhe_output,
  noncanonicalOpening_not_canonical,
  noncanonical_example_rejected
]

end Dregg2.Logic.ProofFheSharedOpening
