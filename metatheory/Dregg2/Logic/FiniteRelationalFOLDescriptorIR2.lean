/-
# Dregg2.Logic.FiniteRelationalFOLDescriptorIR2

An end-to-end, kernel-checked compiler for a genuine finite first-order
language into the live `EffectVmDescriptor2` relation.

The source is first-order logic over a public finite domain.  It has constants,
de Bruijn variables, equality, one arbitrary binary relation supplied by the
model, all Boolean connectives, and exhaustive universal and existential
quantification.  A model is a Boolean table of exactly `q * q` relation bits.

Compilation grounds the finite quantifiers and statically evaluates terms,
then lowers the resulting Boolean formula through
`FiniteLogicDescriptorIR2`.  Consequently:

* every relation-table entry is constrained Boolean by the live descriptor;
* every quantifier ranges over all `q` elements, never a witness-selected
  subset;
* the final always-on window gate fires even on the one-row honest trace;
* soundness and completeness compose with the actual `Satisfied2` semantics;
* a fail-closed certificate reconstructs both the grounded source and the exact
  emitted IR-v2 JSON bytes.

The construction is intentionally relational: it does not yet contain
function symbols, multiple relation symbols, free individual inputs, or a
succinct quantifier protocol.  None of those omissions weakens the theorem for
the language defined here.
-/

import Dregg2.Logic.FiniteLogicDescriptorIR2

namespace Dregg2.Logic.FiniteRelationalFOLDescriptorIR2

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Logic.FiniteLogicDescriptorIR2

namespace Live

abbrev Source := Dregg2.Logic.FiniteLogicDescriptorIR2.Cert.Source
abbrev eval := Dregg2.Logic.FiniteLogicDescriptorIR2.Cert.eval

end Live

set_option autoImplicit false

/-! ## 1. Finite relational first-order syntax and semantics -/

/-- Terms in a one-sorted finite relational language.  Since the signature is
relational, terms are precisely bound variables and domain constants. -/
inductive Term (q : Nat) (bound : Nat) where
  | var (index : Fin bound)
  | const (value : Fin q)
  deriving Repr, DecidableEq

namespace Term

/-- Extensional semantics of relational terms. -/
def eval {q bound : Nat} (boundEnv : Fin bound -> Fin q) : Term q bound -> Fin q
  | .var index => boundEnv index
  | .const value => value

end Term

/-- A finite structure for one binary relation.  The table has exactly one bit
for every ordered pair in the `q`-element domain. -/
structure Model (q : Nat) where
  relationBits : Fin (q * q) -> Bool

/-- Row-major index of an ordered pair in the relation table. -/
def edgeIndex {q : Nat} (x y : Fin q) : Fin (q * q) :=
  ⟨x.val * q + y.val, by
    have hx : x.val + 1 <= q := Nat.succ_le_iff.mpr x.isLt
    have hy : y.val < q := y.isLt
    nlinarith⟩

/-- The binary relation denoted by a model. -/
def Model.rel {q : Nat} (model : Model q) (x y : Fin q) : Bool :=
  model.relationBits (edgeIndex x y)

/-- Closed formulas may temporarily contain `bound` de Bruijn variables while
recursing below quantifiers. -/
inductive Formula (q : Nat) : Nat -> Type where
  | top {bound : Nat} : Formula q bound
  | bottom {bound : Nat} : Formula q bound
  | equal {bound : Nat} (left right : Term q bound) : Formula q bound
  | rel {bound : Nat} (left right : Term q bound) : Formula q bound
  | not {bound : Nat} (p : Formula q bound) : Formula q bound
  | and {bound : Nat} (p r : Formula q bound) : Formula q bound
  | or {bound : Nat} (p r : Formula q bound) : Formula q bound
  | imp {bound : Nat} (p r : Formula q bound) : Formula q bound
  | forall_ {bound : Nat} (body : Formula q (bound + 1)) : Formula q bound
  | exists_ {bound : Nat} (body : Formula q (bound + 1)) : Formula q bound
  deriving Repr, DecidableEq

namespace Formula

/-- Direct Boolean model semantics.  Quantifiers enumerate the complete finite
domain in the canonical `List.ofFn` order. -/
def eval {q bound : Nat} (model : Model q) (boundEnv : Fin bound -> Fin q) :
    Formula q bound -> Bool
  | .top => true
  | .bottom => false
  | .equal left right => decide (left.eval boundEnv = right.eval boundEnv)
  | .rel left right => model.rel (left.eval boundEnv) (right.eval boundEnv)
  | .not p => !(eval model boundEnv p)
  | .and p r => eval model boundEnv p && eval model boundEnv r
  | .or p r => eval model boundEnv p || eval model boundEnv r
  | .imp p r => !(eval model boundEnv p) || eval model boundEnv r
  | .forall_ body =>
      (List.ofFn (fun x : Fin q => eval model (Fin.cases x boundEnv) body)).all id
  | .exists_ body =>
      (List.ofFn (fun x : Fin q => eval model (Fin.cases x boundEnv) body)).any id

end Formula

/-! ## 2. Grounding into the existing live Boolean source -/

def allSources : List Live.Source -> Live.Source
  | [] => .top
  | p :: ps => .and p (allSources ps)

def anySources : List Live.Source -> Live.Source
  | [] => .bot
  | p :: ps => .or p (anySources ps)

theorem eval_allSources (atomEnv : Nat -> Bool) (sources : List Live.Source) :
    Live.eval atomEnv (allSources sources) = sources.all (Live.eval atomEnv) := by
  induction sources with
  | nil => rfl
  | cons p ps ih =>
      simp [allSources,
        Dregg2.Logic.CompilationCertificateBundle.Source.eval, ih]

theorem eval_anySources (atomEnv : Nat -> Bool) (sources : List Live.Source) :
    Live.eval atomEnv (anySources sources) = sources.any (Live.eval atomEnv) := by
  induction sources with
  | nil => rfl
  | cons p ps ih =>
      simp [anySources,
        Dregg2.Logic.CompilationCertificateBundle.Source.eval, ih]

/-- Source evaluation depends only on the atom columns proved to occur. -/
theorem eval_congr_of_atomsBelow {atomCount : Nat} {source : Live.Source}
    (hbound : atomsBelow atomCount source = true)
    {left right : Nat -> Bool}
    (hagrees : forall name, name < atomCount -> left name = right name) :
    Live.eval left source = Live.eval right source := by
  induction source with
  | atom name =>
      have hname : name < atomCount := by simpa [atomsBelow] using hbound
      exact hagrees name hname
  | top => rfl
  | bot => rfl
  | not p ih =>
      have hp : atomsBelow atomCount p = true := by simpa [atomsBelow] using hbound
      simp [Dregg2.Logic.CompilationCertificateBundle.Source.eval, ih hp]
  | and p r ihp ihr =>
      have hb : atomsBelow atomCount p = true /\ atomsBelow atomCount r = true := by
        simpa [atomsBelow] using hbound
      simp [Dregg2.Logic.CompilationCertificateBundle.Source.eval, ihp hb.1, ihr hb.2]
  | or p r ihp ihr =>
      have hb : atomsBelow atomCount p = true /\ atomsBelow atomCount r = true := by
        simpa [atomsBelow] using hbound
      simp [Dregg2.Logic.CompilationCertificateBundle.Source.eval, ihp hb.1, ihr hb.2]

/-- Equality of two statically grounded relational terms. -/
def lowerEqual {q bound : Nat} (boundEnv : Fin bound -> Fin q)
    (left right : Term q bound) : Live.Source :=
  if left.eval boundEnv = right.eval boundEnv then .top else .bot

/-- Ground all finite first-order variables and compile relation applications
to their row-major model-table input columns. -/
def lower {q bound : Nat} : Formula q bound -> (Fin bound -> Fin q) -> Live.Source
  | .top, _ => .top
  | .bottom, _ => .bot
  | .equal left right, env => lowerEqual env left right
  | .rel left right, env => .atom (edgeIndex (left.eval env) (right.eval env)).val
  | .not p, env => .not (lower p env)
  | .and p r, env => .and (lower p env) (lower r env)
  | .or p r, env => .or (lower p env) (lower r env)
  | .imp p r, env => .or (.not (lower p env)) (lower r env)
  | .forall_ body, env =>
      allSources (List.ofFn (fun x : Fin q => lower body (Fin.cases x env)))
  | .exists_ body, env =>
      anySources (List.ofFn (fun x : Fin q => lower body (Fin.cases x env)))

/-- Canonical atom environment for the model's exact finite relation table.
Out-of-range columns are false, although a compiled sentence never reads them. -/
def atomEnv {q : Nat} (model : Model q) (name : Nat) : Bool :=
  if h : name < q * q then model.relationBits ⟨name, h⟩ else false

@[simp] theorem atomEnv_edgeIndex {q : Nat} (model : Model q) (x y : Fin q) :
    atomEnv model (edgeIndex x y).val = model.rel x y := by
  rw [atomEnv]
  simp only [dif_pos (edgeIndex x y).isLt]
  rfl

/-- The grounding compiler preserves the direct finite-model semantics. -/
theorem lower_correct {q bound : Nat} (model : Model q)
    (formula : Formula q bound) (boundEnv : Fin bound -> Fin q) :
    Live.eval (atomEnv model) (lower formula boundEnv) =
      formula.eval model boundEnv := by
  induction formula with
  | top => rfl
  | bottom => rfl
  | equal left right =>
      by_cases h : left.eval boundEnv = right.eval boundEnv <;>
        simp [lower, lowerEqual, Formula.eval, h,
          Dregg2.Logic.CompilationCertificateBundle.Source.eval]
  | rel left right =>
      simp [lower, Formula.eval,
        Dregg2.Logic.CompilationCertificateBundle.Source.eval]
  | not p ih =>
      simp [lower, Formula.eval,
        Dregg2.Logic.CompilationCertificateBundle.Source.eval, ih]
  | and p r ihp ihr =>
      simp [lower, Formula.eval,
        Dregg2.Logic.CompilationCertificateBundle.Source.eval, ihp, ihr]
  | or p r ihp ihr =>
      simp [lower, Formula.eval,
        Dregg2.Logic.CompilationCertificateBundle.Source.eval, ihp, ihr]
  | imp p r ihp ihr =>
      simp [lower, Formula.eval,
        Dregg2.Logic.CompilationCertificateBundle.Source.eval, ihp, ihr]
  | forall_ body ih =>
      rw [lower, eval_allSources, Formula.eval]
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true]
      constructor
      · intro h value hvalue
        obtain ⟨x, rfl⟩ := List.mem_ofFn.mp hvalue
        rw [← ih (Fin.cases x boundEnv)]
        exact h _ (List.mem_ofFn.mpr ⟨x, rfl⟩)
      · intro h source hsource
        obtain ⟨x, rfl⟩ := List.mem_ofFn.mp hsource
        rw [ih (Fin.cases x boundEnv)]
        exact h _ (List.mem_ofFn.mpr ⟨x, rfl⟩)
  | exists_ body ih =>
      rw [lower, eval_anySources, Formula.eval]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨source, hsource, hs⟩
        obtain ⟨x, rfl⟩ := List.mem_ofFn.mp hsource
        refine ⟨Formula.eval model (Fin.cases x boundEnv) body,
          List.mem_ofFn.mpr ⟨x, rfl⟩, ?_⟩
        simpa [ih (Fin.cases x boundEnv)] using hs
      · rintro ⟨value, hvalue, hv⟩
        obtain ⟨x, rfl⟩ := List.mem_ofFn.mp hvalue
        refine ⟨lower body (Fin.cases x boundEnv),
          List.mem_ofFn.mpr ⟨x, rfl⟩, ?_⟩
        simpa [ih (Fin.cases x boundEnv)] using hv

/-! ## 3. Bounds and compilation to the live descriptor -/

theorem edgeIndex_lt_square {q : Nat} (x y : Fin q) :
    (edgeIndex x y).val < q * q := (edgeIndex x y).isLt

theorem atomsBelow_allSources {atomCount : Nat} (sources : List Live.Source)
    (h : forall source, source ∈ sources -> atomsBelow atomCount source = true) :
    atomsBelow atomCount (allSources sources) = true := by
  induction sources with
  | nil => rfl
  | cons p ps ih =>
      simp [allSources, atomsBelow, h p (by simp),
        ih (fun source hs => h source (by simp [hs]))]

theorem atomsBelow_anySources {atomCount : Nat} (sources : List Live.Source)
    (h : forall source, source ∈ sources -> atomsBelow atomCount source = true) :
    atomsBelow atomCount (anySources sources) = true := by
  induction sources with
  | nil => rfl
  | cons p ps ih =>
      simp [anySources, atomsBelow, h p (by simp),
        ih (fun source hs => h source (by simp [hs]))]

/-- Every atom emitted by grounding lies inside the exact `q*q` relation-table
width. -/
theorem lower_atomsBelow {q bound : Nat} (formula : Formula q bound)
    (boundEnv : Fin bound -> Fin q) :
    atomsBelow (q * q) (lower formula boundEnv) = true := by
  induction formula with
  | top => rfl
  | bottom => rfl
  | equal left right =>
      by_cases h : left.eval boundEnv = right.eval boundEnv <;>
        simp [lower, lowerEqual, atomsBelow, h]
  | rel left right =>
      simp [lower, atomsBelow]
  | not p ih => simpa [lower, atomsBelow] using ih boundEnv
  | and p r ihp ihr => simp [lower, atomsBelow, ihp, ihr]
  | or p r ihp ihr => simp [lower, atomsBelow, ihp, ihr]
  | imp p r ihp ihr => simp [lower, atomsBelow, ihp, ihr]
  | forall_ body ih =>
      apply atomsBelow_allSources
      intro source hsource
      obtain ⟨x, rfl⟩ := List.mem_ofFn.mp hsource
      exact ih (Fin.cases x boundEnv)
  | exists_ body ih =>
      apply atomsBelow_anySources
      intro source hsource
      obtain ⟨x, rfl⟩ := List.mem_ofFn.mp hsource
      exact ih (Fin.cases x boundEnv)

/-- The unique empty bound-variable environment for a closed sentence. -/
def emptyBound {q : Nat} : Fin 0 -> Fin q := Fin.elim0

/-- Grounded Boolean source of a closed finite-FOL sentence. -/
def ground {q : Nat} (sentence : Formula q 0) : Live.Source :=
  lower sentence emptyBound

/-- Live IR-v2 descriptor for a closed finite-FOL sentence. -/
def compileDescriptorFOL {q : Nat} (sentence : Formula q 0) : EffectVmDescriptor2 :=
  compileDescriptor (q * q) (ground sentence)

/-- The public relation table is the entire trace row: exactly `q*q` bits. -/
@[simp] theorem compileDescriptorFOL_traceWidth {q : Nat} (sentence : Formula q 0) :
    (compileDescriptorFOL sentence).traceWidth = q * q := rfl

/-- One Booleanity constraint per relation entry, plus the always-on sentence
acceptance constraint. -/
@[simp] theorem compileDescriptorFOL_constraintCount {q : Nat}
    (sentence : Formula q 0) :
    (compileDescriptorFOL sentence).constraints.length = q * q + 1 := by
  simp [compileDescriptorFOL, compileDescriptor, logicConstraints]

/-- This direct finite-model relation needs no auxiliary hash or range table. -/
@[simp] theorem compileDescriptorFOL_noAuxiliaryTables {q : Nat}
    (sentence : Formula q 0) :
    (compileDescriptorFOL sentence).hashSites = [] /\
      (compileDescriptorFOL sentence).ranges = [] := by
  constructor <;> rfl

/-- Canonical live satisfaction specialized to the finite relation table. -/
abbrev FOLSatisfied2 (hash : List Int -> Int) {q : Nat} (sentence : Formula q 0)
    (minit : Int -> Int) (mfin : Int -> Int × Nat) (maddrs : List Int)
    (trace : VmTrace) : Prop :=
  CanonicalLogicSatisfied2 hash (q * q) (ground sentence)
    minit mfin maddrs trace

theorem ground_atomsBelow {q : Nat} (sentence : Formula q 0) :
    atomsBelow (q * q) (ground sentence) = true :=
  lower_atomsBelow sentence emptyBound

/-- **Live soundness.**  Every row of every canonical satisfying trace denotes
a finite structure satisfying the original first-order sentence. -/
theorem fol_sound {hash : List Int -> Int} {q : Nat} {sentence : Formula q 0}
    {minit : Int -> Int} {mfin : Int -> Int × Nat} {maddrs : List Int} {t : VmTrace}
    (hsat : FOLSatisfied2 hash sentence minit mfin maddrs t) :
    forall i, i < t.rows.length ->
      sentence.eval
        { relationBits := fun k => rowEnv (envAt t i).loc k.val }
        emptyBound = true := by
  intro i hi
  have hs := source_sound (ground_atomsBelow sentence) hsat i hi
  let rowModel : Model q :=
    { relationBits := fun k => rowEnv (envAt t i).loc k.val }
  have hagree : Live.eval (atomEnv rowModel) (ground sentence) =
      Live.eval (rowEnv (envAt t i).loc) (ground sentence) := by
    apply eval_congr_of_atomsBelow (ground_atomsBelow sentence)
    intro name hname
    simp [atomEnv, rowModel, hname]
  have hc := lower_correct rowModel sentence emptyBound
  exact hc.symm.trans (hagree.trans hs)

/-- Honest one-row trace containing the exact relation table of a model. -/
def modelTrace {q : Nat} (model : Model q) : VmTrace :=
  traceOf (atomEnv model)

/-- **Live completeness.**  Every finite model satisfying the sentence has a
concrete canonical one-row `Satisfied2` witness. -/
theorem fol_complete (hash : List Int -> Int) {q : Nat}
    (sentence : Formula q 0) (model : Model q)
    (htrue : sentence.eval model emptyBound = true) :
    FOLSatisfied2 hash sentence (fun _ => 0) (fun _ => ((0 : Int), 0)) []
      (modelTrace model) := by
  apply source_complete hash (q * q) (ground sentence) (atomEnv model)
    (ground_atomsBelow sentence)
  change Live.eval (atomEnv model) (lower sentence emptyBound) = true
  exact (lower_correct model sentence emptyBound).trans htrue

/-- Exact semantic characterization on the canonical trace. -/
theorem canonical_model_trace_iff (hash : List Int -> Int) {q : Nat}
    (sentence : Formula q 0) (model : Model q) :
    FOLSatisfied2 hash sentence (fun _ => 0) (fun _ => ((0 : Int), 0)) []
        (modelTrace model)
      <-> sentence.eval model emptyBound = true := by
  change CanonicalLogicSatisfied2 hash (q * q) (ground sentence)
      (fun _ => 0) (fun _ => ((0 : Int), 0)) [] (traceOf (atomEnv model))
      <-> sentence.eval model emptyBound = true
  rw [canonical_trace_iff hash (q * q) (ground sentence) (atomEnv model)
    (ground_atomsBelow sentence)]
  simpa [ground] using congrArg (fun b => b = true)
    (lower_correct model sentence emptyBound)

/-! ## 4. Fail-closed source-to-byte certificate -/

def certificateVersion : Nat := 1

structure FOLLiveCertificate (q : Nat) where
  version : Nat
  sentence : Formula q 0
  live : LiveCertificate

def checkFOLCertificate {q : Nat} (certificate : FOLLiveCertificate q) : Bool :=
  decide (certificate.version = certificateVersion) &&
    checkLive certificate.live &&
    decide (certificate.live.atomCount = q * q) &&
    decide (certificate.live.logic.source = ground certificate.sentence)

def certifyFOL {q : Nat} (sentence : Formula q 0) : FOLLiveCertificate q :=
  { version := certificateVersion
  , sentence := sentence
  , live := certifyLive (q * q) (ground sentence) }

theorem checkFOLCertificate_spec {q : Nat} {certificate : FOLLiveCertificate q} :
    checkFOLCertificate certificate = true <->
      certificate.version = certificateVersion /\
      checkLive certificate.live = true /\
      certificate.live.atomCount = q * q /\
      certificate.live.logic.source = ground certificate.sentence := by
  simp [checkFOLCertificate, and_assoc]

theorem checkFOLCertificate_certify {q : Nat} (sentence : Formula q 0) :
    checkFOLCertificate (certifyFOL sentence) = true := by
  apply checkFOLCertificate_spec.mpr
  refine ⟨rfl, checkLive_certify (q * q) (ground sentence)
    (ground_atomsBelow sentence), rfl, rfl⟩

/-- An accepted certificate and a satisfying trace imply the *certificate's
original first-order sentence*, not merely an untrusted grounded formula. -/
theorem checked_fol_sound {hash : List Int -> Int} {q : Nat}
    {certificate : FOLLiveCertificate q} {minit : Int -> Int}
    {mfin : Int -> Int × Nat} {maddrs : List Int} {t : VmTrace}
    (hcheck : checkFOLCertificate certificate = true)
    (hsat : CanonicalLogicSatisfied2 hash certificate.live.atomCount
      certificate.live.logic.source minit mfin maddrs t) :
    forall i, i < t.rows.length ->
      certificate.sentence.eval
        { relationBits := fun k => rowEnv (envAt t i).loc k.val }
        emptyBound = true := by
  obtain ⟨_, hlive, hcount, hsource⟩ := checkFOLCertificate_spec.mp hcheck
  have hs := checkLive_source_sound hlive hsat
  intro i hi
  have hground : Live.eval (rowEnv (envAt t i).loc)
      (ground certificate.sentence) = true := by
    simpa [hsource] using hs i hi
  let rowModel : Model q :=
    { relationBits := fun k => rowEnv (envAt t i).loc k.val }
  have hagree : Live.eval (atomEnv rowModel) (ground certificate.sentence) =
      Live.eval (rowEnv (envAt t i).loc) (ground certificate.sentence) := by
    apply eval_congr_of_atomsBelow (ground_atomsBelow certificate.sentence)
    intro name hname
    simp [atomEnv, rowModel, hname]
  have hc := lower_correct rowModel certificate.sentence emptyBound
  exact hc.symm.trans (hagree.trans hground)

/-! ## 5. Concrete non-vacuity with both truth values -/

/-- `forall x, exists y, R(x,y)`. -/
def serialSentence (q : Nat) : Formula q 0 :=
  .forall_ (.exists_ (.rel (.var 1) (.var 0)))

/-- The complete relation on two points satisfies seriality. -/
def completeTwo : Model 2 := { relationBits := fun _ => true }

/-- The empty relation on two points falsifies seriality. -/
def emptyTwo : Model 2 := { relationBits := fun _ => false }

#guard (serialSentence 2).eval completeTwo emptyBound
#guard !(serialSentence 2).eval emptyTwo emptyBound
#guard checkFOLCertificate (certifyFOL (serialSentence 2))
#guard (compileDescriptorFOL (serialSentence 2)).traceWidth == 4
#guard (compileDescriptorFOL (serialSentence 2)).constraints.length == 5

theorem serial_completeTwo_satisfied :
    FOLSatisfied2 (fun _ => 0) (serialSentence 2) (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (modelTrace completeTwo) := by
  exact fol_complete (fun _ => 0) (serialSentence 2) completeTwo (by decide)

theorem serial_emptyTwo_refused :
    Not (FOLSatisfied2 (fun _ => 0) (serialSentence 2) (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (modelTrace emptyTwo)) := by
  intro h
  have := (canonical_model_trace_iff (fun _ => 0)
    (serialSentence 2) emptyTwo).mp h
  have hfalse : (serialSentence 2).eval emptyTwo emptyBound = false := by decide
  rw [hfalse] at this
  exact Bool.false_ne_true this

#assert_all_clean [
  eval_allSources,
  eval_anySources,
  eval_congr_of_atomsBelow,
  atomEnv_edgeIndex,
  lower_correct,
  edgeIndex_lt_square,
  atomsBelow_allSources,
  atomsBelow_anySources,
  lower_atomsBelow,
  compileDescriptorFOL_traceWidth,
  compileDescriptorFOL_constraintCount,
  compileDescriptorFOL_noAuxiliaryTables,
  ground_atomsBelow,
  fol_sound,
  fol_complete,
  canonical_model_trace_iff,
  checkFOLCertificate_spec,
  checkFOLCertificate_certify,
  checked_fol_sound,
  serial_completeTwo_satisfied,
  serial_emptyTwo_refused
]

end Dregg2.Logic.FiniteRelationalFOLDescriptorIR2
