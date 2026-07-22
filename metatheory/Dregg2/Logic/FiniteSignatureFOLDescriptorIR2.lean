/-
# Dregg2.Logic.FiniteSignatureFOLDescriptorIR2

Executable finite-signature first-order logic compiled to the live descriptor
IR v2.

This generalizes `FiniteRelationalFOLDescriptorIR2` from one binary relation to
an explicit finite signature:

* arbitrarily many named relation symbols, each with its own finite arity;
* arbitrarily many named total function symbols, each with its own finite
  arity and complete public interpretation table;
* constants, de Bruijn variables, nested function application, equality,
  relation application, every Boolean connective, and exhaustive finite
  universal/existential quantification.

The live row is the canonical concatenation of all relation tables.  Function
tables are public compilation inputs: the fail-closed certificate serializes
and rechecks their complete finite graphs.  It separately binds the signature
manifest, relation-column manifest, exact source-formula encoding, grounded
Boolean source, and exact emitted `EffectVmDescriptor2` JSON.

This is an exact finite-model compiler, not a succinct quantifier protocol.
Grounding can grow exponentially with quantifier depth.  Function tables are
public here; witness-private functions require a RAM/lookup lowering rather
than being smuggled into this construction.
-/

import Dregg2.Logic.FiniteRelationalFOLDescriptorIR2

namespace Dregg2.Logic.FiniteSignatureFOLDescriptorIR2

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Logic.FiniteLogicDescriptorIR2

namespace Base

abbrev Source := Dregg2.Logic.FiniteLogicDescriptorIR2.Cert.Source
abbrev eval := Dregg2.Logic.FiniteLogicDescriptorIR2.Cert.eval
abbrev allSources := Dregg2.Logic.FiniteRelationalFOLDescriptorIR2.allSources
abbrev anySources := Dregg2.Logic.FiniteRelationalFOLDescriptorIR2.anySources

theorem eval_allSources (atomEnv : Nat -> Bool) (sources : List Source) :
    eval atomEnv (allSources sources) = sources.all (eval atomEnv) :=
  Dregg2.Logic.FiniteRelationalFOLDescriptorIR2.eval_allSources atomEnv sources

theorem eval_anySources (atomEnv : Nat -> Bool) (sources : List Source) :
    eval atomEnv (anySources sources) = sources.any (eval atomEnv) :=
  Dregg2.Logic.FiniteRelationalFOLDescriptorIR2.eval_anySources atomEnv sources

theorem eval_congr_of_atomsBelow {atomCount : Nat} {source : Source}
    (hbound : atomsBelow atomCount source = true) {left right : Nat -> Bool}
    (hagrees : forall name, name < atomCount -> left name = right name) :
    eval left source = eval right source :=
  Dregg2.Logic.FiniteRelationalFOLDescriptorIR2.eval_congr_of_atomsBelow
    hbound hagrees

theorem atomsBelow_allSources {atomCount : Nat} (sources : List Source)
    (h : forall source, source ∈ sources -> atomsBelow atomCount source = true) :
    atomsBelow atomCount (allSources sources) = true :=
  Dregg2.Logic.FiniteRelationalFOLDescriptorIR2.atomsBelow_allSources sources h

theorem atomsBelow_anySources {atomCount : Nat} (sources : List Source)
    (h : forall source, source ∈ sources -> atomsBelow atomCount source = true) :
    atomsBelow atomCount (anySources sources) = true :=
  Dregg2.Logic.FiniteRelationalFOLDescriptorIR2.atomsBelow_anySources sources h

end Base

set_option autoImplicit false

/-! ## 1. Finite signatures and their complete public function tables -/

/-- A total function symbol on the `q`-element domain. -/
structure FunctionSymbol (q : Nat) where
  arity : Nat
  interp : (Fin arity -> Fin q) -> Fin q

/-- A finite signature.  List position is the canonical numeric symbol name. -/
structure Signature (q : Nat) where
  functions : List (FunctionSymbol q)
  relationArities : List Nat

def Signature.functionArity {q : Nat} (signature : Signature q)
    (symbol : Fin signature.functions.length) : Nat :=
  (signature.functions.get symbol).arity

def Signature.relationArity {q : Nat} (signature : Signature q)
    (symbol : Fin signature.relationArities.length) : Nat :=
  signature.relationArities.get symbol

/-! ## 2. Canonical enumeration and signature/layout manifests -/

/-- Canonical enumeration of all `arity`-tuples over `Fin q`. -/
def enumerateArgs (q : Nat) : (arity : Nat) -> List (Fin arity -> Fin q)
  | 0 => [Fin.elim0]
  | arity + 1 =>
      (List.finRange q).flatMap fun head =>
        (enumerateArgs q arity).map fun tail => Fin.cases head tail

theorem enumerateArgs_length (q arity : Nat) :
    (enumerateArgs q arity).length = q ^ arity := by
  induction arity with
  | zero => simp [enumerateArgs]
  | succ arity ih =>
      simp [enumerateArgs, ih, pow_succ, Nat.mul_comm]

/-- Natural list encoding of one finite tuple. -/
def encodeArgs {q arity : Nat} (args : Fin arity -> Fin q) : List Nat :=
  List.ofFn fun i => (args i).val

/-- Every relation column, in canonical symbol-major then tuple-major order. -/
def relationManifest {q : Nat} (signature : Signature q) : List (Nat × List Nat) :=
  signature.relationArities.zipIdx.flatMap fun named =>
    (enumerateArgs q named.1).map fun args => (named.2, encodeArgs args)

/-- Canonical trace width: the sum of `q^arity` over all relation symbols. -/
def relationWidth {q : Nat} (signature : Signature q) : Nat :=
  (signature.relationArities.map fun arity => q ^ arity).sum

theorem relationManifest_length {q : Nat} (signature : Signature q) :
    (relationManifest signature).length = relationWidth signature := by
  simp only [relationManifest, List.length_flatMap, List.length_map,
    enumerateArgs_length, relationWidth]
  have hfst : signature.relationArities.zipIdx.map Prod.fst =
      signature.relationArities := by
    exact List.zipIdx_map_fst 0 signature.relationArities
  have hmap :
      (signature.relationArities.zipIdx.map fun named => q ^ named.1) =
        ((signature.relationArities.zipIdx.map Prod.fst).map
          fun arity => q ^ arity) := by
    rw [List.map_map]
    rfl
  rw [hmap, hfst]

/-- Complete graph of one public function symbol. -/
def functionTable {q : Nat} (symbol : FunctionSymbol q) : List (List Nat × Nat) :=
  (enumerateArgs q symbol.arity).map fun args =>
    (encodeArgs args, (symbol.interp args).val)

/-- Serializable data that binds all arities and all total public functions. -/
structure SignatureManifest where
  domainSize : Nat
  relationArities : List Nat
  functionTables : List (Nat × List (List Nat × Nat))
  deriving Repr, DecidableEq

def signatureManifest {q : Nat} (signature : Signature q) : SignatureManifest :=
  { domainSize := q
  , relationArities := signature.relationArities
  , functionTables := signature.functions.zipIdx.map fun named =>
      (named.2, functionTable named.1) }

/-! ## 3. Closed de Bruijn syntax and direct model semantics -/

inductive Term {q : Nat} (signature : Signature q) (bound : Nat) where
  | var (index : Fin bound)
  | const (value : Fin q)
  | app (symbol : Fin signature.functions.length)
      (args : Fin (signature.functionArity symbol) -> Term signature bound)

namespace Term

def eval {q bound : Nat} {signature : Signature q}
    (boundEnv : Fin bound -> Fin q) : Term signature bound -> Fin q
  | .var index => boundEnv index
  | .const value => value
  | .app symbol args =>
      (signature.functions.get symbol).interp fun i => eval boundEnv (args i)

def encode {q bound : Nat} {signature : Signature q} :
    Term signature bound -> List Nat
  | .var index => [0, index.val]
  | .const value => [1, value.val]
  | .app symbol args =>
      [2, symbol.val, signature.functionArity symbol] ++
        (List.ofFn fun i => encode (args i)).flatten

end Term

inductive Formula {q : Nat} (signature : Signature q) : Nat -> Type where
  | top {bound : Nat} : Formula signature bound
  | bottom {bound : Nat} : Formula signature bound
  | equal {bound : Nat} (left right : Term signature bound) : Formula signature bound
  | rel {bound : Nat} (symbol : Fin signature.relationArities.length)
      (args : Fin (signature.relationArity symbol) -> Term signature bound) :
      Formula signature bound
  | not {bound : Nat} (p : Formula signature bound) : Formula signature bound
  | and {bound : Nat} (p r : Formula signature bound) : Formula signature bound
  | or {bound : Nat} (p r : Formula signature bound) : Formula signature bound
  | imp {bound : Nat} (p r : Formula signature bound) : Formula signature bound
  | iff {bound : Nat} (p r : Formula signature bound) : Formula signature bound
  | forall_ {bound : Nat} (body : Formula signature (bound + 1)) : Formula signature bound
  | exists_ {bound : Nat} (body : Formula signature (bound + 1)) : Formula signature bound

/-- Canonically numbered relation column.  `idxOf` returns the manifest length
only on malformed input; well-formed applications are proved below to occur. -/
def relationColumn {q : Nat} {signature : Signature q}
    (symbol : Fin signature.relationArities.length)
    (args : Fin (signature.relationArity symbol) -> Fin q) : Nat :=
  (relationManifest signature).idxOf (symbol.val, encodeArgs args)

/-- A model supplies exactly the flattened Boolean relation interpretation.
Function interpretations are public and already live in the signature. -/
structure Model {q : Nat} (signature : Signature q) where
  relationBits : Fin (relationWidth signature) -> Bool

/- Membership of canonical tuples.  Kept private to the layout proof. -/
private theorem enumerateArgs_mem {q arity : Nat} (args : Fin arity -> Fin q) :
    args ∈ enumerateArgs q arity := by
  induction arity with
  | zero =>
      have hfun : args = Fin.elim0 := by funext i; exact Fin.elim0 i
      simp [enumerateArgs, hfun]
  | succ arity ih =>
      let head : Fin q := args 0
      let tail : Fin arity -> Fin q := fun i => args i.succ
      have hargs : args = Fin.cases head tail := by
        funext i
        refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
      rw [hargs]
      apply List.mem_flatMap.mpr
      refine ⟨head, List.mem_finRange head, ?_⟩
      apply List.mem_map.mpr
      exact ⟨tail, ih tail, rfl⟩

private theorem relationManifest_mem {q : Nat} (signature : Signature q)
    (symbol : Fin signature.relationArities.length)
    (args : Fin (signature.relationArity symbol) -> Fin q) :
    (symbol.val, encodeArgs args) ∈ relationManifest signature := by
  have hnamed : (signature.relationArity symbol, symbol.val) ∈
      signature.relationArities.zipIdx := by
    have hex : ∃ named ∈ signature.relationArities.zipIdx,
        named = (signature.relationArity symbol, symbol.val) :=
      (List.exists_mem_zipIdx').2 ⟨symbol.val, symbol.isLt, by
        simp [Signature.relationArity]⟩
    obtain ⟨named, hmem, hnamed⟩ := hex
    simpa [hnamed] using hmem
  apply List.mem_flatMap.mpr
  refine ⟨(signature.relationArity symbol, symbol.val), hnamed, ?_⟩
  apply List.mem_map.mpr
  exact ⟨args, enumerateArgs_mem args, rfl⟩

theorem relationColumn_lt {q : Nat} {signature : Signature q}
    (symbol : Fin signature.relationArities.length)
    (args : Fin (signature.relationArity symbol) -> Fin q) :
    relationColumn symbol args < relationWidth signature := by
  rw [← relationManifest_length]
  exact List.idxOf_lt_length_of_mem (relationManifest_mem signature symbol args)

def Model.rel {q : Nat} {signature : Signature q} (model : Model signature)
    (symbol : Fin signature.relationArities.length)
    (args : Fin (signature.relationArity symbol) -> Fin q) : Bool :=
  model.relationBits ⟨relationColumn symbol args, relationColumn_lt symbol args⟩

namespace Formula

def eval {q bound : Nat} {signature : Signature q} (model : Model signature)
    (boundEnv : Fin bound -> Fin q) : Formula signature bound -> Bool
  | .top => true
  | .bottom => false
  | .equal left right => decide (left.eval boundEnv = right.eval boundEnv)
  | .rel symbol args => model.rel symbol fun i => (args i).eval boundEnv
  | .not p => !(eval model boundEnv p)
  | .and p r => eval model boundEnv p && eval model boundEnv r
  | .or p r => eval model boundEnv p || eval model boundEnv r
  | .imp p r => !(eval model boundEnv p) || eval model boundEnv r
  | .iff p r => eval model boundEnv p == eval model boundEnv r
  | .forall_ body =>
      (List.ofFn fun x : Fin q => eval model (Fin.cases x boundEnv) body).all id
  | .exists_ body =>
      (List.ofFn fun x : Fin q => eval model (Fin.cases x boundEnv) body).any id

def encode {q bound : Nat} {signature : Signature q} :
    Formula signature bound -> List Nat
  | .top => [16]
  | .bottom => [17]
  | .equal left right => [18] ++ left.encode ++ right.encode
  | .rel symbol args =>
      [19, symbol.val, signature.relationArity symbol] ++
        (List.ofFn fun i => (args i).encode).flatten
  | .not p => 20 :: encode p
  | .and p r => [21] ++ encode p ++ encode r
  | .or p r => [22] ++ encode p ++ encode r
  | .imp p r => [23] ++ encode p ++ encode r
  | .iff p r => [24] ++ encode p ++ encode r
  | .forall_ body => 25 :: encode body
  | .exists_ body => 26 :: encode body

end Formula

/-! ## 4. Executable grounding and semantic preservation -/

def lowerEqual {q bound : Nat} {signature : Signature q}
    (boundEnv : Fin bound -> Fin q) (left right : Term signature bound) : Base.Source :=
  if left.eval boundEnv = right.eval boundEnv then .top else .bot

def lower {q bound : Nat} {signature : Signature q} :
    Formula signature bound -> (Fin bound -> Fin q) -> Base.Source
  | .top, _ => .top
  | .bottom, _ => .bot
  | .equal left right, env => lowerEqual env left right
  | .rel symbol args, env =>
      .atom (relationColumn symbol fun i => (args i).eval env)
  | .not p, env => .not (lower p env)
  | .and p r, env => .and (lower p env) (lower r env)
  | .or p r, env => .or (lower p env) (lower r env)
  | .imp p r, env => .or (.not (lower p env)) (lower r env)
  | .iff p r, env =>
      .or (.and (lower p env) (lower r env))
        (.and (.not (lower p env)) (.not (lower r env)))
  | .forall_ body, env =>
      Base.allSources (List.ofFn fun x : Fin q => lower body (Fin.cases x env))
  | .exists_ body, env =>
      Base.anySources (List.ofFn fun x : Fin q => lower body (Fin.cases x env))

/-- Canonical Boolean atom environment of a typed model. -/
def atomEnv {q : Nat} {signature : Signature q} (model : Model signature)
    (name : Nat) : Bool :=
  if h : name < relationWidth signature then model.relationBits ⟨name, h⟩ else false

@[simp] theorem atomEnv_relationColumn {q : Nat} {signature : Signature q}
    (model : Model signature) (symbol : Fin signature.relationArities.length)
    (args : Fin (signature.relationArity symbol) -> Fin q) :
    atomEnv model (relationColumn symbol args) = model.rel symbol args := by
  rw [atomEnv]
  simp only [dif_pos (relationColumn_lt symbol args)]
  rfl

theorem lower_correct {q bound : Nat} {signature : Signature q}
    (model : Model signature) (formula : Formula signature bound)
    (boundEnv : Fin bound -> Fin q) :
    Base.eval (atomEnv model) (lower formula boundEnv) =
      formula.eval model boundEnv := by
  induction formula with
  | top => rfl
  | bottom => rfl
  | equal left right =>
      by_cases h : left.eval boundEnv = right.eval boundEnv <;>
        simp [lower, lowerEqual, Formula.eval, h,
          Dregg2.Logic.CompilationCertificateBundle.Source.eval]
  | rel symbol args =>
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
  | iff p r ihp ihr =>
      cases hp : Formula.eval model boundEnv p <;>
        cases hr : Formula.eval model boundEnv r <;>
          simp [lower, Formula.eval,
            Dregg2.Logic.CompilationCertificateBundle.Source.eval, ihp, ihr, hp, hr]
  | forall_ body ih =>
      rw [lower, Base.eval_allSources, Formula.eval]
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
      rw [lower, Base.eval_anySources, Formula.eval]
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

theorem lower_atomsBelow {q bound : Nat} {signature : Signature q}
    (formula : Formula signature bound) (boundEnv : Fin bound -> Fin q) :
    atomsBelow (relationWidth signature) (lower formula boundEnv) = true := by
  induction formula with
  | top => rfl
  | bottom => rfl
  | equal left right =>
      by_cases h : left.eval boundEnv = right.eval boundEnv <;>
        simp [lower, lowerEqual, atomsBelow, h]
  | rel symbol args => simp [lower, atomsBelow, relationColumn_lt]
  | not p ih => simpa [lower, atomsBelow] using ih boundEnv
  | and p r ihp ihr => simp [lower, atomsBelow, ihp, ihr]
  | or p r ihp ihr => simp [lower, atomsBelow, ihp, ihr]
  | imp p r ihp ihr => simp [lower, atomsBelow, ihp, ihr]
  | iff p r ihp ihr => simp [lower, atomsBelow, ihp, ihr]
  | forall_ body ih =>
      apply Base.atomsBelow_allSources
      intro source hsource
      obtain ⟨x, rfl⟩ := List.mem_ofFn.mp hsource
      exact ih (Fin.cases x boundEnv)
  | exists_ body ih =>
      apply Base.atomsBelow_anySources
      intro source hsource
      obtain ⟨x, rfl⟩ := List.mem_ofFn.mp hsource
      exact ih (Fin.cases x boundEnv)

/-! ## 5. Actual live descriptor, soundness, completeness, and exact shape -/

def emptyBound {q : Nat} : Fin 0 -> Fin q := Fin.elim0

def ground {q : Nat} {signature : Signature q}
    (sentence : Formula signature 0) : Base.Source := lower sentence emptyBound

def compileDescriptorFOL {q : Nat} {signature : Signature q}
    (sentence : Formula signature 0) : EffectVmDescriptor2 :=
  compileDescriptor (relationWidth signature) (ground sentence)

@[simp] theorem compileDescriptorFOL_traceWidth {q : Nat} {signature : Signature q}
    (sentence : Formula signature 0) :
    (compileDescriptorFOL sentence).traceWidth = relationWidth signature := rfl

@[simp] theorem compileDescriptorFOL_constraintCount {q : Nat}
    {signature : Signature q} (sentence : Formula signature 0) :
    (compileDescriptorFOL sentence).constraints.length = relationWidth signature + 1 := by
  simp [compileDescriptorFOL, compileDescriptor, logicConstraints]

theorem ground_atomsBelow {q : Nat} {signature : Signature q}
    (sentence : Formula signature 0) :
    atomsBelow (relationWidth signature) (ground sentence) = true :=
  lower_atomsBelow sentence emptyBound

abbrev FOLSatisfied2 (hash : List Int -> Int) {q : Nat} {signature : Signature q}
    (sentence : Formula signature 0) (minit : Int -> Int)
    (mfin : Int -> Int × Nat) (maddrs : List Int) (trace : VmTrace) : Prop :=
  CanonicalLogicSatisfied2 hash (relationWidth signature) (ground sentence)
    minit mfin maddrs trace

theorem fol_sound {hash : List Int -> Int} {q : Nat} {signature : Signature q}
    {sentence : Formula signature 0} {minit : Int -> Int}
    {mfin : Int -> Int × Nat} {maddrs : List Int} {t : VmTrace}
    (hsat : FOLSatisfied2 hash sentence minit mfin maddrs t) :
    forall i, i < t.rows.length ->
      sentence.eval
        ({ relationBits := fun k => rowEnv (envAt t i).loc k.val } : Model signature)
        emptyBound = true := by
  intro i hi
  have hs := source_sound (ground_atomsBelow sentence) hsat i hi
  let rowModel : Model signature :=
    { relationBits := fun k => rowEnv (envAt t i).loc k.val }
  have hagree : Base.eval (atomEnv rowModel) (ground sentence) =
      Base.eval (rowEnv (envAt t i).loc) (ground sentence) := by
    apply Base.eval_congr_of_atomsBelow (ground_atomsBelow sentence)
    intro name hname
    simp [atomEnv, rowModel, hname]
  have hc := lower_correct rowModel sentence emptyBound
  exact hc.symm.trans (hagree.trans hs)

def modelTrace {q : Nat} {signature : Signature q} (model : Model signature) : VmTrace :=
  traceOf (atomEnv model)

theorem fol_complete (hash : List Int -> Int) {q : Nat} {signature : Signature q}
    (sentence : Formula signature 0) (model : Model signature)
    (htrue : sentence.eval model emptyBound = true) :
    FOLSatisfied2 hash sentence (fun _ => 0) (fun _ => ((0 : Int), 0)) []
      (modelTrace model) := by
  apply source_complete hash (relationWidth signature) (ground sentence) (atomEnv model)
    (ground_atomsBelow sentence)
  change Base.eval (atomEnv model) (lower sentence emptyBound) = true
  exact (lower_correct model sentence emptyBound).trans htrue

theorem canonical_model_trace_iff (hash : List Int -> Int) {q : Nat}
    {signature : Signature q} (sentence : Formula signature 0) (model : Model signature) :
    FOLSatisfied2 hash sentence (fun _ => 0) (fun _ => ((0 : Int), 0)) []
        (modelTrace model)
      <-> sentence.eval model emptyBound = true := by
  change CanonicalLogicSatisfied2 hash (relationWidth signature) (ground sentence)
      (fun _ => 0) (fun _ => ((0 : Int), 0)) [] (traceOf (atomEnv model))
      <-> sentence.eval model emptyBound = true
  rw [canonical_trace_iff hash (relationWidth signature) (ground sentence) (atomEnv model)
    (ground_atomsBelow sentence)]
  simpa [ground] using congrArg (fun b => b = true)
    (lower_correct model sentence emptyBound)

/-! ## 6. Certificate binds signature, layout, syntax, lowering, and bytes -/

def certificateVersion : Nat := 1

structure FOLLiveCertificate (q : Nat) where
  version : Nat
  signature : Signature q
  sentence : Formula signature 0
  claimedSignature : SignatureManifest
  claimedLayout : List (Nat × List Nat)
  claimedFormula : List Nat
  live : LiveCertificate

def checkFOLCertificate {q : Nat} (certificate : FOLLiveCertificate q) : Bool :=
  decide (certificate.version = certificateVersion) &&
    decide (certificate.claimedSignature = signatureManifest certificate.signature) &&
    decide (certificate.claimedLayout = relationManifest certificate.signature) &&
    decide (certificate.claimedFormula = certificate.sentence.encode) &&
    checkLive certificate.live &&
    decide (certificate.live.atomCount = relationWidth certificate.signature) &&
    decide (certificate.live.logic.source = ground certificate.sentence)

def certifyFOL {q : Nat} {signature : Signature q}
    (sentence : Formula signature 0) : FOLLiveCertificate q :=
  { version := certificateVersion
  , signature := signature
  , sentence := sentence
  , claimedSignature := signatureManifest signature
  , claimedLayout := relationManifest signature
  , claimedFormula := sentence.encode
  , live := certifyLive (relationWidth signature) (ground sentence) }

theorem checkFOLCertificate_spec {q : Nat} {certificate : FOLLiveCertificate q} :
    checkFOLCertificate certificate = true <->
      certificate.version = certificateVersion /\
      certificate.claimedSignature = signatureManifest certificate.signature /\
      certificate.claimedLayout = relationManifest certificate.signature /\
      certificate.claimedFormula = certificate.sentence.encode /\
      checkLive certificate.live = true /\
      certificate.live.atomCount = relationWidth certificate.signature /\
      certificate.live.logic.source = ground certificate.sentence := by
  simp [checkFOLCertificate, and_assoc]

theorem checkFOLCertificate_certify {q : Nat} {signature : Signature q}
    (sentence : Formula signature 0) :
    checkFOLCertificate (certifyFOL sentence) = true := by
  apply checkFOLCertificate_spec.mpr
  refine ⟨rfl, rfl, rfl, rfl,
    checkLive_certify (relationWidth signature) (ground sentence)
      (ground_atomsBelow sentence), rfl, rfl⟩

/-- Certificate-to-source theorem.  A checked certificate and a satisfying live
trace imply the exact encoded first-order sentence under the exact checked
signature and canonical column layout. -/
theorem checked_fol_sound {hash : List Int -> Int} {q : Nat}
    {certificate : FOLLiveCertificate q} {minit : Int -> Int}
    {mfin : Int -> Int × Nat} {maddrs : List Int} {t : VmTrace}
    (hcheck : checkFOLCertificate certificate = true)
    (hsat : CanonicalLogicSatisfied2 hash certificate.live.atomCount
      certificate.live.logic.source minit mfin maddrs t) :
    forall i, i < t.rows.length ->
      certificate.sentence.eval
        ({ relationBits := fun k => rowEnv (envAt t i).loc k.val } :
          Model certificate.signature)
        emptyBound = true := by
  obtain ⟨_, _, _, _, hlive, hcount, hsource⟩ := checkFOLCertificate_spec.mp hcheck
  have hs := checkLive_source_sound hlive hsat
  intro i hi
  have hground : Base.eval (rowEnv (envAt t i).loc)
      (ground certificate.sentence) = true := by
    simpa [hsource] using hs i hi
  let rowModel : Model certificate.signature :=
    { relationBits := fun k => rowEnv (envAt t i).loc k.val }
  have hagree : Base.eval (atomEnv rowModel) (ground certificate.sentence) =
      Base.eval (rowEnv (envAt t i).loc) (ground certificate.sentence) := by
    apply Base.eval_congr_of_atomsBelow (ground_atomsBelow certificate.sentence)
    intro name hname
    simp [atomEnv, rowModel, hname]
  have hc := lower_correct rowModel certificate.sentence emptyBound
  exact hc.symm.trans (hagree.trans hground)

/-! ## 7. Nested-quantifier/function specimen and tamper rejection -/

def flip : FunctionSymbol 2 :=
  { arity := 1
  , interp := fun args => if args 0 = 0 then 1 else 0 }

def demoSignature : Signature 2 :=
  { functions := [flip]
  , relationArities := [1, 2] }

def demoFunction : Fin demoSignature.functions.length := ⟨0, by simp [demoSignature]⟩
def demoUnary : Fin demoSignature.relationArities.length := ⟨0, by simp [demoSignature]⟩
def demoBinary : Fin demoSignature.relationArities.length := ⟨1, by simp [demoSignature]⟩

def flipTerm {bound : Nat} (term : Term demoSignature bound) : Term demoSignature bound :=
  .app demoFunction (fun _ => term)

/-- `forall x, exists y, R_1(flip(x),y) and R_0(flip(flip(x)))`. -/
def nestedSentence : Formula demoSignature 0 :=
  .forall_ (.exists_ (.and
    (.rel demoBinary (fun i => Fin.cases (flipTerm (.var 1)) (fun _ => .var 0) i))
    (.rel demoUnary (fun _ => flipTerm (flipTerm (.var 1))))))

def demoModel : Model demoSignature := { relationBits := fun _ => true }

#guard nestedSentence.eval demoModel emptyBound
#guard checkFOLCertificate (certifyFOL nestedSentence)
#guard (compileDescriptorFOL nestedSentence).traceWidth == 6
#guard (compileDescriptorFOL nestedSentence).constraints.length == 7

def tamperedLayoutCertificate : FOLLiveCertificate 2 :=
  { (certifyFOL nestedSentence) with claimedLayout := [] }

#guard !checkFOLCertificate tamperedLayoutCertificate

theorem nestedSentence_satisfied :
    FOLSatisfied2 (fun _ => 0) nestedSentence (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (modelTrace demoModel) := by
  exact fol_complete (fun _ => 0) nestedSentence demoModel (by decide)

theorem tampered_layout_rejected :
    checkFOLCertificate tamperedLayoutCertificate = false := by
  rfl

#assert_all_clean [
  enumerateArgs_length,
  relationManifest_length,
  relationColumn_lt,
  atomEnv_relationColumn,
  lower_correct,
  lower_atomsBelow,
  compileDescriptorFOL_traceWidth,
  compileDescriptorFOL_constraintCount,
  ground_atomsBelow,
  fol_sound,
  fol_complete,
  canonical_model_trace_iff,
  checkFOLCertificate_spec,
  checkFOLCertificate_certify,
  checked_fol_sound,
  nestedSentence_satisfied,
  tampered_layout_rejected
]

end Dregg2.Logic.FiniteSignatureFOLDescriptorIR2
