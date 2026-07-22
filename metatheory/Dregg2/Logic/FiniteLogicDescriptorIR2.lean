/-
# Dregg2.Logic.FiniteLogicDescriptorIR2 -- a live Boolean compiler to descriptor IR v2

This module closes the smallest source-logic-to-live-circuit triangle.  Its
source is the versioned Boolean language from `CompilationCertificateBundle`.
The target is `EffectVmDescriptor2` itself -- never the retired descriptor IR
v1 -- and the target constraints are live IR-v2 `windowGate`s.

Atoms occupy columns `0 .. atomCount-1`.  Every atom receives the BabyBear
booleanity gate `x * (x - 1) = 0`.  Formulae use the standard Boolean
polynomials with truth represented by one:

* `not p = 1 - p`;
* `p and q = p * q`;
* `p or q = p + q - p*q`.

The final always-on window gate forces the formula polynomial to one.  Using
`windowGate` with `onTransition = false` is deliberate: unlike a base `.gate`,
the assertion also fires on the last/wrap row, so a one-row proof is not
vacuous.

`CanonicalLogicSatisfied2` is the precisely named faithful subrelation needed
by the integer model of IR-v2: `Satisfied2` supplies the live modular gates and
the additional field-canonicality clause chooses the deployed representative
of each input felt.  Soundness is exact against that subrelation; completeness
constructs a one-row `Satisfied2` witness for every true source formula.

The final section extends the existing reference compilation certificate with
the exact `emitVmJson2` bytes.  The checker trusts neither a claimed target tree
nor claimed descriptor bytes.

Standalone additive module.  No central import is changed.  No axioms.
-/

import Dregg2.Logic.CompilationCertificateBundle
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Logic.FiniteLogicDescriptorIR2

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)

/- Lean has no namespace-alias command.  These transparent aliases keep the
certificate vocabulary visually separate without duplicating its definitions. -/
namespace Cert

abbrev Source := Dregg2.Logic.CompilationCertificateBundle.Source
abbrev Bundle := Dregg2.Logic.CompilationCertificateBundle.Bundle
abbrev eval := Dregg2.Logic.CompilationCertificateBundle.Source.eval
abbrev check := Dregg2.Logic.CompilationCertificateBundle.check
abbrev certify := Dregg2.Logic.CompilationCertificateBundle.certify

theorem check_certify (source : Source) : check (certify source) = true :=
  Dregg2.Logic.CompilationCertificateBundle.check_certify source

end Cert

set_option autoImplicit false

/-! ## 1. Bounded source atoms and their field interpretation -/

/-- The deployed base-field modulus. -/
def P : Int := 2013265921

/-- A source formula fits a descriptor of `atomCount` columns. -/
def atomsBelow (atomCount : Nat) : Cert.Source -> Bool
  | .atom name => decide (name < atomCount)
  | .top => true
  | .bot => true
  | .not p => atomsBelow atomCount p
  | .and p q => atomsBelow atomCount p && atomsBelow atomCount q
  | .or p q => atomsBelow atomCount p && atomsBelow atomCount q

/-- Decode a canonical field bit to the source Boolean environment. -/
def rowEnv (a : Assignment) (name : Nat) : Bool := decide (a name = 1)

/-- The integer representative of a Boolean. -/
def bitInt (b : Bool) : Int := if b then 1 else 0

/-- The canonicality condition the deployed field representation supplies for
the source columns. -/
def CanonicalAtoms (atomCount : Nat) (a : Assignment) : Prop :=
  forall name, name < atomCount -> 0 <= a name /\ a name < P

/-! ## 2. Boolean polynomials in the live IR-v2 window grammar -/

def negW (x : WindowExpr) : WindowExpr := .mul (.const (-1)) x

def oneMinusW (x : WindowExpr) : WindowExpr := .add (.const 1) (negW x)

def orW (x y : WindowExpr) : WindowExpr :=
  .add (.add x y) (negW (.mul x y))

/-- Direct Boolean polynomial for a source formula.  It reads only local-row
columns; no witness-authored intermediate value is trusted. -/
def sourcePoly : Cert.Source -> WindowExpr
  | .atom name => .loc name
  | .top => .const 1
  | .bot => .const 0
  | .not p => oneMinusW (sourcePoly p)
  | .and p q => .mul (sourcePoly p) (sourcePoly q)
  | .or p q => orW (sourcePoly p) (sourcePoly q)

/-- `x * (x - 1)`: the field booleanity body for atom column `name`. -/
def binaryBody (name : Nat) : WindowExpr :=
  .mul (.loc name) (.add (.loc name) (.const (-1)))

/-- Always-on booleanity gate; it also fires on the final row. -/
def binaryConstraint (name : Nat) : WindowConstraint :=
  { body := binaryBody name, onTransition := false }

/-- The final formula-is-true body `poly(source) - 1`. -/
def acceptBody (source : Cert.Source) : WindowExpr :=
  .add (sourcePoly source) (.const (-1))

/-- Always-on acceptance gate; in particular it is non-vacuous for one row. -/
def acceptConstraint (source : Cert.Source) : WindowConstraint :=
  { body := acceptBody source, onTransition := false }

def logicConstraints (atomCount : Nat) (source : Cert.Source) : List VmConstraint2 :=
  (List.range atomCount).map (fun name => .windowGate (binaryConstraint name)) ++
    [.windowGate (acceptConstraint source)]

/-- The live IR-v2 descriptor compiled from a source formula. -/
def compileDescriptor (atomCount : Nat) (source : Cert.Source) : EffectVmDescriptor2 :=
  { name := "dregg-finite-logic-v2-" ++ toString atomCount
  , traceWidth := atomCount
  , piCount := 0
  , tables := [mainTableDef atomCount]
  , constraints := logicConstraints atomCount source
  , hashSites := []
  , ranges := [] }

/-! ## 3. Exact polynomial semantics -/

/-- Canonical modular booleanity is an honest integer bit. -/
theorem binary_of_modular_gate {env : VmRowEnv} {atomCount name : Nat}
    (hcanon : CanonicalAtoms atomCount env.loc) (hname : name < atomCount)
    (hmod : (binaryBody name).eval env ≡ 0 [ZMOD 2013265921]) :
    env.loc name = 0 \/ env.loc name = 1 := by
  have hp : Prime (2013265921 : Int) := by
    exact_mod_cast Nat.prime_iff_prime_int.mp
      Dregg2.Circuit.BabyBearFriField.babyBearP_prime
  have hev : (binaryBody name).eval env = env.loc name * (env.loc name - 1) := by
    simp only [binaryBody, WindowExpr.eval]
    ring
  rw [hev, Int.modEq_zero_iff_dvd] at hmod
  rcases hp.dvd_mul.mp hmod with hx | hx
  · obtain ⟨k, hk⟩ := hx
    left
    have hc := hcanon name hname
    simp only [P] at hc
    omega
  · obtain ⟨k, hk⟩ := hx
    right
    have hc := hcanon name hname
    simp only [P] at hc
    omega

/-- The Boolean polynomial evaluates to exactly `0` or `1` when its referenced
atoms are exact bits. -/
theorem sourcePoly_eval (env : VmRowEnv) (atomCount : Nat) (source : Cert.Source)
    (hbound : atomsBelow atomCount source = true)
    (hbits : forall name, name < atomCount -> env.loc name = 0 \/ env.loc name = 1) :
    (sourcePoly source).eval env = bitInt (Cert.eval (rowEnv env.loc) source) := by
  induction source with
  | atom name =>
      have hname : name < atomCount := by simpa [atomsBelow] using hbound
      rcases hbits name hname with hzero | hone
      · simp [sourcePoly, WindowExpr.eval, Cert.eval,
          Dregg2.Logic.CompilationCertificateBundle.Source.eval, rowEnv, bitInt, hzero]
      · simp [sourcePoly, WindowExpr.eval, Cert.eval,
          Dregg2.Logic.CompilationCertificateBundle.Source.eval, rowEnv, bitInt, hone]
  | top =>
      simp [sourcePoly, Cert.eval,
        Dregg2.Logic.CompilationCertificateBundle.Source.eval, bitInt, WindowExpr.eval]
  | bot =>
      simp [sourcePoly, Cert.eval,
        Dregg2.Logic.CompilationCertificateBundle.Source.eval, bitInt, WindowExpr.eval]
  | not p ih =>
      have hp : atomsBelow atomCount p = true := by simpa [atomsBelow] using hbound
      simp only [sourcePoly, oneMinusW, negW, WindowExpr.eval]
      rw [ih hp]
      cases heval : Cert.eval (rowEnv env.loc) p <;>
        simp [Cert.eval, Dregg2.Logic.CompilationCertificateBundle.Source.eval,
          bitInt, heval]
  | and p q ihp ihq =>
      have hb : atomsBelow atomCount p = true /\ atomsBelow atomCount q = true := by
        simpa [atomsBelow] using hbound
      simp only [sourcePoly, WindowExpr.eval]
      rw [ihp hb.1, ihq hb.2]
      cases hp : Cert.eval (rowEnv env.loc) p <;>
        cases hq : Cert.eval (rowEnv env.loc) q <;>
          simp [Cert.eval, Dregg2.Logic.CompilationCertificateBundle.Source.eval,
            bitInt, hp, hq]
  | or p q ihp ihq =>
      have hb : atomsBelow atomCount p = true /\ atomsBelow atomCount q = true := by
        simpa [atomsBelow] using hbound
      simp only [sourcePoly, orW, negW, WindowExpr.eval]
      rw [ihp hb.1, ihq hb.2]
      cases hp : Cert.eval (rowEnv env.loc) p <;>
        cases hq : Cert.eval (rowEnv env.loc) q <;>
          simp [Cert.eval, Dregg2.Logic.CompilationCertificateBundle.Source.eval,
            bitInt, hp, hq]

/-! ## 4. Soundness against the live `Satisfied2` denotation -/

/-- `Satisfied2` plus canonical source columns.  The latter is explicit because
the IR's Lean denotation uses integer representatives for the BabyBear field. -/
structure CanonicalLogicSatisfied2 (hash : List Int -> Int) (atomCount : Nat)
    (source : Cert.Source) (minit : Int -> Int) (mfin : Int -> Int × Nat)
    (maddrs : List Int) (t : VmTrace) : Prop
    extends Satisfied2 hash (compileDescriptor atomCount source) minit mfin maddrs t where
  canonicalAtoms : forall i, i < t.rows.length -> CanonicalAtoms atomCount (envAt t i).loc

theorem binary_constraint_mem {atomCount : Nat} (source : Cert.Source) {name : Nat}
    (hname : name < atomCount) :
    .windowGate (binaryConstraint name) ∈ (compileDescriptor atomCount source).constraints := by
  rw [compileDescriptor]
  simp only [logicConstraints, List.mem_append, List.mem_map]
  exact Or.inl ⟨name, List.mem_range.mpr hname, rfl⟩

theorem accept_constraint_mem (atomCount : Nat) (source : Cert.Source) :
    .windowGate (acceptConstraint source) ∈ (compileDescriptor atomCount source).constraints := by
  simp [compileDescriptor, logicConstraints]

/-- Every row of a canonical satisfying live trace makes the source formula
true.  The always-on final constraint makes this valid even on the last row. -/
theorem source_sound {hash : List Int -> Int} {atomCount : Nat}
    {source : Cert.Source} {minit : Int -> Int} {mfin : Int -> Int × Nat}
    {maddrs : List Int} {t : VmTrace}
    (hbound : atomsBelow atomCount source = true)
    (hsat : CanonicalLogicSatisfied2 hash atomCount source minit mfin maddrs t) :
    forall i, i < t.rows.length -> Cert.eval (rowEnv (envAt t i).loc) source = true := by
  intro i hi
  have hbits : forall name, name < atomCount ->
      (envAt t i).loc name = 0 \/ (envAt t i).loc name = 1 := by
    intro name hname
    have hgate := hsat.toSatisfied2.rowConstraints i hi
      (.windowGate (binaryConstraint name)) (binary_constraint_mem source hname)
    have hmod : (binaryBody name).eval (envAt t i) ≡ 0 [ZMOD 2013265921] := by
      simpa [VmConstraint2.holdsAt, WindowConstraint.holdsAt, binaryConstraint] using hgate
    exact binary_of_modular_gate (hsat.canonicalAtoms i hi) hname hmod
  have hpoly := sourcePoly_eval (envAt t i) atomCount source hbound hbits
  have hfinal := hsat.toSatisfied2.rowConstraints i hi
    (.windowGate (acceptConstraint source)) (accept_constraint_mem atomCount source)
  have hmod : (acceptBody source).eval (envAt t i) ≡ 0 [ZMOD 2013265921] := by
    simpa [VmConstraint2.holdsAt, WindowConstraint.holdsAt, acceptConstraint] using hfinal
  cases heval : Cert.eval (rowEnv (envAt t i).loc) source with
  | false =>
      have hp0 : (sourcePoly source).eval (envAt t i) = 0 := by
        simpa [heval, bitInt] using hpoly
      simp only [acceptBody, WindowExpr.eval, hp0, zero_add] at hmod
      rw [Int.modEq_zero_iff_dvd] at hmod
      norm_num at hmod
  | true => rfl

/-! ## 5. Completeness: construct the live one-row witness -/

def rowOf (env : Nat -> Bool) : Assignment := fun name => bitInt (env name)

def traceOf (env : Nat -> Bool) : VmTrace :=
  { rows := [rowOf env], pub := zeroAsg, tf := fun _ => [] }

theorem rowEnv_rowOf (env : Nat -> Bool) : rowEnv (rowOf env) = env := by
  funext name
  cases h : env name <;> simp [rowEnv, rowOf, bitInt, h]

theorem canonicalAtoms_rowOf (atomCount : Nat) (env : Nat -> Bool) :
    CanonicalAtoms atomCount (rowOf env) := by
  intro name hname
  cases h : env name <;> simp [rowOf, bitInt, P, h]

theorem traceOf_loc (env : Nat -> Bool) : (envAt (traceOf env) 0).loc = rowOf env := by
  simp [envAt, traceOf]

theorem sourcePoly_eval_rowOf (atomCount : Nat) (source : Cert.Source)
    (env : Nat -> Bool) (hbound : atomsBelow atomCount source = true) :
    (sourcePoly source).eval (envAt (traceOf env) 0) = bitInt (Cert.eval env source) := by
  have hbits : forall name, name < atomCount ->
      (envAt (traceOf env) 0).loc name = 0 \/ (envAt (traceOf env) 0).loc name = 1 := by
    intro name hname
    rw [traceOf_loc]
    cases h : env name <;> simp [rowOf, bitInt, h]
  have h := sourcePoly_eval (envAt (traceOf env) 0) atomCount source hbound hbits
  rw [traceOf_loc, rowEnv_rowOf] at h
  exact h

theorem memLog_compileDescriptor (atomCount : Nat) (source : Cert.Source) (t : VmTrace) :
    memLog (compileDescriptor atomCount source) t = [] := by
  simp [memLog, memOpsOf, compileDescriptor, logicConstraints]

theorem mapLog_compileDescriptor (atomCount : Nat) (source : Cert.Source) (t : VmTrace) :
    mapLog (compileDescriptor atomCount source) t = [] := by
  simp [mapLog, mapOpsOf, compileDescriptor, logicConstraints]

/-- Every true bounded source formula has a concrete canonical one-row witness
for the emitted live descriptor. -/
theorem source_complete (hash : List Int -> Int) (atomCount : Nat)
    (source : Cert.Source) (env : Nat -> Bool)
    (hbound : atomsBelow atomCount source = true)
    (htrue : Cert.eval env source = true) :
    CanonicalLogicSatisfied2 hash atomCount source (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (traceOf env) := by
  have hpoly := sourcePoly_eval_rowOf atomCount source env hbound
  refine ⟨⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i hi c hc
    have hi0 : i = 0 := by simp [traceOf] at hi; omega
    subst i
    simp only [compileDescriptor, logicConstraints, List.mem_append, List.mem_map] at hc
    rcases hc with ⟨name, hname, rfl⟩ | hc
    · have hn : name < atomCount := List.mem_range.mp hname
      simp only [VmConstraint2.holdsAt, WindowConstraint.holdsAt, binaryConstraint]
      change (binaryBody name).eval (envAt (traceOf env) 0) ≡ 0 [ZMOD 2013265921]
      cases h : env name <;>
        simp [binaryBody, WindowExpr.eval, traceOf, envAt, rowOf, bitInt, h]
    · have hc' : c = .windowGate (acceptConstraint source) := by simpa using hc
      subst c
      simp only [VmConstraint2.holdsAt, WindowConstraint.holdsAt, acceptConstraint,
        acceptBody, WindowExpr.eval]
      rw [hpoly, htrue]
      exact Int.ModEq.refl 0
  · intro i hi
    trivial
  · intro i hi r hr
    simp [compileDescriptor] at hr
  · intro op hop
    rw [memLog_compileDescriptor atomCount source (traceOf env)] at hop
    cases hop
  · rw [memLog_compileDescriptor atomCount source (traceOf env)]
    trivial
  · rw [memLog_compileDescriptor atomCount source (traceOf env)]
    exact memCheck_nil _ _
  · rw [memLog_compileDescriptor atomCount source (traceOf env)]
    rfl
  · rw [mapLog_compileDescriptor atomCount source (traceOf env)]
    rfl
  · intro i hi
    have hi0 : i = 0 := by simp [traceOf] at hi; omega
    subst i
    rw [traceOf_loc]
    exact canonicalAtoms_rowOf atomCount env

/-- Exact soundness/completeness on the compiler's canonical trace. -/
theorem canonical_trace_iff (hash : List Int -> Int) (atomCount : Nat)
    (source : Cert.Source) (env : Nat -> Bool)
    (hbound : atomsBelow atomCount source = true) :
    CanonicalLogicSatisfied2 hash atomCount source (fun _ => 0)
        (fun _ => ((0 : Int), 0)) [] (traceOf env)
      ↔ Cert.eval env source = true := by
  constructor
  · intro h
    have hs := source_sound hbound h 0 (by simp [traceOf])
    rw [traceOf_loc, rowEnv_rowOf] at hs
    exact hs
  · exact source_complete hash atomCount source env hbound

/-! ## 6. A versioned certificate that binds the exact live bytes -/

def liveVersion : Nat := 1

structure LiveCertificate where
  version : Nat
  atomCount : Nat
  logic : Cert.Bundle
  emittedDescriptor : String
  deriving Repr, DecidableEq

/-- Fail-closed reference checker.  The existing logic checker reconstructs
its independent target, while this checker reconstructs the exact live IR-v2
wire bytes from the accepted source. -/
def checkLive (certificate : LiveCertificate) : Bool :=
  decide (certificate.version = liveVersion) &&
    Cert.check certificate.logic &&
    atomsBelow certificate.atomCount certificate.logic.source &&
    decide (certificate.emittedDescriptor =
      emitVmJson2 (compileDescriptor certificate.atomCount certificate.logic.source))

def certifyLive (atomCount : Nat) (source : Cert.Source) : LiveCertificate :=
  { version := liveVersion
  , atomCount := atomCount
  , logic := Cert.certify source
  , emittedDescriptor := emitVmJson2 (compileDescriptor atomCount source) }

theorem checkLive_spec {certificate : LiveCertificate} :
    checkLive certificate = true ↔
      certificate.version = liveVersion /\
      Cert.check certificate.logic = true /\
      atomsBelow certificate.atomCount certificate.logic.source = true /\
      certificate.emittedDescriptor =
        emitVmJson2 (compileDescriptor certificate.atomCount certificate.logic.source) := by
  simp [checkLive, and_assoc]

theorem checkLive_certify (atomCount : Nat) (source : Cert.Source)
    (hbound : atomsBelow atomCount source = true) :
    checkLive (certifyLive atomCount source) = true := by
  apply checkLive_spec.mpr
  simp [certifyLive, Cert.certify,
    Dregg2.Logic.CompilationCertificateBundle.certify, Cert.check,
    Dregg2.Logic.CompilationCertificateBundle.check, hbound]

/-- Accepted certificate plus live satisfaction implies the accepted source
formula.  The certificate's claimed independent target and descriptor bytes
have both been reconstructed by their checkers. -/
theorem checkLive_source_sound {hash : List Int -> Int} {certificate : LiveCertificate}
    {minit : Int -> Int} {mfin : Int -> Int × Nat} {maddrs : List Int} {t : VmTrace}
    (hcheck : checkLive certificate = true)
    (hsat : CanonicalLogicSatisfied2 hash certificate.atomCount certificate.logic.source
      minit mfin maddrs t) :
    forall i, i < t.rows.length ->
      Cert.eval (rowEnv (envAt t i).loc) certificate.logic.source = true := by
  have hs := (checkLive_spec.mp hcheck).2.2.1
  exact source_sound hs hsat

/-! ## 7. Concrete emitted descriptor and certificate -/

/-- `a0 and (not a1 or a2)`: a small policy with every connective. -/
def demoPolicy : Cert.Source :=
  .and (.atom 0) (.or (.not (.atom 1)) (.atom 2))

def demoEnv : Nat -> Bool
  | 0 => true
  | 1 => false
  | _ => false

def demoDescriptor : EffectVmDescriptor2 := compileDescriptor 3 demoPolicy

def demoCertificate : LiveCertificate := certifyLive 3 demoPolicy

#guard atomsBelow 3 demoPolicy
#guard Cert.eval demoEnv demoPolicy
#guard checkLive demoCertificate
#guard demoDescriptor.constraints.length == 4
#guard demoDescriptor.hashSites.isEmpty
#guard demoDescriptor.ranges.isEmpty

/-- Independently written expected wire image for the concrete policy.  Equality
against this literal detects changes to tags, field names, ordering, constants,
or the compiled polynomial itself. -/
def demoDescriptorJson : String :=
  "{\"name\":\"dregg-finite-logic-v2-3\",\"ir\":2,\"trace_width\":3,\"public_input_count\":0,\"tables\":[{\"id\":0,\"name\":\"main\",\"arity\":3,\"sem\":\"main\"}],\"constraints\":[{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":0},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":0},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":1},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":2},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":2},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":0},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":1}}},\"r\":{\"t\":\"loc\",\"c\":2}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":1}}},\"r\":{\"t\":\"loc\",\"c\":2}}}}},\"r\":{\"t\":\"const\",\"v\":-1}}}],\"hash_sites\":[],\"ranges\":[]}"

#guard emitVmJson2 demoDescriptor == demoDescriptorJson

theorem demo_satisfied :
    CanonicalLogicSatisfied2 (fun _ => 0) 3 demoPolicy (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (traceOf demoEnv) := by
  exact source_complete (fun _ => 0) 3 demoPolicy demoEnv (by decide) (by decide)

#assert_all_clean [
  binary_of_modular_gate,
  sourcePoly_eval,
  binary_constraint_mem,
  accept_constraint_mem,
  source_sound,
  rowEnv_rowOf,
  canonicalAtoms_rowOf,
  traceOf_loc,
  sourcePoly_eval_rowOf,
  memLog_compileDescriptor,
  mapLog_compileDescriptor,
  source_complete,
  canonical_trace_iff,
  checkLive_spec,
  checkLive_certify,
  checkLive_source_sound,
  demo_satisfied
]

end Dregg2.Logic.FiniteLogicDescriptorIR2
