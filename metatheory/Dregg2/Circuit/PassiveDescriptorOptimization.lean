/-
# Dregg2.Circuit.PassiveDescriptorOptimization — checked contracts for passive AIR rewrites

A passive optimization changes descriptor/witness geometry without changing the public statement.
This file deliberately separates four claims which are easy to conflate:

* `PassiveOptimization` merely supplies both trace maps and preserves the public ABI.
* `SecurityRefinement` says every TARGET witness expands to a SOURCE witness.  This is the
  load-bearing, one-way "the optimized AIR is no weaker" theorem.
* `SatisfiabilityPreservation` additionally maps every source witness to a target witness.
  It proves equisatisfiability, but still does not say the witness maps are inverses.
* `WitnessIsomorphism` and `ExactCarrierTransport` separately record pointwise witness and
  auxiliary-table correspondence.  Neither follows from equisatisfiability.

The distinction matters for `Satisfied2`: lookup-table membership is insensitive to unused rows,
so satisfaction alone does not preserve auxiliary-table multiplicities.  Likewise, preserving
the ordered `(boundary row, PI index)` ABI does not preserve the physical columns used by the PI
bindings.  Those stronger properties therefore have their own predicates below.

Two existing passes instantiate the framework:

* E1 dead-column deletion gives an unconditional security refinement once its decidable shape
  certificate holds.  Its existing expansion is the security map.
* BilateralAggregationCompact is an unconditional strengthening (v3 -> v2), with reverse
  witness preservation only under `IdentityConstant`.  It is a target retraction, not a witness
  isomorphism; an explicit trace below proves the missing source round trip false.
-/
import Dregg2.Circuit.Emit.RotWideCompactE1
import Dregg2.Circuit.Emit.BilateralAggregationCompact

namespace Dregg2.Circuit.PassiveDescriptorOptimization

open Dregg2.Circuit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.RotWideCompactS2

set_option autoImplicit false

/-! ## 1. Public ABI: logical slots, not physical columns -/

/-- A public-binding slot is the stable ABI part of a PI binding.  The physical trace column is
intentionally absent: column compaction is allowed to move it. -/
structure PublicBindingSlot where
  row : VmRow
  piIndex : Nat
  deriving Repr, DecidableEq

/-- The full physical PI-binding site.  Equality of these is stronger than public ABI equality. -/
structure PublicBindingSite where
  row : VmRow
  column : Nat
  piIndex : Nat
  deriving Repr, DecidableEq

def bindingSlot? : VmConstraint2 → Option PublicBindingSlot
  | .base (.piBinding row _ piIndex) => some ⟨row, piIndex⟩
  | _ => none

def bindingSite? : VmConstraint2 → Option PublicBindingSite
  | .base (.piBinding row column piIndex) => some ⟨row, column, piIndex⟩
  | _ => none

/-- Ordered slots retain occurrence multiplicity as well as row/PI-index identity. -/
def publicBindingSlots (d : EffectVmDescriptor2) : List PublicBindingSlot :=
  d.constraints.filterMap bindingSlot?

/-- Ordered physical binding sites; a recolumning normally does not preserve this list. -/
def publicBindingSites (d : EffectVmDescriptor2) : List PublicBindingSite :=
  d.constraints.filterMap bindingSite?

/-- The descriptor-level public ABI: same PI-vector size and same ordered binding slots.
Names, trace widths, and binding columns are not part of this relation. -/
structure PublicABIEquivalent (source target : EffectVmDescriptor2) : Prop where
  piCount_eq : source.piCount = target.piCount
  bindingSlots_eq : publicBindingSlots source = publicBindingSlots target

namespace PublicABIEquivalent

theorem refl (d : EffectVmDescriptor2) : PublicABIEquivalent d d := ⟨rfl, rfl⟩

theorem symm {a b : EffectVmDescriptor2} (h : PublicABIEquivalent a b) :
    PublicABIEquivalent b a := ⟨h.piCount_eq.symm, h.bindingSlots_eq.symm⟩

theorem trans {a b c : EffectVmDescriptor2}
    (hab : PublicABIEquivalent a b) (hbc : PublicABIEquivalent b c) :
    PublicABIEquivalent a c :=
  ⟨hab.piCount_eq.trans hbc.piCount_eq,
   hab.bindingSlots_eq.trans hbc.bindingSlots_eq⟩

theorem binding_count_eq {a b : EffectVmDescriptor2} (h : PublicABIEquivalent a b) :
    (publicBindingSlots a).length = (publicBindingSlots b).length :=
  congrArg List.length h.bindingSlots_eq

end PublicABIEquivalent

/-! ## 2. The passive pass and its deliberately layered correctness contracts -/

/-- A passive pass is indexed by its source and target descriptors and carries total trace maps
both ways.  At this layer the maps need not preserve satisfaction or be inverses; those are
separate checked propositions below.  Both maps preserve the whole public assignment, stronger
than merely preserving its first `piCount` entries. -/
structure PassiveOptimization (source target : EffectVmDescriptor2) where
  toTarget : VmTrace → VmTrace
  toSource : VmTrace → VmTrace
  publicABI : PublicABIEquivalent source target
  toTarget_pub : ∀ t, (toTarget t).pub = t.pub
  toSource_pub : ∀ t, (toSource t).pub = t.pub

namespace PassiveOptimization

def identity (d : EffectVmDescriptor2) : PassiveOptimization d d where
  toTarget := id
  toSource := id
  publicABI := PublicABIEquivalent.refl d
  toTarget_pub := by intro t; rfl
  toSource_pub := by intro t; rfl

/-- Composition follows compilation order on `toTarget` and the reverse order on expansions. -/
def comp {a b c : EffectVmDescriptor2}
    (p : PassiveOptimization a b) (q : PassiveOptimization b c) :
    PassiveOptimization a c where
  toTarget := fun t => q.toTarget (p.toTarget t)
  toSource := fun t => p.toSource (q.toSource t)
  publicABI := p.publicABI.trans q.publicABI
  toTarget_pub := by
    intro t
    rw [q.toTarget_pub, p.toTarget_pub]
  toSource_pub := by
    intro t
    rw [p.toSource_pub, q.toSource_pub]

end PassiveOptimization

/-- Target acceptance implies source acceptance after expansion.  This is the exact one-way
security claim needed to justify replacing a verifier descriptor by the target. -/
def SecurityRefinement {source target : EffectVmDescriptor2}
    (p : PassiveOptimization source target) : Prop :=
  ∀ (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace),
    Satisfied2 hash target minit mfin maddrs t →
      Satisfied2 hash source minit mfin maddrs (p.toSource t)

/-- Source acceptance implies target acceptance after projection.  This is completeness, not
security; strengthening passes often have it only for an honest-witness invariant. -/
def CompletenessPreservation {source target : EffectVmDescriptor2}
    (p : PassiveOptimization source target) : Prop :=
  ∀ (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace),
    Satisfied2 hash source minit mfin maddrs t →
      Satisfied2 hash target minit mfin maddrs (p.toTarget t)

/-- Reverse preservation restricted to source witnesses produced by an admissible builder. -/
def ConditionalCompleteness {source target : EffectVmDescriptor2}
    (p : PassiveOptimization source target) (Admissible : VmTrace → Prop) : Prop :=
  ∀ (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace),
    Satisfied2 hash source minit mfin maddrs t → Admissible t →
      Satisfied2 hash target minit mfin maddrs (p.toTarget t)

/-- Two-way satisfaction transport.  This is deliberately not called an isomorphism. -/
structure SatisfiabilityPreservation {source target : EffectVmDescriptor2}
    (p : PassiveOptimization source target) : Prop where
  security : SecurityRefinement p
  completeness : CompletenessPreservation p

/-- Exact equality of every auxiliary table.  This implies preservation of table row
multiplicities; it is extra evidence because `Satisfied2` alone does not imply it. -/
def TablesExact (f : VmTrace → VmTrace) : Prop :=
  ∀ t tid, (f t).tf tid = t.tf tid

/-- Multiset preservation is weaker than `TablesExact`, but still stronger than satisfaction. -/
def TableMultisetsPreserved (f : VmTrace → VmTrace) : Prop :=
  ∀ t tid, List.Perm ((f t).tf tid) (t.tf tid)

theorem TablesExact.toMultisets {f : VmTrace → VmTrace} (h : TablesExact f) :
    TableMultisetsPreserved f := by
  intro t tid
  rw [h t tid]

/-- Exact carrier bookkeeping, separate from semantic preservation. -/
structure ExactCarrierTransport {source target : EffectVmDescriptor2}
    (p : PassiveOptimization source target) : Prop where
  toTarget_tables : TablesExact p.toTarget
  toSource_tables : TablesExact p.toSource
  toTarget_rows_length : ∀ t, (p.toTarget t).rows.length = t.rows.length
  toSource_rows_length : ∀ t, (p.toSource t).rows.length = t.rows.length

/-- Both total trace maps are mutually inverse on all traces.  Equisatisfiability does not entail
this: it relates accepted witnesses only and permits many-to-one canonicalization. -/
structure WitnessIsomorphism {source target : EffectVmDescriptor2}
    (p : PassiveOptimization source target) : Prop where
  sourceRoundTrip : ∀ t, p.toSource (p.toTarget t) = t
  targetRoundTrip : ∀ t, p.toTarget (p.toSource t) = t

/-- The common strengthening-pass shape: target witnesses embed into source witnesses and project
back exactly, while arbitrary source witnesses need not be canonical. -/
def TargetRetraction {source target : EffectVmDescriptor2}
    (p : PassiveOptimization source target) : Prop :=
  ∀ t, p.toTarget (p.toSource t) = t

theorem WitnessIsomorphism.toTarget_injective
    {source target : EffectVmDescriptor2} {p : PassiveOptimization source target}
    (h : WitnessIsomorphism p) : Function.Injective p.toTarget := by
  intro a b hab
  calc
    a = p.toSource (p.toTarget a) := (h.sourceRoundTrip a).symm
    _ = p.toSource (p.toTarget b) := congrArg p.toSource hab
    _ = b := h.sourceRoundTrip b

theorem TargetRetraction.toSource_injective
    {source target : EffectVmDescriptor2} {p : PassiveOptimization source target}
    (h : TargetRetraction p) : Function.Injective p.toSource := by
  intro a b hab
  calc
    a = p.toTarget (p.toSource a) := (h a).symm
    _ = p.toTarget (p.toSource b) := congrArg p.toTarget hab
    _ = b := h b

/-! ## 3. Identity, composition, and the exact logical consequences -/

theorem identity_security (d : EffectVmDescriptor2) :
    SecurityRefinement (PassiveOptimization.identity d) := by
  intro hash minit mfin maddrs t h
  exact h

theorem identity_completeness (d : EffectVmDescriptor2) :
    CompletenessPreservation (PassiveOptimization.identity d) := by
  intro hash minit mfin maddrs t h
  exact h

theorem security_comp {a b c : EffectVmDescriptor2}
    {p : PassiveOptimization a b} {q : PassiveOptimization b c}
    (hp : SecurityRefinement p) (hq : SecurityRefinement q) :
    SecurityRefinement (p.comp q) := by
  intro hash minit mfin maddrs t ht
  exact hp hash minit mfin maddrs _ (hq hash minit mfin maddrs t ht)

theorem completeness_comp {a b c : EffectVmDescriptor2}
    {p : PassiveOptimization a b} {q : PassiveOptimization b c}
    (hp : CompletenessPreservation p) (hq : CompletenessPreservation q) :
    CompletenessPreservation (p.comp q) := by
  intro hash minit mfin maddrs t ha
  exact hq hash minit mfin maddrs _ (hp hash minit mfin maddrs t ha)

theorem identity_preservation (d : EffectVmDescriptor2) :
    SatisfiabilityPreservation (PassiveOptimization.identity d) :=
  ⟨identity_security d, identity_completeness d⟩

theorem preservation_comp {a b c : EffectVmDescriptor2}
    {p : PassiveOptimization a b} {q : PassiveOptimization b c}
    (hp : SatisfiabilityPreservation p) (hq : SatisfiabilityPreservation q) :
    SatisfiabilityPreservation (p.comp q) :=
  ⟨security_comp hp.security hq.security,
   completeness_comp hp.completeness hq.completeness⟩

theorem identity_exactCarriers (d : EffectVmDescriptor2) :
    ExactCarrierTransport (PassiveOptimization.identity d) where
  toTarget_tables := by intro t tid; rfl
  toSource_tables := by intro t tid; rfl
  toTarget_rows_length := by intro t; rfl
  toSource_rows_length := by intro t; rfl

theorem exactCarriers_comp {a b c : EffectVmDescriptor2}
    {p : PassiveOptimization a b} {q : PassiveOptimization b c}
    (hp : ExactCarrierTransport p) (hq : ExactCarrierTransport q) :
    ExactCarrierTransport (p.comp q) where
  toTarget_tables := by
    intro t tid
    change (q.toTarget (p.toTarget t)).tf tid = t.tf tid
    rw [hq.toTarget_tables, hp.toTarget_tables]
  toSource_tables := by
    intro t tid
    change (p.toSource (q.toSource t)).tf tid = t.tf tid
    rw [hp.toSource_tables, hq.toSource_tables]
  toTarget_rows_length := by
    intro t
    change (q.toTarget (p.toTarget t)).rows.length = t.rows.length
    rw [hq.toTarget_rows_length, hp.toTarget_rows_length]
  toSource_rows_length := by
    intro t
    change (p.toSource (q.toSource t)).rows.length = t.rows.length
    rw [hp.toSource_rows_length, hq.toSource_rows_length]

theorem identity_witnessIsomorphism (d : EffectVmDescriptor2) :
    WitnessIsomorphism (PassiveOptimization.identity d) := ⟨by intro t; rfl, by intro t; rfl⟩

theorem witnessIsomorphism_comp {a b c : EffectVmDescriptor2}
    {p : PassiveOptimization a b} {q : PassiveOptimization b c}
    (hp : WitnessIsomorphism p) (hq : WitnessIsomorphism q) :
    WitnessIsomorphism (p.comp q) where
  sourceRoundTrip := by
    intro t
    change p.toSource (q.toSource (q.toTarget (p.toTarget t))) = t
    rw [hq.sourceRoundTrip, hp.sourceRoundTrip]
  targetRoundTrip := by
    intro t
    change q.toTarget (p.toTarget (p.toSource (q.toSource t))) = t
    rw [hp.targetRoundTrip, hq.targetRoundTrip]

theorem security_target_witness_implies_source
    {source target : EffectVmDescriptor2} {p : PassiveOptimization source target}
    (h : SecurityRefinement p)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) :
    (∃ t, Satisfied2 hash target minit mfin maddrs t) →
      ∃ s, Satisfied2 hash source minit mfin maddrs s := by
  rintro ⟨t, ht⟩
  exact ⟨p.toSource t, h hash minit mfin maddrs t ht⟩

theorem security_target_unsat_of_source_unsat
    {source target : EffectVmDescriptor2} {p : PassiveOptimization source target}
    (h : SecurityRefinement p)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (hunsat : ¬ ∃ s, Satisfied2 hash source minit mfin maddrs s) :
    ¬ ∃ t, Satisfied2 hash target minit mfin maddrs t := by
  intro ht
  exact hunsat (security_target_witness_implies_source h hash minit mfin maddrs ht)

theorem satisfiable_iff_of_preservation
    {source target : EffectVmDescriptor2} {p : PassiveOptimization source target}
    (h : SatisfiabilityPreservation p)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) :
    (∃ s, Satisfied2 hash source minit mfin maddrs s) ↔
      ∃ t, Satisfied2 hash target minit mfin maddrs t := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨p.toTarget s, h.completeness hash minit mfin maddrs s hs⟩
  · exact security_target_witness_implies_source h.security hash minit mfin maddrs

/-! ## 4. Generic PI-slot preservation under E1's column remapper -/

@[simp] theorem bindingSlot?_mapC2 (g : Nat → Nat) (c : VmConstraint2) :
    bindingSlot? (mapC2 g c) = bindingSlot? c := by
  cases c with
  | base c => cases c <;> rfl
  | lookup _ => rfl
  | memOp _ => rfl
  | mapOp _ => rfl
  | umemOp _ => rfl
  | proofBind _ => rfl
  | windowGate _ => rfl

theorem publicBindingSlots_mapC2 (g : Nat → Nat) (cs : List VmConstraint2) :
    (cs.map (mapC2 g)).filterMap bindingSlot? = cs.filterMap bindingSlot? := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.map_cons, List.filterMap_cons, bindingSlot?_mapC2, ih]

/-! ## 5. E1 dead-column deletion -/

namespace E1

open Dregg2.Circuit.Emit.RotWideCompactE1

/-- Old columns retained by the target, in old-column order. -/
def survivorCols (source : EffectVmDescriptor2) (ks : List Nat) : List Nat :=
  (List.range source.traceWidth).filter (fun c => !isKilled ks c)

/-- The canonical source-to-target row projection.  Security uses only the independently proved
target-to-source expansion; completeness/inverse claims for this projection are intentionally not
asserted by the E1 instance. -/
def projectRow (source : EffectVmDescriptor2) (ks : List Nat) (a : Assignment) : Assignment :=
  fun c => a ((survivorCols source ks).getD c c)

def projectTrace (source : EffectVmDescriptor2) (ks : List Nat) (t : VmTrace) : VmTrace :=
  { rows := t.rows.map (projectRow source ks), pub := t.pub, tf := t.tf }

theorem publicBindingSlots_compactE1 (source : EffectVmDescriptor2) (ks : List Nat) :
    publicBindingSlots (compactE1 source ks) = publicBindingSlots source := by
  exact publicBindingSlots_mapC2 (dropIdxG ks) source.constraints

def pass (source : EffectVmDescriptor2) (ks : List Nat) :
    PassiveOptimization source (compactE1 source ks) where
  toTarget := projectTrace source ks
  toSource := expandTraceG ks
  publicABI :=
    { piCount_eq := (compactE1_piCount source ks).symm
      bindingSlots_eq := (publicBindingSlots_compactE1 source ks).symm }
  toTarget_pub := by intro t; rfl
  toSource_pub := by intro t; rfl

/-- The existing E1 bridge is exactly the framework's one-way security contract. -/
theorem security (source : EffectVmDescriptor2) (ks : List Nat)
    (hok : compactE1Ok source ks = true) : SecurityRefinement (pass source ks) := by
  intro hash minit mfin maddrs t hsat
  exact compactE1_expand hash source ks minit mfin maddrs t hok hsat

/-- E1's two maps preserve auxiliary tables and row count exactly.  This still does not assert
that the source projection preserves satisfaction or is inverse to expansion. -/
theorem exactCarriers (source : EffectVmDescriptor2) (ks : List Nat) :
    ExactCarrierTransport (pass source ks) where
  toTarget_tables := by intro t tid; rfl
  toSource_tables := by intro t tid; rfl
  toTarget_rows_length := by intro t; simp [pass, projectTrace]
  toSource_rows_length := by intro t; simp [pass, expandTraceG]

end E1

/-! ## 6. The bilateral aggregation strengthening -/

namespace Bilateral

open Dregg2.Circuit.Emit.EffectVmEmitBilateralAgg
open Dregg2.Circuit.Emit.BilateralAggregationCompact

theorem publicABI : PublicABIEquivalent bilateralAggDescriptor bilateralAggDescriptorV3 := by
  constructor
  · rfl
  · rfl

/-- Same logical PI slots does not mean same physical layout: the last cell-count binding moves
from source column 86 to target column 51. -/
theorem physicalBindingLayout_changes :
    publicBindingSites bilateralAggDescriptor ≠ publicBindingSites bilateralAggDescriptorV3 := by
  decide

def pass : PassiveOptimization bilateralAggDescriptor bilateralAggDescriptorV3 where
  toTarget := contractT
  toSource := expandT
  publicABI := publicABI
  toTarget_pub := by intro t; rfl
  toSource_pub := by intro t; rfl

/-- v3 acceptance unconditionally refines v2 acceptance. -/
theorem security : SecurityRefinement pass := by
  intro hash minit mfin maddrs t hsat
  exact expand_satisfies hsat

/-- Reverse witness preservation is exactly conditional on the honest builder's identity carry. -/
theorem honestCompleteness : ConditionalCompleteness pass IdentityConstant := by
  intro hash minit mfin maddrs t hsat hid
  exact contract_preserves hsat hid

theorem exactCarriers : ExactCarrierTransport pass where
  toTarget_tables := by intro t tid; rfl
  toSource_tables := by intro t tid; rfl
  toTarget_rows_length := by intro t; simp [pass, contractT]
  toSource_rows_length := by intro t; simp [pass, expandT]

/-- Compact witnesses expand and contract back exactly. -/
theorem targetRetraction : TargetRetraction pass := contractT_expandT

/-- A physical source row with junk in the deleted expected block witnesses why the pass is not a
trace isomorphism, despite its target retraction and honest-witness completeness. -/
def noncanonicalRow : Assignment := fun c => if c = 49 then 1 else 0

def noncanonicalTrace : VmTrace :=
  { rows := [noncanonicalRow], pub := zeroAsg, tf := fun _ => [] }

theorem source_roundtrip_fails :
    pass.toSource (pass.toTarget noncanonicalTrace) ≠ noncanonicalTrace := by
  intro h
  have hc := congrArg (fun t => t.rows.getD 0 zeroAsg 49) h
  norm_num [pass, contractT, expandT, contractRow,
    Dregg2.Circuit.Emit.BilateralAggregationCompact.expandRow, noncanonicalTrace,
    noncanonicalRow, zeroAsg] at hc

theorem not_witnessIsomorphism : ¬ WitnessIsomorphism pass := by
  intro h
  exact source_roundtrip_fails (h.sourceRoundTrip noncanonicalTrace)

end Bilateral

#assert_axioms security_comp
#assert_axioms preservation_comp
#assert_axioms exactCarriers_comp
#assert_axioms witnessIsomorphism_comp
#assert_axioms security_target_unsat_of_source_unsat
#assert_axioms satisfiable_iff_of_preservation
#assert_axioms E1.security
#assert_axioms Bilateral.security
#assert_axioms Bilateral.not_witnessIsomorphism

end Dregg2.Circuit.PassiveDescriptorOptimization
