/-
# Dregg2.Metatheory.GabbayDescriptorIR2PublicBoundary

The fixed three-entry descriptor proves an existential private witness relation.
This module records the exact public-binding boundary: the descriptor currently
has no public inputs or commitment sites, so an accepting trace cannot by itself
attest an independently named external table.
-/

import Dregg2.Metatheory.GabbayDescriptorIR2
import Dregg2.Tactics

namespace Dregg2.Metatheory.GabbayDescriptorIR2

set_option autoImplicit false

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Metatheory.GabbayMatrixSemantics

/-- The entire public *binding* surface of the current fixed descriptor is
empty: no public inputs, no hash sites, no v1 range carrier.  The descriptor
DOES carry six graduated 30-bit range lookups (the teeth that make acceptance
sound on the wire), but a range tooth binds no external name, so it does not
close the statement gap this module records. -/
theorem descriptor_public_surface_empty :
    compileDescriptor.piCount = 0 /\
      compileDescriptor.hashSites = [] /\
      compileDescriptor.ranges = [] /\
      compileDescriptor.constraints.length = 15 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Every constructed table trace exposes the same public assignment, regardless
of its private matrix entries. -/
theorem constructed_traces_publicly_indistinguishable
    (left right : ThreeEntryTable) :
    (traceOf left).pub = (traceOf right).pub := rfl

/-- There is an accepting trace while an independently named external table is
false.  This is not a contradiction in `Satisfied2`: that external table is not
part of the present descriptor statement.  It is the formal reason a later API
must bind the claimed table through public inputs or a commitment. -/
theorem accepting_trace_does_not_attest_external_table
    (hash : List Int -> Int) :
    (∃ trace,
      Satisfied2 hash compileDescriptor (fun _ => 0)
          (fun _ => ((0 : Int), 0)) [] trace) /\
      ¬ Holds (sourceValuation tamperedEntries) 0 successorSkolemFormula := by
  exact ⟨⟨traceOf successorEntries, successor_trace_satisfies hash⟩,
    tamperedEntries_not_holds⟩

#assert_all_clean [
  descriptor_public_surface_empty,
  constructed_traces_publicly_indistinguishable,
  accepting_trace_does_not_attest_external_table
]

end Dregg2.Metatheory.GabbayDescriptorIR2
