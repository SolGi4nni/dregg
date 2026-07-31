/-
# EmitExactNullifierAafiRotatedState

Byte emitter for the ADDITIVE, UNREGISTERED FNSP-v3 exact-nullifier rotated-state descriptor.

This executable deliberately does not participate in the deployed rotation registry.  It emits the
canonical IR-v2 JSON consumed by Rust's `descriptor_ir2::parse_vm_descriptor2`; the companion
`scripts/emit-exact-nullifier-aafi-rotated-state.py` pins and stages those exact bytes without
changing a verifier key, epoch selector, or deployed descriptor fingerprint.

Run from `metatheory/`:

  lake env lean --run EmitExactNullifierAafiRotatedState.lean

No wrapper JSON and no trailing newline are added: stdout is exactly `emitVmJson2` of the Lean
definition below.
-/

import Dregg2.Circuit.Emit.ExactNullifierAafiRotatedStateWeld

namespace Dregg2.Circuit.Emit.ExactNullifierAafiRotatedStateEmit

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.ExactNullifierAafiRotatedStateWeld

/-- The sole staged wire value.  Keeping this as a named definition makes the correspondence
theorem below definitional rather than a second, re-authored serialization path. -/
def descriptorJson : String :=
  emitVmJson2 exactNullifierAafiRotatedStateDescriptor

/-- The emitted bytes are definitionally the canonical IR-v2 serialization of the welded Lean
descriptor.  The external staging tool pins the SHA-256 of these exact bytes. -/
theorem descriptorJson_eq_canonical_emit :
    descriptorJson = emitVmJson2 exactNullifierAafiRotatedStateDescriptor := rfl

-- The production geometry and ABI are checked at the emitter boundary as well as in the author.
#guard exactNullifierAafiRotatedStateDescriptor.name ==
  "faithful-note-spend-v3-plan::exact-aafi-fns3-rotated-wide-state"
#guard exactNullifierAafiRotatedStateDescriptor.traceWidth == 3804
#guard exactNullifierAafiRotatedStateDescriptor.piCount == 76
#guard exactNullifierAafiRotatedStateDescriptor.constraints.length == 1274
#guard exactNullifierAafiRotatedStateDescriptor.tables.map (fun t => t.id) ==
  [.main, .custom 4, .poseidon2, .custom 79, .custom 80]
#guard descriptorJson.startsWith
  "{\"name\":\"faithful-note-spend-v3-plan::exact-aafi-fns3-rotated-wide-state\",\"ir\":2,\"trace_width\":3804,\"public_input_count\":76"
#guard descriptorJson.endsWith "\"hash_sites\":[],\"ranges\":[]}"

#assert_axioms descriptorJson_eq_canonical_emit

end Dregg2.Circuit.Emit.ExactNullifierAafiRotatedStateEmit

def main : IO Unit :=
  IO.print Dregg2.Circuit.Emit.ExactNullifierAafiRotatedStateEmit.descriptorJson
