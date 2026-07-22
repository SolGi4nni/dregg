/-
# EmitShieldedWholeNoteSwapSubstrate — byte source for the narrow one-opening barter relation

This deliberately stays separate from `EmitByName.lean` while the private-book GPU lane owns that
shared registry.  The registry cutover can import the same authoring module after that lane banks.

    lake env lean --run EmitShieldedWholeNoteSwapSubstrate.lean
-/
import Dregg2.Circuit.Emit.ShieldedWholeNoteSwapSubstrateDescriptor

def main : IO Unit :=
  IO.println Dregg2.Circuit.Emit.ShieldedWholeNoteSwapSubstrateDescriptor.descriptorJson
