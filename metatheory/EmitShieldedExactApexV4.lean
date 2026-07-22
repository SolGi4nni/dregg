/-
# EmitShieldedExactApexV4 — byte source for the one-opening v4 apex relation

This deliberately stays separate from `EmitByName.lean` while the private-book GPU lane owns that
shared registry.  The registry cutover can import the same authoring module after that lane banks.

    lake env lean --run EmitShieldedExactApexV4.lean
-/
import Dregg2.Circuit.Emit.ShieldedExactApexV4Descriptor

def main : IO Unit :=
  IO.println Dregg2.Circuit.Emit.ShieldedExactApexV4Descriptor.descriptorJson
