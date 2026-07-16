/-
# EmitNonRevocationAdjacency — byte source for deployed sorted-tree non-revocation

Run from `metatheory/`:

    lake env lean --run EmitNonRevocationAdjacency.lean

The constraints are authored and proved in `NonRevocationAdjacencyEmit.lean`; this program only
serializes that descriptor as `<name>\t<emitVmJson2 descriptor>` for the checked-in Rust golden.
-/
import Dregg2.Circuit.Emit.NonRevocationAdjacencyEmit

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.NonRevocationAdjacencyEmit (nonRevocationAdjacencyDesc)

def main : IO Unit :=
  IO.println s!"{nonRevocationAdjacencyDesc.name}\t{emitVmJson2 nonRevocationAdjacencyDesc}"
