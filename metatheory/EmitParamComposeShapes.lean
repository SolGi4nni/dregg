/-
`EmitParamComposeShapes` — emit the wire JSON of `paramComposeDesc` at EVERY shape the
`param-compose` Rust test corpus exercises, so each one can be byte-pinned in
`Dregg2/Circuit/Emit/ParamComposeGoldenShapes.lean` (and the large-census pair in
`ParamComposeGoldenCensus.lean`).

The shape census was taken by reading `param-compose/tests/{composition,size,turn_door,
prove_fold}.rs` for every `ComposeShape` that reaches `air::build`. Shapes that the tests
build only to WATCH REFUSED (`n1 p4 l3 k2`, over-shape witness; `n4 p8 l8 k6 i31`, vacuous
ordering tooth) are NOT here — a refusal is a witness/shape-guard property, not a descriptor.

Run:  lake env lean --run EmitParamComposeShapes.lean
Each shape prints one `@@@` header line (name, bounds, width, sites, constraint count)
followed by one line of wire JSON.
-/
import Dregg2.Circuit.Emit.ParamComposeEmit

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.ParamComposeEmit

/-- Every shape the Rust test corpus BUILDS, with the Lean `def` name it will be pinned under. -/
def censusShapes : List (String × ComposeShape) :=
  [ ("pcLeaf",          ⟨3, 4,  3,  2, 28⟩)   -- tests/{composition,turn_door,prove_fold,size}: `shape()`
  , ("pcN2P4L1K1",      ⟨2, 4,  1,  1, 28⟩)   -- composition: fuel-bound sweep
  , ("pcN5P6L4K3",      ⟨5, 6,  4,  3, 28⟩)   -- composition: fuel-bound sweep
  , ("pcN2P4L1K1I16",   ⟨2, 4,  1,  1, 16⟩)   -- composition: fuel-bound sweep, narrowed namespace
  , ("pcN4P4L3K2",      ⟨4, 4,  3,  2, 28⟩)   -- composition: VK-tracks-the-shape (n bumped)
  , ("pcN3P5L3K2",      ⟨3, 5,  3,  2, 28⟩)   -- composition: VK-tracks-the-shape (p bumped)
  , ("pcN3P4L4K2",      ⟨3, 4,  4,  2, 28⟩)   -- composition: VK-tracks-the-shape (l bumped)
  , ("pcN3P4L3K3",      ⟨3, 4,  3,  3, 28⟩)   -- composition: VK-tracks-the-shape (k bumped)
  , ("pcLeafI24",       ⟨3, 4,  3,  2, 24⟩)   -- composition: VK-tracks-the-shape (ib bumped)
  , ("pcN2P2L1K1",      ⟨2, 2,  1,  1, 28⟩)   -- size: census row "n2 p2 l1 k1" (NOT pcMin — ib=28)
  , ("pcRealisticI12",  ⟨4, 8,  8,  6, 12⟩)   -- size: identity-width sweep
  , ("pcRealisticI16",  ⟨4, 8,  8,  6, 16⟩)   -- size: identity-width sweep
  , ("pcRealisticI20",  ⟨4, 8,  8,  6, 20⟩)   -- size: identity-width sweep
  , ("pcRealisticI24",  ⟨4, 8,  8,  6, 24⟩)   -- size: identity-width sweep
  , ("pcSegN6",         ⟨6, 8, 12, 10, 28⟩)   -- size: documented-to-SEGMENT census row
  , ("pcSegN8",         ⟨8, 16, 16, 16, 28⟩)  -- size: documented-to-SEGMENT census row
  ]

def main : IO Unit := do
  for (nm, S) in censusShapes do
    let d := paramComposeDesc S
    IO.println s!"@@@\t{nm}\t{S.n}\t{S.p}\t{S.l}\t{S.k}\t{S.ib}\t{S.width}\t{S.hashSites}\t{d.constraints.length}\t{S.identityBitsSound}"
    IO.println (emitVmJson2 d)
