/-
# Deck Descent emit driver

A separate driver from `EmitMain.lean` for one reason: the descent descriptor is
not yet in the curator-signed POAG1 bundle, and it must not be written into
`poa/artifacts/poag1/`.  `scripts/check-poag1-artifacts.sh` refuses any file
under that directory it does not expect, and enrolling a fourth game changes the
content root, so the manifest bytes change and the curator signature must be
re-taken.  That is a rebuild and it is wanted — it is simply a curator act, and
this driver is not the curator.

So the bytes go to a PENDING directory the design gate can be pointed at:

    POA_DESCENT_OUT=poa/artifacts/poag1-pending \
      lake env lean --run Dregg2/Games/PathOfAngels/DeckDescentEmitMain.lean

The driver fails closed: it validates the bytes and checks them against the
kernel BEFORE writing, so a descriptor that does not refine `DeckDescent` never
reaches the disk.  The same four checks are `#assert_compiled` theorems in
`DeckDescentEmit`; running them here as well costs a second and means an
operator who skips the build still cannot ship a wrong table.
-/
import Dregg2.Games.PathOfAngels.DeckDescentEmit

open Dregg2.Games.PathOfAngels.DeckDescentEmit

def writeAtomic (path : System.FilePath) (contents : String) : IO Unit := do
  let staged := System.FilePath.mk (path.toString ++ ".partial")
  IO.FS.writeFile staged contents
  IO.FS.rename staged path

def orThrow (what : String) : Except String Unit → IO Unit
  | .ok () => pure ()
  | .error err => throw (IO.userError s!"{what}: {err}")

def main : IO Unit := do
  let dir := System.FilePath.mk
    ((← IO.getEnv "POA_DESCENT_OUT").getD "/tmp/poag1-pending")
  let bytes := deckDescentDescriptorJson
  orThrow "POAG1 descent descriptor is not the declared schema"
    (validateDescentDescriptor bytes)
  orThrow "POAG1 descent table does not refine the kernel"
    (descentTableRefinesKernel bytes)
  orThrow "POAG1 descent state views do not refine the kernel"
    (descentViewsRefineKernel bytes)
  orThrow "POAG1 descent practice family does not refine the kernel"
    (descentPracticeRefinesKernel bytes)
  IO.FS.createDirAll (dir / "games")
  writeAtomic (dir / "games" / "deck-descent.json") bytes
  IO.println s!"wrote {dir}/games/deck-descent.json ({bytes.length} bytes, \
{descentStates.length} states, {descentRows.length} rows)"
