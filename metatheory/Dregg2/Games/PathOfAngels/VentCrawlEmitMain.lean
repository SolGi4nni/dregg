/-
# Vent Crawl emit driver

A separate driver from `EmitMain.lean` for the reason `DeckDescentEmitMain`
gives one game earlier: the vent-crawl descriptor is not in the curator-signed
POAG1 bundle, and it must not be written into `poa/artifacts/poag1/`.
`scripts/check-poag1-artifacts.sh` refuses any file under that directory it does
not expect, and enrolling another game changes the content root, so the manifest
bytes change and the curator signature must be re-taken.  That is a rebuild and
it is wanted — it is simply a curator act, and this driver is not the curator.

So the bytes go wherever they are pointed, defaulting to a pending directory the
design gate can be aimed at:

    POA_VENT_OUT=poa/artifacts/poag1-pending \
      lake env lean --run Dregg2/Games/PathOfAngels/VentCrawlEmitMain.lean

The driver fails closed: it validates the bytes and checks them against the
kernel BEFORE writing, so a descriptor that does not refine `VentCrawl` never
reaches the disk.  The same three checks are `#assert_compiled` theorems in
`VentCrawlEmit`; running them here as well costs a second and means an operator
who skips the build still cannot ship a wrong table.
-/
import Dregg2.Games.PathOfAngels.VentCrawlEmit

open Dregg2.Games.PathOfAngels.VentCrawlEmit

def writeAtomic (path : System.FilePath) (contents : String) : IO Unit := do
  let staged := System.FilePath.mk (path.toString ++ ".partial")
  IO.FS.writeFile staged contents
  IO.FS.rename staged path

def orThrow (what : String) : Except String Unit → IO Unit
  | .ok () => pure ()
  | .error err => throw (IO.userError s!"{what}: {err}")

def main : IO Unit := do
  let dir := System.FilePath.mk
    ((← IO.getEnv "POA_VENT_OUT").getD "/tmp/poag1-pending")
  let bytes := ventCrawlDescriptorJson
  orThrow "POAG1 vent-crawl descriptor is not the declared schema"
    (validateVentCrawlDescriptor bytes)
  orThrow "POAG1 vent-crawl table does not refine the kernel"
    (ventCrawlTableRefinesKernel bytes)
  orThrow "POAG1 vent-crawl state views do not refine the kernel"
    (ventCrawlViewsRefineKernel bytes)
  IO.FS.createDirAll (dir / "games")
  writeAtomic (dir / "games" / "vent-crawl.json") bytes
  IO.println s!"wrote {dir}/games/vent-crawl.json ({bytes.length} bytes, \
{ventStates.length} states, {ventRows.length} rows)"
