/-
# Artificer Logic emit driver

A separate driver from `EmitMain.lean` for one reason: the artificer descriptor
is not yet in the curator-signed POAG1 bundle, and it must not be written into
`poa/artifacts/poag1/`.  `scripts/check-poag1-artifacts.sh` refuses any file
under that directory it does not expect, and enrolling another game changes the
content root, so the manifest bytes change and the curator signature must be
re-taken.  That is a rebuild and it is wanted — it is simply a curator act, and
this driver is not the curator.

So the bytes go to a PENDING directory the design gate can be pointed at:

    POA_ARTIFICER_OUT=poa/artifacts/poag1-pending \
      lake env lean --run Dregg2/Games/PathOfAngels/ArtificerLogicEmitMain.lean

The driver fails closed: it validates the bytes, checks the manual against the
kernel, checks that the published manual has no indistinguishable pair, and
checks every row and view against the kernel — all BEFORE writing.  A descriptor
that does not refine `ArtificerLogic` never reaches the disk.

⚑ The distinguishability check is in this list deliberately.  It is the one
failure that a row-by-row differential cannot see (`synonym_manual_is_caught`
proves that: the hostile manual passes the table check and fails only here), and
it is the failure that makes a run unwinnable by a perfect player.
-/
import Dregg2.Games.PathOfAngels.ArtificerLogicEmit

open Dregg2.Games.PathOfAngels.ArtificerLogicEmit

def writeAtomic (path : System.FilePath) (contents : String) : IO Unit := do
  let staged := System.FilePath.mk (path.toString ++ ".partial")
  IO.FS.writeFile staged contents
  IO.FS.rename staged path

def orThrow (what : String) : Except String Unit → IO Unit
  | .ok () => pure ()
  | .error err => throw (IO.userError s!"{what}: {err}")

def main : IO Unit := do
  let dir := System.FilePath.mk
    ((← IO.getEnv "POA_ARTIFICER_OUT").getD "/tmp/poag1-pending")
  let bytes := artificerLogicDescriptorJson
  orThrow "POAG1 artificer descriptor is not the declared schema"
    (validateLogicDescriptor bytes)
  orThrow "POAG1 artificer manual does not refine the kernel"
    (logicManualRefinesKernel bytes)
  orThrow "POAG1 artificer manual holds an indistinguishable pair"
    (logicManualIsDistinguishing bytes)
  orThrow "POAG1 artificer table does not refine the kernel"
    (logicTableRefinesKernel bytes)
  orThrow "POAG1 artificer state views do not refine the kernel"
    (logicViewsRefineKernel bytes)
  IO.FS.createDirAll (dir / "games")
  writeAtomic (dir / "games" / "artificer-logic.json") bytes
  IO.println s!"wrote {dir}/games/artificer-logic.json ({bytes.length} bytes, \
{logicStates.length} states, {logicRows.length} rows)"
