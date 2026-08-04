/-
# POAG1 emit driver

The driver has three fail-closed phases so the external SHA-256 primitive can
measure bytes without making the host an author of game semantics:

  POA_EMIT_MODE=descriptors writes the three digest-independent game descriptors
  POA_EMIT_MODE=artifacts  writes the five canonical artifacts
  POA_EMIT_MODE=bundle     writes artifacts plus the exact self-ingested manifest

scripts/check-poag1-artifacts.sh performs these phases in order, measures SHA-256
over the bytes each preceding phase produced, then byte-compares the complete
result with the checked-in bundle.
-/
import Dregg2.Games.PathOfAngels.Emit

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.Emit

def requiredEnv (name : String) : IO String := do
  match ← IO.getEnv name with
  | some value =>
      if value.isEmpty then throw (IO.userError s!"{name} is empty") else pure value
  | none => throw (IO.userError s!"{name} is required")

def requiredDigest (name : String) : IO (String × Digest32) := do
  let value ← requiredEnv name
  match parseDigest32? value with
  | some digest => pure (value, digest)
  | none => throw (IO.userError s!"{name} must be exactly sha256:<64 lowercase hex>")

def requiredBytes32Hex (name : String) : IO (String × Digest32) := do
  let value ← requiredEnv name
  match parseBytes32Hex? value with
  | some digest => pure (value, digest)
  | none => throw (IO.userError s!"{name} must be exactly 64 lowercase hex digits")

def requiredHash (name : String) : IO String := do
  let value ← requiredEnv name
  if validSha256 value then pure value
  else throw (IO.userError s!"{name} must be exactly sha256:<64 lowercase hex>")

def writeAtomic (path : System.FilePath) (contents : String) : IO Unit := do
  let staged := System.FilePath.mk (path.toString ++ ".partial")
  IO.FS.writeFile staged contents
  IO.FS.rename staged path

def writeArtifacts (dir : System.FilePath)
    (federation source contentRoot : Digest32) (digests : GameContentDigests) : IO Unit := do
  for artifact in canonicalArtifacts federation source contentRoot digests do
    let path := dir / artifact.path
    if let some parent := path.parent then IO.FS.createDirAll parent
    writeAtomic path artifact.contents

def emitDescriptors (dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll (dir / "games")
  writeAtomic (dir / "games" / "relay-repair.json") relayDescriptorJson
  writeAtomic (dir / "games" / "salvage-lock.json") salvageDescriptorJson
  writeAtomic (dir / "games" / "signal-triangulation.json") signalDescriptorJson

def requiredGameDigests : IO GameContentDigests := do
  pure {
    signal := (← requiredDigest "POA_SIGNAL_SHA256").2
    relay := (← requiredDigest "POA_RELAY_SHA256").2
    salvage := (← requiredDigest "POA_SALVAGE_SHA256").2
  }

def main : IO Unit := do
  let dir := System.FilePath.mk ((← IO.getEnv "POA_EMIT_OUT").getD "/tmp/poag1")
  IO.FS.createDirAll dir
  match (← IO.getEnv "POA_EMIT_MODE").getD "bundle" with
  | "descriptors" =>
      emitDescriptors dir
  | "artifacts" =>
      let (_, federation) ← requiredBytes32Hex "POA_FEDERATION_ID"
      let (_, source) ← requiredDigest "POA_SOURCE_SHA256"
      let (_, contentRoot) ← requiredDigest "POA_CONTENT_ROOT_SHA256"
      let digests ← requiredGameDigests
      writeArtifacts dir federation source contentRoot digests
  | "bundle" =>
      let (_, federation) ← requiredBytes32Hex "POA_FEDERATION_ID"
      let (sourceString, source) ← requiredDigest "POA_SOURCE_SHA256"
      let (_, contentRoot) ← requiredDigest "POA_CONTENT_ROOT_SHA256"
      let digests ← requiredGameDigests
      let hashes : ArtifactHashes := {
        schema := ← requiredHash "POA_SCHEMA_SHA256"
        catalog := ← requiredHash "POA_CATALOG_SHA256"
        relay := ← requiredHash "POA_RELAY_SHA256"
        salvage := ← requiredHash "POA_SALVAGE_SHA256"
        signal := ← requiredHash "POA_SIGNAL_SHA256"
      }
      writeArtifacts dir federation source contentRoot digests
      let manifest := manifestFor sourceString federation source contentRoot digests hashes
      let bytes := manifest.toJson
      match ingestManifest sourceString federation source contentRoot digests hashes bytes with
      | .ok accepted =>
          if accepted = manifest then writeAtomic (dir / "manifest.json") bytes
          else throw (IO.userError "POAG1 self-ingest returned a different manifest")
      | .error err => throw (IO.userError s!"POAG1 self-ingest refused: {err}")
  | other =>
      throw (IO.userError s!"POA_EMIT_MODE={other} is invalid; expected descriptors|artifacts|bundle")
