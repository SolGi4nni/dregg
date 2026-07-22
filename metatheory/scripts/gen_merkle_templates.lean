/-
Generator for the commit-phase Merkle-path opening templates consumed by the Go
emit-path replayer (chain/gnark/emitted_verifier_full.go block 2: the
`VerifyMerklePathBn254` case → `ReplayClosed`).

It renders the Lean-authored, ∀-refined `merklePathData d` (MerkleEmit.lean —
`merkle_path_refines`: `gHolds (merklePathData |sibs|) (pathAsg …) ↔ refRoot leaf
(sibs.zip bits) = root`, the deployed `merkleBn254RefRoot` walk) through the
proof-covered `emitGnarkJson` renderer (EmitFaithful `emit_faithful` covers the
byte grammar) to the committed `*_template.json` grammar the generic ReplayClosed
driver reads. One file per commit-phase depth the apex-shrink fixture opens
(`commitMerkleDepths apexShrinkShape = [17,16,…,3]`).

Layout (MerkleEmit.lean §5): `var 0` = leaf, `var 1` = root, `var (2+2i)` =
sibling i, `var (2+2i+1)` = path bit i; the Poseidon internals mint from `2+2d`.
ReplayClosed binds leaf/root/siblings/bits by index and the define-chain solves
the internals, keeping the per-level booleanity `bit·bit = bit` asserts and the
final recomputed-root == root check.

This is NOT part of `lake build` (it lives under scripts/, outside the globbed
libs). Regenerate with, from the metatheory/ directory:

    lake env lean --run scripts/gen_merkle_templates.lean
-/
import Dregg2.Circuit.Emit.GnarkVerifier.MerkleEmit
import Dregg2.Circuit.Emit.GnarkVerifier.EmitJson

open Dregg2.Circuit.Emit.GnarkVerifier

/-- The commit-phase Merkle depths the deployed apex-shrink descriptor opens
(`EmitJson.commitMerkleDepths apexShrinkShape` = `[17,16,…,3]`). -/
def merkleDepths : List Nat := commitMerkleDepths apexShrinkShape

def main : IO Unit := do
  for d in merkleDepths do
    let json := emitGnarkJson (Merkle.merklePathData d)
    let path := s!"../chain/gnark/emitted/merkle_path_bn254_d{d}.json"
    IO.FS.writeFile path json
    IO.println s!"d{d}: wrote {json.length} bytes to {path}"
