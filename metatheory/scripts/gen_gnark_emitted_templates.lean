/-
Generator for the Lean-EMITTED gnark artifacts that are NOT the commit-phase Merkle
templates (those have their own generator, `scripts/gen_merkle_templates.lean`).

It renders, through the proof-covered `emitGnarkJson` byte grammar (EmitFaithful
`emit_faithful` covers the renderer: it adds no constraint content), the templates
the Go emit-path replayer consumes:

  * `leafhash_template.json`        — `leafHashData 8`, the per-class MMCS leaf-hash
                                      ReplayTemplate (rows-in → leaf-out, no `select`).
  * `inputopen_batch_template.json` — `batchData` at the deployed round-1 (quotient)
                                      shape.
  * `inputopen_batch_r{0,2,3}.json` — the same `batchData` at the trace / preprocessed
                                      / permutation round shapes.
  * `verifier_full.json`            — `verifierFullJson`, the COMPACT full-verifier
                                      descriptor at `apexShrinkShape`.
  * `selectors_db{N}.json`          — `selectorsDbJson`, one STARK Lagrange-selector
                                      template per DISTINCT `apexShrinkShape.degreeBits`
                                      entry, at the real fixture ζ (`katZeta`).

Every shape constant is read from `apexShrinkShape` / `katMask` (EmitJson.lean,
InputOpenBatchEmit.lean §11-§12), which are themselves the apex-shrink fixture's own
numbers (`chain/gnark/fixtures/apex_shrink_fri_real.json`). NEVER hand-edit the emitted
JSON: re-run this generator.

The selector WITNESS fixtures that pair with `selectors_db{N}.json` have their own
generator, `scripts/gen_selectors_witness.lean` — run it too after a re-mint.

It also prints, for each artifact, the exact byte length and the FNV-1a digest — those
are the `#guard` byte pins at the end of InputOpenBatchEmit.lean §12, so a re-emit's
pins are readable straight off this run — plus the structure counts those pins cover.

This is NOT part of `lake build` (it lives under scripts/, outside the globbed libs).
The batch templates are multi-MB emissions; expect minutes. Regenerate with, from the
metatheory/ directory:

    lake env lean --run scripts/gen_gnark_emitted_templates.lean

With no arguments it emits everything (and prints the structure counts). Pass one or
more NAME PREFIXES to emit only those — the batch templates are the expensive ones, so
`… scripts/gen_gnark_emitted_templates.lean selectors verifier_full` re-mints just the
cheap artifacts:

    lake env lean --run scripts/gen_gnark_emitted_templates.lean selectors
-/
import Dregg2.Circuit.Emit.GnarkVerifier.InputOpenBatchEmit
import Dregg2.Circuit.Emit.GnarkVerifier.SelectorEmit
import Dregg2.Circuit.Emit.GnarkVerifier.EmitJson

open Dregg2.Circuit.Emit.GnarkVerifier
open Dregg2.Circuit.Emit.GnarkVerifier.InputOpenBatch

/-- Write one emitted artifact and print its byte pins (length + FNV-1a). The body is a
THUNK so a filtered run never forces the multi-MB strings it is skipping. -/
def emitOne (sel : String → Bool) (name : String) (json : Unit → String) : IO Unit := do
  if sel name then
    let s := json ()
    let path := s!"../chain/gnark/emitted/{name}"
    IO.FS.writeFile path s
    IO.println s!"{name}: {s.length} bytes  fnv1a={fnv1a s}"

def main (args : List String) : IO Unit := do
  let sel (name : String) : Bool := args.isEmpty || args.any (fun a => name.startsWith a)
  emitOne sel "leafhash_template.json" (fun _ => leafHashTemplateJson)
  emitOne sel "inputopen_batch_template.json" (fun _ => batchTemplateJson)
  emitOne sel "inputopen_batch_r0.json" (fun _ => batchTemplateR0Json)
  emitOne sel "inputopen_batch_r2.json" (fun _ => batchTemplateR2Json)
  emitOne sel "inputopen_batch_r3.json" (fun _ => batchTemplateR3Json)
  emitOne sel "verifier_full.json" (fun _ => verifierFullJson)
  -- One selector template per DISTINCT degree bits the shrink uses, in fixture order.
  for db in apexShrinkShape.degreeBits.eraseDups do
    emitOne sel s!"selectors_db{db}.json" (fun _ => Selector.selectorsDbJson db)
  if !args.isEmpty then return
  IO.println ""
  IO.println s!"commitMerkleDepths apexShrinkShape = {commitMerkleDepths apexShrinkShape}"
  IO.println s!"(leafHashCircuit 8).asserts.length  = {(leafHashCircuit 8).asserts.length}"
  IO.println s!"(leafHashCircuit 16).asserts.length = {(leafHashCircuit 16).asserts.length}"
  IO.println s!"(leafHashData 8).publicInputs.length = {(leafHashData 8).publicInputs.length}"
  IO.println s!"(batchCircuit [8, 16, 16, 8] 19 katMask).asserts.length = \
{(batchCircuit [8, 16, 16, 8] 19 katMask).asserts.length}"
  IO.println ""
  IO.println "verifierFullJson (the §4 golden pin, verbatim):"
  IO.println verifierFullJson
