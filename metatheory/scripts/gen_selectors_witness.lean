/-
Generator for the honest STARK-selector witness fixtures consumed by the Go
witness-aware replayer test (chain/gnark/emitted_gadget_replay_witness_test.go:
ReplayTemplateWithWitness).

It dumps the Lean-generated honest assignment `selectorsAsg` (SelectorEmit.lean) — the
same object the `selectorTemplate_refines` ∀-theorem quantifies over — for each degree
bits the shrink uses, as a JSON array of decimal BN254 residues indexed by template
variable. Written byte-for-byte to chain/gnark/emitted/selectors_witness_db{N}.json,
alongside the committed template bytes selectors_db{N}.json (which are the emitted
`selectorsData` from the SAME instance, `emitSelectors db katZeta`).

This is NOT part of `lake build` (it lives under scripts/, outside the globbed libs).
Regenerate with, from the metatheory/ directory:

    lake env lean --run scripts/gen_selectors_witness.lean

The Go test then loads these fixtures, classifies the template's free-witness set
(Template.ClassifyVars), binds ζ + the free witnesses, and checks the replay solves
{isFirstRow,isLastRow,isTransition} bit-exact against computeStarkSelectorsRef — and
that a corrupted witness is unsatisfiable.
-/
import Dregg2.Circuit.Emit.GnarkVerifier.SelectorEmit

open Dregg2.Circuit.R1csFr
open Dregg2.Circuit.Emit.GnarkVerifier.Selector

/-- The honest witness list — the minted assignment values in variable-index order for
the committed `selectors_db{db}.json` instance (`emitSelectors db katZeta`). This is the
raw `St.assigns` the builder threads (the honest hint fill: canonicity bit
decompositions, the Fermat inverses, the range-checked ζ-squaring products). -/
def honestAssigns (db : Nat) : List Fr :=
  let s := selectorsV katZeta db
  ((selectorRoundM db katZeta s.1 s.2.1 s.2.2).run ⟨[], []⟩).2.assigns

/-- Render a witness list as the JSON array of decimal residues the Go loader reads. -/
def renderWitness (l : List Fr) : String :=
  "[" ++ String.intercalate "," (l.map (fun x => toString x.val)) ++ "]"

def main : IO Unit := do
  for db in [0, 9, 14, 15] do
    let s := honestAssigns db
    let path := s!"../chain/gnark/emitted/selectors_witness_db{db}.json"
    IO.FS.writeFile path (renderWitness s)
    IO.println s!"db{db}: wrote {s.length} honest witness values to {path}"
