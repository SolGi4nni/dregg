/-
Generator for the FRI arity-2 fold-consistency template + its honest witness,
consumed by the Go emit-path replayer (chain/gnark/emitted_verifier_full.go
block 1: the `FriFoldRowArity2` case -> friFoldReplay -> ReplayTemplateWithWitness).

It renders the Lean-authored, ∀-refined `friFoldData s0 s1 β claimed bits`
(FriFoldEmit.lean -- `friFold_leaf_refines`: `gHolds (friFoldData …) (friFoldAsg …)
↔ foldCheckV … = true`, the deployed `friFoldCoreRef` fold `(e0+e1)/2 +
β·(e0−e1)·inv(2s)`) through the proof-covered `emitGnarkJson` renderer to the
committed `fri_fold_template.json` grammar the generic replayer reads, AND dumps
the Lean-generated honest assignment (`St.assigns`, var-index-ordered) to
`fri_fold_witness.json` -- the same object `friFold_leaf_refines` quantifies over.

The fixture is the apex-shrink round-0 fold: β = the real fixture
`expected_betas[0]` (chain/gnark/fixtures/apex_shrink_fri_real.json), 17 parent
bits = `log_global_max_height − 1` (= 18 − 1). The siblings + claimed are a
self-consistent honest fold (`claimed := foldCoreV s0 s1 β (invSV bits)`), so the
emitted R1CS is satisfiable by the dumped witness. The round-0 fold-beta operand
the transcript link binds (block1FoldBeta) is a SEPARATE flat-bank carrier; this
replay exercises the Lean-authored fold ARITHMETIC as real R1CS in place of the
hand-Go ExtMul cost chain.

This is NOT part of `lake build` (it lives under scripts/, outside the globbed
libs). Regenerate with, from the metatheory/ directory:

    lake env lean --run scripts/gen_fri_fold_template.lean
-/
import Dregg2.Circuit.Emit.GnarkVerifier.FriFoldEmit
import Dregg2.Circuit.Emit.GnarkVerifier.EmitJson

open Dregg2.Circuit.R1csFr
open Dregg2.Circuit.BabyBearFr
open Dregg2.Circuit.Emit.GnarkVerifier
open Dregg2.Circuit.Emit.GnarkVerifier.FriFold

/-- The real apex-shrink fixture round-0 fold beta (`expected_betas[0]`,
chain/gnark/fixtures/apex_shrink_fri_real.json). -/
def katBeta0 : ExtV := ⟨1176421496, 1958289700, 1400433207, 698068907⟩

/-- Two canonical sibling extension values (the FriFoldEmit §1 gold-vector siblings). -/
def foldS0 : ExtV := ⟨123, 456, 789, 1011⟩
def foldS1 : ExtV := ⟨2021, 2223, 2425, 2627⟩

/-- 17 parent-index bits — the round-0 fold's `|parentBits| = logGlobalMaxHeight − 1`
for the apex-shrink fixture (log_global_max_height = 18). -/
def foldBits : List Bool :=
  [true, false, true, true, false, true, false, false, true,
   true, false, true, false, true, true, false, true]

/-- The self-consistent claimed folded value: the deployed fold of the siblings at β. -/
def foldClaimed : ExtV := foldCoreV foldS0 foldS1 katBeta0 (invSV foldBits)

/-- The honest witness list — the minted assignment values in variable-index order for
the emitted `friFoldData` instance (the raw `St.assigns` the builder threads: canonicity
bit decompositions, the parent bits, the reduce quotient/remainder hints). -/
def honestAssigns : List Fr :=
  ((foldRoundM foldS0 foldS1 katBeta0 foldClaimed foldBits).run ⟨[], []⟩).2.assigns

/-- Render a witness list as the JSON array of decimal residues the Go loader reads. -/
def renderWitness (l : List Fr) : String :=
  "[" ++ String.intercalate "," (l.map (fun x => toString x.val)) ++ "]"

def main : IO Unit := do
  let json := emitGnarkJson (friFoldData foldS0 foldS1 katBeta0 foldClaimed foldBits)
  let tplPath := "../chain/gnark/emitted/fri_fold_template.json"
  IO.FS.writeFile tplPath json
  IO.println s!"template: wrote {json.length} bytes to {tplPath}"
  let wit := renderWitness honestAssigns
  let witPath := "../chain/gnark/emitted/fri_fold_witness.json"
  IO.FS.writeFile witPath wit
  IO.println s!"witness: wrote {honestAssigns.length} honest values to {witPath}"
