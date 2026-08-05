/-
# Dregg2.Circuit.Emit.EmitPreimageJson — the `--run` emit driver for the Poseidon-preimage circuit.

Thin executable: writes `KimchiPreimageCircuit`'s two artifacts —

  * `preimage.json`  — the circuit: `Poseidon.hash([x]) = c` with `c` the one PUBLIC input.
  * `unbound.json`   — the CONTROL: same gates, same coefficients, same witness, no binding wire.

to `$DREGG_PREIMAGE_OUT` (default `/tmp/pickles-preimage/`), which the
`pickles-preimage-harness` Rust crate proves + verifies through `kimchi::verifier`.

    cd metatheory
    lake build Dregg2.Circuit.Emit.KimchiPreimageCircuit
    lake env lean --run Dregg2/Circuit/Emit/EmitPreimageJson.lean

House Law #1: the CIRCUIT is Lean-authored; `proof-systems` (the harness) is the Rust PROVER.
-/
import Dregg2.Circuit.Emit.KimchiPreimageCircuit

open Dregg2.Circuit.Emit.KimchiPreimageCircuit

/-- Write ATOMICALLY: stage beside the target, then rename into place. Same reason as
`EmitWrapMainJson.writeAtomic` — a reader cannot tell a complete artifact from one whose writer
died mid-`String`, because both are a file with the right name. -/
def writeAtomic (path contents : String) : IO Unit := do
  let staged := path ++ ".partial"
  IO.FS.writeFile staged contents
  IO.FS.rename staged path

def main : IO Unit := do
  let dir := (← IO.getEnv "DREGG_PREIMAGE_OUT").getD "/tmp/pickles-preimage"
  IO.FS.createDirAll dir
  -- ⚑ THE EMISSION'S OWN OBLIGATIONS, DISCHARGED BEFORE THE WRITE. Each of these is a kernel
  -- theorem in `KimchiPreimageCircuit` at THIS shape; they are re-checked here because a future
  -- edit to the gate list would move the emitted object while the theorems still name the old
  -- indices, and a refusal that lands after `writeAtomic` is not fail-closed.
  if preimagePlaced.length != NROWS then
    throw (IO.userError s!"⚑ ROW COUNT: placed {preimagePlaced.length} rows, header says {NROWS}")
  if preimageWitness.length != 15 then
    throw (IO.userError s!"⚑ WITNESS WIDTH: {preimageWitness.length} columns, kimchi wants 15")
  if preimageWitness.any (fun c => c.length != NROWS) then
    throw (IO.userError s!"⚑ WITNESS HEIGHT: a column is not {NROWS} long")
  if preimagePublic.length != PUB then
    throw (IO.userError s!"⚑ PUBLIC VECTOR: {preimagePublic.length} entries for {PUB} public words")
  -- ⚑ THE BINDING WIRE, READ OFF THE EMITTED OBJECT. Without it the artifact still proves and
  -- still verifies — it just stops saying anything about `c`. That is precisely the failure a
  -- shape check cannot see, so it is checked by value here and by `decide` in the kernel there.
  if wireAt 0 0 != ⟨12, 0⟩ || wireAt 12 0 != ⟨0, 0⟩ then
    throw (IO.userError s!"⚑ THE BINDING WIRE IS GONE: σ(0,0) = {repr (wireAt 0 0)}, \
      σ(12,0) = {repr (wireAt 12 0)}. The public word would be tied to nothing the circuit \
      computes — refusing rather than emitting it.")
  if wireAt 1 1 != ⟨13, 0⟩ || wireAt 1 2 != ⟨13, 3⟩ then
    throw (IO.userError s!"⚑ THE IDLE-LANE PINS ARE GONE: σ(1,1) = {repr (wireAt 1 1)}, \
      σ(1,2) = {repr (wireAt 1 2)}. The statement would weaken to `∃ s, perm(s)₀ = c` \
      — refusing rather than emitting it.")
  -- ⚑ …and the CONTROL must actually be a control: same shape, missing wire.
  if wiresOf unboundPlaced 0 0 != ⟨0, 0⟩ then
    throw (IO.userError "⚑ THE CONTROL IS NOT A CONTROL: its public cell is wired.")
  writeAtomic s!"{dir}/preimage.json" preimageJson
  writeAtomic s!"{dir}/unbound.json" unboundJson
  IO.println s!"EmitPreimageJson: wrote {dir}/preimage.json and {dir}/unbound.json"
  IO.println s!"  rows = {preimagePlaced.length} (1 public + 13)  witness = \
    {preimageWitness.length} x {NROWS}  public words = {PUB}"
  IO.println s!"  secret  x = {xSecret}"
  IO.println s!"  public  c = {digest}   (= Ref.hash [x] = o1js Poseidon.hash([x]))"
  IO.println s!"  binding: sigma(0,0) = {repr (wireAt 0 0)}, sigma(12,0) = {repr (wireAt 12 0)}"
  IO.println s!"  control: sigma(0,0) = {repr (wiresOf unboundPlaced 0 0)} (a singleton)"
