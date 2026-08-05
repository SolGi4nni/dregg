/-
# Dregg2.Circuit.Emit.EmitPreimageJson — the `--run` emit driver for the Poseidon-preimage circuit.

Thin executable: writes `KimchiPreimageCircuit`'s artifacts —

  * `preimage.json`     — the circuit: `Poseidon.hash([x]) = c` with `c` the one PUBLIC input.
  * `unbound.json`      — the CONTROL: same gates, same coefficients, same witness, no binding wire.
  * `preimage_ae.json`  — ⚑ the SAME circuit with its binding re-authored through `assertEqual`
                          (`KimchiAssertEqual`): the output row exposes a variable of its own and the
                          equality is an appended VALUE. Byte-identical to `preimage.json` — proved
                          by `the_reauthored_json_is_byte_identical`, and MEASURED by the harness's
                          `assert_eq!` on the two raw files.
  * `unbound_ae.json`   — its control: the same gate list with the `assertEqual` REMOVED.

to `$DREGG_PREIMAGE_OUT` (default `/tmp/pickles-preimage/`), which the
`pickles-preimage-harness` Rust crate proves + verifies through `kimchi::verifier`.

    cd metatheory
    lake build Dregg2.Circuit.Emit.KimchiPreimageCircuit
    lake env lean --run Dregg2/Circuit/Emit/EmitPreimageJson.lean

House Law #1: the CIRCUIT is Lean-authored; `proof-systems` (the harness) is the Rust PROVER.
-/
import Dregg2.Circuit.Emit.KimchiPreimageCircuit

open Dregg2.Circuit.Emit.KimchiPreimageCircuit
open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.KimchiAssertEqual

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
  -- ⚑ THE `assertEqual` RE-AUTHORING'S OWN OBLIGATION. `the_reauthored_json_is_byte_identical` is
  -- a kernel theorem at THIS shape; it is re-checked by value here so that an edit which moves one
  -- artifact and not the other REFUSES instead of shipping two circuits under one claim.
  if preimageJsonAE != preimageJson then
    throw (IO.userError "⚑ THE RE-AUTHORED EMISSION DIVERGED: the `assertEqual` binding and the \
      named-variable binding no longer produce the same artifact. Refusing rather than emitting \
      two circuits under one compatibility claim.")
  if unboundJsonAE != unboundJson then
    throw (IO.userError "⚑ THE RE-AUTHORED CONTROL DIVERGED from the named-variable control.")
  -- ⚑ …and the merged entry must ACCEPT the re-authored circuit and REFUSE its control (the missing
  -- equality leaves public word 0 inert — the negative, caught statically).
  match placeCheckedMerged preimageContract [] ⟨preimageMerges, preimageAliases⟩ preimageGatesAE with
  | .error e => throw (IO.userError s!"⚑ THE MERGED ENTRY REFUSED THE CIRCUIT: {repr e}")
  | .ok _ => pure ()
  match placeCheckedMerged preimageContract [] ⟨[], unboundAliases⟩ preimageGatesAE with
  | .error (.place (.inertPublicWord 0)) => pure ()
  | other =>
      throw (IO.userError s!"⚑ THE CONTROL WAS NOT REFUSED AS AN INERT PUBLIC WORD: {repr other}. \
        Removing the `assertEqual` must leave the public word read by nothing.")
  writeAtomic s!"{dir}/preimage.json" preimageJson
  writeAtomic s!"{dir}/unbound.json" unboundJson
  writeAtomic s!"{dir}/preimage_ae.json" preimageJsonAE
  writeAtomic s!"{dir}/unbound_ae.json" unboundJsonAE
  IO.println s!"EmitPreimageJson: wrote {dir}/preimage.json, unbound.json, preimage_ae.json, \
    unbound_ae.json"
  IO.println s!"  rows = {preimagePlaced.length} (1 public + 13)  witness = \
    {preimageWitness.length} x {NROWS}  public words = {PUB}"
  IO.println s!"  secret  x = {xSecret}"
  IO.println s!"  public  c = {digest}   (= Ref.hash [x] = o1js Poseidon.hash([x]))"
  IO.println s!"  binding: sigma(0,0) = {repr (wireAt 0 0)}, sigma(12,0) = {repr (wireAt 12 0)}"
  IO.println s!"  control: sigma(0,0) = {repr (wiresOf unboundPlaced 0 0)} (a singleton)"
  IO.println s!"  assertEqual re-authoring: {repr preimageMerges}"
  IO.println s!"    rows named-variable = {preimagePlaced.length}, rows assertEqual = \
    {preimagePlacedAE.length}  (delta = {preimagePlacedAE.length - preimagePlaced.length})"
  IO.println s!"    byte-identical = {preimageJsonAE == preimageJson}"
