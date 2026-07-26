/-
# EmitTinyAutomataPacked — dump the PACKED descriptor bytes AND its satisfying witness.

Every point emitted here carries `TinyAutomataPacked.packMeas_satisfies` — a real
`Satisfied2Public` witness for the emitted descriptor — so the prove-time numbers
`circuit/tests/tiny_automata_packed_rows_measure.rs` reads off these files are costs of a
PROVABLE object, not of an emitted-but-unsatisfiable one.

Three files per `(n, s)` point, under the directory given as the first argument:
  * `n{n}_s{s}.json`  — `emitVmJson2 (packMeas n s)`, the IR-v2 wire bytes.
  * `n{n}_s{s}.trace` — one line per trace row, `2s + 1` space-separated column values, read
    off `packMeasWit n s` (whose `rows.length = n / s` is `packMeas_rows_and_verdict`).
  * `n{n}_s{s}.pis`   — `pi[initial_state] pi[final_state]`.

Run: `lake env lean --run EmitTinyAutomataPacked.lean /tmp/packed`
-/
import Dregg2.Circuit.Emit.TinyAutomataPacked

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.TinyAutomataPacked

/-- The column values of the witness's rows, at the declared width. -/
def rowsOf (n s : Nat) : List (List Nat) :=
  (packMeasWit n s).rows.map (fun a => (List.range (packWidth s)).map (fun c => (a c).toNat))

/-- The witness's two public inputs. -/
def pisOf (n s : Nat) : List Nat :=
  let t := packMeasWit n s
  [(t.pub 0).toNat, (t.pub 1).toNat]

def joinNats (l : List Nat) : String := String.intercalate " " (l.map toString)

/-- The grid: `s ∣ n` at every point, and `n ≤ 128` because the deployed exact-public tooth
caps the DECLARED manifest at `MAX_EXACT_PUBLIC_ROWS = 128` and the declared table is the RUN
table (one row per input symbol — invariant in `s`, which is exactly the point). -/
def grid : List (Nat × Nat) :=
  [(32, 1), (32, 2), (32, 4), (32, 8),
   (64, 1), (64, 2), (64, 4), (64, 8), (64, 16),
   (128, 1), (128, 2), (128, 4), (128, 8), (128, 16), (128, 32)]

def main (args : List String) : IO Unit := do
  let dir := args.headD "/tmp/packed"
  IO.FS.createDirAll dir
  for (n, s) in grid do
    let base := s!"{dir}/n{n}_s{s}"
    let rows := rowsOf n s
    IO.FS.writeFile (base ++ ".json") (emitVmJson2 (packMeas n s))
    IO.FS.writeFile (base ++ ".trace") (String.intercalate "\n" (rows.map joinNats))
    IO.FS.writeFile (base ++ ".pis") (joinNats (pisOf n s))
    IO.println s!"n={n} s={s} rows={rows.length} width={packWidth s} declared={n} \
      bytes={(emitVmJson2 (packMeas n s)).length}"
