import Lean
open Lean

/-- probe: what API exposes the @[export] C-name map? -/
run_cmd do
  let env ← Lean.getEnv
  let some n := Lean.getExportNameFor? env `Nat.add | Lean.logInfo "no export for Nat.add (expected)"
  Lean.logInfo m!"{n}"
