/-
# Dregg2.Tools.ConeCutover — the CUTOVER step of the ConePort toolkit: a port only counts when the
floor-carrying original is GONE.

## Why this exists (the additive-regrounding sin, mechanized away)

`Tools/ConePort` produces verified S3 successors, but a successor DECLARED NEXT TO its vacuous
original reduces the carrier surface by ZERO — the ruler
(`scripts/binding_surface_complete.py`, tier A) counts floor-carrying binders in statements, and
every original still binds its refuted floor. The cutover makes the port real: the original's
floor binder is REMOVED IN PLACE (same name, same conclusion, the per-instance side condition
appended — the exact type ConePort kernel-checked for that site), every consumer call site is
rewired, and the additive scaffolding module is DELETED.

## Why IN PLACE and not "re-point consumers at the generated cone module"

The generated cone module IMPORTS the defining modules (it needs their `def`s to state the ports),
so a defining-module consumer pointed at the cone would be an IMPORT CYCLE. In-place cutover is
the only cycle-free shape — and it keeps every `#assert_axioms` pin aimed at the same name, which
now names the successor (the pin "moves" by the original ceasing to exist).

## The transaction (fail closed, all-or-nothing)

An edit spec is a list of (path, old, new, expectedCount) plus a list of file deletions. Staging
verifies EVERY edit against the real tree — the `old` text must occur EXACTLY `expectedCount`
times at its point in the edit sequence, and must be GONE after its own application — before ANY
byte is written. One failure anywhere refuses the whole cutover with nothing touched. The outer
driver (`scripts/cone_cutover_run.sh`) adds file-level backups and rolls everything back if the
post-edit closure build goes red — a half-cutover (a deleted theorem without a working, imported
replacement) is the worst available outcome and is structurally unreachable.

## The standing tooth (default mode, every build)

After the cutover lands, the same spec elaborates in ASSERT mode on every build: every `old`
fragment must be ABSENT from its file, every `new` fragment PRESENT, every deleted file ABSENT.
Combined with the semantic teeth (the cutover-check module's `example : ⟨ConePort-pinned type⟩ :=
@original` statements and the re-run ConePort driver pinning the cluster as floor-binder-free),
regression to the floor-carrying shape is a build error, not a drift.
-/
import Lean

namespace Dregg2.Tools.ConeCutover

open Lean Elab

set_option autoImplicit false

/-- One textual edit: `old` must occur exactly `count` times in `path` (at its position in the
edit sequence — earlier edits to the same file apply first), and zero times after replacement. -/
structure FileEdit where
  path : String
  old : String
  new : String
  count : Nat := 1
  deriving Inhabited

/-- The whole cutover: the edits plus the additive scaffolding files the cutover retires. -/
structure CutoverSpec where
  edits : List FileEdit
  deletions : List String

def occurrences (s pat : String) : Nat := (s.splitOn pat).length - 1

private def shortId (e : FileEdit) : String :=
  let head := e.old.replace "\n" "⏎"
  s!"{e.path} :: «{head.take 60}…»"

/-- STAGE: verify every edit and deletion against the tree and produce the full set of new file
contents — or throw, with every violation listed, having touched NOTHING. -/
def stage (spec : CutoverSpec) : IO (Array (String × String)) := do
  let mut contents : Array (String × String) := #[]
  let mut idx : Array String := #[]
  let mut violations : Array String := #[]
  for e in spec.edits do
    if e.old.isEmpty || e.old == e.new then
      violations := violations.push s!"DEGENERATE edit (empty old, or old = new): {shortId e}"
      continue
    -- (empty `new` = pure deletion of the `old` span; legal.)
    let i? := idx.findIdx? (· == e.path)
    let mut cur := ""
    match i? with
    | some i => cur := contents[i]!.2
    | none =>
      if !(← System.FilePath.pathExists e.path) then
        violations := violations.push s!"MISSING file: {e.path}"
        continue
      cur ← IO.FS.readFile e.path
      idx := idx.push e.path
      contents := contents.push (e.path, cur)
    let n := occurrences cur e.old
    if n != e.count then
      violations := violations.push
        s!"MATCH-COUNT {n} ≠ expected {e.count}: {shortId e}"
      continue
    let next := cur.replace e.old e.new
    if occurrences next e.old != 0 then
      violations := violations.push
        s!"RESIDUAL: `old` still present after replacement (old ⊆ new?): {shortId e}"
      continue
    let i := (idx.findIdx? (· == e.path)).get!
    contents := contents.set! i (e.path, next)
  for d in spec.deletions do
    if !(← System.FilePath.pathExists d) then
      violations := violations.push s!"MISSING deletion target: {d}"
  unless violations.isEmpty do
    throw <| IO.userError <|
      s!"ConeCutover REFUSED — {violations.size} violation(s), nothing written:\n"
        ++ String.intercalate "\n" (violations.toList.map ("  ✗ " ++ ·))
  return contents

/-- APPLY: write every staged file (backing the originals up to `backupDir` when provided), then
delete the retired files (backed up too). Only ever called on a successful `stage`. -/
def apply (spec : CutoverSpec) (staged : Array (String × String))
    (backupDir : Option String) : IO Unit := do
  if let some dir := backupDir then
    IO.FS.createDirAll dir
  let backup : String → IO Unit := fun path => do
    if let some dir := backupDir then
      let flat := path.replace "/" "__"
      IO.FS.writeFile (System.FilePath.mk dir / flat).toString (← IO.FS.readFile path)
  for (path, content) in staged do
    backup path
    IO.FS.writeFile path content
  for d in spec.deletions do
    backup d
    IO.FS.removeFile d

/-- ASSERT (the standing tooth): the tree is in the POST-cutover state — every `old` absent, every
`new` present, every retired file gone. Returns the violations (empty = holding). -/
def assertPostState (spec : CutoverSpec) : IO (Array String) := do
  let mut violations : Array String := #[]
  for e in spec.edits do
    if !(← System.FilePath.pathExists e.path) then
      violations := violations.push s!"MISSING file: {e.path}"
      continue
    let cur ← IO.FS.readFile e.path
    if occurrences cur e.old != 0 then
      violations := violations.push s!"REGRESSED (old text back): {shortId e}"
    -- an empty `new` is a pure deletion; presence is not checked for it.
    if !e.new.isEmpty && occurrences cur e.new == 0 then
      violations := violations.push s!"MISSING new text: {shortId e}"
  for d in spec.deletions do
    if ← System.FilePath.pathExists d then
      violations := violations.push s!"RETIRED file resurrected: {d}"
  return violations

/-- The command body a spec module invokes. Default mode = the standing post-state tooth (build
error on any regression). `CONE_CUTOVER_WRITE=1` = the one-shot transactional application
(`CONE_CUTOVER_BACKUP_DIR` for in-tool backups; the shell driver keeps its own as well). -/
def runCutoverCmd (spec : CutoverSpec) (tag : String) : Command.CommandElabM Unit := do
  let write := (← IO.getEnv "CONE_CUTOVER_WRITE").isSome
  let stageOnly := (← IO.getEnv "CONE_CUTOVER_STAGE").isSome
  if stageOnly then
    let staged ← stage spec
    logInfo m!"ConeCutover[{tag}] STAGE OK (dry run): {staged.size} file(s) verified editable, {spec.deletions.length} deletion target(s) present. Nothing written."
  else if write then
    let staged ← stage spec
    let backupDir ← IO.getEnv "CONE_CUTOVER_BACKUP_DIR"
    apply spec staged backupDir
    logInfo m!"ConeCutover[{tag}] APPLIED: {staged.size} file(s) edited, {spec.deletions.length} file(s) retired. The closure build + pinned teeth are now the gate; the shell driver rolls back on red."
  else
    let violations ← assertPostState spec
    unless violations.isEmpty do
      throwError "ConeCutover[{tag}] post-state VIOLATED ({violations.size}):\n{String.intercalate "\n" (violations.toList.map ("  ✗ " ++ ·))}"

end Dregg2.Tools.ConeCutover
