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

## ⚑ The standing tooth is SEMANTIC. The textual one CANNOT be a build-time tooth — measured.

The original design made `assertPostState` (below) the standing tooth: on every build, every `old`
fragment absent, every `new` fragment present, every retired file gone. **That was never able to
stand, and it was measured false on 2026-07-25.**

`assertPostState` reads the tree through `IO.FS`. Lake's dependency graph is built from IMPORTS; it
has no idea those reads happened, so once the module has an olean it is REPLAYED FROM CACHE and the
check never runs again. Ground truth at that commit, on a tree whose root had been truncated out
from under the spec:

```
$ lake build Dregg2.Tools.ConeCutoverListCommit          # EXIT=0   ← the cache answering
$ lake env lean Dregg2/Tools/ConeCutoverListCommit.lean  # EXIT=1   ← forced fresh
  ConeCutover[ListDigestBindsList] post-state VIOLATED (2):
    ✗ REGRESSED (old text back): Dregg2.lean :: «32 keystones #assert_all_clean⏎import …»
    ✗ MISSING new text: Dregg2.lean :: «32 keystones #assert_all_clean⏎import …»
```

So the tooth was green in both directions it could be wrong in: it did not fire on a real
regression, and it was not honestly green either. A check a cache can answer for is not a check.

What lake DOES track is the ENVIRONMENT. Change a declaration in an imported module and every
importer is re-elaborated. So the standing tooth is now `assertSemanticPostState`, stated over the
environment rather than over the bytes:

  * every cut-over declaration EXISTS, its STATEMENT does not mention the refuted floor (the
    ruler's own criterion — a resurrected binder is red HERE), and its PROOF CLOSURE does not
    reach it (the `#assert_not_depends_on` walk, shared with `Dregg2.Tactics` so the two go blind
    together or not at all);
  * the retired scaffolding MODULE is absent from the environment;
  * the cutover's own check modules ARE in the environment (a tooth that is not in the build is
    not a tooth);
  * BLINDNESS CONTROLS: named declarations that MUST still reach the floor — one through the
    TYPE, one only through the PROOF TERM. A rejector cannot detect its own blindness; if the
    closure walk ever stops seeing proof terms, the proof control fails and says so instead of
    every floor-freedom claim in the module passing vacuously.

The TEXTUAL post-state keeps a real job — it is the only check that sees `Dregg2.lean` itself, i.e.
the WIRING, which no module can check from inside itself (twice in this campaign a commit truncated
the root and silently unbuilt whole modules). It just cannot live in the build: it runs from
`scripts/cone_cutover_textual_check.sh`, which forces a fresh elaboration
(`CONE_CUTOVER_TEXT=1 lake env lean …`) so a cache can never answer for it.
-/
import Lean
-- for `Dregg2.findForbiddenPath` / `Dregg2.forbiddenMatches`: the SAME closure walk
-- `#assert_not_depends_on` uses, so the semantic tooth and the per-theorem pins cannot disagree
-- about what "reaches the floor" means, and cannot go blind independently.
import Dregg2.Tactics

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

/-- ASSERT, TEXTUALLY: the tree is in the POST-cutover state — every `old` absent, every `new`
present, every retired file gone. Returns the violations (empty = holding).

⚠ NOT A BUILD-TIME TOOTH (see the module note): these are `IO.FS` reads, invisible to lake's
import-based dependency graph, so in a build this is replayed from cache and never re-checked. It
runs from `scripts/cone_cutover_textual_check.sh` (`CONE_CUTOVER_TEXT=1`), which forces a fresh
elaboration. Its unique job is `Dregg2.lean` — the WIRING, which no module can check from inside
itself. -/
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

/-! ## The SEMANTIC post-state — the tooth lake can actually see. -/

/-- What the cutover means IN THE ENVIRONMENT. Every field is checked; every field is fail-closed
(an empty `ported`, `floors` or `proofControls` is itself a violation — a guard that guards nothing
always passes). -/
structure SemanticSpec where
  /-- The cut-over declarations (same names they had before the cutover). Each must EXIST, must not
  mention any `floors` constant in its TYPE, and must not reach one through its PROOF closure. -/
  ported : List Name
  /-- The refuted floors (and retired floor-applying endpoints) this cutover removed. Each must
  still RESOLVE: a floor that has vanished from the tree makes every claim below trivially true,
  which is a re-pin, not a pass. -/
  floors : List Name
  /-- Scaffolding modules the cutover retired: must be ABSENT from the environment. -/
  retiredModules : List Name
  /-- The cutover's own check modules: must be PRESENT in the environment. A tooth that is not in
  the build is not a tooth — this is the in-Lean half of the wiring bar (the other half, that
  `Dregg2.lean` imports THIS module, is only visible from outside: the textual check). -/
  wiredModules : List Name
  /-- POSITIVE CONTROL, statement scanner: `(decl, floor)` where the floor MUST appear in `decl`'s
  TYPE. Proves the statement scan can see a floor binder at all. -/
  typeControls : List (Name × Name)
  /-- POSITIVE CONTROL, closure walk: `(decl, floor)` where the floor MUST be reachable from
  `decl`'s PROOF TERM and MUST NOT appear in its type. A rejector cannot detect its own blindness;
  if the walk ever loses `allowOpaque := true` (theorem values are opaque, and a walk without it
  reports every closure EMPTY) this control fails LOUDLY instead of every floor-freedom claim in
  the module passing vacuously. -/
  proofControls : List (Name × Name)

/-- Does `decl`'s STATEMENT mention floor `f`? (The ruler's criterion: it counts floor-carrying
binders in statements, so this is the surface number stated as a build error.) -/
private def typeMentions (info : ConstantInfo) (f : Name) : Bool :=
  info.type.getUsedConstants.any (fun c => Dregg2.forbiddenMatches f c)

/-- ASSERT, SEMANTICALLY (the standing tooth): the ENVIRONMENT is in the post-cutover state. Rides
lake's dependency graph honestly — every input is an imported declaration, so any edit to any of
them re-elaborates this module and re-runs this check. -/
def assertSemanticPostState (s : SemanticSpec) : Command.CommandElabM (Array String) := do
  let mut v : Array String := #[]
  if s.ported.isEmpty then
    v := v.push "DEGENERATE spec: no cut-over declarations named — this check cannot fail."
  if s.floors.isEmpty then
    v := v.push "DEGENERATE spec: no floors named — floor-freedom of nothing is not a claim."
  if s.proofControls.isEmpty then
    v := v.push "DEGENERATE spec: no proof-closure blindness control — a pure rejector with no \
      positive control cannot distinguish 'clean' from 'blind'."
  let env ← getEnv
  let mods := env.header.moduleNames
  for f in s.floors do
    if (env.find? f).isNone then
      v := v.push s!"FLOOR ABSENT FROM THE ENVIRONMENT: {f} — every claim below is then trivially \
        true. Either it was really deleted (re-pin this spec on what replaced it) or this module \
        no longer imports it (then the check is blind)."
  for m in s.wiredModules do
    unless mods.any (· == m) do
      v := v.push s!"NOT WIRED: {m} is not in the environment — the cutover's teeth are not in \
        this build."
  for m in s.retiredModules do
    if mods.any (· == m) then
      v := v.push s!"RETIRED SCAFFOLDING RESURRECTED: {m} is back in the environment — an additive \
        port standing beside its cut-over original reduces the carrier surface by zero."
  for p in s.ported do
    match env.find? p with
    | none =>
      v := v.push s!"MISSING cut-over declaration: {p} — renamed or deleted; a cutover pin must \
        name a live declaration."
    | some info =>
      for f in s.floors do
        if typeMentions info f then
          v := v.push s!"FLOOR BACK IN THE STATEMENT: {p} mentions {f} in its TYPE — the binder \
            this cutover removed has been restored, so the theorem is vacuous again."
      let (hit?, scanned) ← Dregg2.findForbiddenPath p s.floors
      if scanned == 0 then
        v := v.push s!"VACUOUS WALK: 0 constants scanned from {p}."
      match hit? with
      | some path =>
        v := v.push s!"FLOOR REACHED FROM THE PROOF: {p} → {path} — the statement is clean but the \
          proof routes back through the refuted floor."
      | none => pure ()
  for (d, f) in s.typeControls do
    match env.find? d with
    | none => v := v.push s!"TYPE CONTROL MISSING: {d}"
    | some info =>
      unless typeMentions info f do
        v := v.push s!"TYPE CONTROL FAIL: {d} no longer mentions {f} in its type — the statement \
          scanner can no longer see a floor binder, so every 'floor gone from the statement' claim \
          above may be passing vacuously."
  for (d, f) in s.proofControls do
    match env.find? d with
    | none => v := v.push s!"PROOF CONTROL MISSING: {d}"
    | some info =>
      if typeMentions info f then
        v := v.push s!"PROOF CONTROL DEGENERATE: {d} mentions {f} in its TYPE, so it is satisfied \
          without ever reading a proof term — it cannot detect a blind closure walk."
      let (hit?, scanned) ← Dregg2.findForbiddenPath d [f]
      if hit?.isNone then
        v := v.push s!"PROOF CONTROL FAIL: {d} does NOT reach {f} ({scanned} constants scanned) — \
          either the dependency really went away (re-pin the control) or the closure walk has gone \
          BLIND, in which case every floor-freedom claim above is passing vacuously. Do not delete \
          this control to get green."
  return v

/-- The command body a spec module invokes.

DEFAULT (every build) = the SEMANTIC post-state tooth: it reads only the environment, so lake
re-runs it whenever anything it depends on changes.

`CONE_CUTOVER_TEXT=1` additionally runs the TEXTUAL post-state — the wiring check over
`Dregg2.lean` and the retired files, which only means something on a FRESH elaboration
(`scripts/cone_cutover_textual_check.sh`; see the module note for why it is not in the build).

`CONE_CUTOVER_STAGE=1` / `CONE_CUTOVER_WRITE=1` are the one-shot transactional application. -/
def runCutoverCmd (spec : CutoverSpec) (sem : SemanticSpec) (tag : String) :
    Command.CommandElabM Unit := do
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
    let semViolations ← assertSemanticPostState sem
    unless semViolations.isEmpty do
      throwError "ConeCutover[{tag}] SEMANTIC post-state VIOLATED ({semViolations.size}):\n{String.intercalate "\n" (semViolations.toList.map ("  ✗ " ++ ·))}"
    logInfo m!"ConeCutover[{tag}] semantic post-state HOLDS: {sem.ported.length} cut-over declaration(s) free of {sem.floors.length} floor(s) in statement AND proof closure, {sem.retiredModules.length} retired module(s) absent, {sem.wiredModules.length} check module(s) in the build, {sem.typeControls.length + sem.proofControls.length} blindness control(s) live."
    if (← IO.getEnv "CONE_CUTOVER_TEXT").isSome then
      let violations ← assertPostState spec
      unless violations.isEmpty do
        throwError "ConeCutover[{tag}] TEXTUAL post-state VIOLATED ({violations.size}):\n{String.intercalate "\n" (violations.toList.map ("  ✗ " ++ ·))}"
      logInfo m!"ConeCutover[{tag}] textual post-state HOLDS: {spec.edits.length} edit(s) present, {spec.deletions.length} retired file(s) absent (fresh run — a cached olean cannot answer for this)."

end Dregg2.Tools.ConeCutover
