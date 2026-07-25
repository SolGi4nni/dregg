/-
# Dregg2.Verify.TeethWiring — `#teeth_wired`: the roster of teeth that must be IN THE BUILD.

## The hole this closes

A Lean module that is imported by nothing is compiled by nothing. The `Dregg2` `lean_lib` has no
`globs` (`metatheory/lakefile.toml`), so `lake build` compiles `Dregg2.lean` plus its transitive
imports and NOTHING ELSE. An unimported module is therefore not red — it is ABSENT, and the build
is GREEN precisely because its checks never ran.

That is not hypothetical in this tree, it is the campaign's recurring disease:

  * `6b1e156bdf` truncated `Dregg2.lean`, dropping 1055+ root imports;
  * `8a28420ec9` truncated it a SECOND time, 1301 imports -> 217;
  * `799b5a6e27` dropped the `ListCommitRegrounded`/`ConePort`/driver/cone imports SELECTIVELY,
    under an unrelated Peephole commit — no truncation, no signal, four teeth dark;
  * and the vacuity-elimination campaign shipped SIX cutover teeth that never ran once, because
    nothing imported them, while advertising "teeth armed".

Every one of those was invisible to `lake build Dregg2`, which stayed green throughout.

## Why this check has to live HERE, and why it is not the textual script

A module cannot check from inside itself that the root imports it — asking is what proves it. But
it does not follow that the check must read `Dregg2.lean` as TEXT. `Environment.header.moduleNames`
at the end of the ROOT module is exactly the set of modules this build compiled, and it is a
SEMANTIC fact that arrives through imports, which is the one thing lake's dependency graph tracks.
Editing `Dregg2.lean` invalidates its own olean, so `#teeth_wired` re-runs on the very edit that
could darken a tooth. No cache can answer for it, and no `IO.FS` read is involved.

This is the same repair `#floor_ratchet` applies above, pointed at a different question:
`#floor_ratchet` asks whether a new declaration took a refuted hypothesis; `#teeth_wired` asks
whether the checks that would notice are in the build at all.

`scripts/cone_cutover_textual_check.sh` remains, and is NOT redundant: it verifies the cutovers'
SOURCE post-state (that the pre-cutover text is gone and the post-cutover text present), which is
a claim about bytes and has no semantic shadow. It also greps for the `#teeth_wired` invocation
itself — the one failure this command structurally cannot report, because a deleted command raises
no error.

## ⚑ Why this module imports NONE of its subjects

If `TeethWiring` imported the modules it certifies, importing it would GUARANTEE they are in the
environment and every check below would be a tautology — the additive-regrounding sin in wiring
form. The roster is a list of NAMES. The question "is this module in the build?" is only a real
question when asked from a module that did not put it there, about a root that either did or did
not. So this file imports `Lean` and nothing else, and `#teeth_wired` is invoked from
`Dregg2.lean`, where the answer is genuinely open.

## Blindness control

`#teeth_wired` is a pure rejector over a membership test, and a rejector cannot detect its own
blindness: a membership test that has become constantly-true reports every tooth wired, forever,
and the roster silently certifies nothing. `absentControl` is the dual — a module name that is
guaranteed NOT to exist, which the same test must report ABSENT on the same run. If the test ever
stops being able to say "no", the control fails LOUDLY instead of the whole roster passing
vacuously. Do not delete it to get green; it is the reason the greens above mean anything.
-/
import Lean

namespace Dregg2.Verify.TeethWiring

open Lean Elab Command

/-- A module that exists ONLY to be a tooth, plus what goes dark when it leaves the build. The
reason is not decoration: a wiring failure has to say what stopped being checked, or the next
reader deletes the import again. -/
structure Tooth where
  /-- The module name, as it must appear in the root's environment. -/
  mod : Name
  /-- What this module checks — printed on failure. -/
  guards : String

/-- ⚑ THE ROSTER. Every module here is a check, not a development: it asserts something about
OTHER modules and produces little or nothing of its own. Several
(`LogCommitCutoverCheck`, `MapPathCutoverCheck`) declare NO constants at all — they are pure
`example` + `#assert_*` command modules, so their entire contribution is the act of elaborating.
For those, "is the module in the environment" is not a proxy for whether the tooth ran; it IS
whether the tooth ran.

Add a line here whenever a new tooth lands. That is the point: the roster is the one place the
campaign records what it believes is guarding it, and `#teeth_wired` makes the belief checkable. -/
def roster : List Tooth :=
  [ { mod := `Dregg2.Circuit.ListCommitCutoverCheck
    , guards := "the 13 ListDigestBindsList cut-over theorems: S3 statement identity (kernel \
        defeq against independently-written types) + compressNInjective unreachable from each proof" }
  , { mod := `Dregg2.Circuit.LogCommitCutoverCheck
    , guards := "the 16 logHashInjective cut-over endpoints: statement identity, floor \
        unreachability, and no-strength-lost (the old statement still derivable through the bridge)" }
  , { mod := `Dregg2.Circuit.StateCommitLeafCutoverCheck
    , guards := "the 13 cellLeafInjective cut-over theorems (CommitmentCrossBind + StateCommit)" }
  , { mod := `Dregg2.Circuit.BundleCutoverCheck
    , guards := "the FIELD-BUNDLE cutover class — floors carried as structure fields, where the \
        port unit is the bundle and no binder-keyed check can see the carrier" }
  , { mod := `Dregg2.Circuit.MapPathCutoverCheck
    , guards := "the Poseidon2SpongeCR re-grounding of the DEPLOYED map/heap Merkle-opening spine" }
  , { mod := `Dregg2.Tools.ConeCutover
    , guards := "the cutover metaprogram itself, and the SEMANTIC post-state tooth every cutover \
        spec module invokes" }
  , { mod := `Dregg2.Tools.ConeCutoverListCommit
    , guards := "the ListDigestBindsList cutover's standing post-state: 13 declarations floor-free \
        in statement AND proof closure, retired scaffolding absent, blindness controls live" }
  , { mod := `Dregg2.Tools.ConePort
    , guards := "the threader-port metaprogram (elaborated-term analysis, kernel-verified surgery)" }
  , { mod := `Dregg2.Tools.ConePortListCommitRun
    , guards := "the pinned ListDigestBindsList port measurement — the 13 must now REFUSE as \
        not-a-carrier, which is the standing proof that the cutover still holds" }
  , { mod := `Dregg2.Tools.ConePortLogHashRun
    , guards := "the pinned logHashInjective port measurement (48 ported / 48 eligible, 2 \
        explained refusals); drift in EITHER direction is a build error" }
  , { mod := `Dregg2.Verify.FloorCensus
    , guards := "`#floor_census` — the elaborated-term refuted-floor census, the campaign's \
        instrument of record" }
  , { mod := `Dregg2.Verify.FloorRatchet
    , guards := "`#floor_ratchet` — THE ACCRUAL GATE. It fails the build when a declaration not \
        in the checked-in baseline takes a hypothesis this tree PROVES FALSE at deployed BabyBear \
        parameters (binder, prop-body def, or structure field). Without it in the build, new \
        VACUOUS theorems land unremarked — which is the measured state the gate was built to end \
        (52 carriers removed, 63 added, net +11 over the campaign's own window)" }
  ]

/-! ⚑ WHY `Dregg2.Verify.FloorRatchet` IS ON THE ROSTER AND ITS BASELINE IS NOT.

The roster entry above REPLACES a stale note (landed 2026-07-25) that read "NOT ON THE ROSTER YET
… in flight in a co-tenant lane and not yet at HEAD". That lane landed — `Dregg2.lean` imports
`Dregg2.Verify.FloorRatchet` and invokes `#floor_ratchet` at HEAD, and CI runs
`scripts/floor_ratchet_check.sh` — so the note was asserting the absence of the very module the
root was already carrying. A roster that omits the campaign's principal gate certifies the wrong
set: `#teeth_wired` would have reported "all teeth wired" on a build with the accrual gate cut out.

The entry is NOT redundant with the invocation erroring. Dropping ONLY the import reds the build
(`#floor_ratchet` becomes an unknown command). Dropping the import AND the invocation — which is
exactly what happened to four cutover teeth under `799b5a6e27`, and to 1055+/1084 imports under the
two root truncations — leaves a GREEN build with no gate. That is the case this line catches, from
INSIDE the build, where no textual script has to be remembered.

`Dregg2.Verify.FloorRatchetBaseline` is deliberately NOT listed: `FloorRatchet` imports it, so its
presence follows from the line above and a roster entry for it would be the tautology this module's
header refuses. Its CONTENT (a silent raise) is a different question, gated separately by
`scripts/floor_ratchet_check.sh` step 3 against the merge-base. -/

/-- BLINDNESS CONTROL (negative). A module name that cannot exist, which the same membership test
used above must report ABSENT on the same run. Its job is to fail when the test stops being able to
return `false` — the one failure mode under which every green above is vacuous. -/
def absentControl : Name :=
  `Dregg2.Verify.TeethWiring.ThisModuleDoesNotExistAndMustNotBeCreated

/-- The membership test, named once so the roster and the control provably share it. A control that
exercised a different code path would certify nothing. -/
def wired (mods : Array Name) (m : Name) : Bool := mods.any (· == m)

/-- `#teeth_wired` — ERROR unless every module in `roster` is in the environment of the module that
invokes this command. Invoke it from `Dregg2.lean`, where the answer is a real question.

Fail-closed: an empty roster, or a blindness control that reports PRESENT, is itself a violation. -/
elab "#teeth_wired" : command => do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut violations : Array String := #[]

  if roster.isEmpty then
    violations := violations.push
      "DEGENERATE: the roster is EMPTY — a wiring gate that names no teeth always passes."

  -- The blindness control runs FIRST: if the test cannot say "absent", nothing below means anything.
  if wired mods absentControl then
    violations := violations.push s!"BLINDNESS CONTROL FAILED: the membership test reports \
      {absentControl} — a module that does not exist — as WIRED. The test can no longer return \
      false, so every 'wired' verdict below is vacuous. Fix the test; do not delete this control."

  for t in roster do
    unless wired mods t.mod do
      violations := violations.push s!"DARK TOOTH: {t.mod} is NOT in this build. It guards \
        {t.guards}. An unimported module is compiled by NOTHING — this build is green because \
        that check never ran, not because it passed. Re-add `import {t.mod}` to Dregg2.lean."

  unless violations.isEmpty do
    throwError "#teeth_wired: {violations.size} violation(s) — the campaign's teeth are not all \
      in the build:\n{String.intercalate "\n" (violations.toList.map ("  ✗ " ++ ·))}"

  logInfo m!"#teeth_wired: {roster.length} teeth modules confirmed in the build (blindness \
    control live: the membership test still reports a nonexistent module ABSENT)."

end Dregg2.Verify.TeethWiring
