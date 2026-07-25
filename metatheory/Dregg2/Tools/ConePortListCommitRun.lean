/-
# Dregg2.Tools.ConePortListCommitRun — the ConePort DRIVER for the `ListDigestBindsList` cluster,
with the measurement PINNED as a build-time tooth.

This module re-runs the elaborated-term analysis of every direct threader of
`ListCommit.ListDigestBindsList` on every build and checks each site's outcome against the pinned
expectation. Any drift — a pinned-portable site that refuses, a pinned-refusal that ports, a
refusal for the wrong REASON — is a BUILD ERROR, not a warning: the census may only get more true
(`SWEPT ≠ VERIFIED`, mechanized). Write mode is RETIRED: the cluster was CUT OVER in place
(`Tools/ConeCutoverListCommit`, 2026-07-24) and the generated cone module deleted — emitting it
again would resurrect the additive scaffolding.

The pinned split (re-pinned POST-CUTOVER 2026-07-24; the prototype 13/13-portable split is
superseded — the cutover REMOVED those floor binders):
  * the 13 CUT-OVER theorems REFUSE as NOT-A-CARRIER — the floor binder is GONE from each
    statement (this pin IS the standing, build-time proof the cutover holds);
  * 3 LEVEL-2 threaders (consumers rewired through the `noCNColl_of_inj` bridge) PORT
    mechanically via the ONE bridge AppRule (`bridgeRules` — the AppRule-from-PortResult
    composition gap, closed by the cutover's uniform bridge); their own in-place cutover is the
    next wave; `cellCommit_binds_tail` REFUSES (DAG-order: `cellCommit_binds_fieldsRoot` is an
    unported endpoint-shaped consumer) — the negative control;
  * the endpoint itself REFUSES (`floor APPLIED` — an ENDPOINT; it needed the hand S2 in
    `Circuit/ListCommitRegrounded`);
  * the 2 structure-bundle defs (`accountsComponent`, `listComponent`) REFUSE at the
    COMPILER-LIFTED AUX sink: the elaborator lifted their floor-consuming field proofs into
    `_proof_1` constants, so the floor flows into an aux decl (the design's risk-#3 shape,
    observed live) — the bundle is the port unit, a design decision plus aux contraction, never a
    mechanical rewrite;
  * `leakyExhibit` (below) REFUSES as LEAKY — the floor application's arguments are
    `obtain`-locals, so the side condition would need quantification the tool cannot invent;
  * `listDigest_congr` REFUSES as not-a-carrier (negative control).
-/
import Dregg2.Circuit.ListCommit
import Dregg2.Circuit.ListCommitRegrounded
import Dregg2.Circuit.AccountsCommit
import Dregg2.Circuit.EffectCommit2
import Dregg2.Circuit.RotatedKernelRefinementNotes
import Dregg2.Circuit.RotatedKernelRefinementMisc
import Dregg2.Circuit.RotatedKernelRefinementLifecycleDisc
import Dregg2.Circuit.RotatedKernelRefinementProgram
import Dregg2.Circuit.RotatedKernelRefinementCellSeal
import Dregg2.Circuit.RotatedKernelRefinementBirth
import Dregg2.Circuit.RotatedKernelRefinementLifecycle
import Dregg2.Circuit.RotatedKernelRefinementPermsVK
import Dregg2.Exec.FieldsMap
import Dregg2.Exec.RecordCommit
import Dregg2.Tools.ConePort

namespace Dregg2.Tools.ConePortListCommitRun

open Lean Elab Command Dregg2.Tools.ConePort

set_option autoImplicit false

open Dregg2.Circuit.StateCommit (compressNInjective) in
open Dregg2.Circuit.ListCommit in
/-- **SYNTHETIC LEAKY EXHIBIT** (a real theorem, kept as the tool's negative control): the
`ListDigestBindsList` application's list arguments are `obtain`-locals of an existential, so the
per-instance side condition would need quantification over proof-local binders — the tool MUST
refuse this shape (the measured ~22% leaky class of the whole-tree census, reproduced in
miniature). -/
theorem leakyExhibit (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hex : ∃ xs ys : List Nat, listDigest LE cN xs = listDigest LE cN ys ∧ xs ≠ ys) : False := by
  obtain ⟨xs, ys, h, hne⟩ := hex
  exact hne (ListDigestBindsList LE cN hN hLE xs ys h)

/-- The three S3 rewrite rules for `ListDigestBindsList LE cN hN hLE xs ys h` (app args, with the
implicit `α` at index 0: `#[α, LE, cN, hN, hLE, xs, ys, h]`). Both-floors first, so the strongest
match wins. -/
def rules : List AppRule :=
  [ { orig := `Dregg2.Circuit.ListCommit.ListDigestBindsList, arity := 8,
      floorIdxs := #[3, 4],
      repl := `Dregg2.Circuit.ListCommitRegrounded.listDigest_binds_of_noColl,
      argMap := #[some 0, some 1, some 2, some 5, some 6, none, some 7], tag := "noColl" }
  , { orig := `Dregg2.Circuit.ListCommit.ListDigestBindsList, arity := 8,
      floorIdxs := #[3],
      repl := `Dregg2.Circuit.ListCommitRegrounded.listDigest_binds_of_noCNColl,
      argMap := #[some 0, some 1, some 2, some 4, some 5, some 6, none, some 7],
      tag := "noCNColl" }
  , { orig := `Dregg2.Circuit.ListCommit.ListDigestBindsList, arity := 8,
      floorIdxs := #[4],
      repl := `Dregg2.Circuit.ListCommitRegrounded.listDigest_binds_of_noLeafColl,
      argMap := #[some 0, some 1, some 2, some 3, some 5, some 6, none, some 7],
      tag := "noLeafColl" } ]

/-- ⚑ the LEVEL-2 COMPOSITION rules — the AppRule-from-PortResult gap, closed by the cutover's
UNIFORM bridge: every still-floored consumer's floor now flows into ONE bridge application
(`noCNColl_of_inj` / `noColl_of_carriers`), so the whole NEXT cone level is portable with ONE
rule per bridge (the side condition passes through `noCNColl_self`/`noListColl_self`), never a
per-theorem rule table. -/
def bridgeRules : List AppRule :=
  [ { orig := `Dregg2.Circuit.ListCommitRegrounded.noCNColl_of_inj, arity := 6,
      floorIdxs := #[3],
      repl := `Dregg2.Circuit.ListCommitRegrounded.noCNColl_self,
      argMap := #[some 0, some 1, some 2, some 4, some 5, none], tag := "bridge-noCNColl" }
  , { orig := `Dregg2.Circuit.ListCommitRegrounded.noColl_of_carriers, arity := 7,
      floorIdxs := #[3, 4],
      repl := `Dregg2.Circuit.ListCommitRegrounded.noListColl_self,
      argMap := #[some 0, some 1, some 2, some 5, some 6, none], tag := "bridge-noColl" } ]

def cfg : PortConfig :=
  { floors := [ `Dregg2.Circuit.StateCommit.compressNInjective
              , `Dregg2.Circuit.ListCommit.listLeafInjective ]
  , rules := rules ++ bridgeRules
  , genNamespace := `Dregg2.Circuit.ListCommitPortedCone
  , forbidden := [ `Dregg2.Circuit.StateCommit.compressNInjective
                 , `Dregg2.Circuit.ListCommit.ListDigestBindsList ] }

/-- Every direct in-tree consumer of `ListDigestBindsList`, plus the endpoint itself — the whole
cluster, with its pinned outcome. -/
def targets : List Target :=
  [ -- ⚑ the 13 CUT-OVER theorems: pinned NOT-A-CARRIER — the floor binder is GONE from each
    -- statement (Tools/ConeCutoverListCommit). This pin is the standing, build-time proof the
    -- cutover HOLDS; if anyone re-adds a floor binder, the build goes red HERE.
    { decl := `Dregg2.Circuit.RotatedKernelRefinementNotes.noteListRoot_binds,
      expected := .refuse "not a carrier" }
  , { decl := `Dregg2.Circuit.RotatedKernelRefinementMisc.fixRootBinds,
      expected := .refuse "not a carrier" }
  , { decl := `Dregg2.Circuit.RotatedKernelRefinementLifecycleDisc.discRoot_binds,
      expected := .refuse "not a carrier" }
  , { decl := `Dregg2.Circuit.RotatedKernelRefinementProgram.setProgram_forced,
      expected := .refuse "not a carrier" }
  , { decl := `Dregg2.Circuit.RotatedKernelRefinementCellSeal.lifecycleRoot_binds,
      expected := .refuse "not a carrier" }
  , { decl := `Dregg2.Circuit.RotatedKernelRefinementBirth.accountsRoot_binds,
      expected := .refuse "not a carrier" }
  , { decl := `Dregg2.Circuit.RotatedKernelRefinementBirth.accountsGrowForced,
      expected := .refuse "not a carrier" }
  , { decl := `Dregg2.Circuit.RotatedKernelRefinementLifecycle.deathCertRoot_binds,
      expected := .refuse "not a carrier" }
  , { decl := `Dregg2.Circuit.RotatedKernelRefinementLifecycle.auditSlotRoot_binds,
      expected := .refuse "not a carrier" }
  , { decl := `Dregg2.Circuit.RotatedKernelRefinementLifecycle.auditSlotForced,
      expected := .refuse "not a carrier" }
  , { decl := `Dregg2.Circuit.RotatedKernelRefinementLifecycle.refusal_forced,
      expected := .refuse "not a carrier" }
  , { decl := `Dregg2.Circuit.RotatedKernelRefinementPermsVK.slotSetForced,
      expected := .refuse "not a carrier" }
  , { decl := `Dregg2.Exec.FieldsMap.fieldsRoot_binds_tail,
      expected := .refuse "not a carrier" }
    -- ⚑ LEVEL-2: consumers rewired through the bridge PORT via the ONE bridge AppRule — the
    -- 2-level cone, kernel-checked in-env on every build. In-place cutover of THESE is the
    -- next wave.
  , { decl := `Dregg2.Circuit.RotatedKernelRefinementNotes.noteGrowForced, expected := .port }
  , { decl := `Dregg2.Circuit.RotatedKernelRefinementCellSeal.lifecycleSealForced,
      expected := .port }
  , { decl := `Dregg2.Circuit.RotatedKernelRefinementMisc.makeSovereign_commit_forced,
      expected := .port }
    -- LEVEL-2 NEGATIVE CONTROL: `hN` also flows into `cellCommit_binds_fieldsRoot` (an
    -- endpoint-shaped consumer not yet ported) — the DAG-order refusal, demonstrated.
  , { decl := `Dregg2.Exec.RecordCommit.cellCommit_binds_tail,
      expected := .refuse "unported consumer" }
    -- the endpoint: REFUSES — it applies the floor; the S2 extractor was the hand port. Its
    -- remaining consumers are the two bundle defs below — the cluster's residual, named.
  , { decl := `Dregg2.Circuit.ListCommit.ListDigestBindsList,
      expected := .refuse "ENDPOINT" }
    -- the 2 structure bundles: REFUSE at the compiler-lifted `_proof_1` AUX sink (risk-#3 live);
    -- the bundle (not the theorem) is the port unit — design decision + aux contraction.
  , { decl := `Dregg2.Circuit.AccountsCommit.accountsComponent,
      expected := .refuse "COMPILER-LIFTED AUX" }
  , { decl := `Dregg2.Circuit.EffectCommit2.listComponent,
      expected := .refuse "COMPILER-LIFTED AUX" }
    -- the leaky shape: REFUSES — proof-local binders in the floor application's arguments.
  , { decl := `Dregg2.Tools.ConePortListCommitRun.leakyExhibit,
      expected := .refuse "LEAKY" }
    -- negative control: no floor binder at all.
  , { decl := `Dregg2.Circuit.ListCommit.listDigest_congr,
      expected := .refuse "not a carrier" } ]

elab "#cone_port_run" : command => do
  if (← IO.getEnv "CONE_PORT_WRITE").isSome then
    throwError "CONE_PORT_WRITE is RETIRED: the ListDigestBindsList cluster was CUT OVER in place (Tools/ConeCutoverListCommit) and the generated cone deleted — re-emitting it would resurrect the additive scaffolding"
  liftTermElabM do
    let rep ← runCluster cfg targets
    logInfo m!"=== ConePort ListDigestBindsList cluster (POST-CUTOVER): ported={rep.ported.size} refused={rep.refusals.size} mismatches={rep.mismatches.size} ==="
    unless rep.mismatches.isEmpty do
      for m in rep.mismatches do logError m
      throwError "ConePort: the cluster moved under the pinned measurement — re-measure, understand WHY, then re-pin"

#cone_port_run

end Dregg2.Tools.ConePortListCommitRun
