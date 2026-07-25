/-
# Dregg2.Tools.ConePortListCommitRun — the ConePort DRIVER for the `ListDigestBindsList` cluster,
with the measurement PINNED as a build-time tooth.

This module re-runs the elaborated-term analysis of every direct threader of
`ListCommit.ListDigestBindsList` on every build and checks each site's outcome against the pinned
expectation. Any drift — a pinned-portable site that refuses, a pinned-refusal that ports, a
refusal for the wrong REASON — is a BUILD ERROR, not a warning: the census may only get more true
(`SWEPT ≠ VERIFIED`, mechanized). It never writes files during a normal build; the one-shot
generation of `Circuit/ListCommitPortedCone.lean` is triggered by the `CONE_PORT_WRITE` environment
variable and the output is committed as audited source.

The pinned split (measured 2026-07-24, the prototype throughput number):
  * 13 threader theorems PORT with zero human proof work (kernel-checked, round-tripped, no
    explicit-printer fallback needed);
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

def cfg : PortConfig :=
  { floors := [ `Dregg2.Circuit.StateCommit.compressNInjective
              , `Dregg2.Circuit.ListCommit.listLeafInjective ]
  , rules := rules
  , genNamespace := `Dregg2.Circuit.ListCommitPortedCone
  , forbidden := [ `Dregg2.Circuit.StateCommit.compressNInjective
                 , `Dregg2.Circuit.ListCommit.ListDigestBindsList ] }

/-- Every direct in-tree consumer of `ListDigestBindsList`, plus the endpoint itself — the whole
cluster, with its pinned outcome. -/
def targets : List Target :=
  [ -- the 13 threader theorems: pinned PORTABLE.
    { decl := `Dregg2.Circuit.RotatedKernelRefinementNotes.noteListRoot_binds, expected := .port }
  , { decl := `Dregg2.Circuit.RotatedKernelRefinementMisc.fixRootBinds, expected := .port }
  , { decl := `Dregg2.Circuit.RotatedKernelRefinementLifecycleDisc.discRoot_binds,
      expected := .port }
  , { decl := `Dregg2.Circuit.RotatedKernelRefinementProgram.setProgram_forced, expected := .port }
  , { decl := `Dregg2.Circuit.RotatedKernelRefinementCellSeal.lifecycleRoot_binds,
      expected := .port }
  , { decl := `Dregg2.Circuit.RotatedKernelRefinementBirth.accountsRoot_binds, expected := .port }
  , { decl := `Dregg2.Circuit.RotatedKernelRefinementBirth.accountsGrowForced, expected := .port }
  , { decl := `Dregg2.Circuit.RotatedKernelRefinementLifecycle.deathCertRoot_binds,
      expected := .port }
  , { decl := `Dregg2.Circuit.RotatedKernelRefinementLifecycle.auditSlotRoot_binds,
      expected := .port }
  , { decl := `Dregg2.Circuit.RotatedKernelRefinementLifecycle.auditSlotForced, expected := .port }
  , { decl := `Dregg2.Circuit.RotatedKernelRefinementLifecycle.refusal_forced, expected := .port }
  , { decl := `Dregg2.Circuit.RotatedKernelRefinementPermsVK.slotSetForced, expected := .port }
  , { decl := `Dregg2.Exec.FieldsMap.fieldsRoot_binds_tail, expected := .port }
    -- the endpoint: REFUSES — it applies the floor; the S2 extractor was the hand port.
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

def clusterImports : List Name :=
  [ `Dregg2.Circuit.ListCommitRegrounded
  , `Dregg2.Circuit.RotatedKernelRefinementNotes
  , `Dregg2.Circuit.RotatedKernelRefinementMisc
  , `Dregg2.Circuit.RotatedKernelRefinementLifecycleDisc
  , `Dregg2.Circuit.RotatedKernelRefinementProgram
  , `Dregg2.Circuit.RotatedKernelRefinementCellSeal
  , `Dregg2.Circuit.RotatedKernelRefinementBirth
  , `Dregg2.Circuit.RotatedKernelRefinementLifecycle
  , `Dregg2.Circuit.RotatedKernelRefinementPermsVK
  , `Dregg2.Exec.FieldsMap
  , `Dregg2.Tactics ]

def genHeader : String :=
"# Dregg2.Circuit.ListCommitPortedCone — the MACHINE-PORTED S3 cone of `ListDigestBindsList`.

GENERATED by `Dregg2.Tools.ConePort` (driver: `Tools/ConePortListCommitRun`, regenerate with
`CONE_PORT_WRITE=1 lake env lean Dregg2/Tools/ConePortListCommitRun.lean`), then AUDITED and
committed as source. Do not hand-edit ports in place; regenerate or supersede explicitly.

Each theorem below is a direct threader of `ListCommit.ListDigestBindsList` with the refuted
`compressNInjective` floor binder (and, where it was binder-carried, `listLeafInjective`) replaced
by per-instance `¬ Coll` side conditions instantiated at the EXACT arguments the original proof
passes — the elaborated term decided, never a regex. Conclusions are UNCHANGED (the S3 discipline:
the shape change is confined to the endpoint file, `Circuit/ListCommitRegrounded`).

HONEST-BUT-CONDITIONAL, stated rather than smuggled: each port is conditional on the deployed hash
not colliding at the NAMED per-instance points — a refutable, decidable-per-instance claim (at
1-felt widths ~2^15.5-breakable, `docs/WOUND-felt-width-boundaries-2026-07-19.md`), NOT a security
proof and NOT the refuted universal injectivity. The unconditional content lives in the endpoint's
S2 (`listDigest_binds_or_collides`) and the ROM headline (`listDigestRom_binds`); the teeth
(`canary_drop_moves_digest_or_collides`, `listDigest_binds_unconditional_false`,
`noColl_satisfiable`/`listColl_refutable`) live there too and gate this whole family.

Every port re-verifies at build; the pins below re-prove: axiom-clean, and the refuted floor +
the old endpoint are UNREACHABLE from every port."

elab "#cone_port_run" : command => do
  let write := (← IO.getEnv "CONE_PORT_WRITE").isSome
  liftTermElabM do
    let rep ← runCluster cfg targets
    logInfo m!"=== ConePort ListDigestBindsList cluster: ported={rep.ported.size} refused={rep.refusals.size} mismatches={rep.mismatches.size} ==="
    unless rep.mismatches.isEmpty do
      for m in rep.mismatches do logError m
      throwError "ConePort: the cluster moved under the pinned measurement — re-measure, understand WHY, then re-pin"
    if write then
      let txt := emitModule cfg clusterImports rep.ported genHeader
      IO.FS.writeFile "Dregg2/Circuit/ListCommitPortedCone.lean" txt
      logInfo "WROTE Dregg2/Circuit/ListCommitPortedCone.lean"

#cone_port_run

end Dregg2.Tools.ConePortListCommitRun
