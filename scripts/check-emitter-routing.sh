#!/usr/bin/env bash
# ⚑ EVERY Lean EMITTER MUST BE ROUTED, OR ITS ARTIFACT GOES STALE ON EVERY FLAG DAY.
#
# `scripts/emit_descriptors.py` carries an `EMITTERS` list. An `Emit*.lean` absent from it is never
# re-run by a geometry flag day, so the artifact it produced keeps whatever widths were current when
# somebody last ran it BY HAND — and the failure surfaces later as a test comparing a live descriptor
# against a months-old fixture, which reads as a stale test rather than a stale artifact.
#
# Measured 2026-07-31: THREE separate lanes hit this independently in one day, each rediscovering it
# from a different red:
#   * `circuit/tests/fixtures/{discharge,vault}-sat-v3-staged.json` went stale TWICE in two flag days
#     (`EmitDischargeVaultSat.lean` — unrouted), and a lane regenerated them by hand both times.
#   * `EmitExactNullifierAafiRotatedState.lean`'s 1274-constraint descriptor sat at
#     `staged-unregistered-no-vk` — an artifact nothing re-emitted. ✅ RESOLVED 2026-07-31 by
#     DELETION, not by routing: it was a SECOND producer of bytes `EmitByName.lean` (which IS in
#     `EMITTERS`) already emits from the same Lean definition into
#     `circuit/descriptors/by-name/faithful-note-spend-exact-v3.json`. The two copies had already
#     diverged — the registry copy moved to `trace_width` 3804 while the staged copy and its
#     bespoke `--check` pins stayed at 3760/1258 — and the divergence had rotted THREE runtime
#     constants in `circuit-prove`, leaving `staged_descriptor()` returning `Err` and
#     `relation_program_bytes()` PANICKING. Routing the duplicate would have kept two copies in
#     step; deleting it left one.
#   * A fields-nonet lane found `circuit/staged-descriptors/fnsp-v3/*` "had simply been omitted from
#     the flag day". Same artifact, same cause; that directory no longer exists.
#
# This gate does NOT force every emitter into the driver — several are genuinely one-shot goldens or
# probes, and sweeping them in would run 28 emitters on every flag day. It forces each one to be
# EXPLICIT: routed, or listed here with a reason. An emitter that is neither is the silent case.
#
# ─────────────────────────────────────────────────────────────────────────────────────────────────
# ⚑ 2026-07-31 — A REASON IN PROSE IS A CLAIM. THE CLASSES BELOW ARE CHECKED.
#
# The first version of this allowlist took a free-text string per entry. That is the same shape as a
# doc-comment: it is written once, it is never re-read, and it silently stops being true — an
# emitter excused as "covered by EmitByName" stays excused after somebody drops the routing entry,
# and an emitter excused as "one-shot golden" stays excused after somebody gives it a live consumer.
# The allowlist could not go red, so it was decoration.
#
# Every entry now carries a CLASS whose claim this script VERIFIES:
#
#   no-main|<why>                  — the file has NO root `def main`, so it is a library/proof
#                                    module, not an emitter executable; `lake env lean --run` on it
#                                    produces nothing and `EMITTERS` cannot take it.
#                                    CHECKED: the file must still have no `^def main`.
#   covered:<Emitter>:<leanDef>    — its artifact IS re-emitted, by a ROUTED emitter, off the SAME
#                                    Lean definition. This file is a second renderer of one object.
#                                    CHECKED: <Emitter> is in the driver's EMITTERS, and its source
#                                    still mentions <leanDef>.
#   regen:<script>|<why>           — the artifact has its OWN co-located regen/check pipeline (the
#                                    `COVERAGE_EXEMPT` pattern the driver already documents).
#                                    CHECKED: <script> exists AND names this emitter.
#   no-artifact|<why>              — it commits NOTHING: it writes to an argv/scratch directory, or
#                                    its output is pinned INTO Lean rather than into a file. There
#                                    is no artifact for a flag day to leave behind.
#
# A class whose check FAILS is a FAILURE, not a warning: the excuse stopped being true, which is
# exactly the moment the emitter became silent again.
#
# ⚑ AND `DIAGNOSED` IS NOT AN ALLOWLIST. Entries there STILL FAIL. They are the emitters that are
# genuinely the silent case, recorded with what is actually wrong so the next reader starts from the
# diagnosis instead of from a bare filename. Moving a name from DIAGNOSED to UNROUTED_OK requires
# one of the four checked classes above — there is no prose escape hatch.
set -uo pipefail
cd "$(dirname "$0")/.."

# ── SCOPE ─ this printf is the ONLY copy; it prints on every run, pass or fail. ───────
printf 'ANSWERS:         %s\nDOES NOT ANSWER: %s\n' \
  'is every TRACKED metatheory Emit*.lean either named in the EMITTERS list this script parses out of scripts/emit_descriptors.py, or listed in UNROUTED_OK below under one of four classes, three of which are re-checked right now: no-main (the file still has no line beginning `def main`), covered (the named covering emitter is in EMITTERS and its source still word-matches the named Lean def), regen (the named script exists and greps for this file basename) — and no-artifact, which is checked for NOTHING?' \
  'whether any artifact is FRESH, CORRECT, or read by anybody. Routing means a flag day re-runs the emitter; it is not a claim that the committed bytes equal what a re-run would produce, nor that a covering emitter renders the SAME object (EmitDischargeVaultSat is excused as covered while emitting bytes the routed pipeline does not). The class checks are greps for a name in a file, and untracked emitters are counted and NOT scanned.'

# ── Emitters deliberately NOT in the driver. Each carries a CHECKED class (see header). ──────────
declare -A UNROUTED_OK=(
  # ---- no-main: filename starts with `Emit`, but there is no emitter here at all. ---------------
  # `find -name 'Emit*.lean'` matches by FILENAME PREFIX, so it sweeps in the module that welds the
  # `emitEvent` EFFECT, the module that PROVES the emit round-trips, and the gnark emit LIBRARY.
  # None of them has a root `def main`; `lake env lean --run` cannot run any of them.
  [EmitEvent.lean]="no-main|the Argus weld of the emitEvent EFFECT (emitEventStep ⟺ RecStmt), not an emitter — filename prefix collision"
  [EmitRoundtrip.lean]="no-main|PROVES decode∘emitVmJson = id (the emit loses no field); a theorem module, emits nothing"
  [EmitFaithful.lean]="no-main|gnark emit LIBRARY (emit/decode/emit_faithful over R1csFr); imported, never run"
  [EmitJson.lean]="no-main|gnark JSON grammar library; its golden canonicityToyJson is #guard-pinned IN-KERNEL against chain/gnark/emitted/canonicity_toy.json — a stronger re-derivation check than a driver re-emit"
  [EmitVerifier.lean]="no-main|the keystone composition theorem (six gHolds leaf refinements into emitVerifier); emits nothing"
  [EmitEventWitness.lean]="no-main|witness GENERATOR + execute→prove→verify theorems for emitEventA; no artifact"
  [Market/EmitSameOpeningGadget.lean]="no-main|has emitMain, deliberately NOT a root def main: this module is IMPORTED (Market.lean → Dregg2.lean) and a root main collides with Dregg2/Apps/AgentOrchestration.lean:450. Geometry is #guard-pinned in-kernel (traceWidth 297, piCount 20, emitVmJson2 length 210314). Routing it needs a thin non-imported root runner first"

  # ---- covered: a ROUTED emitter already re-emits the artifact, off the SAME Lean def. ----------
  # Measured 2026-07-31 by running each of these and diffing against the checked-in bytes: all
  # IDENTICAL. They are second renderers of one object — kept because they run in seconds while the
  # full driver does not, but a flag day reaches the artifact through the ROUTED emitter.
  [EmitGraduate.lean]="covered:EmitAllJson.lean:EffectVmEmitIntroduce.introduceVmDescriptor|a focused SUBSET: all 16 of its descriptors are entries of EmitAllJson.lean's allEntries"
  # `EmitCheck.lean` and `EmitAutomataflGolden.lean` were the original prose excuses ("a checker,
  # not an emitter"; "one-shot game golden, no rotated geometry"). Both are stronger than that and
  # now say so checkably: each renders a Lean def a ROUTED emitter also renders.
  [EmitCheck.lean]="covered:EmitAllJson.lean:EffectVmEmitTransfer.transferVmDescriptor|prints transferVmDescriptor only — one entry of EmitAllJson.lean's allEntries; a smoke-test runner, not a producer"
  [EmitAutomataflGolden.lean]="covered:EmitByName.lean:automataflStepDesc|automatafl-step.json + automatafl-step-n11.json (EmitByName.lean:140,142)"
  [EmitDescentCensus.lean]="covered:EmitByName.lean:descentCensusDescriptor|descent-custody-census-fixed8-v1.json (EmitByName.lean:250)"
  [EmitPrivateShuffleFair.lean]="covered:EmitByName.lean:privateShuffleFairN8Descriptor|private-shuffle-fair-n8.json (EmitByName.lean:240)"
  [EmitShieldedWholeNoteSwapSubstrate.lean]="covered:EmitByName.lean:shieldedWholeNoteSwapSubstrateDescriptor|shielded-whole-note-swap-substrate-v1.json (EmitByName.lean:252)"
  [EmitTurnChain.lean]="covered:EmitByName.lean:turnChainBindingDescriptor|turn-chain-binding.json (EmitByName.lean:218)"
  [EmitPastaWindowed.lean]="covered:EmitByName.lean:windowedRowDesc|pasta-rcb-windowed.json (EmitByName.lean:295)"
  [EmitPastaSliced.lean]="covered:EmitByName.lean:slicedRowDesc|pasta-rcb-sg-slice-{0..3}-of-4{,-w8}.json (EmitByName.lean:300-316)"
  # The two FELT-SOUND runners. Both landed with their descriptors checked into by-name/ and NO
  # EmitByName entry — `--verify-by-name-routing` named pasta-f{p,q}mul-sound.json by hand on
  # 2026-08-03. Routed now; these runners survive only because they ALSO render the honest witness
  # TRACES into circuit/tests/fixtures/, which emit_descriptors.py structurally cannot install.
  [EmitPastaFpMulSound.lean]="covered:EmitByName.lean:fpMulSoundDesc|pasta-f{p,q}mul-sound.json; its trace arg renders circuit/tests/fixtures/pasta-fpmul-sound-trace.txt, which the driver cannot install"
  [EmitPastaAddSubSound.lean]="covered:EmitByName.lean:fpAddSoundDesc|pasta-f{p,q}{add,sub}-sound.json; its addtrace/subtrace args render circuit/tests/fixtures/pasta-fp{add,sub}-sound-trace.txt, which the driver cannot install"
  # ⚠ THE GATE'S OWN MOTIVATING EXAMPLE, AND IT HAS MOVED ON. The fixtures named in the header above
  # (circuit/tests/fixtures/{discharge,vault}-sat-v3-staged.json) NO LONGER EXIST; the two
  # descriptors now ride the ROUTED EmitRotationV3.lean as rows 59-60 of
  # circuit/descriptors/rotation-v3-staged-registry.tsv. But the two emitters DO NOT AGREE: the
  # routed one emits `dropUnforcedPins ∘ hardenLastRow ∘ fieldsCanonical9Wire` of the descriptor
  # (EmitRotationV3.lean:200,206) while this one emits the RAW `emitVmJson2 d`. Measured 2026-07-31:
  # discharge 97,383 B here vs 147,185 B in the registry; vault 214,785 B vs 278,681 B. So this
  # file's own docstring claim — "byte-faithful to what the big-bang registry regen will land" — is
  # FALSE, and running it "to refresh a fixture" installs pre-pipeline bytes. Excused because the
  # DEPLOYED object is routed; flagged because the scratch runner is a divergent second authoring
  # path and the right end-state is deleting it.
  [EmitDischargeVaultSat.lean]="covered:EmitRotationV3.lean:dischargeSatVmDescriptor2R24|registry rows 59-60 of rotation-v3-staged-registry.tsv — ⚠ this file's RAW emit DISAGREES with the routed pipeline-processed bytes (see comment)"

  # ---- regen: its own co-located regen/check pipeline. ------------------------------------------
  [EmitCertQpDescriptor.lean]="regen:circuit/descriptors/regen-cert-qp.sh|also named in emit_descriptors.py's COVERAGE_EXEMPT, which documents this exact arrangement"
  [EmitDungeonProgram.lean]="regen:dungeon-on-dregg/program/regen.sh|regenerate-and-diff gated; artifact is dungeon-on-dregg/program/dungeon_program.json"
  [EmitMultiwayTugProgram.lean]="regen:dregg-multiway-tug/program/regen.sh|run as \`regen.sh --check\` by .github/workflows/ci.yml:1605 — the only one of these wired into CI"
  [EmitFhIRClearingPlan.lean]="regen:fhegg-fhe/plans/regen.sh|artifact is fhegg-fhe/plans/rebalance-v1.json"
  # Not a descriptor at all: a shape-covering wire CORPUS anchoring the hand-written Rust
  # marshaller to the PROVED Lean encoder. Enforcement is dregg-lean-ffi/src/marshal_conformance.rs,
  # which joins on `<name>` and fails on a single byte — stronger than a re-emit, and it runs in the
  # Rust suite where the marshaller lives. REGENERATE.md:30 carries the exact emit command.
  [EmitMarshalGolden.lean]="regen:dregg-lean-ffi/goldens/REGENERATE.md|golden corpus dregg-lean-ffi/goldens/marshal-golden.txt, enforced byte-for-byte by dregg-lean-ffi/src/marshal_conformance.rs"
  # The four MinaWrapSrsG emitters MUST NOT be routed: each imports Dregg2.Circuit.Emit.MinaWrapSrsG
  # (32,768 pinned curve points, ~32-48 s just to ELABORATE), which is allowlisted out of the Dregg2
  # root by scripts/lean-orphans-allow.txt precisely so it stays off the descriptor-drift hot path.
  # Putting them in EMITTERS would drag that module into every flag day. Their artifacts are
  # sha256-pinned in the Rust tests instead (pasta_bound_sg_prove.rs::lean_artifacts_are_pinned,
  # pasta_oncurve_gate.rs, pasta_derive_prove.rs) — a byte pin is the check that actually reads them.
  [EmitPastaBound.lean]="regen:scripts/regen-pasta-bound.sh|imports MinaWrapSrsG (32,768 points); artifacts sha256-pinned in circuit/tests/pasta_bound_sg_prove.rs"
  [EmitPastaBoundScaled.lean]="regen:scripts/regen-pasta-bound-scaled.sh|imports MinaWrapSrsG; the row-count ladder measurement, same pinning"
  [EmitPastaOnCurve.lean]="regen:scripts/regen-pasta-oncurve.sh|imports MinaWrapSrsG; artifacts sha256-pinned in circuit/tests/pasta_oncurve_gate.rs"
  [EmitPastaDerive.lean]="regen:scripts/regen-pasta-derive.sh|imports MinaWrapSrsG; artifacts sha256-pinned in circuit/tests/pasta_derive_prove.rs"
  [EmitPastaDeriveChals.lean]="regen:scripts/regen-pasta-derive.sh|emits the 15 IPA CHALLENGES (public-input data), not a descriptor — no geometry; pasta_derive_prove.rs::manifest_digits_are_the_derived_s_vector RECOMPUTES the s-vector from it"

  # ---- no-artifact: nothing is committed, so a flag day has nothing to leave behind. ------------
  [EmitTinyAutomataPacked.lean]="no-artifact|writes 45 files into an ARGV directory (default /tmp/packed) for circuit/tests/tiny_automata_packed_rows_measure.rs; none is checked in"
  [EmitPastaWindowedTrace.lean]="no-artifact|emits an honest WITNESS TRACE (not a descriptor), argv-parameterized, generated live by circuit/tests/pasta_windowed_{prove,tamper}.rs"
  [EmitParamComposeShapes.lean]="no-artifact|its 16 shapes are byte-pinned INTO Lean (Dregg2/Circuit/Emit/ParamComposeGolden{,Shapes,Census}.lean), where the kernel checks them; no JSON is committed"

  # ── 2026-08-05 — THE NINETEEN THIS GATE HAD STOPPED CLASSIFYING. ───────────────────────────────
  # Every one of them was added AFTER this script's last update (`56bbbe1e2`, 08-03), so the gate
  # decayed by CALENDAR, not by defect: it went from naming 4 diagnosed emitters to printing 23
  # names of which 19 carried neither an entry nor a class. A red with nineteen unexplained rows is
  # a red a reader learns to skip, which is this gate's own failure mode pointed at itself.
  #
  # The PICKLES/KIMCHI HARNESS DRIVERS (9). Each writes into `/tmp/pickles-*/` — a scratch directory
  # its Rust harness crate reads back in the same session — and commits NOTHING. Two of them take
  # the destination from the environment (`DREGG_SM_OUT` / `DREGG_WM_OUT`) so two revisions can be
  # byte-diffed without colliding; the default is still `/tmp`. There is no artifact for a flag day
  # to leave behind, which is exactly the `no-artifact` class. (They ARE rooted — `PicklesEmitDrivers`
  # in metatheory/lakefile.toml compiles all nine — so an API change reds them. Rooting and routing
  # are different questions and this is the routing one.)
  [EmitComposeMsmJson.lean]="no-artifact|writes /tmp/pickles-compose/compose_msm{,_unwired}.json for the pickles-compose-harness crate; nothing is checked in"
  [EmitCurveGateJson.lean]="no-artifact|writes /tmp/pickles-curvegate/{complete_add,endo_mul_scalar,var_base_mul,endo_mul}.json for pickles-curvegate-harness; nothing is checked in"
  [EmitPoseidonJson.lean]="no-artifact|writes /tmp/pickles-poseidon/poseidon.json for pickles-poseidon-harness; nothing is checked in"
  [EmitPublicInputJson.lean]="no-artifact|writes /tmp/pickles-publicinput/pi_{mul_a,mul_b,nowire,wide}.json for pickles-publicinput-harness; nothing is checked in"
  [EmitStepFragmentJson.lean]="no-artifact|writes /tmp/pickles-stepfragment/stepfragment*.json (shape via DREGG_SF_SHAPE) for pickles-stepfragment-harness; nothing is checked in"
  # ⚠ ⚑ **THE `nothing is checked in` HALF OF THIS ROW WAS FALSE AND IS CORRECTED (2026-08-06).**
  # `metatheory/fixtures/pickles-stepmain-harness/fixtures/stepmain_step_r8_finalize.json` IS
  # tracked -- 10 347 rows, 67 published entries -- and it is the step proof the whole wrap ladder,
  # `KimchiStepWrapChainFixture` and `MinaWrapDeferredWords.WRAP_PUBLIC_INPUT_MEASURED` are about.
  # It still stays `no-artifact` for ROUTING purposes and the reason is worth writing down: the
  # driver writes only to `$DREGG_SM_OUT`, and the `/tmp -> fixtures/` hop is a MANUAL `cp` that no
  # script performs, so there is no route for this checker to grade. The tracked copy's own drift
  # guard is `pickles_kimchi_marshal`'s refusal (`c.name == "stepmain_step_r8_finalize"`,
  # `c.public_input_size == 67`), added the same day after the generator was found unable to
  # re-emit its own generated file. Saying "nothing is checked in" is how a tracked artifact stops
  # being anybody's job.
  [EmitStepMainJson.lean]="no-artifact|writes \$DREGG_SM_OUT (default /tmp/pickles-stepmain)/*.json for pickles-stepmain-harness; the tracked stepmain_step_r8_finalize.json is copied in BY HAND (no route to grade) and is guarded by pickles_kimchi_marshal's name/width refusal"
  [EmitStepWrapChainJson.lean]="no-artifact|writes /tmp/pickles-chain/chain{,bent,unread}_w*.json for pickles-chain-harness; nothing is checked in"
  # ⚑ **THIS ROW SAID `no-artifact` AND "no route to grade" UNTIL 2026-08-09, AND THE HOLE IT NAMED
  # WAS OPEN AT THAT MOMENT.** Thirty artifacts ARE tracked; the row's own grade — "the harness
  # proves each rung" — grades whatever JSON is on disk, not whether that JSON is this assembly, and
  # a stale fixture is a perfectly provable circuit. Measured: the tracked thirty were last written
  # at 93bca7b7a and three later commits (through 0047cb876's runIpa rewire) moved the wrap assembly
  # under them, so the harness had been proving a two-day-old circuit and reporting GREEN.
  # The refusal is `EmitWrapMainJson.installedGate`, INSIDE the emitter, so a re-emit that does not
  # install cannot slip past it; the script below is the named route and its `--check`.
  [EmitWrapMainJson.lean]="regen:scripts/regen-wrapmain-fixtures.sh|the thirty tracked metatheory/fixtures/pickles-wrapmain-harness/fixtures/wrapmain_smoke_*.json; that script re-emits them and EmitWrapMainJson.installedGate REFUSES when a tracked file is not what the run emits (--check turns the drift into an exit code, DREGG_WM_INSTALL=1 installs). The wrap-scale (DREGG_WM=wrap) emission has no tracked twin"
  [EmitWrapFinDeferred.lean]="no-artifact|prints the three §15c‴ deferred words to stdout; they are typed INTO Lean (KimchiWrapMainCore's FIN_DEFERRED_CIP/_B/_XI) and discharged there by fin_deferred_words_are_the_derivation — no file"
  # ⚑ A DRIVER, NOT AN EMITTER — its own docblock says so ("IT IS A DRIVER, NOT A GATE. Nothing here
  # is a theorem and nothing here can go red"). It prints the emitted forty against
  # WRAP_PUBLIC_INPUT_MEASURED slot by slot at BOTH shapes, and writes no file at all; the gates it
  # re-derives are `the_forty_agree_but_for_slot_twelve` (KimchiWrapMainPins12) and
  # `slot_eleven_agrees_and_slot_twelve_still_disagrees` (KimchiWrapMainPins10).
  [EmitWrapFortyAgreement.lean]="no-artifact|prints the emitted forty against MinaWrapDeferredWords.WRAP_PUBLIC_INPUT_MEASURED, slot by slot, at shapeSmoke AND shapeWrap; a re-derivation driver for the two Pins theorems, no file"

  # ---- covered: the by-name route already re-emits these bytes off the SAME Lean def. -----------
  # Each prints `emitVmJson2` of a descriptor `EmitByName.lean` also renders, and `EmitByName` IS
  # routed. They survive as focused runners because the by-name table's import closure is a strict
  # superset of each of theirs.
  #
  # ⚑ 2026-08-05 — `EmitMinaLightClient.lean` IS DELETED, and its output is the reason. It existed
  # for one stated day: `EmitByName.lean` could not run (its length pin said 92 against 91 rows, so
  # `rfl` failed and the whole by-name surface was unemittable), and a lane redirected this runner
  # into `dregg-mina-lightclient-verify-v1.json` by hand. The Lean then moved underneath the file —
  # `ProofBind` widened to eight lanes — and nothing re-ran the redirect, so production served 70
  # constraints where Lean authored 62: NINE narrow one-lane `proof_bind`s, each tying ONE limb of
  # an eight-felt commitment, in place of the one widened bind. The pin is fixed and the canonical
  # emit re-derives that file, so a second route to those bytes is not a convenience, it is the
  # mechanism. One renderer.
  [EmitMinaLink.lean]="covered:EmitByName.lean:minaLinkDesc|dregg-mina-lightclient-link-v1.json (EmitByName.lean:395)"
  [EmitSolStakeFold.lean]="covered:EmitByName.lean:solStakeFoldDesc|dregg-solana-stake-table-fold-v1.json (EmitByName.lean:418)"
  # ⚠ A THIRD RENDERER OF THE SAME SIX, AND IT SHOULD BE DELETED. `EmitLcTmp.lean` prints
  # `<name>\\t<emitVmJson2 d>` for all six light-client descriptors, every one of which is a row of
  # `EmitByName.lean`'s table; it was untracked scratch until `dc5abe4ab` committed it. It writes to
  # STDOUT and commits nothing, so no flag day leaves an artifact behind through it — but greenfield
  # prefers deleting the old thing to keeping both. Classified rather than deleted only because it
  # landed mid-session from another lane; the right end-state is one renderer, and the Mina half of
  # that end-state landed above (`EmitMinaLightClient.lean` is gone).
  [EmitLcTmp.lean]="covered:EmitByName.lean:ethLcVerifyDesc|prints all six LC descriptors (eth/tm/solana/midnight/mina/mina-link) to stdout — every one a row of EmitByName.lean (:350,352,372,374,385,395); commits nothing"
  # ⚠ AND A FINDING THE CLASS DOES NOT CARRY. `EmitPastaAlu.lean` also renders `fqAluDesc` into
  # `circuit/descriptors/by-name/pasta-alu-fq-sound.json` — a committed, ROUTED descriptor with
  # ZERO readers anywhere in the tree: no `include_str!`, no test, no script. Its Fp twin
  # `pasta-alu-sound.json` is read by `circuit/tests/pasta_alu_verifier_row_proves.rs`. Routing is
  # therefore CORRECT here and insufficient: a flag day will faithfully re-emit bytes nothing
  # checks. That is a consumer question, not a routing one, and it is recorded here because this is
  # where the next reader will be standing.
  [EmitPastaAlu.lean]="covered:EmitByName.lean:fpAluDesc|pasta-alu-{,fq-}sound.json + pasta-sbox-prog{,-1k}.json (EmitByName.lean:235-242); its trace/pis/sboxtrace/sboxpis args render circuit/tests/fixtures/pasta-{alu,sbox}-*.txt, which the driver structurally cannot install"

  # ---- regen: its own co-located regen/check pipeline. ------------------------------------------
  [Dregg2/Games/PathOfAngels/EmitMain.lean]="regen:scripts/check-poag1-artifacts.sh|the POAG1 three-phase emit; that script re-runs all three phases, measures SHA-256 over what each produced, and byte-compares against the checked-in bundle"
  [EmitConformanceVectors.lean]="regen:scripts/pickles-crossimpl-differential.sh|the LEAN half of the Lean<->Rust Pickles differential; that script re-runs both halves and requires the two TSVs to be BYTE-IDENTICAL"
  # ⚑ THE TWO REGEN SCRIPTS BELOW WERE WRITTEN ON 2026-08-05 BECAUSE THESE TWO EMITTERS HAD NO
  # RE-DERIVATION PATH AT ALL. Between them they produce 25 COMMITTED files whose only route back to
  # the Lean was a human retyping shell redirections out of a docstring — the precise shape of the
  # `{discharge,vault}-sat-v3-staged.json` wound in this script's own header, twice over. Neither
  # can join `EMITTERS`: most of their output lands in `circuit/tests/fixtures/`, which
  # `emit_descriptors.py` structurally cannot install (see the note at the bottom).
  # ⚑ 2026-08-05 SPLIT: its 8 by-name DESCRIPTORS moved into `EmitByName.lean`'s routing table, so
  # they now come out of `emit_descriptors.py` under the recursive coverage check like every other
  # by-name artifact. Only the fixtures — which that driver structurally cannot install — remain here.
  [EmitCommitStages.lean]="regen:scripts/regen-mina-commit-stages.sh|15 fixture artifacts under circuit/tests/fixtures/ (mina-commit-{xi,pub,f,ft,agg,ladder}-{trace,pis}.txt, mina-xi-endo-lift-{trace,pis}.txt, mina-commit-golds.txt), read by mina_commit_stages_prove.rs, mina_xi_endo_weld.rs and pasta_msm_bucketed_prove.rs; its 8 by-name descriptors are rows of EmitByName.lean"
  [EmitPastaBucketed.lean]="regen:scripts/regen-pasta-bucketed.sh|4 artifacts under circuit/tests/fixtures/pasta-msm-bucketed/, sha256-pinned in circuit/tests/pasta_msm_bucketed_prove.rs; MUST NOT be routed — it imports MinaWrapSrsG/MinaStepSrsG (32k/64k pinned points), the same reason EmitPastaBound is not routed"

  # ---- no-main: a library in the Emit* filename namespace, not an emitter. ----------------------
  [Dregg2/Games/PathOfAngels/Emit.lean]="no-main|the POAG1 ARTIFACT BOUNDARY (ingestManifest + the bundle projection) — a library imported by EmitMain.lean and by the PoA runtimes; it has no root def main and lake env lean --run on it produces nothing"
)

# ── STILL FAILING, with a diagnosis. NOT an excuse — these are the silent case. ───────────────────
declare -A DIAGNOSED=(
  [EmitTurnAuthProbe.lean]="artifacts circuit/tests/turn-auth-lamport-probe-nb{1,8}.json are COMMITTED and include_str!'d live by circuit/tests/turn_auth_in_air_refuses.rs:47,49 — and that test asserts SHAPE ONLY (d.trace_width vs l.width), with NO sha256 pin and NO regen script. Nothing re-derives these bytes. Re-emitted 2026-07-31: byte-identical today. Routing needs the driver to be able to install OUTSIDE circuit/descriptors/ (see the note below)."
  [EmitKimchiCellCommit.lean]="artifact bridge/mina-zkapp/src/generated/kimchi-cellcommit-b.json (2.2 MB) is committed and read by bridge/mina-zkapp/src/DreggCellCommitNative.ts. CheckKimchiCellCommit.lean gates the EMISSION, not the committed BYTES: scripts/check-kimchi-cellcommit.sh does not diff the artifact and is not in scripts/local-gates.sh. Re-emitted 2026-07-31: byte-identical today."
  [EmitKimchiIncNonce.lean]="artifact bridge/mina-zkapp/src/generated/kimchi-incnonce-b.json is committed and read by bridge/mina-zkapp/src/DreggIncNonceNative.ts. No regen script, no byte pin, no drift gate. Re-emitted 2026-07-31: byte-identical today."
  [EmitKimchiPoseidon2.lean]="artifact bridge/mina-zkapp/src/generated/kimchi-poseidon2-w16.json is committed and read by src/Poseidon2Native.ts:107; the emitter RUNS again as of the joinS repair (was: deep recursion at the interpreter, a non-tail-recursive hand-rolled join). Routing it needs emit_descriptors.py to learn a bridge/mina-zkapp destination — driver work, not an excuse."
)

routed=$(python3 - <<'PY'
import pathlib, re
d = pathlib.Path("scripts/emit_descriptors.py").read_text()
m = re.search(r"EMITTERS = \[(.*?)\n\]", d, re.S)
for f in re.findall(r'"([^"]+\.lean)"', m.group(1) if m else ""):
    print(f.split("/")[-1])
PY
)

# ── verify one allowlist entry's CLASS. echoes a reason on failure. ──────────────────────────────
verify_class() {
  local path="$1" spec="$2" class rest
  class="${spec%%|*}"; rest="${spec#*|}"
  case "$class" in
    no-main)
      if grep -qE '^def main' "$path"; then
        echo "excused as 'no-main' but it NOW HAS a root \`def main\` — it became a real emitter"
        return 1
      fi ;;
    no-artifact) : ;;   # prose class; the emitter's existence is the loop's own precondition
    covered:*)
      local emitter def epath
      emitter="$(cut -d: -f2 <<<"$class")"; def="$(cut -d: -f3 <<<"$class")"
      if ! grep -qx "$emitter" <<<"$routed"; then
        echo "excused as covered by '$emitter', but '$emitter' is NOT in the driver's EMITTERS"
        return 1
      fi
      epath="$(find metatheory -name "$emitter" -not -path '*/.lake/*' | head -1)"
      if [ -z "$epath" ]; then
        echo "excused as covered by '$emitter', which does not exist under metatheory/"
        return 1
      fi
      # ⚑ `-w`, NOT a bare substring. Caught by this script's own red-proof on 2026-07-31: a
      # substring match still succeeds after `descentCensusDescriptor` is renamed to
      # `descentCensusDescriptorV2`, so the excuse survived the exact event it is supposed to
      # detect. A word-boundary match reds on a rename, which is how these defs actually move.
      if ! grep -qw -- "$def" "$epath"; then
        echo "excused as covered by '$emitter' via \`$def\`, but '$emitter' no longer mentions it — the artifact lost its re-emit path"
        return 1
      fi ;;
    regen:*)
      local script
      script="${class#regen:}"
      if [ ! -f "$script" ]; then
        echo "excused by regen script '$script', which does not exist"
        return 1
      fi
      if ! grep -q "$(basename "$path")" "$script"; then
        echo "excused by regen script '$script', which no longer names $(basename "$path")"
        return 1
      fi ;;
    *)
      echo "unknown class '$class' — the four checked classes are no-main / covered: / regen: / no-artifact"
      return 1 ;;
  esac
  return 0
}

# ── THE POPULATION: TRACKED files only (`git ls-files`), same rule as check-dark-modules.py and
# check-export-callers.py, and for the same reason. ⚑ 2026-08-05: this was `find`, which sweeps the
# WORKING TREE, so in a shared tree with nine live lanes this gate graded other people's unsaved
# scratch. `metatheory/EmitLcTmp.lean` — a six-line re-print of six descriptors `EmitByName.lean`
# already emits — sat here UNTRACKED and red for everybody, and the only ways to clear it were to
# classify a file nobody had committed or to delete another lane's working file. (It was committed
# mid-session as `dc5abe4ab` and is classified below, which is the point: an UNCOMMITTED emitter
# cannot leave a COMMITTED artifact stale, and it becomes this gate's business the moment it is
# `git add`ed — not before.) It is NOT hidden either way: the untracked count is printed
# unconditionally below, so the gap between what was scanned and what exists is a number on the same
# screen as the verdict, never a subtraction the reader has to think to perform.
mapfile -t emitters < <(git ls-files 'metatheory/*Emit*.lean' 'metatheory/**/Emit*.lean' \
  | grep -E '(^|/)Emit[^/]*\.lean$' | grep -v '/\.lake/' | sort -u)
untracked_n="$(git ls-files --others --exclude-standard 'metatheory/*Emit*.lean' 'metatheory/**/Emit*.lean' \
  | grep -cE '(^|/)Emit[^/]*\.lean$' || true)"

# ── NON-VACUITY. A gate that scans an empty set greens, and its closing line then says "every Lean
# emitter is routed" about nothing at all. `check-lean-orphans.sh` states this rule and enforces it;
# this script stated neither until 2026-08-05. The floor is well under the live population (~60) and
# well over anything a broken path glob would return.
if [ "${#emitters[@]}" -lt 30 ]; then
  echo "check-emitter-routing: FATAL — found ${#emitters[@]} tracked Emit*.lean under metatheory/ (floor 30)." >&2
  echo "  That is a blinded scan, not a small tree: the path glob or the git index is wrong." >&2
  exit 2
fi
if [ -z "$routed" ]; then
  echo "check-emitter-routing: FATAL — the driver's EMITTERS list parsed EMPTY." >&2
  echo "  Every emitter would then read as unrouted, or (with an empty population) none would." >&2
  exit 2
fi

fail=0
broken_excuse=0
excused=0
routed_n=0
declare -a unrouted=()
for p in "${emitters[@]}"; do
  n="$(basename "$p")"
  if grep -qx "$n" <<<"$routed"; then routed_n=$((routed_n + 1)); continue; fi
  # allowlist keys are basenames, except where two trees share one (Market/EmitSameOpeningGadget).
  key="$n"; [[ -v UNROUTED_OK["$key"] ]] || key="${p#metatheory/}"
  if [[ -v UNROUTED_OK["$key"] ]]; then
    if ! why="$(verify_class "$p" "${UNROUTED_OK[$key]}")"; then
      echo "  BROKEN EXCUSE  $p"
      echo "                 $why"
      broken_excuse=$((broken_excuse + 1))
      fail=$((fail + 1))
    else
      excused=$((excused + 1))
    fi
    continue
  fi
  unrouted+=("$p")
  fail=$((fail + 1))
done

for p in ${unrouted+"${unrouted[@]}"}; do
  n="$(basename "$p")"
  echo "  UNROUTED  $p"
  if [[ -v DIAGNOSED["$n"] ]]; then
    echo "            ${DIAGNOSED[$n]}"
  fi
done

if [ "$fail" -ne 0 ]; then
  cat <<'MSG'

check-emitter-routing: FAIL — the emitters above are in NEITHER the driver's EMITTERS list NOR the
allowlist in this script (or their allowlist CLASS stopped being true).

Each one is an artifact that a geometry flag day will silently leave behind. Either:
  * add it to `EMITTERS` in scripts/emit_descriptors.py (it re-emits with everything else), or
  * add it to UNROUTED_OK here under one of the four CHECKED classes (no-main / covered: / regen: /
    no-artifact). There is no free-text class: a reason this script cannot verify is a reason that
    stops being true without anything going red.

"It has always been like that" is not a reason — three lanes rediscovered this in one day.

⚑ NOTE ON WHY THE REMAINING ONES ARE NOT A ONE-LINE FIX. `emit_descriptors.py` can only install
into `circuit/descriptors/` (plus RUST_FP_FILES and GENERATED_RS_PATHS — see `guarded_paths()`).
Every emitter still listed above writes somewhere else: `circuit/tests/`,
`bridge/mina-zkapp/src/generated/`. Routing one therefore means teaching the driver a new install
destination AND extending `--list-guarded-paths` so `check-descriptor-drift.sh` snapshots it —
otherwise the driver would rewrite a file the drift gate cannot see, which is the hole that
script's own header records. That is real work, and it is the work; it is not a reason to excuse
them.
MSG
  echo
  echo "check-emitter-routing: scanned ${#emitters[@]} tracked Emit*.lean — $routed_n routed, $excused excused (class verified), $broken_excuse broken excuse(s), ${#unrouted[@]} unclassified; $untracked_n untracked Emit*.lean not scanned."
  exit 1
fi
# ⚑ THE VERDICT NAMES ITS POPULATION. This line used to read "PASS — every Lean emitter is routed,
# or excused under a class this script verified" and nothing else. That sentence is true of an empty
# scan, and it is the sentence a reader quotes. The floor above makes an empty scan impossible; these
# numbers make a SHRINKING one visible, which the floor alone does not.
echo "check-emitter-routing: PASS — all ${#emitters[@]} tracked Emit*.lean under metatheory/ are accounted for: $routed_n routed through scripts/emit_descriptors.py, $excused excused under a class this script re-verified just now.${untracked_n:+ ($untracked_n untracked Emit*.lean present and NOT scanned — commit one and it becomes this gate's business.)}"
