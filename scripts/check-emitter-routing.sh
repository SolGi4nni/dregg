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

fail=0
broken_excuse=0
declare -a unrouted=()
while IFS= read -r p; do
  n="$(basename "$p")"
  grep -qx "$n" <<<"$routed" && continue
  # allowlist keys are basenames, except where two trees share one (Market/EmitSameOpeningGadget).
  key="$n"; [[ -v UNROUTED_OK["$key"] ]] || key="${p#metatheory/}"
  if [[ -v UNROUTED_OK["$key"] ]]; then
    if ! why="$(verify_class "$p" "${UNROUTED_OK[$key]}")"; then
      echo "  BROKEN EXCUSE  $p"
      echo "                 $why"
      broken_excuse=$((broken_excuse + 1))
      fail=$((fail + 1))
    fi
    continue
  fi
  unrouted+=("$p")
  fail=$((fail + 1))
done < <(find metatheory -name 'Emit*.lean' -not -path '*/.lake/*' | sort)

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
  exit 1
fi
echo "check-emitter-routing: PASS — every Lean emitter is routed, or excused under a class this script verified."
