#!/usr/bin/env bash
# pickles-synthesis-oracles.sh — run the Pickles-in-Lean SYNTHESIS byte-diff oracles as ONE command,
# green-or-bust. Each oracle is the o1js / real-chain SIDE of a `metatheory/Dregg2/{Circuit/Emit,
# Bridge}/*.lean` EMIT module (rooted in the `PicklesSynthesis` lean_lib target). The Lean side runs
# in `lake build PicklesSynthesis`; THIS script runs the differential half — the byte-exactness of the
# emitted gates/placement/statement-packing against o1js 2.15.0 and a live kimchi-verified devnet block
# — so the diffs are re-checkable on demand, not one-shot elaboration-time `#guard`s.
#
# ⚑ SHARED HARNESS. Three of the diffs now route their byte-walk through `bridge/mina-zkapp/scripts/
# diff-oracle.mjs` — the one differential-oracle harness (a REFERENCE producer + a CANDIDATE producer +
# an ordered {name,value} vector diff + exit-red-on-divergence + a RED-PATH self-test). Step 0 runs the
# harness engine's standalone `--self-test` (proves the diff reports RED on corruption for all three
# shapes), and the MIGRATED oracles are invoked with `--self-test` so each one MEASURES its own red path
# (green diff + corruption-bites) in this same run. A diff that cannot go red is documented-not-detected.
#
# EXIT: 0 iff every green-or-bust step exits 0; non-zero (and the first RED named) otherwise.
# Each oracle `process.exit(1)`s on any byte divergence, so a bent gate coeff / mis-placed wire /
# permuted statement field turns this command RED.
#
# ⚑ AND ONE THAT IS NOT A BYTE-DIFF AGAINST A BLOCK. Every oracle above compares a Lean emission to
# ONE reference value — one o1js render, one devnet block. `pickles-crossimpl-differential.sh` is the
# CROSS-IMPLEMENTATION half: it drives dregg's Lean value layer AND o1-labs' `proof-systems` 0.3.0
# over a deterministic sweep of 2576 inputs across 15 function pairs and requires the two vectors to
# be byte-identical. That is evidence about THE FUNCTION rather than about a value at one input, and
# it carries its own three-polarity red-path self-test.
#
# USAGE:  scripts/pickles-synthesis-oracles.sh            # run all (harness self-test + every oracle)
#         scripts/pickles-synthesis-oracles.sh --no-ts    # skip the .ts oracles (no ts-node)
#         scripts/pickles-synthesis-oracles.sh --no-xi    # skip the cross-implementation differential
#
# ⚠ The cross-impl differential runs the Lean emitter under the interpreter (minutes) and, unless
# `PICKLES_XI_RUST_VECTORS` points at a vector file produced elsewhere, a cold kimchi+arkworks cargo
# build. On a build box that is the right thing; `--no-xi` exists for the fast pass.
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
ZK="$ROOT/bridge/mina-zkapp"
cd "$ZK" || { echo "pickles-oracles: cannot cd $ZK"; exit 2; }

RUN_TS=1
RUN_XI=1
for a in "$@"; do
  case "$a" in
    --no-ts) RUN_TS=0 ;;
    --no-xi) RUN_XI=0 ;;
  esac
done

# ── SCOPE ─ this printf is the ONLY copy; it prints on every run, pass or fail. ───────
printf 'ANSWERS:         %s\nDOES NOT ANSWER: %s\n' \
  'does every green-or-bust step listed below exit 0 — the diff-oracle harness engine and the multiblock-conformance red paths, the four .mjs byte-diff oracles against o1js and against the compiled Mina circuit blobs, the wrap and step region- and shape-conformance gates with their self-tests, the emit-provenance freshness floor, the prover-freedom ratchet, the three ts-node statement oracles against devnet block 539508, the VK-derivation and proof-marshal gates, and the Lean-versus-proof-systems cross-implementation differential — with exit 3 named BLOCKED and still counted as a failure?' \
  'whether any of it VERIFIES. Every step is a BYTE DIFF against one reference (one o1js render, one devnet block, one compiled blob) or a red-path proof of a differ; byte-agreement and successful parsing are not membership, and no proof produced here is verified by a Mina node. ⚠ --no-ts and --no-xi DROP steps while the closing line still reads ALL GREEN and still names the cross-implementation differential.'

# The green-or-bust diffs. `custom-gate-oracle.mjs` is a DUMP (always exit 0), not a gate — omitted.
MJS_ORACLES=(
  "custom-gate-diff.mjs"               # R2: emitted custom-gate typ+coeffs (poseidon 165 coeffs) vs o1js
  "pickles-placement-oracle.mjs"       # R1: {row,col} copy-permutation wires vs live o1js
  "mina-canonical-circuit-oracle.mjs"  # R4: MINA'S OWN wrap+step gate lists as the byte TARGET
  "stepmain-region-conformance.mjs"    # R5: our `verify_one` vs Mina's step circuit GATE BY GATE
)
TS_ORACLES=(
  "pickles-r3-branchdata-oracle.ts"    # R3: branch_data prefix-mask pack vs devnet block 539508
  "pickles-statement-oracle.ts"        # R3: WHOLE Wrap statement packing vs the same block
  "pickles-step-statement-oracle.ts"   # R3: Step per-proof layout + fq=Type2/Fq field-key
)

# Oracles migrated to the shared diff-oracle.mjs harness — invoked with `--self-test` so each MEASURES
# its own red path (corrupted candidate → exit 1) alongside the live green diff.
MIGRATED="custom-gate-diff.mjs pickles-placement-oracle.mjs mina-canonical-circuit-oracle.mjs stepmain-region-conformance.mjs pickles-r3-branchdata-oracle.ts"

# `stepmain-region-conformance.mjs` additionally carries SIX falsifiers of its own (`--falsify`, passed
# in the loop below): five bend the Lean gate list by the smallest possible amount — one Poseidon round
# constant, one wire inside a Poseidon body, one retyped VarBaseMul, one Generic selector coefficient,
# one wire inside an EndoMul-32 body — and DEMAND the conformance vector move; the sixth drops the
# σ-probe rows so the ledger's OTHER leg bites too (a divergence that stops being observed is a stale
# allowance and must be red). A gate-by-gate diff a bent coefficient does not move would be decoration.
is_migrated() { case " $MIGRATED " in *" $1 "*) return 0;; *) return 1;; esac; }

fails=0
blocked=0
declare -a FAILED=()
declare -a BLOCKED=()
# ⚑ EXIT 3 IS A MISSING PREREQUISITE; EXIT 1 IS A DEFECT. THEY MUST NOT LOOK THE SAME.
# ⚠ 2026-08-03: this printed `RED: <name> (exit $?)` for both, so "no `DREGG_WM=wrap` emission on
# this box" and "the Lean assembly diverges from Mina's compiled wrap circuit" arrived as the same
# line. A reader cannot act on that, and the predictable response to an unactionable red is to stop
# reading the gate. The two conformance gates and the freedom ratchet all already SPEAK the
# distinction — they exit 3 on a stale/absent Lean input and 1 on divergence — and it was being
# thrown away one level up.
# ⚠ AND BLOCKED IS STILL NON-ZERO OVERALL. A prerequisite that is absent means the diff DID NOT RUN,
# which is not a pass. Separating the two is about making the failure actionable, never about
# letting one through: `== N ORACLE(S) RED · M BLOCKED ==` exits 1 either way.
run_one() { # name, cmd...
  local name="$1"; shift
  local rc
  echo "── $name ─────────────────────────────────────────────"
  if "$@"; then
    echo "   GREEN: $name"
  else
    rc=$?
    if [ "$rc" -eq 3 ]; then
      echo "   BLOCKED: $name (exit 3 — a PREREQUISITE is absent or stale, not a divergence)"
      blocked=$((blocked + 1)); BLOCKED+=("$name")
    else
      echo "   RED:   $name (exit $rc)"
      fails=$((fails + 1)); FAILED+=("$name")
    fi
  fi
  echo
}

echo "== Pickles-synthesis byte-diff oracles (green-or-bust) =="
echo

# Step 0: the shared harness engine's OWN red-path proof — corruption must make the diff report RED for
# every shape (gates|statement|field). If this is GREEN the migrated oracles' `--self-test`s are trustworthy.
run_one "diff-oracle.mjs --self-test (harness engine red-path)" node "scripts/diff-oracle.mjs" --self-test

# ⚑ Step 0b: THE MULTI-BLOCK CONFORMANCE GATE — the one that stops every real-data claim in this
# tree from being about a single devnet block. Every oracle below and every `MinaWrap*Weld.lean`
# was, until 2026-08-02, pinned to block 539508 alone; `Dregg2/Bridge/MinaMultiBlockConformance.lean`
# re-runs the same weld functions on seven fixtures (five devnet incl. the hardfork genesis, one
# mainnet, plus 539508 as the control) and this gate keeps that generated module answerable to the
# fixtures' own bytes: declared + tracked + decoding + byte-identical inputs, and the deferred
# targets agreeing across two openmina functions. It runs its OWN `--self-test` first, so a run in
# which the gate could not go red is itself RED. The Lean `#guard`s are run by `lake build`
# (`Dregg2.MinaBridgeGuards`, a `defaultTargets` library) — this half needs neither lean nor cargo.
run_one "check-mina-multiblock-conformance.py --self-test (gate red-path)" \
  python3 "$ROOT/scripts/check-mina-multiblock-conformance.py" --self-test
run_one "check-mina-multiblock-conformance.py (7 fixtures, 2 networks)" \
  python3 "$ROOT/scripts/check-mina-multiblock-conformance.py"

# ⚑ AND THE FRESHNESS FLOOR (2026-08-02). `stepmain-region-conformance.mjs` read
# `/tmp/pickles-stepmain/*.json` with NO freshness check: MEASURED, an artifact back-dated four days
# scored GREEN, exit 0, and reported `fixture: in sync`. It is the instrument behind essentially every
# "conformance GREEN byte-exact / EndoMul 32×77 intact / ten falsifiers biting" statement in this
# tree, so a stale read there is a whole night of claims about a file nobody emitted. Its inputs now
# carry a PROVENANCE STAMP naming the Lean source cone they came from, checked against the tree on
# every run and REFUSED on mismatch — and `--stale-self-test` rides along HERE so that floor's own red
# path is MEASURED in this suite (4 stale shapes refused + 1 honest-emission anchor), not merely
# documented. A freshness gate nobody proves can go red is the defect it was built to close.
for o in "${MJS_ORACLES[@]}"; do
  extra=""
  [ "$o" = "stepmain-region-conformance.mjs" ] && extra="--falsify --stale-self-test"
  if is_migrated "$o"; then
    run_one "$o" node "scripts/$o" --self-test ${extra:+$extra}
  else
    run_one "$o" node "scripts/$o"
  fi
done

# ⚑ THE WRAP HALF, which was in NO gate script at all until 2026-08-03. `wrapmain-region-conformance.mjs`
# is `stepmain`'s twin over `wrap_main` — a different field (Tock/Fq), a different PRIMARY_LEN, and the
# thing the step side never had: a SECOND independently compiled blob (`wrap-blockchain`) to cross-check
# every non-Generic fact against. It carried two defects the census measured at `9b3312500`:
#   * `--report` exited 0 BEFORE the vector diff, so every divergence was printed and discarded;
#   * `field/modulus` compared `FQ.toString()` to `FQ.toString()` — the constant to itself, green for
#     ANY value including `FP`, which is precisely the confusion its docblock said it guarded.
# Both are repaired. The modulus is now RECOVERED from Mina's own blob (`max coefficient + 1`; measured
# `q-1` in both wrap blobs and `p-1` in the step blob), and `--self-test` proves it bites.
# ⚠ TWO STEPS, DELIBERATELY. `--self-test` needs neither Lean nor an emission — it grades Mina's blobs
# and re-invokes the gate under a fail-closed bend, requiring exit 1 under `--report`. The FULL gate
# needs a `DREGG_WM=wrap` emission and REFUSES (exit 3) without one, which is the freshness floor
# working; run it with `--emit` on a box that can build Lean.
run_one "wrapmain-region-conformance.mjs --self-test (blob-fact red path + --report exit code)" \
  node "scripts/wrapmain-region-conformance.mjs" --self-test
run_one "wrapmain-region-conformance.mjs (Lean wrap assembly vs 2 compiled wrap_main blobs)" \
  node "scripts/wrapmain-region-conformance.mjs"

# ⚑ AND THE SCOREBOARD, WHICH WAS A SCRATCHPAD `census.py` UNTIL 2026-08-04. The region-conformance
# gate above grades gate BY gate inside the regions it knows; this one answers the question the epoch
# is actually measured by — WHAT FRACTION OF MINA'S WRAP CIRCUIT DO WE EMIT — and ratchets it.
# ⚑ IT ASSEMBLES SOMETHING NO SINGLE ARTIFACT HOLDS: `rungsUpto` is a TREE, three branches off
# `w9_prev`, so `w11_bullet.json` is `prev+combine+bullet` and holds no finalize/wraphack/close.
# Censusing one file UNDERSTATES the assembly; summing the files DOUBLE-COUNTS `w9_prev` five times.
# The union is prefix-stripped and the prefix relation is VERIFIED on the emitted bytes.
# MEASURED at the committed wrap shape over all fourteen rungs: 12550/15122 = 83.0%, EndoMul
# 2528/2528, VarBaseMul 2417/2417, CompleteAdd 492/492, PI 24 of the 24 slots `wrap_main` pins.
# ⚠ Same two-step shape as the gate above: `--self-test` needs neither Lean nor an emission, and the
# full grade REFUSES (exit 3) without a `DREGG_WM=wrap` emission of all fourteen rungs.
run_one "wrapmain-shape-diff.mjs --self-test (ratchet bites + the assembly floor blocks)" \
  node "scripts/wrapmain-shape-diff.mjs" --self-test
run_one "wrapmain-shape-diff.mjs (14-rung census ratchet vs Mina's wrap-transaction)" \
  node "scripts/wrapmain-shape-diff.mjs"

# ⚑ THE TWO THAT WERE IN NO SCRIPT AT ALL, AND WHY THEY ARE HERE NOW (2026-08-03).
#
# `stepmain-shape-diff.mjs` PRINTED TWO TABLES AND EXITED 0 — no comparison, no failure counter, no
# verdict — and `grep -rn` found it referenced only from `HORIZONLOG.md` and one docblock. So
# HORIZONLOG:350 "all five run-length families INTACT: EndoMul 32×77 exactly Mina's" and :878
# "SHAPE-DIFFED against Mina's own compiled circuit" were a human reading two printed tables. It now
# carries four verdicts, every reference value read off Mina's blob (run-length sets ⊆ Mina's, gadget
# counts ≤ Mina's, the seven-type alphabet, whole Poseidon permutations) and a red path whose bites
# each redden a NAMED verdict.
#
# `curve-gate-oracle.mjs` printed `MATCH Lean` while reading o1js and nothing else — the Lean side was
# a parenthesis in a `console.log`, so it was green for any emitter whatsoever. It now reads our
# EMITTED step circuit as the second source and its `--self-test` bends that source three ways.
#
# ⚠ Both take a `--self-test` that needs NEITHER Lean nor an emission (the shape-diff grades Mina's
# own gate list against itself as the honest anchor), and a full run that needs the emission and
# REFUSES (exit 3) without one — the same two-step shape as the wrap gate above.
# ⚑ AND THE FLOOR ITSELF, before either of them. `emit-provenance.mjs` is what every gate above
# delegates "is this input fresh" to, and its THIRD leg — the emit cone was COMMITTED at the stamped
# HEAD — was recorded and gated on NOWHERE until today. This proves all three legs refuse, that a
# stamp from outside git refuses, and that two honest shapes are still ACCEPTED.
run_one "emit-provenance.mjs --self-test (the freshness floor's own three legs)" \
  node "scripts/emit-provenance.mjs" --self-test
run_one "stepmain-shape-diff.mjs --self-test (4 verdicts must bite, + an honest anchor)" \
  node "scripts/stepmain-shape-diff.mjs" --self-test
run_one "stepmain-shape-diff.mjs (run-length families + gadget census vs Mina's step blob)" \
  node "scripts/stepmain-shape-diff.mjs"
run_one "curve-gate-oracle.mjs --self-test (bend the Lean side: it must be READ)" \
  node "scripts/curve-gate-oracle.mjs" --self-test
run_one "curve-gate-oracle.mjs (VarBaseMul/CompleteAdd coeff-free: o1js AND our emission)" \
  node "scripts/curve-gate-oracle.mjs"

# ⚑ AND THE ONE INSTRUMENT THAT CAN SEE A FREE CELL. Every oracle above is a SHAPE diff. Measured
# 2026-08-03: not one prover-chosen cell was visible to any of them AS SUCH — a statement word with no
# in-circuit source has the same ladder shape as one with a source, and a free booleanity row is
# BYTE-IDENTICAL to a derived one. `KimchiStepProverChoice.lean` / `KimchiWrapProverChoice.lean` compute
# those counts in Lean over the actual emitted program; what Lean's build CANNOT notice is a count going
# UP and then being written into the theorem, which turns the build green again with one more free cell
# in the circuit. This gate is the second source: 21 counts against CEILINGS committed in the script,
# each with a direction. Its `--self-test` raises every `max`/`eq` pin and lowers every `min` pin and
# requires each to bite, renames a census theorem, reshapes a statement — with a CONTROL that the
# committed census must still pass. ~0.4s, node only, no Lean build and no artifact.
run_one "prover-freedom-ratchet.mjs --self-test (a RISE in free cells must red)" \
  node "scripts/prover-freedom-ratchet.mjs" --self-test
run_one "prover-freedom-ratchet.mjs (21 census counts vs their committed ceilings)" \
  node "scripts/prover-freedom-ratchet.mjs"

# The .ts oracles are TRANSPILE-ONLY scripts: the non-migrated ones still carry intentional literal-vs-
# literal falsification controls (e.g. `t2q === LEAN_T2Q_SAMPLE`) that full `tsc` rejects as TS2367 but
# that are exactly the RED path at runtime, so they run under `ts-node --transpile-only --esm` (no type-
# check), NOT `npm run build`. The MIGRATED .ts oracle (branchdata) no longer needs the literal control —
# its red path is the harness `--self-test` — but it still runs under ts-node (it imports the .mjs harness).
TSNODE="$ZK/node_modules/.bin/ts-node"
if [ "$RUN_TS" = 1 ]; then
  if [ ! -x "$TSNODE" ]; then
    echo "   RED: ts-node not found at $TSNODE (run 'cd bridge/mina-zkapp && npm ci'); .ts oracles skipped."
    fails=$((fails + 1))
  else
    for o in "${TS_ORACLES[@]}"; do
      if is_migrated "$o"; then
        run_one "$o" "$TSNODE" --transpile-only --esm "scripts/$o" --self-test
      else
        run_one "$o" "$TSNODE" --transpile-only --esm "scripts/$o"
      fi
    done
  fi
else
  echo "(--no-ts: skipping pickles-r3-branchdata / -statement / -step-statement oracles)"
  echo
fi

# ⚑ THE VK-DERIVATION SEAM. Every oracle above diffs a gate list, a statement or a field value. This
# one is the only step that produces the object a NODE parses: a `Side_loaded_verification_key`
# DERIVED from the Lean-assembled `KimchiWrapMain` gate list, handed to o1js's own OCaml binprot
# reader. `--self-test` proves it can go red (a bent commitment must be REFUSED, and a corrupted o1js
# reference key must turn the crate's unit gates red). It is about the KEY, not about a proof.
run_one "mina-vk-derivation-gate.sh --self-test (Lean gates -> Mina VK -> o1js PARSES it)" \
  bash "$ROOT/scripts/mina-vk-derivation-gate.sh" --self-test

# ⚑ THE PROOF SEAM, the twin of the one above. The VK gate produces the object a node parses; this
# one produces the object a node would VERIFY: a kimchi `ProverProof` proved HERE over the
# Lean-authored `wrap_main` sub-circuit at the 2^15 Tock domain, marshalled to
# `PicklesProofProofsVerified2ReprStableV2`, and handed to `Pickles.proofOfBase64` — Mina's own
# reader — which re-prints it byte-identically. `--self-test` proves it can go red (one record
# field renamed must be REFUSED). ⚠ It PROVES two kimchi circuits, so it costs ~60s.
# ⚠ Parsing is shape, not membership: p-valued fields, off-curve points and a 14-round IPA all
# parse. This step says the object is well-formed Pickles, not that it verifies.
run_one "mina-proof-marshal-gate.sh --self-test (our kimchi proof -> wire -> Mina's reader)" \
  bash "$ROOT/scripts/mina-proof-marshal-gate.sh" --self-test

# The CROSS-IMPLEMENTATION differential — the only step here that is not a diff against a single
# reference value. Green or bust, with its own red path.
if [ "$RUN_XI" = 1 ]; then
  run_one "pickles-crossimpl-differential.sh --self-test (Lean ↔ proof-systems 0.3.0, 15 pairs)" \
    bash "$ROOT/scripts/pickles-crossimpl-differential.sh" --self-test
else
  echo "(--no-xi: skipping the cross-implementation differential)"
  echo
fi

if [ "$fails" -eq 0 ] && [ "$blocked" -eq 0 ]; then
  echo "== ALL GREEN — every Pickles-synthesis byte-diff oracle byte-exact, and the Lean↔Rust cross-implementation differential agrees =="
  exit 0
fi

echo "== $fails ORACLE(S) RED · $blocked BLOCKED =="
[ "${#FAILED[@]}"  -gt 0 ] && printf '   RED      %s\n' "${FAILED[@]}"
[ "${#BLOCKED[@]}" -gt 0 ] && printf '   BLOCKED  %s\n' "${BLOCKED[@]}"
if [ "$blocked" -gt 0 ]; then
  cat <<'EOF'
   ⚑ BLOCKED means the diff DID NOT RUN — a prerequisite this box does not have. It is NOT a pass
     and it is NOT a divergence. The three, and how to tell which:
       * o1-labs circuit blobs   $MINA_CIRCUIT_BLOBS_BASE_DIR, ~/.mina/circuit-blobs, or
                                 /usr/local/lib/mina/circuit-blobs; otherwise fetched (network).
       * a DREGG_WM=wrap TOP-RUNG emission at /tmp/pickles-wrapmain/wrapmain_wrap_<TOP_RUNG>.json:
                                 (cd metatheory && DREGG_WM=wrap lake env lean --run \
                                    Dregg2/Circuit/Emit/EmitWrapMainJson.lean)
                                 ⚠ wrap-scale under the interpreter — hours. A LOWER rung on disk
                                 does not satisfy it; the gate checks the emission's own `name`.
       * ts-node                 (cd bridge/mina-zkapp && npm ci)
     ⚠ THIS IS NOT A SKIP LIST. Nothing here is optional and nothing is suppressed — a blocked run
     still exits 1. It exists so a missing prerequisite is fixed by producing it, and a RED is read
     as a defect, instead of both being read as neither.
EOF
fi
exit 1
