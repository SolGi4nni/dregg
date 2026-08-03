/-
# Dregg2.Circuit.Emit.EmitStepMainJson — the `--run` emit driver for the `verify_one` assembly

Thin executable: writes each RUNG of the Lean-assembled `step_verifier.verify_one` circuit — and its
UNWIRED control — to `/tmp/pickles-stepmain/*.json`, which `pickles-stepmain-harness` proves +
verifies. Carries the `main` (kept OUT of `KimchiStepMain` so that module roots cleanly into
`PicklesSynthesis`).

    lake env lean --run Dregg2/Circuit/Emit/EmitStepMainJson.lean              # the committed shape
    DREGG_SM=smoke  lake env lean --run …                                      # the CI fixture shape
    DREGG_SM=A,C,E,M,I,B,D,V,P,W lake env lean --run …                         # an arbitrary rung

The ten-field spec is `absorbs,chals,emsRows,msmTerms,ipaRounds,ipaBlocks,bRounds,cipEvals,tComms,
pubWords`. ⚑ `msmChunks` is GONE (2026-08-03): the MSM chunk count is per statement WORD
(`msmChunksAt`, §1b), so there is nothing shape-wide left to pass. ⚑ `tComms` is new since the R1 interleaving: `absorbs` is DERIVED from the
transcript schedule now (`absorbBlocksOf`), so sizing `t_comm` off `absorbs` would be circular.
The shape comes through the ENVIRONMENT, not `argv`: `lean --run` does not forward
trailing arguments through `lake env`, and a silently-ignored argument emitting the DEFAULT shape
under a scale-rung filename is exactly the measurement that lies.

Each rung reports its wall-clock split — chain evaluation, row scheduling, placement (`place`),
witness composition (`WitnessBuilder.compose`), render+write — because that split, not the prover,
is what governs whether the assembly reaches full `verify_one` scale.

House Law #1: the CIRCUIT is Lean-authored; `proof-systems` (the harness) is the Rust PROVER.

⚑ IMPORTS `…KimchiStepMainCore`, NOT THE UMBRELLA (2026-08-02, with the split). Every name this
driver uses — `mkStep`, `rungRows`, `stepGates`, `placedOf`, `stepWitness`, `rungProbeRows`,
`stepPublic`, `renderStepCircuit`, `Rung`, `shapeStep`/`shapeSmoke` — is §1–§11, i.e. Core, which
elaborates in ~11 s. The umbrella additionally pulls the thirteen PIN modules (837 `#guard`s,
~15 min of interpretation), and EMITTING a circuit does not depend on any of them. So the emit →
prove loop no longer waits on the pins. ⚠ This does NOT unroot a guard: `Dregg2.PicklesSynthesis`
(a `defaultTargets` root) imports the umbrella, so every pin module still runs in `lake build`.
-/
import Dregg2.Circuit.Emit.KimchiStepMainCore

open Dregg2.Circuit.Emit.KimchiStepMain
open Dregg2.Circuit.Emit.KimchiPlacement (PGate PlacedGate)

/-- Force a `Nat` before the next clock read. `let x := e` for pure `e` is FLOATABLE — the compiler
happily sinks the work past an `IO.monoMsNow`, which is how a phase split silently reports `0 ms`
for the phase that actually ran. An `IO` action that inspects the value pins it in place. -/
def force (n : Nat) (what : String) : IO Nat := do
  if n == 0 then throw (IO.userError s!"emit: phase '{what}' produced nothing — degenerate shape")
  pure n

/-- Emit one rung (wired + unwired), with the phase split. Returns `(rows, probes)`. -/
def emitRung (dir tag : String) (t : StepData) (k : Rung) : IO (Nat × Nat) := do
  let s := t.sh
  let p := rungPub s k
  let t0 ← IO.monoMsNow
  let rows := rungRows t k true
  let rowsU := rungRows t k false
  let n := rows.length
  let _ ← force (n + rowsU.length) "rows"
  let t1 ← IO.monoMsNow
  let placed := placedOf p (stepGates rows)
  let placedU := placedOf p (stepGates rowsU)
  let nw ← force ((placed.map (fun g => g.wires.length)).foldl (· + ·) 0
                  + (placedU.map (fun g => g.wires.length)).foldl (· + ·) 0) "place"
  let t2 ← IO.monoMsNow
  let w := stepWitness t p rows
  let ncell ← force ((w.map (·.length)).foldl (· + ·) 0) "compose"
  let t3 ← IO.monoMsNow
  let probes := rungProbeRows t k
  let pub := if p == 0 then [] else stepPublic t
  let js := renderStepCircuit s!"stepmain_{tag}_{k.tag}" p (p + n) placed w pub probes
  let jsU := renderStepCircuit s!"stepmain_{tag}_{k.tag}_UNWIRED" p (p + n) placedU w pub probes
  IO.FS.writeFile s!"{dir}/stepmain_{tag}_{k.tag}.json" js
  IO.FS.writeFile s!"{dir}/stepmain_{tag}_{k.tag}_unwired.json" jsU
  let t4 ← IO.monoMsNow
  -- A refusal must be LOUD: `placedOf` returns `[]` on refusal, and an empty gate list would
  -- otherwise be written out as a "circuit" the harness rejects for the wrong reason.
  if placed.length != p + n then
    throw (IO.userError s!"{k.tag}: placeChecked REFUSED — {repr (refusalOf p (stepGates rows))}")
  IO.println s!"[{tag}/{k.tag}] rows={p + n} (pub={p}) probes={probes.length} \
cells={ncell} wires={nw}"
  IO.println s!"    rows {t1 - t0} ms | place {t2 - t1} ms | compose {t3 - t2} ms | \
render+write {t4 - t3} ms | TOTAL {t4 - t0} ms"
  pure (p + n, probes.length)

def parseShape (spec : String) : Option StepShape :=
  match spec.splitOn "," with
  | [a, c, e, m, i, b, d, ce, tc, pw] =>
      some { absorbs := a.toNat!, chals := c.toNat!, emsRows := e.toNat!
           , msmTerms := m.toNat!
           , ipaRounds := i.toNat!, ipaBlocks := b.toNat!
           , bRounds := d.toNat!, cipEvals := ce.toNat!, tComms := tc.toNat!
           , pubWords := pw.toNat! }
  | _ => none

def main : IO Unit := do
  let dir := "/tmp/pickles-stepmain"
  IO.FS.createDirAll dir
  let spec ← IO.getEnv "DREGG_SM"
  let (tag, sh) :=
    match spec with
    | none => ("step", shapeStep)
    | some "smoke" => ("smoke", shapeSmoke)
    | some "step" => ("step", shapeStep)
    | some str => match parseShape str with
                  | some s => (str.replace "," "_", s)
                  | none => ("step", shapeStep)
  -- ⚑ FAIL CLOSED on a shape too small for `Common.ft_comm`. `tCommN` is `min 7 tComms`, and the
  -- Horner needs at least two chunks (`common.ml:247-253` seeds at `t_comm.(n-1)` and folds down);
  -- at `tCommN < 2` the add chain would index past its own list and emit a `(0,0)` "point".
  -- The two committed shapes are 7 and 3; an arbitrary `DREGG_SM` spec must not silently degrade.
  if tCommN sh < 2 then
    throw (IO.userError s!"emit: tCommN = {tCommN sh} — the shape carries fewer than two `t_comm` \
quotient chunks (tComms={sh.tComms}); `Common.ft_comm`'s Horner needs at least two")
  -- ⚑ FAIL CLOSED on a shape whose `absorbs` is not the SCHEDULE's own block count, and on one with
  -- too few `chals` to hold upstream's scheduled squeezes. Both are silent-degradation doors: the
  -- first would leave absorb blocks the sponge never feeds, the second would drop a squeeze.
  if sh.absorbs != absorbBlocksOf sh then
    throw (IO.userError s!"emit: absorbs={sh.absorbs} but the transcript schedule has \
{absorbBlocksOf sh} absorb blocks (§2b)")
  if sh.chals < sqScheduled sh then
    throw (IO.userError s!"emit: chals={sh.chals} < {sqScheduled sh} scheduled transcript \
squeezes (β γ α ζ u, one per bullet_reduce round, c)")
  IO.println s!"== step_main assembly: absorbs={sh.absorbs} chals={sh.chals} ems={sh.emsRows} \
msm={sh.msmTerms} terms / {msmChunkPrefix sh.msmTerms} chunks ipa={sh.ipaRounds}x{sh.ipaBlocks} \
b={sh.bRounds} pub={sh.pubWords} =="
  let tc0 ← IO.monoMsNow
  let t := mkStep sh
  -- ⚑ `t.ftc.terms` is in the force since `Common.ft_comm`'s MSM landed: it is eight 255-bit
  -- `scale_fast2` ladders and by far the largest single item in the chain phase, so leaving it out
  -- would report its cost under "rows".
  let _ ← force (t.sp.states.length + t.msm.terms.length + t.ipa.accs.length
                 + t.ft.fp.prog.size + t.segB.states.length + t.ftc.terms.length) "chains"
  let tc1 ← IO.monoMsNow
  IO.println s!"    chain evaluation (sponge + vbm + endo + deferred): {tc1 - tc0} ms"
  for k in [Rung.transcript, Rung.challenges, Rung.msm, Rung.ipa, Rung.full,
            Rung.ftEval0, Rung.absorb, Rung.finalize, Rung.opening] do
    let _ ← emitRung dir tag t k
    pure ()
