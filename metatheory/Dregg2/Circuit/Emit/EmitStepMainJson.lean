/-
# Dregg2.Circuit.Emit.EmitStepMainJson — the `--run` emit driver for the `verify_one` assembly

Thin executable: writes each RUNG of the Lean-assembled `step_verifier.verify_one` circuit — and its
UNWIRED control — to `/tmp/pickles-stepmain/*.json`, which `pickles-stepmain-harness` proves +
verifies. Carries the `main` (kept OUT of `KimchiStepMain` so that module roots cleanly into
`PicklesSynthesis`).

    lake env lean --run Dregg2/Circuit/Emit/EmitStepMainJson.lean              # the committed shape
    DREGG_SM=smoke  lake env lean --run …                                      # the CI fixture shape
    DREGG_SM=A,C,E,M,K,I,B,D,V,P lake env lean --run …                         # an arbitrary rung

The ten-field spec is `absorbs,chals,emsRows,msmTerms,msmChunks,ipaRounds,ipaBlocks,bRounds,cipEvals,
pubWords`. The shape comes through the ENVIRONMENT, not `argv`: `lean --run` does not forward
trailing arguments through `lake env`, and a silently-ignored argument emitting the DEFAULT shape
under a scale-rung filename is exactly the measurement that lies.

Each rung reports its wall-clock split — chain evaluation, row scheduling, placement (`place`),
witness composition (`WitnessBuilder.compose`), render+write — because that split, not the prover,
is what governs whether the assembly reaches full `verify_one` scale.

House Law #1: the CIRCUIT is Lean-authored; `proof-systems` (the harness) is the Rust PROVER.
-/
import Dregg2.Circuit.Emit.KimchiStepMain

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
  | [a, c, e, m, k, i, b, d, ce, pw] =>
      some { absorbs := a.toNat!, chals := c.toNat!, emsRows := e.toNat!
           , msmTerms := m.toNat!, msmChunks := k.toNat!
           , ipaRounds := i.toNat!, ipaBlocks := b.toNat!
           , bRounds := d.toNat!, cipEvals := ce.toNat!, pubWords := pw.toNat! }
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
  -- ⚑ FAIL CLOSED on a shape too small for `Common.ft_comm`. `tCommN` is `min 7 (free blocks)`, and
  -- the Horner needs at least two chunks (`common.ml:247-253` seeds at `t_comm.(n-1)` and folds
  -- down); at `tCommN < 2` the add chain would index past its own list and emit a `(0,0)` "point".
  -- The two committed shapes are 7 and 3; an arbitrary `DREGG_SM` spec must not silently degrade.
  if tCommN sh < 2 then
    throw (IO.userError s!"emit: tCommN = {tCommN sh} — the shape has fewer than two FREE \
transcript blocks for `t_comm` (absorbs={sh.absorbs}, absorbed rounds={(absRoundList sh).length}); \
`Common.ft_comm`'s Horner needs at least two quotient chunks")
  IO.println s!"== step_main assembly: absorbs={sh.absorbs} chals={sh.chals} ems={sh.emsRows} \
msm={sh.msmTerms}x{sh.msmChunks} ipa={sh.ipaRounds}x{sh.ipaBlocks} b={sh.bRounds} \
pub={sh.pubWords} =="
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
            Rung.ftEval0, Rung.absorb, Rung.finalize] do
    let _ ← emitRung dir tag t k
    pure ()
