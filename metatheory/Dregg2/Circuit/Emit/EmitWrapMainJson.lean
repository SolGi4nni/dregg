/-
# EmitWrapMainJson — write the Lean-assembled `wrap_main` rungs as prover-ready JSON.

Clone of `EmitStepMainJson` for the WRAP side. Everything it writes is over **Fq** and is proved by
`metatheory/fixtures/pickles-wrapmain-harness` on **Pallas**, not Vesta.

⚠ THE SHAPE COMES THROUGH `DREGG_WM` IN THE ENVIRONMENT, NOT `argv`. `lean --run` does not forward
trailing args through `lake env`, and a silently-ignored argument that emits the default shape under
a scale-rung filename is exactly the measurement that lies.

    cd metatheory
    lake build Dregg2.Circuit.Emit.KimchiWrapMain
    DREGG_WM=wrap  lake env lean --run Dregg2/Circuit/Emit/EmitWrapMainJson.lean
    DREGG_WM=smoke lake env lean --run Dregg2/Circuit/Emit/EmitWrapMainJson.lean

Files land in `/tmp/pickles-wrapmain/wrapmain_<tag>_<rung>{,_unwired}.json`.

Then:

    cargo run --release --manifest-path metatheory/fixtures/pickles-wrapmain-harness/Cargo.toml \
      -- /tmp/pickles-wrapmain wrap
-/
import Dregg2.Circuit.Emit.KimchiWrapMain

open Dregg2.Circuit.Emit.KimchiWrapMain
open Dregg2.Circuit.Emit.KimchiPlacement

/-- Pin a pure `let` in place before an `IO.monoMsNow`, so a phase split cannot report `0 ms` for
the phase that actually ran. -/
def force (n : Nat) (what : String) : IO Nat := do
  IO.println s!"    [{what}] {n}"
  pure n

def emitRung (dir tag : String) (t : WrapData) (k : Rung) : IO (Nat × Nat) := do
  let t0 ← IO.monoMsNow
  let rowsW := rungRows t k true
  let rowsU := rungRows t k false
  let p := rungPub t.sh k
  let _ ← force rowsW.length s!"{k.tag} rows"
  let gs := wrapGates rowsW
  let gu := wrapGates rowsU
  let placed := placedOf t.sh p gs
  let placedU := placedOf t.sh p gu
  let t1 ← IO.monoMsNow
  -- ⚑ ONE witness, used for BOTH circuits. That is what makes the UNWIRED emission a CONTROL: the
  -- rows, the gate types, the coefficients and every witness cell are byte-identical, and the ONLY
  -- difference is the copy-permutation. Computing a second witness from the unwired rows would
  -- leave the probe cells empty there and the "control" would be a different circuit.
  let wit := wrapWitness t p rowsW
  let probes := rungProbeRows t k
  let pub := if p == 0 then [] else wrapPublic t
  let jw := renderWrapCircuit s!"wrapmain_{tag}_{k.tag}" p (p + rowsW.length) placed wit pub probes
  let ju := renderWrapCircuit s!"wrapmain_{tag}_{k.tag}_UNWIRED" p (p + rowsU.length) placedU wit
              pub probes
  IO.FS.writeFile s!"{dir}/wrapmain_{tag}_{k.tag}.json" jw
  IO.FS.writeFile s!"{dir}/wrapmain_{tag}_{k.tag}_unwired.json" ju
  let t2 ← IO.monoMsNow
  -- ⚠ A REFUSAL IS LOUD. `placeChecked` returning `.error` yields the empty placement, which would
  -- otherwise ship as a zero-gate circuit the harness "proves".
  if placed.length != p + rowsW.length || placedU.length != p + rowsU.length then
    throw (IO.userError s!"placeChecked REFUSED at {k.tag}: {repr (refusalOf t.sh p gs)}")
  IO.println s!"  {k.tag}: {rowsW.length} rows, pub {p}, {probes.length} probes  \
    (place {t1 - t0} ms, witness+render {t2 - t1} ms)"
  pure (rowsW.length, probes.length)

/-- A seven-field comma spec: `prevs,ipaRounds,wComms,tComms,emsRows,branches,pubWords`. -/
def parseShape (spec : String) : Option WrapShape :=
  match (spec.splitOn ",").map String.toNat? with
  | [some a, some b, some c, some d, some e, some f, some g] =>
      some { prevs := a, ipaRounds := b, wComms := c, tComms := d, emsRows := e
           , branches := f, pubWords := g }
  | _ => none

def main : IO Unit := do
  let dir := "/tmp/pickles-wrapmain"
  IO.FS.createDirAll dir
  let sm ← IO.getEnv "DREGG_WM"
  let (tag, s) : String × WrapShape :=
    match sm with
    | none => ("wrap", shapeWrap)
    | some "wrap" => ("wrap", shapeWrap)
    | some "smoke" => ("smoke", shapeSmoke)
    | some spec =>
      match parseShape spec with
      | some sh => ("custom", sh)
      | none => ("wrap", shapeWrap)
  -- ⚑ FAIL-CLOSED SHAPE GUARDS. A shape whose schedule cannot carry its own census would emit a
  -- circuit that is not the one the header describes.
  if s.pubWords > WRAP_PRIMARY_LEN then
    throw (IO.userError s!"pubWords {s.pubWords} exceeds Mina's own PRIMARY_LEN {WRAP_PRIMARY_LEN}")
  if s.emsRows == 0 || s.branches == 0 then
    throw (IO.userError "degenerate shape: emsRows/branches must be positive")
  IO.println s!"emitting wrap_main tag={tag} shape={repr s}"
  IO.println s!"  items={nItems s} squeezes={nSqueezes s} chals={nChals s} \
    PRIMARY_LEN(mina)={WRAP_PRIMARY_LEN} pubWords(here)={s.pubWords}"
  let t := mkWrap s
  let _ ← force t.sp.evs.length "sponge events"
  for k in [Rung.transcript, Rung.challenges, Rung.branch, Rung.bind] do
    let _ ← emitRung dir tag t k
    pure ()
  IO.println s!"wrote {dir}/wrapmain_{tag}_*.json"
