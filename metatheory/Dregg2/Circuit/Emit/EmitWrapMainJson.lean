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
    DREGG_WM=wrap DREGG_WM_OUT=/tmp/mine lake env lean --run …    # a lane's OWN directory

Files land in `$DREGG_WM_OUT/wrapmain_<tag>_<rung>{,_unwired}.json`, default
`/tmp/pickles-wrapmain/`. ⚑ `DREGG_WM_OUT` is the step side's `DREGG_SM_OUT` and exists for the same
reason: two revisions emitted for a byte-diff must not write to one path.

Then:

    cargo run --release --manifest-path metatheory/fixtures/pickles-wrapmain-harness/Cargo.toml \
      -- /tmp/pickles-wrapmain wrap
-/
import Dregg2.Circuit.Emit.KimchiWrapMainCore

open Dregg2.Circuit.Emit.KimchiWrapMain
open Dregg2.Circuit.Emit.KimchiPlacement

/-- Pin a pure `let` in place before an `IO.monoMsNow`, so a phase split cannot report `0 ms` for
the phase that actually ran. -/
def force (n : Nat) (what : String) : IO Nat := do
  IO.println s!"    [{what}] {n}"
  pure n

/-- Write ATOMICALLY: stage beside the target, then rename into place. The step driver's own
`writeAtomic` and its note apply verbatim here — a reader of the emit directory cannot tell a
complete artifact from one whose writer died mid-`String`, because both are a file with the right
name, and `rename(2)` within one directory is the only thing that makes the real name appear
carrying complete bytes. ⚑ This matters most to the byte-diff gate, whose whole job is to compare
these files against another revision's while an emitter may still be running. -/
def writeAtomic (path contents : String) : IO Unit := do
  let staged := path ++ ".partial"
  IO.FS.writeFile staged contents
  IO.FS.rename staged path

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
  -- ⚑ RUNG-LOCAL: `wrapWitnessAt t k` gives rung `k` the environment its OWN rows define. Asking
  -- for the closing rung's here would compute §15's ladders for every rung below `w6_xhat`.
  let wit := wrapWitnessAt t k p rowsW
  let probes := rungProbeRows t k
  let pub := if p == 0 then [] else wrapPublicAt t k
  let jw := renderWrapCircuit s!"wrapmain_{tag}_{k.tag}" p (p + rowsW.length) placed wit pub probes
  let ju := renderWrapCircuit s!"wrapmain_{tag}_{k.tag}_UNWIRED" p (p + rowsU.length) placedU wit
              pub probes
  -- ⚠ A REFUSAL IS LOUD, AND IT LANDS BEFORE THE WRITE. `placeChecked` returning `.error` yields
  -- the empty placement, which would otherwise ship as a zero-gate circuit the harness "proves".
  -- ⚑ Both refusals used to fire AFTER `writeAtomic`, which is not fail-closed at all: the artifact
  -- the refusal is about was already on disk under its real name, and a reader of the emit
  -- directory cannot tell it from a good one.
  if placed.length != p + rowsW.length || placedU.length != p + rowsU.length then
    throw (IO.userError s!"placeChecked REFUSED at {k.tag}: {repr (refusalOf t.sh p gs)}")
  -- ⚑ **THE §17b CAPS' OBLIGATION, DISCHARGED AT EVERY EMISSION.** `baseWh`, `baseFin` and
  -- `baseComb` are stacked on shape-determined CAPS rather than on the regions' actual sizes,
  -- because W-FINALIZE's size is `finStride`/`finSpSize` — computed by RUNNING the program builder,
  -- which no kernel reduction of `combSlot` can afford. A cap is only honest if an emission that
  -- exceeds it STOPS, and this is where. `regionEscape` reads the emitted GATES, so it is an
  -- independent source against the caps' arithmetic, and it checks both ends: a rung reaching DOWN
  -- into the block below is the aliasing the layout exists to refuse.
  match regionEscape t.sh t.sp k gs with
  | some i =>
    throw (IO.userError s!"⚑ REGION CAP ESCAPED at {k.tag}: a gate references external {i}, which \
      is neither below the three blocks ({baseWh t.sh t.sp}) nor inside ANY block {k.tag} declares \
      ({repr (rungRegions t.sh t.sp k)}, as (base, cap) pairs). Two sub-circuits' variable regions \
      would alias — `placeChecked` would see one variable where two were meant and merge two σ \
      classes that were never meant to meet. Refusing rather than emitting it; see §17b.")
  | none => pure ()
  writeAtomic s!"{dir}/wrapmain_{tag}_{k.tag}.json" jw
  writeAtomic s!"{dir}/wrapmain_{tag}_{k.tag}_unwired.json" ju
  let t2 ← IO.monoMsNow
  IO.println s!"  {k.tag}: {rowsW.length} rows, pub {p}, {probes.length} probes  \
    (place {t1 - t0} ms, witness+render {t2 - t1} ms)"
  pure (rowsW.length, probes.length)

/-- An eight-field comma spec:
`prevs,ipaRounds,wComms,tComms,emsRows,branches,pubWords,xhatTerms`.

⚑ **`xhatXY` IS DERIVED HERE, NOT PARSED**, and that is the only honest option: the pair is two
Fq coordinates and a comma spec of naturals has no independent source for them. So a
`DREGG_WM`-supplied shape gets `xhatOut xhatTerms` by construction and `main`'s memo refusal
cannot fire on this path — it is live for the two COMMITTED shapes, which are the shapes anything
actually emits, and where the pair is written down and could disagree.

⚠ Before this, `parseShape` still built the seven-field record and did not compile at all once §15
added `xhatXY`, so the whole emit path was red — the two committed shapes included. -/
def parseShape (spec : String) : Option WrapShape :=
  match (spec.splitOn ",").map String.toNat? with
  | [some a, some b, some c, some d, some e, some f, some g, some h] =>
      some { prevs := a, ipaRounds := b, wComms := c, tComms := d, emsRows := e
           , branches := f, pubWords := g, xhatTerms := h, xhatXY := xhatOut h }
  | _ => none

def main : IO Unit := do
  -- ⚑ **`DREGG_WM_OUT` LETS A LANE OWN ITS OWN DIRECTORY**, exactly as `DREGG_SM_OUT` does on the
  -- step side. This was a HARDCODED path until 2026-08-03, and the omission was not cosmetic: a
  -- before/after byte-diff of the emitted circuit was written as
  --     DREGG_SM=wrap DREGG_SM_OUT=/tmp/emit-before-wrap  lean --run …EmitWrapMainJson.lean
  -- which is wrong TWICE over — this driver reads `DREGG_WM`, not `DREGG_SM`, so the shape selector
  -- was ignored; and it had no output override at all, so BOTH revisions wrote to this one path and
  -- the `diff` compared a directory against itself. ⚠ That is a gate that cannot go red.
  let dir := (← IO.getEnv "DREGG_WM_OUT").getD "/tmp/pickles-wrapmain"
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
  -- ⚑ A shape whose x_hat MSM has no `Add_with_correction` entry has no correction reduce and no
  -- `~init`, so the fold would start from a variable nothing defines. Refuse rather than emit it.
  if (xhLadders s).isEmpty then
    throw (IO.userError s!"degenerate shape: xhatTerms {s.xhatTerms} selects no ladder entry")
  if s.xhatTerms > XHAT_TERMS_FULL then
    throw (IO.userError s!"xhatTerms {s.xhatTerms} exceeds wrap_verifier's own entry count \
      {XHAT_TERMS_FULL}")
  -- ⚑ **THE MEMO'S OBLIGATION, DISCHARGED AT EVERY EMISSION.** `WrapShape.xhatXY` carries the pair
  -- `wrap_verifier.ml:617` absorbs so that a dozen kernel theorems do not each re-reduce the MSM.
  -- That is only sound if the pair IS the MSM's output, and this is where any shape — committed or
  -- `DREGG_WM`-supplied — is refused when it is not. The smoke shape's copy is additionally closed
  -- by `rfl` in the kernel (`xhat_smoke_shape_absorbs_the_msm_output`); this covers the wrap shape,
  -- which is 1805 five-bit chunks and out of the kernel's reach without `native_decide`.
  if s.xhatXY != xhatOut s.xhatTerms then
    throw (IO.userError s!"⚑ xhatXY IS NOT THE MSM'S OUTPUT: shape carries {s.xhatXY} but \
      `xhatOut {s.xhatTerms}` is {xhatOut s.xhatTerms}. The transcript would absorb a value no row \
      computes — refusing rather than emitting it.")
  -- ⚑ **THE §15c‴ MEMO'S OBLIGATION, DISCHARGED AT EVERY EMISSION.** `FIN_DEFERRED_CIP/_B/_XI`
  -- are the three deferred words the finalizing block carries, and `xhatScalar` reads them, so a
  -- wrong triple would put a scalar into the x_hat MSM that no row of W-FINSPONGE computes and make
  -- `Boolean.Assert.any [finalized; not should_finalize]` unsatisfiable in the rung that emits it.
  -- ⚑ `fin_deferred_words_are_the_derivation` (`…Pins12`) closes this at the SMOKE shape by
  -- `native_decide`; ⚠ it is not, and was never, a kernel `rfl` at both shapes, whatever this
  -- comment said until 2026-08-05 — for a day the theorem it cited did not exist at all and THIS
  -- refusal was the only discharge there was. It still is the only one at the WRAP shape and at any
  -- `DREGG_WM`-supplied one, which is why it is here and not a comment, and it costs one evaluation
  -- of a program the emission runs anyway.
  let fd := finSpDerivedWords (mkWrap s)
  if (FIN_DEFERRED_CIP, FIN_DEFERRED_B, FIN_DEFERRED_XI) != fd then
    throw (IO.userError s!"⚑ FIN_DEFERRED_* IS NOT THE DERIVATION: the memo carries \
      {(FIN_DEFERRED_CIP, FIN_DEFERRED_B, FIN_DEFERRED_XI)} but `finSpDerivedWords` says {fd}. \
      W-FINSPONGE would emit a `Boolean.all` no witness satisfies — refusing rather than emitting \
      it. Re-run `lake env lean --run Dregg2/Circuit/Emit/EmitWrapFinDeferred.lean`.")
  IO.println s!"emitting wrap_main tag={tag} shape={repr s}"
  IO.println s!"  items={nItems s} squeezes={nSqueezes s} chals={nChals s} \
    PRIMARY_LEN(mina)={WRAP_PRIMARY_LEN} pubWords(here)={s.pubWords}"
  IO.println s!"  x_hat MSM: {xhN s} entries, {xhTotalChunks s} five-bit chunks, \
    {(xhLadders s).length} ladders, widths={(xhSel s).map xhatBits}"
  IO.println s!"  x_hat (DERIVED, absorbed at wrap_verifier.ml:617) = {xhatOut s.xhatTerms}"
  let t := mkWrap s
  let _ ← force t.sp.evs.length "sponge events"
  for k in [Rung.transcript, Rung.challenges, Rung.branch, Rung.bind, Rung.key, Rung.xhat,
           Rung.split, Rung.ftcomm, Rung.prev, Rung.wraphack, Rung.close, Rung.finalize,
           Rung.finsponge, Rung.combine, Rung.bullet] do
    let _ ← emitRung dir tag t k
    pure ()
  IO.println s!"wrote {dir}/wrapmain_{tag}_*.json"
