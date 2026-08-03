/-
# Dregg2.Circuit.Emit.EmitStepMainJson — the `--run` emit driver for the `verify_one` assembly

Thin executable: writes each RUNG of the Lean-assembled `step_verifier.verify_one` circuit — and its
UNWIRED control — to `/tmp/pickles-stepmain/*.json`, which `pickles-stepmain-harness` proves +
verifies. Carries the `main` (kept OUT of `KimchiStepMain` so that module roots cleanly into
`PicklesSynthesis`).

    lake env lean --run Dregg2/Circuit/Emit/EmitStepMainJson.lean              # the committed shape
    DREGG_SM=smoke  lake env lean --run …                                      # the CI fixture shape
    DREGG_SM=A,C,E,M,I,B,D,V,P,W lake env lean --run …                         # an arbitrary shape
    DREGG_SM_RUNGS=r8_finalize lake env lean --run …                           # ONE rung
    DREGG_SM_RUNGS=all lake env lean --run …                                   # the nine (default)

⚑ **`DREGG_SM_RUNGS` is why a conformance re-grade is minutes and not a working day** (2026-08-03).
`rungRows` binds all nine sub-lists BEFORE it matches on `k`, so every rung evaluates the whole
chain; `emitRung` then walks it twice more (wired, unwired). Nine rungs therefore cost 9 × 2 full
traversals, and the three gates that consume this driver
(`stepmain-shape-diff`, `curve-gate-oracle`, `stepmain-region-conformance`) grade `r8_finalize`
ALONE. Measured on the `step` shape from artifact mtimes: consecutive rungs land 68–69 min apart and
the gap does not grow with the rung — the uniformity IS the evidence that the work is shared and
re-done. The full set stays the default because §15's row-length pins want every rung.

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

/-- Write ATOMICALLY: stage beside the target, then rename into place.

⚑ A reader of `/tmp/pickles-stepmain` cannot tell a fully-written artifact from one whose writer
died mid-`String` — both are a file with the right name. `rename(2)` within one directory is atomic,
so the real name only ever appears carrying complete bytes. Measured 2026-08-03: the directory held
a nine-rung `smoke` set beside a four-rung `step` set with no stamp and no way to tell which run
either came from. -/
def writeAtomic (path contents : String) : IO Unit := do
  let staged := path ++ ".partial"
  IO.FS.writeFile staged contents
  IO.FS.rename staged path

/-- The nine rungs in schedule order. ⚑ This is the FULL-SET path and it stays the DEFAULT: §15's
row-length pins and the shape-diff sweeps legitimately want every rung. -/
def allRungs : List Rung :=
  [Rung.transcript, Rung.challenges, Rung.msm, Rung.ipa, Rung.full,
   Rung.ftEval0, Rung.absorb, Rung.finalize, Rung.opening]

/-- A selector name matches a rung by its full tag (`r8_finalize`) or its index alone (`r8`). -/
def rungMatches (n : String) (k : Rung) : Bool :=
  k.tag == n || (k.tag.splitOn "_").headD "" == n

/-- Resolve a `DREGG_SM_RUNGS` selector. ⚑ FAILS CLOSED on a name that is not a rung: a selector
silently falling back to all nine is the same lie the shape docblock above names — the run would
cost ten hours while reporting that it honoured a one-rung request. -/
def parseRungs (spec : String) : Except String (List Rung) := do
  let names := ((spec.splitOn ",").map String.trim).filter (· != "")
  if names.isEmpty then throw s!"DREGG_SM_RUNGS={spec} names no rung"
  names.foldlM (fun acc n =>
    match allRungs.find? (rungMatches n) with
    | some k => pure (acc ++ [k])
    | none => throw s!"DREGG_SM_RUNGS: '{n}' is not a rung — expected one of \
{String.intercalate ", " (allRungs.map Rung.tag)} (or its 'rN' prefix)") []

/-- Emit one rung (wired + unwired), with the phase split. Returns `(rows, probes)`. -/
def emitRung (dir tag : String) (t : StepData) (k : Rung) (wiredOnly : Bool := false) :
    IO (Nat × Nat) := do
  let s := t.sh
  let p := rungPub s k
  let t0 ← IO.monoMsNow
  let rows := rungRows t k true
  -- ⚑ The UNWIRED control is a SECOND full `rungRows` traversal plus a second `placedOf`, i.e.
  -- roughly half this rung's cost. It is the tamper control the `pickles-stepmain-harness` proves
  -- against — and NONE of the three conformance gates reads it: `stepmain-shape-diff`,
  -- `curve-gate-oracle` and `stepmain-region-conformance` all load `stepmain_step_r8_finalize.json`
  -- and never open `_unwired.json`. So a grade pays for it and throws it away.
  -- ⚠ Default stays FALSE. The control is what makes "the tamper is REJECTED here and ACCEPTED on
  -- the unwired twin" a real claim, and a flag that quietly stopped emitting it would hollow out
  -- the harness's whole falsification story. Opt in when you are grading, not when you are proving.
  let rowsU := if wiredOnly then [] else rungRows t k false
  let n := rows.length
  let _ ← force (n + rowsU.length + (if wiredOnly then 1 else 0)) "rows"
  let t1 ← IO.monoMsNow
  let placed := placedOf p (stepGates rows)
  let placedU := if wiredOnly then [] else placedOf p (stepGates rowsU)
  let nw ← force ((placed.map (fun g => g.wires.length)).foldl (· + ·) 0
                  + (placedU.map (fun g => g.wires.length)).foldl (· + ·) 0) "place"
  let t2 ← IO.monoMsNow
  let w := stepWitness t p rows
  let ncell ← force ((w.map (·.length)).foldl (· + ·) 0) "compose"
  let t3 ← IO.monoMsNow
  -- ⚑ NOT `rungProbeRows t k`. That recomputes `rungRows t k true` from scratch, and `rungRows`
  -- evaluates ALL NINE sub-lists on every call before it matches on `k` — so the convenience
  -- wrapper costs a THIRD full chain traversal per rung on top of the wired/unwired pair. This is
  -- `rungProbeRows`' body verbatim over the `rows` already in hand (same `p`, same list).
  let probes := ((rows.zip (List.range rows.length)).filter (fun ri => ri.1.probe)).map
                  (fun ri => p + ri.2)
  let pub := if p == 0 then [] else stepPublic t
  let js := renderStepCircuit s!"stepmain_{tag}_{k.tag}" p (p + n) placed w pub probes
  writeAtomic s!"{dir}/stepmain_{tag}_{k.tag}.json" js
  unless wiredOnly do
    let jsU := renderStepCircuit s!"stepmain_{tag}_{k.tag}_UNWIRED" p (p + n) placedU w pub probes
    writeAtomic s!"{dir}/stepmain_{tag}_{k.tag}_unwired.json" jsU
  -- ⚠ And REMOVE a stale control rather than leave one from an older run beside a fresh wired
  -- artifact. A `_unwired.json` that no longer corresponds to the `.json` next to it is exactly the
  -- mixed-run directory this pass is closing.
  if wiredOnly then
    let up := s!"{dir}/stepmain_{tag}_{k.tag}_unwired.json"
    if ← System.FilePath.pathExists up then IO.FS.removeFile up
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
  -- ⚑ SETTABLE OUTPUT DIR — the shared `/tmp/pickles-stepmain` made concurrent lanes collide BY
  -- CONSTRUCTION. Two lanes emitting the `step` shape write byte-different `stepmain_step_r8_*.json`
  -- to the same path, and whichever finishes last silently wins; the loser's stamp then vouches for
  -- bytes that are no longer there. Measured 2026-08-03 on hbox: that directory held r5–r9 from a
  -- run at 11:58–12:00 beside r1–r4 from a *different* run at 13:06–16:19, and nothing in the
  -- directory recorded that they came from two runs. `DREGG_SM_OUT` lets a lane own its own dir.
  let dir := (← IO.getEnv "DREGG_SM_OUT").getD "/tmp/pickles-stepmain"
  IO.FS.createDirAll dir
  let spec ← IO.getEnv "DREGG_SM"
  let (tag, sh) :=
    match spec with
    | none => ("step", shapeStep)
    | some "smoke" => ("smoke", shapeSmoke)
    | some "step" => ("step", shapeStep)
    | some str => match parseShape str with
                  | some s => (str.replace "," "_", s)
                  -- ⚑ FAIL CLOSED. Falling back to `shapeStep` here would emit the DEFAULT shape
                  -- under a filename nobody asked for, which is the measurement that lies.
                  | none => panic! s!"emit: DREGG_SM={str} is neither 'step', 'smoke', nor a \
ten-field spec 'absorbs,chals,emsRows,msmTerms,ipaRounds,ipaBlocks,bRounds,cipEvals,tComms,pubWords'"
  -- ⚑ THE RUNG SELECTOR. Default = all nine, unchanged. `DREGG_SM_RUNGS=r8_finalize` emits ONLY
  -- what the caller asked for. Measured 2026-08-03 on the `step` shape: consecutive rung artifacts
  -- land 68–69 min apart, and the gap does NOT grow with the rung — because `rungRows` evaluates
  -- all nine sub-lists before it matches on `k`, so EVERY rung pays the whole chain. The three
  -- conformance gates grade `r8_finalize` alone and were waiting on all nine.
  -- ⚑ `DREGG_SM_WIRED_ONLY=1` drops the unwired control — see `emitRung`. Roughly halves a rung.
  let wiredOnly := ((← IO.getEnv "DREGG_SM_WIRED_ONLY").getD "0") != "0"
  let rungs ← match ← IO.getEnv "DREGG_SM_RUNGS" with
    | none | some "all" => pure allRungs
    | some sel => match parseRungs sel with
                  | .ok ks => pure ks
                  | .error e => throw (IO.userError s!"emit: {e}")
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
  for k in rungs do
    let _ ← emitRung dir tag t k wiredOnly
    pure ()
