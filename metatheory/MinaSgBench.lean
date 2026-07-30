/-
# MinaSgBench — **the NATIVE-COMPILED cost of one Mina checkpoint's `⟨s, srs.g⟩` leg.**

`Dregg2.Bridge.MinaWrapSgWeld` pins the answer under `#guard`, which runs Lean's **interpreter**
(this package sets no `precompileModules`), so its wall time is an upper bound rather than the
compiled cost. This executable runs the IDENTICAL function — `PastaIpaFold.msmHornerM` at
`(p, b3 = 15, 255)` over the same 32,768 real generators and the same wire-derived scalars —
through `leanc`, and prints the number the cadence table in `docs/MINA-CHECKPOINT-CADENCE.md`
needs.

It is self-checking in **both polarities**: it fails non-zero if the fold does not reproduce block
539508's own `opening.sg`, and it fails non-zero if a tampered generator list still does. A
benchmark that only measured would be a benchmark of an unknown function.

Build/run:  `lake build mina_sg_bench && ./.lake/build/bin/mina_sg_bench`
(or `scripts/run-mina-sg-compiled.sh`, which also times the weld).

⚠ This measures the CHECK, not the PROOF of the check. `MinaObserver::prove_opening_check` is a
separate and much larger number (`docs/MINA-CHECKPOINT-CADENCE.md` §5b); do not conflate them.
-/
import Dregg2.Bridge.MinaWrapSgWeld

open Dregg2.Bridge.MinaWrapSg (sVecN sgFold sgWireOk sgVerdict sgFoldAdds)
open Dregg2.Bridge.MinaWrapSgWeld (CHALS_W)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaCurveComplete (curveB3 Oproj projEqM)
open Dregg2.Circuit.Emit.PastaIpaFold (msmHornerM)
open Dregg2.Circuit.Emit.MinaWrapSrsG (SRS_G)
open Dregg2.Circuit.Emit.MinaWrapSgParts (SG)

/-- Render a millisecond count as seconds, one decimal. -/
def secs (ms : Nat) : String := s!"{ms / 1000}.{(ms % 1000) / 100} s"

def main : IO Unit := do
  let gens := SRS_G
  let ng := gens.length
  IO.println s!"mina_sg_bench — devnet block 539508, wrap SRS k = 15"
  IO.println s!"  generators      : {ng}"
  IO.println s!"  challenges      : {CHALS_W.length} (derived from wire by MinaWrapChallenges)"

  -- The scalars, from the 15 challenges. This is the compression the deferral rests on.
  let t0 ← IO.monoMsNow
  let scalars := sVecN qN CHALS_W
  let ns := scalars.length
  let t1 ← IO.monoMsNow
  IO.println s!"  s-vector        : {ns} scalars in {t1 - t0} ms"

  -- The shape gate, which includes the 32,768-point on-curve scan.
  let t2 ← IO.monoMsNow
  let shape := sgWireOk CHALS_W gens SG
  let t3 ← IO.monoMsNow
  IO.println s!"  shape gate      : {shape} in {t3 - t2} ms  (2^15 on-curve + non-degeneracy)"

  -- ⚑ THE MEASUREMENT: one 2^15-point Pallas MSM by the shared doubling chain.
  let t4 ← IO.monoMsNow
  let out := msmHornerM pN curveB3 255 scalars gens
  let ok := projEqM pN out SG
  let t5 ← IO.monoMsNow
  let msmMs := t5 - t4
  IO.println s!"  MSM <s, srs.g>  : {secs msmMs} ({msmMs} ms) for {sgFoldAdds 15 255} complete adds"
  IO.println s!"  verdict         : sg == <s, srs.g>  ->  {ok}"

  -- ⚑ THE OTHER POLARITY: one generator swapped for another REAL generator. Shape stays valid,
  -- so this is a genuine disagreement rather than a refusal.
  let t6 ← IO.monoMsNow
  let bad := projEqM pN
    (msmHornerM pN curveB3 255 scalars (gens.set 12345 (gens.getD 12346 Oproj))) SG
  let t7 ← IO.monoMsNow
  IO.println s!"  tamper          : one generator swapped -> {bad} (must be false), {secs (t7 - t6)}"

  -- What a checkpoint costs, at this measured rate. Legs 5g + 5h are three 2^15 MSMs.
  IO.println s!"  ---"
  IO.println s!"  checkpoint sg leg (5h)      : {secs msmMs}"
  IO.println s!"  + 2 accumulator MSMs (5g)   : {secs (3 * msmMs)} total for the three"
  IO.println s!"  everything else is ~110 ms (sponges, opening relation, public_comm)"

  if !ok then
    throw (IO.userError "FAIL: the compiled MSM did NOT reproduce block 539508's opening.sg")
  if bad then
    throw (IO.userError "FAIL: a tampered generator list was ACCEPTED — the gate is not reading srs.g")
  IO.println s!"  ok — both polarities."
