/-
SCRATCH executable: emit the honest and forged multi-row traces for
`Dregg2.Circuit.Emit.MinaAccumulatorAir.{accSegDesc, accFinalDesc}`.

  lake env lean --run EmitMinaAccumulator.lean discharging > ../circuit/tests/fixtures/mina-accumulator-discharging-trace.txt
  lake env lean --run EmitMinaAccumulator.lean open        > ../circuit/tests/fixtures/mina-accumulator-open-trace.txt
  lake env lean --run EmitMinaAccumulator.lean unchained   > ../circuit/tests/fixtures/mina-accumulator-unchained-trace.txt

⚑ **THREE TRACES, AND THE PAIRING IS THE WHOLE EXHIBIT.**

* `discharging` — a REAL threaded chain on Vesta that ENDS AT THE POINT AT INFINITY. `n` rows add
  the generator, and the LAST row adds the NEGATION of the running accumulator, so `acc + (−acc)`
  closes the chain at `O` by the complete formula. Every row is a genuine `rcbSoundRow`, every
  thread holds, and the terminal `X`/`Z` blocks are the canonical all-zero limbs. This proves under
  BOTH descriptors.

* `open` — the SAME chain with the final negation replaced by one more generator add, so the
  accumulator ends at `(n+2)·G`, which is not `O`. ⚑ Every row is still honest, every thread still
  holds, every cell is still a legal limb — **the ONLY thing wrong with it is that the accumulator
  did not vanish.** It proves under `-seg` and must be REFUSED under `-final`, by a `.last` window
  gate on a terminal limb. That pair is the discharge gate's own falsifier and nothing else in the
  descriptor can be what separates them.

* `unchained` — the discharging chain's rows, but the LAST row's accumulator input is the chain's
  STARTING point rather than the previous row's output. Row-locally honest, inside the limb width,
  and refused only by a `.transition` thread gate. This is the re-pinned-instead-of-threaded
  forgery, carried onto the accumulator descriptor so the thread's refusal is exhibited HERE and not
  only on the bare row.

⚠ THE CURVE IS VESTA AND THAT IS NOT COSMETIC. `accumulator_check` is the Step/Tick leg; a Pallas
trace would satisfy a Pallas descriptor and prove the wrong claim. Modulus `qN`, limbs `qLimb`,
generator `Gv` — chosen here, next to the emit, and never defaulted.

This file only RENDERS; it authors nothing.
-/
import Dregg2.Circuit.Emit.MinaAccumulatorAir

open Dregg2.Circuit.Emit.PastaCurveSound (rcbSoundRow)
open Dregg2.Circuit.Emit.PastaCurveComplete (rcbAddM curveB3)
open Dregg2.Circuit.Emit.PastaFieldSound (qLimb)
open Dregg2.Circuit.Emit.PastaField (qN)

/-- The Vesta generator in projective coordinates. -/
def Gvesta : Nat × Nat × Nat :=
  (Dregg2.Circuit.Emit.PastaCurve.Gv.1, Dregg2.Circuit.Emit.PastaCurve.Gv.2, 1)

/-- `−P = (X : −Y : Z)`, reduced. The additive inverse a complete addition sends to `O`. -/
def negP (M : Nat) (P : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (P.1, (M - P.2.1 % M) % M, P.2.2)

/-- The accumulator after `k` additions of `Q`. -/
def walk (M b3 : Nat) (Q : Nat × Nat × Nat) : (Nat × Nat × Nat) → Nat → (Nat × Nat × Nat)
  | P, 0 => P
  | P, (k + 1) => walk M b3 Q (rcbAddM M b3 P Q) k

/-- `k` honestly threaded rows, each adding `Q`. -/
def rowsAdding (M b3 : Nat) (pl : Nat → ℤ) (Q : Nat × Nat × Nat) :
    (Nat × Nat × Nat) → Nat → List (List ℤ)
  | _, 0 => []
  | P, (k + 1) =>
      rcbSoundRow M b3 pl P.1 P.2.1 P.2.2 Q.1 Q.2.1 Q.2.2
        :: rowsAdding M b3 pl Q (rcbAddM M b3 P Q) k

/-- ⚑ **THE DISCHARGING CHAIN.** `n` rows adding `Q`, then ONE row adding the negation of the
running accumulator. The last row's output is the point at infinity, so the 64 `.last` discharge
gates are satisfied — and they are satisfied by ARITHMETIC, not by a zero the emitter wrote. -/
def dischargingRows (M b3 : Nat) (pl : Nat → ℤ) (Q P0 : Nat × Nat × Nat) (n : Nat) :
    List (List ℤ) :=
  let Pn := walk M b3 Q P0 n
  let N := negP M Pn
  rowsAdding M b3 pl Q P0 n
    ++ [rcbSoundRow M b3 pl Pn.1 Pn.2.1 Pn.2.2 N.1 N.2.1 N.2.2]

/-- ⚑ **THE OPEN CHAIN** — the same `n` rows, then one MORE generator add instead of the negation.
Row-locally identical in kind; the accumulator simply does not vanish. -/
def openRows (M b3 : Nat) (pl : Nat → ℤ) (Q P0 : Nat × Nat × Nat) (n : Nat) : List (List ℤ) :=
  rowsAdding M b3 pl Q P0 (n + 1)

/-- ⚑ **THE UNCHAINED CHAIN** — the discharging one, with the last row's ACCUMULATOR INPUT replaced
by the chain's starting point. Its own 4 476 constraints hold and its cells are real limbs; only the
thread can refuse it. -/
def unchainedRows (M b3 : Nat) (pl : Nat → ℤ) (Q P0 : Nat × Nat × Nat) (n : Nat) : List (List ℤ) :=
  let Pn := walk M b3 Q P0 n
  let N := negP M Pn
  rowsAdding M b3 pl Q P0 n
    ++ [rcbSoundRow M b3 pl P0.1 P0.2.1 P0.2.2 N.1 N.2.1 N.2.2]

def traceText (rows : List (List ℤ)) : String :=
  String.intercalate "\n" (rows.map (fun r => String.intercalate " " (r.map toString))) ++ "\n"

/-- Seven adds then the closing negation = eight rows, a power of two, which the deployed prover
needs for the base trace height. -/
def N_ADDS : Nat := 7

/-- ⚑ The two descriptors' JSON, for the same reason `EmitPastaBucketed.lean` prints its own: the
by-name ROUTER (`EmitByName.lean`, where these are registered and where the drift gate reads them)
imports the whole wrap-verifier cone, so a sibling lane rebuilding that cone makes the router
unrunnable for reasons that have nothing to do with this artifact. This mode prints
`emitVmJson2` of the SAME `def` the router's table names, so the bytes are identical by
construction — it is a second ROUTE to one term, not a second author. -/
def descJson (which : String) : Option String :=
  if which = "seg" then
    some (Dregg2.Circuit.DescriptorIR2.emitVmJson2
      Dregg2.Circuit.Emit.MinaAccumulatorAir.accSegDesc)
  else if which = "final" then
    some (Dregg2.Circuit.DescriptorIR2.emitVmJson2
      Dregg2.Circuit.Emit.MinaAccumulatorAir.accFinalDesc)
  else none

def main (args : List String) : IO Unit :=
  match args with
  | ["desc", w] =>
      match descJson w with
      | some s => IO.println s
      | none => IO.eprintln "usage: EmitMinaAccumulator.lean desc (seg|final)"
  | ["discharging"] =>
      IO.print (traceText (dischargingRows qN curveB3 qLimb Gvesta Gvesta N_ADDS))
  | ["open"] =>
      IO.print (traceText (openRows qN curveB3 qLimb Gvesta Gvesta N_ADDS))
  | ["unchained"] =>
      IO.print (traceText (unchainedRows qN curveB3 qLimb Gvesta Gvesta N_ADDS))
  | _ => IO.eprintln "usage: EmitMinaAccumulator.lean (discharging|open|unchained)"
