/-
SCRATCH executable: emit an HONEST witness trace for the windowed Pasta RCB row descriptor.

  lake env lean --run EmitPastaWindowedTrace.lean <nTerms> <nPlanes> <traceHeight> > trace.txt

One line per row, `traceHeight` lines, 525 space-separated non-negative integers each (the row's
cells, column 0 first). Every value is < 2^30 or a 0/1 selector, so each fits BabyBear.

WHY THIS IS NOT A SECOND WITNESS GENERATOR: every cell comes from
`PastaMsmWindowed.rowAsg`, which is built from `PastaCurveComplete.rcbAsg` — the SAME assignment
whose acceptance by the emitted `rowGates` is `#guard`-verified in the kernel
(`PastaMsmWindowed` §4c). Nothing here re-derives a quotient or a carry; it re-addresses an
already-checked witness and threads it down the rows.

## The schedule

Horner: per plane, one DOUBLING row (`DBL = 1`, source pinned to the accumulator) followed by
`nTerms` conditional-add rows (`DBL = 0`, `BIT` = that term's scalar bit at that plane).

⚠ PAD ROWS ARE NOT EXEMPT. `builder.when_transition()` exempts only the trace's LAST row, so every
row before it — pad rows included — must satisfy all 45 constraints. Pads are emitted as genuine
`DBL = 0, BIT = 0` rows, whose addend the selector forces to `O = (0,1,0)`: a real RCB complete add
of `acc + O`, not a zero-fill.
-/
import Dregg2.Circuit.Emit.PastaMsmWindowed

open Dregg2.Circuit.Emit.PastaMsmWindowed (rowAsg W)
open Dregg2.Circuit.Emit.PastaCurveComplete (rcbAddM curveB3)
open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.PastaCurve (Gp)

abbrev P3 := Nat × Nat × Nat

/-- The projective point at infinity, `(0 : 1 : 0)`. -/
def Oproj : P3 := (0, 1, 0)

/-- One scheduled step's effect on the accumulator: add the SELECTED addend. -/
def nextAcc (acc src : P3) (bit : Nat) : P3 :=
  rcbAddM pN curveB3 acc (if bit = 1 then src else Oproj)

/-- The `k`-th multiple of the Pallas generator, by repeated complete addition. -/
def multG : Nat → P3
  | 0     => Oproj
  | k + 1 => rcbAddM pN curveB3 (multG k) (Gp.1, Gp.2, 1)

/-- A fixed, reproducible 255-bit scalar for term `i` (no randomness in a build artifact). -/
def scalarOf (i : Nat) : Nat :=
  (1234567891 + i * 987654323) ^ 7 % (2 ^ 255)

/-- Bit `plane` of term `i`'s scalar, MSB-first over `nPlanes` planes. -/
def bitOf (nPlanes i plane : Nat) : Nat :=
  (scalarOf i) / 2 ^ (nPlanes - 1 - plane) % 2

/-- The flat schedule: for each plane, a doubling marker then `nTerms` conditional adds. `none`
marks a doubling row (its source is the accumulator, known only during the fold). -/
def schedule (nTerms nPlanes : Nat) : List (Option (Nat × Nat)) :=
  (List.range nPlanes).flatMap (fun plane =>
    none :: (List.range nTerms).map (fun t => some (t, bitOf nPlanes t plane)))

/-- Render one row's 525 cells. -/
def rowLine (acc src : P3) (bit dbl : Nat) : String :=
  let a := rowAsg acc.1 acc.2.1 acc.2.2 src.1 src.2.1 src.2.2 bit dbl
  String.intercalate " " ((List.range W).map (fun c => toString (a c)))

/-- Walk the schedule, threading the accumulator, emitting one line per row. Pads with genuine
`acc + O` rows so that every constrained row is honest, and stops at `height` rows. -/
def emitRows (pts : List P3) (sched : List (Option (Nat × Nat))) (acc0 : P3) (height : Nat) :
    List String :=
  let step : (P3 × Nat × List String) → Option (Nat × Nat) → (P3 × Nat × List String) :=
    fun st e =>
      let acc := st.1
      let (src, bit, dbl) : P3 × Nat × Nat :=
        match e with
        | none        => (acc, 1, 1)                        -- doubling row
        | some (t, b) => (pts.getD t Oproj, b, 0)           -- conditional-add row for term `t`
      (nextAcc acc src bit, st.2.1 + 1, st.2.2 ++ [rowLine acc src bit dbl])
  let real := sched.foldl step (acc0, 0, [])
  -- pad every remaining CONSTRAINED row with a genuine `acc + O` add …
  let padCount := height - 1 - real.2.2.length
  let padded := (List.range padCount).foldl
    (fun st _ => (nextAcc st.1 Oproj 0, st.2.1, st.2.2 ++ [rowLine st.1 Oproj 0 0]))
    (real.1, real.2.1, real.2.2)
  -- … and emit the final row, whose gates the transition domain does not reach.
  padded.2.2 ++ [rowLine padded.1 Oproj 0 0]

def main (args : List String) : IO Unit := do
  let nTerms  := (args.getD 0 "4").toNat!
  let nPlanes := (args.getD 1 "8").toNat!
  let height  := (args.getD 2 "64").toNat!
  let pts := (List.range nTerms).map (fun i => multG (i + 1))
  let lines := emitRows pts (schedule nTerms nPlanes) Oproj height
  for l in lines do IO.println l
