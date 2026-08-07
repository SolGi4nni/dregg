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
import Dregg2.Circuit.Emit.MinaAccumulatorSrsDemo

open Dregg2.Circuit.Emit.PastaCurveSound (rcbSoundRow)
open Dregg2.Circuit.Emit.PastaCurveComplete (rcbAddM curveB3 Oproj)
open Dregg2.Circuit.Emit.PastaFieldSound (qLimb)
open Dregg2.Circuit.Emit.PastaField (pN qN)

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

/-- ⚑ `k` honestly threaded rows over an EXPLICIT ADDEND LIST. The routed descriptor needs this
shape rather than `rowsAdding`'s "same addend every row", because the declared manifest and the
trace's addend columns must be the SAME list or the exact-public balance refuses. -/
def rowsFromAddends (M b3 : Nat) (pl : Nat → ℤ) :
    (Nat × Nat × Nat) → List (Nat × Nat × Nat) → List (List ℤ)
  | _, [] => []
  | P, (A :: rest) =>
      rcbSoundRow M b3 pl P.1 P.2.1 P.2.2 A.1 A.2.1 A.2.2
        :: rowsFromAddends M b3 pl (rcbAddM M b3 P A) rest

/-- Widen every row to the routed descriptor's `3 049` columns by appending the ROW INDEX, which is
column `RIDX = 3 048`. -/
def withRowIndex (rows : List (List ℤ)) : List (List ℤ) :=
  rows.mapIdx (fun i r => r ++ [(i : ℤ)])

/-- ⚑ **THE SHARP FORGERY'S ADDENDS: `2G` seven times, then the closing negation.**

Every addend is a REAL Vesta point, every row is a genuine `rcbSoundRow`, every thread holds, every
cell is a legal 8-bit limb, the chain starts at the SAME published `acc_in` (`G`) and ends at the
SAME published `acc_out` (`O`) — so `PI[0..191]` is byte-identical to the honest trace's. **The only
thing wrong with it is that the addends are not the ones the descriptor declares.**

That is exactly the case `accumulator_discharge_forced` admits: it proves under `-final` and must be
REFUSED under `-routed`, by the balance of `mina_accumulator_addends` and by nothing else. -/
def Q2 : Nat × Nat × Nat := rcbAddM qN curveB3 Gvesta Gvesta

def substitutedAddends : List (Nat × Nat × Nat) :=
  List.replicate N_ADDS Q2 ++ [negP qN (walk qN curveB3 Q2 Gvesta N_ADDS)]

/-! ## ⚑⚑ THE SRS RAIL — the manifest is `−s_r · G_r` over the PINNED blob, not a list.

`MinaAccumulatorAir` §10 removed the free `As` parameter: `srsScaledAddends Gs u n` is a total
function of a generator list and the challenges. This section supplies the two inputs and RENDERS —
it still authors nothing.

* `Gs` is `MinaStepSrsG.SRS_G`, decoded from `metatheory/emitted/mina-accumulator/vesta_srs_g.bin`
  (sha `f28a8a91…`), the SAME blob `dregg_bridge::mina_accumulator_discharge::VESTA_SRS_G_SHA256`
  pins and re-checks on-curve. One decode, not a transcription.
* `u⃗` is `demoChals` below — a PARAMETER CHOICE with §8a's exact status, and the ONLY thing the
  emitter still chooses.

⚠ THE PAIRING. `mina-accumulator-routed.json`'s manifest is `demoAddends` — seven `G`s and a closing
negation, an internally-consistent table that DISCHARGES and is **not** anybody's scalar multiples.
That is precisely the forgery §8's theorem admits. The routed trace already on disk therefore proves
under `-routed` and must be REFUSED under `-srs`, by the balance of `mina_accumulator_addends` and
by nothing else. The old-admits pole is not a fixture written for the occasion; it is the previous
rung's own honest artifact. -/

open Dregg2.Circuit.Emit.MinaAccumulatorSrsDemo (demoChals srsDemoAddends srsDemoClaim
  accSrsDemoDesc srsParamsText demoHeadLanes accHeadDemoDesc accHeadGenesisDesc)

/-! ## ⚑⚑ THE HEAD RAIL — the same chain, plus the nineteen columns the seam reads.

`MinaAccumulatorAir` §11 adds `RIDX + 1 … RIDX + 19`: the guard, the nine published head lanes and
the nine attested program lanes. The guard is `1` on the FIRST row and `0` on every successor —
which is not a convention chosen here but what `headOkOnLeg`/`headOkOffLeg` force, and what makes
the seam's off-row obligation the first row's and not one per intermediate accumulator.

⚠ **THE PROGRAM LANES ARE THE DESCRIPTOR'S OWN `MINA_HEAD_VK_LANES`, NOT A SECOND SPELLING.** A
transcription here would let the trace and the `vkPin` drift into agreement about a program neither
names; `75df624cf` is the commit where exactly that happened one rail over. -/

/-- Widen the routed rows with the head seam's nineteen columns. -/
def withHeadSeam (H : List ℤ) (rows : List (List ℤ)) : List (List ℤ) :=
  rows.mapIdx (fun i r =>
    r ++ ((if i = 0 then (1 : ℤ) else 0) :: H)
      ++ Dregg2.Circuit.Emit.MinaAccumulatorAir.MINA_HEAD_VK_LANES)

/-- ⚑ The three descriptors' JSON, for the same reason `EmitPastaBucketed.lean` prints its own: the
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
  else if which = "routed" then
    some (Dregg2.Circuit.DescriptorIR2.emitVmJson2
      Dregg2.Circuit.Emit.MinaAccumulatorAir.accRoutedDemoDesc)
  else if which = "srs" then
    some (Dregg2.Circuit.DescriptorIR2.emitVmJson2 accSrsDemoDesc)
  else if which = "head" then
    some (Dregg2.Circuit.DescriptorIR2.emitVmJson2 accHeadDemoDesc)
  else if which = "head-genesis" then
    some (Dregg2.Circuit.DescriptorIR2.emitVmJson2 accHeadGenesisDesc)
  else none

def main (args : List String) : IO Unit :=
  match args with
  | ["desc", w] =>
      match descJson w with
      | some s => IO.println s
      | none => IO.eprintln "usage: EmitMinaAccumulator.lean desc (seg|final|routed|srs|head|head-genesis)"
  | ["discharging"] =>
      IO.print (traceText (dischargingRows qN curveB3 qLimb Gvesta Gvesta N_ADDS))
  | ["open"] =>
      IO.print (traceText (openRows qN curveB3 qLimb Gvesta Gvesta N_ADDS))
  | ["unchained"] =>
      IO.print (traceText (unchainedRows qN curveB3 qLimb Gvesta Gvesta N_ADDS))
  -- ⚑ The ROUTED pair. Both are 3 049 columns wide (the row index in column 3 048); the narrow
  -- rendering of the SAME substituted chain is what proves under `-final`, which is the
  -- OLD-ADMITS pole. `demoAddends` is the descriptor's own manifest — one source, not two.
  | ["routed"] =>
      IO.print (traceText (withRowIndex (rowsFromAddends qN curveB3 qLimb Gvesta
        Dregg2.Circuit.Emit.MinaAccumulatorAir.demoAddends)))
  | ["substituted"] =>
      IO.print (traceText (withRowIndex (rowsFromAddends qN curveB3 qLimb Gvesta
        substitutedAddends)))
  | ["substituted-narrow"] =>
      IO.print (traceText (rowsFromAddends qN curveB3 qLimb Gvesta substitutedAddends))
  -- ⚑ The SRS rail. The chain starts at the COMPUTED claim and its addends are the DERIVED
  -- `−s_r·G_r`; both come from `srsScaledAddends`/`smulV`, so the manifest and the trace cannot
  -- drift. The OLD-ADMITS pole of this pair is `mina-accumulator-routed-trace.txt`, already on disk.
  | ["srs"] =>
      IO.print (traceText (withRowIndex (rowsFromAddends qN curveB3 qLimb srsDemoClaim
        srsDemoAddends)))
  | ["srs-params"] => IO.print srsParamsText
  -- ⚑ The HEAD rail. The SAME srs chain — same claim, same derived addends, same manifest — with
  -- the seam's nineteen columns appended. The OLD-ADMITS pole of this pair is
  -- `mina-accumulator-srs-trace.txt`, already on disk: this trace narrowed to 3 049 columns IS it.
  | ["head"] =>
      IO.print (traceText (withHeadSeam demoHeadLanes
        (withRowIndex (rowsFromAddends qN curveB3 qLimb srsDemoClaim srsDemoAddends))))
  | _ => IO.eprintln
      "usage: EmitMinaAccumulator.lean (discharging|open|unchained|routed|substituted|substituted-narrow|srs|srs-params|head)"
