/-
SCRATCH executable: emit the descriptors and the multi-row traces for
`Dregg2.Circuit.Emit.MinaWrapClosingAir`.

  lake env lean --run EmitMinaWrapClosing.lean desc final       > ../circuit/tests/fixtures/mina-wrap-closing-final.json
  lake env lean --run EmitMinaWrapClosing.lean desc srs         > ../circuit/tests/fixtures/mina-wrap-closing-srs.json
  lake env lean --run EmitMinaWrapClosing.lean desc srs-forged  > ../circuit/tests/fixtures/mina-wrap-closing-srs-forged.json
  lake env lean --run EmitMinaWrapClosing.lean bound            > ../circuit/tests/fixtures/mina-wrap-closing-bound-trace.txt
  lake env lean --run EmitMinaWrapClosing.lean bound-routed     > ../circuit/tests/fixtures/mina-wrap-closing-bound-routed-trace.txt
  lake env lean --run EmitMinaWrapClosing.lean free-sg          > ../circuit/tests/fixtures/mina-wrap-closing-free-sg-trace.txt
  lake env lean --run EmitMinaWrapClosing.lean free-sg-routed   > ../circuit/tests/fixtures/mina-wrap-closing-free-sg-routed-trace.txt
  lake env lean --run EmitMinaWrapClosing.lean params           > ../circuit/tests/fixtures/mina-wrap-closing-params.txt

⚑⚑ **THE FALSIFIER IS THE FORGERY THE VACUITY THEOREM NAMES, AND NOTHING ELSE.**

`MinaWrapVerifierAir.opening_is_vacuous_when_sg_is_free` says: with `sg` free, a prover picks
`sg` so that `c·Q + delta − z₁·sg − z₁b₀·U − z₂·H = O` at EVERY value of everything else. Here that
prover is CONSTRUCTED rather than described — `SG_FORGED` is an arbitrary Pallas point that is NOT
`⟨s, G⟩`, and `DELTA_FORGED` is the `delta` that makes his chain close. Then:

* **`free-sg`** is his chain in the UN-ELIMINATED shape — four addends, `−z₁·sg*` among them —
  and it VANISHES. It is a genuine `rcbSoundRow` chain, every thread holds, every cell is a legal
  limb, the terminal `X`/`Z` blocks are canonically zero. **It PROVES under
  `dregg-mina-wrap-closing-final::v1`.** That is the vacuity, as a real STARK proof rather than as
  a theorem about a model.

* **`free-sg-routed`** is the SAME prover's own data — his `delta*`, his `z₁`, `z₂`, `b₀`, the same
  `c·Q` published at `PI[0..95]` — run through the ELIMINATED manifest, where the `sg` slot does
  not exist and the `−z₁·s_r·G_r` slots do. His chain now lands on `z₁·(sg* − ⟨s,G⟩) ≠ O`.
  **REFUSED, by a `.last` discharge gate on a terminal limb** — an algebraic constraint, not a bus,
  and not a range lookup: every cell of the refused trace is inside the declared 8-bit limb width.

* **`bound` / `bound-routed`** are the honest pair at the SAME shape and the SAME row count, where
  `delta` is derived from the TRUE `⟨s, G⟩`. They prove under both rungs. Without them the refusal
  above would be evidence that the descriptor accepts nothing.

⚠ **THE CURVE IS PALLAS AND THAT IS NOT COSMETIC.** `opening.sg` and the Wrap SRS live on Pallas;
coordinates reduce at `pN` and scalars at `qN`. A Vesta trace would satisfy a Vesta descriptor and
prove the wrong claim. Modulus `pN`, limbs `pLimb`, generator `Gp` — chosen here, next to the emit,
and never defaulted.

⚠ **THE DEMONSTRATION IS AT `n = 5` GENERATORS, NOT `2^15`.** Five SRS slots plus the three group
terms is eight rows, which is a power of two and therefore a legal base trace height. The full-width
chain is a FOLD of segments — `MinaAccumulatorAir.the_full_width_sum_needs_the_fold` is that
arithmetic — and nothing here should be read as evidence about `2^15`. What the eight rows exhibit
is the ALGEBRA and the two polarities; the width is the fold's problem.

This file only RENDERS; it authors nothing.
-/
import Dregg2.Circuit.Emit.MinaWrapClosingAir

open Dregg2.Circuit.Emit.PastaCurveSound (rcbSoundRow)
open Dregg2.Circuit.Emit.PastaCurveComplete (rcbAddM curveB3 Oproj)
open Dregg2.Circuit.Emit.PastaFieldSound (pLimb)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.MinaWrapClosingAir

abbrev P3 : Type := Nat × Nat × Nat

/-- The Pallas generator, projective. -/
def Gp1 : P3 := (Dregg2.Circuit.Emit.PastaCurve.Gp.1, Dregg2.Circuit.Emit.PastaCurve.Gp.2, 1)

/-- `[k]·G` on Pallas, through the SAME complete formula the row computes. -/
def kG (k : Nat) : P3 := smulP k Gp1

/-! ## The demonstration's parameters.

⚠ These are CHOSEN, and that is their whole status: the arithmetic below is a real Pallas
computation over `rcbAddM pN curveB3`, but the operands are not block 539508's. What is exhibited is
the algebra and the two polarities, never a claim about a Mina proof. -/

/-- The IPA round challenges, endo-lifted, as the manifest's `u⃗`. Five distinct values so
`bPolyCoeff` is not constantly `1`. -/
def UVEC : List Nat := [3, 5, 7, 11, 13]

/-- The generator count of the demonstration slice. `3 + 5 = 8` rows. -/
def NGEN : Nat := 5

/-- The demonstration's SRS generators — five distinct real Pallas points. -/
def GS : List P3 := [kG 1, kG 2, kG 3, kG 5, kG 8]

def C_CHAL : Nat := 9
def Z1 : Nat := 23
def Z2 : Nat := 29
def B0 : Nat := 31

/-- `Q` — the IPA aggregate, a real Pallas point. -/
def QPT : P3 := kG 17
/-- `U` — `groupMap(challenge_fq())`, a real Pallas point. -/
def UPT : P3 := kG 19
/-- `H` — the SRS blinding base. -/
def HPT : P3 := kG 21

/-- The accumulator entering row 0: `c·Q`, published at `PI[0..95]`. -/
def ACC0 : P3 := redPtP (smulP (C_CHAL % qN) QPT)

/-- ⚑ `S = ⟨s(u⃗), G⟩` — the terminal MSM the SRS slots sum to, computed HERE by the same
`bPolyCoeff`/`smulP` the manifest uses, so the honest `delta` below is derived and not fitted. -/
def SMSM : P3 :=
  (List.range NGEN).foldl
    (fun acc r => rcbAddM pN curveB3 acc
      (smulP (Dregg2.Circuit.Emit.MinaAccumulatorAir.bPolyCoeff qN UVEC r)
        (GS.getD r (0, 0, 0))))
    Oproj

/-- The `delta` that makes the ELIMINATED relation close at a given `sg`-side point `T`:
`delta := −c·Q + z₁·T + (z₁b₀)·U + z₂·H`. At `T = S` this is the honest opening proof's `delta`;
at `T = sg*` it is the forger's. -/
def deltaFor (T : P3) : P3 :=
  let a := negP (smulP (C_CHAL % qN) QPT)
  let b := smulP (Z1 % qN) T
  let c := smulP (Z1 * B0 % qN) UPT
  let d := smulP (Z2 % qN) HPT
  redPtP (rcbAddM pN curveB3 (rcbAddM pN curveB3 (rcbAddM pN curveB3 a b) c) d)

/-- The honest `delta`, derived from the TRUE `⟨s, G⟩`. -/
def DELTA_HONEST : P3 := deltaFor SMSM

/-- ⚑⚑ **THE FREE `sg`.** An arbitrary real Pallas point that is not `⟨s, G⟩` — the witness
`opening_is_vacuous_when_sg_is_free` says the prover may choose. -/
def SG_FORGED : P3 := kG 4242

/-- …and the `delta` that makes HIS chain close. -/
def DELTA_FORGED : P3 := deltaFor SG_FORGED

/-! ## The two manifests. -/

/-- The honest eliminated manifest: `delta`, `−(z₁b₀)·U`, `−z₂·H`, then the five `−(z₁·s_r)·G_r`. -/
def MANIFEST_HONEST : List P3 :=
  closingAddends GS UVEC Z1 B0 Z2 DELTA_HONEST UPT HPT NGEN

/-- ⚑ The SAME function at the FORGER's own `delta`. This is the descriptor a verifier builds for
his proof: his `delta` is in it, his scalars are in it, and there is no slot for his `sg`. -/
def MANIFEST_FORGED : List P3 :=
  closingAddends GS UVEC Z1 B0 Z2 DELTA_FORGED UPT HPT NGEN

/-- ⚑ **THE FORGER'S UN-ELIMINATED CHAIN** — four addends, `−z₁·sg*` among them. This is the shape
the closing check has while `sg` is a free witness, and it VANISHES by his construction. -/
def FREE_SG_ADDENDS : List P3 :=
  [ redPtP DELTA_FORGED
  , scaledNeg (Z1 % qN) SG_FORGED
  , scaledNeg (Z1 * B0 % qN) UPT
  , scaledNeg (Z2 % qN) HPT ]

/-! ## Rendering. -/

/-- `k` honestly threaded rows over an EXPLICIT addend list, starting from `P`. -/
def rowsFromAddends : P3 → List P3 → List (List ℤ)
  | _, [] => []
  | P, (A :: rest) =>
      rcbSoundRow pN curveB3 pLimb P.1 P.2.1 P.2.2 A.1 A.2.1 A.2.2
        :: rowsFromAddends (rcbAddM pN curveB3 P A) rest

/-- The chain's terminal accumulator, so the emitter can PRINT what it landed on rather than
predict it. -/
def chainEnd : P3 → List P3 → P3
  | P, [] => P
  | P, (A :: rest) => chainEnd (rcbAddM pN curveB3 P A) rest

/-- Widen every row to the routed descriptor's `3 049` columns with the row index at `RIDX`. -/
def withRowIndex (rows : List (List ℤ)) : List (List ℤ) :=
  rows.mapIdx (fun i r => r ++ [(i : ℤ)])

def traceText (rows : List (List ℤ)) : String :=
  String.intercalate "\n" (rows.map (fun r => String.intercalate " " (r.map toString))) ++ "\n"

def ptText (nm : String) (P : P3) : String :=
  nm ++ " " ++ toString P.1 ++ " " ++ toString P.2.1 ++ " " ++ toString P.2.2

/-- ⚑ The parameter dump the Rust test re-asserts against, so no number is transcribed twice. -/
def paramsText : String :=
  String.intercalate "\n"
    [ "ngen " ++ toString NGEN
    , "c " ++ toString C_CHAL, "z1 " ++ toString Z1, "z2 " ++ toString Z2, "b0 " ++ toString B0
    , ptText "acc0" ACC0
    , ptText "smsm" SMSM
    , ptText "sg_forged" SG_FORGED
    , ptText "delta_honest" DELTA_HONEST
    , ptText "delta_forged" DELTA_FORGED
    , ptText "bound_end" (chainEnd ACC0 MANIFEST_HONEST)
    , ptText "free_sg_end" (chainEnd ACC0 FREE_SG_ADDENDS)
    , ptText "free_sg_routed_end" (chainEnd ACC0 MANIFEST_FORGED)
    ] ++ "\n"

def descJson (which : String) : Option String :=
  if which = "seg" then
    some (Dregg2.Circuit.DescriptorIR2.emitVmJson2 closingSegDesc)
  else if which = "final" then
    some (Dregg2.Circuit.DescriptorIR2.emitVmJson2 closingFinalDesc)
  else if which = "srs" then
    some (Dregg2.Circuit.DescriptorIR2.emitVmJson2
      (closingRoutedDescNamed "dregg-mina-wrap-closing-srs::v1" MANIFEST_HONEST))
  else if which = "srs-forged" then
    some (Dregg2.Circuit.DescriptorIR2.emitVmJson2
      (closingRoutedDescNamed "dregg-mina-wrap-closing-srs::v1" MANIFEST_FORGED))
  else none

def main (args : List String) : IO Unit :=
  match args with
  | ["desc", w] =>
      match descJson w with
      | some s => IO.println s
      | none => IO.eprintln "usage: EmitMinaWrapClosing.lean desc (seg|final|srs|srs-forged)"
  | ["params"] => IO.print paramsText
  | ["bound"] => IO.print (traceText (rowsFromAddends ACC0 MANIFEST_HONEST))
  | ["bound-routed"] =>
      IO.print (traceText (withRowIndex (rowsFromAddends ACC0 MANIFEST_HONEST)))
  | ["free-sg"] => IO.print (traceText (rowsFromAddends ACC0 FREE_SG_ADDENDS))
  | ["free-sg-routed"] =>
      IO.print (traceText (withRowIndex (rowsFromAddends ACC0 MANIFEST_FORGED)))
  | _ =>
      IO.eprintln
        "usage: EmitMinaWrapClosing.lean (desc <w>|params|bound|bound-routed|free-sg|free-sg-routed)"
