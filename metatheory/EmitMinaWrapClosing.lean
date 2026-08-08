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
  lake env lean --run EmitMinaWrapClosing.lean desc seg         > ../circuit/tests/fixtures/mina-wrap-closing-seg.json
  ⚑ the transcript-weld set (2026-08-08):
  lake env lean --run EmitMinaWrapClosing.lean desc fs                 > ../circuit/tests/fixtures/mina-wrap-closing-fs.json
  lake env lean --run EmitMinaWrapClosing.lean desc fs-shifted-manifest> ../circuit/tests/fixtures/mina-wrap-closing-fs-shifted-manifest.json
  lake env lean --run EmitMinaWrapClosing.lean desc srs-fs             > ../circuit/tests/fixtures/mina-wrap-closing-srs-fs.json
  lake env lean --run EmitMinaWrapClosing.lean desc srs-fs-shifted     > ../circuit/tests/fixtures/mina-wrap-closing-srs-fs-shifted.json
  lake env lean --run EmitMinaWrapClosing.lean fs                      > ../circuit/tests/fixtures/mina-wrap-closing-fs-trace.txt
  lake env lean --run EmitMinaWrapClosing.lean fs-shifted              > ../circuit/tests/fixtures/mina-wrap-closing-fs-shifted-trace.txt
  lake env lean --run EmitMinaWrapClosing.lean srs-fs                  > ../circuit/tests/fixtures/mina-wrap-closing-srs-fs-trace.txt
  lake env lean --run EmitMinaWrapClosing.lean srs-fs-shifted          > ../circuit/tests/fixtures/mina-wrap-closing-srs-fs-shifted-trace.txt

⚠ This driver is NOT a `[[lean_exe]]` target in `lakefile.toml`, so an API change in
`MinaWrapClosingAir` stays CI-green until a human re-runs the emit. Named as a defect, not as a
convention.

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
import Dregg2.Circuit.Emit.MinaRealBlockTranscript

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

/-! ## ⚑⚑ THE TRANSCRIPT-ORDERED CONSTRUCTION — the one the `-fs` weld is about.

⚑ **READ THE ORDER, IT IS THE WHOLE EXHIBIT.** Everything above builds `delta` LAST, by `deltaFor`,
from a chosen `c` — which is the FORGER's order and is why `MinaWrapClosingAir` §6 can shift it.
This block builds in upstream's order (`ipa.rs:382-383`):

    1. a sponge state `TR_IN` (chosen — it stands for the state after the fifteen IPA rounds)
    2. `delta` — chosen FREELY, but chosen NOW, before `c` exists
    3. `TR_OUT := perm(TR_IN + [delta.x, delta.y, 0])`   -- `absorb_g(&[opening.delta])`
    4. `c := ScalarChallenge(low128(TR_OUT[0])).to_field(endo_r)`  -- the very next line upstream
    5. `acc₀ := c·Q`
    6. and only THEN is a manifest slot solved for, so the chain closes — here it is `H`, the SRS
       blinding base, at `z₂ = 1`.

Step 6 is where the residue lives and it is named rather than hidden: SOMETHING has to absorb the
residual, and with `delta` fixed by step 3 it cannot be `delta`. Upstream refuses step 6 by the
dlog/extraction argument (P10), not by a transcript — see `MinaWrapClosingAir` §7 caveat (c).

⚠ `TR_IN` is CHOSEN and is not block 539508's. What this exhibits is the ORDER and the two
polarities; it is not a claim about a Mina proof, exactly as the `c`/`z₁`/`z₂`/`b₀` above are not. -/

/-- Binary modular exponentiation — needed only to normalise a projective point to affine, because
`absorb_g` absorbs AFFINE coordinates. Rendering only; nothing in any AIR reads this. -/
def powMod (b e m : Nat) : Nat :=
  let rec go : Nat → Nat → Nat → Nat
    | 0, _, acc => acc
    | (k + 1), bb, acc =>
        go ((k + 1) / 2) (bb * bb % m) (if (k + 1) % 2 = 1 then acc * bb % m else acc)
    termination_by k => k
    decreasing_by exact Nat.div_lt_self (Nat.succ_pos _) (by omega)
  go e (b % m) (1 % m)

/-- `(X : Y : Z) ↦ (X/Z, Y/Z, 1)` at `pN`, by Fermat. -/
def affineP (P : P3) : P3 :=
  let zi := powMod P.2.2 (pN - 2) pN
  ((P.1 * zi) % pN, (P.2.1 * zi) % pN, 1)

/-- ⚑ STEP 1 — the sponge state entering the `delta` absorb. CHOSEN. -/
def TR_IN : P3 := (7, 11, 13)

/-- ⚑ STEP 2 — `delta`, fixed BEFORE `c` exists, in AFFINE form because that is what `absorb_g`
absorbs. -/
def DELTA_FS : P3 := affineP (kG 77)

/-- ⚑ STEP 3 — `sponge.absorb_g(&[opening.delta])`: one rate-2 absorb, one Kimchi permutation over
`Fp`. This is EXACTLY `dregg-pasta-fp-absorb::v1`'s program at `fpParams`. -/
def TR_OUT : List Nat :=
  Dregg2.Circuit.Emit.PastaPoseidonFq.Core.perm Dregg2.Circuit.Emit.PastaPoseidonFq.fpParams
    [(TR_IN.1 + DELTA_FS.1) % pN, (TR_IN.2.1 + DELTA_FS.2.1) % pN, TR_IN.2.2]

/-- The squeezed lane — `sponge.challenge()`'s raw output before truncation. -/
def SQUEEZE : Nat := TR_OUT.getD 0 0

/-- ⚑ STEP 4 — `ScalarChallenge::new(sponge.challenge()).to_field(&endo_r)`, at the SAME `endo_r`
`MinaRealBlockTranscript` pins from a real block. -/
def C_FS : Nat :=
  (Dregg2.Circuit.Emit.KimchiVerify.endoMap
    Dregg2.Circuit.Emit.MinaRealBlockTranscript.ENDO_R
    (Dregg2.Circuit.Emit.KimchiVerify.low128 SQUEEZE)).val

/-- ⚑ STEP 5 — the accumulator entering row 0, at the transcript's own `c`. -/
def ACC0_FS : P3 := redPtP (smulP (C_FS % qN) QPT)

/-- `z₂ = 1`, so the `H` slot is exactly `−H` and step 6 is one addition rather than a dlog. -/
def Z2_FS : Nat := 1

/-- The part of the chain that is fixed once steps 1-5 are done: `acc₀`, `delta`, `−(z₁b₀)·U` and
the five SRS slots. -/
def FS_KNOWN_SUM : P3 :=
  (redPtP DELTA_FS :: scaledNeg (Z1 * B0 % qN) UPT :: srsSlots GS UVEC Z1 NGEN).foldl
    (fun acc A => rcbAddM pN curveB3 acc A) ACC0_FS

/-- ⚑ STEP 6 — the SRS blinding base, DERIVED so the chain closes at a `delta` the transcript
already fixed. ⚠ This is the inversion the exhibit is about: upstream fixes `delta` first and
lets the SCHNORR RESPONSES `z₁`/`z₂` close the equation, and their soundness is P10. Here the
closing slot is `H`, which is the same move at demonstration scale and is labelled as such. -/
def H_FS : P3 := redPtP FS_KNOWN_SUM

/-- The welded manifest: same shape, `delta` from step 2, `H` from step 6. -/
def MANIFEST_FS : List P3 :=
  closingAddends GS UVEC Z1 B0 Z2_FS DELTA_FS UPT H_FS NGEN

/-! ### ⚑ THE SHIFT — `MinaWrapClosingAir.the_delta_shift_is_invisible`, CONSTRUCTED. -/

/-- The group element the forgery shifts by. Any real Pallas point does. -/
def SHIFT_PT : P3 := kG 3

/-- ⚑ `delta ↦ delta + Δ`, renormalised to affine so the AFFINE pin is not what refuses it — the
falsifier must fire on the DELTA pin, not on a normalisation gate. -/
def DELTA_SHIFTED : P3 := affineP (rcbAddM pN curveB3 DELTA_FS SHIFT_PT)

/-- ⚑ …and `acc₀ ↦ acc₀ − Δ`, the matching move. -/
def ACC0_SHIFTED : P3 := redPtP (rcbAddM pN curveB3 ACC0_FS (negP SHIFT_PT))

/-- ⚑⚑ The forger's manifest — `MANIFEST_FS` with slot 0 replaced and NOTHING else touched. -/
def MANIFEST_SHIFTED : List P3 :=
  closingAddends GS UVEC Z1 B0 Z2_FS DELTA_SHIFTED UPT H_FS NGEN

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

/-- ⚑ Widen a ROUTED trace to the welded descriptor's `3 091` columns: the guard at `DBIND`, the
nine attested-program lanes at `FSVK`, and the squeezed sponge lane's 32 limbs at `TROUT`. Only row
0 carries them — `dbindStartLeg` and `trOutPinLegs` are `.first`, and on later rows the guard is a
free bit the prover sets to zero, which makes the bind inert there. -/
def withWeldCells (rows : List (List ℤ)) : List (List ℤ) :=
  rows.mapIdx (fun i r =>
    if i = 0 then
      r ++ [1] ++ ABSORB_VK_LANES
        ++ (List.range Dregg2.Circuit.Emit.PastaFieldSound.SK).map
             (fun j => (((SQUEEZE / 2 ^ (8 * j)) % 256 : Nat) : ℤ))
    else r ++ [0] ++ List.replicate 9 (0 : ℤ)
           ++ List.replicate Dregg2.Circuit.Emit.PastaFieldSound.SK (0 : ℤ))

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
    -- ⚑ the transcript-ordered block
    , ptText "tr_in" TR_IN
    , ptText "delta_fs" DELTA_FS
    , "squeeze " ++ toString SQUEEZE
    , "tr_out " ++ String.intercalate " " (TR_OUT.map toString)
    , "c_fs " ++ toString C_FS
    , ptText "acc0_fs" ACC0_FS
    , ptText "h_fs" H_FS
    , ptText "shift_pt" SHIFT_PT
    , ptText "delta_shifted" DELTA_SHIFTED
    , ptText "acc0_shifted" ACC0_SHIFTED
    , ptText "fs_end" (chainEnd ACC0_FS MANIFEST_FS)
    , ptText "fs_shifted_end" (chainEnd ACC0_SHIFTED MANIFEST_SHIFTED)
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
  -- ⚑ the transcript-ordered trio
  else if which = "fs" then
    some (Dregg2.Circuit.DescriptorIR2.emitVmJson2
      (closingFsDesc GS UVEC Z1 B0 Z2_FS DELTA_FS UPT H_FS TR_IN NGEN))
  else if which = "srs-fs" then
    some (Dregg2.Circuit.DescriptorIR2.emitVmJson2
      (closingRoutedDescNamed "dregg-mina-wrap-closing-srs::v1" MANIFEST_FS))
  else if which = "srs-fs-shifted" then
    some (Dregg2.Circuit.DescriptorIR2.emitVmJson2
      (closingRoutedDescNamed "dregg-mina-wrap-closing-srs::v1" MANIFEST_SHIFTED))
  -- ⚑⚑ THE SURGICAL FALSIFIER'S DESCRIPTOR: the SHIFTED manifest (so the addend bus BALANCES and
  -- a LogUp imbalance cannot be what refuses) against the HONEST transcript pin. Nothing but the
  -- `delta` pin can fire on the shifted trace here.
  else if which = "fs-shifted-manifest" then
    some (Dregg2.Circuit.DescriptorIR2.emitVmJson2
      (closingFsDescNamed "dregg-mina-wrap-closing-fs::v1" MANIFEST_SHIFTED
        (redPtP DELTA_FS) TR_IN))
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
  -- ⚑ the transcript-ordered traces
  | ["fs"] =>
      IO.print (traceText (withWeldCells (withRowIndex (rowsFromAddends ACC0_FS MANIFEST_FS))))
  | ["fs-shifted"] =>
      IO.print (traceText (withWeldCells
        (withRowIndex (rowsFromAddends ACC0_SHIFTED MANIFEST_SHIFTED))))
  | ["srs-fs"] =>
      IO.print (traceText (withRowIndex (rowsFromAddends ACC0_FS MANIFEST_FS)))
  | ["srs-fs-shifted"] =>
      IO.print (traceText (withRowIndex (rowsFromAddends ACC0_SHIFTED MANIFEST_SHIFTED)))
  | _ =>
      IO.eprintln
        "usage: EmitMinaWrapClosing.lean (desc <w>|params|bound|bound-routed|free-sg|free-sg-routed)"
