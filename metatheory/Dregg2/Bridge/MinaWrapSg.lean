/-
# Dregg2.Bridge.MinaWrapSg — **the terminal `⟨s, srs.g⟩` MSM as a COMPILED function of a block's
wire arguments, not a kernel `decide` over pinned literals.**

## What this file is, and what it is NOT

It is the **CHECKER**. `sgVerdict chals gens sg` takes `k` IPA challenges, `2^k` generators and a
claimed `sg`, and answers. It is parameterised over all three, it holds no fixture, and it is the
function a per-block checkpoint would call. Its instance differential — this checker run on Mina
devnet block 539508's own `srs.g`, its own wire-derived challenges and its own `opening.sg`, both
polarities — is `Dregg2.Bridge.MinaWrapSgWeld`, which is deliberately NOT rooted (it carries the
32,768-generator fixture).

⚑ **SAY WHICH OBJECT THIS BINDS.** Rung 5h (`MinaWrapSgCore` + `MinaWrapSgChunk0..3`) binds the
CONTENTS: `sg` really is `⟨s, srs.g⟩` over the 32,768 real generators. The `5h-AIR` rungs
(`PastaMsmBound`/`PastaMsmOnCurve`) bind a PROOF OBJECT — that the emitted constraints force a
row's source to be `srs.g` at the index the manifest names — and bind no contents. **They are
different objects and neither subsumes the other.** This file is on the CONTENTS side: it is the
same statement rung 5h makes, evaluated by the compiled evaluator instead of by the kernel. It is
NOT a Lean-authored AIR and it emits no constraints; the AIR half stays where it is.

## Why moving the evaluation matters, in one number

The kernel proves rung 5h's 32 chunk statements in **≈3.5 h of serial `decide` at ~28 GB** (105 min
at 2-way parallelism; each chunk peaks far higher when rooted, which is why the family is
allowlisted out of `Dregg2.lean`). That cost is the whole reason `docs/MINA-CHECKPOINT-CADENCE.md`
puts a *checked* checkpoint at "nothing shorter than a day". The arithmetic did not change; the
evaluator did. `#guard` uses Lean's untrusted evaluator, and the `lean_exe mina_sg_bench` beside
this file runs the identical function through the native compiler.

⚠ **Neither `#guard` nor the bench is a proof.** The kernel proves the CHECKER — `PastaIpaFold`
§3's `msmHorner_eq_msmN` says the bit-plane scan computes the MSM, at arbitrary
`AddCommGroup`, with the 255-bit budget as a real hypothesis. A differential checks the INSTANCE.
That split is the point: the expensive half was never the theorem, it was re-deciding one block's
arithmetic inside the kernel.

## What is still trusted here, unchanged by this file

`srs.g` itself. It is on-curve-checked (below, and in rung 5h) but not DERIVED — deriving it needs
in-kernel BLAKE2b + SvdW at 32,768 inputs. And the RCB residual (RCB'15 Thm 1) that transports
`PastaIpaFold` §3's group statement to the `Nat`-triple evaluation in §3c. Both are inherited from
rungs 5a–5f; this file adds neither.

## Axiom hygiene

No `sorry`/`admit`/`native_decide`. Every pin below is a `#guard` on a four-point toy over the real
Pallas generator — the block-scale pins live in the weld. Rooted in `Dregg2.lean` at **+0 closure**:
it imports `PastaIpaFold`, which is already rooted, and nothing else.
-/
import Dregg2.Circuit.Emit.PastaIpaFold

namespace Dregg2.Bridge.MinaWrapSg

open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaCurve (curveB)
open Dregg2.Circuit.Emit.PastaCurveComplete
  (curveB3 rcbAddM Oproj projEqM projOnCurveM isInfM GpP)
open Dregg2.Circuit.Emit.PastaIpaFold (Pt msmHornerM ptsSumM)

set_option autoImplicit false

/-! ## §1 — The scalars: `2^k` of them, from `k` challenges, over `Nat`.

`PastaIPA.sVec` is the same recursion at an arbitrary `CommRing`, and `PastaIPA.sVec_eq_bPoly`
proves it is the coefficient vector of `b(X) = ∏_j (1 + c_j·X^{2^…})` — o1-labs'
`b_poly_coefficients`, the vector `SRS::verify` builds. `sVecN` is that recursion with `ZMod q`
multiplication written out as `Nat`, so the hot path carries no type-level `match` on a 255-bit
modulus. The weld pins the two against each other on the real block's 32,768 scalars. -/

/-- The s-vector over `Nat` mod `q`: `s ↦ s ++ (c · s)`, one doubling per challenge, head challenge
outermost — the order `PastaIPA.sVec` uses and the order the IPA produced them in. -/
def sVecN (q : Nat) : List Nat → List Nat
  | [] => [1]
  | c :: rest => let s := sVecN q rest; s ++ s.map (fun z => z * c % q)

/-- The bit budget. Every Pallas scalar is `< q < 2^255`, which is exactly
`MinaWrapSgCore.svec_fits_255` and exactly the hypothesis `msmHorner_eq_msmN` needs. It is not
slack: `q > 2^254`, so 255 is the smallest budget that is CORRECT for every element of `Fq`. -/
def NBITS : Nat := 255

/-! ## §2 — The fold. -/

/-- **`sgFold`** — `⟨s, G⟩` over Pallas, by ONE doubling chain shared across all `|G|` terms.

This is `PastaIpaFold.msmHornerM` at `(p, b3 = 15, 255)`, i.e. the evaluated mirror of `msmHorner`,
which `msmHorner_eq_msmN` proves equals `msmN`. At `k = 15` it is `255` doublings plus one complete
add per set bit — **4,161,791 complete adds against the 16,711,680** a naive `2^15` ladder pays,
and against the `2^15 − 1` scalar multiplications the generator FOLD (`msm_sVec_eq_fold`) would
pay. Folding is the right structural statement and the wrong evaluator; this is the lever. -/
def sgFold (chals : List Nat) (gens : List Pt) : Pt :=
  msmHornerM pN curveB3 NBITS (sVecN qN chals) gens

/-- **`sgSlice w i`** — the same MSM restricted to indices `[w·i, w·i + w)` of BOTH lists, cut at
the same `i`. This is the object `MinaWrapSgCore.ChunkOk i` states in the kernel. Compiled, the
slicing buys nothing — `List.foldl` is a tail loop and the whole `2^15` goes through `sgFold` in
one call — so it exists only so the compiled path can be compared to the kernel path chunk for
chunk, on the same 32 statements. -/
def sgSlice (w i : Nat) (scalars : List Nat) (gens : List Pt) : Pt :=
  msmHornerM pN curveB3 NBITS ((scalars.drop (w * i)).take w) ((gens.drop (w * i)).take w)

/-- The left-to-right sum of a list of Pallas points (the chunk-partial reassembly). -/
def sgSum (ps : List Pt) : Pt := ptsSumM pN curveB3 ps

/-! ## §3 — The fail-closed per-block checker.

Three outcomes, not two. A checker that answered `false` on a malformed tape would be
indistinguishable from one that had checked and refused, and a `2^14`-generator fold is a
well-formed answer **to the wrong index** — precisely the confusion `openingWireOk` refuses on the
`lr` side in `MinaWrapChallenges`. -/

/-- The shape gate: `k ≥ 1` canonical `Fq` challenges, exactly `2^k` generators, every generator a
real Pallas point that is not `O`, and a claimed `sg` that is a real Pallas point. -/
def sgWireOk (chals : List Nat) (gens : List Pt) (sg : Pt) : Bool :=
  chals.length != 0
    && gens.length == 2 ^ chals.length
    && chals.all (fun c => c < qN)
    && gens.all (fun P => projOnCurveM pN curveB P && !isInfM pN P)
    && projOnCurveM pN curveB sg

/-- **`sgVerdict`** — statement (A) of `SRS::verify`, per block.

* `some true` — the claimed `sg` IS `⟨s, G⟩` for these challenges and these generators;
* `some false` — it is not, and the fold was actually performed to find that out;
* `none` — the wire did not present a checkable shape, so **nothing was checked**. -/
def sgVerdict (chals : List Nat) (gens : List Pt) (sg : Pt) : Option Bool :=
  if sgWireOk chals gens sg then some (projEqM pN (sgFold chals gens) sg) else none

/-! ## §4 — Pins, on a four-point toy over the REAL Pallas generator.

Everything here reduces in milliseconds and is rooted. The `2^15`-scale pins, on real devnet block
539508, are in `Dregg2.Bridge.MinaWrapSgWeld` — which is not rooted, because it carries the
32,768-point fixture. -/

/- The scalar recursion agrees with `PastaIPA.sVec` at `PastaIpaFold` §5's own KAT numbers: two
challenges `[5, 7]` give the coefficient vector `[1, 7, 5, 35]` there, over `ℤ`, and here over
`Nat` mod `q`. Same object, two carriers. -/
#guard sVecN qN [5, 7] == [1, 7, 5, 35]
#guard (sVecN qN [5, 7]).length == 4
/- `k` challenges, `2^k` scalars — the compression the whole deferral rests on. -/
#guard (sVecN qN (List.replicate 15 1)).length == 32768
/- All-zero challenges select the FIRST generator alone, which is what `s = [1,0,…,0]` means. -/
#guard sVecN qN [0, 0] == [1, 0, 0, 0]

/- ⚑ The fold evaluates. `[1,0,0,0] · [G,G,G,G] = G`. -/
#guard projEqM pN (sgFold [0, 0] [GpP, GpP, GpP, GpP]) GpP
/- …and it is not selecting the first entry by accident: all-ones challenges give `[1,1,1,1]`, and
`⟨[1,1,1,1], [G,G,G,G]⟩` is `4G` — the same point the plain left-to-right sum produces. -/
#guard sVecN qN [1, 1] == [1, 1, 1, 1]
#guard projEqM pN (sgFold [1, 1] [GpP, GpP, GpP, GpP]) (sgSum [GpP, GpP, GpP, GpP])
/- …and `4G ≠ G`, so the two pins above are distinguishing a real difference. -/
#guard !projEqM pN (sgFold [1, 1] [GpP, GpP, GpP, GpP]) GpP

/- The slice is the same evaluator on a window: halves 0 and 1 of a 4-point MSM, re-added, are the
whole. -/
#guard projEqM pN
  (sgSum [sgSlice 2 0 (sVecN qN [1, 1]) [GpP, GpP, GpP, GpP],
          sgSlice 2 1 (sVecN qN [1, 1]) [GpP, GpP, GpP, GpP]])
  (sgFold [1, 1] [GpP, GpP, GpP, GpP])

/- ⚑ BOTH POLARITIES OF THE VERDICT, at toy scale. -/
#guard sgVerdict [0, 0] [GpP, GpP, GpP, GpP] GpP == some true
#guard sgVerdict [0, 0] [GpP, GpP, GpP, GpP] (sgSum [GpP, GpP]) == some false

/- …and the shape gate REFUSES rather than answering, in each of the six ways it can: no
challenges, the wrong generator COUNT, a non-canonical challenge, an off-curve generator, a
generator that is `O`, and an off-curve `sg`. A verdict that folded any of these would be a
plausible point for a different claim. -/
#guard (sgVerdict [] [] GpP).isNone
#guard (sgVerdict [0, 0] [GpP, GpP] GpP).isNone
#guard (sgVerdict [0, qN] [GpP, GpP, GpP, GpP] GpP).isNone
#guard (sgVerdict [0, 0] [GpP, GpP, GpP, (1, 1, 1)] GpP).isNone
#guard (sgVerdict [0, 0] [GpP, GpP, GpP, Oproj] GpP).isNone
#guard (sgVerdict [0, 0] [GpP, GpP, GpP, GpP] (1, 1, 1)).isNone
/- …and the gate ADMITS the shape it is supposed to, so the six refusals above are not a gate
that refuses everything. -/
#guard sgWireOk [0, 0] [GpP, GpP, GpP, GpP] GpP

/-! ## §5 — What one checkpoint's `sg` leg costs, in complete adds, at Mina's `k = 15`.

`PastaIpaFold` §4 counts the same numbers for the identities; these count them for the function a
checkpoint actually calls, so the cadence table in `docs/MINA-CHECKPOINT-CADENCE.md` has an object
to point at. -/

/-- Complete adds `sgFold` performs at `2^k` terms and `nbits` bits, at an average Hamming weight
of `nbits/2`: `nbits` doublings plus one add per set bit. -/
def sgFoldAdds (k nbits : Nat) : Nat := nbits + 2 ^ k * (nbits / 2)

/-- Complete adds a naive per-term double-and-add ladder performs: two per bit, per term. -/
def naiveAdds (k nbits : Nat) : Nat := 2 ^ k * (2 * nbits)

#guard sgFoldAdds 15 255 == 4161791
#guard naiveAdds 15 255 == 16711680
/- The shared doubling chain is worth ~4×; the generator fold, which saves exactly one scalar
multiplication out of `2^15`, is worth nothing. -/
#guard naiveAdds 15 255 / sgFoldAdds 15 255 == 4
/- Mina's wrap SRS is `k = 15`: 15 challenges, 32,768 generators, 32,768 scalars. -/
#guard 2 ^ 15 == 32768

/-! ## §6 — ⚑ WHAT CALLING THIS COSTS, with its evidence class.

A `#guard` cannot pin a clock, so the numbers live here. **Measured 2026-07-30 on an Apple M2 Max,
one core**, running this evaluator — `msmHornerM` over `rcbTraceM` — at full scale, 32,768 points
and 255 bit planes, 4,162,977 complete adds:

| | per complete add | one `sgFold` at `k = 15` | peak RSS |
|---|---|---|---|
| native (`leanc -O3`) | 8.44 µs | **35.1 s** | **18.8 MB** |
| interpreted (`lean --run`, = `#guard`) | 12.31 µs | 51.2 s | — |
| kernel `decide` (rung 5h, measured on hbox) | ~3.0 ms | ~3.5 h serial | ~28 GB |

Linear to within 0.5 % across n = 1024 / 4096 / 8192 / 32768. **kernel → native ≈ 359×**, and
**≈ 1,500× in memory** — the memory factor is the one that matters structurally, because ~28 GB
(and near 75 GB per chunk when rooted) is what made `lake build Dregg2` unable to finish and is why
`MinaWrapSg*` is allowlisted out of the root. That constraint does not exist on this path.

**Evidence class.** Measured on a *faithful standalone re-expression* of this evaluator — same
`rcbTraceM` op sequence (12 mulmods, 2 const-muls, 19 add/sub-mods, one 33-field allocation), same
fold, full scale — **not yet on this artifact.** `metatheory/MinaSgBench.lean` measures the
artifact; until it has run, treat 35.1 s as a prediction with a named falsifier
(`docs/MINA-CHECKPOINT-CADENCE.md` §5a).

**Where the time is NOT**, so nobody optimises the wrong half: the bit-plane traversal (`as.zip ps`
rebuilt on all 255 planes, 8.4 M `Nat.testBit`s) is **0.8 %** of the total, measured with all-zero
scalars. Hoisting the zip out of the plane loop was implemented and measured — 8.50 µs against
8.57 µs, inside the noise — and **deliberately not landed**, because it would have bought a
non-`rfl` mirror for nothing. The cost is the modular arithmetic: ~256 ns per 255-bit `Nat` mulmod,
allocation included. The real lever is `PastaMsmWindowed` (bucketed, 11-bit window: ~0.86 M adds
against 4.16 M, ~4.9×), which needs its own identity theorem and is not this file's job. -/

end Dregg2.Bridge.MinaWrapSg
