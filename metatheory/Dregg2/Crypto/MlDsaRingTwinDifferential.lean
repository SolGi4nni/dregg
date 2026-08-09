/-
# `MlDsaRing` twin differentials — the seam evidence the aliases made expressible.

`Dregg2.Crypto.MlDsaRing` routes the ML-DSA ring ops to hand-written `Array UInt32` twins through
`@[implemented_by]`. That attribute carries NO proof obligation: the kernel never checks the twin
against the def, and a wrong twin silently corrupts FIPS 204 sign and verify with no theorem
catching it. This module is the evidence that it does not.

## Why this module could not have existed yesterday

`@[implemented_by]` is honoured by the COMPILED evaluator, and `#guard` / `native_decide` / `#eval`
all run on that evaluator. Until 2026-08-09 the five attributes sat on the pure defs themselves, so
`fastNtt x == ntt x` compared `fastNtt` with `fastNtt` and printed `true` for ANY twin. The seams
were not merely untested — they were **untestable**, and the obvious fix was a permanently green
tautology, which is worse than nothing because it reads as closure. Moving each attribute onto a
`…Fast` alias (`MlDsaRing`'s "THE ROUTED ALIASES" note) left the pure defs unrouted; every
differential below is a genuine fast-vs-pure comparison that can go RED.

## Why the corpus is new

The corpus that shipped with those twins is `sampleA`/`sampleB`, both sparse. Measured over all 256
lanes — and re-asserted here as `oldCorpus_max_product_is_4` / `oldCorpus_max_sum_is_7` — the largest
coefficient product is **4** and the largest coefficient sum is **7**, against a `2³²` truncation
threshold and a `q = 8 380 417` reduction threshold. The twins' own docstring names 32-bit
truncation as THE correctness crux; a corpus whose largest product is 4 cannot see it.

## The shape of the evidence: every differential is shown to DISTINGUISH

A differential that cannot fail is not a differential. Each seam below therefore comes with a
CONSTRUCTED wrong twin and a pair of theorems: the wrong twin **passes** the old evidence and
**fails** the new. Nothing here rests on a claim that a corpus is adequate — the falsifiers are in
the environment and the build reds if one of them stops being caught.

  * `fastPointwiseMulTrunc` — `mulQu` written the naive 32-bit way, the exact port `MlDsaRing`'s
    docstring warns against. Passes on `sampleA`/`sampleB`; caught on the full-range corpus.
  * `fastAddPolyUnreduced` — `addQu` with its `% qU` DELETED. Same: passes on the old corpus,
    caught on the new one.
  * `nttPerm` / `inttPerm` — the permuted twin PAIR. Pointwise multiplication is
    permutation-equivariant, so post-composing the forward transform with `List.reverse` and
    pre-composing the inverse with the same involution leaves both the negacyclic product and the
    round trip unchanged. It satisfies BOTH composite differentials in `MlDsaRing` and differs from
    the routed twin — the falsifier that motivated this whole module. It is caught only by a DIRECT
    `fastNtt x == ntt x`, which is exactly the check the alias move made expressible.

Everything is `native_decide` + `#assert_compiled`: these are 256-lane `Std.Range.forIn` loops over
`Array Nat`, which do not kernel-reduce (`MlDsaRing`'s `zeta_primitive_512th_root` note records the
same wall), so the honest pin is the compiled-evaluation one. `#assert_compiled` re-runs each claim
through the evaluator, so a differential that stops holding cannot stay green.
-/
import Dregg2.Crypto.MlDsaRing
import Dregg2.Tactics

namespace Dregg2.Crypto.MlDsaRingTwinDifferential

open Dregg2.Crypto.MlDsaRing

/-! ## 1. The full-range corpus.

Every one of the 256 lanes carries a large canonical residue, so the reduction and the widening the
twins perform actually FIRE. `(i * seed) % q < q`, hence `q - 1 - (i * seed) % q ∈ [0, q-1]` — no
`Nat` truncation in the construction, and every coefficient is canonical. -/

/-- A dense full-range test polynomial: lane `i` carries `q − 1 − (i·seed mod q)`. -/
def hiPoly (seed : Nat) : Poly := Array.ofFn (n := 256) (fun i => q - 1 - (i.val * seed) % q)

/-- Full-range corpus, first operand. -/
def sampleHiA : Poly := hiPoly 7919
/-- Full-range corpus, second operand (a different stride, so the two disagree per-lane in BOTH
directions — see `hiCorpus_sub_borrow_fires`). -/
def sampleHiB : Poly := hiPoly 104729

/-- The corpus is CANONICAL: every coefficient is a legal `R_q` residue. Without this the
differentials would be comparing behaviour on inputs neither implementation promises anything
about, and a disagreement would prove nothing. -/
theorem hiCorpus_is_canonical :
    ((List.range 256).all (fun i => sampleHiA[i]! < q && sampleHiB[i]! < q)) = true := by
  native_decide
#assert_compiled hiCorpus_is_canonical

/-! ## 2. Corpus adequacy — the branches the twins take actually FIRE here, and did not before. -/

/-- ADEQUACY (`addPoly` seam): some lane sums to `≥ q`, so `addQu`'s `% qU` reduction is exercised.
This is the fact the old corpus lacks. -/
theorem hiCorpus_add_reduction_fires :
    ((List.range 256).any (fun i => sampleHiA[i]! + sampleHiB[i]! ≥ q)) = true := by
  native_decide
#assert_compiled hiCorpus_add_reduction_fires

/-- ADEQUACY (`subPoly` seam): some lane has `a < b`, so `subQu`'s `+ qU` borrow is exercised. -/
theorem hiCorpus_sub_borrow_fires :
    ((List.range 256).any (fun i => sampleHiA[i]! < sampleHiB[i]!)) = true := by
  native_decide
#assert_compiled hiCorpus_sub_borrow_fires

/-- ADEQUACY (`pointwiseMul` seam, THE crux): some lane's coefficient product exceeds `2³²`, so a
32-bit multiply would TRUNCATE. This is the exact fault `mulQu` widens to `UInt64` to avoid, and the
old corpus (max product 4) could not reach it. -/
theorem hiCorpus_mul_exceeds_uint32 :
    ((List.range 256).any (fun i => sampleHiA[i]! * sampleHiB[i]! ≥ 4294967296)) = true := by
  native_decide
#assert_compiled hiCorpus_mul_exceeds_uint32

/-- The OLD corpus's largest coefficient product is **4** — against the `2³²` threshold the twin's
own docstring names as the correctness crux. Named so that a future edit which weakens the corpus
back toward this reds instead of quietly re-blinding the differentials. -/
theorem oldCorpus_max_product_is_4 :
    ((List.range 256).foldl (fun m i => max m (sampleA[i]! * sampleB[i]!)) 0) = 4 := by
  native_decide
#assert_compiled oldCorpus_max_product_is_4

/-- The OLD corpus's largest coefficient sum is **7** — against `q = 8 380 417`. So `addQu`'s
reduction never fires there. -/
theorem oldCorpus_max_sum_is_7 :
    ((List.range 256).foldl (fun m i => max m (sampleA[i]! + sampleB[i]!)) 0) = 7 := by
  native_decide
#assert_compiled oldCorpus_max_sum_is_7

/-! ## 3. The five DIRECT seam differentials — twin vs PURE def, both unrouted.

Each statement is substantive: `fastAddPoly` and `addPoly` are different definitions over different
representations, and neither is `@[implemented_by]`-routed any more (the attribute lives on
`addPolyFast`). So the compiled evaluator really runs both bodies and compares. Before the alias
move the `ntt`/`intt` pair of these could not be written at all. -/

/-- `fastAddPoly` agrees with the pure `addPoly`, on a corpus where the reduction fires. -/
theorem fastAddPoly_matches_pure :
    (fastAddPoly sampleHiA sampleHiB == addPoly sampleHiA sampleHiB) = true := by native_decide
#assert_compiled fastAddPoly_matches_pure

/-- `fastSubPoly` agrees with the pure `subPoly`, on a corpus where the borrow fires. -/
theorem fastSubPoly_matches_pure :
    (fastSubPoly sampleHiA sampleHiB == subPoly sampleHiA sampleHiB) = true := by native_decide
#assert_compiled fastSubPoly_matches_pure

/-- `fastPointwiseMul` agrees with the pure `pointwiseMul`, on a corpus whose products exceed `2³²`
— the case a 32-bit multiply truncates. -/
theorem fastPointwiseMul_matches_pure :
    (fastPointwiseMul sampleHiA sampleHiB == pointwiseMul sampleHiA sampleHiB) = true := by
  native_decide
#assert_compiled fastPointwiseMul_matches_pure

/-- ⚑ `fastNtt` agrees with the pure `ntt`, POINTWISE on the full transform. This is the check that
did not exist: it is the one a permuted twin cannot survive (`nttPerm_is_caught_by_the_direct_one`),
and writing it was impossible while `ntt` itself carried the attribute. -/
theorem fastNtt_matches_pure : (fastNtt sampleHiA == ntt sampleHiA) = true := by native_decide
#assert_compiled fastNtt_matches_pure

/-- ⚑ `fastIntt` agrees with the pure `intt`, pointwise. See `fastNtt_matches_pure`. -/
theorem fastIntt_matches_pure : (fastIntt sampleHiA == intt sampleHiA) = true := by native_decide
#assert_compiled fastIntt_matches_pure

/-- The same two, on the ORIGINAL corpus — kept because `sampleA` has a high-degree term the dense
corpus's smooth stride does not, so the two inputs exercise different wrap behaviour. -/
theorem fastNtt_matches_pure_oldCorpus : (fastNtt sampleA == ntt sampleA) = true := by native_decide
#assert_compiled fastNtt_matches_pure_oldCorpus

/-- See `fastNtt_matches_pure_oldCorpus`. -/
theorem fastIntt_matches_pure_oldCorpus :
    (fastIntt sampleA == intt sampleA) = true := by native_decide
#assert_compiled fastIntt_matches_pure_oldCorpus

/-! ## 4. FALSIFIERS — each differential is shown to be able to FAIL.

These are DELIBERATE wrong twins. Nothing routes them; they exist so that "the differential holds"
is a fact with content. Do not delete one to get green — a falsifier that stops being caught is the
signal, not the noise. -/

/-! ### 4a. The truncating 32-bit multiply — the naive port. -/

/-- `mulQu` written the WRONG way: a bare 32-bit product, which truncates for coefficients near `q`.
`MlDsaRing`'s docstring names this exact fault as the reason `mulQu` widens to `UInt64`. -/
def mulQuTrunc (a b : UInt32) : UInt32 := (a * b) % qU

/-- `fastPointwiseMul` built on the truncating multiply. -/
def fastPointwiseMulTrunc (a b : Poly) : Poly := Id.run do
  let au := toU32 a; let bu := toU32 b
  let mut c : Array UInt32 := Array.replicate 256 0
  for i in [0:256] do
    c := c.set! i (mulQuTrunc au[i]! bu[i]!)
  return toNatA c

/-- ⚑ The truncating twin PASSES on the original corpus. This is what "the differential written for
this twin is degenerate" means, stated as a theorem rather than as prose. -/
theorem truncating_mul_survives_the_old_corpus :
    (fastPointwiseMulTrunc sampleA sampleB == pointwiseMul sampleA sampleB) = true := by
  native_decide
#assert_compiled truncating_mul_survives_the_old_corpus

/-- ⚑ …and is CAUGHT on the full-range corpus. Together with the previous theorem this is the proof
that `fastPointwiseMul_matches_pure` can distinguish: a wrong twin exists, and this corpus separates
it from the right one while the old corpus does not. -/
theorem truncating_mul_is_caught_on_the_hi_corpus :
    (fastPointwiseMulTrunc sampleHiA sampleHiB == pointwiseMul sampleHiA sampleHiB) = false := by
  native_decide
#assert_compiled truncating_mul_is_caught_on_the_hi_corpus

/-! ### 4b. The add with its reduction deleted. -/

/-- `fastAddPoly` with `addQu`'s `% qU` DELETED — the coefficient escapes `[0,q)`. -/
def fastAddPolyUnreduced (a b : Poly) : Poly := Id.run do
  let au := toU32 a; let bu := toU32 b
  let mut c : Array UInt32 := Array.replicate 256 0
  for i in [0:256] do
    c := c.set! i (au[i]! + bu[i]!)
  return toNatA c

/-- ⚑ Deleting the modular reduction entirely PASSES on the original corpus (max sum 7 < q). -/
theorem unreduced_add_survives_the_old_corpus :
    (fastAddPolyUnreduced sampleA sampleB == addPoly sampleA sampleB) = true := by native_decide
#assert_compiled unreduced_add_survives_the_old_corpus

/-- ⚑ …and is CAUGHT on the full-range corpus. The distinguishing proof for
`fastAddPoly_matches_pure`. -/
theorem unreduced_add_is_caught_on_the_hi_corpus :
    (fastAddPolyUnreduced sampleHiA sampleHiB == addPoly sampleHiA sampleHiB) = false := by
  native_decide
#assert_compiled unreduced_add_is_caught_on_the_hi_corpus

/-! ### 4c. ⚑ The permuted twin PAIR — the falsifier the alias move exists for.

Pointwise multiplication is permutation-equivariant, so conjugating the transform pair by an
involution leaves the negacyclic product and the round trip invariant. Both composite differentials
in `MlDsaRing` are satisfied; the pair is not the spec; and on the live FIPS 204 sign/verify path
`ntt` is reached from `dregg_fips204_verify_real`. What catches it is a DIRECT comparison, which is
precisely what could not be written while `ntt` carried the attribute. -/

/-- Forward transform, post-composed with `List.reverse`. NOT the spec. -/
def nttPerm (w : Poly) : Poly := (fastNtt w).reverse
/-- Inverse transform, pre-composed with the same involution. NOT the spec. -/
def inttPerm (w : Poly) : Poly := fastIntt w.reverse

/-- ⚑ The permuted pair satisfies the WHOLE-PIPELINE differential (`MlDsaRing`'s composite: the fast
NTT multiply equals the pure `schoolbookMul`). -/
theorem nttPerm_survives_the_composite_product :
    (inttPerm (fastPointwiseMul (nttPerm sampleA) (nttPerm sampleB)) == schoolbookMul sampleA sampleB)
      = true := by native_decide
#assert_compiled nttPerm_survives_the_composite_product

/-- ⚑ …and the ROUND-TRIP differential (`intt ∘ ntt = id`). Those two were the only tests in the
tree that touched `ntt`/`intt`. -/
theorem nttPerm_survives_the_round_trip :
    (inttPerm (nttPerm sampleA) == sampleA) = true := by native_decide
#assert_compiled nttPerm_survives_the_round_trip

/-- ⚑ …and the DIRECT differential catches it. This theorem plus the two above is the proof that
`fastNtt_matches_pure` distinguishes something no pre-existing check in the tree could: a twin that
passes every test that existed and is still wrong. -/
theorem nttPerm_is_caught_by_the_direct_one :
    (nttPerm sampleA == ntt sampleA) = false := by native_decide
#assert_compiled nttPerm_is_caught_by_the_direct_one

/-- The inverse half of the same falsifier, likewise caught only by the direct comparison. -/
theorem inttPerm_is_caught_by_the_direct_one :
    (inttPerm sampleA == intt sampleA) = false := by native_decide
#assert_compiled inttPerm_is_caught_by_the_direct_one

end Dregg2.Crypto.MlDsaRingTwinDifferential
