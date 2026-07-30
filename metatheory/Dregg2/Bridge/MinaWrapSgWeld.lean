/-
# Dregg2.Bridge.MinaWrapSgWeld — **rung 5h's statement, on the real block, through the COMPILED
checker: `sg == ⟨s, srs.g⟩` over all 32,768 generators, with the 32 chunk statements the kernel
takes ~3.5 h to `decide` reproduced as `#guard`s.**

## What this is

The INSTANCE differential for `Dregg2.Bridge.MinaWrapSg`. The checker is rooted and generic; this
file feeds it Mina devnet block 539508 — the block's own `srs.g` (`MinaWrapSrsG`, 32,768 real
Pallas generators), the block's own IPA challenges **derived from wire coordinates** by
`MinaWrapChallengesWeld`'s compiled sponge chain, and the block's own `opening.sg` — and pins the
answer in both polarities.

The chain, end to end, with no transcribed challenge anywhere in it:

```
block 539508's wire coordinates   (MinaWrapChallengesWeld.B539508: vk, prev_comm, public_comm,
      │                            w_comm, z_comm, t_comm, cip_shifted, lr, delta)
      ├─ wrapPhase1Of ──────────▶  β, γ, α′, ζ′, fq_digest              [compiled]
      ├─ ipaChallengesOf ───────▶  t, 15 IPA PRECHALLENGES, c′          [compiled]
      ├─ endoMap ENDO_R ────────▶  the 15 field challenges  = CHAL      [compiled, §1]
      ├─ sVecN ─────────────────▶  32,768 scalars           = SVEC      [compiled, §2]
      └─ sgFold over SRS_G ─────▶  ⟨s, srs.g⟩               = sg        [compiled, §3]
```

## ⚑ Why this is a differential and not a proof, and what the kernel still holds

`#guard` uses Lean's **untrusted evaluator**; it is not a proof that the expression is `true`. The
split is deliberate and is this tree's rule: **the kernel proves the CHECKER, a differential checks
the INSTANCE.** The checker's theorem is `PastaIpaFold.msmHorner_eq_msmN` — the bit-plane scan
computes the MSM, at an arbitrary `AddCommGroup`, with the bit budget as a real hypothesis (§7
below breaks it on purpose). Nothing here weakens rung 5h: `MinaWrapSgCore` + `MinaWrapSgChunk0..3`
still say the same thing in the kernel, over the same `msmHornerM`, and §4 below reproduces their
32 statements one for one so the two paths are compared on the same object rather than trusted
separately.

## ⚑ Which object this binds

The CONTENTS: that the block's `sg` really is the MSM of the derived s-vector against the real
`srs.g`. It does **not** bind a proof object, and the `5h-AIR` rungs
(`PastaMsmBound`/`PastaMsmOnCurve`), which force an emitted row's source to be `srs.g` at the index
the manifest names, bind no contents. Neither subsumes the other.

## Why this file is NOT rooted

It carries `MinaWrapSrsG` — 32,768 generators, 5.4 MB of Lean — into whatever imports it. That is
the same reason the `MinaWrapSg*` kernel family is allowlisted out of `Dregg2.lean`, and the same
split `MinaWrapChallengesWeld` documents for the challenge derivation. The runner is
`scripts/run-mina-sg-compiled.sh`; **these `#guard`s run nowhere else.**

## Cost, and how to read the wall clock — see §9. Read it before quoting a number from this file.
-/
import Dregg2.Bridge.MinaWrapSg
import Dregg2.Bridge.MinaWrapChallengesWeld
import Dregg2.Circuit.Emit.MinaWrapSrsG
import Dregg2.Circuit.Emit.MinaWrapSgParts

namespace Dregg2.Bridge.MinaWrapSgWeld

open Dregg2.Bridge.MinaWrapSg (sVecN NBITS sgFold sgSlice sgSum sgWireOk sgVerdict)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaCurveComplete (curveB3 Oproj projEqM)
open Dregg2.Circuit.Emit.PastaIpaFold (Pt msmHornerM)
open Dregg2.Circuit.Emit.KimchiVerify (endoMap)
open Dregg2.Circuit.Emit.MinaRealBlockTranscript (ENDO_R)
open Dregg2.Circuit.Emit.MinaWrapOpeningGate (CHAL CHAL_F IPA_PRECHALS)
open Dregg2.Circuit.Emit.MinaWrapSrsG (SRS_G)
open Dregg2.Circuit.Emit.MinaWrapSgParts (PARTS SG)

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## §1 — The 15 challenges, DERIVED, not transcribed.

`MinaWrapChallengesWeld.ic` is the output of a compiled function of block 539508's wire
coordinates. `endoMap ENDO_R` is the `ScalarChallenge::to_field` expansion — the same map
`MinaWrapOpeningGate.derived_ipa_challenges` proves in the kernel carries `IPA_PRECHALS` to
`CHAL_F`. So `CHALS_W` below is a function of the block's bytes all the way down, and `CHAL` is
only the thing it is CHECKED against. -/

/-- The block's 15 IPA challenges, as canonical `Fq` values, from the wire. -/
def CHALS_W : List Nat :=
  (Dregg2.Bridge.MinaWrapChallengesWeld.ic.prechals.map (fun c => endoMap ENDO_R c)).map ZMod.val

/- ⚑ **THE FIRST LINK.** The wire-derived challenges are exactly the 15 literals rung 5f's kernel
theorems and rung 5h's 32,768 scalars are stated over. -/
#guard CHALS_W == CHAL
#guard CHALS_W.length == 15
/- …and the prechallenges they came from are the block's, not a re-transcription. -/
#guard Dregg2.Bridge.MinaWrapChallengesWeld.ic.prechals == IPA_PRECHALS

/-! ## §2 — The 32,768 scalars, from those 15.

This is `PastaIPA.deferral_compression` as an actual object: 15 field elements determine the whole
terminal MSM's scalar vector, which is why Pickles may defer it. -/

/-- The s-vector of the block's own challenges. -/
def SVEC_W : List Nat := sVecN qN CHALS_W

#guard SVEC_W.length == 32768
#guard SVEC_W.all (fun a => a < 2 ^ NBITS)

/- ⚑ **THE SECOND LINK, and it is the one that says the two evaluators share an object.** The
`Nat`-mod-`q` recursion produces exactly `(PastaIPA.sVec CHAL_F).map ZMod.val` — which IS
`MinaWrapSgCore.SVEC`, the 32,768 scalars the kernel's 32 chunk theorems consumed. -/
#guard SVEC_W == (Dregg2.Circuit.Emit.PastaIPA.sVec CHAL_F).map ZMod.val

/-! ## §3 — ⚑⚑ THE RESULT: the terminal MSM, compiled, over all 32,768 real generators. -/

/- The block's shape is ADMITTED — 15 canonical challenges, 2^15 generators every one of which is a
real Pallas point and not `O`, and an `sg` that is a real Pallas point. This is the compiled
restatement of `MinaWrapSgCore.srs_g_on_curve`, and it is what makes §8's refusals mean something:
the gate is not refusing everything. -/
#guard sgWireOk CHALS_W SRS_G SG
#guard SRS_G.length == 32768
#guard PARTS.length == 32

/- ⚑⚑ **STATEMENT (A) OF `SRS::verify`, ON MINA DEVNET BLOCK 539508, IN ONE COMPILED CALL.**
`sg == ⟨s, srs.g⟩`. The kernel says this in 32 pieces because `whnf` blows its C stack past 512
terms; compiled, `List.foldl` is a tail loop and there is no chunking at all. -/
#guard sgVerdict CHALS_W SRS_G SG == some true

/-! ## §4 — The 32 chunk statements the kernel `decide`s, as `#guard`s.

`MinaWrapSgChunk0..3` prove exactly these — "the MSM over generator indices `[1024k, 1024k+1024)`
is the partial arkworks' own `msm_bigint` produced for that same slice" — in ~3.5 h of serial
kernel. The index is in the statement on both sides (`sgSlice 1024 k` cuts BOTH lists at the same
`k`), so a partial at the wrong offset is caught; a group sum forgets its order, and these do not.

The kernel assembles each 1024 as two 512-halves because it must; this takes the 1024 directly.
Same statement, same partials, same generators. -/

/-- Chunk `k` of the real block, compiled. -/
def chunkOkC (k : Nat) : Bool :=
  projEqM pN (sgSlice 1024 k SVEC_W SRS_G) (PARTS.getD k Oproj)

/- ⚑⚑ **ALL 32.** -/
#guard (List.range 32).all chunkOkC

/- …and the 32 partials re-sum to `sg` (`MinaWrapSgCore.parts_sum_is_sg`, compiled). -/
#guard projEqM pN (sgSum PARTS) SG
/- …with the same anti-vacuity control that theorem carries: duplicate one partial and it breaks. -/
#guard !projEqM pN (sgSum (PARTS.set 7 (PARTS.getD 8 Oproj))) SG

/-! ## §5 — Value tampers, at chunk-0 scale.

Chunk 0 is a real statement rung 5h proves (`MinaWrapSgChunk0.chunk_00`), and moving it costs 1/32
of a full fold with the same discriminating power. The one control that genuinely needs the full
`2^15` is in §6, and it is there for a reason. -/

/-- Chunk 0 of the real block against arkworks' own partial for indices `[0, 1024)`. -/
def chunk0Ok (scalars : List Nat) (gens : List Pt) : Bool :=
  projEqM pN (sgSlice 1024 0 scalars gens) (PARTS.getD 0 Oproj)

/- The positive pole, so every refusal below is a refusal OF something that otherwise passes. -/
#guard chunk0Ok SVEC_W SRS_G

/- (a) ONE generator replaced by ANOTHER REAL generator — the shape stays perfectly valid, so this
is a genuine disagreement and not a shape refusal. -/
#guard !chunk0Ok SVEC_W (SRS_G.set 123 (SRS_G.getD 124 Oproj))
/- (b) chunk 0's generators REVERSED. A group sum forgets its order; an index-matched MSM does not,
and this is what would go unnoticed if the scalars were not really being paired with generators. -/
#guard !chunk0Ok SVEC_W ((SRS_G.take 1024).reverse ++ SRS_G.drop 1024)
/- (c) the WRONG SLICE: chunk 0's scalars against the generators starting at index 1024. An
off-by-one-chunk offset is the exact error a per-chunk theorem without an index in its statement
cannot see. -/
#guard !chunk0Ok SVEC_W (SRS_G.drop 1024)
/- (d) challenge 14 moved. `c_j` multiplies scalar `i` iff bit `14−j` of `i` is set, so `c_14` is
bit 0 — it moves every odd-indexed scalar, chunk 0 included. **The 15 challenges are READ.** -/
#guard !chunk0Ok (sVecN qN (CHALS_W.set 14 ((CHALS_W.getD 14 0 + 1) % qN))) SRS_G
/- (e) challenge 5 — bit 9, the highest bit that varies inside chunk 0. -/
#guard !chunk0Ok (sVecN qN (CHALS_W.set 5 ((CHALS_W.getD 5 0 + 1) % qN))) SRS_G

/-! ## §6 — ⚑ The control that needs the WHOLE `2^15`, and why a cheap prefix is not a checkpoint.

`c_0` multiplies scalar `i` iff bit 14 of `i` is set: it touches **only** indices `≥ 2^14` and is
invisible to every one of chunks 0–15. A checker that folded a prefix — or any single chunk —
would accept a proof carrying a forged first challenge. -/

/- Chunk 0 cannot see it, and does not pretend to: -/
#guard chunk0Ok (sVecN qN (CHALS_W.set 0 ((CHALS_W.getD 0 0 + 1) % qN))) SRS_G
/- ⚑ …and the full fold does. -/
#guard sgVerdict (CHALS_W.set 0 ((CHALS_W.getD 0 0 + 1) % qN)) SRS_G SG == some false

/-! ## §7 — The bit budget is load-bearing, and this control is not vacuous.

`msmHorner_eq_msmN` needs `∀ a ∈ as, a < 2^nbits`. `q > 2^254`, so 255 is the smallest budget that
is CORRECT for every `Fq` element — but almost no real scalar reaches bit 254 (the interval
`[2^254, q)` is ~`2^-125` of the field), so a 254-bit scan would agree by luck and prove nothing.
253 is the sharp cut: about half the scalars set bit 253, and the guard below CHECKS that some
scalar in chunk 0 does before asking the scan to be wrong. -/

#guard (SVEC_W.take 1024).any (fun a => a.testBit 253)
#guard !projEqM pN (msmHornerM pN curveB3 253 (SVEC_W.take 1024) (SRS_G.take 1024))
                   (PARTS.getD 0 Oproj)

/-! ## §8 — Shape refusals: `none`, not `false`, and no fold is performed.

Each of these fails `sgWireOk` before any group operation, so they are free. They are also the
outcomes that matter most: a `2^14`-generator fold is a well-formed answer to a proof of a
DIFFERENT index, and returning `false` for it would be indistinguishable from having checked. -/

/- Half the SRS against 15 challenges. -/
#guard (sgVerdict CHALS_W (SRS_G.take 16384) SG).isNone
/- 14 challenges against 32,768 generators. -/
#guard (sgVerdict (CHALS_W.take 14) SRS_G SG).isNone
/- A non-canonical challenge. -/
#guard (sgVerdict (CHALS_W.set 0 qN) SRS_G SG).isNone
/- A generator that is not a Pallas point. -/
#guard (sgVerdict CHALS_W (SRS_G.set 0 (1, 1, 1)) SG).isNone
/- A generator that is the point at infinity — `O` is on the curve, so only the explicit
non-degeneracy clause catches it. -/
#guard (sgVerdict CHALS_W (SRS_G.set 0 Oproj) SG).isNone
/- A claimed `sg` that is not a Pallas point. -/
#guard (sgVerdict CHALS_W SRS_G (1, 1, 1)).isNone

/-! ## §9 — ⚑ COST ACCOUNTING. Read this before quoting this file's wall clock.

`#guard` runs Lean's untrusted evaluator, which is the **interpreter** — this package does not set
`precompileModules`, so imported `.olean` IR is interpreted rather than executed as native code.
**The wall time of this module is therefore an UPPER BOUND on the compiled cost, not the compiled
cost.** The native number comes from `lean_exe mina_sg_bench`, which runs the identical `sgFold` on
the identical data through `leanc`.

The module evaluates, in units of one full `2^15`-term fold (`sgFoldAdds 15 255 = 4,161,791`
complete adds):

| § | what | full-fold equivalents |
|---|---|---|
| 3 | `sgVerdict` on the real block | 1.00 |
| 4 | the 32 chunk statements | 1.00 |
| 5 | six chunk-0-scale evaluations | 0.19 |
| 6 | the `c_0` control, full scale | 1.00 |
| 7 | one 253-bit chunk-0 scan | 0.03 |
| 8 | six shape refusals | 0.00 (no fold performed) |
| | **total** | **≈ 3.2** |

So: (module wall time − `MinaWrapSrsG` elaboration − olean load) / 3.2 ≈ the interpreted cost of
one checkpoint's `sg` leg. Divide the bench's number, not this one, into the cadence table.
-/

end Dregg2.Bridge.MinaWrapSgWeld
