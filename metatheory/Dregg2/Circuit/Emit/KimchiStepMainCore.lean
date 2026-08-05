/-
`KimchiStepMain` §1–§11 — THE EMISSION PROPER: the shape, the variable space, the row-schedule
primitives, the eight sub-circuits R1–R8, the arithmetic compiler, the whole assembly, the rungs
and the committed shape. Definitions only — every `#guard` about them lives in `…Pins01`–`…Pins13`,
so editing a rung re-elaborates THIS file (seconds) and then the pin modules IN PARALLEL.
-/
import Dregg2.Circuit.Emit.KimchiPlacement
import Dregg2.Circuit.Emit.KimchiGadgets
import Dregg2.Circuit.Emit.WitnessBuilder
import Dregg2.Circuit.Emit.KimchiCustomGates
import Dregg2.Circuit.Emit.KimchiRenderPoseidon
import Dregg2.Circuit.Emit.KimchiRenderVarBaseMul
import Dregg2.Circuit.Emit.KimchiRenderCompleteAdd
import Dregg2.Circuit.Emit.KimchiRenderEndoMul
import Dregg2.Circuit.Emit.KimchiRenderEndoMulScalar
import Dregg2.Circuit.Emit.KimchiRenderPublicInput
import Dregg2.Circuit.Emit.KimchiComposeStepFragment
import Dregg2.Circuit.Emit.KimchiVerify
import Dregg2.Circuit.Emit.PastaCurve
import Dregg2.Circuit.Emit.PastaPoseidon
import Dregg2.Bridge.MinaWrapFtEval0
import Dregg2.Bridge.TickShifts
import Dregg2.Bridge.MinaStepPrevCommitments
import Dregg2.Circuit.Emit.KimchiStepMainField

namespace Dregg2.Circuit.Emit.KimchiStepMain

open Dregg2.Circuit.Emit.KimchiTarget (KGateType K_PERMUTS)
open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.WitnessBuilder
  (VarEnv GateWitness gridAt envIndex envLookupAt gateVarWitnessAt compose)
open Dregg2.Circuit.Emit.KimchiRenderVarBaseMul (fAdd fMul)
open Dregg2.Circuit.Emit.KimchiRenderCompleteAdd (completeAddWitness)
open Dregg2.Circuit.Emit.KimchiCustomGates (poseidonRowCoeffs)
open Dregg2.Circuit.Emit.KimchiRenderEndoMulScalar (cFuncFp dFuncFp)
open Dregg2.Circuit.Emit.KimchiComposeStepFragment
  (TermData EndoBlock runVbm endoStep dblA addA onCurveA jOf jDbl jAdd jNeg)
open Dregg2.Circuit.Emit.KimchiVerify
  (varBaseMulConstraints completeAddConstraints endoMulConstraints endomulScalarConstraints)
open Dregg2.Circuit.Emit.PastaCurve (jacEqM scMulM)
open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.PastaPoseidon (rcsN)
open Dregg2.Bridge.MinaWrapFtEval0 (IDX_Z IDX_SEL IDX_W IDX_COEFF IDX_S)

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## §1 — the shape. -/

/-- The assembly's size. Every field is a quantity upstream fixes; the committed instance in §10
sets them against the `verify_one` line items in the header. -/
structure StepShape where
  /-- transcript absorb blocks; each swallows TWO field elements (`rate = 2`). -/
  absorbs : Nat
  /-- squeezed scalar challenges (one permutation each). -/
  chals : Nat
  /-- `EndoMulScalar` rows per challenge; each eats 8 crumbs = 16 bits (`bits_per_row = 16`). -/
  emsRows : Nat
  /-- `var_base_mul` terms in the commitment MSM — the packed Wrap STATEMENT's word count. ⚑ There
  is no companion `msmChunks` field: the chunk count is PER WORD (§1b, `msmChunksAt`), because
  `Spec.pack` gives each statement word its own bit width and a uniform one emitted twenty-five
  chunks of leading zeros on every challenge-shaped word. -/
  msmTerms : Nat
  /-- `Scalar_challenge.endo` scalar multiplications in the IPA/commitment fold. -/
  ipaRounds : Nat
  /-- 4-bit `endo_mul` blocks per round (`32` is upstream's 128-bit `endo`). -/
  ipaBlocks : Nat
  /-- rounds of the deferred `b(ζ)` product (`Step_bp_vec = N16`). -/
  bRounds : Nat
  /-- evaluation columns folded by `combined_inner_product`
  (`NUM_COMMITMENTS_WITHOUT_DEGREE_BOUND = N45`, + `sg_old` padding = 47). -/
  cipEvals : Nat
  /-- ⚑ `t_comm`'s quotient chunks this shape absorbs (`N_TCOMM = 7` upstream). A FIELD since the
  R1 interleaving: `absorbs` is now DERIVED from the schedule, so sizing `t_comm` off `absorbs`
  would be circular. -/
  tComms : Nat
  /-- the public-input width (`PRIMARY_LEN`). -/
  pubWords : Nat
  deriving Repr, Inhabited, DecidableEq

-- ⚑ **`StepShape.blocks` IS GONE (2026-08-03).** It was `absorbs + chals` — one permutation per
-- absorb block PLUS one per squeeze — which is not what Mina's lazy sponge performs. The
-- permutation count is `tBlocks` (§1c′), DERIVED from the op tape, and it is smaller.
/-- Bits a challenge carries (`emsRows` rows × 8 crumbs × 2 bits). -/
def StepShape.chalBits (s : StepShape) : Nat := 16 * s.emsRows
/-! ⚑ **RETIRED 2026-08-03 (§21).** There was a `StepShape.msmChal i = i % chals` here — "which
challenge MSM term `i` consumes". `multiscale_known` consumes NO challenge: term `i`'s scalar is Wrap
statement WORD `i` (`step_verifier.ml:543-544,1236-1251`), and the round-robin was a placeholder that
made a 255-bit ladder run over a structurally `< 2¹²⁸` value. The wiring is `stmtVar` (§2c); the old
expression survives only inside §12m's red control, where it is the thing being refuted. -/
/-- Which challenge IPA round `r` consumes. -/
def StepShape.ipaChal (s : StepShape) (r : Nat) : Nat := (s.msmTerms + r) % s.chals

/-! ### ⚑⚑ §1b — **`Spec.pack`'s PER-WORD SCALAR WIDTHS.**

`multiscale_known`'s scalars are NOT one width and never were. They are the previous proof's PACKED
WRAP STATEMENT — `multiscale_known (Array.mapi public_input ~f:(fun i x -> (x, lagrange_commitment
~domain srs i)))` (`step_verifier.ml:543-544`) over `public_input = Spec.pack (module Impl)
(Types.Wrap.Statement.In_circuit.spec …) (… to_data statement)` (`:1236-1251`) — and `Spec.pack`
carries a width PER BASIC (`spec.ml:305-395`, `pack_basic`):

    Unit                  → no word at all
    Field                 → `` `Field x ``   ⚠ NOT `Packed_bits`             255
    Bool                  → `Packed_bits (x, 1)`                               1
    Digest                → `Packed_bits (x, Field.size_in_bits)`            255
    Challenge             → `Packed_bits (x, Challenge.length)`              128
    Branch_data           → `Packed_bits (…, Branch_data.length_in_bits)`     10
    Bulletproof_challenge → `Packed_bits (pre, Challenge.length)`            128

⚠ ⚑ **CORRECTED 2026-08-03: the `Field` arm is `` [| `Field x |] `` and this block said
`Packed_bits` (`spec.ml:373-374`).** The WIDTH is 255 either way — `multiscale_known` scales the
`` `Field `` case at `~num_bits:Field.size_in_bits` (`step_verifier.ml:159-165`) — so `msmBits` does
not move. What the constructor decides is the CONSTANT PARTITION, which matches
`` `Field (Constant c) | `Packed_bits (Constant c, _) `` (`:135-137`), i.e. both.

⚠ There is **no `Scalar_challenge` basic**. `Scalar chal` is a `T.t` CONSTRUCTOR whose `pack` is
`p.pack chal` on the SAME seven (`spec.ml:94-99`), so `Vector (Scalar Challenge, N3)` packs at 128
exactly like `B Challenge`. `Challenge.length = 64 · Nat.to_int N2 = 128` — `Challenge.Constant =
Constant.Make (Nat.N2)` (`limb_vector/challenge.ml:5`) and `Constant.Make.length = 64 * Nat.to_int
N.n` (`limb_vector/constant.ml:70`; `make.ml:11` is the same line for the var side).
`Branch_data.length_in_bits = 10` (`composition_types/branch_data.ml:61`, 2 bits `proofs_verified`
+ 8 bits `domain_log2`).

The statement's own order is `Types.Wrap.Statement.In_circuit.spec`
(`composition_types.ml:785-823`), and `to_data` (`:825-880`) is what fills it:

    Vector (B Field, N5)                              cip, b, ζ^srs_len, ζ^dom, perm     5 × 255
    Vector (B Challenge, N2)                          β, γ                               2 × 128
    Vector (Scalar Challenge, N3)                     α, ζ, ξ                            3 × 128
    Vector (B Digest, N3)                             sponge_digest, msgs_next_wrap/step 3 × 255
    Vector (B Bulletproof_challenge, Tick.Rounds.n)   bulletproof_challenges            16 × 128
    Vector (B Branch_data, N1)                        branch_data                        1 ×  10
    feature_flags_spec                                f1..f8                             8 ×   1
    Lookup_parameters.opt_spec                        the Opt's OWN flag + its Scalar     1 ×   1
                                                                                       + 1 × 128

**= 40**, which IS the devnet Wrap VK's `public = 40`.

⚑ **TWO CORRECTIONS TO THE CAMPAIGN BRIEF, both read at source and both confirmed by MINA'S OWN
COMPILED CIRCUIT.**

* `Backend.Tick.Rounds.n` is **16, not 15**. `Backend.Tick = Kimchi_backend.Pasta.Vesta_based_plonk`
  (`pickles/backend/backend.ml:1-4`), `Vesta_based_plonk.Rounds = Rounds.Step`
  (`pasta/vesta_based_plonk.ml:51`), `Rounds.Step = Nat.N16` (`pasta/basic/kimchi_pasta_basic.ml:17`).
  `Rounds.Wrap = Nat.N15` is real but is the WRAP proof's own IPA round count on Pallas
  (`pallas_based_plonk.ml:52`); this vector is the wrap STATEMENT's `bulletproof_challenges`, sized by
  the Tick rounds.
* `feature_flags_spec` carries **8** bools (`composition_types.ml:786-812`, `f1`..`f8`) — and the
  NINTH one-bit word is the lookup `Opt`'s own flag, which `Spec.pack`'s `Opt` case emits ahead of
  the inner spec in all three polarities (`spec.ml:123-140`: `zero`/`one`/`p.pack Bool b`). So nine
  one-bit words is right, and it is 8 + 1 rather than 9 features.

⚑ **MEASURED, off `step-zkapp-proved` — the o1-labs circuit blob, Mina's OWN compiled step circuit.**
The `x_hat` ladder cluster there is **31 `var_base_mul` ladders**, chunk widths in row order

    51,51,51,51,51, 26,26,26,26,26, 51,51,51, 26×16, 2, 26      (982 chunks, `51×8 26×22 2×1`)

which is this census word for word — five `Field`, five `Challenge`+`Scalar Challenge`, three
`Digest`, **sixteen** bulletproof challenges, one `Branch_data`, then the lookup challenge. ⚠ Read it
as **chunks × count**: ONE ladder of 2 chunks (`branch_data`, 10 bits), 22 of 26, 8 of 51 = 31
ladders / 982 chunks. §21/§22 read `2×1` as "two 1-chunk ladders", which would make 32.

⚠ ⚑ **AND THE NINE ONE-BIT WORDS ARE NOT DROPPED CONSTANTS — CORRECTED 2026-08-03 (§23).** This block
said `multiscale_known`'s constant partition (`step_verifier.ml:134-151`) folds them outside the
circuit. It does not, because they are not `Cvar.Constant`: the `proved` rule's only predecessor is
the SIDE-LOADED tag, whose eight feature flags are all `Opt.Flag.Maybe`
(`transaction_snark.ml:609-620,2111-2112`), so `maybe_constant` yields `Spec.T.B Bool` and NOT
`Spec.T.Constant` (`composition_types.ml:794-802`) and the `Opt` header at `Maybe` packs
`p.pack Bool b` — a witness (`spec.ml:123-141`). **`constant_part` is EMPTY in this circuit.** The
nine are live **ZERO-CHUNK** ladders: `chunks_needed ~num_bits:(1−1) = 0`, so they emit no scale
chunks — which is why the chunk census still lands on 982 without a special case — but upstream
still emits two `add_fast`es, an `EC_scale` with an empty round array and the `2·s_div_2 + s_odd = s`
tie for each (`plonk_curve_ops.ml:202-208,291`). **Mina emits 40 ladders; this assembly emits 31.**
A named residue with a corrected mechanism, not a closure. -/

/-- `Ops.chunks_needed ~num_bits` — `(num_bits + bits_per_chunk − 1) / bits_per_chunk` at
`bits_per_chunk = 5` (`plonk_curve_ops.ml:64-68`). -/
def chunksNeeded (numBits : Nat) : Nat := (numBits + 4) / 5

/-- `Field.size_in_bits` — what `Field` and `Digest` pack at (`spec.ml:377,379`). -/
def W_FIELD : Nat := 255
/-- `Challenge.length` — what `Challenge`, `Scalar Challenge` and `Bulletproof_challenge` pack at. -/
def W_CHAL : Nat := 128
/-- `Branch_data.length_in_bits`. -/
def W_BRANCH : Nat := 10
/-- `Bool` packs as ONE bit (`spec.ml:375`). -/
def W_BOOL : Nat := 1

/-- ⚑ Wrap statement word `i`'s PACKED BIT WIDTH, in `In_circuit.spec`'s own order. Beyond word 39
the statement has no more words, so a shape carrying more MSM terms than the statement has words
gets the challenge width — stated rather than defaulted, and §10 pins that the committed shape does
not reach it. -/
def msmBits (i : Nat) : Nat :=
  if i < 5 then W_FIELD             -- Vector (B Field, N5)
  else if i < 10 then W_CHAL        -- Vector (B Challenge, N2) ++ Vector (Scalar Challenge, N3)
  else if i < 13 then W_FIELD       -- Vector (B Digest, N3)
  else if i < 29 then W_CHAL        -- Vector (B Bulletproof_challenge, Tick.Rounds.n = N16)
  else if i == 29 then W_BRANCH     -- Vector (B Branch_data, N1)
  else if i < 39 then W_BOOL        -- f1..f8 ++ the lookup Opt's own flag bit
  else if i == 39 then W_CHAL       -- the lookup Opt's inner `Struct [Scalar Challenge]`
  else W_CHAL

/-- ⚑ MSM term `i`'s 5-bit chunk count — `multiscale_known`'s own `Ops.chunks_needed
~num_bits:(n − 1)` (`step_verifier.ml:172-174`, `plonk_curve_ops.ml:250-256`). **Zero** on the nine
one-bit words, which is why a faithful emission has 31 ladders and not 40. -/
def msmChunksAt (i : Nat) : Nat := chunksNeeded (msmBits i - 1)

/-- Chunks over the MSM terms below `n` — the CUMULATIVE offset the point and counter regions index
by, now that the per-term stride is not constant. -/
def msmChunkPrefix (n : Nat) : Nat := ((List.range n).map msmChunksAt).foldl (· + ·) 0

/-! ## §1c — ⚑ THE TRANSCRIPT SCHEDULE AND ITS LAZY LAYOUT.

⚑ MOVED ABOVE §2 on 2026-08-03: the variable space is now SIZED BY the schedule (`tBlocks` is the
permutation count Mina actually performs, not `absorbs + chals`), so the schedule has to be
elaborated before the first `xv`. Nothing in this block mentions a variable. -/

/-- `Nat.N45` + `Wrap_hack`'s two `sg_old` slots — `combine_split_commitments`' commitment count. -/
def N_WDB : Nat := 47
/-- `bullet_reduce`'s fifteen `absorb (PC :: PC) gammas_i` (`step_verifier.ml:199`) — every fold
round past `combine_split_commitments`'. TWO transcript blocks each, then one `squeeze_scalar`. -/
def gamRounds (s : StepShape) : List Nat :=
  (List.range s.ipaRounds).filter (fun r => N_WDB ≤ r + 1)
/-- ⚑ The transcript squeezes upstream takes at SCHEDULED positions (§2b): β, γ, α, ζ, `u`, one per
`bullet_reduce` round, and `c`. **21** at the committed shape; `chals − 21` is what this file still
takes off the transcript that upstream takes off the fr-sponge (ξ and r, §8g). -/
def sqScheduled (s : StepShape) : Nat := 6 + (gamRounds s).length / 2
-- ⚑ THE SCHEDULE'S OWN ORDER since the R1 interleaving (`step_verifier.ml:563-568`): β then γ then
-- α then ζ, squeezes 0..3. They were `ζ,α,β,γ = 0,1,2,3` when R1 had no schedule and the numbering
-- was arbitrary. ⚑ These four are ALL squeezed BEFORE `combined_inner_product` is absorbed (`:256`),
-- which is the whole reason `cip` can be a transcript word at all — §12i pins it.
def StepShape.betaChal (_s : StepShape) : Nat := 0
def StepShape.gammaChal (_s : StepShape) : Nat := 1
def StepShape.alphaChal (_s : StepShape) : Nat := 2
def StepShape.zetaChal (_s : StepShape) : Nat := 3
/-- ⚑ `c = squeeze_scalar sponge` (`:322`) — the LAST scheduled transcript squeeze, and the scalar
`lhs = Scalar_challenge.endo q c + delta` multiplies the fold output by. -/
def StepShape.cChal (s : StepShape) : Nat := sqScheduled s - 1
/-- ⚑ The `bRounds` challenges `b(ζ) = ∏(1 + uₖ·ζ^{2^{…}})` folds over. Upstream these are the
previous proof's `bulletproof_challenges` (`step_verifier.ml:937-938,1124-1128`); this file still
takes them off the transcript (the round-robin sharing #4 names), and takes them from the squeezes
AFTER ζ — which at the committed shape ARE `u` and `bullet_reduce`'s fifteen. It was `k + 1` when ζ
was challenge 0; at ζ = 3 that would have made ζ one of its own `uₖ`. -/
def StepShape.uChal (s : StepShape) (k : Nat) : Nat := s.zetaChal + 1 + k

/-- ⚑ Upstream's provenance census for `combine_split_commitments`' 47 `without_degree_bound`
commitments, in ITS OWN ORDER (`step_verifier.ml:601-616`); `true` = absorbed into the transcript.

    0,1    sg_old, padded          ABSORBED (`Vector.iter ~f:(absorb sponge PC) sg_old`, :537)
    2      x_hat                   ABSORBED (`absorb sponge PC x_hat`, :559)
    3      ft_comm                 computed from `t_comm` + the VK — NOT assembled (#5), so const
    4      z_comm                  ABSORBED (`receive without z_comm`, :564)
    5..10  generic/psm/complete_add/mul/emul/endomul_scalar     VK CONSTANT
    11..25 w_comm ×15              ABSORBED (`Vector.iter ~f:absorb_g w_comm`, :561)
    26..40 coefficients_comm ×15   VK CONSTANT
    41..46 sigma_comm_init ×6      VK CONSTANT -/
def wdbAbsorbed (i : Nat) : Bool := i ≤ 2 || i == 4 || (11 ≤ i && i < 26)

/-- ⚑ IPA round `r`'s base provenance before block assignment. Rounds `0 .. N_WDB−2` are
`combine_split_commitments`' own — round `r` folds in commitment `r+1`, the accumulator starting at
commitment `0` — and every round past them is a `bullet_reduce` `(L,R)`, all of which are absorbed
(`step_verifier.ml:193`). -/
def ipaAbsorbs (r : Nat) : Bool := if r + 1 < N_WDB then wdbAbsorbed (r + 1) else true

/-- ⚑ The fold rounds the transcript absorbs BEFORE β, in `incrementally_verify_proof`'s own order:
`sg_old[1]` and `x_hat` (`step_verifier.ml:538,560`) and `w_comm ×15` (`:562`) — census commitments
1, 2 and 11..25, i.e. rounds 0, 1 and 10..24. ⚠ Commitment 0 (`sg_old[0]`) is NOT a round at all:
it is where `combine_split_commitments` STARTS its accumulator (`~init`, `:606`). -/
def preRounds (s : StepShape) : List Nat :=
  (List.range s.ipaRounds).filter (fun r => ipaAbsorbs r && r + 1 < N_WDB && r + 1 != 4)
/-- `receive without z_comm` (`:565`) — census commitment 4, round 3, absorbed BETWEEN γ and α. -/
def zRounds (s : StepShape) : List Nat :=
  (List.range s.ipaRounds).filter (fun r => ipaAbsorbs r && r + 1 == 4)

/-- The rounds whose bases the transcript absorbs, IN UPSTREAM'S ABSORPTION ORDER. ⚑ Since the R1
interleaving this is `preRounds ++ zRounds ++ gamRounds` and not the raw `ipaAbsorbs` filter: the
filter puts `z_comm` (round 3) ahead of `w_comm` (rounds 10..24) and the gammas ahead of `t_comm`,
which is NOT the order `verify_one` feeds the sponge, and a sponge is order-sensitive. §12b pins
that the two are the same SET and a different LIST. -/
def absRoundList (s : StepShape) : List Nat :=
  preRounds s ++ zRounds s ++ gamRounds s

/-! ### ⚑ `verify_one`'s SPONGE-ITEM CENSUS — what `absorbs` is supposed to be a count OF.

Read at source and counted item by item, because the number `absorbs` carried until 2026-08-02 was
not a count of anything: it was 71, i.e. `2·71 = 142` field elements, against the **117** sponge
items `verify_one` actually feeds its transcript. Twenty-five words the sponge swallowed corresponded
to nothing upstream absorbs — a SHAPE overshoot that the previous rung's residue note had mistaken
for twenty-five unwired absorptions.

`Sponge.absorb` takes ONE field element per call; `absorb sponge PC p` is
`g1_to_field_elements p` = **two**, and `absorb sponge Scalar (x, b)` is `Field x` then `Bits [b]` =
**two** (`step_verifier.ml:75-84`). At rate 2 the block count is `⌈items/2⌉`. -/

/-- The census, in `incrementally_verify_proof`'s own absorption order. -/
def ABSORB_ITEMS : List (String × Nat) :=
  [ -- `absorb sponge Field index_digest` (`step_verifier.ml:534`) — ONE field element.
    ("index_digest", 1)
    -- `Vector.iter ~f:(absorb sponge PC) sg_old` (`:538`) over `Wrap_hack.Checked.pad_commitments`,
    -- `Padded_length = Nat.N2` (`wrap_hack.ml:24,28`): TWO points.
  , ("sg_old, padded ×2", 4)
    -- `absorb sponge PC x_hat` (`:560`).
  , ("x_hat", 2)
    -- `Vector.iter ~f:absorb_g w_comm` (`:562`), `Plonk_types.Columns = 15`.
  , ("w_comm ×15", 30)
    -- `receive without z_comm` (`:565`).
  , ("z_comm", 2)
    -- `receive without t_comm` (`:567`), `Commitment_lengths.create ~t:(of_int 7)`
    -- (`commitment_lengths.ml:6-11`).
  , ("t_comm ×7", 14)
    -- `absorb sponge Scalar advice.combined_inner_product` (`:256-259`) — `Other_field.t` is
    -- `(Field.t, Boolean.var)`, so `absorb_scalar` emits field THEN bit (`:79-81`).
  , ("combined_inner_product, field+bit", 2)
    -- `bullet_reduce`'s `absorb (PC :: PC) gammas_i` (`:199`) over 15 `(L,R)` pairs.
  , ("bullet_reduce (L,R) ×15", 60)
    -- `absorb sponge PC delta` (`:321`).
  , ("delta", 2) ]
/-- **117.** -/
def N_ABSORB_ITEMS : Nat := (ABSORB_ITEMS.map (·.2)).foldl (· + ·) 0

/-- ⚑ The absorptions `verify_one` performs that this file does NOT yet wire to a variable a
sub-circuit reads. Named individually so the residue is a LIST and not an adjective. -/
def UNWIRED_ITEMS : List (String × Nat) := []
/-- **0** since 2026-08-02. The three that were here are closed WITH their consumers:

  * `sg_old[0]` — absorbed at block `oSgOld0` and consumed as `combine_split_commitments`' `~init`
    accumulator (`:606`), the point R4's `complete_add` chain starts at.
  * `combined_inner_product` as field+bit — absorbed at `oCip`, which is where `:256` puts it: AFTER
    ζ (`:568`), so it is not a cycle. The field half IS `vCipShift`, the statement word R8's
    `combined_inner_product_correct` ties to R5's Horner output.
  * `delta` — absorbed at `oDelta` and consumed by `lhs = Scalar_challenge.endo q c + delta`
    (`:325-327`), one endo ladder over the fold output at the LAST transcript squeeze plus one
    `Ops.add_fast`.

⚠ What remains is the ONE PAD LANE, which is not an item: 117 is odd. -/
def N_UNWIRED_ITEMS : Nat := (UNWIRED_ITEMS.map (·.2)).foldl (· + ·) 0

/-- The absorb-block count a shape needs to feed `N_ABSORB_ITEMS` items at rate 2 — `⌈117/2⌉ = 59`.
⚑ 117 is ODD, so one lane of one block has nothing upstream to carry: `index_digest` is a single
`Field` and every later item comes in pairs, so the spare lane is block 0's second, exactly where the
one non-commitment free word already sat (`msgVar`). That single PAD LANE is the difference between
`2·absorbs` and 117, and it is a consequence of modelling ONE commitment per rate-2 block. -/
def absorbBlocksNeeded : Nat := (N_ABSORB_ITEMS + 1) / 2

/-! ### `Common.ft_comm`'s own quantities (§6b).

`common.ml:238-256` and `step_verifier.ml:240-242,587-591`. Everything the ft_comm MSM is sized by,
stated where the transcript census can already see it: `t_comm`'s chunk count decides how many
transcript blocks stop being free, and the on-curve region below is sized by it. -/

/-- `Commitment_lengths.create ~t:(of_int 7)` (`commitment_lengths.ml:6-11`) — the quotient
polynomial's chunk count, hence `Array.length t_comm` in `common.ml:248`. -/
def N_TCOMM : Nat := 7
/-- …as many as THIS shape carries, capped at 7. The smoke shape carries three, the same way it
carries five fold rounds instead of 76; §12b″ pins that the cap does not bind at the committed shape,
so no `t_comm` chunk silently stays a free witness. ⚑ Read off `s.tComms` and no longer off
`absorbs − 1 − |absRoundList|`: since the R1 interleaving `absorbs` is DERIVED from the schedule and
the schedule contains the `t_comm` blocks, so the old form was circular. -/
def tCommN (s : StepShape) : Nat := min N_TCOMM s.tComms
/-- `ft_comm`'s `scale_fast2` count: `plonk.perm · sigma_comm_last`, the `n−1` Horner steps in
`plonk.zeta_to_srs_length`, and the closing `plonk.zeta_to_domain_size` scale. **Eight** at
`tCommN = 7`, which is `common.ml:246,251,256` counted. -/
def ftcTerms (s : StepShape) : Nat := tCommN s + 1
/-- `Ops.chunks_needed ~num_bits:(Field.size_in_bits − 1) = ⌈254/5⌉` — the chunk count EVERY
`ft_comm` scale runs at (`plonk_curve_ops.ml:66-70,254-257`; `scale_fast2 ~num_bits:255` via
`step_verifier.ml:240-242`). ⚠ NOT `msmChunksAt`: `multiscale_known`'s scalars carry a width PER
BASIC (§1b) and `ft_comm`'s are uniformly 255-bit, so the two `VarBaseMul` regions keep two
independent chunk counts. -/
def FTC_CHUNKS : Nat := 51
/-- ⚑ The fold round whose base `Common.ft_comm` COMPUTES. `combine_split_commitments`' commitment
`3` is `ft_comm` (`step_verifier.ml:606`), and round `r` folds commitment `r+1`, so it is round 2. -/
def FTC_ROUND : Nat := 2

/-! ### ⚑⚑ §2b — **THE TRANSCRIPT SCHEDULE**: `incrementally_verify_proof`'s OWN absorb/squeeze
INTERLEAVING, read at source.

Until 2026-08-02 R1 ran **all** `absorbs` absorb blocks and **then** all `chals` squeeze blocks, and
its absorb order was the `ipaAbsorbs` FILTER order (z_comm ahead of w_comm, the gammas ahead of
`t_comm`). Neither is `verify_one`'s. A sponge is order-sensitive, so both were fidelity defects; and
the all-absorbs-first shape is what made `combined_inner_product` unwireable — absorbing it would
have made β/γ/α/ζ depend on a value the transcript itself determines. Upstream has no such cycle
because it absorbs it AFTER ζ.

`step_verifier.ml:529-574` then `:247-340`, in order, with the sponge item counts:

    :534   absorb Field index_digest                    1   (+1 PAD lane — 117 is odd)
    :538   Vector.iter (absorb PC) sg_old ×2            4   ⚑ sg_old[0] is the fold's `~init`
    :560   absorb PC x_hat                              2
    :562   Vector.iter absorb_g w_comm ×15             30
    :563   let beta  = sample ()                          SQUEEZE
    :564   let gamma = sample ()                          SQUEEZE
    :565   let z_comm = receive without z_comm          2
    :566   let alpha = sample_scalar ()                   SQUEEZE
    :567   let t_comm = receive without t_comm         14
    :568   let zeta  = sample_scalar ()                   SQUEEZE
    :573   sponge_before_evaluations = Sponge.copy sponge     ⚑ THE FORK
    :574   sponge_digest_before_evaluations = squeeze_field   (off the COPY's twin — see below)
    :256   absorb Scalar advice.combined_inner_product  2   ⚑ AFTER ζ. This is why there is no cycle.
    :264   let u = group_map (squeeze_field sponge)        SQUEEZE
    :199   ×15  absorb (PC :: PC) gammas_i              60   (two blocks per round)
    :200   ×15  squeeze_scalar                            SQUEEZE
    :321   absorb PC delta                              2
    :322   let c = squeeze_scalar sponge                  SQUEEZE

**117 items, 59 rate-2 blocks, 21 transcript squeezes.** ⚠ THE FORK, stated rather than elided: the
copy at `:573` is taken BEFORE the `:574` squeeze, so `check_bulletproof` continues from the state ζ
left and the digest permutation is a SIDE branch — the same `Sponge.copy` shape §3c already models
for `index_digest`. This file's linear chain IS the copy's; `sponge_digest_before_evaluations` is not
modelled as a block (nothing here consumes it — it is `verify_one`'s return value, absorbed by
`step_main.ml:45` into the sponge `finalize_other_proof` runs, which is segment A/B's business).

⚠ `chals = 23` against upstream's 21: the two extra are ξ and r, which upstream squeezes from the
**fr-sponge** (`:1008-1009`, §8g) and which this file still also allocates as transcript squeezes for
the round-robin `msmChal`/`ipaChal` sharing. They are scheduled at the END, after `c`, and named. -/

/-- Absorb SOURCE ordinals, in upstream's order. ⚑ A *source* is one `absorb` CALL of `verify_one`
(`step_verifier.ml:75-84`): `absorb sponge Field x` feeds ONE item, `absorb sponge PC p` feeds
`g1_to_field_elements p` = two, `absorb sponge Scalar (x, b)` feeds `Field x` then `Bits [b]` = two.
⚠ A source is NOT a block: since the lazy re-model a rate-2 block is filled by the ITEM STREAM and
straddles sources — `index_digest` shares block 0 with `sg_old[0]`'s x. -/
def oDigest : Nat := 0
/-- ⚑ `sg_old[0]` — `combine_split_commitments`' `~init` accumulator (`:606`), absorbed at `:538`
and consumed by R4's `complete_add` chain rather than by a fold round. -/
def oSgOld0 : Nat := 1
def oPre : Nat := 2
def oZ (s : StepShape) : Nat := oPre + (preRounds s).length
def oTc (s : StepShape) : Nat := oZ s + (zRounds s).length
/-- ⚑ `absorb sponge Scalar advice.combined_inner_product` (`:256`) — field then bit (`:79-81`). -/
def oCip (s : StepShape) : Nat := oTc s + tCommN s
def oGam (s : StepShape) : Nat := oCip s + 1
/-- ⚑ `absorb sponge PC delta` (`:321`), consumed by `lhs = Scalar_challenge.endo q c + delta`. -/
def oDelta (s : StepShape) : Nat := oGam s + (gamRounds s).length
/-- **`absorbs`, DERIVED from the schedule.** §12b pins `s.absorbs == absorbBlocksOf s` at both
shapes, so a shape cannot swallow a block the source does not feed. -/
def absorbBlocksOf (s : StepShape) : Nat := oDelta s + 1

/-- ⚑⚑ **THE SOURCE ORDINALS, HOISTED — and this is the whole of the elaboration floor.**

`oZ`/`oTc`/`oCip`/`oGam`/`oDelta`/`sqScheduled` are a CHAIN, and each link rebuilds one of
`preRounds`/`zRounds`/`gamRounds` — a `filter` over `List.range s.ipaRounds`, 76 entries at the
committed shape. `sqAfter` names five of them, so ONE call walked eleven such filters, and `tOps`
calls `sqAfter` once per absorb source (60 of them at `shapeStep`): ~660 traversals per `tOps`.

MEASURED at `shapeStep` under the same interpreter `native_decide` runs on (`wip/FloorProbe.lean`,
`lean --run`, cold process): **`tOps` 33 ms, `spLay` 34 ms** — i.e. `tOps` IS `spLay`, 97% of it.
And `spLay` is not a constant; it is a FUNCTION of the shape, so nothing caches it. `tBlocks s =
(spLay s).cur` sits under `nSt`, `nSt` sits under `baseN = nSt s + 2 * tBlocks s + 1` — **two**
`spLay`s — and every one of the ~thirty region bases above it inherits that. Measured: `baseFtc
shapeStep` = **68 ms**, exactly 2 × `spLay`, for ONE variable-name lookup; `tPadCell shapeStep` =
**7.9 s**, because it asked `blockAbsorbs`/`blockWords` per (block, lane) and each recomputed
`spLay`. A schedule that names tens of thousands of variables therefore paid tens of thousands of
33 ms transcript layouts, which is the twenty-minute `native_decide` floor.

This record is that chain, evaluated ONCE. `srcOrd_eq` states it is exactly the six ordinals — a
general theorem over every shape, by `rfl`, so the hoist cannot drift from what it hoists. -/
structure SrcOrd where
  z : Nat
  tc : Nat
  cip : Nat
  gam : Nat
  delta : Nat
  sched : Nat
  deriving Repr, Inhabited, DecidableEq

/-- The six ordinals in one pass: `gamRounds` once (it is both `oDelta`'s addend and
`sqScheduled`'s), `preRounds` once, `zRounds` once. -/
def srcOrd (s : StepShape) : SrcOrd :=
  let nGam := (gamRounds s).length
  let z := oZ s
  let tc := z + (zRounds s).length
  let cip := tc + tCommN s
  let gam := cip + 1
  { z := z, tc := tc, cip := cip, gam := gam, delta := gam + nGam, sched := 6 + nGam / 2 }

/-- ⚑ **THE HOIST IS THE THING IT HOISTS.** General, `rfl`, no shape instance and no oracle — so a
change to either `srcOrd` or any of the six reds here instead of splitting the schedule in two. -/
theorem srcOrd_eq (s : StepShape) :
    srcOrd s = ⟨oZ s, oTc s, oCip s, oGam s, oDelta s, sqScheduled s⟩ := rfl

/-- …and `absorbBlocksOf` is the last source plus one. -/
theorem absorbBlocksOf_eq_srcOrd (s : StepShape) : absorbBlocksOf s = (srcOrd s).delta + 1 := rfl

/-- ⚑ How many SQUEEZE blocks follow absorb block `a`. Additive rather than a chain of `else if`, so
a shape whose `zRounds` or `t_comm` list is empty still gets both of the squeezes that bracket it.

⚑ The ordinals arrive in `o` rather than being recomputed per source — see `SrcOrd`. `sqAfter` below
is this at `o = srcOrd s`, so the spec is unchanged and there is one body. -/
def sqAfterAt (s : StepShape) (o : SrcOrd) (a : Nat) : Nat :=
  (if a + 1 == o.z then 2 else 0)                               -- β (:563), γ (:564)
  + (if a + 1 == o.tc then 1 else 0)                            -- α (:566)
  + (if a + 1 == o.cip then 1 else 0)                           -- ζ (:568)
  + (if a == o.cip then 1 else 0)                               -- u = group_map … (:264)
  + (if o.gam ≤ a && a < o.delta && (a - o.gam) % 2 == 1 then 1 else 0)   -- prechallenge (:200)
  -- `c` (:322), then the `chals − 21` this file still takes off the transcript rather than off the
  -- fr-sponge (ξ and r, §8g).
  + (if a == o.delta then 1 + (s.chals - o.sched) else 0)

/-- …at the shape's own ordinals. -/
def sqAfter (s : StepShape) (a : Nat) : Nat := sqAfterAt s (srcOrd s) a

/-! ### ⚑⚑ §1c′ — **MINA'S SPONGE IS LAZY, AND THIS FILE'S WAS EAGER.**

`snarky/sponge/sponge.ml:280-326`, `rate = m − capacity = 3 − 1 = 2` (`:294`), verbatim:

    let absorb t x = match t.sponge_state with
      | Absorbed n -> if n = rate then (t.state <- block_cipher …; add_assign … 0 x;
                                        t.sponge_state <- Absorbed 1)
                      else (add_assign … n x; t.sponge_state <- Absorbed (n + 1))
      | Squeezed _ -> add_assign … 0 x ; t.sponge_state <- Absorbed 1
    let squeeze t = match t.sponge_state with
      | Squeezed n -> if n = rate then (t.state <- block_cipher …; t.sponge_state <- Squeezed 1;
                                        copy t.state.(0))
                      else (t.sponge_state <- Squeezed (n + 1) ; copy t.state.(n))
      | Absorbed _ -> t.state <- block_cipher … ; t.sponge_state <- Squeezed 1 ; copy t.state.(0)

**The permutation is triggered by an ARRIVING element, never on the way out.** Three consequences,
and until 2026-08-03 this file had all three wrong:

1. **A squeeze from `Absorbed _` supplies the block's ONE permutation.** The old `tSched` gave every
   squeeze a block of its own on top of the absorb blocks, so the transcript ran **one extra
   permutation per squeeze** — 21 of them at `shapeStep`.
2. **A second consecutive squeeze is FREE**: `Squeezed 1`, `n ≠ rate`, `else` branch, `state.(1)`.
   So β and γ (`:563-564`) are lanes 0 and 1 of ONE permutation, and segment B's ξ′ and r′
   (`:1007-1009`) likewise — where the old model put them two permutations apart. The THIRD
   consecutive squeeze permutes again (`Squeezed 2 = rate`).
3. **An absorb from `Squeezed _` lands in lane 0 and does NOT permute**, so the rate counter RESTARTS
   at every squeeze and the item stream re-pairs. The old model paired per SOURCE (one commitment per
   block) and padded `index_digest` to two; upstream pairs per ITEM, so `index_digest` shares block 0
   with `sg_old[0]`'s x and the ONE pad lane lands at the END of the pre-β run instead.

⚑ THE REALITY GATE FOR THIS SHAPE IS ALREADY IN THE TREE AND ALREADY RED-PROOFED.
`PastaPoseidon.Ref.absorbFrom` is this same state machine, and its header records that an EAGER
variant "permuted twice on every input of nonzero EVEN length" and failed **exactly the two
even-length o1js gold KATs** — `[123456789, 987654321]` and `[p−1, p−1]`. The lazy shape is what
reproduces all nine golds. This section is that fix carried from `Poseidon.hash` up to `verify_one`'s
transcript. -/

/-- The sponge rate — `m − capacity = 3 − 1` (`sponge.ml:294`). -/
def RATE : Nat := 2

/-- ⚑ How many sponge ITEMS absorb source `a` feeds. `absorb sponge Field index_digest` is a bare
`Field` — ONE. Every other source is a curve point or an `absorb_scalar` `(field, bit)` pair — TWO.
This is why `N_ABSORB_ITEMS` is ODD. -/
def srcItems (a : Nat) : Nat := if a == oDigest then 1 else 2

/-- **THE OP TAPE** — `verify_one`'s sponge calls in order. `some (a, j)` absorbs source `a`'s lane
`j`; `none` is a squeeze. -/
def tOps (s : StepShape) : List (Option (Nat × Nat)) :=
  -- ⚑ ONE `srcOrd` for the whole tape rather than one per source — `SrcOrd`'s note carries the
  -- measurement. `absorbBlocksOf s = o.delta + 1` is `absorbBlocksOf_eq_srcOrd`, by `rfl`.
  let o := srcOrd s
  (List.range (o.delta + 1)).flatMap (fun a =>
    (List.range (srcItems a)).map (fun j => some (a, j))
    ++ List.replicate (sqAfterAt s o a) none)

/-- The LAYOUT the lazy state machine produces. `put` is `(block, lane, source, lane-in-source)` —
where each absorbed item lands; `sq` is `(block, lane)` per squeeze — the state a squeeze reads is
the one ENTERING block `.1`, at lane `.2`, so a squeeze that permutes advances `cur` first and a
free one does not. `cur` ends as the PERMUTATION COUNT. -/
structure SpLay where
  put : List (Nat × Nat × Nat × Nat) := []
  sq : List (Nat × Nat) := []
  cur : Nat := 0
  n : Nat := 0
  sqz : Bool := false
  deriving Repr, Inhabited

/-- One op, transcribed from `sponge.ml:296-325` clause for clause.

⚑ `put`/`sq` are built **REVERSED** and `spLay` reverses them once at the end, so the two tapes cost
one cons per op instead of `L.put ++ [x]`'s copy of everything already there. At 117 items that
append was ~6,800 cells per layout, and after `SrcOrd` took `tOps` out of the way it was what was
left of `spLay`. The FINAL value is unchanged — `spLay`, not `spStep`, is what every consumer
reads. -/
def spStep (L : SpLay) : Option (Nat × Nat) → SpLay
  | some (a, j) =>
      -- `| Squeezed _ -> add_assign ~state 0 x ; Absorbed 1`  (no permutation)
      if L.sqz then { L with put := (L.cur, 0, a, j) :: L.put, n := 1, sqz := false }
      -- `| Absorbed n -> if n = rate then (block_cipher; add_assign 0 x; Absorbed 1)`
      else if L.n == RATE then
        { L with put := (L.cur + 1, 0, a, j) :: L.put, cur := L.cur + 1, n := 1 }
      -- `else (add_assign n x; Absorbed (n+1))`
      else { L with put := (L.cur, L.n, a, j) :: L.put, n := L.n + 1 }
  | none =>
      if L.sqz then
        -- `| Squeezed n -> if n = rate then (block_cipher; Squeezed 1; state.(0))`
        (if L.n == RATE then { L with sq := (L.cur + 1, 0) :: L.sq, cur := L.cur + 1, n := 1 }
         -- `else (Squeezed (n+1); state.(n))` — FREE, no permutation
         else { L with sq := (L.cur, L.n) :: L.sq, n := L.n + 1 })
      -- `| Absorbed _ -> block_cipher ; Squeezed 1 ; state.(0)`
      else { L with sq := (L.cur + 1, 0) :: L.sq, cur := L.cur + 1, n := 1, sqz := true }

/-- **R1's LAYOUT.** ⚑ The two tapes come out of the fold newest-first (`spStep`'s note); the
reverse here is what puts them back in schedule order, which is the order every consumer —
`itemAt`, `blockWordsL`, `sqPos` — reads them in. -/
def spLay (s : StepShape) : SpLay :=
  let L := (tOps s).foldl spStep {}
  { L with put := L.put.reverse, sq := L.sq.reverse }

/-- **The transcript's PERMUTATION COUNT** — the number of `Poseidon` blocks R1 emits, and the
number `Sponge.absorb`/`Sponge.squeeze` between them perform. `states` runs `0 … tBlocks`. -/
def tBlocks (s : StepShape) : Nat := (spLay s).cur

/-- ⚑ Where source `a`'s lane `j` LANDS: `(block, lane)`. The inverse of `blockWords`, and the
replacement for the retired `absBlock` — a source no longer owns a block. -/
def itemAt (s : StepShape) (a j : Nat) : Nat × Nat :=
  match ((spLay s).put.find? (fun x => x.2.2.1 == a && x.2.2.2 == j)) with
  | some x => (x.1, x.2.1)
  | none => (0, 0)

/-- Block `b`'s two absorbed items as `(source, lane-in-source)`; `none` in a lane no item lands in
(there is at most one such lane in the whole transcript — see `tPadBlock`). -/
def blockWordsL (L : SpLay) (b : Nat) : List (Option (Nat × Nat)) :=
  (List.range RATE).map (fun l =>
    (L.put.find? (fun x => x.1 == b && x.2.1 == l)).map (fun x => (x.2.2.1, x.2.2.2)))
def blockWords (s : StepShape) (b : Nat) : List (Option (Nat × Nat)) := blockWordsL (spLay s) b

/-- Does block `b` swallow anything at all? A block that does not is a pure permutation — the third
consecutive squeeze's. -/
def blockAbsorbs (s : StepShape) (b : Nat) : Bool := (blockWords s b).any (·.isSome)

/-- ⚑ Squeeze `c`'s `(block, lane)`: R2 reads challenge `c` out of `vSt s (sqStBlock s c)
(sqStLane s c)`. ⚠ NOT `vSt (sqBlock c + 1) 0` — `sqBlock` is GONE, because a squeeze no longer owns
a block and no longer always reads lane 0. -/
def sqPos (s : StepShape) (c : Nat) : Nat × Nat := (spLay s).sq.getD c (0, 0)
def sqStBlock (s : StepShape) (c : Nat) : Nat := (sqPos s c).1
def sqStLane (s : StepShape) (c : Nat) : Nat := (sqPos s c).2

/-- ⚑ **THE ONE PAD LANE**, and it MOVED. `N_ABSORB_ITEMS` is odd, so exactly one rate-2 lane of the
transcript receives no item. Under the per-source model that was block 0's second lane (paired with
`index_digest`) and it carried a `msgVal` FIXTURE — a word upstream never feeds. Under the item
stream it is the last lane of the pre-β run, it receives NOTHING, and `transcriptRows` pins a cell to
ZERO there: `absorb` ADDS, and adding zero to a lane the previous permutation already filled is
exactly "no arrival". `none` at a shape whose item count is even.

⚑ ONE `spLay` for the whole scan, not one per `(block, lane)` question. `blockWords s b` is
`blockWordsL (spLay s) b` and `blockAbsorbs s b` is `(blockWords s b).any (·.isSome)`, both by
definition, so this is the same value — but the version that asked them through the shape recomputed
the transcript layout 2·RATE·`tBlocks` + 1 = 237 times and MEASURED **7.9 s for one call** at
`shapeStep` (`SrcOrd`'s note has the instrument). -/
def tPadCell (s : StepShape) : Option (Nat × Nat) :=
  let L := spLay s
  ((List.range L.cur).flatMap (fun b =>
    let ws := blockWordsL L b
    (List.range RATE).filterMap (fun l =>
      if ws.any (·.isSome) && (ws.getD l none).isNone then some (b, l) else none))).head?

/-- Which blocks a squeeze reads the output of — where `transcriptRows` puts a σ-only probe, exactly
as it did when every squeeze had its own block. -/
def tProbeAfterL (L : SpLay) (b : Nat) : Bool :=
  (L.sq.any (fun p => p.1 == b + 1)) || (b + 1 == L.cur && !L.sq.any (fun p => p.1 == L.cur))
/-- ⚑ one `spLay`, not five: the two `.sq` reads and the two `tBlocks` were four more layouts. And
`transcriptRows` calls `tProbeAfterL` against the layout it already holds, so the whole per-block
scan costs ONE layout rather than one per block. -/
def tProbeAfter (s : StepShape) (b : Nat) : Bool := tProbeAfterL (spLay s) b

/-- ⚑ **`u`'s squeeze index.** `let u = group_map (Sponge.squeeze_field sponge)` (`:263-266`) is the
squeeze that follows absorb source `oCip`, so its index is the number of squeezes scheduled before
that source — `4` at both shapes (β, γ, α, ζ). -/
def uChalIx (s : StepShape) : Nat :=
  -- ⚑ one `srcOrd` for the whole prefix, as in `tOps`.
  let o := srcOrd s
  ((List.range o.cip).map (sqAfterAt s o)).foldl (· + ·) 0



/-! ## §2 — the variable space.

Public words are `external 0 .. pubWords-1` (Snarky's own numbering, which `place` reproduces). The
circuit's OWN variables start at `AUX`, so `placeChecked`'s H1 (silent public/aux absorption) cannot
fire and its H2 (an inert public word) is the real gate on the closing rung. Ids are laid out in
disjoint REGIONS whose bases are functions of the shape; §9 pins the distinct-variable count, so a
collision (which MERGES two σ classes and shrinks the count) goes red. -/

/-- The lowest `external` id the circuit allocates for itself; equals `PRIMARY_LEN` for the committed
shape, so `placeChecked`'s dead gap `pubWords ≤ i < AUX` is empty. -/
def AUX : Nat := 67

/-- Circuit variable `k`. -/
def xv (k : Nat) : PVar := .external (AUX + k)

/-- Sponge state lane `j` entering block `b` (`b = 0..tBlocks`). -/
def vSt (_s : StepShape) (b j : Nat) : PVar := xv (3 * b + j)
/-- The state region's size at a given permutation count. ⚑ Named separately from `nSt` so the two
places that need `nSt` AND `tBlocks` in one expression (`vTPad`, `baseN` — and `baseN` is under every
region above it) can ask `spLay` once instead of twice. -/
def nStOf (tb : Nat) : Nat := 3 * (tb + 1)
def nSt (s : StepShape) : Nat := nStOf (tBlocks s)

/-- Post-absorb lane `j ∈ {0,1}` of block `b`. ⚑ The `…At` form takes `nSt s` — see `mpxAt`'s note;
`circuitEnv` and `transcriptRows` both name this once per (block, lane). -/
def vPostAt (nst : Nat) (b j : Nat) : PVar := xv (nst + 2 * b + j)
def vPost (s : StepShape) (b j : Nat) : PVar := vPostAt (nSt s) b j
/-- ⚑ **THE TRANSCRIPT'S ONE PAD CELL**, pinned to zero by `transcriptRows` — the single rate-2 lane
an odd item count leaves without an arrival (`tPadCell`). ⚠ It REPLACES the whole `vMsg` region: with
the item stream every one of `N_ABSORB_ITEMS` words is a variable some sub-circuit reads, so there is
no free-witness transcript word left at all. `vMsg`/`msgVal` are GONE. -/
def vTPad (s : StepShape) : PVar := let tb := tBlocks s; xv (nStOf tb + 2 * tb)

/-- ⚑ The base every region above the transcript is measured from — and the one `spLay` call the
whole chain bottoms out in. It asked for `tBlocks` twice (once inside `nSt`); now once. -/
def baseN (s : StepShape) : Nat := let tb := tBlocks s; nStOf tb + 2 * tb + 1
/-- Challenge `c`'s `n` accumulator after `k` `EndoMulScalar` rows. `vN c emsRows` is THE CHALLENGE
VALUE — the variable three gate types share. -/
def vN (s : StepShape) (c k : Nat) : PVar := xv (baseN s + c * (s.emsRows + 1) + k)
def nN (s : StepShape) : Nat := s.chals * (s.emsRows + 1)
def baseA (s : StepShape) : Nat := baseN s + nN s
def vA (s : StepShape) (c k : Nat) : PVar := xv (baseA s + c * (s.emsRows + 1) + k)
def baseB (s : StepShape) : Nat := baseA s + nN s
def vB (s : StepShape) (c k : Nat) : PVar := xv (baseB s + c * (s.emsRows + 1) + k)
def baseHi (s : StepShape) : Nat := baseB s + nN s
/-- The high part of challenge `c`'s squeeze decomposition. -/
def vHi (s : StepShape) (c : Nat) : PVar := xv (baseHi s + c)

/-! ### The `to_field_checked` OUTPUT (`scalar_challenge.ml:125-129`).

`to_field_checked` is the `EndoMulScalar` chain, then `Field.Assert.equal n scalar`, then
**`Field.(scale a endo + b)`** — the endomorphism LIFT of the prechallenge. R2 emitted the first two
and stopped; these are the variables of the third, so `vLift c` IS `ScalarChallenge::to_field`
(`KimchiVerify.endoMap ENDO_R`) of the squeeze and the chain's `a₈`/`b₈` cells become load-bearing
rather than merely constrained. -/
def baseLift (s : StepShape) : Nat := baseHi s + s.chals
/-- `a₈ · endo_r` — the lift's product half. -/
def vLiftT (s : StepShape) (c : Nat) : PVar := xv (baseLift s + c)
/-- ⚑ **The LIFTED challenge** `a₈·endo_r + b₈`. This is what `plonk.zeta`/`plonk.alpha`, the
deferred `ξ`/`r` and every bulletproof challenge ARE upstream; the raw `vN c emsRows` is the
prechallenge the curve gadgets consume. -/
def vLift (s : StepShape) (c : Nat) : PVar := xv (baseLift s + s.chals + c)
/-- `Endo.Wrap_inner_curve.scalar`, pinned by one `Generic` row and shared by every lift. -/
def vEndoR (s : StepShape) : PVar := xv (baseLift s + 2 * s.chals)

def baseMsm (s : StepShape) : Nat := baseLift s + 2 * s.chals + 1
/-! ### ⚑⚑ **A VARIABLE NAME COSTS A TRANSCRIPT LAYOUT, AND THE `…At` FORMS ARE WHY IT NEED NOT.**

Every region base above the transcript is `baseN s + <shape arithmetic>` and `baseN s` bottoms out in
`tBlocks s = (spLay s).cur`, which is a FUNCTION of the shape and therefore caches nothing. MEASURED
2026-08-03 after the `SrcOrd` hoist: `spLay shapeStep` is under a millisecond and `baseFtc shapeStep`
is **1 ms** — for ONE variable-name lookup. The fifteen `rungRows … .opening` families cost
**15 879 ms** for 10 756 rows, i.e. about five such lookups a row, and that is essentially all of it.

So each hot region gets an `…At` form taking the base as an argument, with the shape-form defined
THROUGH it — exactly `sqAfter`/`sqAfterAt`'s shape, so the two cannot drift and every existing `rfl`
still holds by delta. A row emitter binds `let b := baseX s` once and names `xAt b` per row. -/
def mpxAt (b : Nat) (p : Nat) : PVar := xv (b + 2 * p)
def mpyAt (b : Nat) (p : Nat) : PVar := xv (b + 2 * p + 1)
def mpx (s : StepShape) (p : Nat) : PVar := mpxAt (baseMsm s) p
def mpy (s : StepShape) (p : Nat) : PVar := mpyAt (baseMsm s) p
/-- MSM term `i`'s base point. ⚑ CUMULATIVE since §1b: term `i` owns `msmChunksAt i + 2` points
(its base and its `msmChunksAt i + 1` accumulator boundaries), and the widths differ per word. -/
def pT (_s : StepShape) (i : Nat) : Nat := msmChunkPrefix i + 2 * i
/-- MSM term `i`'s accumulator at chunk boundary `j` (`j = 0..msmChunksAt i`). -/
def pAcc (s : StepShape) (i j : Nat) : Nat := pT s i + 1 + j
/-- The running MSM sum after add `a`. -/
def pSum (s : StepShape) (a : Nat) : Nat := pT s s.msmTerms + a
def nMsmPts (s : StepShape) : Nat := pT s s.msmTerms + s.msmTerms

def baseSN (s : StepShape) : Nat := baseMsm s + 2 * nMsmPts s
-- ⚑ `vSN` — MSM term `i`'s scalar counter chain — is **§2c**, below `baseFtS`: since 2026-08-03 its
-- terminal cell is the STATEMENT WORD `stmtVar i`, and two of the forty words live in R6's compiled
-- program (`baseFtS`) and one in segment C's sponge state. It cannot be stated here.


def baseIpa (s : StepShape) : Nat := baseSN s + msmChunkPrefix s.msmTerms
/-- ⚑ The `…At` forms — see `mpxAt`'s note. `ipx`/`ipy` are the hottest names in the assembly:
`endoRoundRows` alone asks for five of them per `endo_mul` block, 32 blocks a ladder, 77 ladders. -/
def ipxAt (b : Nat) (p : Nat) : PVar := xv (b + 2 * p)
def ipyAt (b : Nat) (p : Nat) : PVar := xv (b + 2 * p + 1)
def ipx (s : StepShape) (p : Nat) : PVar := ipxAt (baseIpa s) p
def ipy (s : StepShape) (p : Nat) : PVar := ipyAt (baseIpa s) p
/-- IPA round `r`'s `endo_mul` base point. ⚑ The per-round stride is `ipaBlocks + 3` and not `+ 2`
since 2026-08-02: the third slot is `Scalar_challenge.endo`'s own seed intermediate. -/
def qT (s : StepShape) (r : Nat) : Nat := r * (s.ipaBlocks + 3)
/-- IPA round `r`'s accumulator after `e` blocks (`e = 0..ipaBlocks`). -/
def qAcc (s : StepShape) (r e : Nat) : Nat := r * (s.ipaBlocks + 3) + 1 + e
/-- ⚑ `Scalar_challenge.endo`'s SEED intermediate `p = t + φ(t)` (`scalar_challenge.ml:230-233`:
`let p = G.( + ) t (seal (Field.scale xt Endo.base), yt) in ref G.(p + p)`). `qAcc r 0` is `p + p`,
so BOTH are rows and neither is a witness. -/
def qP (s : StepShape) (r : Nat) : Nat := r * (s.ipaBlocks + 3) + s.ipaBlocks + 2
/-- The running IPA fold sum after add `a`. ⚑ `a = 0 .. ipaRounds−1` since the `~init` wiring: the
chain STARTS at commitment 0 (`sg_old[0]`, `qInit`) and folds in every round's output, so there is
one add per round and `qSum (ipaRounds−1)` is `combined_polynomial`. It was `ipaRounds − 1` adds
starting at round 0's output, i.e. `combine_split_commitments` with its `~init` dropped. -/
def qSum (s : StepShape) (a : Nat) : Nat := s.ipaRounds * (s.ipaBlocks + 3) + a
/-- ⚑ **`sg_old[0]`** — `combine_split_commitments`' `~init` accumulator (`step_verifier.ml:606`,
`~init:(function `Finite x -> `Finite x | …)`), whose two coordinates ARE transcript block
`oSgOld0`'s absorbed words. It gets no fold ROUND; it is the point the chain starts at. -/
def qInit (s : StepShape) : Nat := s.ipaRounds * (s.ipaBlocks + 3) + s.ipaRounds
/-- ⚑ `check_bulletproof`'s TAIL (`:325-327`): `lhs = Scalar_challenge.endo q c + delta`, one more
`Scalar_challenge.endo` over the fold output `q` and one `Ops.add_fast` with `delta`. `qLhsP` is the
seed intermediate `p = t + φ(t)`. -/
def qLhsP (s : StepShape) : Nat := qInit s + 1
def qLhsAcc (s : StepShape) (e : Nat) : Nat := qInit s + 2 + e
/-- ⚑ **`delta`** — `absorb sponge PC delta` (`:321`); its two coordinates are transcript block
`oDelta`'s absorbed words and the second operand of the closing `add_fast`. -/
def qDel (s : StepShape) : Nat := qInit s + s.ipaBlocks + 3
/-- `lhs` itself. -/
def qLhsOut (s : StepShape) : Nat := qInit s + s.ipaBlocks + 4
/-- ⚑ **`q = p_prime + lr_prod`** (`step_verifier.ml:316-320`), i.e. the fold sum PLUS
`uc = scale_fast2 u advice.combined_inner_product`. §19 emits that `scale_fast2`; this is the
`Ops.add_fast` output it feeds, and `Scalar_challenge.endo q c` reads THIS point, not `qSum`.
⚠ The BRACKETING differs from upstream and the value does not: upstream is
`(combined_polynomial + uc) + lr_prod`, this chain is `(Σ combine + Σ lr) + uc`. Addition on the
curve is associative and commutative, so the point is the same one; what the difference costs is one
`Ops.add_fast` placed later in the schedule, and it is said here rather than elided. -/
def qPrime (s : StepShape) : Nat := qInit s + s.ipaBlocks + 5
def nIpaPts (s : StepShape) : Nat := s.ipaRounds * (s.ipaBlocks + 3) + s.ipaRounds + s.ipaBlocks + 6

def baseQN (s : StepShape) : Nat := baseIpa s + 2 * nIpaPts s
/-- IPA round `r`'s endo scalar counter after `e` blocks; at `e = ipaBlocks` it IS the round's
challenge variable.

⚑ The `…At` form takes `baseQN s` — see `mpxAt`'s note. `EndoSlots.n` is a PARTIAL APPLICATION of
this, so the base is evaluated once per ladder rather than once per `endo_mul` block; the terminal
`vN` branch fires once a ladder and keeps its own chain. -/
def vQNAt (s : StepShape) (bq : Nat) (r e : Nat) : PVar :=
  if e == s.ipaBlocks then vN s (s.ipaChal r) s.emsRows
  else xv (bq + r * s.ipaBlocks + e)
def vQN (s : StepShape) (r e : Nat) : PVar := vQNAt s (baseQN s) r e
/-- ⚑ `Field.scale xt Endo.base` — the endomorphism image's x, the SECOND operand of
`scalar_challenge.ml:232`'s `add_fast`. One `Generic` half per round pins it to `endo·xt`, so the
seed's provenance is the base and a constant rather than a witness. -/
def vQEndoAt (s : StepShape) (bq : Nat) (r : Nat) : PVar :=
  xv (bq + s.ipaRounds * s.ipaBlocks + r)
def vQEndo (s : StepShape) (r : Nat) : PVar := vQEndoAt s (baseQN s) r
/-- The `c`-endo tail's own counter chain; at `e = ipaBlocks` it IS `c`'s challenge variable, so the
value the ladder multiplies by is the one `to_field_checked` decoded from the LAST squeeze. -/
def vLhsNAt (s : StepShape) (bq : Nat) (e : Nat) : PVar :=
  if e == s.ipaBlocks then vN s (sqScheduled s - 1) s.emsRows
  else xv (bq + s.ipaRounds * s.ipaBlocks + s.ipaRounds + e)
def vLhsN (s : StepShape) (e : Nat) : PVar := vLhsNAt s (baseQN s) e
/-- …and its seed's `endo·x_q`. -/
def vLhsEndoAt (s : StepShape) (bq : Nat) : PVar :=
  xv (bq + s.ipaRounds * s.ipaBlocks + s.ipaRounds + s.ipaBlocks)
def vLhsEndo (s : StepShape) : PVar := vLhsEndoAt s (baseQN s)

/-- ⚑⚑ **`t`, the argument `group_map` actually gets — the FULL field element.** `:264` is
`Sponge.squeeze_field`, NOT `squeeze_scalar`: there is no `lowest_128_bits`, no `to_field_checked`
chain and no endomorphism lift on this path. ⚠ §17's exhibit read `chalOf` here — the LOW 128 bits —
which is the wrong `t` and hence the wrong `u`; §19 emits `group_map` over this variable and the
exhibit's `u` values move with it. -/
def uSqueezeVar (s : StepShape) : PVar :=
  vSt s (sqStBlock s (uChalIx s)) (sqStLane s (uChalIx s))

/-! ### ⚑⚑ §22 — **`sponge_digest_before_evaluations` IS A CELL THIS TRANSCRIPT ALREADY COMPUTES.**

`step_verifier.ml:573-574`:

    let sponge_before_evaluations = Sponge.copy sponge in
    let sponge_digest_before_evaluations = Sponge.squeeze_field sponge in

⚑ **AND IT COSTS NO PERMUTATION, read at source.** Mina's sponge is a LAZY rate-2 state machine
(`snarky/sponge/sponge.ml:294`: `rate = m − capacity = 3 − 1 = 2`). ζ at `:568` is
`sample_scalar → squeeze_scalar → Sponge.squeeze`, which on an `Absorbed _` state permutes, sets
`Squeezed 1` and returns `state.(0)` (`:322-325`). The very next `squeeze_field` at `:574` finds
`Squeezed 1` with `n ≠ rate`, so it takes the `else` branch (`:319-321`): **no permutation, return
`state.(1)`.** ζ and the digest are lane 0 and lane 1 of ONE permutation output.

That lane is already a wired cell here: `transcriptRows`' squeeze block emits
`permBlockRows … (vSt s (b+1) 0) (vSt s (b+1) 1) (vSt s (b+1) 2)` and already probes lanes 0/1. So
the digest needs no new row, no new variable and no new block — it needs to be NAMED. -/

/-- ⚑ **`sponge_digest_before_evaluations`** — lane 1 of the state ζ's squeeze permutation produced
(`step_verifier.ml:574`; `chalOf` reads lane 0 of the same state as ζ). -/
def digestBeforeEvalsVar (s : StepShape) : PVar := vSt s (sqStBlock s s.zetaChal) 1

/-! ### `Inner_curve.typ`'s own CHECK (§7b) — `assert_on_curve`.

`snarky_curve.ml:212-217`: `let x2 = square x in let x3 = x2 * x in let ax = Params.a * x in
assert_square y (x3 + ax + Params.b)`. Pallas has `a = 0, b = 5` (`Inner_curve.C =
Kimchi_pasta.Pasta.Pallas`, `step_main_inputs.ml:115`), so `ax` folds to the zero cvar and the
assert is ONE `Generic` half. Two variables per checked point — `x²` and `x³`; `y²` needs no slot
because the double-generic's own `w₀w₁` term is it.

⚑ The checked set is every SUPPLIED commitment the transcript absorbs: the `absRoundList` fold
bases, since §6b `t_comm`'s `tCommN` chunks, and since the R1 interleaving `sg_old[0]` and `delta`.
A CONSTANT base is pinned coordinate-for-coordinate and needs no membership check; the one COMPUTED
base (`ft_comm`, fold round `FTC_ROUND`) is on the curve because the `complete_add` chain that
produced it is. ⚑ …and since 2026-08-02 the THIRD non-round point is `G`, the previous proof's
`opening.challenge_polynomial_commitment` (`vGx`/`vGy`): it too arrives through `Inner_curve.typ`
(`wrap_proof.ml:39,60`) and it is what segment D absorbs. -/
def nOnC (s : StepShape) : Nat := (absRoundList s).length + tCommN s + 3
def baseOnC (s : StepShape) : Nat :=
  baseQN s + s.ipaRounds * s.ipaBlocks + s.ipaRounds + s.ipaBlocks + 1
def vOcX2At (b : Nat) (k : Nat) : PVar := xv (b + 2 * k)
def vOcX3At (b : Nat) (k : Nat) : PVar := xv (b + 2 * k + 1)
def vOcX2 (s : StepShape) (k : Nat) : PVar := vOcX2At (baseOnC s) k
def vOcX3 (s : StepShape) (k : Nat) : PVar := vOcX3At (baseOnC s) k

def baseDef (s : StepShape) : Nat := baseOnC s + 2 * nOnC s
/-- `ζ^{2^k}` in the deferred product (`k = 0..bRounds`). -/
def vZ (s : StepShape) (k : Nat) : PVar := xv (baseDef s + k)
/-- The factor `1 + u_k · ζ^{2^{bRounds−1−k}}`. -/
def vFac (s : StepShape) (k : Nat) : PVar := xv (baseDef s + s.bRounds + 1 + k)
/-- The running product after `k` factors; `vAcc bRounds` is `b(ζ)`. -/
def vAcc (s : StepShape) (k : Nat) : PVar := xv (baseDef s + 2 * s.bRounds + 1 + k)

def baseCip (s : StepShape) : Nat := baseDef s + 3 * s.bRounds + 2
/-- The claimed evaluation of column `k` at `ζ`. -/
def vEz (s : StepShape) (k : Nat) : PVar := xv (baseCip s + k)
/-- The claimed evaluation of column `k` at `ζω`. -/
def vEw (s : StepShape) (k : Nat) : PVar := xv (baseCip s + s.cipEvals + k)
/-- `r · evₖ(ζω)`. -/
def vDk (s : StepShape) (k : Nat) : PVar := xv (baseCip s + 2 * s.cipEvals + k)
/-- `cₖ = evₖ(ζ) + r · evₖ(ζω)` — the k-th coefficient of the ξ-weighted sum. -/
def vCk (s : StepShape) (k : Nat) : PVar := xv (baseCip s + 3 * s.cipEvals + k)
/-- The Horner intermediate `accᵢ · ξ`. -/
def vTk (s : StepShape) (i : Nat) : PVar := xv (baseCip s + 4 * s.cipEvals + i)
/-- The Horner accumulator after `i` steps; `vCa cipEvals` IS `combined_inner_product`. -/
def vCa (s : StepShape) (i : Nat) : PVar := xv (baseCip s + 5 * s.cipEvals + i)

/-! ### ⚑⚑ `combine`'s `Opt.Maybe` MUX — the cells, and the fact that decides their shape.

`combine` (`step_verifier.ml:1076-1090`) builds its list as

    List.append sg_evals ([| Some x_hat |] :: [| Some ft |] :: a)                    (:1094-1095)

where `sg_evals` is `List.map (fun (keep, eval) -> [| Plonk_types.Opt.Maybe (keep, eval) |])`
(`:1080-1083`) over the vector `:940-948` masks with `actual_width_mask =
branch_data.proofs_verified_mask` (`:916`) — §8h's two DERIVED bits. So prefix entries 0 and 1 are
`Maybe`, entries 2 … are `Some`, and `Common.combined_evaluation` folds them:

    | None       -> acc                                                             (common.ml:266-267)
    | Some fx    -> fx + (xi * acc)                                                 (:268-269)
    | Maybe (b, fx) -> Field.if_ b ~then_:(fx + (xi * acc)) ~else_:acc              (:270-271)

⚑⚑ **THE MUX IS A SKIP, NOT A ZERO, AND THAT IS THE WHOLE POINT OF THIS REGION.** The `else_` branch
is bare `acc` — it does NOT multiply by ξ. And `Pcs_batch.combine_split_evaluations`
(`pickles_types/pcs_batch.ml:85-94`) flattens the arrays, REVERSES, seeds `init` with the LAST
element and folds the rest left-to-right, so the list is Horner'd from its tail and **slot 0 is the
LAST step**. Dropping it therefore removes `c₀` AND removes one ξ power from every one of the other
46 terms. `combined_inner_product` at mask `[0,1]` is `cipR ξ r (ez.drop 1) (ew.drop 1)`, NOT
`cipR` over all 47 with entry 0 zeroed — those are different field elements.

⚠ So "slot 0 is the `Wrap_hack` dummy (`wrap_hack.ml:26-28` prepends dummies with
`Vector.extend_front_exn`), therefore dropping it is a no-op on the value" is FALSE. The dummy's
VALUE is irrelevant here; the ξ-power shift is not. §12l measures it at all three legal masks.

⚑ ONE mux per masked slot, where upstream runs two (`combine … + r * combine …`, `:1097-1101`).
That is the SAME fusion this region already runs — `cₖ = evₖ(ζ) + r·evₖ(ζω)` folded once instead of
two folds combined — and it commutes with `Field.if_` exactly, because both `combine` calls take the
SAME `keep` bit: `(b ? ez+ξC₁ : C₁) + r·(b ? ew+ξC₂ : C₂) = b ? (c+ξF) : F`. Stated here rather than
assumed, and pinned in §12l against `cipR` over the kept sub-list, which is the two-combine form. -/
/-- The `Maybe` entries of `combine`'s prefix: `sg_evals`' two slots. -/
def N_CIP_MASKED : Nat := 2
def baseCipM (s : StepShape) : Nat := baseCip s + 6 * s.cipEvals + 1
/-- `sⱼ = cⱼ + ξ·accᵢ` — `mul_and_add`'s `then_` branch (`common.ml:271`). -/
def vCs (s : StepShape) (j : Nat) : PVar := xv (baseCipM s + 3 * j)
/-- `dⱼ = sⱼ − accᵢ` — the `Field.if_` difference, §8e's own mux shape. -/
def vCd (s : StepShape) (j : Nat) : PVar := xv (baseCipM s + 3 * j + 1)
/-- `pⱼ = keepⱼ · dⱼ`, `keepⱼ` being `vMask j` — §8h's DERIVED bit, not a fresh witness. -/
def vCp (s : StepShape) (j : Nat) : PVar := xv (baseCipM s + 3 * j + 2)

/-! ### R6/R7 regions (§8d, §8e).

The absorption segments come FIRST and the ft program's slots LAST, because only the ft region's
size depends on a compiled program: every other base is a closed function of the shape. -/

def baseHm (s : StepShape) : Nat := baseCipM s + 3 * N_CIP_MASKED
/-- One of `hash_messages_for_next_step_proof`'s `Not_opt` prefix words — the 28 plonk-index
commitments as 56 coordinates that `sponge_after_index` swallowed, plus two app-state words. ⚑ The
count is EVEN because the `Opt` region must begin on a rate-2 block boundary: upstream's
`Opt_sponge` masks per FIELD ELEMENT, this segment's `Field.if_` mux is per BLOCK, and an odd
prefix would put a `Not_opt` word and an `Opt` word under one `keep` bit. -/
def vHm (s : StepShape) (i : Nat) : PVar := xv (baseHm s + i)
/-- `Plonk_verification_key_evals`' commitment count: `sigma_comm` 7 + `coefficients_comm` 15 + six
selectors (`plonk_verification_key_evals.ml:8-19`). -/
def N_IDX_COMMS : Nat := 28
/-- …as field elements, `Inner_curve.to_field_elements` flattened — `sponge_after_index`'s WHOLE
input (`step_verifier.ml:1149-1157`). -/
def N_IDX_WORDS : Nat := 2 * N_IDX_COMMS
/-- ⚑ The APP-STATE words, and since 2026-08-02 the only fixtures left in the `Not_opt` prefix.
`to_field_elements_without_index` puts `state_to_field_elements app_state` first; the app state is
the INDUCTIVE RULE's own statement and no `verify_one` sub-circuit derives it, so it is a witness
here and is named as one rather than counted as derived. -/
def N_HM_APP : Nat := 2
def N_HM_FIX : Nat := N_IDX_WORDS + N_HM_APP

/-! ### The PLONK-INDEX region (§3c) — `sponge_after_index`'s own variables.

Only the index commitments the FOLD does not already carry need variables of their own; the other
27 ARE `combine_split_commitments`' `.const` bases and segment C absorbs THOSE variables. The
region is allocated in full at every shape so no id moves when a round becomes available. -/
def baseIdx (s : StepShape) : Nat := baseHm s + N_HM_APP
def vIdxX (s : StepShape) (k : Nat) : PVar := xv (baseIdx s + 2 * k)
def vIdxY (s : StepShape) (k : Nat) : PVar := xv (baseIdx s + 2 * k + 1)
-- ⚑ `vIdxD` MOVED below `baseSegC` (2026-08-03): under Mina's lazy sponge `index_digest` is not a
-- permutation of its own but a LANE of the state segment C's index prefix already leaves behind, so
-- its three ids ARE segment C's state cells. The three slots here stay RESERVED so nothing moves.
def N_IDX_VARS : Nat := N_IDX_WORDS + 3

/-- Variables one sponge segment consumes: `3(nb+sq+1)` state lanes, `2·nb` post lanes, and for a
MASKED segment the `after`/`d`/`p`/`keep` mux cells. -/
def segVarCount (nb sq : Nat) : Nat := 3 * (nb + sq + 1) + 2 * nb + 9 * nb + nb

def baseSegA (s : StepShape) : Nat := baseIdx s + N_IDX_VARS
/-- Segment A (the opt-sponge): `2·bRounds` masked words, one squeeze. -/
def nbA (s : StepShape) : Nat := (2 * s.bRounds + 1) / 2
def baseSegB (s : StepShape) : Nat := baseSegA s + segVarCount (nbA s) 1
/-- ⚑ Segment B (the fr-sponge): **the SEED**, the challenge digest, `ft_eval1`, `p(ζ)`, `p(ζω)` and
the 43 columns at both points, two squeezes (ξ′ and r′).

⚑ **THE FIVE-WORD PREFIX IS FIVE SINCE 2026-08-03 (§22).** It was four: `finalize_other_proof`'s own
absorbs (`step_verifier.ml:962-965`) start at `challenge_digest`, and this segment started there too
— but the sponge `finalize_other_proof` is HANDED is not a fresh one. `step_main.ml:41-46` creates it
and absorbs `proof_state.sponge_digest_before_evaluations` FIRST, so the fr-sponge's first word is
Wrap statement word 10 and every squeeze off this segment is a function of it. -/
def SEG_B_PREFIX : Nat := 5
def nbB (s : StepShape) : Nat := (SEG_B_PREFIX + 2 * (s.cipEvals - 4) + 1) / 2
def baseSegC (s : StepShape) : Nat := baseSegB s + segVarCount (nbB s) 2
/-- Segment C (the INNER `hash_messages_for_next_step_proof_opt`, `step_main.ml:66-81`), one
squeeze. `N_HM_FIX` prefix words + two slots of `(commitment ×2, bRounds challenges)`. -/
def nbC (s : StepShape) : Nat := (N_HM_FIX + 2 * (2 + s.bRounds) + 1) / 2

/-- ⚑⚑ **`index_digest` COSTS NO PERMUTATION OF ITS OWN** (2026-08-03). `index_digest =
Sponge.squeeze_field (Sponge.copy sponge_after_index)` (`step_verifier.ml:529-534`), and
`sponge_after_index` has absorbed `N_IDX_WORDS = 56` field elements — an EVEN count, so it sits at
`Absorbed 2` with the last pair pending and the 28th permutation NOT yet performed. The copy's
`squeeze` is the `Absorbed _` arm (`sponge.ml:322-325`): it performs exactly that pending
permutation and returns `state.(0)`.

Segment C's block `N_IDX_WORDS / 2 = 28` is entered on precisely that state, so `vIdxD j` IS
`sgSt (baseSegC s) … 28 j` — the same three variables, one σ class, **no rows**. The old model
emitted an EXTRA `permBlockRows` here (`idxDigestRows`) and read `perm idxAfterState`, i.e. a
29th permutation `verify_one` never performs.

⚑ The named equality `indexDigest = PastaPoseidon.Ref.hash …` (§12s) is the reality gate for this:
`Ref.hash` is the o1js-KAT'd lazy machine, and the pre-fix value fails it. -/
def vIdxD (s : StepShape) (j : Nat) : PVar :=
  xv (baseSegC s + 3 * (N_IDX_WORDS / 2) + j)

/-- ⚑ Segment D — the **OUTER** `hash_messages_for_next_step_proof` (`step_main.ml:525-566`). It is
a `Sponge.copy` of `sponge_after_index` (`step_verifier.ml:1162-1164`), so it re-absorbs NONE of the
28 index commitments: its words are the app state and, per previous proof of THIS rule, the wrap
proof's `opening.challenge_polynomial_commitment` (`:534`) followed by that proof's computed
`bulletproof_challenges` (`:563-565`, unpadded). This file assembles ONE `verify_one`, so
`V.f proofs_verified` (`:538`) is one slot. -/
def baseSegD (s : StepShape) : Nat := baseSegC s + segVarCount (nbC s) 1
def nbD (s : StepShape) : Nat := (N_HM_APP + 2 + s.bRounds + 1) / 2

/-- The OUTER hash's own witnesses: its two app-state words (`step_main.ml:550-557` — the rule's
OUTPUT state, a different object from the previous proof's `app_state` segment C absorbs) and the
previous proof's `challenge_polynomial_commitment`. -/
def baseOut (s : StepShape) : Nat := baseSegD s + segVarCount (nbD s) 1
def vHmO (s : StepShape) (i : Nat) : PVar := xv (baseOut s + i)
/-- ⚑ **`G`** — `acc.wrap_proof.opening.challenge_polynomial_commitment` (`step_main.ml:534`), the
very field `check_bulletproof` destructures at `step_verifier.ml:253` and uses at `:333`. Until this
rung it occurred in this assembly NOWHERE (§17); it is now `Inner_curve.typ`-checked (§7b) and
absorbed by segment D, whose squeeze is the step statement's public `messages_for_next_step_proof`.
⚠ `check_bulletproof`'s `rhs` is still NOT emitted, so no row here relates `G` to the opening. -/
def vGx (s : StepShape) : PVar := xv (baseOut s + N_HM_APP)
def vGy (s : StepShape) : PVar := xv (baseOut s + N_HM_APP + 1)
def N_OUT_VARS : Nat := N_HM_APP + 2

-- ⚠ ⚑ **`G_XY` was DELETED 2026-08-03 (§19).** `G` was a fixture point (`GAMMA_XY[27]`) because
-- nothing in the assembly related it to anything. §19's `rhs`/`equal_g` do relate it: `G` is now
-- `solveG`'s output, a FUNCTION of `lhs`, and it lives on `StepData.gXY`. A constant here would be a
-- second `G` that the opening does not close, and R8's `Boolean.all` would refuse the honest witness.

/-- The OUTER hash's two app-state words — `rule.main`'s OUTPUT state (`step_main.ml:550-557`),
which no `verify_one` sub-circuit derives. A distinct fixture from segment C's `hmVal`, because it
is a distinct object: segment C's is the PREVIOUS proof's app state. -/
def hmOVal (i : Nat) : Nat := (23 + 5000011 * i + 11 * i * i) % pN

/-! ### The STATEMENT words R8 binds (§8f).

Upstream these are the Wrap proof-state's `Deferred_values` — `combined_inner_product`, `b` and
`plonk.perm` in `Shifted_value.Type1` form, and the `Scalar_challenge` `xi` — carried in the step
circuit's statement and CHECKED against what the circuit recomputes. They are exposed as the first
four public words, so a prover who supplies a different deferred value is refused by R8's
`Boolean.all` assert rather than believed. ⚠ In rungs r5–r7 (below the rung that checks them) they
are statement inputs and nothing else; r8 is the rung that binds them. -/
def baseStmt (s : StepShape) : Nat := baseOut s + N_OUT_VARS
/-- `combined_inner_product`, `Shifted_value.Type1`. -/
def vCipShift (s : StepShape) : PVar := xv (baseStmt s)
/-- `b`, `Shifted_value.Type1`. -/
def vBShift (s : StepShape) : PVar := xv (baseStmt s + 1)
/-- `plonk.perm`, `Shifted_value.Type1` (`Plonk_checks.checked` compares the SHIFTED words). -/
def vPermShift (s : StepShape) : PVar := xv (baseStmt s + 2)
/-- `xi`'s RAW prechallenge — `xi_correct` compares it against the fr-sponge's own squeeze, and
§8g's chain `0` LIFTS it into the multiplier the C8 fold uses. -/
def vXiStmt (s : StepShape) : PVar := xv (baseStmt s + 3)

/-! ⚑ **`branch_data`, the fifth statement word** (`step_main.ml:53,70-72`;
`composition_types/branch_data.ml:88-101`). It is ONE field element that PACKS the two
`Proofs_verified.Prefix_mask` bits and `domain_log2`:

    Checked.pack {proofs_verified_mask; domain_log2} = 4·domain_log2 + pack(mask)

and `Vector.trim_front branch_data.proofs_verified_mask` is what gates the opt-sponge's absorptions.
§8h emits `pack` as rows, so the mask bits are Boolean circuit VARIABLES tied to a statement word
rather than a constant pattern — the retirement of the module header's simplification #9. -/
def vBranch (s : StepShape) : PVar := xv (baseStmt s + 4)
/-- `domain_log2`, the packed word's high part. -/
def vDomLog2 (s : StepShape) : PVar := xv (baseStmt s + 5)
/-- `proofs_verified_mask ! i` — a Boolean variable. `Prefix_mask.there` is
`N0 ↦ [ff;ff] · N1 ↦ [ff;tt] · N2 ↦ [tt;tt]` (`pickles_base/proofs_verified.ml:75-81`), so the SET
bits are a SUFFIX: with one previous proof it is slot 1 that is kept, not slot 0. -/
def vMask (s : StepShape) (i : Nat) : PVar := xv (baseStmt s + 6 + i)
/-- The mask's own packing `m₀ + 2·m₁`, `Checked.pack`'s inner `pack`. -/
def vMaskPack (s : StepShape) : PVar := xv (baseStmt s + 8)
/-- ⚑ **`should_verify`, and it is a STATEMENT BOOL and not a witness.**
`step_main.ml:36-37` opens `verify_one` with `Boolean.Assert.( = )
unfinalized.should_finalize should_verify`, and `should_finalize` is a field of
`Types.Step.Proof_state.Per_proof.In_circuit` whose `spec` puts it in the `bool` list
(`composition_types.ml:1219,1310`) — i.e. it is part of the STEP STATEMENT, hence public.
Until 2026-08-02 this file made it an `AOp.wit`: the prover could set it to 0 and R8's
`verified && finalized ||| not should_verify` assert passed with ALL FOUR deferred bindings
false. §16g exhibits that. It is now a statement word, tied by a closing row like the other
four, so the mux branch is a PUBLIC CLAIM a consumer reads rather than a prover's private
choice — which is exactly upstream's semantics for a dummy previous proof. -/
def vShouldVerify (s : StepShape) : PVar := xv (baseStmt s + 9)
/-! ⚑⚑ **`advice.combined_inner_product`'s BIT — DERIVED SINCE 2026-08-03, and the id here is now
UNUSED.** `xv (baseStmt s + 10)` used to be `vCipBit`, an `Fq`-side companion bit with a value
constant `CIP_BIT = 0` whose ONLY constraints were `Boolean.typ`'s `b² = b` and the transcript
absorb. Booleanity is not a derivation: the prover had TWO transcripts, and every squeeze after
`combined_inner_product` (`u`, the fifteen prechallenges, `c`) moved with the bit.

⚑ **THE CLOSURE COSTS NO ROW AT ALL, because upstream's two uses are ONE OBJECT.**
`absorb sponge Scalar advice.combined_inner_product` (`step_verifier.ml:256-259`) destructures the
SAME `Other_field.t = (Field.t * Boolean.var)` pair that `scale_fast2 u advice.combined_inner_product`
(`:317`) consumes — `absorb_scalar (x, b)` at `:79-81` feeds `Field x` then `Bits [b]`, and
`plonk_curve_ops.ml:251-253` names that pair `(s_div_2, s_odd)`. §19's ladder 0 ALREADY emits that
pair, its `Field.Assert.equal (2·s_div_2 + s_odd) s` split row (`plonk_curve_ops.ml:290-291`, the
`split_field` shape of `wrap_main.ml:69-81`) against `vCipShift`, and the ladder's own
`bits_lsb.(254) = 0` assert. So `vCipBit` is now DEFINED as `bpOdd s 0` (§19's region) and the
transcript absorbs the parity the split row forces, not a free cell.

⚠ **AND SAY THE RESIDUAL, because the split row alone does not make the bit unique.** `2·h + b ≡ x
(mod p)` with `b` boolean and `h < 2^254` (which is all the ladder's top-bit assert gives) admits
BOTH parities for all but a ~2^−128 fraction of `x`: the wrong-parity solution is
`h = (x − b + p)/2 < 2^254` whenever `x < p − 2δ`, and `δ = p − 2^254 ≈ 2^125.1`. What CHANGED is
that the bit is no longer free of the assembly: flipping it now moves `bpDiv2 0`, hence `uc`, hence
`q`, hence `lhs` — so the second transcript costs the prover a re-solved `G` rather than nothing.
**Upstream's gadget has exactly this residual** (`wrap_main.ml:64-67` defers the fit-check to
`scale_fast2`, which checks 254 bits and not `< p/2`), so this is a fidelity match and NOT a proof
that one transcript remains. -/

/-! ### ⚑ The Wrap statement words with no in-circuit source — TWO since §22, and word 10 is gone.

`multiscale_known`'s scalars are the packed Wrap statement, forty words. Twenty-nine of them are
variables this assembly DERIVES (§2c's `stmtVar`); nine are the one-bit words, which emit no ladder
at all; **two are not here, and each one is a named absence rather than a wire to something
convenient.** They get their own cells so that the MSM's σ class for word `i` is word `i`'s and not
some unrelated challenge's.

  * ✅ **word 10 — `sponge_digest_before_evaluations` — CLOSED 2026-08-03 (§22).** It had a cell
    (`vStmtDigest`) and no source. It has neither now: `stmtVar 10` is `digestBeforeEvalsVar`, the
    transcript's OWN lane-1 cell at ζ's squeeze (`step_verifier.ml:573-574`), and segment B's first
    absorbed word is that same cell (`step_main.ml:41-46`). Derived AND consumed; see §2b/§8e.
  * **word 11 — `messages_for_next_wrap_proof`.** `step_main.ml:85` SUBSTITUTES it into the
    statement from `verify_one`'s own argument (`:35`), and that argument is
    `exists (Vector.typ Digest.typ Max_proofs_verified.n) ~request:Req.Messages_for_next_wrap_proof`
    at **`step_main.ml:364-366`** — a REQUESTED WITNESS of the whole step circuit. ⚑ So this is not
    an absence in this assembly: upstream derives it nowhere either, and its ONLY in-circuit consumer
    upstream is the same x_hat ladder it has here. **Faithful as it stands; nothing to land.**
  * **word 39 — the lookup `Opt`'s inner `Scalar Challenge`** (`spec.ml:94-99,123-141`,
    `composition_types.ml:655-666`). This assembly models no lookup. ⚠ Read at source, `Spec.pack`'s
    `Opt` `None` arm packs `dummy2` — `Sc.create lookup_parameters.zero.var.challenge`, which
    `step_main.ml:91` sets to `Field.zero` — and a `` `Packed_bits (Constant 0, _) `` is dropped by
    `multiscale_known`'s partition (`step_verifier.ml:138-140`), which would make word 39 a CONSTANT
    with no ladder at all. **That inference is REFUTED by Mina's own compiled circuit**, whose x_hat
    cluster is `2×1 26×22 51×8` = 31 ladders, 982 chunks: `51×8` is words 0–4 and 10–12, `2×1` is
    word 29, and `26×22` is the five challenge words, the sixteen bulletproof words **and one more**
    — word 39. So the `None` arm is not what `step-zkapp-proved` compiles, the word is a live
    26-chunk ladder, and landing it needs the lookup sub-circuit this assembly does not have.

⚠ So TWO of the forty x_hat scalars are prover-chosen here, one of which (11) is prover-chosen
upstream too. -/
/-- Wrap statement word 11 — see the note above. -/
def vStmtWrapMsgs (s : StepShape) : PVar := xv (baseStmt s + 11)
/-- Wrap statement words 30..38 — the eight `Plonk_types.Features` flags and the lookup `Opt`'s own
flag bit. `msmChunksAt = 0` on all nine, so NO row ever reads these cells; they exist so that
`stmtVar` is total and injective on the statement rather than folding nine words onto one name. -/
def vStmtFlag (s : StepShape) (k : Nat) : PVar := xv (baseStmt s + 12 + k)
/-- Wrap statement word 39 — see the note above. -/
def vStmtLookup (s : StepShape) : PVar := xv (baseStmt s + 21)
def N_STMT : Nat := 22

/-! ### ⚑ `prev_challenges` — the PREVIOUS proofs' carried bulletproof challenges.

`step_verifier.ml:953-959` (`Opt_sponge.absorb opt_sponge (keep, chal)` over `prev_challenges`) and
`step_main.ml:80` (`old_bulletproof_challenges = prev_challenges`): segments A and C absorb THE SAME
vector, and it is a field of `Per_proof_witness` — the previous proof's own statement, checked by
`verified` (#11) and by nothing in `verify_one`.

⚠ ⚑ **THIS RETIRES A FALSE WIRE, AND THE TRADE IS STATED RATHER THAN QUIET.** Until 2026-08-02
`optSpec` and `hmSpec` absorbed `vN s (i % chals) emsRows` — R1's OWN transcript challenges — for
these `2·bRounds` words. Upstream those two vectors have no relationship: `prev_challenges` come from
the previous proof's statement, not from this transcript. That false wire cost more than fidelity: it
made segment A, hence the fr-sponge, hence ξ and r, hence `combined_inner_product` a function of
EVERY transcript challenge — so absorbing `cip` into the transcript at ANY position was a cycle, and
the interleaving alone would not have fixed it. What is LOST is that these words were derived cells
and are now witnesses; what is GAINED is that they are the ones upstream has, and that `cip` can be
absorbed. Both segments read the SAME variables, so they are still one σ class across two sponges and
segment C's public digest moves when one is bent. -/
def basePrevC (s : StepShape) : Nat := baseStmt s + N_STMT
/-- Carried challenge `i` — proof `i / bRounds`, round `i % bRounds`. -/
def vPrevChal (s : StepShape) (i : Nat) : PVar := xv (basePrevC s + i)
/-- A deterministic fixture standing for one carried challenge. -/
def prevChalVal (i : Nat) : Nat := (19 + 4000037 * i + 7 * i * i) % pN

/-! ### The DEFERRED challenges ξ and r (§8g) — the fold's own multipliers.

`step_verifier.ml:1006-1013`, verbatim:

    let squeeze () = squeeze_challenge sponge in
    let xi_actual = squeeze () in
    let r_actual  = squeeze () in
    let xi_correct = Field.equal xi_actual (match xi with { inner = xi } -> xi) in
    let xi = scalar xi in
    let r  = scalar (Import.Scalar_challenge.create r_actual) in

so the ξ the C8 fold multiplies by is `to_field_checked` of **the statement's ξ word** — the word
`xi_correct` ties to the fr-sponge's FIRST squeeze — and the `r` it (and `b_correct`) multiplies by
is `to_field_checked` of the fr-sponge's **SECOND squeeze**, with no statement word at all. Each
gets its own `to_field_checked` chain; chain `0` is ξ and chain `1` is r. ⚑ This is the retirement
of the module header's simplification #10: before it, both were R1 transcript challenges and the
fr-sponge squeeze fed NOTHING but `xi_correct`. -/
def N_DEFC : Nat := 2
/-- One deferred chain's variable block: `n/a/b` at every `EndoMulScalar` row boundary, the
`lowest_128_bits` high part, and the lift's two cells. -/
def defcStride (s : StepShape) : Nat := 3 * (s.emsRows + 1) + 3
def baseDefC (s : StepShape) : Nat := basePrevC s + 2 * s.bRounds
def vDN (s : StepShape) (c k : Nat) : PVar := xv (baseDefC s + c * defcStride s + k)
def vDA (s : StepShape) (c k : Nat) : PVar :=
  xv (baseDefC s + c * defcStride s + (s.emsRows + 1) + k)
def vDB (s : StepShape) (c k : Nat) : PVar :=
  xv (baseDefC s + c * defcStride s + 2 * (s.emsRows + 1) + k)
/-- The discarded high part. Chain `0` has none — its source is already a `Challenge.t`. -/
def vDHi (s : StepShape) (c : Nat) : PVar :=
  xv (baseDefC s + c * defcStride s + 3 * (s.emsRows + 1))
def vDLiftT (s : StepShape) (c : Nat) : PVar :=
  xv (baseDefC s + c * defcStride s + 3 * (s.emsRows + 1) + 1)
/-- ⚑ **THE FOLD'S OWN MULTIPLIER.** `vDLift 0` is ξ and `vDLift 1` is r: the variables `cipRows`
Horners over and scales its `evₖ(ζω)` leg by, and the one `b_correct` weights `challenge_poly ζω`
with. Nothing else in the assembly plays those two roles. -/
def vDLift (s : StepShape) (c : Nat) : PVar :=
  xv (baseDefC s + c * defcStride s + 3 * (s.emsRows + 1) + 2)

/-! ### The `assert_128_bits hi` CHAINS (§5b) — simplification #1.

`lowest_128_bits ~constrain_low_bits x` (`util.ml:78-101`) witnesses `(lo, hi)`, asserts
`x = lo + 2¹²⁸·hi`, and RANGE-CHECKS BOTH PARTS — and `assert_n_bits ~n:128`
(`step_verifier.ml:88-97`) is not a bespoke gadget, it is
`ignore (SC.to_field_checked … ~num_bits:128)`: the `EndoMulScalar` chain runs and emits every one
of its rows, only the returned field element is dropped. So the range check IS a second
`to_field_checked`, and `tfcRows` emits it unchanged.

⚑ WHY IT IS A SOUNDNESS HOLE AND NOT A ROW COUNT. Without the `hi` chain, the decomposition row is
ONE equation in TWO unknowns with only `lo` constrained: for ANY `lo' < 2¹²⁸` the prover can solve
`hi' = (x − lo')·2^{−128}` and hand `lo'` to the rest of the circuit. The Fiat-Shamir challenge
becomes prover-chosen outright. §12c exhibits exactly that witness and shows this chain refuses it.

One block per SPLIT source: R2's `chals` transcript squeezes and §8g's chain `1` (`r`, the
fr-sponge's second squeeze). §8g's chain `0` has no block — its source is already a `Challenge.t`,
so upstream splits nothing there either. -/
def rngStride (s : StepShape) : Nat := 3 * (s.emsRows + 1) + 3
def baseRng (s : StepShape) : Nat := baseDefC s + N_DEFC * defcStride s
/-- Range chain `c`: `c < chals` is transcript challenge `c`'s high part, `chals + d` is deferred
chain `d`'s. -/
def vRN (s : StepShape) (c k : Nat) : PVar := xv (baseRng s + c * rngStride s + k)
def vRA (s : StepShape) (c k : Nat) : PVar :=
  xv (baseRng s + c * rngStride s + (s.emsRows + 1) + k)
def vRB (s : StepShape) (c k : Nat) : PVar :=
  xv (baseRng s + c * rngStride s + 2 * (s.emsRows + 1) + k)
def vRHi (s : StepShape) (c : Nat) : PVar :=
  xv (baseRng s + c * rngStride s + 3 * (s.emsRows + 1))
def vRLiftT (s : StepShape) (c : Nat) : PVar :=
  xv (baseRng s + c * rngStride s + 3 * (s.emsRows + 1) + 1)
def vRLift (s : StepShape) (c : Nat) : PVar :=
  xv (baseRng s + c * rngStride s + 3 * (s.emsRows + 1) + 2)
/-- **R8's `lowest_128_bits`, high part.** `xi_actual = lowest_128_bits (squeeze fr_sponge)`
(`step_verifier.ml:821-822`; `lowest_128_bits` is `:99-101`, `Util.lowest_128_bits` `util.ml:78-101`)
is decomposed INSIDE the compiled finalize program (§8f), where
its high part is an `AOp.wit` — a cell with no defining row. `Util.lowest_128_bits` asserts
`assert_128_bits hi` UNCONDITIONALLY (`util.ml:98`), and this is that chain. -/
def RNG_FIN_HI (s : StepShape) : Nat := s.chals + N_DEFC
/-- **…and its LOW part.** `Opt_sponge.squeeze_challenge` passes `~constrain_low_bits:true`
(`step_verifier.ml:821-822`), so `util.ml:99` asserts the low part too. -/
def RNG_FIN_LO (s : StepShape) : Nat := s.chals + N_DEFC + 1
/-- ⚑ **`Branch_data`'s `~assert_16_bits`** (`per_proof_witness.ml:166-168`,
`composition_types/branch_data.ml:110-127`): `Branch_data.typ`'s `check` is
`Step_verifier.assert_n_bits ~n:16` on the PACKED word's `domain_log2`, i.e. one more
`to_field_checked` — at **16 bits, hence ONE `EndoMulScalar` row**, not `emsRows`. Until 2026-08-03
this assembly emitted none, and `branchRows`' single equation `4·domLog2 + maskPack = branch_data`
was one equation in three unknowns: the prover picked both mask bits and solved for `domLog2`. With
the suffix constraint below the mask has three legal values, and this chain refuses two of the three
`domLog2` they imply — because `(branch_data − maskPack)/4` is a small integer for exactly one of
them and a full-width field element for the others. Together they PIN the triple. -/
def RNG_DOMLOG2 (s : StepShape) : Nat := s.chals + N_DEFC + 2
/-- Rows of the `domain_log2` chain — `~n:16` over 8 crumbs. -/
def RNG_DOMLOG2_ROWS : Nat := 1
/-- One block per split source; the ξ chain's block is allocated and unused, so no id moves when a
future rung splits it. Two are R8's, over the fr-sponge's FIRST squeeze; the last is
`Branch_data`'s 16-bit check, which uses only the first of its `emsRows` row slots. -/
def nRng (s : StepShape) : Nat := s.chals + N_DEFC + 3

/-! ### `Common.ft_comm`'s MSM region (§6b) — the `scale_fast2` variables.

One block per `scale_fast2` term (`ftcStride`), then the shared globals. ⚑ The region owns NO base
variables except `t_comm`'s: term 0's base is `sigma_comm_last`, which is §3c's own pinned
`vIdxX/vIdxY 6`; term 1's is `t_comm[n−1]`, whose two variables ARE transcript block `l+1`'s absorbed
words; and every later term's base is the PREVIOUS `Ops.add_fast`'s output. -/
def baseFtc (s : StepShape) : Nat := baseRng s + nRng s * rngStride s

/-- One `scale_fast2` term's variables: `FTC_CHUNKS+1` accumulator points, `FTC_CHUNKS` counter
boundaries (the last is the scalar's own `s_div_2`, shared), the top bit `scale_fast2` asserts zero,
the base's negated `y`, the `s_odd = 0` branch point, and `G.if_`'s three cells per coordinate. -/
def ftcStride : Nat := 2 * (FTC_CHUNKS + 1) + FTC_CHUNKS + 1 + 1 + 2 + 2 + 2 + 2

/-- ⚑ `Shifted_value.Type2`'s DISTINCT scalars: `0` is `plonk.perm`, `1` is
`plonk.zeta_to_srs_length` — which at `log2n = srs_length_log2 = 16` IS `plonk.zeta_to_domain_size`
(`plonk_checks.ml:496-497`), so the Horner steps and the closing scale share ONE pair. Upstream
shares it too: `scale_fast2` takes the already-split pair, so `common.ml` splits nothing per scale. -/
def N_FTC_SCAL : Nat := 2
/-- Term `k`'s scalar block. -/
def ftcScalOf (k : Nat) : Nat := if k == 0 then 0 else 1

def ftcAccX (s : StepShape) (k j : Nat) : PVar := xv (baseFtc s + k * ftcStride + 2 * j)
def ftcAccY (s : StepShape) (k j : Nat) : PVar := xv (baseFtc s + k * ftcStride + 2 * j + 1)
/-- Term `k`'s block base offset for the non-accumulator cells. -/
def ftcOff (s : StepShape) (k : Nat) : Nat := baseFtc s + k * ftcStride + 2 * (FTC_CHUNKS + 1)
/-- `scale_fast2`'s TOP BIT — `bits_lsb.(254)`, which `plonk_curve_ops.ml:262-265` asserts zero. It
is chunk 0's MSB, so it is a wired permutation cell of that chunk's `Zero` row and a `Generic` row
pins it. Without it the counter equation has TWO solutions mod `p` and the prover picks. -/
def ftcTop (s : StepShape) (k : Nat) : PVar := xv (ftcOff s k + FTC_CHUNKS)
/-- `Inner_curve.negate g`'s `y` — the odd-branch `add_fast h (G.negate g)` (`:267`). -/
def ftcNegY (s : StepShape) (k : Nat) : PVar := xv (ftcOff s k + FTC_CHUNKS + 1)
def ftcHmX (s : StepShape) (k : Nat) : PVar := xv (ftcOff s k + FTC_CHUNKS + 2)
def ftcHmY (s : StepShape) (k : Nat) : PVar := xv (ftcOff s k + FTC_CHUNKS + 3)
/-- `G.if_`'s `then_ − else_` (`h − (h−g)`), per coordinate. -/
def ftcDX (s : StepShape) (k : Nat) : PVar := xv (ftcOff s k + FTC_CHUNKS + 4)
def ftcDY (s : StepShape) (k : Nat) : PVar := xv (ftcOff s k + FTC_CHUNKS + 5)
/-- …and `s_odd · (then_ − else_)`. -/
def ftcMX (s : StepShape) (k : Nat) : PVar := xv (ftcOff s k + FTC_CHUNKS + 6)
def ftcMY (s : StepShape) (k : Nat) : PVar := xv (ftcOff s k + FTC_CHUNKS + 7)
/-- Term `k`'s `scale_fast2` OUTPUT. -/
def ftcResX (s : StepShape) (k : Nat) : PVar := xv (ftcOff s k + FTC_CHUNKS + 8)
def ftcResY (s : StepShape) (k : Nat) : PVar := xv (ftcOff s k + FTC_CHUNKS + 9)

def baseFtcG (s : StepShape) : Nat := baseFtc s + ftcTerms s * ftcStride
/-- ⚑ **`t_comm` chunk `i`'s coordinates — and they are TRANSCRIPT WORDS.** `receive without t_comm`
(`step_verifier.ml:567`) absorbs them; `Common.ft_comm`'s Horner consumes them. One σ class spanning
the `Poseidon` sponge, `assert_on_curve` and this MSM's `VarBaseMul` chain. -/
def vTcX (s : StepShape) (i : Nat) : PVar := xv (baseFtcG s + 2 * i)
def vTcY (s : StepShape) (i : Nat) : PVar := xv (baseFtcG s + 2 * i + 1)
/-- `Ops.add_fast` output `a` (`a = 0 .. tCommN−1`): the `n−1` Horner partials `resₙ₋₂₋ₐ`, then
`f_comm + chunked_t_comm`. The LAST add's output is not here — it is the fold's own round-`FTC_ROUND`
base variable. -/
def ftcAddX (s : StepShape) (a : Nat) : PVar := xv (baseFtcG s + 2 * tCommN s + 2 * a)
def ftcAddY (s : StepShape) (a : Nat) : PVar := xv (baseFtcG s + 2 * tCommN s + 2 * a + 1)
/-- `negate (scale chunked_t_comm zeta_to_domain_size)`'s `y` (`common.ml:256`). -/
def ftcNegQ (s : StepShape) : PVar := xv (baseFtcG s + 4 * tCommN s)
/-- `Shifted_value.Type2`'s `s_div_2` — and the cell the ladder's FINAL counter IS. -/
def ftcDiv2 (s : StepShape) (c : Nat) : PVar := xv (baseFtcG s + 4 * tCommN s + 1 + 2 * c)
/-- …and its `s_odd`, a `Boolean.var`. -/
def ftcOdd (s : StepShape) (c : Nat) : PVar := xv (baseFtcG s + 4 * tCommN s + 2 + 2 * c)
/-- Term `k`'s counter at chunk boundary `j`. At `j = FTC_CHUNKS` it IS the scalar's `s_div_2`
variable — `Field.Assert.equal !n_acc scalar` (`plonk_curve_ops.ml:208`), the wire that makes the
ladder multiply by the value R6 derived and not by one the prover picked. -/
def ftcN (s : StepShape) (k j : Nat) : PVar :=
  if j == FTC_CHUNKS then ftcDiv2 s (ftcScalOf k) else xv (ftcOff s k + j)
def nFtcVars (s : StepShape) : Nat :=
  ftcTerms s * ftcStride + 4 * tCommN s + 1 + 2 * N_FTC_SCAL

/-! ### ⚑⚑ §8i — `sg_olds` / `sg_evals`: the ACCUMULATOR CHECK's FIRST LEG, and its variables.

READ AT SOURCE, and this is the whole of it (`step_verifier.ml:934-948`, verbatim in shape):

    let zetaw = Field.mul domain#generator plonk.zeta in                            (* :934 *)
    let sg_olds =
      Vector.map prev_challenges ~f:(fun chals ->
          unstage (challenge_polynomial (Vector.to_array chals))) in                (* :935-939 *)
    let sg_evals1, sg_evals2 =
      let sg_evals pt =
        Vector.map2 ~f:(fun keep f -> (keep, f pt))
          (Vector.trim_front actual_width_mask …) sg_olds in
      (sg_evals plonk.zeta, sg_evals zetaw)                                          (* :940-948 *)

and `challenge_polynomial ~one ~add ~mul chals = stage (fun pt →
∏_i (1 + chals.(i) · pt^{2^{k−1−i}}))` (`wrap_verifier.ml:16-35`, reached through
`step_verifier.ml:655-657`). Those two vectors are `combine`'s OWN PREFIX
(`:1076-1102`, `List.append sg_evals ([| Some x_hat |] :: [| Some ft |] :: a)`) — i.e. exactly
`EV_PREFIX`'s first two entries at both points, which is why this region's four outputs ARE
`vEz 0/1` and `vEw 0/1` rather than four cells that feed them.

⚑ **WHAT `per_proof_witness.ml:12-32` SAYS THIS IS.** "…we get an evaluation `E_c` at a random point
zeta and check that `challenge_polynomial_commitment` **opens** to `E_c` at zeta. Then we will need
to check that `E_c = f_c(zeta)`." So `E_c` is these four values and the accumulator check is TWO
legs. **This region is leg ONE and only leg one**; leg two (the opening) is `verified` (#11), a
witnessed boolean, and §18(g) says so where it is measured.

⚠ ⚑ **THE VECTOR IS `prev_challenges` AND NOT THIS PROOF'S OWN, and upstream says it in a comment**:
`step_verifier.ml:918` — *"You use the NEW bulletproof challenges to check b. Not the old ones."* —
which is the same sentence read from the other side. `b_correct` (§8f) folds `bulletproof_challenges`
(`:1114-1121`, `finalize_other_proof`'s RETURNED vector, the one segment D absorbs); `sg_olds` folds
`prev_challenges` (`:937`, `Per_proof_witness.t`'s carried field, the one segments A and C absorb).
**Conflating them would close this leg vacuously**, and §18(f) pins the two values apart so that a
future conflation goes red rather than green.

⚑ THE POINT LADDER IS SHARED AND THE PRODUCT LADDERS ARE NOT, which is a deviation and is stated
here rather than in a footnote. Upstream's `challenge_polynomial` is `stage`d and re-`unstage`d per
(vector, point), so it recomputes `pow_two_pows` in each of the four calls; this region computes
`ζ^{2^j}` ONCE (it reuses §8's own `vZ`, which the `b(ζ)` ladder already owns) and `(ζω)^{2^j}` once.
Sharing MERGES σ classes rather than splitting them — strictly fewer free cells, never more — and
the four PRODUCTS, which are what the challenge vectors reach, are four separate chains. -/
def baseEc (s : StepShape) : Nat := baseFtc s + nFtcVars s
/-- ⚑ `domain#generator`, pinned by one `Generic` half so `ζω` is a MULTIPLICATION by a wired
constant rather than a coefficient baked into a bespoke selector shape. -/
def vOmegaC (s : StepShape) : PVar := xv (baseEc s)
/-- ⚑ **`zetaw` (`step_verifier.ml:934`) at `k = 0`, and `(ζω)^{2^k}` above it.** ONE `zetaw`
variable, because upstream has one: `:934` binds it, `:948` evaluates `sg_evals` at it and `:1124`
folds `b_correct`'s second leg over it. §8f's program now READS this cell instead of recomputing
`ω·ζ` in its own slot. -/
def vZW (s : StepShape) (k : Nat) : PVar := xv (baseEc s + 1 + k)
/-- The four `sg_evals` ladders: `l = 2·slot + point`, point `0` = ζ and `1` = ζω. -/
def N_EC : Nat := 4
def ecSlot (l : Nat) : Nat := l / 2
def ecPoint (l : Nat) : Nat := l % 2
/-- One ladder's own cells: `bRounds` factors and the `bRounds − 1` interior products (the seed is
the shared constant-1 cell, the output is `vEz`/`vEw`). -/
def ecStride (s : StepShape) : Nat := 2 * s.bRounds - 1
def baseEcL (s : StepShape) : Nat := baseEc s + 1 + s.bRounds
/-- Ladder `l`'s factor `1 + c_k·pt^{2^{bRounds−1−k}}`. -/
def vEcFac (s : StepShape) (l k : Nat) : PVar := xv (baseEcL s + l * ecStride s + k)
/-- ⚑ Ladder `l`'s OUTPUT — `E_c` for slot `l/2` at point `l%2`, which IS `combine`'s prefix entry
and not a cell that feeds one. -/
def vEcOut (s : StepShape) (l : Nat) : PVar :=
  if ecPoint l == 0 then vEz s (ecSlot l) else vEw s (ecSlot l)
/-- Ladder `l`'s running product after `k` factors. `k = 0` is §8's own constant-1 cell (one
constant, five consumers, one σ class); `k = bRounds` is the output. -/
def vEcAcc (s : StepShape) (l k : Nat) : PVar :=
  if k == 0 then vAcc s 0
  else if k == s.bRounds then vEcOut s l
  else xv (baseEcL s + l * ecStride s + s.bRounds + (k - 1))
/-- The point's power ladder: ζ's is §8's `vZ`, ζω's is this region's own. -/
def vEcPow (s : StepShape) (l k : Nat) : PVar :=
  if ecPoint l == 0 then vZ s k else vZW s k
def nEcVars (s : StepShape) : Nat := 1 + s.bRounds + N_EC * ecStride s

/-! ### ⚑⚑ §19 — `check_bulletproof`'s OPENING SIDE: `group_map`, `p_prime`'s `uc`, `rhs`, `equal_g`.
The variables.

`step_verifier.ml:263-266, 316-320, 328-340`, and this region owns every cell of it:

    let u = group_map (Sponge.squeeze_field sponge)              (* :263-266 *)
    let p_prime = combined_polynomial + scale_fast2 u advice.combined_inner_product
    let q = p_prime + lr_prod                                    (* :316-320 *)
    let rhs =
      let b_u = scale_fast2 u advice.b in
      let z_1_g_plus_b_u = scale_fast2 (challenge_polynomial_commitment + b_u) z_1 in
      let z2_h = scale_fast2 (Inner_curve.constant (Lazy.force Generators.h)) z_2 in
      z_1_g_plus_b_u + z2_h                                      (* :328-338 *)
    (`Success (equal_g lhs rhs), challenges)                     (* :340 *)

**FOUR `scale_fast2` ladders, not three** — `uc` is one of them, and it is the one that carries
`combined_inner_product` (a STATEMENT word, R8's `vCipShift`) onto the curve side. Before §19 that
word reached only R5's Horner and R8's `Field.equal`; it now also determines `q`, hence `lhs`.

⚑ **AND SAY WHAT `equal_g` DOES NOT DO.** `G = challenge_polynomial_commitment`, `z₁` and `z₂` occur
at exactly two places each in `step_verifier.ml` (`:253` destructure, `:332-336` use): no absorption
inside `verify_one`, no pin, no statement word. So for ANY `lhs` a prover sets
`G := z₁⁻¹·(lhs − z₂·H) − b·u` — one scalar-field inverse and three scalar multiplications — and the
equality holds. §17 measures that on this assembly's own numbers and §19's rows do not change it.
What emitting `rhs`/`equal_g` DOES buy is that `verified` (#11) stops being a free witness: R8's
`ver` slot is this section's Boolean output, so `verified` is now a function of
`(q, c, δ, b, u, G, z₁, z₂)` — where the last three are still the prover's. That is the true label;
the row count is not the claim. -/

/-- ⚑ **`z₁`'s fixture value**, a witness with no upstream binder. The circuit cell exists (`bpZ1`)
and no row determines it, which is the fact §17 exhibits; the value here is what the honest
assembly's witness carries. -/
def BP_Z1_VAL : Nat := 987654321098765432109876543210
def BP_Z2_VAL : Nat := 555555555555555555555555555555

/-- §19's four `scale_fast2` ladders, in `step_verifier.ml`'s own order.

    k  base                              scalar                        source of the scalar
    0  u = group_map (squeeze)           advice.combined_inner_product  vCipShift — STATEMENT word
    1  u                                 advice.b                       vBShift   — STATEMENT word
    2  G + b_u                           z_1                            bpZ1      — FREE WITNESS
    3  Generators.h  (constant)          z_2                            bpZ2      — FREE WITNESS -/
def N_SF : Nat := 4

/-- `Snarky_group_map.Checked.wrap`'s cells (`checked_map.ml:20-55`), in emission order. Twelve for
`potential_xs` (`bw19.ml:78-99`), six per candidate for `y_squared` + `sqrt_flagged`, three for the
indicator booleans, and five per coordinate for the indicator dot-product. -/
def N_GM : Nat := 43
def baseBp (s : StepShape) : Nat := baseEc s + nEcVars s
/-- `group_map` cell `i`. -/
def vGm (s : StepShape) (i : Nat) : PVar := xv (baseBp s + i)
/-- ⚑ **`u`'s two coordinates** — `group_map`'s output, and the base of ladders 0 and 1. It needs no
`assert_on_curve`: `sqrt_flagged`'s `assert_square` plus `Boolean.Assert.any` and the first-of-three
selection ARE the on-curve proof, which is why upstream hands the result straight to `scale_fast2`. -/
def vUx (s : StepShape) : PVar := vGm s 37
def vUy (s : StepShape) : PVar := vGm s 42

/-- Ladder `k`'s block base. Same stride and same internal layout as §6b's, because it is the same
gadget: `sfTermRows` emits both. -/
def bpSfOff (s : StepShape) (k : Nat) : Nat := baseBp s + N_GM + k * ftcStride
def bpAccX (s : StepShape) (k j : Nat) : PVar := xv (bpSfOff s k + 2 * j)
def bpAccY (s : StepShape) (k j : Nat) : PVar := xv (bpSfOff s k + 2 * j + 1)
def bpOff (s : StepShape) (k : Nat) : Nat := bpSfOff s k + 2 * (FTC_CHUNKS + 1)
def bpTop (s : StepShape) (k : Nat) : PVar := xv (bpOff s k + FTC_CHUNKS)
def bpNegY (s : StepShape) (k : Nat) : PVar := xv (bpOff s k + FTC_CHUNKS + 1)
def bpHmX (s : StepShape) (k : Nat) : PVar := xv (bpOff s k + FTC_CHUNKS + 2)
def bpHmY (s : StepShape) (k : Nat) : PVar := xv (bpOff s k + FTC_CHUNKS + 3)
def bpDX (s : StepShape) (k : Nat) : PVar := xv (bpOff s k + FTC_CHUNKS + 4)
def bpDY (s : StepShape) (k : Nat) : PVar := xv (bpOff s k + FTC_CHUNKS + 5)
def bpMX (s : StepShape) (k : Nat) : PVar := xv (bpOff s k + FTC_CHUNKS + 6)
def bpMY (s : StepShape) (k : Nat) : PVar := xv (bpOff s k + FTC_CHUNKS + 7)
def bpResX (s : StepShape) (k : Nat) : PVar := xv (bpOff s k + FTC_CHUNKS + 8)
def bpResY (s : StepShape) (k : Nat) : PVar := xv (bpOff s k + FTC_CHUNKS + 9)

def baseBpT (s : StepShape) : Nat := baseBp s + N_GM + N_SF * ftcStride
/-- `Generators.h`, pinned coordinate-for-coordinate by one `Generic` row (`Inner_curve.constant`,
`:336`). ⚑ MEASURED off `SRS::<Pallas>::create`, not adopted from a doc — `GENERATORS_H`. -/
def bpHx (s : StepShape) : PVar := xv (baseBpT s)
def bpHy (s : StepShape) : PVar := xv (baseBpT s + 1)
/-- `challenge_polynomial_commitment + b_u` (`:333`), ladder 2's base. -/
def bpGbX (s : StepShape) : PVar := xv (baseBpT s + 2)
def bpGbY (s : StepShape) : PVar := xv (baseBpT s + 3)
/-- `rhs = z_1_g_plus_b_u + z2_h` (`:337`). -/
def bpRhsX (s : StepShape) : PVar := xv (baseBpT s + 4)
def bpRhsY (s : StepShape) : PVar := xv (baseBpT s + 5)
/-- ⚑ **`z₁` and `z₂` — FREE WITNESSES, and the region says so by giving them cells no row defines.**
Their only occurrences are ladders 2 and 3's `Shifted_value.Type2` splits, which is exactly upstream's
count of occurrences. -/
def bpZ1 (s : StepShape) : PVar := xv (baseBpT s + 6)
def bpZ2 (s : StepShape) : PVar := xv (baseBpT s + 7)
/-- Ladder `k`'s `Shifted_value.Type2` pair (`plonk_curve_ops.ml:290-291`). ⚑ FOUR pairs and not two:
each ladder has its own scalar here, where §6b's eight ladders share two. -/
def bpDiv2 (s : StepShape) (k : Nat) : PVar := xv (baseBpT s + 8 + 2 * k)
def bpOdd (s : StepShape) (k : Nat) : PVar := xv (baseBpT s + 9 + 2 * k)
/-- ⚑⚑ **`advice.combined_inner_product`'s `Boolean.var` — LADDER 0's `s_odd`, and not a cell of its
own.** This is the whole of the 2026-08-03 closure: upstream absorbs and scales ONE
`Other_field.Packed` pair (`step_verifier.ml:256-259` and `:317`), so the transcript's second `cip`
item IS the `s_odd` the `Shifted_value.Type2` split row derives. The long note at §8f's statement
block says what that does and does not buy. -/
def vCipBit (s : StepShape) : PVar := bpOdd s 0
/-- Ladder `k`'s counter at chunk boundary `j`; at `j = FTC_CHUNKS` it IS the scalar's `s_div_2` —
`Field.Assert.equal !n_acc scalar` (`plonk_curve_ops.ml:208`), the wire that makes the ladder
multiply by the value the statement carries and not by one the prover picked. -/
def bpN (s : StepShape) (k j : Nat) : PVar :=
  if j == FTC_CHUNKS then bpDiv2 s k else xv (bpOff s k + j)
/-- `equal_g`'s two `Field.equal` gadgets: per coordinate a difference, a witnessed inverse and the
result bit (`d·inv = 1 − bit`, `d·bit = 0`, `bit² = bit`), then `Boolean.all` of the two. -/
def bpEqD (s : StepShape) (i : Nat) : PVar := xv (baseBpT s + 16 + 4 * i)
def bpEqInv (s : StepShape) (i : Nat) : PVar := xv (baseBpT s + 17 + 4 * i)
def bpEqBit (s : StepShape) (i : Nat) : PVar := xv (baseBpT s + 18 + 4 * i)
def bpEqSq (s : StepShape) (i : Nat) : PVar := xv (baseBpT s + 19 + 4 * i)
def bpEqP (s : StepShape) (i : Nat) : PVar := xv (baseBpT s + 24 + 2 * i)
def bpEqZ (s : StepShape) (i : Nat) : PVar := xv (baseBpT s + 25 + 2 * i)
/-- ⚑ **`equal_g lhs rhs`** — and R8's `verified` slot IS this variable since §19, so the boolean
`check_bulletproof` returns is the boolean `finalize_other_proof`'s `Boolean.all` consumes. -/
def bpEq (s : StepShape) : PVar := xv (baseBpT s + 28)
def nBpVars (s : StepShape) : Nat := N_GM + N_SF * ftcStride + 29

def baseFtS (s : StepShape) : Nat := baseBp s + nBpVars s

/-! ## ⚑⚑ §2c — **`multiscale_known`'s SCALARS ARE THE WRAP STATEMENT'S WORDS.**

`x_hat = multiscale_known (Array.mapi public_input ~f:(fun i x -> (x, lagrange_commitment ~domain
srs i)))` (`step_verifier.ml:543-544`) over

    public_input = Spec.pack (module Impl) (Types.Wrap.Statement.In_circuit.spec …)
                     (Types.Wrap.Statement.In_circuit.to_data … statement)        (`:1236-1251`)

so term `i`'s SCALAR is packed statement word `i`. §1b gave each word its own WIDTH; this gives each
word its own VALUE, and the two only mean something together — a 255-bit ladder over a `< 2¹²⁸`
transcript challenge is shape-faithful and semantically empty.

`to_data`'s own order (`composition_types.ml:823-880`, read at source) and where this assembly
already holds each word:

    i      statement word                          this assembly's variable        provenance
    0      combined_inner_product  (Type1)         `vCipShift`      R5's Horner output, R8 binds it
    1      b                       (Type1)         `vBShift`        R8's `b_correct`
    2      zeta_to_srs_length      (Type1)         R6's `ζ^n` slot  DERIVED (see below)
    3      zeta_to_domain_size     (Type1)         R6's `ζ^n` slot  DERIVED (see below)
    4      perm                    (Type1)         `vPermShift`     R8's `Plonk_checks.checked`
    5,6    beta, gamma                             `vN β/γ emsRows` R2's decoded prechallenge
    7,8    alpha, zeta                             `vN α/ζ emsRows` R2's decoded prechallenge
    9      xi                                      `vXiStmt`        R8's `xi_correct`, §8g's lift
    10     sponge_digest_before_evaluations        `digestBeforeEvalsVar`  ⚑ §22 — R1's ζ-squeeze
                                                                    lane 1, and segment B's SEED
    11     messages_for_next_wrap_proof            `vStmtWrapMsgs`  ⚠ NO SOURCE — nor upstream
    12     messages_for_next_step_proof            segment C's squeeze — `hmDigestVar`
    13–28  bulletproof_challenges ×16              `vN (uChal k) emsRows`  R8's `b_correct` folds
                                                                    these SAME sixteen
    29     branch_data                             `vBranch`        §8h unpacks it
    30–38  the eight feature flags + the Opt flag  `vStmtFlag k`    ⚑ ZERO chunks — no row reads it
    39     the lookup Opt's Scalar Challenge       `vStmtLookup`    ⚠ NO SOURCE (§8f)

⚑ **THE SCALARS ARE `Bulletproof_challenge.pack`'s PRECHALLENGE, NOT THE LIFT.** `pack_basic`'s
`Bulletproof_challenge` arm is `let { Sc.inner = pre } = Bulletproof_challenge.pack x in
[| `Packed_bits (pre, Challenge.length) |]` (`spec.ml:390-393`), and `Scalar chal` packs its inner
too (`:94-99`). So words 5–9, 13–28 and 39 are the RAW `vN c emsRows` cells and NOT `vLift c` — the
endo image is what the curve gadgets consume, the prechallenge is what the statement carries. Getting
this backwards would put a `> 2¹²⁸` value under a 130-bit ladder and the counter chain would not
close.

⚑ **`Field` PACKS AS `` `Field x ``, NOT AS `` `Packed_bits (x, 255) ``** — `pack_basic`'s `Field`
arm is `[| `Field x |]` (`spec.ml:373-374`), and `multiscale_known` scales THAT case at
`~num_bits:Field.size_in_bits` (`step_verifier.ml:159-165`). The WIDTH is 255 either way, so §1b's
`msmBits` is unchanged; §1b's docblock said `Packed_bits` and that was wrong at source. `Digest` IS
`Packed_bits (x, Field.size_in_bits)` (`:379-380`).

⚠ ⚑ **WORDS 2 AND 3 ARE ONE VARIABLE HERE AND TWO UPSTREAM, and that is a DIVERGENCE, not a
simplification.** At `log2n = srs_length_log2 = 16` the two are the same field element
(`plonk_checks.ml:496-497`), and §6b already feeds BOTH of `ft_comm`'s scalar roles from R6's single
derived `ζ^n` cell. Upstream they are two unconstrained statement words that happen to be equal;
here they are one derived cell, so this assembly's σ has ONE class where Snarky has two and the
value is COMPUTED where upstream's is claimed. Strictly more constrained, and stated rather than
elided. ⚠ Also: `Plonk_checks.checked` compares the list `[ perm ]` and NOTHING ELSE
(`plonk_checks.ml:537-544`) — `zeta_to_srs_length`/`zeta_to_domain_size` are never checked in-circuit
upstream at all. -/

/-- ⚑ R6's `ζ^n` slot index in the compiled ft program (`ftBuild`'s `zetaN`, the `log2n`-fold
squaring of ζ). A LITERAL here and a derivation there — §21 pins the two against each other at both
committed shapes, which a constant checked against its own definition would not do. -/
def FT_SLOT_ZETAN : Nat := 55

/-- ⚑ **Wrap statement word `i`'s CIRCUIT VARIABLE.** See §2c's table. Beyond word 39 the statement
has no more words; a shape carrying more MSM terms than the statement has words falls back to the
retired round-robin, and §10 pins that the committed shape does not reach it. -/
def stmtVar (s : StepShape) (i : Nat) : PVar :=
  if i == 0 then vCipShift s
  else if i == 1 then vBShift s
  else if i < 4 then xv (baseFtS s + FT_SLOT_ZETAN)
  else if i == 4 then vPermShift s
  else if i == 5 then vN s s.betaChal s.emsRows
  else if i == 6 then vN s s.gammaChal s.emsRows
  else if i == 7 then vN s s.alphaChal s.emsRows
  else if i == 8 then vN s s.zetaChal s.emsRows
  else if i == 9 then vXiStmt s
  -- ⚑ §22: `sponge_digest_before_evaluations`, spelled out of R1's own block schedule rather than
  -- given a statement cell. `digestBeforeEvalsVar` is §2b's name for the same expression and §22
  -- pins the two equal, which makes this a gate between two sources rather than an alias.
  else if i == 10 then vSt s (sqStBlock s s.zetaChal) 1
  else if i == 11 then vStmtWrapMsgs s
  -- ⚑ segment C's SQUEEZE, spelled out rather than reached for: `hmDigestVar` is `sgSt (baseSegC s)
  -- … (nbC s + 1) 0` and `sgSt` is §8e, below this point. §21 pins the two expressions equal, which
  -- makes this a gate between two sources rather than an alias.
  else if i == 12 then xv (baseSegC s + 3 * nbC s)
  else if i < 29 then vN s (s.uChal (i - 13)) s.emsRows
  else if i == 29 then vBranch s
  else if i < 39 then vStmtFlag s (i - 30)
  else if i == 39 then vStmtLookup s
  else vN s (i % s.chals) s.emsRows

/-- MSM term `i`'s scalar counter at chunk boundary `j`. At `j = msmChunksAt i` it IS **Wrap
statement word `i`** — the cross-sub-circuit wire, and since 2026-08-03 a wire to the value the word
actually carries rather than to a round-robin transcript challenge. ⚠ On a ZERO-chunk term
(`msmBits i = 1`) the two coincide at `j = 0`, so the term has no counter cell of its own at all —
which is what a ladder with no chunk rows means. -/
def vSNAt (s : StepShape) (bs : Nat) (i j : Nat) : PVar :=
  if j == msmChunksAt i then stmtVar s i
  else xv (bs + msmChunkPrefix i + j)
def vSN (s : StepShape) (i j : Nat) : PVar := vSNAt s (baseSN s) i j

/-! ## §3 — the row-schedule primitives. -/

/-- One circuit row: gate `kind`, the `K_PERMUTS = 7` permutation-column variables (`none` = unwired
⇒ `place` self-wires), the `coeffs`, and the ADVICE `(col, value)` placements for every column no
variable owns (including permutation columns deliberately left unwired). -/
structure SRow where
  kind : KGateType
  perm : List (Option PVar)
  coeffs : List Int := []
  advice : List (Nat × Int) := []
  /-- `true` only for the standalone `Zero` σ-only probes. -/
  probe : Bool := false
  deriving Repr, Inhabited

def noPerm : List (Option PVar) := List.replicate K_PERMUTS none

/-- A σ-ONLY PROBE. -/
def probeRow (wired : Bool) (a b : PVar) : SRow :=
  { kind := .zero
  , perm := if wired then [some a, some b, none, none, none, none, none] else noPerm
  , probe := true }

/-- The DOUBLE generic gate: half 1 is `c₀w₀+c₁w₁+c₂w₂+c₃w₀w₁+c₄ = 0` over cols 0,1,2; half 2 is the
same with `coeffs[5..9]` over cols 3,4,5 (`generic.rs:283-314`, read-only — `check_single(0,0)` then
`check_single(GENERIC_COEFFS, GENERIC_REGISTERS)`; the public term applies to half 1 only). -/
def genericRow (v0 v1 v2 v3 v4 v5 : Option PVar) (c : List Int) : SRow :=
  { kind := .generic, perm := [v0, v1, v2, v3, v4, v5, none], coeffs := c }

/-! ⚑ **THE COEFFICIENT VECTORS LIVE ON THE GADGET RAIL** (`KimchiGadgets` §2), not here. These
delegate, so there is ONE source for `cAdd`/`cMul`/`cSub`/`cEq`/`cConst`/`cNil` on the Step side and
every existing `rfl` over them still holds (the definitions are defeq). ⚠ `KimchiWrapMainCore` still
carries its own copy; that file is the wrap cone and is not touched here. -/

/-- `w₂ = w₀ + w₁`. -/ def cAdd : List Int := KimchiGadgets.cAdd
/-- `w₂ = w₀ · w₁`. -/ def cMul : List Int := KimchiGadgets.cMul
/-- `w₂ = 1 + w₀·w₁`. -/ def cMulPlus1 : List Int := [0, 0, -1, 1, 1]
/-- `w₂ = w₀ − w₁`. -/ def cSub : List Int := KimchiGadgets.cSub
/-- `w₀ = w₁`. -/ def cEq : List Int := KimchiGadgets.cEq
/-- `w₀ = k`. -/ def cConst (k : Int) : List Int := KimchiGadgets.cConst k
/-- `w₀ = w₂ + 2^bits·w₁` — the challenge decomposition. -/
def cSplit (bits : Nat) : List Int := [1, -((2 ^ bits : Nat) : Int), -1, 0, 0]
/-- An unused generic half. -/ def cNil : List Int := KimchiGadgets.cNil

/-- A `complete_add` row: `o = l + r`, with `Ops.add_fast`'s four stored cells as advice. -/
def caRow (l r o : PVar × PVar) (c : List Nat) : SRow :=
  { kind := .completeAdd
  , perm := [ some l.1, some l.2, some r.1, some r.2, some o.1, some o.2, none ]
  , advice := [ (7, (c.getD 7 0 : Int)), (8, (c.getD 8 0 : Int))
              , (9, (c.getD 9 0 : Int)), (10, (c.getD 10 0 : Int)) ] }

/-- Pack a list of `Generic` HALVES two to a row (Snarky's own double-generic filling). -/
def packHalves (hs : List (List (Option PVar) × List Int)) : List SRow :=
  let nil : List (Option PVar) × List Int := ([none, none, none], cNil)
  (List.range ((hs.length + 1) / 2)).map (fun r =>
    let h1 := hs.getD (2 * r) nil
    let h2 := if 2 * r + 1 < hs.length then hs.getD (2 * r + 1) nil else nil
    ({ kind := .generic, perm := h1.1 ++ h2.1 ++ [none]
     , coeffs := h1.2 ++ h2.2 } : SRow))

/-! ## §3b — the SUPPLIED COMMITMENTS, and where each curve base COMES FROM.

⚑ This is simplification #3, and reading `step_verifier.ml` at source splits it in two, because
upstream's curve bases have TWO provenances and NEITHER of them is "a free witness":

  * **CONSTANTS.** `multiscale_known`'s bases are `Inner_curve.constant (lagrange_commitment
    ~domain srs i)` (`:150,165-172,543-544`) — SRS points the verifier key fixes. So are the
    verifier-key commitments `m.generic_comm … m.sigma_comm` the fold consumes (`:606-616`), which
    reach the transcript only through `sponge_after_index`. A prover cannot choose any of them.
  * **THE PREVIOUS PROOF'S OWN COMMITMENTS.** `sg_old`, `x_hat`, `z_comm`, `w_comm`, and
    `bullet_reduce`'s fifteen `(L,R)` pairs. Every one is ABSORBED INTO THE TRANSCRIPT SPONGE before
    the challenge that weights it is squeezed (`:537,559,561,564`; `:193`) — which is the entire
    reason a Fiat-Shamir challenge binds the commitment it multiplies.

Until 2026-08-02 this file had NEITHER. Every base was a free witness variable carrying a `basePts`
fixture, and R1 absorbed `2·absorbs` UNRELATED `msgVal` words, so bending a base moved nothing and a
prover could pick the bases outright. Now a `.const` base is pinned by a `Generic` row
(`Inner_curve.constant`), and an `.absorbed` base's two coordinate variables **ARE** the two words
transcript block `b` absorbs — one σ class spanning the `Poseidon` sponge and the `EndoMul` chain.

⚠ THE RESIDUE, named rather than absorbed. The VALUES are a real proof's — `MinaStepPrevCommitments`
reads them out of the `MinaWrap*` gates for devnet block 539508 — and since §7b every absorbed one
also carries `Inner_curve.typ`'s `assert_on_curve`. What is still undone and is not a theorem:
`multiscale_known`'s SCALARS are upstream's PUBLIC INPUT words (the packed Wrap statement; #2 has
the word-for-word census) and here are still the circuit's own derived challenges. ⚑ The second
residue this note used to carry — "segment C's `sponge_after_index` prefix is still 58 fixture words
rather than the real plonk index" — is §3c, retired 2026-08-02. -/

/-- Where a curve base comes from. -/
inductive BaseSrc where
  /-- an SRS / verifier-key CONSTANT (`Inner_curve.constant`), pinned by a `Generic` row. -/
  | const
  /-- the previous proof's commitment, absorbed at transcript block `b` — the SAME two variables. -/
  | absorbed (b : Nat)
  /-- ⚑ COMPUTED IN-CIRCUIT: `Common.ft_comm`, whose two coordinate variables are the OUTPUT of
  §6b's own `complete_add` chain. Neither pinned nor absorbed — derived. -/
  | computed
  deriving Repr, DecidableEq, Inhabited

-- (⚑ the provenance CENSUS — `wdbAbsorbed` / `ipaAbsorbs` / `absRoundList` — is stated in §2,
-- because §2's `assert_on_curve` region is sized by it.)

/-- Position `k` of `absRoundList` as an ABSORB ORDINAL: the `preRounds ++ zRounds` prefix sits at
`oPre …`, the `gamRounds` tail at `oGam …` (§2b). -/
def absOrdOfIdx (s : StepShape) (k : Nat) : Nat :=
  let np := (preRounds s).length + (zRounds s).length
  if k < np then oPre + k else oGam s + (k - np)

/-- IPA round `r`'s base source. ⚑ Round `FTC_ROUND` is `ft_comm` and is COMPUTED since §6b — it was
an `Inner_curve.constant` carrying the real block's `COMBINE_XY[3]` until 2026-08-02. -/

def ipaSrc (s : StepShape) (r : Nat) : BaseSrc :=
  if r == FTC_ROUND then .computed
  else match (absRoundList s).findIdx? (fun x => x == r) with
  | some k => .absorbed (absOrdOfIdx s k)
  | none => .const

/-- Absorb block `a`'s commitment, as an IPA round — the inverse of `ipaSrc`. ⚑ Blocks `oDigest`,
`oSgOld0`, the `t_comm` run, `oCip` and `oDelta` carry no ROUND: `index_digest` is a bare `Field`,
`sg_old[0]` is the fold's `~init`, and the other three are consumed elsewhere. -/
def blockRound (s : StepShape) (a : Nat) : Option Nat :=
  if oPre ≤ a && a < oTc s then (absRoundList s)[a - oPre]?
  else if oGam s ≤ a && a < oDelta s then
    (absRoundList s)[(a - oGam s) + (preRounds s).length + (zRounds s).length]?
  else none

/-- ⚑ Absorb block `a`'s `t_comm` CHUNK, if it carries one. `receive without t_comm`
(`step_verifier.ml:567`) absorbs the seven quotient commitments after `z_comm` (hence after α) and
before ζ, which is exactly the `oTc … oCip` run of the schedule. -/
def tCommBlock (s : StepShape) (a : Nat) : Option Nat :=
  if oTc s ≤ a && a < oCip s then some (a - oTc s) else none

/-- ⚑ R3 is `multiscale_known` — the x_hat MSM — and every one of ITS bases is an SRS Lagrange
commitment inside `Inner_curve.constant`. There is no absorbed base in R3, upstream or here. -/
def msmSrc (_i : Nat) : BaseSrc := BaseSrc.const

/-- R4's bases in round order: `combine_split_commitments`' 46 (round `r` folds in commitment
`r+1`; commitment 0 is where the accumulator starts), then `bullet_reduce`'s 30 interleaved
`(L, R)`. -/
def REAL_IPA_XY : List (Nat × Nat) :=
  Dregg2.Bridge.MinaStepPrevCommitments.COMBINE_XY.tail
  ++ Dregg2.Bridge.MinaStepPrevCommitments.GAMMA_XY

/-- ⚑ THE SUPPLIED COMMITMENTS, indexed as the assembly consumes them: the `msmTerms` SRS Lagrange
constants, then the `ipaRounds` fold / `bullet_reduce` bases. **These are Mina devnet block
539508's own Wrap-proof commitments**, Pallas points in this assembly's own field — not `basePts`,
which is what `[3]G, [4]G, …` this file ran until 2026-08-02. -/
def stepBases (s : StepShape) : List (Nat × Nat) :=
  (List.range s.msmTerms).map (fun i =>
     Dregg2.Bridge.MinaStepPrevCommitments.LAGRANGE_XY.getD i (0, 0))
  ++ (List.range s.ipaRounds).map (fun r => REAL_IPA_XY.getD r (0, 0))
def msmBaseOf (bs : List (Nat × Nat)) (i : Nat) : Nat × Nat := bs.getD i (0, 0)
def ipaBaseOf (s : StepShape) (bs : List (Nat × Nat)) (r : Nat) : Nat × Nat :=
  bs.getD (s.msmTerms + r) (0, 0)

/-- `Inner_curve.constant`: ONE `Generic` row pinning BOTH coordinates of a base the verifier fixes.
Half 1 is `w₀ − x = 0` over col 0, half 2 is `w₃ − y = 0` over col 3. -/
def baseConstRow (vx vy : PVar) (p : Nat × Nat) : SRow :=
  genericRow (some vx) none none (some vy) none none (cConst (p.1 : Int) ++ cConst (p.2 : Int))

/-! ## §3c — `sponge_after_index`, DERIVED (the other half of Fiat–Shamir).

`step_verifier.ml:1149-1157`, verbatim:

    let sponge_after_index index =
      let sponge = Sponge.create sponge_params in
      Array.iter (Types.index_to_field_elements ~g:Inner_curve.to_field_elements index)
        ~f:(fun x -> Sponge.absorb sponge (`Field x)) ; sponge

with `index = d.wrap_key` (`step_main.ml:61`) — the SAME `Plonk_verification_key_evals.t` the fold
consumes as `~verification_key:m`. Two things read it, and both are here:

  * **`index_digest`** (`:529-535`) — `Sponge.squeeze_field (Sponge.copy sponge_after_index)`, and
    `absorb sponge Field index_digest` is the FIRST thing the transcript swallows, ahead of
    `sg_old`. That is the wire that makes every transcript challenge a function of the verifier key.
  * **`hash_messages_for_next_step_proof`** (`:1158-1168`) — `Sponge.copy after_index`, then the
    app state / commitments / challenges. Segment C's `Not_opt` prefix IS that copy: absorbing the
    56 index words into a fresh sponge and continuing gives the same state a copy does, and 56 is
    even so the continuation starts on a rate-2 block boundary.

⚑ **27 OF THE 28 COMMITMENTS ARE ALREADY VARIABLES IN THIS ASSEMBLY.** `combine_split_commitments`
carries `sigma_comm[0..5]`, `coefficients_comm[0..14]` and the six selector commitments
(`step_verifier.ml:583-617`) as `.const` fold bases, each already pinned by an `Inner_curve.constant`
row. Segment C absorbs THOSE VERY VARIABLES, so the plonk index the sponge hashes and the plonk
index the fold multiplies by are ONE object rather than two agreeing copies. The 28th,
`sigma_comm[6]`, is `Common.ft_comm`'s `sigma_comm_last` (`common.ml:243-246`) and the fold does not
carry it, so it gets a pinned variable of its own here.

⚠ WHAT THIS DOES NOT DO: the 56 words are the verifier key, which a PROVER cannot choose either way
— the substance is that they are no longer FREE, i.e. the sponge state is a function of the key
rather than of a witness. -/

/-- VK commitment `k`, in `index_to_field_elements` order, as an IPA fold round — `none` for
`sigma_comm[6]`, which `combine_split_commitments` does not carry. Round `r`'s base is
`COMBINE_XY[r+1]`, so the census indices 41..46 / 26..40 / 5..10 become rounds 40..45 / 25..39 /
4..9. -/
def idxRoundOf (k : Nat) : Option Nat :=
  if k < 6 then some (40 + k)
  else if k == 6 then none
  else if k < 22 then some (25 + (k - 7))
  else some (4 + (k - 22))

/-- …and whether THIS shape has that round as a constant fold base. A shape too small to reach the
round falls back to a pinned variable of its own, so the derivation holds at every shape. -/
def idxSrc (s : StepShape) (k : Nat) : Option Nat :=
  match idxRoundOf k with
  | some r => if r < s.ipaRounds && ipaSrc s r == BaseSrc.const then some r else none
  | none => none

/-- The VARIABLE `sponge_after_index` absorbs at coordinate `j` of index commitment `k`. -/
def idxVar (s : StepShape) (k j : Nat) : PVar :=
  match idxSrc s k with
  | some r => if j == 0 then ipx s (qT s r) else ipy s (qT s r)
  | none => if j == 0 then vIdxX s k else vIdxY s k

/-- …and its VALUE, out of `MinaStepPrevCommitments.INDEX_XY`. -/
def idxVal (k j : Nat) : Nat :=
  let p := Dregg2.Bridge.MinaStepPrevCommitments.INDEX_XY.getD k (0, 0)
  if j == 0 then p.1 else p.2

/-- The index commitments this shape must pin itself — everything the fold does not already hold. -/
def idxOwn (s : StepShape) : List Nat :=
  (List.range N_IDX_COMMS).filter (fun k => idxSrc s k == none)

/-- `Inner_curve.constant` rows for those. -/
def idxConstRows (s : StepShape) : List SRow :=
  (idxOwn s).map (fun k =>
    baseConstRow (vIdxX s k) (vIdxY s k)
      (Dregg2.Bridge.MinaStepPrevCommitments.INDEX_XY.getD k (0, 0)))

/-- `sponge_after_index`'s trajectory over a WORD FUNCTION — `idxStatesWith ws ! b` is the state
entering absorb block `b`. Parametrised so §12d can re-run it on a prover's chosen input. -/
def idxStatesWith (ws : Nat → Nat) : List (List Nat) :=
  (List.range N_IDX_COMMS).foldl
    (fun acc b =>
      let st := acc.getLastD [0, 0, 0]
      acc ++ [ Dregg2.Circuit.Emit.PastaPoseidon.Ref.perm
                 [ (st.getD 0 0 + ws (2 * b)) % pN, (st.getD 1 0 + ws (2 * b + 1)) % pN
                 , st.getD 2 0 ] ])
    [[0, 0, 0]]

/-- The honest word at flat position `i` of the index absorption. -/
def idxWordAt (i : Nat) : Nat := idxVal (i / 2) (i % 2)

/-- ⚑ `sponge_after_index`'s STATE after all 28 absorptions — a closed function of the verifier key,
shape-independent by construction (the prefix is the same 56 words at every shape). -/
def idxAfterState : List Nat := (idxStatesWith idxWordAt).getLastD [0, 0, 0]

/-- ⚑ …and **lane 0 of THAT state IS `index_digest`** — no further permutation. `idxStatesWith`'s
last fold step already performed the one the copy's `squeeze` triggers (see `vIdxD`). Until
2026-08-03 this was `perm idxAfterState`, a 29th permutation over 56 absorbed words where Mina
performs 28; `Ref.hash` (nine o1js golds) says 28. -/
def idxDigestState : List Nat := idxAfterState
def indexDigest : Nat := idxDigestState.getD 0 0

/-! ### ⚑⚑ **THERE IS NO FREE TRANSCRIPT WORD LEFT.** This is where `msgVal` stood — "a transcript word
no row pins and no sub-circuit derives" — and it is DELETED (2026-08-03).

It survived because the old model paired the item stream PER SOURCE and padded `index_digest` to two
lanes, so block 0's second lane carried a deterministic FIXTURE: a word `verify_one` never feeds the
sponge, absorbed anyway. Under Mina's lazy sponge the pairing is per ITEM (`spLay`), `index_digest`
shares block 0 with `sg_old[0]`'s x, and the single unpaired lane an odd item count forces lands at
the end of the pre-β run with NOTHING in it — `tPadCell`, pinned to zero by one `Generic` row, which
is `absorb`'s own "no arrival" (it ADDS). So all `N_ABSORB_ITEMS` items are wired variables and the
last place Fiat–Shamir was the prover's is closed by the re-model rather than by a new wire.

⚑ The count was 7 until 2026-08-02 (31 at `absorbs = 71`, 45 before §6b), then ONE, now ZERO. -/

/-- ⚑ The VARIABLE `verify_one` absorbs at lane `j` of SOURCE `a` (an absorb-call ordinal, not a
block index — `spLay` decides which block/lane the item lands in). Every one of them is a variable
some sub-circuit reads; there is no residue arm any more. -/
def msgVar (s : StepShape) (a j : Nat) : PVar :=
  match blockRound s a with
  | some r => if j == 0 then ipx s (qT s r) else ipy s (qT s r)
  | none =>
    match tCommBlock s a with
    | some i => if j == 0 then vTcX s i else vTcY s i
    | none =>
      if a == oDigest then vIdxD s 0
      -- ⚑ `sg_old[0]`: the fold's `~init` accumulator point, R4's own `complete_add` chain head.
      else if a == oSgOld0 then (if j == 0 then ipx s (qInit s) else ipy s (qInit s))
      -- ⚑ `advice.combined_inner_product`: the STATEMENT word R8 binds, then its `Boolean.var`.
      else if a == oCip s then (if j == 0 then vCipShift s else vCipBit s)
      -- ⚑ `delta`: the second operand of `check_bulletproof`'s closing `add_fast`.
      else if j == 0 then ipx s (qDel s) else ipy s (qDel s)

/-- …and its VALUE. `cipW` is `(field, bit)` of `advice.combined_inner_product`, threaded in because
it is computed from ξ, r and `ft_eval0` — all of which the transcript fixes BEFORE this block
(`:568` precedes `:256`), which is exactly why absorbing it is not a cycle. -/
def msgValOf (s : StepShape) (bs : List (Nat × Nat)) (cipW : Nat × Nat) (a j : Nat) : Nat :=
  match blockRound s a with
  | some r => let p := ipaBaseOf s bs r; if j == 0 then p.1 else p.2
  | none =>
    match tCommBlock s a with
    | some i =>
      let p := Dregg2.Bridge.MinaStepPrevCommitments.T_COMM_XY.getD i (0, 0)
      if j == 0 then p.1 else p.2
    | none =>
      if a == oDigest then indexDigest
      else if a == oSgOld0 then
        (let p := Dregg2.Bridge.MinaStepPrevCommitments.SG_OLD0_XY
         if j == 0 then p.1 else p.2)
      else if a == oCip s then (if j == 0 then cipW.1 else cipW.2)
      else
        (let p := Dregg2.Bridge.MinaStepPrevCommitments.DELTA_XY
         if j == 0 then p.1 else p.2)

/-! ## §4 — R1, the TRANSCRIPT SPONGE.

Rate 2 into lanes 0,1, capacity lane 2 (`PastaPoseidon.Ref.absorbFrom`: `n = rate` triggers `perm`
then `absorbAt _ 0`). One absorb block:

    Generic  w₀=stᵦ[0] w₁=msg₀ w₂=postᵦ[0]  |  w₃=stᵦ[1] w₄=msg₁ w₅=postᵦ[1]
    Poseidon ×11, row j coeffs `poseidonRowCoeffs j`; row 0's cols 0,1,2 WIRED to
             (postᵦ[0], postᵦ[1], stᵦ[2]) — the capacity lane passes through untouched
    Zero     cols 0,1,2 WIRED to stᵦ₊₁[0..2] = the permutation output

A squeeze block is the same without the absorb row. The `Poseidon` gate at row `j` reads the NEXT
row's cols 0,1,2 as its output state, which is why the closing `Zero` row exists and why the state
chains across the eleven rows through the gate reference rather than through σ.

⚑ **THE BLOCKS ARE INTERLEAVED AS §2b's SCHEDULE SAYS**, not "all absorbs, then all squeezes". The
row COUNT is unchanged by that — `absorbs` absorb rows, `blocks` permutations, one probe per squeeze
plus one at the last absorb — but every squeeze's POSITION moves, so every challenge value moves and
with it every ladder the challenges drive. -/

/-- ⚑ **THE GENERAL FACT, NOT THE ONE INSTANCE.** Building a trajectory newest-first with `headD`
and reversing once is the forward `acc ++ [f (acc.getLastD d)]` fold, for EVERY step function, EVERY
default and EVERY index list — the `range 55` in `permStates` is one instance of it.

⚠ This was `:= rfl` until 2026-08-03 and **`rfl` does not typecheck**: whnf must reduce 55 nested
`++ [·]`s, each re-walking the accumulator through `getLastD` and indexing `rcsN`, so the declaration
died on `(deterministic) timeout at whnf, maximum number of heartbeats (200000)` — i.e. the module
was RED at `95ed4f2ec` and the claim "general … by `rfl`" was never checked by anything. The
induction is O(1) heartbeats and is genuinely general, which `rfl` at `range 55` was not. -/
theorem foldl_cons_reverse_is_the_append_fold {α : Type} (f : Nat → α → α) (d : α) :
    ∀ (l : List Nat) (acc : List α),
      (l.foldl (fun a i => f i (a.headD d) :: a) acc).reverse
        = l.foldl (fun a i => a ++ [f i (a.getLastD d)]) acc.reverse := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons i t ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    simp

/-- The 56 states of one permutation, `s(0) = st` through `s(55)`, ONE round per step.

⚑ The trajectory is built NEWEST-FIRST and reversed once, so a round costs one cons and an O(1)
`headD` instead of `acc ++ [x]`'s copy of everything already there plus `acc.getLastD`'s walk to the
end. That was 2·Σ₅₅ ≈ 3 000 list cells per permutation, and the assembly runs a few hundred
permutations per `mkStep` — the same defect `spStep` carried in §1c′, in the inner loop. The FINAL
value is unchanged, and `permStates_is_the_forward_fold` states that generally, by INDUCTION on the
fold's index list (`foldl_cons_reverse_is_the_append_fold`) — not by `rfl`. -/
def permStates (st : List Nat) : List (List Nat) :=
  ((List.range 55).foldl
    (fun acc i =>
      Dregg2.Circuit.Emit.PastaPoseidon.Ref.round (rcsN.getD i []) (acc.headD st) :: acc)
    [st]).reverse

/-- ⚑ **THE HOIST IS THE THING IT HOISTS** — general over every input state, so the reversed
accumulator cannot drift from the forward fold it replaces. An instance of
`foldl_cons_reverse_is_the_append_fold` at `range 55`. -/
theorem permStates_is_the_forward_fold (st : List Nat) :
    permStates st
      = (List.range 55).foldl
          (fun acc i =>
            acc ++ [Dregg2.Circuit.Emit.PastaPoseidon.Ref.round (rcsN.getD i []) (acc.getLastD st)])
          [st] := by
  simpa [permStates] using
    foldl_cons_reverse_is_the_append_fold
      (fun i s => Dregg2.Circuit.Emit.PastaPoseidon.Ref.round (rcsN.getD i []) s) st
      (List.range 55) [st]

/-- Lane `j` of round state `k`. -/
def stLane (ss : List (List Nat)) (k j : Nat) : Int := ((ss.getD k []).getD j 0 : Int)

/-- The eleven `Poseidon` rows + the closing `Zero` row of ONE permutation. `round_to_cols` is
`STATE_ORDER = [0,2,3,4,1]` (`KimchiRenderPoseidon`, read-only): `s(5r)` at 0,1,2 · `s(5r+4)` at
3,4,5 · `s(5r+1)` at 6,7,8 · `s(5r+2)` at 9,10,11 · `s(5r+3)` at 12,13,14. -/
def permBlockRows (i0 i1 i2 o0 o1 o2 : PVar) (ss : List (List Nat)) : List SRow :=
  (List.range 11).map (fun r =>
    ({ kind := .poseidon
     , perm := if r == 0 then [some i0, some i1, some i2, none, none, none, none] else noPerm
     , coeffs := poseidonRowCoeffs r
     , advice :=
         (if r == 0 then [] else (List.range 3).map (fun j => (j, stLane ss (5 * r) j)))
         ++ (List.range 3).map (fun j => (3 + j, stLane ss (5 * r + 4) j))
         ++ (List.range 3).map (fun j => (6 + j, stLane ss (5 * r + 1) j))
         ++ (List.range 3).map (fun j => (9 + j, stLane ss (5 * r + 2) j))
         ++ (List.range 3).map (fun j => (12 + j, stLane ss (5 * r + 3) j)) } : SRow))
  ++ [ { kind := .zero, perm := [some o0, some o1, some o2, none, none, none, none] } ]

/-- The sponge's evaluated trajectory: `states ! b` is the state ENTERING block `b`, `perms ! b` is
block `b`'s 56 round states. -/
structure SpongeData where
  states : List (List Nat)
  perms : List (List (List Nat))
  /-- ⚑ the two words each absorb block SWALLOWED. For a block carrying one of the previous proof's
  commitments these are its coordinates, so the sponge trajectory is a function OF THE COMMITMENTS
  and every challenge below moves when one is bent. -/
  msgs : List (List Nat)
  deriving Repr, Inhabited

/-- R1's trajectory, PARAMETRISED on the value of `index_digest` (§3c), on the absorbed
`combined_inner_product` pair, AND on ONE absorbed word, absorb SOURCE `bt` lane `jt` — the grinds
§12d, §12b″ and §12i run. One implementation, so every control re-runs the assembly's own sponge
rather than a second copy of it; `bt ≥ absorbs` overrides nothing.

⚑ `states`, `perms` and `msgs` are all indexed by BLOCK — a `spLay` permutation — while `msgVar`/
`msgValOf` are indexed by absorb SOURCE, and `spLay.put` is what relates them. A lane no item lands
in gets a ZERO addend, which is `absorb`'s own behaviour: it ADDS into `state.(n)` and never writes
a lane nothing arrives at. -/
def runSpongeAt (s : StepShape) (bs : List (Nat × Nat)) (dig : Nat) (cipW : Nat × Nat)
    (bt jt w : Nat) : SpongeData :=
  let L := spLay s
  (List.range L.cur).foldl
    (fun d b =>
      let pre := d.states.getLastD [0, 0, 0]
      let ms := (blockWordsL L b).map (fun o =>
        match o with
        | none => 0
        | some (a, j) =>
            if a == bt && j == jt then w
            else if a == oDigest then dig
            else msgValOf s bs cipW a j)
      let post :=
        [ (pre.getD 0 0 + ms.getD 0 0) % pN, (pre.getD 1 0 + ms.getD 1 0) % pN, pre.getD 2 0 ]
      let ss := permStates post
      { states := d.states ++ [ss.getLastD post], perms := d.perms ++ [ss]
      , msgs := d.msgs ++ [ms] })
    { states := [[0, 0, 0]], perms := [], msgs := [] }

/-- …with no word overridden. -/
def runSpongeWith (s : StepShape) (bs : List (Nat × Nat)) (dig : Nat) (cipW : Nat × Nat)
    : SpongeData := runSpongeAt s bs dig cipW s.absorbs 0 0

/-- …at the DERIVED digest, which is the only instance the assembly emits. -/
def runSponge (s : StepShape) (bs : List (Nat × Nat)) (cipW : Nat × Nat) : SpongeData :=
  runSpongeWith s bs indexDigest cipW

/-- The variable at lane `l` of block `b` — the item `spLay` put there, or the ONE pad cell. -/
def tWordVar (s : StepShape) (ws : List (Option (Nat × Nat))) (l : Nat) : PVar :=
  match ws.getD l none with
  | some (a, j) => msgVar s a j
  | none => vTPad s

/-- **R1's rows.** ⚑ ONE `Poseidon` block per PERMUTATION and no more: a squeeze reads a lane of a
state some block already produced (`sqPos`), so it emits no rows of its own. A block that swallows
nothing at all — the third consecutive squeeze's — is a bare permutation with no `Generic` addend. -/
def transcriptRows (s : StepShape) (d : SpongeData) (wired : Bool) : List SRow :=
  -- ⚑ ONE layout for the whole schedule: `L.cur` IS `tBlocks s`, so `nStOf L.cur` is `nSt s` and
  -- `vPostAt`/`tProbeAfterL` read the layout already in hand instead of rebuilding it per block.
  let L := spLay s
  let nst := nStOf L.cur
  [ genericRow (some (vSt s 0 0)) none none (some (vSt s 0 1)) none none (cConst 0 ++ cConst 0)
  , genericRow (some (vSt s 0 2)) none none none none none (cConst 0 ++ cNil) ]
  -- ⚑ the ONE pad cell, pinned to zero. `getD`'s default used to be `xv 0` here and in `segRows`;
  -- naming the cell is what keeps a lane with no arrival out of another sponge's σ class.
  ++ (if (tPadCell s).isSome then
        [ genericRow (some (vTPad s)) none none none none none (cConst 0 ++ cNil) ] else [])
  ++ (List.range L.cur).flatMap (fun b =>
      let ws := blockWordsL L b
      (if ws.any (·.isSome) then
        -- ⚑ `msgVar` — for the lanes that carry a commitment coordinate this is the FOLD'S OWN
        -- BASE-POINT variable, so the sponge row and the `EndoMul` chain share one σ class.
        [ genericRow (some (vSt s b 0)) (some (tWordVar s ws 0)) (some (vPostAt nst b 0))
                     (some (vSt s b 1)) (some (tWordVar s ws 1)) (some (vPostAt nst b 1))
                     (cAdd ++ cAdd) ]
        ++ permBlockRows (vPostAt nst b 0) (vPostAt nst b 1) (vSt s b 2)
                         (vSt s (b+1) 0) (vSt s (b+1) 1) (vSt s (b+1) 2) (d.perms.getD b [])
       else
        permBlockRows (vSt s b 0) (vSt s b 1) (vSt s b 2)
                      (vSt s (b+1) 0) (vSt s (b+1) 1) (vSt s (b+1) 2) (d.perms.getD b []))
      ++ (if tProbeAfterL L b then [probeRow wired (vSt s (b+1) 0) (vSt s (b+1) 1)] else []))

/-! ## §5 — R2, CHALLENGE DERIVATION (`to_field_checked`).

Squeeze `c` is lane `sqStLane c` of the state ENTERING block `sqStBlock c`. Its low `chalBits` bits are the scalar
challenge. One `EndoMulScalar` row eats 8 crumbs and folds `n ↦ 4n + xⱼ`, `a ↦ 2a + c(xⱼ)`,
`b ↦ 2b + d(xⱼ)` from `n₀=0, a₀=2, b₀=2` (`endomul_scalar.rs:227-288`, read-only via
`KimchiRenderEndoMulScalar`). Column order `[n0, n8, a0, b0, a8, b8, x₀..x₇, 0]`, so cols 0..5 are
all permutation columns and the chain hops row→row through σ; col 6 holds crumb `x₀`, unwired. -/

/-- ⚑ **The raw squeeze `c`** — `copy t.state.(n)` off the state the last permutation left, with `n`
either 0 (the squeeze that permuted) or 1 (a FREE second consecutive squeeze). -/
def sqValOf (s : StepShape) (d : SpongeData) (c : Nat) : Nat :=
  (d.states.getD (sqStBlock s c) []).getD (sqStLane s c) 0
def chalOf (s : StepShape) (d : SpongeData) (c : Nat) : Nat :=
  (sqValOf s d c) % 2 ^ s.chalBits
def hiOf (s : StepShape) (d : SpongeData) (c : Nat) : Nat :=
  (sqValOf s d c) / 2 ^ s.chalBits

/-- ⚑ **The value `uSqueezeVar` holds** — the WHOLE squeeze, not `chalOf`'s low `chalBits`. §19's
`group_map` is a function of this. -/
def uSqueezeVal (s : StepShape) (d : SpongeData) : Nat := sqValOf s d (uChalIx s)

/-- ⚑ **`sponge_digest_before_evaluations`'s VALUE** — lane 1 of the state ζ's squeeze produced; the
variable is `digestBeforeEvalsVar` (§2b). ⚑ Identical across `mkStepWith`'s two transcript passes:
the `cip` absorb is block `oCip`, which comes AFTER ζ's squeeze (`step_verifier.ml:256` vs `:568`,
§12i), so nothing the second pass changes reaches this state. That is why seeding the fr-sponge with
it closes no cycle. -/
def digestBeforeEvalsVal (s : StepShape) (d : SpongeData) : Nat :=
  (d.states.getD (sqStBlock s s.zetaChal) []).getD 1 0

/-- ⚑ `Endo.Wrap_inner_curve.scalar` (`endo.ml:7`) — the SCALAR-challenge endomorphism of `Fp`, the
constant `to_field_checked` scales `a₈` by. NOT `FT_ENDO`, which is the BASE endomorphism
`5^((p−1)/3)` the linearization reads; conflating the two cube roots is the defect
`MinaWrapFtEval0Weld` closed, and §16's red control shows it here. -/
def ENDO_R : Nat :=
  8503465768106391777493614032514048814691664078728891710322960303815233784505

/-- The `8·rows` base-4 crumbs of an `EndomulScalar` source, MSB-first. ⚑ `rows` is explicit because
`to_field_checked ~num_bits:n` runs `n/16` rows and the assembly has TWO widths — 128 (`emsRows`, the
transcript squeezes and the two deferred chains) and **16**, `Branch_data.typ`'s `~assert_16_bits`
(`per_proof_witness.ml:166-168`). -/
def crumbsOfN (rows v : Nat) : List Nat :=
  (List.range (8 * rows)).map (fun j => v / 4 ^ (8 * rows - 1 - j) % 4)

/-- The `(n,a,b)` accumulator triples at every ROW boundary (every 8 crumbs), `k = 0..rows`. -/
def emsAccsN (rows v : Nat) : List (Nat × Nat × Nat) :=
  let all := (crumbsOfN rows v).foldl
    (fun acc x =>
      let cur := acc.getLastD (0, 2, 2)
      acc ++ [((4 * cur.1 + x) % pN, (2 * cur.2.1 + cFuncFp x) % pN,
               (2 * cur.2.2 + dFuncFp x) % pN)])
    [(0, 2, 2)]
  (List.range (rows + 1)).map (fun k => all.getD (8 * k) (0, 2, 2))

/-- The `8·emsRows` base-4 crumbs of a challenge, MSB-first. -/
def crumbsOf (s : StepShape) (v : Nat) : List Nat := crumbsOfN s.emsRows v

/-- The `(n,a,b)` accumulator triples at every ROW boundary (every 8 crumbs), `k = 0..emsRows`. -/
def emsAccs (s : StepShape) (v : Nat) : List (Nat × Nat × Nat) := emsAccsN s.emsRows v

/-- The `(a₈, b₈)` accumulators and the LIFT `a₈·endo_r + b₈` of a 128-bit prechallenge. -/
def liftVal (s : StepShape) (v : Nat) : Nat :=
  let a := (emsAccs s v).getD s.emsRows (0, 2, 2)
  fAdd (fMul a.2.1 ENDO_R) a.2.2
def liftTVal (s : StepShape) (v : Nat) : Nat :=
  fMul ((emsAccs s v).getD s.emsRows (0, 2, 2)).2.1 ENDO_R
/-- …of transcript challenge `c`. -/
def liftOf (s : StepShape) (d : SpongeData) (c : Nat) : Nat := liftVal s (chalOf s d c)
def liftTOf (s : StepShape) (d : SpongeData) (c : Nat) : Nat := liftTVal s (chalOf s d c)

/-- The one row that pins `endo_r`, emitted once ahead of the challenge chains. Every
`to_field_checked` chain in the assembly — R2's `chals` and §8g's two deferred ones — shares it. -/
def endoConstRow (s : StepShape) : List SRow :=
  [ genericRow (some (vEndoR s)) none none none none none (cConst (ENDO_R : Int) ++ cNil) ]

/-- One `to_field_checked` chain's variable block, so the SAME row emitter serves R2's transcript
challenges and §8g's deferred ξ/r. -/
structure ChalVars where
  n : Nat → PVar
  a : Nat → PVar
  b : Nat → PVar
  hi : PVar
  liftT : PVar
  lift : PVar

def r2Vars (s : StepShape) (c : Nat) : ChalVars :=
  { n := vN s c, a := vA s c, b := vB s c, hi := vHi s c
  , liftT := vLiftT s c, lift := vLift s c }
def defcVars (s : StepShape) (c : Nat) : ChalVars :=
  { n := vDN s c, a := vDA s c, b := vDB s c, hi := vDHi s c
  , liftT := vDLiftT s c, lift := vDLift s c }

/-- **`to_field_checked`'s rows** over a 128-bit prechallenge `v` (`scalar_challenge.ml:12-129`):
`n₀=0, a₀=2, b₀=2` pinned by `Generic` rows, `emsRows` chained `EndoMulScalar` rows, the tie of the
chain's reconstructed `n₈` back to its SOURCE, and the closing lift `Field.(scale a endo + b)`.

`split = true` — the source is a FULL field element (a sponge squeeze), so the tie is the
`lowest_128_bits` decomposition `src = n₈ + 2^chalBits·hi`. `split = false` — the source is already
a `Challenge.t` (§8g's statement ξ word), so the tie is `Field.Assert.equal n scalar` (`:124`) and
the chain's `hi` cell is not allocated by any row. -/
def tfcRowsN (s : StepShape) (rows : Nat) (cv : ChalVars) (src : PVar) (split : Bool) (v : Nat)
    (wired : Bool) : List SRow :=
  let cr := crumbsOfN rows v
  [ genericRow (some (cv.n 0)) none none (some (cv.a 0)) none none (cConst 0 ++ cConst 2)
  , genericRow (some (cv.b 0)) none none none none none (cConst 2 ++ cNil) ]
  ++ (List.range rows).map (fun k =>
      ({ kind := .endoMulScalar
       , perm := [ some (cv.n k), some (cv.n (k+1)), some (cv.a k), some (cv.b k)
                 , some (cv.a (k+1)), some (cv.b (k+1)), none ]
       , advice := (List.range 8).map (fun j => (6 + j, (cr.getD (8 * k + j) 0 : Int)))
                   ++ [(14, 0)] } : SRow))
  ++ [ (if split then
          genericRow (some src) (some cv.hi) (some (cv.n rows)) none none none
                     (cSplit (16 * rows) ++ cNil)
        else
          genericRow (some (cv.n rows)) (some src) none none none none (cEq ++ cNil))
     -- ⚑ `to_field_checked`'s CLOSING LINE: `Field.(scale a endo + b)`. Two halves of one row, and
     -- the `a₈`/`b₈` cells the `EndoMulScalar` chain produced now carry a value the rest of the
     -- assembly reads.
     , genericRow (some (cv.a rows)) (some (vEndoR s)) (some cv.liftT)
                  (some cv.liftT) (some (cv.b rows)) (some cv.lift) (cMul ++ cAdd)
     , probeRow wired (cv.n rows) (cv.a rows)
     , probeRow wired cv.lift (cv.b rows) ]

/-- …at the assembly's 128-bit width. -/
def tfcRows (s : StepShape) (cv : ChalVars) (src : PVar) (split : Bool) (v : Nat)
    (wired : Bool) : List SRow :=
  tfcRowsN s s.emsRows cv src split v wired

def rngVars (s : StepShape) (c : Nat) : ChalVars :=
  { n := vRN s c, a := vRA s c, b := vRB s c, hi := vRHi s c
  , liftT := vRLiftT s c, lift := vRLift s c }

/-- Range chain `c`'s accumulator trace at value `v`. -/
def rngEnvN (s : StepShape) (rows c v : Nat) : VarEnv :=
  let accs := emsAccsN rows v
  (List.range (rows + 1)).flatMap (fun k =>
    let a := accs.getD k (0, 2, 2)
    [ (vRN s c k, (a.1 : Int)), (vRA s c k, (a.2.1 : Int)), (vRB s c k, (a.2.2 : Int)) ])
  ++ (let a := accs.getD rows (0, 2, 2)
      [ (vRLiftT s c, (fMul a.2.1 ENDO_R : Int))
      , (vRLift s c, (fAdd (fMul a.2.1 ENDO_R) a.2.2 : Int)) ])

/-- …at the assembly's 128-bit width. -/
def rngEnv (s : StepShape) (c v : Nat) : VarEnv := rngEnvN s s.emsRows c v

/-- **`assert_128_bits x`** — `ignore (to_field_checked … ~num_bits:128)`, so the SAME chain over
the same source, tied by `Field.Assert.equal n scalar` and with the lift emitted (Snarky emits it;
only the value is dropped). Range chain `c` over source `src` holding value `v`. -/
def rangeRows (s : StepShape) (c : Nat) (src : PVar) (v : Nat) (wired : Bool) : List SRow :=
  tfcRows s (rngVars s c) src false v wired

/-- **R2's rows** for challenge `c` — `tfcRows` at the transcript sponge's own squeeze, then
`lowest_128_bits`' OTHER range check, over the high part (`~constrain_low_bits:true` asserts both;
`step_verifier.ml:186-187`). -/
def challengeRows (s : StepShape) (d : SpongeData) (wired : Bool) (c : Nat) : List SRow :=
  tfcRows s (r2Vars s c) (vSt s (sqStBlock s c) (sqStLane s c)) true (chalOf s d c) wired
  ++ rangeRows s c (vHi s c) (hiOf s d c) wired

/-! ## §6 — R3, the COMMITMENT MSM (`multiscale_known` / `ft_comm`).

`runVbm` (read-only) runs `accₖ₊₁ = [2]accₖ + (2bₖ−1)·T`, `nₖ₊₁ = 2nₖ+bₖ`, so with `n₀ = 0` the
final counter IS the scalar — and that cell is wired to the CHALLENGE variable, not a fresh one. -/

/-- The `5·msmChunksAt i` bits of `v`, MSB-first — MSM term `i`'s own width (§1b). Empty on the nine
one-bit statement words, which is exactly a ladder with no chunk rows. -/
def bitsOf (i : Nat) (v : Nat) : List Nat :=
  let n := 5 * msmChunksAt i
  (List.range n).map (fun k => v / 2 ^ (n - 1 - k) % 2)
/-- The `4·ipaBlocks` bits of `v`, MSB-first. -/
def endoBitsOf (s : StepShape) (v : Nat) : List Nat :=
  (List.range (4 * s.ipaBlocks)).map (fun k => v / 2 ^ (4 * s.ipaBlocks - 1 - k) % 2)

structure MsmData where
  terms : List TermData
  bits : List (List Nat)
  sums : List (Nat × Nat)
  addCells : List (List Nat)
  deriving Repr, Inhabited

/-- ⚑ **`multiscale_known`'s NON-CONSTANT PARTITION** (`step_verifier.ml:133-140`): the terms whose
scalar is not a `Field.Constant`, which upstream is exactly the terms that emit a ladder. The nine
one-bit statement words are `Spec.T.Constant` (`composition_types.ml:794-812`) / `Field.zero`
(`spec.ml:397`), fold into `constant_part` OUT of circuit, and get **no base pin, no
`add_fast base base` seed, no ladder and no fold add**. `chunks_needed ~num_bits:0 = 0` lands on the
same partition without a special case, so this list is `msmChunksAt ≠ 0`. -/
def msmLive (s : StepShape) : List Nat :=
  (List.range s.msmTerms).filter (fun i => msmChunksAt i != 0)

/-- ⚑ Since 2026-08-03 the scalars are supplied — they are the packed Wrap STATEMENT (§2c), not a
function of the sponge — and the fold runs over the NON-CONSTANT partition only. -/
def runMsm (s : StepShape) (bases : List (Nat × Nat)) (scal : Nat → Nat) : MsmData :=
  let live := msmLive s
  let bs := (List.range s.msmTerms).map (fun i => bitsOf i (scal i))
  let tds := (List.range s.msmTerms).map (fun i =>
    let T := msmBaseOf bases i
    runVbm T (dblA T) (bs.getD i []))
  let pts := (List.range s.msmTerms).map (fun i => (tds.getD i default).accs.getLastD (0, 0))
  let st := (List.range (live.length - 1)).foldl
    (fun (acc : List (Nat × Nat) × List (List Nat)) a =>
      let l := if a == 0 then pts.getD (live.getD 0 0) (0, 0) else acc.1.getLastD (0, 0)
      let r := pts.getD (live.getD (a + 1) 0) (0, 0)
      let cells := completeAddWitness l.1 l.2 r.1 r.2
      (acc.1 ++ [(cells.getD 4 0, cells.getD 5 0)], acc.2 ++ [cells]))
    ([], [])
  { terms := tds, bits := bs, sums := st.1, addCells := st.2 }

/-- The two rows of MSM term `i`'s chunk `j`.
CURR `w₀=xT w₁=yT w₂=x₀ w₃=y₀ w₄=n w₅=n' w₆=Ø w₇..w₁₄ = x₁y₁..x₄y₄`;
NEXT `w₀=x₅ w₁=y₅ w₂..w₆=b₀..b₄ w₇..w₁₁=s₀..s₄`. -/
def msmChunkRows (s : StepShape) (m : MsmData) (i j : Nat) : List SRow :=
  -- ⚑ ONE `baseMsm` and ONE `baseSN` for the pair of rows rather than six region walks: this
  -- function runs once per (term, chunk) and the committed shape has 982 chunks. See `mpxAt`'s note.
  let bm := baseMsm s
  let bsn := baseSN s
  let td := m.terms.getD i default
  let bits := m.bits.getD i []
  let ax : Nat → Int := fun k => ((td.accs.getD k (0, 0)).1 : Int)
  let ay : Nat → Int := fun k => ((td.accs.getD k (0, 0)).2 : Int)
  let bt : Nat → Int := fun k => (td.slopes.getD k 0 : Int)
  let bi : Nat → Int := fun k => (bits.getD k 0 : Int)
  [ { kind := .varBaseMul
    , perm := [ some (mpxAt bm (pT s i)), some (mpyAt bm (pT s i))
              , some (mpxAt bm (pAcc s i j)), some (mpyAt bm (pAcc s i j))
              , some (vSNAt s bsn i j), some (vSNAt s bsn i (j+1)), none ]
    , advice := [ (7, ax (5*j+1)), (8, ay (5*j+1)), (9, ax (5*j+2)), (10, ay (5*j+2))
                , (11, ax (5*j+3)), (12, ay (5*j+3)), (13, ax (5*j+4)), (14, ay (5*j+4)) ] }
  , { kind := .zero
    , perm := [ some (mpxAt bm (pAcc s i (j+1))), some (mpyAt bm (pAcc s i (j+1)))
              , none, none, none, none, none ]
    , advice := [ (2, bi (5*j)), (3, bi (5*j+1)), (4, bi (5*j+2)), (5, bi (5*j+3)), (6, bi (5*j+4))
                , (7, bt (5*j)), (8, bt (5*j+1)), (9, bt (5*j+2)), (10, bt (5*j+3))
                , (11, bt (5*j+4)) ] } ]

/-- The `a`-th `complete_add` of the MSM chain: `Rₐ = Lₐ + Pₐ₊₁`, `L₀ = P₀`, `Lₐ = Rₐ₋₁`.
⚑ Over the NON-CONSTANT partition since 2026-08-03 (`msmLive`), i.e. `live.length − 1` adds — which
is Mina's own `List.reduce_exn` over `non_constant_part` (`step_verifier.ml:180-182`) and is what
its compiled step circuit's single run of **30 consecutive `CompleteAdd` rows** is. -/
def msmAddRow (s : StepShape) (m : MsmData) (a : Nat) : SRow :=
  let bm := baseMsm s
  let live := msmLive s
  let i0 := live.getD 0 0
  let i1 := live.getD (a + 1) 0
  let lp := if a == 0 then pAcc s i0 (msmChunksAt i0) else pSum s (a - 1)
  let rp := pAcc s i1 (msmChunksAt i1)
  let c := m.addCells.getD a []
  { kind := .completeAdd
  , perm := [ some (mpxAt bm lp), some (mpyAt bm lp), some (mpxAt bm rp), some (mpyAt bm rp)
            , some (mpxAt bm (pSum s a)), some (mpyAt bm (pSum s a)), none ]
  , advice := [ (7, (c.getD 7 0 : Int)), (8, (c.getD 8 0 : Int))
              , (9, (c.getD 9 0 : Int)), (10, (c.getD 10 0 : Int)) ] }

/-- **R3's base pins** — `multiscale_known`'s bases are `Inner_curve.constant (lagrange_commitment
~domain srs i)` (`step_verifier.ml:150,165-172,543-544`), so every one that reaches the circuit is
pinned. Before 2026-08-02 every one was a free witness the prover chose.
⚑ Over `msmLive` since 2026-08-03: a CONSTANT-scalar term's base is folded into `constant_part`
outside the circuit (`:133-152`), so upstream pins no in-circuit base for it either. -/
def msmBaseRows (s : StepShape) (m : MsmData) : List SRow :=
  let bm := baseMsm s
  (msmLive s).map (fun i =>
    baseConstRow (mpxAt bm (pT s i)) (mpyAt bm (pT s i)) (m.terms.getD i default).T)

/-- **`scale_fast_unpack`'s OWN SEED**, `Ops.add_fast base base` (`plonk_curve_ops.ml:157`) — one
`CompleteAdd` row per LADDER (`msmLive`, since 2026-08-03), DEFINING `pAcc i 0` instead of leaving
it a witness.

⚑ THE HOLE THIS CLOSES. The ladder is `accₖ₊₁ = [2]accₖ + (2bₖ−1)·T`, so
`acc_N = 2^{5·msmChunksAt i}·acc₀ + Σₖ (2bₖ−1)·2^{5·msmChunksAt i−1−k}·T`. Doubling is a BIJECTION on the
group, so for ANY target point the prover solves for `acc₀` — and nothing else in R3 objects: the
base is pinned (`msmBaseRows`), the bits are the chunk rows' own advice, and the counter chain closes
on the challenge variable, none of which say a word about the seed. `multiscale_known`'s output —
`x_hat`, a PUBLIC word here and a segment-C absorption — was the prover's outright. §12f exhibits the
witness. §6b's `ft_comm` ladders carried this row from the start (`ftcTermRows`'s `caRow g g`); R3's
did not. -/
def msmDblRow (s : StepShape) (m : MsmData) (i : Nat) : SRow :=
  let bm := baseMsm s
  let T := (m.terms.getD i default).T
  let c := completeAddWitness T.1 T.2 T.1 T.2
  { kind := .completeAdd
  , perm := [ some (mpxAt bm (pT s i)), some (mpyAt bm (pT s i))
            , some (mpxAt bm (pT s i)), some (mpyAt bm (pT s i))
            , some (mpxAt bm (pAcc s i 0)), some (mpyAt bm (pAcc s i 0)), none ]
  , advice := [ (7, (c.getD 7 0 : Int)), (8, (c.getD 8 0 : Int))
              , (9, (c.getD 9 0 : Int)), (10, (c.getD 10 0 : Int)) ] }

/-- **`let n_acc = ref Field.zero`** (`plonk_curve_ops.ml:158`) — the SECOND free witness of the same
two lines, one `Generic` half per MSM term.

⚑ `Field.zero` is a CONSTANT upstream; here `vSN i 0` was a variable no row read. The chunk rows
constrain `n' = 32·n + Σ_t 2^{4−t}·b_t`, so the chain closes on
`n_final = 32^{msmChunksAt i}·n₀ + (the bits as an integer)` — and `n_final` IS the challenge variable
(`vSN i (msmChunksAt i) = vN (msmChal i) emsRows`). With `n₀` free a prover picks ANY bit vector and
solves `n₀ = (n_final − bits)·32^{−msmChunksAt i}`; the bits he picks are the multiplier the ladder actually
uses. That is the acc₀ hole through the other cell, and §12f exhibits it too.

⚠ **ONLY THE TERMS THAT RUN A LADDER.** On a zero-chunk term `vSN i 0` IS `vSN i (msmChunksAt i)`,
i.e. the term's CHALLENGE variable (§2), so a `w₀ = 0` half over it would pin that challenge — and
challenges are shared round-robin (`msmChal i = i % chals`), so it would pin R2's chain, R4's fold
and the deferred values with it. Upstream has no `n_acc` there either: `scale_fast_unpack ~num_bits:0`
runs zero chunk iterations and its `Field.Assert.equal !n_acc scalar` (`plonk_curve_ops.ml:207`) is
about a scalar this file does not model. -/
def msmNZeroRows (s : StepShape) : List SRow :=
  let bsn := baseSN s
  packHalves (((List.range s.msmTerms).filter (fun i => msmChunksAt i != 0)).map (fun i =>
    ([some (vSNAt s bsn i 0), none, none], cConst 0)))

/-- **R3's rows.** ⚑ Per-term chunk counts since §1b: a term whose statement word is one bit emits
NO `VarBaseMul` row, which is what makes the emitted `x_hat` region **31 ladders** at Mina's own
widths rather than 40 at a uniform 26.
⚑⚑ …and since 2026-08-03 the whole REGION is the non-constant partition (`msmLive`): the nine
one-bit words get no base pin, no `add_fast base base` seed, no probe and no fold add, because
`multiscale_known` folds their bases into `constant_part` outside the circuit
(`step_verifier.ml:133-152`). The fold chain is `live − 1 = 30` `CompleteAdd`s, which is the single
run of thirty consecutive `CompleteAdd` rows in Mina's own compiled `step-zkapp-proved`. -/
def msmRows (s : StepShape) (m : MsmData) (wired : Bool) : List SRow :=
  let bm := baseMsm s
  let live := msmLive s
  let i0 := live.getD 0 0
  msmBaseRows s m
  ++ msmNZeroRows s
  ++ [msmDblRow s m i0]
  ++ ((List.range (msmChunksAt i0)).flatMap (msmChunkRows s m i0))
  ++ [probeRow wired (mpxAt bm (pAcc s i0 (msmChunksAt i0)))
                     (mpyAt bm (pAcc s i0 (msmChunksAt i0)))]
  ++ (List.range (live.length - 1)).flatMap (fun a =>
       let i := live.getD (a + 1) 0
       [msmDblRow s m i]
       ++ ((List.range (msmChunksAt i)).flatMap (msmChunkRows s m i))
       ++ [probeRow wired (mpxAt bm (pAcc s i (msmChunksAt i)))
                          (mpyAt bm (pAcc s i (msmChunksAt i)))]
       ++ [msmAddRow s m a]
       ++ [probeRow wired (mpxAt bm (pSum s a)) (mpyAt bm (pSum s a))])

/-! ## §7 — R4, the IPA / commitment FOLD (`Scalar_challenge.endo`).

`endo_mul` chains by ROW OVERLAP, not by σ: row `r+1` is simultaneously block `r`'s `Next`
(`w'₄=xs w'₅=ys w'₆=n'`) and block `r+1`'s `Curr` (`w₄=xp w₅=yp w₆=n`) — the SAME three cells. The
base point at cols 0,1 IS a σ class of `ipaBlocks` cells, and the FINAL scalar counter (on the tail
`Zero` row, col 6) is the round's CHALLENGE variable. -/

/-- ⚑ **`Scalar_challenge.endo`'s OWN SEED** (`scalar_challenge.ml:230-234`), verbatim:

    let acc =
      with_label __LOC__ (fun () ->
          let p = G.( + ) t (seal (Field.scale xt Endo.base), yt) in
          ref G.(p + p) )
    in
    let n_acc = ref Field.zero in

`φ(t) = (endo·xt, yt)` is the endomorphism image — `Endo.base` is the base field's primitive cube
root, `KimchiRenderEndoMul.endo = PastaCurve.zetaP` — so the seed is `2·(t + φ(t))`, THREE rows: a
`Generic` half for `endo·xt` and two `Ops.add_fast`s. ⚠ Until 2026-08-02 `runIpa` seeded at `dblA T`
with `qAcc r 0` and `vQN r 0` read by NO row, which was both a free-witness hole of R3's exact class
(§12f) and the wrong point: `2t` is not `2(t + φ(t))`, so the fold's arithmetic was self-consistent
but was not `Scalar_challenge.endo`. -/
def endoQ (T : Nat × Nat) : Nat × Nat :=
  (fMul Dregg2.Circuit.Emit.KimchiRenderEndoMul.endo T.1, T.2)
/-- `p = add_fast t φ(t)`. -/
def endoP (T : Nat × Nat) : Nat × Nat := addA T (endoQ T)
/-- `acc₀ = add_fast p p`. -/
def endoSeed (T : Nat × Nat) : Nat × Nat := dblA (endoP T)

structure IpaData where
  accs : List (List (Nat × Nat))
  blks : List (List EndoBlock)
  ns : List (List Nat)
  bases : List (Nat × Nat)
  sums : List (Nat × Nat)
  addCells : List (List Nat)
  /-- ⚑ `check_bulletproof`'s tail (`:325-327`): `Scalar_challenge.endo q c`'s accumulator trace,
  its blocks, its counter chain, and the closing `add_fast` with `delta`. -/
  lhsAccs : List (Nat × Nat) := []
  lhsBlks : List EndoBlock := []
  lhsNs : List Nat := []
  lhsAdd : List Nat := []
  /-- ⚑ §19: `q = p_prime + lr_prod` (`:316-320`) — the fold sum PLUS `uc`. `Scalar_challenge.endo`
  reads THIS point; `sums.getLast` is only `combined_polynomial + lr_prod`. -/
  qPrimeAdd : List Nat := []
  deriving Repr, Inhabited

/-- One `Scalar_challenge.endo` ladder over base `T` at prechallenge `v`, seeded at
`scalar_challenge.ml:230-235`. Shared by the fold's rounds and by `check_bulletproof`'s tail. -/
def runEndo (s : StepShape) (T : Nat × Nat) (v : Nat)
    : List (Nat × Nat) × List EndoBlock × List Nat :=
  let bits := endoBitsOf s v
  (List.range s.ipaBlocks).foldl
    (fun (st : List (Nat × Nat) × List EndoBlock × List Nat) e =>
      let cur := st.1.getLastD (0, 0)
      let b := endoStep T.1 T.2 cur.1 cur.2
        (bits.getD (4*e) 0) (bits.getD (4*e+1) 0) (bits.getD (4*e+2) 0) (bits.getD (4*e+3) 0)
      (st.1 ++ [(b.xs, b.ys)], st.2.1 ++ [b],
       st.2.2 ++ [16 * st.2.2.getLastD 0 + 8*b.b1 + 4*b.b2 + 2*b.b3 + b.b4]))
    ([endoSeed T], [], [0])

/-- ⚑ `ftcOut` is `Common.ft_comm`'s ASSEMBLED value — round `FTC_ROUND`'s base since §6b. The
supplied list still carries `COMBINE_XY[3]` (the real block's own `ft_comm`) and the assembly
IGNORES it: that round's base is computed, so a supplied one would be a second copy.

⚑ THE FOLD CHAIN NOW STARTS AT COMMITMENT 0. `combine_split_commitments` is called with
`~init:(function `Finite x -> `Finite x | …)` (`step_verifier.ml:606`), i.e. the accumulator IS
`sg_old[0]`; every round's output is folded into it, so there are `ipaRounds` adds and not
`ipaRounds − 1`. Until 2026-08-02 the chain started at round 0's output and `sg_old[0]` was one of
the three transcript words nothing read. -/
def runIpa (s : StepShape) (allB : List (Nat × Nat)) (d : SpongeData) (ftcOut : Nat × Nat)
    (ucRes : Nat × Nat) : IpaData :=
  let bases := (List.range s.ipaRounds).map (fun r =>
    if ipaSrc s r == BaseSrc.computed then ftcOut else ipaBaseOf s allB r)
  let rounds := (List.range s.ipaRounds).map (fun r =>
    runEndo s (bases.getD r (0, 0)) (chalOf s d (s.ipaChal r)))
  let pts := rounds.map (fun r => r.1.getLastD (0, 0))
  let st := (List.range s.ipaRounds).foldl
    (fun (acc : List (Nat × Nat) × List (List Nat)) a =>
      let l := if a == 0 then Dregg2.Bridge.MinaStepPrevCommitments.SG_OLD0_XY
               else acc.1.getLastD (0, 0)
      let r := pts.getD a (0, 0)
      let cells := completeAddWitness l.1 l.2 r.1 r.2
      (acc.1 ++ [(cells.getD 4 0, cells.getD 5 0)], acc.2 ++ [cells]))
    ([], [])
  -- ⚑ §19: `q = p_prime + lr_prod` — the fold sum plus `uc = scale_fast2 u cip` (`:316-320`).
  let q0 := st.1.getLastD (0, 0)
  let qpc := completeAddWitness q0.1 q0.2 ucRes.1 ucRes.2
  let q : Nat × Nat := (qpc.getD 4 0, qpc.getD 5 0)
  -- ⚑ `check_bulletproof`'s tail: `cq = Scalar_challenge.endo q c`, `lhs = cq + delta`.
  let lhs := runEndo s q (chalOf s d s.cChal)
  let cq := lhs.1.getLastD (0, 0)
  let dl := Dregg2.Bridge.MinaStepPrevCommitments.DELTA_XY
  { accs := rounds.map (·.1), blks := rounds.map (·.2.1), ns := rounds.map (·.2.2)
  , bases := bases, sums := st.1, addCells := st.2
  , lhsAccs := lhs.1, lhsBlks := lhs.2.1, lhsNs := lhs.2.2
  , lhsAdd := completeAddWitness cq.1 cq.2 dl.1 dl.2
  , qPrimeAdd := qpc }

/-- One endo ladder's variable slots — the fold's rounds and `check_bulletproof`'s tail differ only
in where their points and counters live. -/
structure EndoSlots where
  /-- the base point's index. -/
  base : Nat
  /-- the seed intermediate `p = t + φ(t)`. -/
  p : Nat
  /-- accumulator point after `e` blocks. -/
  acc : Nat → Nat
  /-- counter after `e` blocks; at `e = ipaBlocks` it is the challenge variable. -/
  n : Nat → PVar
  /-- `endo · x_t`. -/
  endoX : PVar

/-- ⚑ ONE `baseQN` for the whole ladder, not one per block: `n` is `vQNAt`'s partial application and
`endoX` is a strict field, so the region chain (and the `spLay` under it) is walked once here rather
than `ipaBlocks + 1` times inside `endoRoundRows`. -/
def roundSlots (s : StepShape) (r : Nat) : EndoSlots :=
  let bq := baseQN s
  { base := qT s r, p := qP s r, acc := qAcc s r, n := vQNAt s bq r, endoX := vQEndoAt s bq r }
/-- ⚑ The tail's base is the FOLD OUTPUT `q = p_prime + lr_prod` — a computed point, not a supplied
one, so it needs no pin and no `assert_on_curve`. ⚑ Since §19 it is `qPrime` and not
`qSum (ipaRounds−1)`: `p_prime` carries the `uc` term, so `combined_inner_product` reaches `lhs`. -/
def lhsSlots (s : StepShape) : EndoSlots :=
  let bq := baseQN s
  { base := qPrime s, p := qLhsP s, acc := qLhsAcc s
  , n := vLhsNAt s bq, endoX := vLhsEndoAt s bq }

/-- ⚑⚑ **THE HOTTEST FUNCTION IN THE ASSEMBLY.** Every `endo_mul` row names four IPA point variables
and one counter, at 32 blocks a ladder and 77 ladders (`ipaRounds = 76` fold rounds plus
`check_bulletproof`'s tail) — **12 551 variable names**, and each one used to walk the region chain
down to `spLay`. ⚑ ONE `baseIpa` here and ONE `baseQN` in `roundSlots`/`lhsSlots`; the emitted names
are the same by `ipx`/`ipy`'s own definitions (`ipx s p = ipxAt (baseIpa s) p`, by delta). -/
def endoRoundRows (s : StepShape) (sl : EndoSlots) (bl : List EndoBlock) : List SRow :=
  let bi := baseIpa s
  (List.range s.ipaBlocks).map (fun e =>
    let b := bl.getD e default
    ({ kind := .endoMul
     , perm := [ some (ipxAt bi sl.base), some (ipyAt bi sl.base), none, none
               , some (ipxAt bi (sl.acc e)), some (ipyAt bi (sl.acc e)), some (sl.n e) ]
     , advice := [ (2, (b.inv : Int)), (3, 0), (7, (b.xr : Int)), (8, (b.yr : Int))
                 , (9, (b.s1 : Int)), (10, (b.s3 : Int)), (11, (b.b1 : Int)), (12, (b.b2 : Int))
                 , (13, (b.b3 : Int)), (14, (b.b4 : Int)) ] } : SRow))
  ++ [ { kind := .zero
       , perm := [ none, none, none, none, some (ipxAt bi (sl.acc s.ipaBlocks))
                 , some (ipyAt bi (sl.acc s.ipaBlocks)), some (sl.n s.ipaBlocks) ] } ]

def ipaRoundRows (s : StepShape) (v : IpaData) (r : Nat) : List SRow :=
  endoRoundRows s (roundSlots s r) (v.blks.getD r [])

/-- ⚑ The `a`-th fold add. `a = 0`'s LEFT operand is `qInit` — `sg_old[0]`, the `~init` accumulator
(`step_verifier.ml:606`) whose two coordinates ARE transcript block `oSgOld0`'s absorbed words. -/
def ipaAddRow (s : StepShape) (v : IpaData) (a : Nat) : SRow :=
  let bi := baseIpa s
  let lp := if a == 0 then qInit s else qSum s (a - 1)
  let rp := qAcc s a s.ipaBlocks
  let c := v.addCells.getD a []
  { kind := .completeAdd
  , perm := [ some (ipxAt bi lp), some (ipyAt bi lp), some (ipxAt bi rp), some (ipyAt bi rp)
            , some (ipxAt bi (qSum s a)), some (ipyAt bi (qSum s a)), none ]
  , advice := [ (7, (c.getD 7 0 : Int)), (8, (c.getD 8 0 : Int))
              , (9, (c.getD 9 0 : Int)), (10, (c.getD 10 0 : Int)) ] }

/-- **R4's base pins** — ONLY the verifier-key CONSTANTS (`ipaSrc r = .const`). The absorbed ones are
pinned by nothing here on purpose: they are the previous proof's, and what binds them is that their
two variables ARE transcript block `b`'s absorbed words. ⚑ Round `FTC_ROUND` is in neither set since
§6b: its base is `.computed`, so a pin row there would be pinning a derived value to a literal. -/
def ipaBaseRows (s : StepShape) (v : IpaData) : List SRow :=
  let bi := baseIpa s
  ((List.range s.ipaRounds).filter (fun r => ipaSrc s r == BaseSrc.const)).map (fun r =>
    baseConstRow (ipxAt bi (qT s r)) (ipyAt bi (qT s r)) (v.bases.getD r (0, 0)))

/-! ### §7b — `Inner_curve.typ`'s CHECK on every SUPPLIED point.

⚑ THE HOLE THIS CLOSES. `EndoMul`, `VarBaseMul` and `CompleteAdd` constrain the ADDITION ARITHMETIC
and nothing else: every one of their polynomials is satisfied by any `(x, y)` in the field, on or
off the curve. Upstream never has to think about it because a supplied point arrives through
`Inner_curve.typ`, whose `check` IS `assert_on_curve` (`snarky_curve.ml:219-229`) — Snarky runs it
on every `exists` of that type. This file read the previous proof's commitments in as bare
coordinate variables, so an off-curve "commitment" satisfied every gate. §12b′ exhibits one.

The CONSTANT bases need no check and get none, which is upstream's shape too: an
`Inner_curve.constant` is a literal, and here it is pinned coordinate-for-coordinate by a `Generic`
row — strictly stronger than membership. So the checked set is exactly the ABSORBED bases. -/

/-- `Pallas.Params.b`. `Params.a = 0`, so the `a·x` term of `assert_on_curve` folds away; a curve
with `a ≠ 0` would need one more half and one more variable, and this is where that would go. -/
def PALLAS_B : Nat := 5

/-- `assert_on_curve (x, y)` as three `Generic` halves: `x2 = x·x`, `x3 = x2·x`, and
`y·y − x3 − b = 0` — the `assert_square` with the linear combination folded into the coefficients,
which is what Snarky's `Basic.Square` emits. -/
def onCurveHalvesAt (bo : Nat) (k : Nat) (vx vy : PVar) :
    List (List (Option PVar) × List Int) :=
  [ ([some vx, some vx, some (vOcX2At bo k)], cMul)
  , ([some (vOcX2At bo k), some vx, some (vOcX3At bo k)], cMul)
  , ([some vy, some vy, some (vOcX3At bo k)], [0, 0, -1, 1, -(PALLAS_B : Int)]) ]
def onCurveHalves (s : StepShape) (k : Nat) (vx vy : PVar) :
    List (List (Option PVar) × List Int) := onCurveHalvesAt (baseOnC s) k vx vy

/-- The `k`-th CHECKED point's coordinate VARIABLES: the `absRoundList` fold bases, `t_comm`'s
`tCommN` chunks, and — since the R1 interleaving — `sg_old[0]` and `delta`. Every SUPPLIED commitment
the transcript swallows, and no other. -/
def onCVarAt (s : StepShape) (bi : Nat) (k : Nat) : PVar × PVar :=
  let l := (absRoundList s).length
  let t := l + tCommN s
  if k < l then let r := (absRoundList s).getD k 0; (ipxAt bi (qT s r), ipyAt bi (qT s r))
  else if k < t then (vTcX s (k - l), vTcY s (k - l))
  else if k == t then (ipxAt bi (qInit s), ipyAt bi (qInit s))
  else if k == t + 1 then (ipxAt bi (qDel s), ipyAt bi (qDel s))
  else (vGx s, vGy s)
def onCVar (s : StepShape) (k : Nat) : PVar × PVar := onCVarAt s (baseIpa s) k

/-- **R4's on-curve rows** — one `assert_on_curve` per ABSORBED commitment, over the very coordinate
variables the transcript absorbed and the `EndoMul` (or, for `t_comm`, the `VarBaseMul`) chain
multiplies. -/
def onCurveRows (s : StepShape) : List SRow :=
  let bi := baseIpa s
  let bo := baseOnC s
  packHalves ((List.range (nOnC s)).flatMap (fun k =>
    let v := onCVarAt s bi k
    onCurveHalvesAt bo k v.1 v.2))

/-- **`Scalar_challenge.endo`'s SEED PINS**, two `Generic` halves per round
(`scalar_challenge.ml:232,235`): `endo·xt − xq = 0` and `n_acc = Field.zero`. ⚑ Both cells were free
witnesses until 2026-08-02 — `vQN r 0` in exactly R3's way (the counter closes on the challenge from
`16^{ipaBlocks}·n₀ + bits`, so a free `n₀` buys any bit vector), and `vQEndo r` is new because the
seed's second operand did not exist as a variable at all. -/
def seedPinHalvesAt (bi : Nat) (sl : EndoSlots) : List (List (Option PVar) × List Int) :=
  [ ([some (ipxAt bi sl.base), none, some sl.endoX],
     [ (Dregg2.Circuit.Emit.KimchiRenderEndoMul.endo : Int), 0, -1, 0, 0 ])
  , ([some (sl.n 0), none, none], cConst 0) ]
def seedPinHalves (s : StepShape) (sl : EndoSlots) : List (List (Option PVar) × List Int) :=
  seedPinHalvesAt (baseIpa s) sl

def ipaSeedPinRows (s : StepShape) : List SRow :=
  let bi := baseIpa s
  packHalves ((List.range s.ipaRounds).flatMap (fun r => seedPinHalvesAt bi (roundSlots s r))
              ++ seedPinHalvesAt bi (lhsSlots s))

/-- **Round `r`'s two `Ops.add_fast`s**: `p = t + φ(t)` and `acc₀ = p + p`. The probe between them
keeps every `CompleteAdd` run at length 1 and materialises `p` as a σ-only boundary value. ⚑ `φ(t)`'s
`y` IS `t`'s — `(seal (Field.scale xt Endo.base), yt)` — so the row reads `ipy (qT r)` at cols 1
AND 3, which is upstream's own shape and not a wiring accident. -/
def endoSeedRows (s : StepShape) (sl : EndoSlots) (T : Nat × Nat) (wired : Bool) : List SRow :=
  let bi := baseIpa s
  let q := endoQ T
  let p := endoP T
  [ caRow (ipxAt bi sl.base, ipyAt bi sl.base) (sl.endoX, ipyAt bi sl.base)
          (ipxAt bi sl.p, ipyAt bi sl.p) (completeAddWitness T.1 T.2 q.1 q.2)
  , probeRow wired (ipxAt bi sl.p) (ipyAt bi sl.p)
  , caRow (ipxAt bi sl.p, ipyAt bi sl.p) (ipxAt bi sl.p, ipyAt bi sl.p)
          (ipxAt bi (sl.acc 0), ipyAt bi (sl.acc 0)) (completeAddWitness p.1 p.2 p.1 p.2) ]

def ipaSeedRows (s : StepShape) (v : IpaData) (wired : Bool) (r : Nat) : List SRow :=
  endoSeedRows s (roundSlots s r) (v.bases.getD r (0, 0)) wired

/-- ⚑ `q = p_prime + lr_prod`'s VALUE — §19's `uc` folded into the fold sum. -/
def IpaData.qPrimePt (v : IpaData) : Nat × Nat := (v.qPrimeAdd.getD 4 0, v.qPrimeAdd.getD 5 0)

/-- ⚑ **`check_bulletproof`'s TAIL** (`step_verifier.ml:321-327`), the consumer that makes `delta` an
absorbed word something READS:

    absorb sponge PC delta ;
    let c = squeeze_scalar sponge in
    let lhs = let cq = Scalar_challenge.endo q c in cq + delta in

One `Scalar_challenge.endo` over the fold output `q = qSum (ipaRounds−1)` at the LAST transcript
squeeze, seeded at `scalar_challenge.ml:230-235` like every other round, then one `Ops.add_fast` with
`delta` — whose two coordinate variables ARE transcript block `oDelta`'s absorbed words.

⚠ WHAT THIS DOES NOT DO, at the point of use: `lhs` is not compared with `rhs`. `equal_g lhs rhs`
(`:340`) is the IPA opening's own equality and `rhs` needs `scale_fast2 u advice.b`,
`challenge_polynomial_commitment`, `z_1`, `z_2` and `Generators.h` — that is `verified` (#11), still a
witnessed boolean here. What IS closed is that `delta` and `c` are no longer words the sponge eats
and nothing reads: bend either and this ladder's own gate polynomials move.

⚠ ⚑ **AND `equal_g` WOULD REFUSE NO ON-CURVE SUBSTITUTION — MEASURED (§17), which inverts the reason
this rung was queued.** `G = challenge_polynomial_commitment`, `z_1` and `z_2` occur at exactly two
places each in `step_verifier.ml` (`:253` destructure, `:332-336` use): no absorption, no pin, no
statement word, no other consumer. So for ANY `lhs` a prover sets `G := z_1⁻¹·(lhs − z_2·H) − b·u` —
one scalar-field inverse and three scalar multiplications — and the equality holds. §17 exhibits it
on this assembly's own values: honest CLOSES, the on-curve-substituted assembly with the same `G`
REFUSED, the same substitution with `G` re-solved ACCEPTED. ⚑ `G`'s binder — `step_main.ml:525-566`,
one rung ABOVE `verify_one` — is ASSEMBLED since 2026-08-02 (segment D, §8e′), and **the re-solved
witness is STILL ACCEPTED**: what changed is that it now moves the step statement's public
`messages_for_next_step_proof` (§17(d)–(e)). -/
def lhsRows (s : StepShape) (v : IpaData) (wired : Bool) : List SRow :=
  let bi := baseIpa s
  let sl := lhsSlots s
  endoSeedRows s sl v.qPrimePt wired
  ++ endoRoundRows s sl v.lhsBlks
  ++ [ probeRow wired (ipxAt bi (sl.acc s.ipaBlocks)) (ipyAt bi (sl.acc s.ipaBlocks))
     , caRow (ipxAt bi (sl.acc s.ipaBlocks), ipyAt bi (sl.acc s.ipaBlocks))
             (ipxAt bi (qDel s), ipyAt bi (qDel s))
             (ipxAt bi (qLhsOut s), ipyAt bi (qLhsOut s)) v.lhsAdd
     , probeRow wired (ipxAt bi (qLhsOut s)) (ipyAt bi (qLhsOut s)) ]

/-- **R4's rows.** -/
def ipaRows (s : StepShape) (v : IpaData) (wired : Bool) : List SRow :=
  let bi := baseIpa s
  ipaBaseRows s v
  ++ ipaSeedPinRows s
  ++ onCurveRows s
  ++ (List.range s.ipaRounds).flatMap (fun r =>
       ipaSeedRows s v wired r
       ++ ipaRoundRows s v r
       ++ [probeRow wired (ipxAt bi (qAcc s r s.ipaBlocks)) (ipyAt bi (qAcc s r s.ipaBlocks))]
       ++ [ipaAddRow s v r]
       ++ [probeRow wired (ipxAt bi (qSum s r)) (ipyAt bi (qSum s r))])
  -- ⚑ §19: `q = p_prime + lr_prod` (`:316-320`) — the `Ops.add_fast` that puts `uc` into the point
  -- `Scalar_challenge.endo q c` reads. It rides here and not in §19's own block because `lhsRows` is
  -- its only consumer; `bpResX/Y 0` is `uc`, defined by §19's ladder 0.
  ++ [ caRow (ipxAt bi (qSum s (s.ipaRounds - 1)), ipyAt bi (qSum s (s.ipaRounds - 1)))
             (bpResX s 0, bpResY s 0) (ipxAt bi (qPrime s), ipyAt bi (qPrime s)) v.qPrimeAdd
     , probeRow wired (ipxAt bi (qPrime s)) (ipyAt bi (qPrime s)) ]
  ++ lhsRows s v wired

/-! ## §6b — `Common.ft_comm`'s MSM: the sub-circuit that makes `t_comm` MEAN something.

`common.ml:238-256`, verbatim:

    let ft_comm ~add:( + ) ~scale ~endoscale ~negate ~verification_key:m ~alpha ~plonk ~t_comm =
      let ( * ) x g = scale g x in
      let _, [ sigma_comm_last ] = Vector.split m.sigma_comm (…) in
      let f_comm = List.reduce_exn ~f:( + ) [ plonk.perm * sigma_comm_last ] in
      let chunked_t_comm =
        let n = Array.length t_comm in
        let res = ref t_comm.(n - 1) in
        for i = n - 2 downto 0 do res := t_comm.(i) + scale !res plonk.zeta_to_srs_length done ;
        !res
      in
      f_comm + chunked_t_comm + negate (scale chunked_t_comm plonk.zeta_to_domain_size)

instantiated at `step_verifier.ml:587-591` with `~add:Ops.add_fast ~scale:scale_fast2
~negate:Inner_curve.negate ~verification_key:m ~plonk ~t_comm`, and `scale_fast2 p s = Ops.scale_fast2
p s ~num_bits:Field.size_in_bits` (`:240-242`) — **255 bits, uniformly, all eight of them.** So
`chunks_needed ~num_bits:254 = 51` five-bit chunks per scale (`plonk_curve_ops.ml:66-70,254-257`).

⚑ **WHY THIS IS THE RUNG AND NOT A ROW COUNT.** Until 2026-08-02 `t_comm`'s seven commitments were
seven `msgVal` fixtures: free variables the transcript ate and nothing read. The previous lane
refused to absorb them on their own and was right to — an absorbed commitment no sub-circuit CONSUMES
is still ground freely, and the only thing absorbing it buys is a smaller number in a census. §12b″
exhibits the grind that was open, and shows what refuses it now.

## THE EIGHT SCALES AND WHERE EACH BASE COMES FROM

    k       base                                  scalar                     provenance of the base
    0       sigma_comm_last = sigma_comm[6]       plonk.perm                 §3c's own pinned var
    1       t_comm[n−1]                           zeta_to_srs_length         TRANSCRIPT-ABSORBED
    2..n−1  resₙ₋ₖ (add k−2's output)             zeta_to_srs_length         COMPUTED
    n       chunked_t_comm = res₀                 zeta_to_domain_size        COMPUTED

and `tCommN + 1` `Ops.add_fast`s: the `n−1` Horner adds `resₙ₋₂₋ₐ = t_comm[n−2−a] + scale(a+1)`,
then `f_comm + chunked_t_comm`, then `+ negate (…)`. The last one's OUTPUT is R4 round `FTC_ROUND`'s
base — `combine_split_commitments`' commitment 3 (`step_verifier.ml:606`), which was an
`Inner_curve.constant` carrying the real block's `COMBINE_XY[3]` and is now derived.

## ⚑ THE SCALARS, AND THE ONE DIVERGENCE FROM UPSTREAM — NAMED, AND IT IS A STRENGTHENING

Upstream's `plonk` here is `unfinalized.deferred_values.plonk` mapped through
`Plonk.In_circuit.to_wrap` (`step_verifier.ml:1264-1267`), whose `'fp` is
`Other_field.t Shifted_value.Type2.t` — i.e. **`(Field.t * Boolean.var)` statement words over the
OTHER field** (`impls.ml:50-57`). Nothing in the step circuit constrains them: `Plonk_checks.checked`
(R6/R8) compares the **`Fp` Type1** twins of the same deferred values, and the `Fq` Type2 twins are
checked by the NEXT wrap proof. So upstream's `ft_comm` multiplies by three values a step-circuit
prover chooses.

Here they are R6's OWN derived cells — `Plonk_checks.checked`'s `perm` and the `ζ^n` slot — split
into `(s_div_2, s_odd)` by a row that reads that cell. That is strictly MORE constrained than
upstream inside this circuit, and it is why `ft_comm`'s output is a function of the transcript rather
than of a witness.
⚠ **THE RESIDUE, stated rather than absorbed.** `Shifted_value.Type2`'s shift lives in the OTHER
field (`shifted_value.ml:178-188`: `to_field t = t + 2^{size_in_bits}`), so what this ladder computes
is `[s + 2^255]·g` for the wired `s` — upstream's own emitted arithmetic, with the shift's
cancellation an `Fq`-side fact this circuit cannot see. And ⚑ at `log2n = srs_length_log2 = 16`
(`FT_LOG2N`; `plonk_checks.ml:496-497`) `zeta_to_srs_length` and `zeta_to_domain_size` are the SAME
field element, so the Horner steps and the closing scale share one scalar here; at a shape where the
wrap domain and the step SRS length differ they would not, and that is a shape fact, not a wiring
one. -/

/-- The `5·FTC_CHUNKS = 255` bits of `v`, MSB-first — `scale_fast_unpack`'s `bits_msb`
(`plonk_curve_ops.ml:151-156`), at `actual_bits_used = chunks_needed · 5`. -/
def ftcBitsOf (v : Nat) : List Nat :=
  (List.range (5 * FTC_CHUNKS)).map (fun k => v / 2 ^ (5 * FTC_CHUNKS - 1 - k) % 2)

/-- The two scalar cells `ft_comm` reads, as VARIABLE + VALUE. Passed in rather than reached for, so
§6b has no forward dependency on §8d's compiled program. -/
structure FtcWire where
  /-- `plonk.perm` — R6's `Plonk_checks.checked` slot. -/
  permV : PVar
  permVal : Nat
  /-- `plonk.zeta_to_srs_length` = `plonk.zeta_to_domain_size` — R6's `ζ^n` slot. -/
  zetaV : PVar
  zetaVal : Nat
  deriving Repr, Inhabited

/-- Scalar block `c`'s variable and value. -/
def ftcScalV (W : FtcWire) (c : Nat) : PVar := if c == 0 then W.permV else W.zetaV
def ftcScalVal (W : FtcWire) (c : Nat) : Nat := if c == 0 then W.permVal else W.zetaVal

/-- One evaluated `scale_fast2` (`plonk_curve_ops.ml:251-267`). -/
structure FtcTerm where
  /-- the `scale_fast_unpack` ladder: base, 256 accumulator points, 255 slopes, 256 counters. -/
  td : TermData
  bits : List Nat
  /-- `Ops.add_fast g g` — `scale_fast_unpack`'s own `acc := ref (add_fast base base)` (`:157`).
  Without this row `acc₀` is a free witness and the ladder's OUTPUT is the prover's. -/
  dblCells : List Nat
  /-- `add_fast h (G.negate g)` — the `s_odd = 0` branch (`:267`). -/
  hMg : Nat × Nat
  hMgCells : List Nat
  /-- `G.if_ s_odd ~then_:h ~else_:(h − g)`. -/
  res : Nat × Nat
  deriving Repr, Inhabited

/-- `Common.ft_comm`, evaluated. -/
structure FtcData where
  terms : List FtcTerm
  /-- the `tCommN` `Ops.add_fast` outputs that get variables: the `n−1` Horner partials, then
  `f_comm + chunked_t_comm`. -/
  adds : List (Nat × Nat)
  /-- …and all `tCommN + 1` of their cell vectors, the last being the closing subtraction. -/
  addCells : List (List Nat)
  /-- ⚑ **`Common.ft_comm`.** R4 round `FTC_ROUND`'s base. -/
  out : Nat × Nat
  deriving Repr, Inhabited

/-- `sigma_comm_last` — `Vector.split m.sigma_comm` hands `common.ml:243-245` the SEVENTH permutation
commitment, which is `INDEX_XY[6]` and the one plonk-index commitment the fold does not carry. -/
def ftcSigma : Nat × Nat := Dregg2.Bridge.MinaStepPrevCommitments.INDEX_XY.getD 6 (0, 0)
def ftcTc (i : Nat) : Nat × Nat := Dregg2.Bridge.MinaStepPrevCommitments.T_COMM_XY.getD i (0, 0)

/-- ONE `scale_fast2` over base `g` and scalar `sv`. -/
def ftcScaleTerm (g : Nat × Nat) (sv : Nat) : FtcTerm :=
  let bits := ftcBitsOf (sv / 2)
  let td := runVbm g (dblA g) bits
  let h := td.accs.getLastD (0, 0)
  let ng : Nat × Nat := (g.1, Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fSub 0 g.2)
  let hc := completeAddWitness h.1 h.2 ng.1 ng.2
  let hmg : Nat × Nat := (hc.getD 4 0, hc.getD 5 0)
  { td := td, bits := bits
  , dblCells := completeAddWitness g.1 g.2 g.1 g.2
  , hMg := hmg, hMgCells := hc
  , res := if sv % 2 == 1 then h else hmg }

/-- **`Common.ft_comm`, run** over a `t_comm` ACCESSOR. The Horner is evaluated in `common.ml`'s own
`downto` order, so term `k ≥ 2`'s base is add `k−2`'s output and the two loops are ONE fold.
Parametrised so §12b″ can re-run it on a prover's substituted quotient commitment. -/
def runFtcWith (s : StepShape) (W : FtcWire) (ftcTc : Nat → Nat × Nat) : FtcData :=
  let n := tCommN s
  let t0 := ftcScaleTerm ftcSigma W.permVal
  let st := (List.range n).foldl
    (fun (acc : List FtcTerm × List (Nat × Nat) × List (List Nat)) j =>
      let k := j + 1
      let g := if k == 1 then ftcTc (n - 1) else acc.2.1.getD (k - 2) (0, 0)
      let tk := ftcScaleTerm g W.zetaVal
      if k + 1 ≤ n then
        let l := ftcTc (n - 1 - k)
        let c := completeAddWitness l.1 l.2 tk.res.1 tk.res.2
        (acc.1 ++ [tk], acc.2.1 ++ [(c.getD 4 0, c.getD 5 0)], acc.2.2 ++ [c])
      else (acc.1 ++ [tk], acc.2.1, acc.2.2))
    ([], [], [])
  let terms := t0 :: st.1
  let chunked := st.2.1.getD (n - 2) (0, 0)
  let cF := completeAddWitness t0.res.1 t0.res.2 chunked.1 chunked.2
  let fc : Nat × Nat := (cF.getD 4 0, cF.getD 5 0)
  let qn := (terms.getD n default).res
  let cO := completeAddWitness fc.1 fc.2 qn.1
              (Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fSub 0 qn.2)
  { terms := terms, adds := st.2.1 ++ [fc], addCells := st.2.2 ++ [cF, cO]
  , out := (cO.getD 4 0, cO.getD 5 0) }

/-- …at the block's OWN quotient commitments, which is the only instance the assembly emits. -/
def runFtc (s : StepShape) (W : FtcWire) : FtcData := runFtcWith s W ftcTc

/-- Term `k`'s base-point VARIABLES. -/
def ftcBaseVar (s : StepShape) (k : Nat) : PVar × PVar :=
  if k == 0 then (vIdxX s 6, vIdxY s 6)
  else if k == 1 then (vTcX s (tCommN s - 1), vTcY s (tCommN s - 1))
  else (ftcAddX s (k - 2), ftcAddY s (k - 2))

/-- ⚑ ONE `scale_fast2` ladder's variable slots, so the SAME emitter serves `Common.ft_comm`'s eight
and §19's four. Introduced 2026-08-03 with §19: the alternative was a second spelling of a 110-row
gadget, and two spellings that agree today are two that disagree later. -/
structure SfSlots where
  baseX : PVar
  baseY : PVar
  /-- accumulator point at chunk boundary `j = 0..FTC_CHUNKS`. -/
  accX : Nat → PVar
  accY : Nat → PVar
  /-- counter at chunk boundary `j`; at `j = FTC_CHUNKS` it IS the scalar's `s_div_2`. -/
  n : Nat → PVar
  /-- `bits_lsb.(254)`, which `plonk_curve_ops.ml:262-265` asserts zero. -/
  top : PVar
  negY : PVar
  hmX : PVar
  hmY : PVar
  dX : PVar
  dY : PVar
  mX : PVar
  mY : PVar
  resX : PVar
  resY : PVar
  /-- `Shifted_value.Type2`'s `s_odd` — the `G.if_` selector. -/
  odd : PVar

/-- Chunk `j` — the same two-row `VarBaseMul` shape R3 uses. ⚑ Chunk 0's `Zero` row wires col 2 (bit
`5j+0`, the MSB) to `top`, so `scale_fast2`'s `bits_lsb.(254) = 0` (`plonk_curve_ops.ml:262-265`) is a
real row: without it the counter identity has two solutions mod `p` and the prover picks the point. -/
def sfChunkRows (sl : SfSlots) (tm : FtcTerm) (j : Nat) : List SRow :=
  let td := tm.td
  let ax : Nat → Int := fun i => ((td.accs.getD i (0, 0)).1 : Int)
  let ay : Nat → Int := fun i => ((td.accs.getD i (0, 0)).2 : Int)
  let bt : Nat → Int := fun i => (td.slopes.getD i 0 : Int)
  let bi : Nat → Int := fun i => (tm.bits.getD i 0 : Int)
  [ { kind := .varBaseMul
    , perm := [ some sl.baseX, some sl.baseY
              , some (sl.accX j), some (sl.accY j)
              , some (sl.n j), some (sl.n (j+1)), none ]
    , advice := [ (7, ax (5*j+1)), (8, ay (5*j+1)), (9, ax (5*j+2)), (10, ay (5*j+2))
                , (11, ax (5*j+3)), (12, ay (5*j+3)), (13, ax (5*j+4)), (14, ay (5*j+4)) ] }
  , { kind := .zero
    , perm := [ some (sl.accX (j+1)), some (sl.accY (j+1))
              , (if j == 0 then some sl.top else none), none, none, none, none ]
    , advice := (if j == 0 then [] else [(2, bi (5*j))])
                ++ [ (3, bi (5*j+1)), (4, bi (5*j+2)), (5, bi (5*j+3)), (6, bi (5*j+4))
                   , (7, bt (5*j)), (8, bt (5*j+1)), (9, bt (5*j+2)), (10, bt (5*j+3))
                   , (11, bt (5*j+4)) ] } ]

/-- **One `scale_fast2`'s rows.** The `G.if_` mux is `d = h − (h−g) ; m = s_odd·d ; res = (h−g) + m`
per coordinate — Snarky's `Field.if_` (`else_ + b·(then_ − else_)`) with the difference sealed,
because a double-`Generic` half carries three variables and `res − else_ − b·(then_ − else_)` needs
four. -/
def sfTermRows (sl : SfSlots) (tm : FtcTerm) (wired : Bool) : List SRow :=
  packHalves
    ([ ([some sl.baseY, some sl.negY, none], [1, 1, 0, 0, 0])
     , ([some sl.top, none, none], cConst 0) ]
     ++ KimchiGadgets.sfMuxHalves sl.odd
          (sl.accX FTC_CHUNKS) sl.hmX sl.dX sl.mX sl.resX
          (sl.accY FTC_CHUNKS) sl.hmY sl.dY sl.mY sl.resY)
  ++ [ caRow (sl.baseX, sl.baseY) (sl.baseX, sl.baseY) (sl.accX 0, sl.accY 0) tm.dblCells ]
  ++ ((List.range FTC_CHUNKS).flatMap (sfChunkRows sl tm))
  ++ [ probeRow wired (sl.accX FTC_CHUNKS) (sl.accY FTC_CHUNKS)
     , caRow (sl.accX FTC_CHUNKS, sl.accY FTC_CHUNKS) (sl.baseX, sl.negY) (sl.hmX, sl.hmY)
             tm.hMgCells
     , probeRow wired sl.resX sl.resY ]

set_option maxRecDepth 100000 in
/-- ⚑ **THE EMITTED OBJECT DID NOT MOVE.** `sfTermRows`' first four rows are what the hand-written
eight-half list produced — the `G.if_` mux on both coordinates, byte-for-byte — for EVERY `SfSlots`,
by `rfl`. Not a case test: a general theorem over every shape. -/
theorem sfTermRows_prefix_is_the_open_coded_shape (sl : SfSlots) (tm : FtcTerm) (wired : Bool) :
    (sfTermRows sl tm wired).take 4 =
      packHalves
        [ ([some sl.baseY, some sl.negY, none], [1, 1, 0, 0, 0])
        , ([some sl.top, none, none], cConst 0)
        , ([some (sl.accX FTC_CHUNKS), some sl.hmX, some sl.dX], [1, -1, -1, 0, 0])
        , ([some sl.odd, some sl.dX, some sl.mX], cMul)
        , ([some sl.hmX, some sl.mX, some sl.resX], cAdd)
        , ([some (sl.accY FTC_CHUNKS), some sl.hmY, some sl.dY], [1, -1, -1, 0, 0])
        , ([some sl.odd, some sl.dY, some sl.mY], cMul)
        , ([some sl.hmY, some sl.mY, some sl.resY], cAdd) ] := by
  simp [sfTermRows, packHalves, KimchiGadgets.sfMuxHalves, KimchiGadgets.selectHalves,
        KimchiGadgets.subHalf, KimchiGadgets.mulHalf, KimchiGadgets.addHalf,
        KimchiGadgets.cSub, KimchiGadgets.cMul, KimchiGadgets.cAdd, cSub, cMul, cAdd, cNil]

/-- §6b's term `k`, as `SfSlots`. -/
def ftcSlots (s : StepShape) (k : Nat) : SfSlots :=
  let g := ftcBaseVar s k
  { baseX := g.1, baseY := g.2
  , accX := ftcAccX s k, accY := ftcAccY s k, n := ftcN s k
  , top := ftcTop s k, negY := ftcNegY s k, hmX := ftcHmX s k, hmY := ftcHmY s k
  , dX := ftcDX s k, dY := ftcDY s k, mX := ftcMX s k, mY := ftcMY s k
  , resX := ftcResX s k, resY := ftcResY s k, odd := ftcOdd s (ftcScalOf k) }

/-- **`Shifted_value.Type2`'s own rows**, once per DISTINCT scalar: `Field.Assert.equal (2·s_div_2 +
s_odd) s` (`plonk_curve_ops.ml:290-291`) and `Boolean.typ`'s check on `s_odd`. ⚑ The `s` these read
is R6's derived cell, not a statement word. -/
def ftcScalRows (s : StepShape) (W : FtcWire) (wired : Bool) : List SRow :=
  packHalves ((List.range N_FTC_SCAL).flatMap (fun c =>
    [ ([some (ftcScalV W c), some (ftcDiv2 s c), some (ftcOdd s c)], cSplit 1)
    , ([some (ftcOdd s c), some (ftcOdd s c), some (ftcOdd s c)], cMul) ]))
  ++ (List.range N_FTC_SCAL).map (fun c => probeRow wired (ftcDiv2 s c) (ftcOdd s c))

/-- **`let n_acc = ref Field.zero`** for `ft_comm`'s own ladders (`plonk_curve_ops.ml:158`), one
`Generic` half per `scale_fast2`. ⚑ §6b emitted `:157`'s `add_fast base base` from the start and NOT
`:158`'s counter seed, so `ftcN k 0` was a free witness and the closing
`Field.Assert.equal !n_acc scalar` (`:208`) — the wire that makes the ladder multiply by R6's derived
`perm` / `ζ^n` — was one equation in two unknowns: the prover picks the 255 bits and solves for
`ftcN k 0`. The same defect R3 carried at `vSN i 0`, in the ladder that computes `ft_comm`. -/
def ftcNZeroRows (s : StepShape) : List SRow :=
  packHalves ((List.range (ftcTerms s)).map (fun k =>
    ([some (ftcN s k 0), none, none], cConst 0)))

/-- **Term `k`'s rows** — `sfTermRows` at §6b's own slots. -/
def ftcTermRows (s : StepShape) (d : FtcData) (wired : Bool) (k : Nat) : List SRow :=
  sfTermRows (ftcSlots s k) (d.terms.getD k default) wired

/-- **The `Ops.add_fast` chain**, in `common.ml`'s order — and its LAST output is the fold's own
round-`FTC_ROUND` base variable, which is the whole point of the rung. -/
def ftcAddRows (s : StepShape) (d : FtcData) (wired : Bool) : List SRow :=
  let n := tCommN s
  let cel : Nat → List Nat := fun a => d.addCells.getD a []
  (List.range (n - 1)).flatMap (fun a =>
    [ caRow (vTcX s (n - 2 - a), vTcY s (n - 2 - a))
            (ftcResX s (a + 1), ftcResY s (a + 1))
            (ftcAddX s a, ftcAddY s a) (cel a)
    , probeRow wired (ftcAddX s a) (ftcAddY s a) ])
  ++ [ caRow (ftcResX s 0, ftcResY s 0) (ftcAddX s (n - 2), ftcAddY s (n - 2))
             (ftcAddX s (n - 1), ftcAddY s (n - 1)) (cel (n - 1))
     , probeRow wired (ftcAddX s (n - 1)) (ftcAddY s (n - 1)) ]
  ++ packHalves [ ([some (ftcResY s n), some (ftcNegQ s), none], [1, 1, 0, 0, 0]) ]
  ++ [ caRow (ftcAddX s (n - 1), ftcAddY s (n - 1)) (ftcResX s n, ftcNegQ s)
             (ipx s (qT s FTC_ROUND), ipy s (qT s FTC_ROUND)) (cel n)
     , probeRow wired (ipx s (qT s FTC_ROUND)) (ipy s (qT s FTC_ROUND)) ]

/-- **§6b's rows.** -/
def ftcRows (s : StepShape) (W : FtcWire) (d : FtcData) (wired : Bool) : List SRow :=
  ftcScalRows s W wired
  ++ ftcNZeroRows s
  ++ (List.range (ftcTerms s)).flatMap (ftcTermRows s d wired)
  ++ ftcAddRows s d wired

/-! ## §8 — R5, the DEFERRED `b(ζ)` and the CLOSING public ties.

`b(ζ) = ∏_k (1 + u_k · ζ^{2^{bRounds−1−k}})` — `Wrap.challenge_polynomial` (`wrap.ml:15-17`), the
product `KimchiVerify.bEvalSq` folds. `ζ` is challenge 0 and `u_k` is challenge `k+1`, so the
deferred rung READS R2's outputs rather than being a private arithmetic island. -/

structure DefData where
  zs : List Nat
  facs : List Nat
  accs : List Nat
  /-- ⚑ **`zetaw` and its own squaring ladder** (`step_verifier.ml:934`), `zws k = (ζω)^{2^k}`,
  `bRounds` entries — `pow_two_pows`' own recurrence at the SECOND evaluation point. -/
  zws : List Nat
  /-- ⚑ **The four `sg_evals` ladders' factors**, ladder-major (`l = 2·slot + point`). -/
  ecFacs : List (List Nat)
  /-- ⚑ …and their running products, `bRounds + 1` per ladder. The last entry of ladder `l` IS
  `E_c` for slot `l/2` at point `l%2` — `f_c(ζ)` / `f_c(ζω)` over `prev_challenges`. -/
  ecAccs : List (List Nat)
  /-- the evaluations at ζ and ζω (the `cipEvals` poly columns). ⚑ Entries 0 and 1 are no longer
  claimed: since §8i they are `ecAccs`' outputs, i.e. `E_c` computed from the carried challenges. -/
  ez : List Nat
  ew : List Nat
  dk : List Nat
  ck : List Nat
  tk : List Nat
  ca : List Nat
  /-- ⚑ `combine`'s `Opt.Maybe` mux cells, one triple per masked prefix slot `j < N_CIP_MASKED`:
  the `then_` value `sⱼ = cⱼ + ξ·accᵢ`, its difference `dⱼ = sⱼ − accᵢ`, and `pⱼ = keepⱼ·dⱼ`. -/
  csk : List Nat
  cdk : List Nat
  cpk : List Nat
  deriving Repr, Inhabited

/-- Claimed evaluation of column `k` at point `pt ∈ {0,1}` — a deterministic fixture standing for a
column of the previous proof's `PointEvaluations`. -/
def evVal (k pt : Nat) : Nat := (11 + 2000003 * (2 * k + pt) + 7 * k * k) % pN

/-- ⚑ The column vector at ζ, with entry 3 — the `ft` column — OVERRIDDEN by R6's computed
`ft_eval0`. That is upstream's own wiring: `combine ~ft:ft_eval0 …` (`step_verifier.ml:1078-1083`)
folds `ft_eval0` into `combined_inner_product` as the fourth prefix column. The four-entry prefix is
`sg_old`×2, the public polynomial, `ft`; R6 reads only entries ≥ 4, so the override is not
circular. -/
def evZOf (ftVal : Nat) (k : Nat) : Nat := if k == 3 then ftVal else evVal k 0

/-- ⚑ **`f_c` — `challenge_polynomial` (`wrap_verifier.ml:16-35`) as a value**, over an arbitrary
challenge vector and an arbitrary point ladder. `pw j` is `pt^{2^j}`, so factor `k` is
`1 + c_k·pt^{2^{bRounds−1−k}}` — `bEvalSq`'s own convention (§18(f) pins the emitted output against
`KimchiVerify.bEvalSq`, which is the read-only transcription). Returns `(factors, products)`; the
products' last entry is `f_c(pt)`. -/
def fcLadder (rounds : Nat) (pw : Nat → Nat) (ch : Nat → Nat) : List Nat × List Nat :=
  (List.range rounds).foldl
    (fun (acc : List Nat × List Nat) k =>
      let f := fAdd 1 (fMul (ch k) (pw (rounds - 1 - k)))
      (acc.1 ++ [f], acc.2 ++ [fMul (acc.2.getLastD 1) f]))
    ([], [1])

/-- ⚑ `xi` and `rr` are the DEFERRED multipliers of §8g — `to_field_checked` of the statement's ξ
word and of the fr-sponge's second squeeze — NOT transcript challenges. The fold is `fed` by the
squeeze, not merely checked against it.

⚑ `omega` is `domain#generator` and `pc` is **`prev_challenges`** — the CARRIED vector
(`per_proof_witness.ml:90-92`), NOT this proof's own returned bulletproof challenges, which are
`liftOf s d (s.uChal k)` and which `st` below folds for `b(ζ)`. Upstream keeps the two apart in one
sentence at `step_verifier.ml:918` ("You use the NEW bulletproof challenges to check b. Not the old
ones."), and this signature keeps them apart by taking the old ones as a separate argument that no
default connects to the transcript. -/
def runDef (s : StepShape) (d : SpongeData) (ftVal : Nat) (xi rr omega : Nat)
    (pc : Nat → Nat) (ms : List Nat) : DefData :=
  let zs := (List.range s.bRounds).foldl
    (fun acc _ => let x := acc.getLastD 0; acc ++ [fMul x x]) [liftOf s d s.zetaChal]
  let st := (List.range s.bRounds).foldl
    (fun (acc : List Nat × List Nat) k =>
      let f := fAdd 1 (fMul (liftOf s d (s.uChal k)) (zs.getD (s.bRounds - 1 - k) 0))
      (acc.1 ++ [f], acc.2 ++ [fMul (acc.2.getLastD 1) f]))
    ([], [1])
  -- ⚑ §8i — `zetaw` (`:934`) and `sg_olds`/`sg_evals` (`:935-948`). FOUR ladders: two slots, two
  -- points. `l = 2·slot + point`.
  let zws := (List.range (s.bRounds - 1)).foldl
    (fun acc _ => let x := acc.getLastD 0; acc ++ [fMul x x])
    [fMul omega (liftOf s d s.zetaChal)]
  let ecs := (List.range N_EC).map (fun l =>
    fcLadder s.bRounds
      (fun j => if ecPoint l == 0 then zs.getD j 0 else zws.getD j 0)
      (fun k => pc (ecSlot l * s.bRounds + k)))
  let ecOut : Nat → Nat := fun l => ((ecs.getD l ([], [])).2).getLastD 0
  -- ⚑ prefix entries 0 and 1 are `sg_evals`' — `E_c` at ζ in `ez`, at ζω in `ew` — where they were
  -- `evVal` FIXTURES until §8i. Entry 2 is `x_hat`, entry 3 is R6's `ft_eval0`; both keep their
  -- fixtures and `evZOf` is unchanged, because `combine`'s prefix is
  -- `sg_evals ++ [x_hat] ++ [ft] ++ …` and only its first two entries are this leg.
  let ez := (List.range s.cipEvals).map (fun k =>
    if k < 2 then ecOut (2 * k) else evZOf ftVal k)
  let ew := (List.range s.cipEvals).map (fun k =>
    if k < 2 then ecOut (2 * k + 1) else evVal k 1)
  let dk := (List.range s.cipEvals).map (fun k => fMul rr (ew.getD k 0))
  let ck := (List.range s.cipEvals).map (fun k => fAdd (ez.getD k 0) (dk.getD k 0))
  -- Horner from the TOP: `accᵢ₊₁ = accᵢ·ξ + c_{n−1−i}`, so slot `j = cipEvals−1−i` is folded at
  -- step `i` and the two MASKED slots (`j = 1` then `j = 0`) are the LAST two steps — which is
  -- `Pcs_batch.combine_split_evaluations`' own order (`pcs_batch.ml:88-94` reverses the flattened
  -- list). ⚑ At `ms = [1,1]` this closes to `Σ_k ξ^k · c_k`, which IS
  -- `KimchiVerify.combinedInnerProduct`; at any other legal mask it closes to the SAME fold over
  -- the KEPT sub-list, because `common.ml:271`'s `else_` branch is bare `acc` and consumes no ξ.
  let hz := (List.range s.cipEvals).foldl
    (fun (acc : List Nat × List Nat) i =>
      let j := s.cipEvals - 1 - i
      let a := acc.2.getLastD 0
      let t := fMul a xi
      let sv := fAdd t (ck.getD j 0)
      (acc.1 ++ [t], acc.2 ++ [if j < N_CIP_MASKED && ms.getD j 0 == 0 then a else sv]))
    ([], [0])
  -- ⚑ the mux cells. Slot `j`'s fold step is `i = cipEvals − 1 − j`, so `accᵢ` is `hz.2` at `i`.
  let mux := (List.range N_CIP_MASKED).map (fun j =>
    let i := s.cipEvals - 1 - j
    let a := hz.2.getD i 0
    let sv := fAdd (hz.1.getD i 0) (ck.getD j 0)
    let dv := fSub sv a
    (sv, dv, fMul (ms.getD j 0) dv))
  { zs := zs, facs := st.1, accs := st.2
  , zws := zws, ecFacs := ecs.map (·.1), ecAccs := ecs.map (·.2)
  , ez := ez, ew := ew, dk := dk, ck := ck, tk := hz.1, ca := hz.2
  , csk := mux.map (·.1), cdk := mux.map (·.2.1), cpk := mux.map (·.2.2) }

/-- **R5a's rows.** ⚑ Its challenge operand is `vLift (uChal k)` — this proof's OWN bulletproof
challenges, the vector `step_verifier.ml:918` calls "the NEW" ones. §8i's ladders read `vPrevChal`
and NOTHING from this list, and §18(f) pins that read-set disjointness in both directions. -/
def deferredRows (s : StepShape) (wired : Bool) : List SRow :=
  [ genericRow (some (vAcc s 0)) none none none none none (cConst 1 ++ cNil)
  , genericRow (some (vZ s 0)) (some (vLift s s.zetaChal)) none none none none (cEq ++ cNil) ]
  ++ (List.range s.bRounds).map (fun k =>
      genericRow (some (vZ s k)) (some (vZ s k)) (some (vZ s (k+1))) none none none (cMul ++ cNil))
  ++ (List.range s.bRounds).map (fun k =>
      genericRow (some (vLift s (s.uChal k))) (some (vZ s (s.bRounds - 1 - k))) (some (vFac s k))
                 (some (vAcc s k)) (some (vFac s k)) (some (vAcc s (k+1))) (cMulPlus1 ++ cMul))
  ++ [ probeRow wired (vAcc s s.bRounds) (vZ s s.bRounds) ]

/-- **§8i's rows — `sg_olds` / `sg_evals`, `E_c = f_c(ζ)` over `prev_challenges`.**

`step_verifier.ml:934-948`. One `Generic` half pins `domain#generator`; one multiplies it by
`plonk.zeta` to give the SINGLE `zetaw` cell `:948` and `:1124` share; then ζω's squaring ladder
(`bRounds − 1` halves, `pow_two_pows`' own count); then FOUR product ladders, one `Generic` row per
factor in exactly `deferredRows`' fused shape (`w₂ = 1 + w₀w₁` beside `w₅ = w₃w₄`), whose outputs
ARE `vEz 0/1` and `vEw 0/1`.

⚑ THE CHALLENGE OPERAND IS `vPrevChal`. That is the whole point of the rung: before it, these four
prefix entries were free `evVal` witnesses and `prev_challenges` reached nothing in R5 at all. ⚠ It
is leg ONE. `E_c` is a function of `prev_challenges` and NOT of `sg_old`, so nothing here relates the
commitment to the value it must open to; that relation is the opening, `verified` (#11). -/
def sgEvalRows (s : StepShape) (omega : Nat) (wired : Bool) : List SRow :=
  [ genericRow (some (vOmegaC s)) none none
               (some (vLift s s.zetaChal)) (some (vOmegaC s)) (some (vZW s 0))
               (cConst (omega : Int) ++ cMul) ]
  ++ packHalves ((List.range (s.bRounds - 1)).map (fun k =>
       ([some (vZW s k), some (vZW s k), some (vZW s (k+1))], cMul)))
  ++ (List.range N_EC).flatMap (fun l =>
      (List.range s.bRounds).map (fun k =>
        genericRow (some (vPrevChal s (ecSlot l * s.bRounds + k)))
                   (some (vEcPow s l (s.bRounds - 1 - k))) (some (vEcFac s l k))
                   (some (vEcAcc s l k)) (some (vEcFac s l k)) (some (vEcAcc s l (k+1)))
                   (cMulPlus1 ++ cMul)))
  ++ (List.range N_EC).map (fun l => probeRow wired (vEcOut s l) (vEcFac s l 0))

/-- **R5a', `combined_inner_product`** — `Common.combined_evaluation` (`common.ml:258-…`), the
`2 × cipEvals` `mul_and_add`s. `cip = Σ_k ξ^k · (evₖ(ζ) + r · evₖ(ζω))`, assembled as a Horner fold
from the top over `Generic` rows, two per evaluation column:

    A(k)  half1  w₀=r      w₁=evₖ(ζω)  w₂=dₖ      dₖ = r · evₖ(ζω)
          half2  w₃=evₖ(ζ) w₄=dₖ       w₅=cₖ      cₖ = evₖ(ζ) + dₖ
    B(i)  half1  w₀=accᵢ   w₁=ξ        w₂=tᵢ      tᵢ = accᵢ · ξ
          half2  w₃=tᵢ     w₄=c_{n−1−i} w₅=accᵢ₊₁ accᵢ₊₁ = tᵢ + c_{n−1−i}

⚑ ξ and `r` are `vDLift 0` / `vDLift 1` — §8g's DEFERRED challenges, `to_field_checked` of the
statement's ξ word and of the fr-sponge's second squeeze (`step_verifier.ml:1012-1013`). Every
`Generic` half of this fold therefore hangs off the fr-sponge through σ, which is the retirement of
simplification #10.

⚑⚑ **AND SINCE 2026-08-02 THE B-STEP IS MUXED AT THE TWO `Maybe` SLOTS** (`common.ml:270-271`),
which is `combine`'s last ignoring consumer of `branch_data.proofs_verified_mask`. For `j ≥ 2` the
step is `Some` and stays the two halves above. For `j < N_CIP_MASKED` it is `Field.if_ keepⱼ`, which
is §8e's own three-half shape on top of them:

    C(j)  half3  w₀=sⱼ      w₁=accᵢ    w₂=dⱼ       dⱼ = sⱼ − accᵢ
          half4  w₃=maskⱼ   w₄=dⱼ      w₅=pⱼ       pⱼ = keepⱼ · dⱼ
          half5  w₀=accᵢ    w₁=pⱼ      w₂=accᵢ₊₁   accᵢ₊₁ = accᵢ + pⱼ

with `B(i)`'s second half retargeted from `accᵢ₊₁` to the `then_` cell `sⱼ`. `w₃ = vMask j` is
§8h's DERIVED bit — the same variable `branchRows` booleanity-checks and `Checked.pack` ties to the
`branch_data` statement word — not a fresh witness and not a schedule constant.

⚑ The halves are `packHalves`-packed, so the 45 unmasked steps keep EXACTLY the row pairing they had
(two halves each, in order, from half 0) and the change is confined to the ten halves at the tail:
`2·(cipEvals − 2) + 5·2 = 100` halves, 50 rows where there were 47. **+3 `Generic` rows**, plus **+1
`Zero`** for the mux's own σ probe — four rows, and no other gate family.

⚠ ⚑ **THE ROWS DO NOT DEPEND ON THE MASK'S VALUE, and that is the point rather than an omission.**
`keepⱼ` is `vMask j`, a circuit VARIABLE that `branchRows` booleanity-checks and `Checked.pack` ties
to the `branch_data` STATEMENT word — so all three legal masks emit the SAME gate list and differ
only in the witness, exactly as upstream's `branch_data` does. The mask VALUE enters at `runDef`,
which is where §12l varies it. A `cipRows` that took the mask as a schedule constant would be the
defect §8h retired one rung ago, in a new place. -/
def cipRows (s : StepShape) (wired : Bool) : List SRow :=
  [ genericRow (some (vCa s 0)) none none none none none (cConst 0 ++ cNil) ]
  ++ (List.range s.cipEvals).map (fun k =>
      genericRow (some (vDLift s 1)) (some (vEw s k)) (some (vDk s k))
                 (some (vEz s k)) (some (vDk s k)) (some (vCk s k)) (cMul ++ cAdd))
  ++ packHalves ((List.range s.cipEvals).flatMap (fun i =>
      let j := s.cipEvals - 1 - i
      let mulHalf : List (Option PVar) × List Int :=
        ([some (vCa s i), some (vDLift s 0), some (vTk s i)], cMul)
      if j < N_CIP_MASKED then
        [ mulHalf
        , ([some (vTk s i), some (vCk s j), some (vCs s j)], cAdd)
        , ([some (vCs s j), some (vCa s i), some (vCd s j)], cSub)
        , ([some (vMask s j), some (vCd s j), some (vCp s j)], cMul)
        , ([some (vCa s i), some (vCp s j), some (vCa s (i + 1))], cAdd) ]
      else
        [ mulHalf
        , ([some (vTk s i), some (vCk s j), some (vCa s (i + 1))], cAdd) ]))
  ++ [ probeRow wired (vCa s s.cipEvals) (vCk s 0)
     -- ⚑ …and the mux's own σ probe, so a tamper isolates `keepⱼ·dⱼ` rather than only the
     -- accumulator it feeds. Without it `vCp 0`'s whole class is its two defining halves.
     , probeRow wired (vCp s 0) (vCp s 1) ]
  -- ⚑ `absorb sponge Scalar advice.combined_inner_product` (`:79-81,256-259`) absorbs the FIELD half
  -- and then a `Bits [b]` — `Other_field.Packed`'s `Boolean.var`, which since 2026-08-03 IS §19
  -- ladder 0's `s_odd` (`vCipBit = bpOdd 0`). `Boolean.typ`'s own `b² = b` is emitted HERE rather
  -- than in `bpRows`, so every rung that absorbs the bit carries its booleanity — including the ones
  -- below `r9_opening`, where the split row that DERIVES it is not yet emitted.
  ++ [ genericRow (some (vCipBit s)) (some (vCipBit s)) (some (vCipBit s)) none none none
                  (cMul ++ cNil)
     , probeRow wired (vCipBit s) (vCipShift s) ]

/-! ## §8b — the ARITHMETIC COMPILER: a straight-line program over `Generic` rows.

`ft_eval0`, `Plonk_checks.checked` and the linearization constant term are pure scalar arithmetic
over the previous proof's evaluations, and Snarky emits them as `Generic` rows
(`plonk_constraint_system.ml`'s `Basic.R1CS`/`Square`/`Boolean` all land on the double generic gate).
Rather than hand-writing several hundred rows, this compiles a STRAIGHT-LINE PROGRAM: slot `i` owns
one circuit variable, each operation is one HALF of a double-`Generic` row, and two consecutive
operations share a row.

⚑ THE PROGRAM IS CHECKED AGAINST THE VALUE LAYER, NOT TRUSTED. `KimchiVerify`'s constraint bodies —
read-only transcriptions of `proof-systems` — are evaluated at the SAME inputs in §12, **list by
list**, and the compiled program's slot values must agree elementwise. A transcription slip in any
one of the 67 constraint bodies goes red there, not silently into a proof. -/

/-- One straight-line arithmetic operation. Slot `i` is the `i`-th entry of the program. -/
inductive AOp where
  /-- ALIAS an existing circuit variable — no row, no new variable. This is how the program reaches
  the sponge's challenges and the previous proof's evaluation columns. -/
  | inp (v : PVar)
  /-- A FREE witness cell: no defining row. Only what the program asserts about it constrains it —
  the witnessed-inverse device (`KimchiVerify` §9b's `denomInv`). -/
  | wit (val : Nat)
  /-- A field constant, pinned by the row `w₀ = k`. -/
  | lit (val : Nat)
  | add (i j : Nat)
  | sub (i j : Nat)
  | mul (i j : Nat)
  /-- ASSERT slot `i` = slot `j`; the produced slot is inert. -/
  | aeq (i j : Nat)
  deriving Repr, Inhabited, DecidableEq

/-- The program builder. -/
abbrev AM := StateM (Array AOp)

def em (o : AOp) : AM Nat := do
  let st ← get
  set (st.push o)
  pure st.size

def eLit (k : Nat) : AM Nat := em (.lit k)
def eWit (k : Nat) : AM Nat := em (.wit k)
def eInp (v : PVar) : AM Nat := em (.inp v)
def eAdd (a b : Nat) : AM Nat := em (.add a b)
def eSub (a b : Nat) : AM Nat := em (.sub a b)
def eMul (a b : Nat) : AM Nat := em (.mul a b)
def eEq (a b : Nat) : AM Nat := em (.aeq a b)

/-- Evaluate the program. `lk` resolves `.inp` variables out of the surrounding circuit. -/
def aEval (lk : PVar → Int) (prog : Array AOp) : Array Nat :=
  prog.foldl (fun (vs : Array Nat) op =>
    vs.push (match op with
      | .inp v => (lk v).toNat % pN
      | .wit x => x % pN
      | .lit x => x % pN
      | .add i j => fAdd (vs.getD i 0) (vs.getD j 0)
      | .sub i j => fSub (vs.getD i 0) (vs.getD j 0)
      | .mul i j => fMul (vs.getD i 0) (vs.getD j 0)
      | .aeq i _ => vs.getD i 0)) #[]

/-- Slot `i`'s circuit variable. `.inp` aliases; everything else owns `xv (base + i)`. -/
def aVarAt (base : Nat) (prog : Array AOp) (i : Nat) : PVar :=
  match prog.getD i default with
  | .inp v => v
  | _ => xv (base + i)

/-- The slots that need a `Generic` half (`.inp` and `.wit` need none). -/
def aHalfSlots (prog : Array AOp) : List Nat :=
  (List.range prog.size).filter (fun i =>
    match prog.getD i default with | .inp _ => false | .wit _ => false | _ => true)

/-- Slot `i`'s half: its three permutation columns and its five coefficients. -/
def aHalf (base : Nat) (prog : Array AOp) (i : Nat) : List (Option PVar) × List Int :=
  let V := aVarAt base prog
  match prog.getD i default with
  | .lit k => ([some (V i), none, none], cConst (k : Int))
  | .add a b => ([some (V a), some (V b), some (V i)], cAdd)
  | .sub a b => ([some (V a), some (V b), some (V i)], cSub)
  | .mul a b => ([some (V a), some (V b), some (V i)], cMul)
  | .aeq a b => ([some (V a), some (V b), none], cEq)
  | _ => ([none, none, none], cNil)

/-- The program's rows: two halves per double-`Generic` row, a `cNil` tail half when odd. -/
def aRows (base : Nat) (prog : Array AOp) : List SRow :=
  let sl := aHalfSlots prog
  (List.range ((sl.length + 1) / 2)).map (fun r =>
    let h1 := aHalf base prog (sl.getD (2 * r) 0)
    let h2 := if 2 * r + 1 < sl.length then aHalf base prog (sl.getD (2 * r + 1) 0)
              else (([none, none, none] : List (Option PVar)), cNil)
    ({ kind := .generic, perm := h1.1 ++ h2.1 ++ [none], coeffs := h1.2 ++ h2.2 } : SRow))

/-- The program's contribution to the variable environment. -/
def aEnvOf (base : Nat) (prog : Array AOp) (vals : Array Nat) : VarEnv :=
  (List.range prog.size).filterMap (fun i =>
    match prog.getD i default with
    | .inp _ => none
    | _ => some (xv (base + i), (vals.getD i 0 : Int)))

/-! ## §8c — the SIX GATE CONSTRAINT BODIES, compiled.

Each mirrors a `KimchiVerify` body one-for-one, and §12 pins the compiled values against that body's
own output list. These are the factors the six selectors multiply in the linearization constant term
(`gateLinConst`, `argument.rs:201-213`). -/

/-- `x⁷` — kimchi's Poseidon S-box (`PlonkSpongeConstantsKimchi::PERM_SBOX = 7`). 4 muls. -/
def pSbox (x : Nat) : AM Nat := do
  let x2 ← eMul x x
  let x4 ← eMul x2 x2
  let x6 ← eMul x4 x2
  eMul x6 x

/-- `poseidonLaneConstraint`: `target − (rc + Σ_c mds[j][c]·sbox(source_c))`, sboxes precomputed. -/
def pLane (mdsRow : List Nat) (rc : Nat) (sb : List Nat) (target : Nat) : AM Nat := do
  let t0 ← eMul (mdsRow.getD 0 0) (sb.getD 0 0)
  let t1 ← eMul (mdsRow.getD 1 0) (sb.getD 1 0)
  let t2 ← eMul (mdsRow.getD 2 0) (sb.getD 2 0)
  let s01 ← eAdd t0 t1
  let s ← eAdd s01 t2
  let r ← eAdd rc s
  eSub target r

/-- The 15 `Poseidon` constraints (`poseidonConstraints`), in emission order. -/
def pPoseidon (mdsS : List (List Nat)) (c w wn : List Nat) : AM (List Nat) := do
  let ww := fun i => w.getD i 0
  let cc := fun i => c.getD i 0
  let wnn := fun i => wn.getD i 0
  let sb ← (List.range 15).foldlM (fun acc i => do let s ← pSbox (ww i); pure (acc ++ [s])) []
  let g := fun (ix : List Nat) => ix.map (fun i => sb.getD i 0)
  let s0 := g [0, 1, 2]; let s1 := g [6, 7, 8]; let s2 := g [9, 10, 11]
  let s3 := g [12, 13, 14]; let s4 := g [3, 4, 5]
  let m := fun j => mdsS.getD j []
  let spec : List (Nat × Nat × List Nat × Nat) :=
    [ (0, 0, s0, ww 6), (1, 1, s0, ww 7), (2, 2, s0, ww 8)
    , (0, 3, s1, ww 9), (1, 4, s1, ww 10), (2, 5, s1, ww 11)
    , (0, 6, s2, ww 12), (1, 7, s2, ww 13), (2, 8, s2, ww 14)
    , (0, 9, s3, ww 3), (1, 10, s3, ww 4), (2, 11, s3, ww 5)
    , (0, 12, s4, wnn 0), (1, 13, s4, wnn 1), (2, 14, s4, wnn 2) ]
  spec.foldlM (fun acc q => do let k ← pLane (m q.1) (cc q.2.1) q.2.2.1 q.2.2.2; pure (acc ++ [k])) []

/-- The 7 `CompleteAdd` constraints (`completeAddConstraints`). -/
def pCompleteAdd (one : Nat) (w : List Nat) : AM (List Nat) := do
  let ww := fun i => w.getD i 0
  let x1 := ww 0; let y1 := ww 1; let x2 := ww 2; let y2 := ww 3
  let x3 := ww 4; let y3 := ww 5; let inf := ww 6; let sameX := ww 7
  let s := ww 8; let infZ := ww 9; let x21Inv := ww 10
  let x21 ← eSub x2 x1
  let y21 ← eSub y2 y1
  let x1sq ← eMul x1 x1
  let nsx ← eSub one sameX
  let a ← eMul x21Inv x21
  let k0 ← eSub a nsx
  let k1 ← eMul sameX x21
  let ss ← eAdd s s
  let ssy ← eMul ss y1
  let q2 ← eAdd x1sq x1sq
  let t1a ← eSub ssy q2
  let t1 ← eSub t1a x1sq
  let p1 ← eMul sameX t1
  let x21s ← eMul x21 s
  let t2 ← eSub x21s y21
  let p2 ← eMul nsx t2
  let k2 ← eAdd p1 p2
  let sx ← eAdd x1 x2
  let sx3 ← eAdd sx x3
  let s2v ← eMul s s
  let k3 ← eSub sx3 s2v
  let d ← eSub x1 x3
  let sd ← eMul s d
  let e1 ← eSub sd y1
  let k4 ← eSub e1 y3
  let f ← eSub sameX inf
  let k5 ← eMul y21 f
  let g ← eMul y21 infZ
  let k6 ← eSub g inf
  pure [k0, k1, k2, k3, k4, k5, k6]

/-- The 21 `VarbaseMul` constraints (`varBaseMulConstraints`). -/
def pVarBaseMul (one : Nat) (w wn : List Nat) : AM (List Nat) := do
  let ww := fun i => w.getD i 0
  let wnn := fun i => wn.getD i 0
  let xT := ww 0; let yT := ww 1
  let accX := fun i => ([ww 2, ww 7, ww 9, ww 11, ww 13, wnn 0] : List Nat).getD i 0
  let accY := fun i => ([ww 3, ww 8, ww 10, ww 12, ww 14, wnn 1] : List Nat).getD i 0
  let bit := fun i => ([wnn 2, wnn 3, wnn 4, wnn 5, wnn 6] : List Nat).getD i 0
  let sl := fun i => ([wnn 7, wnn 8, wnn 9, wnn 10, wnn 11] : List Nat).getD i 0
  let nPrev := ww 4; let nNext := ww 5
  let acc ← (List.range 5).foldlM (fun a i => do let aa ← eAdd a a; eAdd (bit i) aa) nPrev
  let dec ← eSub nNext acc
  let rest ← (List.range 5).foldlM (fun out i => do
      let b := bit i; let s := sl i
      let ix := accX i; let iy := accY i
      let ox := accX (i + 1); let oy := accY (i + 1)
      let b2 ← eAdd b b
      let bSign ← eSub b2 one
      let ssq ← eMul s s
      let rxa ← eSub ssq ix
      let rx ← eSub rxa xT
      let t ← eSub ix rx
      let iy2 ← eAdd iy iy
      let ts ← eMul t s
      let u ← eSub iy2 ts
      let bb ← eMul b b
      let k0 ← eSub bb b
      let ixT ← eSub ix xT
      let l1 ← eMul ixT s
      let by' ← eMul bSign yT
      let r1 ← eSub iy by'
      let k1 ← eSub l1 r1
      let uu ← eMul u u
      let tt ← eMul t t
      let oxT ← eSub ox xT
      let q ← eAdd oxT ssq
      let ttq ← eMul tt q
      let k2 ← eSub uu ttq
      let oyiy ← eAdd oy iy
      let l3 ← eMul oyiy t
      let ixox ← eSub ix ox
      let r3 ← eMul ixox u
      let k3 ← eSub l3 r3
      pure (out ++ [k0, k1, k2, k3])) []
  pure (dec :: rest)

/-- The 11 DEPLOYED `EndosclMul` constraints (`endoMulConstraints … |>.take 11`, `proof-systems`
0.3.0's `CONSTRAINTS = 11` — the 12th distinct-point witness is NOT in the deployed constant term,
`gateLinConst`'s own `.take 11`). -/
def pEndoMul (one endo : Nat) (w wn : List Nat) : AM (List Nat) := do
  let ww := fun i => w.getD i 0
  let wnn := fun i => wn.getD i 0
  let xt := ww 0; let yt := ww 1
  let xp := ww 4; let yp := ww 5; let n := ww 6
  let xr := ww 7; let yr := ww 8; let s1 := ww 9; let s3 := ww 10
  let b1 := ww 11; let b2 := ww 12; let b3 := ww 13; let b4 := ww 14
  let xs := wnn 4; let ys := wnn 5; let nNext := wnn 6
  let em1 ← eSub endo one
  let t1 ← eMul b1 em1
  let u1 ← eAdd one t1
  let xq1 ← eMul u1 xt
  let t3 ← eMul b3 em1
  let u3 ← eAdd one t3
  let xq2 ← eMul u3 xt
  let b22 ← eAdd b2 b2
  let v2 ← eSub b22 one
  let yq1 ← eMul v2 yt
  let b42 ← eAdd b4 b4
  let v4 ← eSub b42 one
  let yq2 ← eMul v4 yt
  let s1sq ← eMul s1 s1
  let s3sq ← eMul s3 s3
  let n2 ← eAdd n n
  let d1 ← eAdd n2 b1
  let d1a ← eAdd d1 d1
  let d2 ← eAdd d1a b2
  let d2a ← eAdd d2 d2
  let d3 ← eAdd d2a b3
  let d3a ← eAdd d3 d3
  let d4 ← eAdd d3a b4
  let nC ← eSub d4 nNext
  let xpxr ← eSub xp xr
  let xrxs ← eSub xr xs
  let ysyr ← eAdd ys yr
  let yryp ← eAdd yr yp
  let k0 ← do let t ← eMul b1 b1; eSub t b1
  let k1 ← do let t ← eMul b2 b2; eSub t b2
  let k2 ← do let t ← eMul b3 b3; eSub t b3
  let k3 ← do let t ← eMul b4 b4; eSub t b4
  let k4 ← do let a ← eSub xq1 xp; let l ← eMul a s1; let r ← eSub yq1 yp; eSub l r
  let k5 ← do
    let xp2 ← eAdd xp xp
    let a ← eSub xp2 s1sq
    let a2 ← eAdd a xq1
    let m1 ← eMul xpxr s1
    let m2 ← eAdd m1 yryp
    let l ← eMul a2 m2
    let yp2 ← eAdd yp yp
    let r ← eMul yp2 xpxr
    eSub l r
  let k6 ← do
    let l ← eMul yryp yryp
    let p ← eMul xpxr xpxr
    let a ← eSub s1sq xq1
    let a2 ← eAdd a xr
    let r ← eMul p a2
    eSub l r
  let k7 ← do let a ← eSub xq2 xr; let l ← eMul a s3; let r ← eSub yq2 yr; eSub l r
  let k8 ← do
    let xr2 ← eAdd xr xr
    let a ← eSub xr2 s3sq
    let a2 ← eAdd a xq2
    let m1 ← eMul xrxs s3
    let m2 ← eAdd m1 ysyr
    let l ← eMul a2 m2
    let yr2 ← eAdd yr yr
    let r ← eMul yr2 xrxs
    eSub l r
  let k9 ← do
    let l ← eMul ysyr ysyr
    let p ← eMul xrxs xrxs
    let a ← eSub s3sq xq2
    let a2 ← eAdd a xs
    let r ← eMul p a2
    eSub l r
  pure [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, nC]

/-- The 11 `EndomulScalar` constraints (`endomulScalarConstraints`). `cA/cB/cC` are the witnessed
quotients `11/6, −5/2, 2/3`, and `negOne/three/six/eleven` are the small literals of `c`, `d` and
`crumb`. -/
def pEmScalar (cA cB cC negOne three six eleven : Nat) (w : List Nat) : AM (List Nat) := do
  let ww := fun i => w.getD i 0
  let n0 := ww 0; let n8 := ww 1; let a0 := ww 2; let b0 := ww 3
  let a8 := ww 4; let b8 := ww 5
  let x := fun i => ww (6 + i)
  let cf : Nat → AM Nat := fun t => do
    let m1 ← eMul cC t
    let s1 ← eAdd m1 cB
    let m2 ← eMul s1 t
    let s2 ← eAdd m2 cA
    eMul s2 t
  let cfs ← (List.range 8).foldlM (fun acc i => do let v ← cf (x i); pure (acc ++ [v])) []
  let dfs ← (List.range 8).foldlM (fun acc i => do
      let t := x i
      let m1 ← eMul negOne t
      let s1 ← eAdd m1 three
      let m2 ← eMul s1 t
      let s2 ← eAdd m2 negOne
      let v ← eAdd (cfs.getD i 0) s2
      pure (acc ++ [v])) []
  let n8e ← (List.range 8).foldlM (fun acc i => do
      let a2 ← eAdd acc acc
      let a4 ← eAdd a2 a2
      eAdd a4 (x i)) n0
  let a8e ← (List.range 8).foldlM (fun acc i => do
      let a2 ← eAdd acc acc
      eAdd a2 (cfs.getD i 0)) a0
  let b8e ← (List.range 8).foldlM (fun acc i => do
      let a2 ← eAdd acc acc
      eAdd a2 (dfs.getD i 0)) b0
  let c0 ← eSub n8e n8
  let c1 ← eSub a8e a8
  let c2 ← eSub b8e b8
  let cr ← (List.range 8).foldlM (fun acc i => do
      let t := x i
      let a ← eSub t six
      let b ← eMul a t
      let c ← eAdd b eleven
      let d ← eMul c t
      let e ← eSub d six
      let v ← eMul e t
      pure (acc ++ [v])) []
  pure ([c0, c1, c2] ++ cr)

/-- `genericGateConstraint` — the double generic gate's own linearization factor. -/
def pGenericGate (genSel alpha : Nat) (c w : List Nat) : AM Nat := do
  let cc := fun i => c.getD i 0
  let ww := fun i => w.getD i 0
  let t0 ← eMul (cc 0) (ww 0)
  let t1 ← eMul (cc 1) (ww 1)
  let t2 ← eMul (cc 2) (ww 2)
  let w01 ← eMul (ww 0) (ww 1)
  let t3 ← eMul (cc 3) w01
  let s0 ← eAdd t0 t1
  let s1 ← eAdd s0 t2
  let s2 ← eAdd s1 t3
  let k1 ← eAdd s2 (cc 4)
  let u0 ← eMul (cc 5) (ww 3)
  let u1 ← eMul (cc 6) (ww 4)
  let u2 ← eMul (cc 7) (ww 5)
  let w34 ← eMul (ww 3) (ww 4)
  let u3 ← eMul (cc 8) w34
  let r0 ← eAdd u0 u1
  let r1 ← eAdd r0 u2
  let r2 ← eAdd r1 u3
  let k2 ← eAdd r2 (cc 9)
  let ak2 ← eMul alpha k2
  let sum ← eAdd k1 ak2
  eMul genSel sum

/-- `alphaCombine α cs = Σᵢ αⁱ·csᵢ`, Horner-free (the powers are shared with `ft_eval0`'s `α^21..23`
so the whole rung pays for one power chain). -/
def pAlphaCombine (apow : List Nat) (cs : List Nat) : AM Nat := do
  match cs with
  | [] => eLit 0
  | c0 :: rest =>
      (List.range rest.length).foldlM (fun acc i => do
        let t ← eMul (apow.getD (i + 1) 0) (rest.getD i 0)
        eAdd acc t) c0

/-! ## §8d — R6, `ft_eval0` + `Plonk_checks.checked`, with `scalars_env`.

`step_verifier.ml:1019-1071,1131-1136`. The rung compiles, in order:

  * **`scalars_env`** (`plonk_checks.ml:254-408`) — `ω^{n−1}` as a WITNESSED inverse (`ω·ω⁻¹ = 1`
    checked in-circuit, so `ω^{n−1}` is derived rather than asserted), `ω^{n−2}`, `ω^{n−3}`,
    `zk_polynomial`, `ζ^n − 1` by `log2n` squarings, and the α power chain `α⁰..α²³`.
  * **the linearization constant term** — `gateLinConst`: all six gate bodies of §8c behind their
    selectors, α-combined. This is `Sc.constant_term env` (`plonk_checks.ml:459`).
  * **`ft_eval0`** (`plonk_checks.ml:420-460`) — the permutation numerator fold over the 6 σ evals,
    minus `p(ζ)`, minus the denominator fold over the 7 coset shifts, plus `numerator·denomInv` with
    `denom·denomInv = 1` CHECKED (the same witnessed-inverse device, no `Field` instance needed),
    minus the constant term.
  * **`Plonk_checks.checked`** (`plonk_checks.ml:516-548`) — `derive_plonk`'s `perm` scalar
    `−(fold over e.s of (γ + β·s + w) from z(ζω)·β·α²¹·zkp)`, asserted equal to the deferred value.

⚑ IT READS THE ASSEMBLY, not a private island: `ζ/α/β/γ` are R2's challenge variables and the 43
evaluation columns are R5's `vEz`/`vEw` — so the whole rung hangs off σ classes that R1–R5 created.
And its OUTPUT is tied to `vEz 3`, the `ft` entry of the `combined_inner_product` column vector,
which is exactly `combine ~ft:ft_eval0` at `step_verifier.ml:1078-1083`. -/

/-- The four-entry prefix of the C8 column vector (`sg_old`×2, the public polynomial, `ft`);
`MinaWrapFtEval0`'s own slicing, and `IDX_Z`/`IDX_W`/`IDX_S`/`IDX_COEFF`/`IDX_SEL` index AFTER it. -/
def EV_PREFIX : Nat := 4
/-- Column `k` of the 43-column evaluation vector at ζ. -/
def vColZ (s : StepShape) (k : Nat) : PVar := vEz s (EV_PREFIX + k)
/-- …and at ζω. -/
def vColW (s : StepShape) (k : Nat) : PVar := vEw s (EV_PREFIX + k)

-- (Which challenge plays ζ / α / β / γ is §2b's — `StepShape.betaChal` and friends, positions the
-- transcript SCHEDULE fixes rather than an arbitrary numbering.)

/-- The wire the ft program reads: each field is a SOURCE OP, so the same program compiles against
the assembled circuit's variables (`.inp`) and against a real block's field values (`.lit`). -/
structure FtWire where
  ez : Nat → AOp
  ew : Nat → AOp
  zeta : AOp
  alpha : AOp
  beta : AOp
  gamma : AOp
  pZeta : AOp

/-- The config the ft program bakes in as constants: the domain, the seven coset shifts, the MDS,
the endomorphism coefficient and the three `EndomulScalar` quotients — plus the two witnessed
values the circuit CHECKS rather than trusts. -/
structure FtCfg where
  log2n : Nat
  omega : Nat
  omegaInv : Nat
  shifts : List Nat
  mds9 : List Nat
  endo : Nat
  cA : Nat
  cB : Nat
  cC : Nat
  /-- ⚑ The ONE witnessed value. There were two until 2026-08-03: a `permClaimed` sat here and
  `ftBuild` closed with `eEq perm permClaimed` — an assert that **cannot fail**, because
  `permClaimed` occupied exactly ONE permutation cell in the whole emitted schedule (that assert's
  own). A row whose only novel operand is a variable no other row reads constrains the prover not at
  all. It is DELETED: the check upstream wants is R8's, which reads the COMPUTED `perm` slot and
  compares it against the statement's `vPermShift`. -/
  denomInv : Nat
  deriving Repr, Inhabited

/-- The slots the rung's rows and pins refer to. -/
structure FtSlots where
  ftEval0 : Nat
  linConst : Nat
  zkp : Nat
  perm : Nat
  zetaN : Nat
  omInv3 : Nat
  deriving Repr, Inhabited

/-- **The ft program.** Returns the named output slots. -/
def ftBuild (W : FtWire) (C : FtCfg) : AM FtSlots := do
  -- ── small literals and the config constants ───────────────────────────────────────────────
  let one ← eLit 1
  let negOne ← eLit (pN - 1)
  let three ← eLit 3
  let six ← eLit 6
  let eleven ← eLit 11
  let omega ← eLit C.omega
  let omInv ← eLit C.omegaInv
  let endo ← eLit C.endo
  let cA ← eLit C.cA
  let cB ← eLit C.cB
  let cC ← eLit C.cC
  let shiftS ← (List.range 7).foldlM
    (fun acc i => do let v ← eLit (C.shifts.getD i 0); pure (acc ++ [v])) []
  let mdsS ← (List.range 3).foldlM (fun acc j => do
      let row ← (List.range 3).foldlM
        (fun r i => do let v ← eLit (C.mds9.getD (3 * j + i) 0); pure (r ++ [v])) []
      pure (acc ++ [row])) []
  -- ── scalars_env ───────────────────────────────────────────────────────────────────────────
  -- ⚑ ω^{n−1} = ω⁻¹ is DERIVED: `ω·ω⁻¹ = 1` is a row, so a wrong inverse cannot be witnessed.
  let chk ← eMul omega omInv
  let _ ← eEq chk one
  let omInv2 ← eMul omInv omInv
  let omInv3 ← eMul omInv2 omInv
  let zeta ← em W.zeta
  let alpha ← em W.alpha
  let beta ← em W.beta
  let gamma ← em W.gamma
  let zm3 ← eSub zeta omInv3
  let zm2 ← eSub zeta omInv2
  let zm1 ← eSub zeta omInv
  let zkpA ← eMul zm3 zm2
  let zkp ← eMul zkpA zm1
  let zetaN ← (List.range C.log2n).foldlM (fun acc _ => eMul acc acc) zeta
  let zeta1m1 ← eSub zetaN one
  let apow ← (List.range 23).foldlM (fun acc _ => do
      let p ← eMul (acc.getLastD one) alpha; pure (acc ++ [p])) [one]
  let a0 := apow.getD 21 0
  let a1 := apow.getD 22 0
  let a2 := apow.getD 23 0
  -- ── the wire columns ──────────────────────────────────────────────────────────────────────
  let ez ← (List.range 43).foldlM (fun acc k => do let v ← em (W.ez k); pure (acc ++ [v])) []
  let ew ← (List.range 43).foldlM (fun acc k => do let v ← em (W.ew k); pure (acc ++ [v])) []
  let coeff := (List.range 15).map (fun i => ez.getD (IDX_COEFF + i) 0)
  let wv := (List.range 15).map (fun i => ez.getD (IDX_W + i) 0)
  let wn := (List.range 15).map (fun i => ew.getD (IDX_W + i) 0)
  let sv := (List.range 6).map (fun i => ez.getD (IDX_S + i) 0)
  let zZeta := ez.getD IDX_Z 0
  let zZetaW := ew.getD IDX_Z 0
  let genSel := ez.getD (IDX_SEL + 0) 0
  let posSel := ez.getD (IDX_SEL + 1) 0
  let caddSel := ez.getD (IDX_SEL + 2) 0
  let mulSel := ez.getD (IDX_SEL + 3) 0
  let emulSel := ez.getD (IDX_SEL + 4) 0
  let emsSel := ez.getD (IDX_SEL + 5) 0
  -- ── gateLinConst: the six bodies behind their selectors ───────────────────────────────────
  let gG ← pGenericGate genSel alpha coeff wv
  let cPos ← pPoseidon mdsS coeff wv wn
  let aPos ← pAlphaCombine apow cPos
  let gPos ← eMul posSel aPos
  let cAdd' ← pCompleteAdd one wv
  let aAdd ← pAlphaCombine apow cAdd'
  let gAdd ← eMul caddSel aAdd
  let cMulG ← pVarBaseMul one wv wn
  let aMul ← pAlphaCombine apow cMulG
  let gMul ← eMul mulSel aMul
  let cEmul ← pEndoMul one endo wv wn
  let aEmul ← pAlphaCombine apow cEmul
  let gEmul ← eMul emulSel aEmul
  let cEms ← pEmScalar cA cB cC negOne three six eleven wv
  let aEms ← pAlphaCombine apow cEms
  let gEms ← eMul emsSel aEms
  let l1 ← eAdd gG gPos
  let l2 ← eAdd l1 gAdd
  let l3 ← eAdd l2 gMul
  let l4 ← eAdd l3 gEmul
  let lct ← eAdd l4 gEms
  -- ── ft_eval0 (`ftEval0R`, term for term) ──────────────────────────────────────────────────
  let w6g ← eAdd (wv.getD 6 0) gamma
  let i1 ← eMul w6g zZetaW
  let i2 ← eMul i1 a0
  let init ← eMul i2 zkp
  let numerFold ← (List.range 6).foldlM (fun x i => do
      let bs ← eMul beta (sv.getD i 0)
      let bw ← eAdd bs (wv.getD i 0)
      let bwg ← eAdd bw gamma
      eMul x bwg) init
  let afterPub ← eSub numerFold (← em W.pZeta)
  let dInit0 ← eMul a0 zkp
  let dInit ← eMul dInit0 zZeta
  let bz ← eMul beta zeta
  let denomFold ← (List.range 7).foldlM (fun x i => do
      let bzs ← eMul bz (shiftS.getD i 0)
      let gb ← eAdd gamma bzs
      let gbw ← eAdd gb (wv.getD i 0)
      eMul x gbw) dInit
  let afterDenom ← eSub afterPub denomFold
  let n1a ← eMul zeta1m1 a1
  let n1 ← eMul n1a zm3
  let n2a ← eMul zeta1m1 a2
  let zm1c ← eSub zeta one
  let n2 ← eMul n2a zm1c
  let nsum ← eAdd n1 n2
  let oneMz ← eSub one zZeta
  let numerator ← eMul nsum oneMz
  let denom ← eMul zm3 zm1c
  let dinv ← eWit C.denomInv
  let dchk ← eMul denom dinv
  let _ ← eEq dchk one
  let nd ← eMul numerator dinv
  let afterZk ← eAdd afterDenom nd
  let ftEval0 ← eSub afterZk lct
  -- ── Plonk_checks.checked: derive_plonk's `perm` scalar, asserted against the deferred word ──
  let p0 ← eMul zZetaW beta
  let p1 ← eMul p0 a0
  let pInit ← eMul p1 zkp
  let pFold ← (List.range 6).foldlM (fun x i => do
      let bs ← eMul beta (sv.getD i 0)
      let gb ← eAdd gamma bs
      let gbw ← eAdd gb (wv.getD i 0)
      eMul x gbw) pInit
  -- ⚑ The `perm` slot is the rung's OUTPUT and nothing more: `Plonk_checks.checked`'s comparison
  -- against the deferred word is R8's (`finWireOf`'s `permActual` reads THIS slot and `pc` compares
  -- it to `vPermShift`), not a second witnessed twin here. See `FtCfg.denomInv`.
  let perm ← eMul negOne pFold
  pure { ftEval0 := ftEval0, linConst := lct, zkp := zkp, perm := perm
       , zetaN := zetaN, omInv3 := omInv3 }

/-- The compiled program plus its named slots. -/
structure FtProg where
  prog : Array AOp
  slots : FtSlots
  deriving Repr, Inhabited

def ftProgOf (W : FtWire) (C : FtCfg) : FtProg :=
  let r := (ftBuild W C).run #[]
  { prog := r.2, slots := r.1 }

/-! ### The committed ft config and wire, for the ASSEMBLED instance. -/

/-- The step domain: `Common.Max_degree.step_log2 = 16` (`plonk_checks.ml` `srs_length_log2`). -/
def FT_LOG2N : Nat := 16
def FT_N : Nat := 2 ^ FT_LOG2N
/-- The `2^16`-th root of unity of `Fp`, DERIVED (`MinaWrapFtEval0.rootOfUnity`, read-only). -/
def FT_OMEGA : Nat := (Dregg2.Bridge.MinaWrapFtEval0.rootOfUnity pN FT_LOG2N).val
def FT_OMEGA_INV : Nat := Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fInv FT_OMEGA
/-- `env.endo_coefficient()` on the STEP side: the BASE endomorphism eigenvalue `5^((p−1)/3)`, NOT
the scalar-challenge endo (`MinaWrapFtEval0Weld` §6's `stepEndoCoefficient`; the conflation of the
two cube roots is the defect that file closed). -/
def FT_ENDO : Nat :=
  (Dregg2.Bridge.MinaWrapFtEval0.powFast ((5 : Nat) : ZMod pN) ((pN - 1) / 3)).val
/-- The three `EndomulScalar` quotients `11/6, −5/2, 2/3` (`quotientConsts`, read-only). -/
def FT_QUOT : Nat × Nat × Nat :=
  match Dregg2.Bridge.MinaWrapFtEval0.quotientConsts pN with
  | some (a, b, c) => (a.val, b.val, c.val)
  | none => (0, 0, 0)
/-- ⚑ **The SEVEN TICK COSET SHIFTS, DERIVED** — `TickShifts.tickShiftsFp 16`, the `Shifts::new`
Blake2b→field construction over the Step field, `#guard`-pinned THERE byte-exact against o1-labs'
own `Shifts::new(Radix2EvaluationDomain::<Fp>::new(2^16))` output. This is what `Plonk_checks`
`ft_eval0`'s denominator fold really runs on; §13 re-states the byte-exact identity here and shows
the OLD fixtures move `ft_eval0`. (Retires the module header's simplification #8.) -/
def FT_SHIFTS : List Nat := (Dregg2.Bridge.TickShifts.tickShiftsFp 16).map (fun x => x.val)

/-- The seven distinct nonzero placeholders the rung used BEFORE the derivation was wired in. Kept
for exactly one purpose: §13's red control, which shows they give a DIFFERENT `ft_eval0`. Nothing
emits them. -/
def FT_SHIFTS_WERE_FIXTURES : List Nat :=
  (List.range 7).map (fun i => (1 + 7919 * (i + 1) * (i + 3)) % pN)
/-- The linearization's `Constants::mds` IS `Vesta::sponge_params().mds = fp_kimchi` (`curve.rs:63`),
i.e. K3's own `PastaPoseidon.mdsN` — the same nine constants the sponge rung R1 permutes with. -/
def FT_MDS9 : List Nat := Dregg2.Circuit.Emit.PastaPoseidon.mdsN.flatten

/-- The ft program's `.inp` lookup: the challenges and the 43 columns, straight from the chains. It
does NOT read column 3, so the `ft` override below is not circular. -/
def ftInputEnv (s : StepShape) (d : SpongeData) : VarEnv :=
  (List.range s.chals).map (fun c => (vN s c s.emsRows, (chalOf s d c : Int)))
  ++ (List.range s.chals).map (fun c => (vLift s c, (liftOf s d c : Int)))
  ++ (List.range s.cipEvals).flatMap (fun k =>
      [(vEz s k, (evVal k 0 : Int)), (vEw s k, (evVal k 1 : Int))])

/-- ⚑ `Plonk.In_circuit.map_challenges ~f:Fn.id ~scalar plonk` (`step_verifier.ml:920-923`): the
`Scalar_challenge` fields α and ζ go through `scalar = SC.to_field_checked`, β and γ are `Challenge`
fields and stay RAW. So R6 reads `vLift` for α/ζ and `vN` for β/γ — upstream's own split, and the
retirement of the module header's simplification #7. -/
def ftWireOf (s : StepShape) : FtWire :=
  { ez := fun k => .inp (vColZ s k)
  , ew := fun k => .inp (vColW s k)
  , zeta := .inp (vLift s s.zetaChal)
  , alpha := .inp (vLift s s.alphaChal)
  , beta := .inp (vN s s.betaChal s.emsRows)
  , gamma := .inp (vN s s.gammaChal s.emsRows)
  , pZeta := .inp (vEz s 2) }

/-- ⚑ **The ONE witnessed value, and the sentence that used to be false about the other.** `denomInv`
is CHECKED by a row — `denom·denomInv = 1`, with `1` the program's own literal — so a wrong witness is
a refusal (or, at `denom = 0`, an unsatisfiable assert) rather than an accept. Until 2026-08-03 this
docblock said that of **both** witnesses, and of the second, `permClaimed`, it was FALSE:
`eEq perm permClaimed` forced a variable no other row read, so the prover set `permClaimed := perm`
and the row closed. That witness is gone. Computed by running the program once with a placeholder. -/
def ftCfgRaw (dInv : Nat) : FtCfg :=
  { log2n := FT_LOG2N, omega := FT_OMEGA, omegaInv := FT_OMEGA_INV
  , shifts := FT_SHIFTS, mds9 := FT_MDS9, endo := FT_ENDO
  , cA := FT_QUOT.1, cB := FT_QUOT.2.1, cC := FT_QUOT.2.2
  , denomInv := dInv }

/-- Everything R6 needs, evaluated ONCE. -/
structure FtData where
  fp : FtProg
  vals : Array Nat
  /-- The witnessed inverse of `(ζ − ω^{n−3})(ζ − 1)`, checked by a row. -/
  denomInv : Nat
  deriving Repr, Inhabited

/-- Run the program twice: once to read off `denom`, then once with the witness it forces. The second
run is the emitted one. ⚠ The FIRST run's `perm` slot used to be read off here as `permClaimed`; it is
not, since the assert that consumed it could not fail. -/
def runFt (s : StepShape) (d : SpongeData) : FtData :=
  let W := ftWireOf s
  let lk := envLookupAt (envIndex (ftInputEnv s d))
  let p0 := ftProgOf W (ftCfgRaw 1)
  let v0 := aEval lk p0.prog
  -- `denom` is the slot the `dchk` multiplication reads; recompute it directly from ζ and ω^{n−3}.
  let zeta := (lk (vLift s s.zetaChal)).toNat % pN
  let omInv3 := v0.getD p0.slots.omInv3 0
  let denom := fMul (fSub zeta omInv3) (fSub zeta 1)
  let dInv := Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fInv denom
  let p1 := ftProgOf W (ftCfgRaw dInv)
  { fp := p1, vals := aEval lk p1.prog, denomInv := dInv }

/-- ⚑ §6b's two scalars, READ OFF R6's compiled program: `Plonk_checks.checked`'s `perm`
(`plonk_checks.ml:482-488`) and `ζ^n` (`:496`, `= zeta_to_srs_length` at `log2n = 16`, `:497`). This
is the whole of the divergence §6b names — upstream's `ft_comm` reads the `Fq` Type2 statement twins
of these, which the step circuit does not constrain at all. -/
def ftcWireOf (s : StepShape) (f : FtData) : FtcWire :=
  { permV := aVarAt (baseFtS s) f.fp.prog f.fp.slots.perm
  , permVal := f.vals.getD f.fp.slots.perm 0
  , zetaV := aVarAt (baseFtS s) f.fp.prog f.fp.slots.zetaN
  , zetaVal := f.vals.getD f.fp.slots.zetaN 0 }

/-- **R6's rows**: the compiled program, the tie of its `ft_eval0` output to the `ft` column of the
`combined_inner_product` vector, and the σ-only probes. -/
def ftRows (s : StepShape) (f : FtData) (wired : Bool) : List SRow :=
  let base := baseFtS s
  let V := aVarAt base f.fp.prog
  aRows base f.fp.prog
  ++ [ genericRow (some (V f.fp.slots.ftEval0)) (some (vEz s 3)) none none none none (cEq ++ cNil)
     , probeRow wired (V f.fp.slots.ftEval0) (V f.fp.slots.linConst)
     , probeRow wired (V f.fp.slots.perm) (V f.fp.slots.zkp) ]

/-! ## §8e — R7, the EVALUATION ABSORPTION + opt-sponge masking.

`step_verifier.ml:950-1006`, `step_main.ml:525-567`. Three sponge SEGMENTS, each a fresh `[0,0,0]`
state, `absorb` blocks of two words (`rate = 2`), then bare squeeze permutations:

  * **A — the opt-sponge** over the carried bulletproof challenges, with a per-block `keep` MASK.
    Upstream's own trick (`:985-1003`) absorbs unconditionally and then MUXES the state
    (`Array.map2_exn sponge.state state_before ~f:(Field.if_ b)`); this compiles that mux as
    `outⱼ = beforeⱼ + keep·(afterⱼ − beforeⱼ)`, three lanes, three `Generic` halves each. That is
    the `branch_data.proofs_verified_mask` path, and it is the piece the sponge rung R1 had no
    shape for.
  * **B — the fr-sponge**: the challenge digest, `ft_eval1`, `p(ζ)`, `p(ζω)`, then **the 43 columns
    at ζ and ζω interleaved** (`to_absorption_sequence`), then TWO squeezes for ξ′ and r′.
  * **C — `hash_messages_for_next_step_proof`**: the app state, the 28 plonk-index commitments (56
    coordinates), the two challenge-polynomial commitments and the unpadded bulletproof challenges,
    then one squeeze.

⚑ EVERY ABSORBED WORD IS AN ASSEMBLY VARIABLE where upstream's is: segment A absorbs R2's
challenges, segment B absorbs R5's evaluation columns (the SAME variables R6 reads) and R6's
`ft_eval1`/`p(ζ)` entries, and segment C absorbs R3's and R4's fold outputs. -/

/-- One segment's schedule. -/
structure SegSpec where
  /-- absorbed words: the variable and its value, padded to an even length. -/
  ws : List (PVar × Nat)
  /-- squeeze permutations after the absorb blocks. -/
  squeezes : Nat
  /-- whether the segment muxes its state with a per-block `keep` bit. -/
  masked : Bool
  /-- ⚑ the FIRST masked block. `Opt_sponge.of_sponge` converts at the first `Opt` element and
  everything after it is opt (`step_verifier.ml:1198-1211`), so a segment can absorb a `Not_opt`
  prefix unconditionally and mask the rest — which is exactly `hash_messages_for_next_step_proof`'s
  shape. `0` for a wholly-masked segment. -/
  maskFrom : Nat := 0
  /-- ⚑ For a MASKED segment, the `keep` VARIABLE and BIT of each absorb block. Both come from
  §8h's unpacking of the `branch_data` statement word — this is not a schedule constant. -/
  keep : Nat → PVar × Nat := fun _ => (xv 0, 0)
  /-- ⚑ **`Sponge.copy`** — the segment does not start at `[0,0,0]` but at ANOTHER sponge's state,
  whose three lanes are that sponge's own variables. `none` is a fresh `Sponge.create` (segments A,
  B, C); `some f` is `Sponge.copy` (segment D, `step_main.ml:547` / `step_verifier.ml:1164`, which
  copies `sponge_after_index` rather than re-absorbing the 28 index commitments). A copy is a σ
  class, not a recomputation: block 0's state lanes ARE the source's variables. -/
  copyFrom : Option (Nat → PVar) := none
  /-- …and the copied STATE's values. `[0,0,0]` for a fresh sponge. -/
  init : List Nat := [0, 0, 0]
  deriving Inhabited

/-- Is absorb block `b` muxed by a `keep` bit? -/
def SegSpec.maskedAt (g : SegSpec) (b : Nat) : Bool := g.masked && g.maskFrom ≤ b
def SegSpec.nb (g : SegSpec) : Nat := (g.ws.length + 1) / 2
/-- ⚑⚑ **A SEGMENT'S PERMUTATION COUNT, UNDER MINA'S LAZY SPONGE** (§1c′). The `nb` absorb blocks
supply `nb − 1` permutations while absorbing; the FIRST squeeze supplies the `nb`-th
(`sponge.ml:322-325`, `Absorbed _ → block_cipher`); the SECOND is free (`Squeezed 1`, `n ≠ rate`,
`state.(1)`); only every second squeeze after that costs one more. So `blocks = nb + ⌈sq/2⌉ − 1`.
⚠ It was `nb + squeezes` — one permutation per squeeze on top of the absorb blocks — which put
segment B's ξ′ and r′ TWO permutations apart where `step_verifier.ml:1007-1009` reads
`state.(0)`/`state.(1)` of ONE. -/
def SegSpec.blocks (g : SegSpec) : Nat := g.nb + (g.squeezes + 1) / 2 - 1
/-- Squeeze `k`'s `(block, lane)` — the state ENTERING block `.1`, at lane `.2`. -/
def SegSpec.sqStBlock (g : SegSpec) (k : Nat) : Nat := g.nb + k / 2
def SegSpec.sqStLane (_g : SegSpec) (k : Nat) : Nat := k % 2

/-- A segment's evaluated trajectory. -/
structure SegData where
  /-- the state ENTERING each block, `blocks + 1` of them. -/
  states : List (List Nat)
  /-- the 56 round states of each block's permutation. -/
  perms : List (List (List Nat))
  /-- the un-muxed permutation output of each absorb block. -/
  afters : List (List Nat)
  deriving Repr, Inhabited

/-- `keep` bit of absorb block `b`, out of the spec. -/
def SegSpec.keepBit (g : SegSpec) (b : Nat) : Nat := (g.keep b).2
/-- …and its variable. -/
def SegSpec.keepVar (g : SegSpec) (b : Nat) : PVar := (g.keep b).1

def runSeg (g : SegSpec) : SegData :=
  (List.range g.blocks).foldl
    (fun d b =>
      let pre := d.states.getLastD [0, 0, 0]
      let post :=
        if b < g.nb then
          [ fAdd (pre.getD 0 0) ((g.ws.getD (2 * b) (xv 0, 0)).2)
          , fAdd (pre.getD 1 0) ((g.ws.getD (2 * b + 1) (xv 0, 0)).2)
          , pre.getD 2 0 ]
        else pre
      let ss := permStates post
      let after := ss.getLastD post
      let next :=
        if b < g.nb && g.maskedAt b && g.keepBit b == 0 then pre else after
      { states := d.states ++ [next], perms := d.perms ++ [ss]
      , afters := d.afters ++ [after] })
    { states := [g.init], perms := [], afters := [] }

/-- Segment variable regions, all relative to one base. -/
def sgSt (base _nb _sq b j : Nat) : PVar := xv (base + 3 * b + j)
def sgPost (base nb sq b j : Nat) : PVar := xv (base + 3 * (nb + sq + 1) + 2 * b + j)
def sgAfter (base nb sq b j : Nat) : PVar :=
  xv (base + 3 * (nb + sq + 1) + 2 * nb + 3 * b + j)
def sgD (base nb sq b j : Nat) : PVar :=
  xv (base + 3 * (nb + sq + 1) + 5 * nb + 3 * b + j)
def sgP (base nb sq b j : Nat) : PVar :=
  xv (base + 3 * (nb + sq + 1) + 8 * nb + 3 * b + j)
/-- ⚑ **THE RATE-2 PAD LANE** — the second lane of a segment's LAST absorb block when its word list
is odd. Mina's sponge is LAZY (`snarky/sponge/sponge.ml:296-308`): `absorb` fills lanes `0..rate−1`
and only permutes when the rate is already full, so an odd final word sits alone in lane 0 and the
first `squeeze` (`:322-325`) permutes it. Adding a PINNED ZERO to lane 1 is that permutation exactly,
and `segRows` emits the `w = 0` row that pins it — a padded lane that were a free witness would be
one more field element the prover feeds the sponge.

The cell comes out of the segment's own RESERVED tail — `segVarCount`'s trailing `nb`, the ids the
retired per-block `keep` region left behind — so no region moves and `segVarCount` is unchanged. -/
def sgPad (base nb sq : Nat) : PVar := xv (base + 3 * (nb + sq + 1) + 11 * nb)
/-- Does this segment's word list need the pad lane? -/
def SegSpec.padded (g : SegSpec) : Bool := g.ws.length % 2 == 1
/-- ⚑ `hash_messages_for_next_step_proof`'s OUTPUT — segment C's squeeze. Upstream this IS the step
statement's `messages_for_next_step_proof` hash, which the step circuit carries as a public word
(`step_main.ml:121,522`). Exposing it is what makes segment C's mask REACH the verifier: change
`branch_data` and this public word moves. -/
def hmDigestVar (s : StepShape) : PVar := sgSt (baseSegC s) (nbC s) 1 (nbC s) 0
-- ⚑ There is no per-block `keep` VARIABLE region any more: since §8h a masked segment's mux reads
-- `g.keepVar b`, which is one of the two `branch_data` mask bits. The id slots the old region
-- occupied stay reserved in `segVarCount` so no other region moves.

/-- ⚑ Segment state lane `j` entering block `b`, THROUGH the copy: block 0's lanes are the copy
source's variables when the segment is a `Sponge.copy`, and its own otherwise. Every read of a
segment's state goes through this, so a copied segment cannot silently allocate a second state. -/
def SegSpec.stV (g : SegSpec) (base nb sq b j : Nat) : PVar :=
  match g.copyFrom with
  | some f => if b == 0 then f j else sgSt base nb sq b j
  | none => sgSt base nb sq b j

/-! ### §8m — ⚑ the segment mask's `Field.if_`, ON THE GADGET RAIL.

Until 2026-08-05 this was open-coded here, and the same three-half mux was open-coded again in
`sfTermRows` and a third time in `KimchiWrapMainCore` — three copies of `e + b·(t − e)` with no
shared name, no soundness lemma, and nothing to stop one drifting. It is now
`KimchiGadgets.spongeMaskHalves`, whose selector semantics are a named field-general theorem
(`selectHalves_sound`) and whose booleanity gate is a named gate rather than a fourteenth
`x(x−1)`. -/

/-- ⚑ **THE MASK, AS ONE GADGET CALL.** Three lanes, one selector:
`outⱼ = beforeⱼ + keep·(afterⱼ − beforeⱼ)`. -/
def sgMaskRows (base nb sq : Nat) (g : SegSpec) (b : Nat) : List SRow :=
  let lane : Nat → KimchiGadgets.MuxWires := fun j =>
    ⟨sgAfter base nb sq b j, g.stV base nb sq b j, sgD base nb sq b j,
     sgP base nb sq b j, g.stV base nb sq (b + 1) j⟩
  packHalves (KimchiGadgets.spongeMaskHalves (g.keepVar b) [lane 0, lane 1, lane 2])

set_option maxRecDepth 100000 in
/-- ⚑ **THE EMITTED OBJECT DID NOT MOVE.** The gadget call produces exactly the five rows this site
wrote by hand — three `(cSub ++ cMul)`, one `(cAdd ++ cAdd)`, one `(cAdd ++ cNil)` — for EVERY
`base`, `nb`, `sq`, `g` and `b`, by `rfl`. Not a case test: a general theorem over every shape. -/
theorem sgMaskRows_is_the_open_coded_shape (base nb sq : Nat) (g : SegSpec) (b : Nat) :
    sgMaskRows base nb sq g b =
      (List.range 3).map (fun j =>
        genericRow (some (sgAfter base nb sq b j)) (some (g.stV base nb sq b j))
                   (some (sgD base nb sq b j))
                   (some (g.keepVar b)) (some (sgD base nb sq b j))
                   (some (sgP base nb sq b j)) (cSub ++ cMul))
      ++ [ genericRow (some (g.stV base nb sq b 0)) (some (sgP base nb sq b 0))
                      (some (g.stV base nb sq (b + 1) 0))
                      (some (g.stV base nb sq b 1)) (some (sgP base nb sq b 1))
                      (some (g.stV base nb sq (b + 1) 1)) (cAdd ++ cAdd)
         , genericRow (some (g.stV base nb sq b 2)) (some (sgP base nb sq b 2))
                      (some (g.stV base nb sq (b + 1) 2)) none none none (cAdd ++ cNil) ] := by
  simp [sgMaskRows, packHalves, genericRow, KimchiGadgets.spongeMaskHalves,
        KimchiGadgets.selectHalvesN, KimchiGadgets.subHalf, KimchiGadgets.mulHalf,
        KimchiGadgets.addHalf, KimchiGadgets.cSub, KimchiGadgets.cMul, KimchiGadgets.cAdd,
        cSub, cMul, cAdd, cNil, List.range_succ, List.range_zero]

/-- **One segment's rows.** -/
def segRows (base : Nat) (g : SegSpec) (d : SegData) (wired : Bool) : List SRow :=
  let nb := g.nb
  let sq := g.squeezes
  let stv := g.stV base nb sq
  -- ⚑ absorbed word `k`, with the PAD LANE as the default rather than `xv 0`. An odd word list used
  -- to fall through `getD`'s default and wire variable ZERO — the transcript's own pinned init lane
  -- — into the last block's addend row, i.e. a σ class across two sponges for a lane that carries
  -- nothing. `sgPad` is this segment's own cell and the row below pins it.
  let wAt : Nat → PVar × Nat := fun k => g.ws.getD k (sgPad base nb sq, 0)
  -- ⚑ A FRESH sponge pins its own `[0,0,0]`; a COPY has no init rows at all, because its block-0
  -- lanes are the source sponge's variables and the source's own rows already computed them.
  (if g.copyFrom.isSome then []
   else [ genericRow (some (sgSt base nb sq 0 0)) none none (some (sgSt base nb sq 0 1)) none none
            (cConst 0 ++ cConst 0)
        , genericRow (some (sgSt base nb sq 0 2)) none none none none none (cConst 0 ++ cNil) ])
  ++ (if g.padded then
        [ genericRow (some (sgPad base nb sq)) none none none none none (cConst 0 ++ cNil) ]
      else [])
  ++ (List.range g.blocks).flatMap (fun b =>
      if b < nb then
        let out : Nat → PVar :=
          if g.maskedAt b then (fun j => sgAfter base nb sq b j)
          else (fun j => stv (b + 1) j)
        [ genericRow (some (stv b 0)) (some (wAt (2 * b)).1)
                     (some (sgPost base nb sq b 0))
                     (some (stv b 1)) (some (wAt (2 * b + 1)).1)
                     (some (sgPost base nb sq b 1)) (cAdd ++ cAdd) ]
        ++ permBlockRows (sgPost base nb sq b 0) (sgPost base nb sq b 1) (stv b 2)
             (out 0) (out 1) (out 2) (d.perms.getD b [])
        -- the `Field.if_` mux: outⱼ = beforeⱼ + keep·(afterⱼ − beforeⱼ), now ONE gadget call.
        -- `sgMaskRows_is_the_open_coded_shape` (§8m) pins the emitted rows unchanged.
        ++ (if g.maskedAt b then sgMaskRows base nb sq g b else [])
        -- ⚑ the probe sits on the state the FIRST squeeze reads — which is the last absorb block's
        -- own output now, not a squeeze block's.
        ++ (if b + 1 == nb then [probeRow wired (stv (b + 1) 0) (stv (b + 1) 1)] else [])
      else
        -- a bare permutation: the THIRD consecutive squeeze's (`Squeezed 2 = rate`).
        permBlockRows (stv b 0) (stv b 1) (stv b 2)
          (stv (b + 1) 0) (stv (b + 1) 1) (stv (b + 1) 2)
          (d.perms.getD b [])
        ++ [probeRow wired (stv (b + 1) 0) (stv (b + 1) 1)])

/-- A segment's environment. ⚑ A COPY owns no block-0 state cells — those are the source sponge's
variables and `circuitEnv` already binds them there; assigning them again would be a second binding
of one id, which `envIndex` would silently resolve to whichever came first. -/
def segEnv (base : Nat) (g : SegSpec) (d : SegData) : VarEnv :=
  let nb := g.nb
  let sq := g.squeezes
  ((List.range (g.blocks + 1)).filter (fun b => b != 0 || g.copyFrom.isNone)).flatMap (fun b =>
    (List.range 3).map (fun j => (sgSt base nb sq b j, ((d.states.getD b []).getD j 0 : Int))))
  -- ⚑ the pad lane's own cell, at the zero `segRows` pins it to.
  ++ (if g.padded then [(sgPad base nb sq, (0 : Int))] else [])
  ++ (List.range nb).flatMap (fun b =>
      let pre := d.states.getD b []
      (List.range 2).map (fun j =>
        (sgPost base nb sq b j,
         (fAdd (pre.getD j 0) ((g.ws.getD (2 * b + j) (xv 0, 0)).2) : Int))))
  -- (the `keep` VARIABLE's value is owned by §8h — it is a `branch_data` mask bit, not a segment id)
  ++ (if g.masked then
        ((List.range nb).filter g.maskedAt).flatMap (fun b =>
          let pre := d.states.getD b []
          let aft := d.afters.getD b []
          let k := g.keepBit b
          (List.range 3).flatMap (fun j =>
              let dv := fSub (aft.getD j 0) (pre.getD j 0)
              [ (sgAfter base nb sq b j, (aft.getD j 0 : Int))
              , (sgD base nb sq b j, (dv : Int))
              , (sgP base nb sq b j, (fMul k dv : Int)) ]))
      else [])

/-- The three segments' shapes, from the committed `StepShape`. -/
def StepShape.frCols (s : StepShape) : Nat := s.cipEvals - EV_PREFIX
/-- Carried bulletproof challenges: two previous proofs × `bRounds` each. -/
def StepShape.optWords (s : StepShape) : Nat := 2 * s.bRounds
/-- The INNER `hash_messages_for_next_step_proof_opt`'s field elements: the `Not_opt` prefix
(`sponge_after_index` + app state), then TWO `Opt`-masked runs of `(sg_old[i] ×2, that proof's
`bRounds` carried challenges)` — interleaved per proof, `composition_types.ml:603-606`. -/
def StepShape.hmWords (s : StepShape) : Nat := N_HM_FIX + 2 * (2 + s.bRounds)
/-- The OUTER `hash_messages_for_next_step_proof`'s: app state, then ONE unmasked run of
(`G` ×2, this step's `bRounds` computed bulletproof challenges). No index prefix — it is a
`Sponge.copy` of `sponge_after_index` (`step_verifier.ml:1164`). -/
def StepShape.hmOutWords (s : StepShape) : Nat := N_HM_APP + 2 + s.bRounds

/-! ### §8h — `branch_data`'s `proofs_verified_mask`, UNPACKED.

`step_main.ml:53,70-72`, `composition_types/branch_data.ml:88-101`, `pickles_base/
proofs_verified.ml:70-100`. The opt-sponge's per-absorption `keep` is
`Vector.trim_front branch_data.proofs_verified_mask` — two Boolean variables of the STATEMENT, not a
schedule constant. `Checked.pack` recombines them with `domain_log2` into the single field element
the statement carries: `4·domain_log2 + (m₀ + 2·m₁)`. These are the rows for that, and `optSpec`
below reads the two bits.

⚑ `Prefix_mask.there` is `N0 ↦ [ff;ff] · N1 ↦ [ff;tt] · N2 ↦ [tt;tt]`, so a set bit is a SUFFIX and
the committed instance (ONE previous proof, `N1`) keeps slot 1 and drops slot 0 — the OPPOSITE of
the "first half kept" pattern this rung ran until 2026-08-02. -/

/-- `Prefix_mask.there N1` — the honest instance's mask, one previous proof of two slots. -/
def MASK_BITS : List Nat := [0, 1]
/-- `domain_log2` — `Common.Max_degree.step_log2`, the same 16 `FT_LOG2N` is. -/
def BRANCH_DOMAIN_LOG2 : Nat := 16
/-- `Branch_data.Checked.pack` (`branch_data.ml:95-101`). -/
def branchPacked : Nat :=
  (4 * BRANCH_DOMAIN_LOG2 + MASK_BITS.getD 0 0 + 2 * MASK_BITS.getD 1 0) % pN

/-- Which previous proof absorb block `b` of the opt-sponge carries: each of the two previous proofs
contributes `bRounds` challenge words and a block absorbs two, so the blocks split at `bRounds/2`. -/
def optProofOf (s : StepShape) (b : Nat) : Nat := if 2 * b < s.bRounds then 0 else 1
/-- ⚑ Block `b`'s `keep` — the mask VARIABLE and its bit, both from `branch_data`. -/
def optKeep (s : StepShape) (b : Nat) : PVar × Nat :=
  (vMask s (optProofOf s b), MASK_BITS.getD (optProofOf s b) 0)

/-- **§8h's rows.** Booleanity of both mask bits (`Boolean.typ`'s own check), `Checked.pack` — which
ties them to the `branch_data` statement word — the `Prefix_mask` SUFFIX shape, and `Branch_data.typ`'s
own `~assert_16_bits` on `domain_log2`.

⚑⚑ **THE TWO THAT LANDED 2026-08-03, and what each one refuses.**

  * **The suffix half `m₀·(1 − m₁) = 0`.** `Prefix_mask.there` is `N0 ↦ [ff;ff] · N1 ↦ [ff;tt] ·
    N2 ↦ [tt;tt]` (`pickles_base/proofs_verified.ml:75-81`) — a set bit is a SUFFIX, so `m₀ ≤ m₁`.
    Booleanity alone admits FOUR masks and `[1,0]` is not one upstream can name; it closed here until
    this row, and it is a different `combined_inner_product` (§12l) and a different opt-sponge digest
    (§14a) — i.e. an ILLEGAL branch the circuit accepted.
  * **The 16-bit chain on `vDomLog2`** (`per_proof_witness.ml:166-168`). `Checked.pack` is ONE
    equation, so with the mask free the prover solved for `domain_log2`; with the mask pinned to
    three values he still had three. `(branch_data − maskPack)·4⁻¹` is a 16-bit integer for exactly
    one of the three and a full-width field element for the other two, so this chain is what makes
    the triple `(m₀, m₁, domain_log2)` a FUNCTION of the statement word rather than a choice. -/
def branchRows (s : StepShape) (wired : Bool) : List SRow :=
  [ genericRow (some (vMask s 0)) (some (vMask s 0)) (some (vMask s 0))
               (some (vMask s 1)) (some (vMask s 1)) (some (vMask s 1)) (cMul ++ cMul)
  , genericRow (some (vMask s 0)) (some (vMask s 1)) (some (vMaskPack s))
               (some (vDomLog2 s)) (some (vMaskPack s)) (some (vBranch s))
               ([1, 2, -1, 0, 0] ++ [4, 1, -1, 0, 0])
  -- ⚑ `Prefix_mask.there`'s SUFFIX shape: `m₀ − m₀·m₁ = 0`, i.e. `m₀ ≤ m₁`. The second half is the
  -- probe's partner rather than a second constraint.
  , genericRow (some (vMask s 0)) (some (vMask s 1)) none none none none
               ([1, 0, 0, -1, 0] ++ cNil)
  , probeRow wired (vMask s 0) (vMask s 1)
  , probeRow wired (vBranch s) (vMaskPack s) ]
  ++ tfcRowsN s RNG_DOMLOG2_ROWS (rngVars s (RNG_DOMLOG2 s)) (vDomLog2 s) false
       BRANCH_DOMAIN_LOG2 wired

/-- ⚑ Segment A absorbs **`prev_challenges`** (`step_verifier.ml:953-959`), the previous proofs'
CARRIED bulletproof challenges — a `Per_proof_witness` field, not this transcript's squeezes. It took
`vN s (i % chals) emsRows` until 2026-08-02; see `vPrevChal` for what that false wire cost. Segment C
absorbs the SAME variables (`step_main.ml:80`), so they are one σ class across two sponges. -/
def optSpec (s : StepShape) : SegSpec :=
  { ws := (List.range s.optWords).map (fun i => (vPrevChal s i, prevChalVal i))
  , squeezes := 1, masked := true, keep := optKeep s }

/-- ⚑⚑ **THE fr-SPONGE, WITH ITS SEED** (§22). `sd` is `step_main.ml:41-46`'s
`Sponge.absorb sponge (\`Field proof_state.sponge_digest_before_evaluations)` — the FIRST item the
sponge `finalize_other_proof` runs ever eats, and the reason Wrap statement word 10 is not a free
witness. `dg` is `challenge_digest` (`step_verifier.ml:962`), which is where this segment used to
start; then `ft_eval1`, `p(ζ)`, `p(ζω)` (`:963-965`) and `to_absorption_sequence`'s 2×43 columns.

⚑ 5 + 2·43 = 91 words is ODD, so this segment carries the rate-2 PAD LANE (`sgPad`), which is
Mina's own lazy sponge leaving the last word alone in lane 0 until the first squeeze permutes. -/
def frSpec (s : StepShape) (sd : PVar × Nat) (dg : PVar × Nat) (ftVal : Nat) : SegSpec :=
  { ws := [ sd, dg, (vEw s 3, evVal 3 1), (vEz s 2, evZOf ftVal 2), (vEw s 2, evVal 2 1) ]
      ++ (List.range s.frCols).flatMap (fun k =>
          [ (vColZ s k, evZOf ftVal (EV_PREFIX + k))
          , (vColW s k, evVal (EV_PREFIX + k) 1) ])
  , squeezes := 2, masked := false }

/-- A deterministic fixture standing for one of the two APP-STATE words. Since §3c the plonk-index
half of this prefix is derived and this covers only `state_to_field_elements app_state`. -/
def hmVal (i : Nat) : Nat := (13 + 3000017 * i + 5 * i * i) % pN

/-- ⚑ Segment C's per-block `keep`, and the SECOND consumer of `branch_data`'s mask.
`hash_messages_for_next_step_proof_opt` masks BOTH the `challenge_polynomial_commitments` and the
`old_bulletproof_challenges` with the SAME `proofs_verified_mask` — two `Vector.map2`s over the
vector §8h already unpacked (`step_verifier.ml:1180-1186`) — while the app state stays `Not_opt`.

⚑ **CORRECTED AT SOURCE 2026-08-02: the two vectors are INTERLEAVED PER PROOF, not concatenated.**
`to_field_elements_without_index` (`composition_types.ml:595-607`) is
`Array.concat [app_state; Vector.map2 comms chals ~f:(fun c ch -> g c ++ ch) |> concat]`, so the
word order is `comm₀ ×2 · chals₀ ×bRounds · comm₁ ×2 · chals₁ ×bRounds` — one proof's commitment
IMMEDIATELY followed by that proof's challenges. This function ran the concatenated layout (all four
commitment coordinates, then all `2·bRounds` challenges) until it was read at source. The per-proof
stride is `2 + bRounds`, which is EVEN because `bRounds` is, so no rate-2 block straddles the two
mask bits. -/
def hmKeepAt (s : StepShape) (ms : List Nat) (b : Nat) : PVar × Nat :=
  let w := 2 * b
  let i := min 1 (if w < N_HM_FIX then 0 else (w - N_HM_FIX) / (2 + s.bRounds))
  (vMask s i, ms.getD i 0)

/-- **`index_digest` EMITS NO ROWS** (§3c, 2026-08-03). `Sponge.copy` is a σ class and the squeeze it
runs is the permutation segment C's own block 27 already performs; `vIdxD` names segment C's block-28
state lanes, so the digest is a READ and not a computation. This function is kept as the NAME of that
fact — deleting it would leave "where did `index_digest`'s permutation go?" unanswered — and it is
the only place in the assembly that answers `[]` on purpose. -/
def idxDigestRows (_s : StepShape) (_wired : Bool) : List SRow := []

/-- ⚑ **`sg_old[i]`, the variable and its value** — `prev_challenge_polynomial_commitments`, the
`Per_proof_witness` field `verify_one` passes as `~sg_old` (`step_main.ml:107`) and absorbs at
`step_verifier.ml:538`. BOTH slots are already variables of this assembly and neither needed a new
one: slot 0 is `combine_split_commitments`' `~init` accumulator (`:606`, `qInit`) and slot 1 is fold
ROUND 0's base, because round `r` folds census commitment `r+1` and commitment 1 IS `sg_old[1]`
(§2, `wdbAbsorbed`). ⚠ §17 priced the second half as needing a new `Wrap_hack.Checked.pad_commitments`
slot; read at source it does not — the correction is a FOUR-word swap, not two. -/
def sgOldVar (s : StepShape) (i j : Nat) : PVar :=
  let p := if i == 0 then qInit s else qT s 0
  if j == 0 then ipx s p else ipy s p
def sgOldVal (v : IpaData) (i j : Nat) : Nat :=
  let p := if i == 0 then Dregg2.Bridge.MinaStepPrevCommitments.SG_OLD0_XY
           else v.bases.getD 0 (0, 0)
  if j == 0 then p.1 else p.2

/-- ⚑ **THE INNER `hash_messages_for_next_step_proof_opt`** (`step_main.ml:59-81`), read at source.

    { app_state
    ; dlog_plonk_index = d.wrap_key
    ; challenge_polynomial_commitments = prev_challenge_polynomial_commitments
    ; old_bulletproof_challenges = prev_challenges }

⚠ ⚑ **CORRECTED 2026-08-02, AND IT WAS A MEASURED WRONG WIRE.** The two commitment slots were
`mpx/mpy (pSum (msmTerms−2))` — R3's x_hat MSM output — and `ipx/ipy (qSum (ipaRounds−1))` — R4's
fold output `q`. Neither is `prev_challenge_polynomial_commitments`: `x_hat` is `multiscale_known`'s
result over the SRS Lagrange bases and `q` is `p_prime + lr_prod`, both computed INSIDE this
`verify_one` and both already public words of their own (`exposedVars` 13–16). What the hash absorbs
is the previous proof's own `sg_old`, which the fold consumes as its `~init` and its round-0 base.
So this segment's digest — a PUBLIC word — was a function of two quantities upstream does not put in
it, and not a function of the two it does.

⚑ §3c: the `Not_opt` prefix is `sponge_after_index`'s own absorption — the 28 plonk-index
commitments as 56 coordinates, 27 of them THE FOLD'S OWN `.const` base variables — then the two
app-state words, which are the only fixtures left in it. -/
def hmSpec (s : StepShape) (v : IpaData) : SegSpec :=
  { ws := (List.range N_IDX_WORDS).map (fun i => (idxVar s (i / 2) (i % 2), idxVal (i / 2) (i % 2)))
      ++ (List.range N_HM_APP).map (fun i => (vHm s i, hmVal i))
      -- ⚑ INTERLEAVED per previous proof (`composition_types.ml:603-606`): `sg_old[i]`'s two
      -- coordinates, then THAT proof's `bRounds` carried challenges, then the next slot.
      -- `old_bulletproof_challenges = prev_challenges` (`step_main.ml:80`) — the SAME vector
      -- segment A absorbs, so segment C's public digest moves when one of them is bent.
      ++ (List.range 2).flatMap (fun i =>
          [ (sgOldVar s i 0, sgOldVal v i 0), (sgOldVar s i 1, sgOldVal v i 1) ]
          ++ (List.range s.bRounds).map (fun k =>
              (vPrevChal s (i * s.bRounds + k), prevChalVal (i * s.bRounds + k))))
  , squeezes := 1, masked := true, maskFrom := N_HM_FIX / 2, keep := hmKeepAt s MASK_BITS }

/-- ⚑ **THE MIS-WIRED SEGMENT C, kept as the RED CONTROL'S "before" object and nothing else.**
`§12k` bends the two things this absorbed and shows they no longer move the digest, and bends the two
`sg_old` slots and shows they now do. Not reachable from `rungRows`; it emits no row. -/
def hmSpecMiswired (s : StepShape) (t : MsmData) (v : IpaData) : SegSpec :=
  { ws := (List.range N_IDX_WORDS).map (fun i => (idxVar s (i / 2) (i % 2), idxVal (i / 2) (i % 2)))
      ++ (List.range N_HM_APP).map (fun i => (vHm s i, hmVal i))
      ++ [ (mpx s (pSum s (s.msmTerms - 2)), (t.sums.getLastD (0, 0)).1)
         , (mpy s (pSum s (s.msmTerms - 2)), (t.sums.getLastD (0, 0)).2)
         , (ipx s (qSum s (s.ipaRounds - 1)), (v.sums.getLastD (0, 0)).1)
         , (ipy s (qSum s (s.ipaRounds - 1)), (v.sums.getLastD (0, 0)).2) ]
      ++ (List.range (2 * s.bRounds)).map (fun i => (vPrevChal s i, prevChalVal i))
  , squeezes := 1, masked := true, maskFrom := N_HM_FIX / 2
  -- …with the CONCATENATED layout's own `keep` map, the one `hmKeepAt` ran: the four commitment
  -- coordinates take one mask bit per PAIR, then the challenges split at `bRounds`. Running the
  -- corrected map over the old word order would be a straw man.
  , keep := fun b =>
      let w := 2 * b
      let i := if w < N_HM_FIX + 4 then (w - N_HM_FIX) / 2
               else if w - (N_HM_FIX + 4) < s.bRounds then 0 else 1
      (vMask s i, MASK_BITS.getD i 0) }

/-! ### ⚑⚑ Segment D — the **OUTER** `hash_messages_for_next_step_proof` (`step_main.ml:525-566`).

    let messages_for_next_step_proof =
      let challenge_polynomial_commitments =
        … fun acc -> acc.wrap_proof.opening.challenge_polynomial_commitment …    (:530-535)
      hash_messages_for_next_step_proof
        { app_state ; dlog_plonk_index ; challenge_polynomial_commitments
        ; old_bulletproof_challenges = (* unpadded! *) bulletproof_challenges }  (:559-566)
    in … { proof_state = { unfinalized_proofs; messages_for_next_step_proof } …  (:572-575)

**This is `G`'s binder**, and it is one rung ABOVE `verify_one`: the commitment it absorbs is the
very `challenge_polynomial_commitment` `check_bulletproof` destructures (`step_verifier.ml:253`) and
uses in `rhs` (`:333`), and its squeeze is the step statement's `messages_for_next_step_proof`, a
PUBLIC word.

Three things it is NOT, each read at source rather than assumed:

  * **NOT masked.** It is `hash_messages_for_next_step_proof`, not `…_opt` (`:547`), so there is no
    `proofs_verified_mask` and no `Opt_sponge` — every word is `Not_opt`.
  * **NOT a re-absorption of the index.** Both hashes are `Sponge.copy after_index`
    (`step_verifier.ml:1164`, `:1178`), so segment D starts at segment C's OWN state after its 56
    index words — the same copy §3c already models for `index_digest`. Its block-0 state lanes ARE
    segment C's variables.
  * **NOT `prev_challenges`.** `old_bulletproof_challenges` here is `bulletproof_challenges`, the
    vector `finalize_other_proof` RETURNS (`step_verifier.ml:1114-1116,1147`,
    `compute_challenges ~scalar`), i.e. the deferred challenges the `b(ζ)` product folds over,
    LIFTED. In this assembly those are `vLift (uChal k)` — segment C's are `vPrevChal`, a different
    vector. Two hashes, two challenge vectors; conflating them would have been the same class of
    defect this rung is correcting.

⚑ Slot count: `V.f proofs_verified (M.f prevs)` (`:538`) is one entry per previous proof of THIS
rule, unmasked and unpadded. This file assembles ONE `verify_one`, so segment D has ONE slot.
(`StepMergeProof` and `StepBlockProof` have two; `StepZkappProvedProof` one.) -/
def hmOutSpec (s : StepShape) (d : SpongeData) (G : Nat × Nat) : SegSpec :=
  { ws := (List.range N_HM_APP).map (fun i => (vHmO s i, hmOVal i))
      ++ [ (vGx s, G.1), (vGy s, G.2) ]
      ++ (List.range s.bRounds).map (fun k =>
          (vLift s (s.uChal k), liftOf s d (s.uChal k)))
  , squeezes := 1, masked := false
  , copyFrom := some (fun j => sgSt (baseSegC s) (nbC s) 1 (N_IDX_WORDS / 2) j)
  , init := idxAfterState }

/-- ⚑ **The step statement's `messages_for_next_step_proof`** (`step_main.ml:572-575`) — segment D's
squeeze, and the word `G` moves. -/
def hmOutDigestVar (s : StepShape) : PVar := sgSt (baseSegD s) (nbD s) 1 (nbD s) 0
/-- …and its VALUE, as a function of `G` alone with the rest of the assembly held fixed. This is what
§17's exhibit evaluates at the honest and at the re-solved commitment. -/
def hmOutDigestOf (s : StepShape) (d : SpongeData) (G : Nat × Nat) : Nat :=
  ((runSeg (hmOutSpec s d G)).states.getLastD []).getD 0 0

/-! ## §8f — R8, `finalize_other_proof`'s TAIL: the deferred values BIND.

`step_verifier.ml:1076-1147`. R5–R7 compute the deferred quantities; NOTHING yet compares them with
what the proof CLAIMS. This rung is that comparison, and it is the semantically load-bearing part of
`finalize_other_proof`:

  * **`ζω = domain#generator · plonk.zeta`** (`:934`) and the SECOND challenge polynomial
    `b(ζω) = ∏(1 + uₖ·(ζω)^{2^{k}})` over the LIFTED bulletproof challenges, so
    **`b_actual = challenge_poly ζ + r · challenge_poly ζω`** (`:1124-1128`) — the `+ r·…` leg the
    module header's simplification #4 named as absent.
  * **THREE `Shifted_value.Type1.to_field` unshifts** (`shifted_value.ml:133-135`: `t + t + c`) of
    `combined_inner_product` (`:1105-1109`), `b` (`:1126-1127`) and — inside
    `Plonk_checks.checked` (`plonk_checks.ml:536-544`) — `plonk.perm`.
    ⚑ **THE FIELD KEY.** A Type1 shift keys on the VALUE's own field, not the circuit's. These three
    are the Wrap proof-state's `fp` block, so the shift is **Type1 over `Fp`**: `c = 2^255 + 1`,
    `scale = 1/2` (`shift1`, `step_verifier.ml:825`; `PicklesStatementDiff` §1). The step statement's
    own `fq` block is Type2/`Fq` — subtract-only, no halving (`impls.ml:135`,
    `PicklesStepStatementDiff` §1) — and §16 shows both wrong readings diverge here.
  * **`xi_correct`** (`:1010-1013`) — the fr-sponge's own squeeze, `lowest_128_bits`-decomposed,
    against the statement's `xi`.
  * **`Boolean.all [xi_correct; b_correct; combined_inner_product_correct; plonk_checks_passed]`**
    (`:1141-1147`), each leg a REAL `Field.equal` gadget (`d·inv = 1 − bit`, `d·bit = 0`, `bit² =
    bit`), and the `should_verify` mux `verified && finalized || not should_verify`
    (`step_main.ml:121`, asserted at `:522`) closing on `= 1`. -/

/-- `Shifted_value.Type1.Shift.create (module Fp)`: `c = 2^{255} + 1` (`shifted_value.ml:122-126`,
`Fp.size_in_bits = 255`). -/
def SHIFT_C : Nat := (2 ^ 255 + 1) % pN
/-- …and `scale = 1/2`, as the `Fp` representative. -/
def SHIFT_INV2 : Nat := (pN + 1) / 2
/-- `Shifted_value.Type1.of_field` — `(x − c)·½`. -/
def shiftT1 (x : Nat) : Nat := fMul (fSub x SHIFT_C) SHIFT_INV2
/-- `Shifted_value.Type1.to_field` — `t + t + c`, the map the circuit emits. -/
def unshiftT1 (t : Nat) : Nat := fAdd (fAdd t t) SHIFT_C
/-- `Shifted_value.Type2.of_field` — subtract-only, `x − 2^255`. The WRONG-KIND reading, carried so
§16's control is about the rule and not about a typo. -/
def shiftT2 (x : Nat) : Nat := fSub x (2 ^ 255 % pN)

/-- The wire R8 reads: every field a SOURCE OP, so the rung's program can also be run on bent inputs
(§16's red controls) without touching the assembly. -/
structure FinWire where
  /-- `r`, LIFTED (`scalar (Scalar_challenge.create r_actual)`). -/
  r : AOp
  /-- ⚑ `zetaw` — §8i's OWN cell (`vZW 0`), not a slot of this program. `step_verifier.ml:934` binds
  `zetaw` ONCE and both `sg_evals` (`:948`) and `b_correct` (`:1124`) read that binding; recomputing
  `ω·ζ` here would be a second variable with the same value and no tie between them. -/
  zetaw : AOp
  /-- `challenge_poly ζ` — R5's `vAcc bRounds`. -/
  bZeta : AOp
  /-- R5's `combined_inner_product` output. -/
  cipActual : AOp
  /-- R6's `Plonk_checks.checked` `perm` scalar. -/
  permActual : AOp
  /-- the LIFTED bulletproof challenges `u₀..u_{rounds−1}`. -/
  u : Nat → AOp
  /-- the fr-sponge's first squeeze (R7 segment B). -/
  xiSqueeze : AOp
  cipShift : AOp
  bShift : AOp
  permShift : AOp
  xiStmt : AOp
  /-- `should_verify` — a STATEMENT bool (`step_main.ml:36-37`), not a witness. -/
  shouldVerify : AOp
  /-- ⚑⚑ **`verified`** (`step_main.ml:121`) — since §19 this is `equal_g lhs rhs`'s own output cell
  (`bpEq`), i.e. `check_bulletproof`'s returned `` `Success `` boolean, and NOT an `AOp.wit`. That is
  the whole point of emitting `rhs`: a free witness that R8's assert forces to 1 constrains nothing,
  while this one is a function of `(q, c, δ, b, u, G, z₁, z₂)`. ⚠ Three of those eight are still the
  prover's, so this is a WIRING and not a refusal — §17(e) re-runs and is unchanged. -/
  verified : AOp

/-- What R8 bakes in, plus the witnesses its own rows CHECK. -/
structure FinCfg where
  rounds : Nat
  shiftC : Nat
  /-- `lowest_128_bits`' discarded high part. -/
  hiXi : Nat
  /-- per `Field.equal` gadget: the witnessed inverse and the result bit. -/
  eqInv : List Nat
  eqBit : List Nat
  deriving Repr, Inhabited

structure FinSlots where
  zetaw : Nat
  bwZeta : Nat
  bActual : Nat
  cipUsed : Nat
  bUsed : Nat
  permUsed : Nat
  xiActual : Nat
  /-- ⚑ `lowest_128_bits`' HIGH part, as a program slot, so §5b's `assert_128_bits` chain can be
  wired to the very cell the decomposition row reads. Without that chain this witness is free and
  `xiActual` is whatever the prover wants (§12c). -/
  xiHi : Nat
  xc : Nat
  bc : Nat
  cc : Nat
  pc : Nat
  finalized : Nat
  out : Nat
  deriving Repr, Inhabited

/-- **The finalize program.** -/
def finBuild (W : FinWire) (C : FinCfg) : AM FinSlots := do
  let zero ← eLit 0
  let one ← eLit 1
  let shiftC ← eLit C.shiftC
  let two128 ← eLit (2 ^ 128 % pN)
  let r ← em W.r
  -- ── b_correct's SECOND leg (`:1124-1128`) ─────────────────────────────────────────────────
  -- ⚑ `zetaw` is READ, not recomputed: §8i owns `Field.mul domain#generator plonk.zeta` (`:934`)
  -- because `sg_evals` needs it too, and upstream binds it once for both. ⚑ …and ζ ITSELF left this
  -- program with it: `challenge_poly plonk.zeta` (`:1124`) is R5's `vAcc bRounds`, which `bZeta`
  -- already aliases, so R8 had no other use for it and a slot that aliases a variable nothing reads
  -- is not kept for shape.
  let zetaw ← em W.zetaw
  let zws ← (List.range C.rounds).foldlM (fun acc _ => do
      let y ← eMul (acc.getLastD zetaw) (acc.getLastD zetaw); pure (acc ++ [y])) [zetaw]
  let bw ← (List.range C.rounds).foldlM (fun acc k => do
      let u ← em (W.u k)
      let t ← eMul u (zws.getD (C.rounds - 1 - k) 0)
      let f ← eAdd one t
      eMul acc f) one
  let bz ← em W.bZeta
  let rbw ← eMul r bw
  let bAct ← eAdd bz rbw
  -- ── the THREE Type1/Fp unshifts ───────────────────────────────────────────────────────────
  let unshift : Nat → AM Nat := fun t => do let tt ← eAdd t t; eAdd tt shiftC
  let cipUsed ← unshift (← em W.cipShift)
  let bUsed ← unshift (← em W.bShift)
  let permUsed ← unshift (← em W.permShift)
  -- ── xi_actual = lowest_128_bits(squeeze) ──────────────────────────────────────────────────
  let sq ← em W.xiSqueeze
  let hi ← eWit C.hiXi
  let hiHigh ← eMul hi two128
  let xiAct ← eSub sq hiHigh
  let xiStmt ← em W.xiStmt
  -- ── `Field.equal`, the real gadget: `d·inv = 1 − bit`, `d·bit = 0`, `bit² = bit`. ─────────
  let mkEq : Nat → Nat → Nat → AM Nat := fun i x y => do
    let d ← eSub x y
    let iv ← eWit (C.eqInv.getD i 0)
    let bb ← eWit (C.eqBit.getD i 0)
    let bb2 ← eMul bb bb
    let _ ← eEq bb2 bb
    let p ← eMul d iv
    let q ← eSub one bb
    let _ ← eEq p q
    let sZ ← eMul d bb
    let _ ← eEq sZ zero
    pure bb
  let cipAct ← em W.cipActual
  let permAct ← em W.permActual
  let xc ← mkEq 0 xiAct xiStmt
  let bc ← mkEq 1 bUsed bAct
  let cc ← mkEq 2 cipUsed cipAct
  let pc ← mkEq 3 permUsed permAct
  -- ── `Boolean.all` and the `should_verify` mux, asserted ───────────────────────────────────
  let f1 ← eMul xc bc
  let f2 ← eMul f1 cc
  let fin ← eMul f2 pc
  let ver ← em W.verified
  let ver2 ← eMul ver ver
  let _ ← eEq ver2 ver
  let sv ← em W.shouldVerify
  let sv2 ← eMul sv sv
  let _ ← eEq sv2 sv
  let vf ← eMul ver fin
  let svf ← eMul sv vf
  let nsv ← eSub one sv
  let out ← eAdd svf nsv
  let _ ← eEq out one
  pure { zetaw := zetaw, bwZeta := bw, bActual := bAct, cipUsed := cipUsed, bUsed := bUsed
       , permUsed := permUsed, xiActual := xiAct, xiHi := hi, xc := xc, bc := bc, cc := cc, pc := pc
       , finalized := fin, out := out }

structure FinProg where
  prog : Array AOp
  slots : FinSlots
  deriving Repr, Inhabited

def finProgOf (W : FinWire) (C : FinCfg) : FinProg :=
  let r := (finBuild W C).run #[]
  { prog := r.2, slots := r.1 }

/-- The circuit variables EXPOSED as the public output — `pubWords` of them, drawn from every
sub-circuit so a public tie reaches all five. ⚑ The FIRST FOUR are the statement's deferred values;
R8's `Boolean.all` assert is what makes them a claim the circuit refuses to lie about. -/
def exposedVars (s : StepShape) : List PVar :=
  ([ vCipShift s, vBShift s, vPermShift s, vXiStmt s, vShouldVerify s, vBranch s, hmDigestVar s
   -- ⚑ the STEP statement's own `messages_for_next_step_proof` (`step_main.ml:572-575`), segment
   -- D's squeeze. `hmDigestVar` above is the WRAP statement's (`:83-86`), segment C's — two
   -- different digests of two different hashes, and both are public.
   , hmOutDigestVar s
   , vAcc s s.bRounds, vCa s s.cipEvals, vZ s s.bRounds
   , vSt s (tBlocks s) 0, vSt s (tBlocks s) 1, vSt s (tBlocks s) 2
   , mpx s (pSum s (s.msmTerms - 2)), mpy s (pSum s (s.msmTerms - 2))
   -- ⚑ §19: `q = p_prime + lr_prod`, NOT `qSum (ipaRounds−1)`. The exposed word is the point
   -- `Scalar_challenge.endo q c` actually reads, so `combined_inner_product` reaches the public
   -- vector through the curve side as well as through R8's `Field.equal`.
   , ipx s (qPrime s), ipy s (qPrime s) ]
   ++ (List.range s.chals).map (fun c => vN s c s.emsRows)
   -- ⚑ `0 .. bRounds−1`, NOT `0 .. bRounds`: `vAcc bRounds` and `vZ bRounds` are already the head
   -- entries, and at `shapeStep`'s 67 words the inclusive range made TWO of Step's public words
   -- carry the same circuit variable (measured 2026-08-02; the smoke shape's 12-word `take` cut
   -- before the collision, so the distinctness pin never saw it — §12 now pins BOTH shapes).
   ++ (List.range s.bRounds).map (fun k => vAcc s k)
   ++ (List.range s.bRounds).map (fun k => vZ s k)
   ++ (List.range (tBlocks s + 1)).map (fun b => vSt s b 0)).take s.pubWords

/-- **R5b's rows**: every public word tied to a computed circuit variable, two per `Generic` row
(`w₀ = w₁` in each half). Every one of `pubWords` public words is READ here — exactly what
`placeChecked`'s `inertPublicWord` refusal demands. -/
def closingRows (s : StepShape) : List SRow :=
  let ev := exposedVars s
  (List.range ((s.pubWords + 1) / 2)).map (fun r =>
    if 2 * r + 1 < s.pubWords then
      genericRow (some (ev.getD (2*r) (xv 0))) (some (.external (2*r))) none
                 (some (ev.getD (2*r+1) (xv 0))) (some (.external (2*r+1))) none (cEq ++ cEq)
    else
      genericRow (some (ev.getD (2*r) (xv 0))) (some (.external (2*r))) none none none none
                 (cEq ++ cNil))

/-! ### R8's wire, environment and data. -/

/-- R6's `ft_eval0`, as a value. -/
def FtData.out (f : FtData) : Nat := f.vals.getD f.fp.slots.ftEval0 0

/-- The finalize program's slots start after the ft program's. -/
def baseFin (s : StepShape) (f : FtData) : Nat := baseFtS s + f.fp.prog.size

/-- The fr-sponge's FIRST squeeze — `xi_actual` (`step_verifier.ml:1007`) — lane 0 of the state the
segment's last permutation produced, the same convention R1 uses. -/
def frSqueezeVar (s : StepShape) : PVar := sgSt (baseSegB s) (nbB s) 2 (nbB s) 0
def frSqueezeVal (segB : SegData) (specB : SegSpec) : Nat :=
  (segB.states.getD specB.nb []).getD 0 0

/-- ⚑⚑ The fr-sponge's **SECOND** squeeze — `r_actual` (`step_verifier.ml:1008`) — and since the lazy
re-model it is **`state.(1)` OF THE SAME PERMUTATION**, not a second one. `squeeze_challenge` is
`lowest_128_bits (Sponge.squeeze …)` (`:186-187`) and the second `Sponge.squeeze` finds `Squeezed 1`
with `n ≠ rate`, so it takes the `else` branch and returns `state.(1)` free (`sponge.ml:319-321`).
ξ′ and r′ were TWO permutations apart here until 2026-08-03. -/
def frSqueeze2Var (s : StepShape) : PVar := sgSt (baseSegB s) (nbB s) 2 (nbB s) 1
def frSqueeze2Val (segB : SegData) (specB : SegSpec) : Nat :=
  (segB.states.getD specB.nb []).getD 1 0

/-- `b(ζω)` — the SECOND challenge polynomial, over the lifted bulletproof challenges. -/
def bwOf (s : StepShape) (d : SpongeData) : Nat :=
  let zetaw := fMul FT_OMEGA (liftOf s d s.zetaChal)
  let zws := (List.range s.bRounds).foldl
    (fun acc _ => let x := acc.getLastD 0; acc ++ [fMul x x]) [zetaw]
  (List.range s.bRounds).foldl
    (fun acc k => fMul acc (fAdd 1 (fMul (liftOf s d (s.uChal k)) (zws.getD (s.bRounds - 1 - k) 0)))) 1

/-- `b_actual = challenge_poly ζ + r · challenge_poly ζω` (`step_verifier.ml:1124-1128`), computed
DIRECTLY here so §16 can pin the emitted program's own slot against it. `rv` is §8g's DEFERRED r. -/
def bActualOf (s : StepShape) (d : SpongeData) (df : DefData) (rv : Nat) : Nat :=
  fAdd (df.accs.getLastD 0) (fMul rv (bwOf s d))

def finWireOf (s : StepShape) (f : FtData) : FinWire :=
  { r := .inp (vDLift s 1)
  , zetaw := .inp (vZW s 0)
  , bZeta := .inp (vAcc s s.bRounds)
  , cipActual := .inp (vCa s s.cipEvals)
  , permActual := .inp (aVarAt (baseFtS s) f.fp.prog f.fp.slots.perm)
  , u := fun k => .inp (vLift s (s.uChal k))
  , xiSqueeze := .inp (frSqueezeVar s)
  , cipShift := .inp (vCipShift s)
  , bShift := .inp (vBShift s)
  , permShift := .inp (vPermShift s)
  , xiStmt := .inp (vXiStmt s)
  , shouldVerify := .inp (vShouldVerify s)
  -- ⚑ §19: `check_bulletproof`'s own returned boolean.
  , verified := .inp (bpEq s) }

/-- Everything R8 needs, evaluated ONCE. -/
structure FinData where
  fp : FinProg
  vals : Array Nat
  bActual : Nat
  cipShift : Nat
  bShift : Nat
  permShift : Nat
  xiStmt : Nat
  xiHi : Nat
  deriving Repr, Inhabited

/-- R8's `.inp` lookup: the lifted challenges, §8g's deferred `r`, R5's two outputs, R6's `perm`
slot, R7's squeeze, and the four statement words — every one of them a variable another rung's rows
compute. -/
def finInputEnv (s : StepShape) (d : SpongeData) (f : FtData) (df : DefData)
    (segB : SegData) (specB : SegSpec) (rv ver : Nat) : VarEnv :=
  let sqv := frSqueezeVal segB specB
  let permA := f.vals.getD f.fp.slots.perm 0
  [ (vDLift s 1, (rv : Int))
  -- ⚑ §8i's `zetaw` cell (`step_verifier.ml:934`), which `sg_evals` and `b_correct` share.
  , (vZW s 0, (df.zws.getD 0 0 : Int))
  , (vAcc s s.bRounds, (df.accs.getLastD 0 : Int))
  , (vCa s s.cipEvals, (df.ca.getLastD 0 : Int))
  , (aVarAt (baseFtS s) f.fp.prog f.fp.slots.perm, (permA : Int))
  , (frSqueezeVar s, (sqv : Int))
  , (vCipShift s, (shiftT1 (df.ca.getLastD 0) : Int))
  , (vBShift s, (shiftT1 (bActualOf s d df rv) : Int))
  , (vPermShift s, (shiftT1 permA : Int))
  , (vXiStmt s, ((sqv % 2 ^ 128 : Nat) : Int))
  , (vShouldVerify s, 1)
  -- ⚑ §19's `equal_g` output — a cell §19's rows define, read here rather than witnessed.
  , (bpEq s, (ver : Int)) ]
  ++ (List.range s.bRounds).map (fun k => (vLift s (s.uChal k), (liftOf s d (s.uChal k) : Int)))

/-- The HONEST config: `lowest_128_bits`' high part, and — because every `Field.equal` leg holds —
`bit = 1`, `inv = 0` in all four gadgets. ⚑ `verified` LEFT this structure with §19: it is no longer
a witness the config picks but a wire the program reads. §16 re-runs this at bent inputs, where the
honest witness is `bit = 0` and the assert FAILS. -/
def finCfgOf (s : StepShape) (hi : Nat) : FinCfg :=
  { rounds := s.bRounds, shiftC := SHIFT_C, hiXi := hi
  , eqInv := List.replicate 4 0, eqBit := List.replicate 4 1 }

def runFin (s : StepShape) (d : SpongeData) (f : FtData) (df : DefData)
    (segB : SegData) (specB : SegSpec) (rv ver : Nat) : FinData :=
  let sqv := frSqueezeVal segB specB
  let permA := f.vals.getD f.fp.slots.perm 0
  let p := finProgOf (finWireOf s f) (finCfgOf s (sqv / 2 ^ 128))
  let lk := envLookupAt (envIndex (finInputEnv s d f df segB specB rv ver))
  { fp := p, vals := aEval lk p.prog, bActual := bActualOf s d df rv
  , cipShift := shiftT1 (df.ca.getLastD 0), bShift := shiftT1 (bActualOf s d df rv)
  , permShift := shiftT1 permA, xiStmt := sqv % 2 ^ 128, xiHi := sqv / 2 ^ 128 }

/-- **R8's rows**: the compiled finalize program, the TWO `assert_128_bits` chains its
`lowest_128_bits` owes (`util.ml:98-99` — the high part unconditionally, the low part because
`Opt_sponge.squeeze_challenge` passes `~constrain_low_bits:true`), and its σ-only probes.

⚑ THE HIGH CHAIN IS THE SOUNDNESS-BEARING ONE. `hi` is an `AOp.wit`: no row defines it, so before
this chain the decomposition `xiActual = squeeze − 2¹²⁸·hi` was ONE equation in TWO unknowns and the
prover could hand `xi_correct` any 128-bit ξ he liked — the fold's own multiplier, since §8g's chain
0 lifts that same statement word. §12c exhibits that witness: R8's program ACCEPTS it (`out = 1`)
and the high chain REFUSES it. The chains' sources are the program's OWN cells, not fresh copies. -/
def finRows (s : StepShape) (f : FtData) (fn : FinData) (wired : Bool) : List SRow :=
  let base := baseFin s f
  let V := aVarAt base fn.fp.prog
  aRows base fn.fp.prog
  ++ rangeRows s (RNG_FIN_HI s) (V fn.fp.slots.xiHi)
       (fn.vals.getD fn.fp.slots.xiHi 0) wired
  ++ rangeRows s (RNG_FIN_LO s) (V fn.fp.slots.xiActual)
       (fn.vals.getD fn.fp.slots.xiActual 0) wired
  ++ [ probeRow wired (V fn.fp.slots.finalized) (V fn.fp.slots.bActual)
     , probeRow wired (V fn.fp.slots.cipUsed) (V fn.fp.slots.xiActual)
     , probeRow wired (V fn.fp.slots.permUsed) (V fn.fp.slots.bUsed) ]

/-! ## §8g — the DEFERRED CHALLENGES: the fr-sponge FEEDS the fold.

`step_verifier.ml:1006-1013`. Before this section the C8 fold multiplied by two R1 transcript
challenges and the fr-sponge's squeeze reached nothing but `xi_correct` — the fold was CHECKED
against the squeeze and not FED by it (the module header's simplification #10). Here the two
multipliers are `to_field_checked` chains whose sources are the fr-sponge's own two squeezes:

  * **chain 0 — ξ.** Source is the STATEMENT's ξ word (`vXiStmt`), which is already a
    `Challenge.t`, so the chain's tie is `Field.Assert.equal n scalar` and not a decomposition. R8's
    `xi_correct` is what binds that word to the fr-sponge's FIRST squeeze — upstream's own two-step
    (`let xi_correct = … xi_actual … in let xi = scalar xi`), so a prover cannot move the fold
    without failing the assert.
  * **chain 1 — r.** Source is the fr-sponge's SECOND squeeze, decomposed by `lowest_128_bits`.
    Upstream carries no statement word for `r` at all: `scalar (Scalar_challenge.create r_actual)`.

⚑ THE RUNG CONSEQUENCE, stated plainly. Chain 0's source is a statement word and its rows ride with
R5, so ξ is derived at EVERY rung from r5 up. Chain 1's source is an R7 variable, so its rows ride
with R7: at r5/r6 (sub-circuits strictly below the fr-sponge) the fold's `r` is a free witness, and
at r7/r8 it is the squeeze's lift. That is the same ladder position `vEz 3` (R6's `ft_eval0`) and
the four statement words already occupy, and §15 pins which rung binds which. -/

/-- The two deferred prechallenges and their discarded high parts. -/
structure DefcData where
  /-- `lowest_128_bits` of the fr-sponge's first (ξ) and second (r) squeeze. -/
  pre : List Nat
  /-- the high parts. Chain `0`'s is unused — its source is already a `Challenge.t`. -/
  hi : List Nat
  deriving Repr, Inhabited

def runDefc (segB : SegData) (specB : SegSpec) : DefcData :=
  let sq1 := frSqueezeVal segB specB
  let sq2 := frSqueeze2Val segB specB
  { pre := [sq1 % 2 ^ 128, sq2 % 2 ^ 128], hi := [0, sq2 / 2 ^ 128] }

/-- Chain `c`'s LIFTED value — the multiplier itself. -/
def DefcData.lift (dc : DefcData) (s : StepShape) (c : Nat) : Nat :=
  liftVal s (dc.pre.getD c 0)

/-- **§8g's rows** for chain `c`, over the source `src`. -/
def defcRows (s : StepShape) (dc : DefcData) (c : Nat) (src : PVar) (split : Bool)
    (wired : Bool) : List SRow :=
  tfcRows s (defcVars s c) src split (dc.pre.getD c 0) wired

/-- Chain 0 (ξ), from the statement word — rides with R5. -/
def xiDefRows (s : StepShape) (dc : DefcData) (wired : Bool) : List SRow :=
  defcRows s dc 0 (vXiStmt s) false wired
/-- Chain 1 (r), from the fr-sponge's second squeeze — rides with R7, and so does the
`assert_128_bits` of ITS high part (`squeeze_scalar`'s `~constrain_low_bits:false` asserts the high
part only; `step_verifier.ml:190-192`). -/
def rDefRows (s : StepShape) (dc : DefcData) (wired : Bool) : List SRow :=
  defcRows s dc 1 (frSqueeze2Var s) true wired
  ++ rangeRows s (s.chals + 1) (vDHi s 1) (dc.hi.getD 1 0) wired

/-! ## ⚑⚑ §19 — `group_map`, `p_prime`'s `uc`, `rhs`, `equal_g`: THE ROWS.

The variable region and the honest label are at §19's variable block above. This is the emission.

## `group_map` — `Snarky_group_map.Checked.wrap`, read at `checked_map.ml:20-55`

    let x1, x2, x3 = potential_xs x in
    let y1, b1 = sqrt_flagged (y_squared ~x:x1) and … and … in
    Boolean.Assert.any [ b1; b2; b3 ] ;
    let x1_is_first = (b1 :> Field.t)
    and x2_is_first = (Boolean.((not b1) && b2) :> Field.t)
    and x3_is_first = (Boolean.((not b1) && (not b2) && b3) :> Field.t) in
    ( Field.((x1_is_first * x1) + (x2_is_first * x2) + (x3_is_first * x3)) , …same for y… )

with `sqrt_flagged x = (sqrt_exn (Field.if_ is_square ~then_:x ~else_:(Field.scale x m)), is_square)`
(`:22-36`) and `sqrt_exn y = exists; assert_square y x` (`:11-15`). ⚑ **This is an indicator
dot-product, not a `Field.if_` chain**, and it is NOT ~13 rows.

⚑ **`y_squared` folds `a·x` away.** `step_verifier.ml:231-236` passes
`fun ~x -> (x*x*x) + constant Inner_curve.Params.a * x + constant Inner_curve.Params.b`, and Pallas
has `a = 0` (`step_main_inputs.ml:115`), so `Field.mul` on a constant-zero operand is `Field.scale …
0` and emits nothing. `b = 5`.

⚠ **WHERE THIS EMISSION IS AN UPPER BOUND AND SAYS SO.** Snarky's `assert_r1cs` takes arbitrary
linear combinations as operands, so `(t2 + fu) * t2` is ONE constraint with a two-term left operand.
This region materialises every linear combination that feeds a multiplication as its own `Generic`
half. So the emitted half-count is **≥** Snarky's constraint count, never fewer, and the difference is
in the cheapest rows in the file. The ladders — which are 96% of §19 — are chunk-for-chunk exact.

## The four ladders, the two adds, and `equal_g`

`sfTermRows` at §19's slots, i.e. the same emitter `Common.ft_comm`'s eight ladders run through, at
`~num_bits:Field.size_in_bits = 255` → `FTC_CHUNKS = 51` five-bit chunks each. Then
`Ops.add_fast (G, b_u)`, `Ops.add_fast (z_1_g_plus_b_u, z2_h)`, and `equal_g` as two `Field.equal`
gadgets plus `Boolean.all`.

⚑ **`H` is a pin and `G`, `z₁`, `z₂` are not.** `Inner_curve.constant (Lazy.force Generators.h)`
(`:336`) is one `Generic` row over a MEASURED constant; `G` arrives already `assert_on_curve`d and
absorbed by segment D (§8e′); `z₁`/`z₂` arrive as nothing at all, and their cells have no defining
row, which is the whole content of §17. -/

/-- ⚑ **`group_map`'s 43 cells, evaluated in emission order.** Slot names are in the row emitter
below; the last two entries of each five-slot dot-product are `u`'s coordinates.

⚠ `db_i` is `(1 − m)·b_i·q_i` and `sel_i = m·q_i + db_i`, which is `Field.if_ b ~then_:q
~else_:(m·q)` with the `(1−m)` folded into the multiplication's coefficient — one half rather than
two, and exactly the same value. -/
def gmVals (t : Nat) : List Nat :=
  let t2 := fMul t t
  let tf := fAdd t2 BW_FU
  let ai := fMul tf t2
  let alpha := Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fInv ai
  let t4 := fMul t2 t2
  let ta := fMul t4 alpha
  let x1 := fSub BW_SQ3_MU2 (fMul BW_SQ3 ta)
  let x2 := fSub (fSub 0 BW_U) x1
  let ti := fMul alpha tf
  let tf2 := fMul tf tf
  let tb := fMul tf2 ti
  let x3 := fSub BW_U (fMul BW_INV3U2 tb)
  let xs := [x1, x2, x3]
  let per := xs.flatMap (fun x =>
    let sq := fMul x x
    let qv := fAdd (fMul sq x) PALLAS_B
    let b := if fIsSquare qv then 1 else 0
    let db := fMul (fSub 1 FP_NONRES) (fMul b qv)
    let sel := fAdd (fMul FP_NONRES qv) db
    [sq, qv, b, db, sel, fSqrt sel])
  let bv : Nat → Nat := fun i => per.getD (6 * i + 2) 0
  let yv : Nat → Nat := fun i => per.getD (6 * i + 5) 0
  let p12 := fSub (fAdd 1 (fMul (bv 0) (bv 1))) (fAdd (bv 0) (bv 1))
  let f2 := fSub (bv 1) (fMul (bv 0) (bv 1))
  let f3 := fMul p12 (bv 2)
  let fs := [bv 0, f2, f3]
  let dot : (Nat → Nat) → List Nat := fun g =>
    let m := (List.range 3).map (fun i => fMul (fs.getD i 0) (g i))
    let s12 := fAdd (m.getD 0 0) (m.getD 1 0)
    m ++ [s12, fAdd s12 (m.getD 2 0)]
  [t2, tf, ai, alpha, t4, ta, x1, x2, ti, tf2, tb, x3] ++ per ++ [p12, f2, f3]
    ++ dot (fun i => xs.getD i 0) ++ dot yv

/-- `group_map`'s OUTPUT, off the emitted cells rather than restated. -/
def gmOut (t : Nat) : Nat × Nat := ((gmVals t).getD 37 0, (gmVals t).getD 42 0)

/-- ⚑ Everything §19 evaluates. `uc` is here AND reaches `runIpa`, because `q` depends on it. -/
structure BpData where
  /-- `group_map`'s 43 cells at the transcript's own squeeze. -/
  gm : List Nat
  /-- the four `scale_fast2` ladders: `uc`, `b_u`, `z_1·(G + b_u)`, `z_2·H`. -/
  terms : List FtcTerm
  /-- their four scalars, in the same order — `s_odd` is the parity of these. -/
  scals : List Nat
  /-- `lhs`, so `equal_g`'s difference is read off the assembly rather than recomputed. -/
  lhs : Nat × Nat
  /-- `Ops.add_fast challenge_polynomial_commitment b_u` (`:333`). -/
  gbCells : List Nat
  /-- `Ops.add_fast z_1_g_plus_b_u z2_h` (`:337`). -/
  rhsCells : List Nat
  deriving Repr, Inhabited

def BpData.u (v : BpData) : Nat × Nat := (v.gm.getD 37 0, v.gm.getD 42 0)
def BpData.term (v : BpData) (k : Nat) : FtcTerm := v.terms.getD k default
def BpData.gb (v : BpData) : Nat × Nat := (v.gbCells.getD 4 0, v.gbCells.getD 5 0)
def BpData.rhs (v : BpData) : Nat × Nat := (v.rhsCells.getD 4 0, v.rhsCells.getD 5 0)
/-- ⚑ **`equal_g lhs rhs`, as a value** — R8's `verified`. It is COMPUTED from the two points and
never assumed: a `G` that does not solve the opening leaves this `0`, and `Boolean.all` then refuses
the witness. -/
def BpData.ver (v : BpData) : Nat := if v.lhs == v.rhs then 1 else 0

/-- ⚑ **`uc` alone**, which `runIpa` needs before the rest of §19 can be evaluated: `q` depends on
`uc`, `lhs` depends on `q`, and `rhs`/`equal_g` depend on `lhs`. So the chain is
`group_map → uc → q → lhs → rhs → equal_g` and it is a chain, not a cycle. -/
def runUc (t cip : Nat) : FtcTerm := ftcScaleTerm (gmOut t) cip

/-- Jacobian → affine, so a SOLVED `G` can be handed to a ladder and to segment D as a commitment. -/
def jAffOf (P : Nat × Nat × Nat) : Nat × Nat :=
  let zi := Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fInv P.2.2
  let z2 := fMul zi zi
  (fMul P.1 z2, fMul P.2.1 (fMul z2 zi))

/-- ⚑⚑ **`challenge_polynomial_commitment`, SOLVED — and this is the finding, not a shortcut.**
`G := z₁⁻¹·(lhs − z₂·H) − b·u` (`KimchiStepMainField.bpSolveG`). The assembly has no IPA opening to
take a real `G` from, and §17 measures that it does not need one: `G`, `z₁` and `z₂` are free
witnesses, so for ANY `lhs` this identity produces a `G` that closes `equal_g`, at one scalar-field
inverse and three scalar multiplications. The honest witness this file emits is therefore the SAME
object a substituting prover would compute — which is why `equal_g` refuses no on-curve substitution
and why the emitted rows change no verdict.

⚠ It is also why `G` is data-dependent now: it is a function of `lhs`, hence of the transcript, hence
of every commitment the fold consumed. A bent commitment moves `lhs`, moves the solved `G`, and moves
segment D's public word — which is §17(d), now true of the emitted witness rather than of an
exhibit. -/
def solveG (u : Nat × Nat) (lhs : Nat × Nat) (bAdv z1 z2 : Nat) : Nat × Nat :=
  jAffOf (bpSolveG u GENERATORS_H lhs bAdv z1 z2)

/-- **§19, evaluated.** `t` is the FULL squeeze, `cip`/`bAdv` the two statement words, `z1`/`z2` the
two free witnesses, `G` the previous proof's `challenge_polynomial_commitment`. -/
def runBp (t cip bAdv z1 z2 : Nat) (G lhs : Nat × Nat) : BpData :=
  let gm := gmVals t
  let u : Nat × Nat := (gm.getD 37 0, gm.getD 42 0)
  let t0 := ftcScaleTerm u cip
  let t1 := ftcScaleTerm u bAdv
  let gbc := completeAddWitness G.1 G.2 t1.res.1 t1.res.2
  let gb : Nat × Nat := (gbc.getD 4 0, gbc.getD 5 0)
  let t2 := ftcScaleTerm gb z1
  let t3 := ftcScaleTerm GENERATORS_H z2
  let rc := completeAddWitness t2.res.1 t2.res.2 t3.res.1 t3.res.2
  { gm := gm, terms := [t0, t1, t2, t3], scals := [cip, bAdv, z1, z2]
  , lhs := lhs, gbCells := gbc, rhsCells := rc }

/-- Ladder `k`'s base VARIABLES: `u` twice, then `G + b_u`, then the pinned `H`. -/
def bpBaseVar (s : StepShape) (k : Nat) : PVar × PVar :=
  if k ≤ 1 then (vUx s, vUy s)
  else if k == 2 then (bpGbX s, bpGbY s)
  else (bpHx s, bpHy s)

/-- Ladder `k`'s scalar SOURCE — the cell `Field.Assert.equal (2·s_div_2 + s_odd) s` reads. ⚑ Two of
the four are statement words the rest of the assembly already binds; two are cells no row defines. -/
def bpScalV (s : StepShape) (k : Nat) : PVar :=
  if k == 0 then vCipShift s else if k == 1 then vBShift s
  else if k == 2 then bpZ1 s else bpZ2 s

def bpSlots (s : StepShape) (k : Nat) : SfSlots :=
  let g := bpBaseVar s k
  { baseX := g.1, baseY := g.2
  , accX := bpAccX s k, accY := bpAccY s k, n := bpN s k
  , top := bpTop s k, negY := bpNegY s k, hmX := bpHmX s k, hmY := bpHmY s k
  , dX := bpDX s k, dY := bpDY s k, mX := bpMX s k, mY := bpMY s k
  , resX := bpResX s k, resY := bpResY s k, odd := bpOdd s k }

/-- **`group_map`'s rows.** Every half is one Snarky operation; the comment on each names it. -/
def gmRows (s : StepShape) (wired : Bool) : List SRow :=
  let V := vGm s
  let hs : List (List (Option PVar) × List Int) :=
    -- `potential_xs` (`bw19.ml:78-99`)
    [ ([some (uSqueezeVar s), some (uSqueezeVar s), some (V 0)], cMul)          -- t2 = t·t
    , ([some (V 0), some (V 1), none], [1, -1, 0, 0, (BW_FU : Int)])            -- tf = t2 + fu
    , ([some (V 1), some (V 0), some (V 2)], cMul)                              -- ai = tf·t2
    , ([some (V 3), some (V 2), none], [0, 0, 0, 1, -1])                        -- alpha·ai = 1
    , ([some (V 0), some (V 0), some (V 4)], cMul)                              -- t4 = t2·t2
    , ([some (V 4), some (V 3), some (V 5)], cMul)                              -- ta = t4·alpha
    , ([some (V 5), some (V 6), none], [-(BW_SQ3 : Int), -1, 0, 0, (BW_SQ3_MU2 : Int)])
    , ([some (V 6), some (V 7), none], [-1, -1, 0, 0, -(BW_U : Int)])           -- x2 = −u − x1
    , ([some (V 3), some (V 1), some (V 8)], cMul)                              -- ti = alpha·tf
    , ([some (V 1), some (V 1), some (V 9)], cMul)                              -- tf2 = tf·tf
    , ([some (V 9), some (V 8), some (V 10)], cMul)                             -- tb = tf2·ti
    , ([some (V 10), some (V 11), none], [-(BW_INV3U2 : Int), -1, 0, 0, (BW_U : Int)]) ]
    -- `y_squared` + `sqrt_flagged`, per candidate
    ++ (List.range 3).flatMap (fun i =>
        let x := V (if i == 0 then 6 else if i == 1 then 7 else 11)
        let o := 12 + 6 * i
        [ ([some x, some x, some (V o)], cMul)                                   -- sq = x·x
        , ([some (V o), some x, some (V (o+1))], [0, 0, -1, 1, (PALLAS_B : Int)]) -- q = sq·x + b
        , KimchiGadgets.boolHalf (V (o+2))                                        -- b² = b
        , ([some (V (o+2)), some (V (o+1)), some (V (o+3))],
           [0, 0, -1, ((pN + 1 - FP_NONRES : Nat) : Int), 0])                     -- db = (1−m)·b·q
        , ([some (V (o+1)), some (V (o+3)), some (V (o+4))],
           [(FP_NONRES : Int), 1, -1, 0, 0])                                      -- sel = m·q + db
        , ([some (V (o+5)), some (V (o+5)), some (V (o+4))], cMul) ])              -- y² = sel
    -- `Boolean.Assert.any [b1;b2;b3]` = `(1−b1)(1−b2)(1−b3) = 0`, and the two derived indicators.
    ++ [ ([some (V 14), some (V 20), some (V 30)], [-1, -1, -1, 1, 1])            -- p12 = (1−b1)(1−b2)
       , ([some (V 30), some (V 26), none], [1, 0, 0, -1, 0])                     -- p12·(1−b3) = 0
       , ([some (V 20), some (V 14), some (V 31)], [1, 0, -1, -1, 0])             -- f2 = b2 − b1·b2
       , ([some (V 30), some (V 26), some (V 32)], cMul) ]                        -- f3 = p12·b3
    -- the two indicator dot-products.
    ++ (List.range 2).flatMap (fun c =>
        let o := 33 + 5 * c
        let xs : Nat → Nat := fun i =>
          if c == 0 then (if i == 0 then 6 else if i == 1 then 7 else 11) else 17 + 6 * i
        [ ([some (V 14), some (V (xs 0)), some (V o)], cMul)
        , ([some (V 31), some (V (xs 1)), some (V (o+1))], cMul)
        , ([some (V 32), some (V (xs 2)), some (V (o+2))], cMul)
        , ([some (V o), some (V (o+1)), some (V (o+3))], cAdd)
        , ([some (V (o+3)), some (V (o+2)), some (V (o+4))], cAdd) ])
  packHalves hs ++ [ probeRow wired (vUx s) (vUy s) ]

/-- **`equal_g lhs rhs`** (`step_verifier.ml:69-73`): `Field.equal` per coordinate — the real gadget
`d·inv = 1 − bit`, `d·bit = 0`, `bit² = bit` — then `Boolean.all` of the two, which for a two-list is
one `&&`. ⚑ Its output is R8's `verified`. -/
def bpEqRows (s : StepShape) : List SRow :=
  let lx := ipx s (qLhsOut s)
  let ly := ipy s (qLhsOut s)
  packHalves ((List.range 2).flatMap (fun i =>
    let l := if i == 0 then lx else ly
    let r := if i == 0 then bpRhsX s else bpRhsY s
    [ ([some l, some r, some (bpEqD s i)], cSub)
    , ([some (bpEqBit s i), some (bpEqBit s i), some (bpEqSq s i)], cMul)
    , ([some (bpEqSq s i), some (bpEqBit s i), none], cEq)
    , ([some (bpEqD s i), some (bpEqInv s i), some (bpEqP s i)], cMul)
    , ([some (bpEqP s i), some (bpEqBit s i), none], [1, 1, 0, 0, -1])
    , ([some (bpEqD s i), some (bpEqBit s i), some (bpEqZ s i)], cMul)
    , ([some (bpEqZ s i), none, none], cConst 0) ])
    ++ [ ([some (bpEqBit s 0), some (bpEqBit s 1), some (bpEq s)], cMul) ])

/-- **§19's rows.** -/
def bpRows (s : StepShape) (v : BpData) (wired : Bool) : List SRow :=
  gmRows s wired
  ++ [ baseConstRow (bpHx s) (bpHy s) GENERATORS_H ]
  -- `Shifted_value.Type2`'s split, once per ladder, plus `let n_acc = ref Field.zero` (`:158`).
  -- ⚑ Ladder 0's `s_odd` IS `vCipBit`, whose `b² = b` `cipRows` already emits (it is absorbed at
  -- every rung, and this one is emitted only at `r9_opening`). Emitting it twice would be one
  -- redundant `Generic` half, so the booleanity here is the three ladders that do not have one.
  ++ packHalves ((List.range N_SF).flatMap (fun k =>
       [ ([some (bpScalV s k), some (bpDiv2 s k), some (bpOdd s k)], cSplit 1) ]
       ++ (if k == 0 then [] else [([some (bpOdd s k), some (bpOdd s k), some (bpOdd s k)], cMul)])
       ++ [ ([some (bpN s k 0), none, none], cConst 0) ]))
  -- ladder 1 (`b_u`) must precede the `G + b_u` add that ladder 2's base is.
  ++ sfTermRows (bpSlots s 0) (v.term 0) wired
  ++ sfTermRows (bpSlots s 1) (v.term 1) wired
  ++ [ caRow (vGx s, vGy s) (bpResX s 1, bpResY s 1) (bpGbX s, bpGbY s) v.gbCells
     , probeRow wired (bpGbX s) (bpGbY s) ]
  ++ sfTermRows (bpSlots s 2) (v.term 2) wired
  ++ sfTermRows (bpSlots s 3) (v.term 3) wired
  ++ [ caRow (bpResX s 2, bpResY s 2) (bpResX s 3, bpResY s 3) (bpRhsX s, bpRhsY s) v.rhsCells
     , probeRow wired (bpRhsX s) (bpRhsY s) ]
  ++ bpEqRows s

/-- §19's environment. -/
def bpEnv (s : StepShape) (v : BpData) : VarEnv :=
  (List.range N_GM).map (fun i => (vGm s i, (v.gm.getD i 0 : Int)))
  ++ [ (bpHx s, (GENERATORS_H.1 : Int)), (bpHy s, (GENERATORS_H.2 : Int))
     , (bpGbX s, (v.gb.1 : Int)), (bpGbY s, (v.gb.2 : Int))
     , (bpRhsX s, (v.rhs.1 : Int)), (bpRhsY s, (v.rhs.2 : Int))
     , (bpZ1 s, (v.scals.getD 2 0 : Int)), (bpZ2 s, (v.scals.getD 3 0 : Int)) ]
  ++ (List.range N_SF).flatMap (fun k =>
      let tm := v.term k
      let hx := (tm.td.accs.getLastD (0, 0)).1
      let hy := (tm.td.accs.getLastD (0, 0)).2
      let dx := fSub hx tm.hMg.1
      let dy := fSub hy tm.hMg.2
      let odd := v.scals.getD k 0 % 2
      (List.range (FTC_CHUNKS + 1)).flatMap (fun j =>
        let a := tm.td.accs.getD (5 * j) (0, 0)
        [ (bpAccX s k j, (a.1 : Int)), (bpAccY s k j, (a.2 : Int)) ])
      ++ (List.range FTC_CHUNKS).map (fun j =>
          (bpN s k j, (tm.td.ns.getD (5 * j) 0 : Int)))
      ++ [ (bpTop s k, (tm.bits.headD 0 : Int))
         , (bpNegY s k, (fSub 0 tm.td.T.2 : Int))
         , (bpHmX s k, (tm.hMg.1 : Int)), (bpHmY s k, (tm.hMg.2 : Int))
         , (bpDX s k, (dx : Int)), (bpDY s k, (dy : Int))
         , (bpMX s k, (fMul odd dx : Int)), (bpMY s k, (fMul odd dy : Int))
         , (bpResX s k, (tm.res.1 : Int)), (bpResY s k, (tm.res.2 : Int))
         , (bpOdd s k, (odd : Int))
         , (bpDiv2 s k, ((v.scals.getD k 0 / 2 : Nat) : Int)) ])
  -- ⚑ `equal_g`'s witness, read off the assembly: `d = lhs − rhs` per coordinate. It is ZERO for the
  -- honest (solved) `G`, and a `G` that does not solve leaves `bit = 0` — which R8's `Boolean.all`
  -- then refuses. Nothing here assumes it closes; the value is computed.
  ++ (List.range 2).flatMap (fun i =>
      let l := if i == 0 then v.lhs.1 else v.lhs.2
      let r := if i == 0 then v.rhs.1 else v.rhs.2
      let d : Nat := fSub l r
      let bit : Nat := if d == 0 then 1 else 0
      let iv : Nat := if d == 0 then 0 else Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fInv d
      [ (bpEqD s i, (d : Int)), (bpEqInv s i, (iv : Int)), (bpEqBit s i, (bit : Int))
      , (bpEqSq s i, (bit : Int)), (bpEqP s i, (fMul d iv : Int))
      , (bpEqZ s i, (fMul d bit : Int)) ])
  ++ [ (bpEq s, ((if v.lhs == v.rhs then 1 else 0 : Nat) : Int)) ]

/-! ## §9 — the whole assembly: rows, environment, placement, witness. -/

/-- Everything the schedule and the environment read, evaluated ONCE. -/
structure StepData where
  sh : StepShape
  sp : SpongeData
  msm : MsmData
  ipa : IpaData
  ft : FtData
  /-- §6b's two scalar cells, read off R6's program. -/
  ftw : FtcWire
  /-- ⚑ `Common.ft_comm` — the MSM whose output is R4 round `FTC_ROUND`'s base. -/
  ftc : FtcData
  defc : DefcData
  df : DefData
  fin : FinData
  segA : SegData
  segB : SegData
  segC : SegData
  /-- ⚑ Segment D — the OUTER `hash_messages_for_next_step_proof` (`step_main.ml:525-566`). -/
  segD : SegData
  /-- ⚑ §19 — `group_map`, the four `scale_fast2`s, `rhs` and `equal_g`. -/
  bp : BpData
  /-- ⚑ `challenge_polynomial_commitment`, SOLVED off `lhs` (`solveG`). Segment D absorbs it and
  §19's ladder 2 consumes it, so it is data and not a constant. -/
  gXY : Nat × Nat
  specA : SegSpec
  specB : SegSpec
  specC : SegSpec
  specD : SegSpec
  deriving Inhabited

/-! ### ⚑ §2c's VALUE side — the packed Wrap statement, word by word. -/

/-- ⚠ Wrap statement word 11's VALUE. `vStmtWrapMsgs` has no in-circuit source — and neither does
upstream's (`step_main.ml:364-366` `exists`-es it) — so this is a deterministic fixture. -/
def STMT_WRAPMSG_VAL : Nat := (41 + 7000019 * 11 + 13 * 121) % pN
/-- ⚑ **Wrap statement word 39's VALUE — UPSTREAM'S OWN DUMMY, not a fixture (2026-08-03).** It was
`(53 + 7000019·39 + 13·1521) % 2¹²⁸`, an arbitrary `Challenge`-width number. Read at source: the
lookup `Opt`'s inner scalar-challenge dummy is `Sc.create lookup_parameters.zero.var.challenge`
(`spec.ml:123-128`'s `None` arm packs `dummy2`), `verify_one` is called with
`~lookup_parameters:{ zero = { var = { challenge = Field.zero; … } } }`
(`step_main.ml:90-95`) and `Common.Lookup_parameters.tick_zero` sets the same
(`common.ml:105-118`). **So the value is `0`**, and it stays a `Challenge`-width word trivially.

⚠ This pins the VALUE and nothing else. Word 39 still owns exactly one cell — its own 26-chunk
`var_base_mul` counter — and no row WRITES it, because this assembly models no lookup sub-circuit
that would derive it. Upstream derives it nowhere either (`lookup_verification_enabled = false`,
`step_verifier.ml:12`; `use = Opt.Flag.No`, `wrap_main.ml:83-86`), so the residue is a shared one;
what changed is that the number is now upstream's rather than invented. -/
def STMT_LOOKUP_VAL : Nat := 0

/-- ⚑ **`Spec.pack … (Wrap.Statement.In_circuit.to_data statement)`**, evaluated — the forty scalars
`multiscale_known` multiplies the SRS Lagrange commitments by, in `to_data`'s own order (§2c).

⚠ **EVERY ENTRY IS THE VALUE `circuitEnv` ASSIGNS TO `stmtVar i`, and it has to be.** The chunk rows
constrain `n_final = Σ bits` and `n_final` IS `stmtVar i`, so a scalar that disagreed with the
statement word's own cell would emit a witness the prover rejects. The two are written once each and
§21 pins them equal term by term.

⚑ **THE TRANSCRIPT ENTERS ONLY THROUGH `ch`, AND ONLY AT THE WORDS THAT ARE PRECHALLENGES.** That
is what makes §21's red control statable: bending `ch` at a challenge some word CARRIES moves the
vector; bending it at one no word carries — at the committed shape, `u`, the fifteen `bullet_reduce`
prechallenges past ζ are words 13–28, so what is left over is `c`, ξ and r — moves NOTHING. Under
the retired round-robin every challenge moved forty terms. -/
def msmScalars (s : StepShape) (ch : Nat → Nat) (sd : Nat) (ft : FtData) (fin : FinData)
    (segC : SegData) (i : Nat) : Nat :=
  if i == 0 then fin.cipShift
  else if i == 1 then fin.bShift
  else if i < 4 then ft.vals.getD FT_SLOT_ZETAN 0
  else if i == 4 then fin.permShift
  else if i == 5 then ch s.betaChal
  else if i == 6 then ch s.gammaChal
  else if i == 7 then ch s.alphaChal
  else if i == 8 then ch s.zetaChal
  else if i == 9 then fin.xiStmt
  -- ⚑ §22: `digestBeforeEvalsVal`, the transcript's own ζ-squeeze lane 1. `ch` cannot supply it —
  -- `chalOf` is lane 0 masked to `chalBits`, and this word is a full 255-bit `Digest`.
  else if i == 10 then sd
  else if i == 11 then STMT_WRAPMSG_VAL
  else if i == 12 then (segC.states.getLastD []).getD 0 0
  else if i < 29 then ch (s.uChal (i - 13))
  else if i == 29 then branchPacked
  else if i < 39 then 0
  else if i == 39 then STMT_LOOKUP_VAL
  else ch (i % s.chals)

/-- ⚑ THE DEPENDENCY ORDER, and why the fr-sponge now runs BEFORE the fold. Since §8g the C8 fold's
own multipliers are `to_field_checked` of the fr-sponge's two squeezes, so segment B is evaluated
first and `runDef` is fed from it. Nothing the fr-sponge absorbs depends on `combined_inner_product`
(segment B absorbs the digest of segment A, `ft_eval1`, the two public-poly evaluations and the 43
columns — R6's and R5's fixtures), so the order is a chain and not a cycle. -/
def mkStepWith (s : StepShape) (bs : List (Nat × Nat)) : StepData :=
  -- ⚑⚑ **PASS 1 — the transcript through ζ.** `absorb sponge Scalar advice.combined_inner_product`
  -- (`step_verifier.ml:256`) comes AFTER `let zeta = sample_scalar ()` (`:568`), so blocks 0 …
  -- `sqBlock zetaChal` do not depend on it and β/γ/α/ζ are already exact in this pass. §12i pins
  -- that as an EQUALITY over the four, which is the machine-checked form of "upstream has no cycle".
  let sp0 := runSponge s bs (0, 0)
  let ft0 := runFt s sp0
  -- ⚑ segment A reads `prev_challenges` and NOT the transcript, so nothing below depends on a
  -- squeeze taken after ζ. That is the other half of why two passes suffice.
  let specA := optSpec s
  let segA := runSeg specA
  let dg : PVar × Nat :=
    (sgSt (baseSegA s) (nbA s) 1 specA.blocks 0,
     (segA.states.getLastD []).getD 0 0)
  -- ⚑ §22 — THE SEED. `step_main.ml:41-46`: the sponge `finalize_other_proof` is handed already
  -- carries `proof_state.sponge_digest_before_evaluations`. Read off THIS pass's transcript rather
  -- than shared with pass 2 — the two agree (ζ's squeeze precedes the `cip` absorb) and §22 pins
  -- that as an equality instead of assuming it here.
  let specB0 := frSpec s (digestBeforeEvalsVar s, digestBeforeEvalsVal s sp0) dg ft0.out
  let defc0 := runDefc (runSeg specB0) specB0
  -- ⚑ the SHIFTED value, because that is what `:257-259` unwraps and absorbs
  -- (`Shifted_value.Type2.Shifted_value x -> x`) and it is exactly `vCipShift`, the statement word
  -- R8's `combined_inner_product_correct` ties back to this same Horner output.
  -- ⚑ §8i's four `E_c` ladders ride in `runDef` and read `prevChalVal` — a witness vector, NOT the
  -- transcript — so PASS 1 computes the same `E_c` PASS 2 does and the fold stays a chain. (ζ is
  -- identical across the two passes: `cip` is absorbed after ζ is squeezed, §12i.)
  -- ⚑ …and `combine`'s mux rides in it too, at `MASK_BITS` — the SAME two `branch_data` bits the
  -- opt-sponge and segment C take, so the transcript's `cip` word is the masked fold from pass 1 on.
  let cipV := shiftT1 ((runDef s sp0 ft0.out (defc0.lift s 0) (defc0.lift s 1)
                          FT_OMEGA prevChalVal MASK_BITS).ca.getLastD 0)
  -- **PASS 2 — the real transcript**, carrying `(combined_inner_product, its `Boolean.var`)` — and
  -- ⚑ since 2026-08-03 the second item is the PARITY of the first, because it is §19 ladder 0's
  -- `s_odd` and the split row `2·s_div_2 + s_odd = cip` forces it. Not a constant, not a witness.
  let sp := runSponge s bs (cipV, cipV % 2)
  -- ⚑ R6 next: `ft_eval0` is the `ft` column R5's `combined_inner_product` folds — and since §6b
  -- its `perm` / `ζ^n` slots are also `Common.ft_comm`'s scalars, so R6 runs BEFORE the fold. That
  -- is a chain and not a cycle: `runFt` reads only β/γ/α/ζ, and fold round
  -- `FTC_ROUND`'s base is `ft_comm`'s output rather than a supplied commitment.
  let ft := runFt s sp
  let ftw := ftcWireOf s ft
  let ftc := runFtc s ftw
  -- ⚑⚑ §19, FIRST HALF. `u = group_map (squeeze_field)` and `uc = scale_fast2 u cip` come BEFORE the
  -- fold's tail, because `q = p_prime + lr_prod` (`:316-320`) contains `uc` and `lhs` reads `q`.
  -- The chain is `group_map → uc → q → lhs → G → rhs → equal_g`; every arrow is a dependency and
  -- none of them closes a cycle, which is why two passes still suffice.
  let tSq := uSqueezeVal s sp
  let uc := runUc tSq cipV
  let ipa := runIpa s bs sp ftc.out uc.res
  let ftv := ft.out
  let specB := frSpec s (digestBeforeEvalsVar s, digestBeforeEvalsVal s sp) dg ftv
  let segB := runSeg specB
  -- ⚑ §8g: ξ and r, squeezed from the fr-sponge and lifted, are the fold's multipliers.
  let defc := runDefc segB specB
  let df := runDef s sp ftv (defc.lift s 0) (defc.lift s 1) FT_OMEGA prevChalVal MASK_BITS
  -- ⚑ §19, SECOND HALF. `advice.b` is R8's statement word, and its VALUE is `bActualOf` — available
  -- without running the whole finalize program, which is what keeps `G` off a cycle.
  let bSh := shiftT1 (bActualOf s sp df (defc.lift s 1))
  let lhsPt : Nat × Nat := (ipa.lhsAdd.getD 4 0, ipa.lhsAdd.getD 5 0)
  let gA := solveG (gmOut tSq) lhsPt bSh BP_Z1_VAL BP_Z2_VAL
  let bp := runBp tSq cipV bSh BP_Z1_VAL BP_Z2_VAL gA lhsPt
  let ver : Nat := bp.ver
  let specC := hmSpec s ipa
  -- ⚑ segment D copies `sponge_after_index` (`step_verifier.ml:1164`), so it does not depend on
  -- segment C's own trajectory past the index prefix — the two hashes are SIBLINGS off one copy,
  -- not a chain.
  let specD := hmOutSpec s sp gA
  let fin := runFin s sp ft df segB specB (defc.lift s 1) ver
  let segC := runSeg specC
  -- ⚑⚑ **R3 IS LAST IN THE CHAIN SINCE §21**, because its scalars ARE the Wrap statement's words and
  -- three of them (`combined_inner_product`, `b`, `perm` in `Shifted_value.Type1` form, plus ξ) are
  -- R8's own cells and one is segment C's squeeze. Nothing above depends on `msm`: segment C absorbs
  -- `sg_old` (§12k's correction), not the x_hat sum, and R8 does not read it. The chain is
  -- `sponge → ft → fold → fr-sponge → finalize → segment C → x_hat`, still no cycle.
  let msm := runMsm s bs (msmScalars s (chalOf s sp) (digestBeforeEvalsVal s sp) ft fin segC)
  { sh := s, sp := sp, msm := msm, ipa := ipa, ft := ft, ftw := ftw, ftc := ftc
  , defc := defc, df := df, bp := bp, gXY := gA
  , fin := fin
  , segA := segA, segB := segB, segC := segC, segD := runSeg specD
  , specA := specA, specB := specB, specC := specC, specD := specD }

/-- The assembly on the HONEST supplied commitments — block 539508's own. -/
def mkStep (s : StepShape) : StepData := mkStepWith s (stepBases s)

/-- **R7's rows** — the three sponge segments of §8e, then §8g's `r` chain over the fr-sponge's
second squeeze. -/
def absRows (t : StepData) (wired : Bool) : List SRow :=
  let s := t.sh
  segRows (baseSegA s) t.specA t.segA wired
  ++ segRows (baseSegB s) t.specB t.segB wired
  ++ idxConstRows s
  ++ segRows (baseSegC s) t.specC t.segC wired
  -- ⚑ segment D — the OUTER hash, a `Sponge.copy` off segment C's index prefix, so it emits NO
  -- init pin row and its block-0 state lanes are segment C's own variables.
  ++ segRows (baseSegD s) t.specD t.segD wired
  ++ idxDigestRows s wired
  ++ rDefRows s t.defc wired

/-- **THE ROW SCHEDULE**, in the order `verify_one` runs it. -/
def stepRows (t : StepData) (wired : Bool) : List SRow :=
  let s := t.sh
  transcriptRows s t.sp wired
  ++ endoConstRow s
  ++ (List.range s.chals).flatMap (challengeRows s t.sp wired)
  ++ msmRows s t.msm wired
  ++ ftcRows s t.ftw t.ftc wired
  ++ ipaRows s t.ipa wired
  ++ deferredRows s wired
  ++ sgEvalRows s FT_OMEGA wired
  ++ branchRows s wired
  ++ xiDefRows s t.defc wired
  ++ cipRows s wired
  ++ closingRows s
  ++ ftRows s t.ft wired
  ++ absRows t wired
  ++ finRows s t.ft t.fin wired
  ++ bpRows s t.bp wired

/-- The CIRCUIT's variable → value assignment (public words are added by `stepEnv`). -/
def circuitEnv (t : StepData) : VarEnv :=
  let s := t.sh
  -- ⚑⚑ **ONE WALK PER REGION, NOT ONE PER ENTRY.** This environment is 17 743 entries at the
  -- committed shape and every entry used to name a variable through the shape, i.e. through the
  -- region-base chain and the `spLay` under it — MEASURED after the `SrcOrd` hoist at **1 ms** for
  -- one such name at the top of the chain (`baseFtc shapeStep`). The `…At` forms (see `mpxAt`'s
  -- note) take the base as an argument; these seven bindings are the whole of the fix, and the
  -- emitted pairs are the same by delta.
  let tb := tBlocks s
  let nst := nStOf tb
  let bm := baseMsm s
  let bsn := baseSN s
  let bi := baseIpa s
  let bq := baseQN s
  let bo := baseOnC s
  (List.range (tb + 1)).flatMap (fun b =>
    let st := t.sp.states.getD b []
    (List.range 3).map (fun j => (vSt s b j, (st.getD j 0 : Int))))
  -- ⚑ `vPost` is indexed by BLOCK since the lazy re-model — the same index the trajectory carries,
  -- because a block no longer corresponds to an absorb SOURCE.
  ++ (List.range tb).flatMap (fun b =>
      let pre := t.sp.states.getD b []
      let ms := t.sp.msgs.getD b []
      (List.range 2).map (fun j =>
        (vPostAt nst b j, (((pre.getD j 0 + ms.getD j 0) % pN : Nat) : Int))))
  -- ⚑ the ONE pad cell, at the zero `transcriptRows` pins it to. There is no `vMsg` region any more:
  -- every absorbed word is a variable some sub-circuit reads.
  ++ (if (tPadCell s).isSome then [(vTPad s, (0 : Int))] else [])
  ++ (List.range s.chals).flatMap (fun c =>
      let accs := emsAccs s (chalOf s t.sp c)
      (List.range (s.emsRows + 1)).flatMap (fun k =>
        let a := accs.getD k (0, 2, 2)
        [ (vN s c k, (a.1 : Int)), (vA s c k, (a.2.1 : Int)), (vB s c k, (a.2.2 : Int)) ])
      ++ [ (vHi s c, (hiOf s t.sp c : Int))
         , (vLiftT s c, (liftTOf s t.sp c : Int)), (vLift s c, (liftOf s t.sp c : Int)) ])
  ++ [ (vEndoR s, (ENDO_R : Int)) ]
  -- §5b: the `assert_128_bits hi` chains — one per SPLIT source, R2's `chals` and §8g's `r`…
  ++ (List.range s.chals).flatMap (fun c => rngEnv s c (hiOf s t.sp c))
  ++ rngEnv s (s.chals + 1) (t.defc.hi.getD 1 0)
  -- …and R8's own `lowest_128_bits`, BOTH parts (`~constrain_low_bits:true`), over the compiled
  -- finalize program's OWN cells rather than over a parallel computation of them.
  ++ rngEnv s (RNG_FIN_HI s) (t.fin.vals.getD t.fin.fp.slots.xiHi 0)
  ++ rngEnv s (RNG_FIN_LO s) (t.fin.vals.getD t.fin.fp.slots.xiActual 0)
  -- …and §8h's `Branch_data.typ` `~assert_16_bits` chain, ONE `EndoMulScalar` row wide.
  ++ rngEnvN s RNG_DOMLOG2_ROWS (RNG_DOMLOG2 s) BRANCH_DOMAIN_LOG2
  -- §8g: the two DEFERRED challenge chains (ξ from the statement word, r from the fr-sponge's
  -- second squeeze), each a full `to_field_checked` accumulator trace.
  ++ (List.range N_DEFC).flatMap (fun c =>
      let v := t.defc.pre.getD c 0
      let accs := emsAccs s v
      (List.range (s.emsRows + 1)).flatMap (fun k =>
        let a := accs.getD k (0, 2, 2)
        [ (vDN s c k, (a.1 : Int)), (vDA s c k, (a.2.1 : Int)), (vDB s c k, (a.2.2 : Int)) ])
      ++ [ (vDHi s c, (t.defc.hi.getD c 0 : Int))
         , (vDLiftT s c, (liftTVal s v : Int)), (vDLift s c, (liftVal s v : Int)) ])
  -- ⚑ Over `msmLive` since §21: a constant-scalar word owns no base, no `acc₀` and no counter cell
  -- here because it owns no ROW there.
  ++ (msmLive s).flatMap (fun i =>
      let td := t.msm.terms.getD i default
      [ (mpxAt bm (pT s i), (td.T.1 : Int)), (mpyAt bm (pT s i), (td.T.2 : Int)) ]
      ++ (List.range (msmChunksAt i + 1)).flatMap (fun j =>
          let a := td.accs.getD (5 * j) (0, 0)
          [ (mpxAt bm (pAcc s i j), (a.1 : Int)), (mpyAt bm (pAcc s i j), (a.2 : Int)) ])
      ++ (List.range (msmChunksAt i)).map (fun j =>
          (vSNAt s bsn i j, (td.ns.getD (5 * j) 0 : Int))))
  ++ (List.range ((msmLive s).length - 1)).flatMap (fun a =>
      let p := t.msm.sums.getD a (0, 0)
      [ (mpxAt bm (pSum s a), (p.1 : Int)), (mpyAt bm (pSum s a), (p.2 : Int)) ])
  ++ (List.range s.ipaRounds).flatMap (fun r =>
      let T := t.ipa.bases.getD r (0, 0)
      [ (ipxAt bi (qT s r), (T.1 : Int)), (ipyAt bi (qT s r), (T.2 : Int)) ]
      ++ (List.range (s.ipaBlocks + 1)).flatMap (fun e =>
          let a := (t.ipa.accs.getD r []).getD e (0, 0)
          [ (ipxAt bi (qAcc s r e), (a.1 : Int)), (ipyAt bi (qAcc s r e), (a.2 : Int)) ])
      ++ (List.range s.ipaBlocks).map (fun e =>
          (vQNAt s bq r e, ((t.ipa.ns.getD r []).getD e 0 : Int)))
      -- §7's seed: `φ(t)`'s x and the `p = t + φ(t)` intermediate `acc₀ = p + p` doubles.
      ++ [ (vQEndoAt s bq r, ((endoQ T).1 : Int))
         , (ipxAt bi (qP s r), ((endoP T).1 : Int)), (ipyAt bi (qP s r), ((endoP T).2 : Int)) ])
  ++ (List.range s.ipaRounds).flatMap (fun a =>
      let p := t.ipa.sums.getD a (0, 0)
      [ (ipxAt bi (qSum s a), (p.1 : Int)), (ipyAt bi (qSum s a), (p.2 : Int)) ])
  -- ⚑ `sg_old[0]` (the fold's `~init`), `delta`, and `check_bulletproof`'s `endo q c + delta` tail.
  -- ⚑⚑ `q` IS `qPrimePt` SINCE §19 — `p_prime + lr_prod`, with the `uc` term in it. ⚠ This block
  -- read `sums.getLast` for one build after §19 landed and the `qPrime` cells had no entry at all,
  -- so the `Ops.add_fast` output was 0 and the endo seed was taken at the OLD point: the honest
  -- r4_ipa witness was REJECTED by the prover (`rest of division by vanishing polynomial`) while
  -- every σ-class and row-count pin stayed green. A row schedule and a witness environment are two
  -- places, and only the prover reads both.
  ++ (let g := Dregg2.Bridge.MinaStepPrevCommitments.SG_OLD0_XY
      let dl := Dregg2.Bridge.MinaStepPrevCommitments.DELTA_XY
      let q := t.ipa.qPrimePt
      [ (ipxAt bi (qInit s), (g.1 : Int)), (ipyAt bi (qInit s), (g.2 : Int))
      , (ipxAt bi (qDel s), (dl.1 : Int)), (ipyAt bi (qDel s), (dl.2 : Int))
      , (ipxAt bi (qPrime s), (q.1 : Int)), (ipyAt bi (qPrime s), (q.2 : Int))
      , (vLhsEndoAt s bq, ((endoQ q).1 : Int))
      , (ipxAt bi (qLhsP s), ((endoP q).1 : Int)), (ipyAt bi (qLhsP s), ((endoP q).2 : Int))
      , (ipxAt bi (qLhsOut s), (t.ipa.lhsAdd.getD 4 0 : Int))
      , (ipyAt bi (qLhsOut s), (t.ipa.lhsAdd.getD 5 0 : Int)) ]
      ++ (List.range (s.ipaBlocks + 1)).flatMap (fun e =>
          let a := t.ipa.lhsAccs.getD e (0, 0)
          [ (ipxAt bi (qLhsAcc s e), (a.1 : Int)), (ipyAt bi (qLhsAcc s e), (a.2 : Int)) ])
      ++ (List.range s.ipaBlocks).map (fun e =>
          (vLhsNAt s bq e, (t.ipa.lhsNs.getD e 0 : Int))))
  -- §7b: `assert_on_curve`'s two intermediates per ABSORBED commitment — the fold's bases, `t_comm`'s
  -- chunks, and since the R1 interleaving `sg_old[0]` and `delta`.
  ++ (List.range (nOnC s)).flatMap (fun k =>
      let l := (absRoundList s).length
      let x := if k < l then (t.ipa.bases.getD ((absRoundList s).getD k 0) (0, 0)).1
               else if k < l + tCommN s then (ftcTc (k - l)).1
               else if k == l + tCommN s then Dregg2.Bridge.MinaStepPrevCommitments.SG_OLD0_XY.1
               else if k == l + tCommN s + 1 then Dregg2.Bridge.MinaStepPrevCommitments.DELTA_XY.1
               else t.gXY.1
      [ (vOcX2At bo k, (fMul x x : Int)), (vOcX3At bo k, (fMul (fMul x x) x : Int)) ])
  -- ⚑ §6b: `Common.ft_comm`'s MSM — the eight `scale_fast2` ladders, `t_comm`'s absorbed
  -- coordinates, the `Ops.add_fast` chain and `Shifted_value.Type2`'s two split pairs.
  ++ (List.range (ftcTerms s)).flatMap (fun k =>
      let tm := t.ftc.terms.getD k default
      let hx := (tm.td.accs.getLastD (0, 0)).1
      let hy := (tm.td.accs.getLastD (0, 0)).2
      let od := ftcScalVal t.ftw (ftcScalOf k) % 2
      let dx := fSub hx tm.hMg.1
      let dy := fSub hy tm.hMg.2
      (List.range (FTC_CHUNKS + 1)).flatMap (fun j =>
        let a := tm.td.accs.getD (5 * j) (0, 0)
        [ (ftcAccX s k j, (a.1 : Int)), (ftcAccY s k j, (a.2 : Int)) ])
      ++ (List.range FTC_CHUNKS).map (fun j =>
          (ftcN s k j, (tm.td.ns.getD (5 * j) 0 : Int)))
      ++ [ (ftcTop s k, (tm.bits.headD 0 : Int))
         , (ftcNegY s k, (fSub 0 tm.td.T.2 : Int))
         , (ftcHmX s k, (tm.hMg.1 : Int)), (ftcHmY s k, (tm.hMg.2 : Int))
         , (ftcDX s k, (dx : Int)), (ftcDY s k, (dy : Int))
         , (ftcMX s k, (fMul od dx : Int)), (ftcMY s k, (fMul od dy : Int))
         , (ftcResX s k, (tm.res.1 : Int)), (ftcResY s k, (tm.res.2 : Int)) ])
  ++ (List.range (tCommN s)).flatMap (fun i =>
      [ (vTcX s i, ((ftcTc i).1 : Int)), (vTcY s i, ((ftcTc i).2 : Int)) ])
  ++ (List.range (tCommN s)).flatMap (fun a =>
      let p := t.ftc.adds.getD a (0, 0)
      [ (ftcAddX s a, (p.1 : Int)), (ftcAddY s a, (p.2 : Int)) ])
  ++ [ (ftcNegQ s, (fSub 0 (t.ftc.terms.getD (tCommN s) default).res.2 : Int)) ]
  ++ (List.range N_FTC_SCAL).flatMap (fun c =>
      let v := ftcScalVal t.ftw c
      [ (ftcDiv2 s c, ((v / 2 : Nat) : Int)), (ftcOdd s c, ((v % 2 : Nat) : Int)) ])
  ++ (List.range (s.bRounds + 1)).map (fun k => (vZ s k, (t.df.zs.getD k 0 : Int)))
  ++ (List.range s.bRounds).map (fun k => (vFac s k, (t.df.facs.getD k 0 : Int)))
  ++ (List.range (s.bRounds + 1)).map (fun k => (vAcc s k, (t.df.accs.getD k 0 : Int)))
  -- ⚑ §8i: `domain#generator`, `zetaw` and its squaring ladder, and the FOUR `f_c` ladders over
  -- `prev_challenges`. The ladders' OUTPUTS are `vEz 0/1` / `vEw 0/1`, which the `cipEvals` block
  -- below already places out of `t.df.ez` / `t.df.ew` — so they appear once, not twice.
  ++ [ (vOmegaC s, (FT_OMEGA : Int)) ]
  ++ (List.range s.bRounds).map (fun k => (vZW s k, (t.df.zws.getD k 0 : Int)))
  ++ (List.range N_EC).flatMap (fun l =>
      (List.range s.bRounds).map (fun k =>
        (vEcFac s l k, ((t.df.ecFacs.getD l []).getD k 0 : Int)))
      ++ (List.range (s.bRounds - 1)).map (fun k =>
        (vEcAcc s l (k + 1), ((t.df.ecAccs.getD l []).getD (k + 1) 0 : Int))))
  ++ (List.range s.cipEvals).flatMap (fun k =>
      [ (vEz s k, (t.df.ez.getD k 0 : Int)), (vEw s k, (t.df.ew.getD k 0 : Int))
      , (vDk s k, (t.df.dk.getD k 0 : Int)), (vCk s k, (t.df.ck.getD k 0 : Int))
      , (vTk s k, (t.df.tk.getD k 0 : Int)) ])
  ++ (List.range (s.cipEvals + 1)).map (fun i => (vCa s i, (t.df.ca.getD i 0 : Int)))
  -- ⚑ `combine`'s `Opt.Maybe` mux cells (`common.ml:270-271`), one triple per masked prefix slot.
  -- The `keep` VARIABLE is NOT here — it is `vMask j`, owned by §8h below.
  ++ (List.range N_CIP_MASKED).flatMap (fun j =>
      [ (vCs s j, (t.df.csk.getD j 0 : Int)), (vCd s j, (t.df.cdk.getD j 0 : Int))
      , (vCp s j, (t.df.cpk.getD j 0 : Int)) ])
  -- R6: the compiled ft program's slots.
  ++ aEnvOf (baseFtS s) t.ft.fp.prog t.ft.vals
  -- R7: the three sponge segments, `sponge_after_index`'s own pinned commitments and its squeeze,
  -- and the two APP-STATE words that are all that is left of the old fixture prefix (§3c).
  ++ (List.range N_HM_APP).map (fun i => (vHm s i, (hmVal i : Int)))
  -- ⚑ the OUTER hash's own witnesses: its app-state words and `G`, the previous proof's
  -- `opening.challenge_polynomial_commitment` (`step_main.ml:534`).
  ++ (List.range N_HM_APP).map (fun i => (vHmO s i, (hmOVal i : Int)))
  ++ [ (vGx s, (t.gXY.1 : Int)), (vGy s, (t.gXY.2 : Int)) ]
  -- ⚑ §19: `group_map`'s cells, the four `scale_fast2` ladders, `H`, `G + b_u`, `rhs`, the two free
  -- response scalars and `equal_g`'s gadget.
  ++ bpEnv s t.bp
  -- ⚑ `prev_challenges` — segments A and C absorb these SAME variables (`step_verifier.ml:956`,
  -- `step_main.ml:80`).
  ++ (List.range (2 * s.bRounds)).map (fun i => (vPrevChal s i, (prevChalVal i : Int)))
  ++ (idxOwn s).flatMap (fun k =>
      [ (vIdxX s k, (idxVal k 0 : Int)), (vIdxY s k, (idxVal k 1 : Int)) ])
  -- ⚑ `vIdxD` is NOT bound here: since 2026-08-03 its three ids ARE segment C's block-28 state
  -- lanes, which `segEnv` already binds. Binding them again would be a second binding of one id.
  ++ segEnv (baseSegA s) t.specA t.segA
  ++ segEnv (baseSegB s) t.specB t.segB
  ++ segEnv (baseSegC s) t.specC t.segC
  ++ segEnv (baseSegD s) t.specD t.segD
  -- R8: the four STATEMENT words and the compiled finalize program's slots.
  ++ [ (vCipShift s, (t.fin.cipShift : Int)), (vBShift s, (t.fin.bShift : Int))
     , (vPermShift s, (t.fin.permShift : Int)), (vXiStmt s, (t.fin.xiStmt : Int))
     -- §8h: `branch_data` and the two `proofs_verified_mask` bits it packs.
     -- ⚑ NO `vCipBit` entry: it IS `bpOdd s 0`, which `bpEnv` binds to `cip % 2`. A second binding
     -- here would be a second value for one id.
     , (vShouldVerify s, 1)
     , (vBranch s, (branchPacked : Int)), (vDomLog2 s, (BRANCH_DOMAIN_LOG2 : Int))
     , (vMask s 0, (MASK_BITS.getD 0 0 : Int)), (vMask s 1, (MASK_BITS.getD 1 0 : Int))
     , (vMaskPack s, ((MASK_BITS.getD 0 0 + 2 * MASK_BITS.getD 1 0 : Nat) : Int))
     -- ⚑ §2c's sourceless statement words — TWO since §22, word 10 having become the transcript's
     -- own `digestBeforeEvalsVar`. Their ONLY consumer is the x_hat ladder, which is exactly what
     -- "no in-circuit source" means; the nine one-bit words get no entry because no row reads them.
     , (vStmtWrapMsgs s, (STMT_WRAPMSG_VAL : Int))
     , (vStmtLookup s, (STMT_LOOKUP_VAL : Int)) ]
  ++ aEnvOf (baseFin s t.ft) t.fin.fp.prog t.fin.vals

/-- The full environment: the circuit's variables, then the `pubWords` public words, whose values
are READ OUT of the circuit env at the exposed variables — so a public word and the variable the
closing row ties it to hold ONE value by construction, exactly as a copy class does. -/
def stepEnv (t : StepData) : VarEnv :=
  let ce := circuitEnv t
  let ix := envIndex ce
  ce ++ (List.range t.sh.pubWords).map (fun i =>
    ((.external i : PVar), envLookupAt ix ((exposedVars t.sh).getD i (xv 0))))

/-- The public vector the verifier is handed, in order. -/
def stepPublic (t : StepData) : List Int :=
  let ix := envIndex (circuitEnv t)
  (List.range t.sh.pubWords).map (fun i =>
    envLookupAt ix ((exposedVars t.sh).getD i (xv 0)))

def stepGates (rows : List SRow) : List PGate :=
  rows.map (fun r => { kind := r.kind, permVars := r.perm, coeffs := r.coeffs })

/-- The composed 15 × `(pubSize + nRows)` witness grid. The `pubSize` public rows carry the public
word at col 0 (`prover.rs:270`: the prover's public vector IS witness column 0, rows `0..n`); the
circuit rows start at `pubSize` (`compute_witness`, `transaction.rs:3854-3872`). Built with the
ROW-INDEXED front ends (`envIndex`/`gateVarWitnessAt`), which is what keeps the assembly linear
rather than quadratic in the row count. -/
def stepWitness (t : StepData) (pubSize : Nat) (rows : List SRow) : List (List Int) :=
  let ix := envIndex (stepEnv t)
  let n := rows.length
  compose 15 (pubSize + n)
    (((List.range pubSize).map (fun i => ((⟨i, 0⟩ : Cell), envLookupAt ix (.external i))))
     :: (rows.zip (List.range n)).map (fun ri =>
          gateVarWitnessAt ix (pubSize + ri.2)
            { kind := ri.1.kind, permVars := ri.1.perm, coeffs := ri.1.coeffs }
          ++ ri.1.advice.map (fun cv => ((⟨pubSize + ri.2, cv.1⟩ : Cell), cv.2))))

/-- Read circuit row `r` out of the ASSEMBLED column-major grid (all 15 columns). -/
def gridRow (w : List (List Int)) (r : Nat) : List Nat :=
  (List.range 15).map (fun c => (gridAt w ⟨r, c⟩).toNat)

/-- **THE FAIL-CLOSED PLACEMENT.** `placeChecked`, never `place`: `auxOverlapsPublic` /
`referenceInGap` / `inertPublicWord` REFUSE rather than reinterpret. A refusal yields the empty
placement, which every downstream `#guard` then fails loudly. -/
def placedOf (pubSize : Nat) (gs : List PGate) : List PlacedGate :=
  match placeChecked ⟨pubSize, AUX⟩ gs with
  | .ok p => p
  | .error _ => []

/-- Did the placement refuse, and why. -/
def refusalOf (pubSize : Nat) (gs : List PGate) : Option PlaceRefusal :=
  match placeChecked ⟨pubSize, AUX⟩ gs with
  | .ok _ => none
  | .error e => some e

/-! ## §10 — the RUNGS.

`Rung` names how far up the assembly a circuit reaches. Rungs 1–4 are placed at `pubSize = 0`
(their public output is not yet tied); rung 5 IS the closing rung and is placed at `pubSize =
pubWords` through `placeChecked`. Each rung is a superset of the one below, so a regression cannot
hide behind a smaller circuit. -/

inductive Rung where
  | transcript | challenges | msm | ipa | full | ftEval0 | absorb | finalize
  /-- ⚑ §19 — `group_map`, `p_prime`'s `uc`, `rhs`, `equal_g`, and the wire that makes `verified` a
  function of them instead of a witness. -/
  | opening
  deriving Repr, DecidableEq, Inhabited

def Rung.tag : Rung → String
  | .transcript => "r1_transcript" | .challenges => "r2_challenges" | .msm => "r3_msm"
  | .ipa => "r4_ipa" | .full => "r5_full" | .ftEval0 => "r6_ft_eval0"
  | .absorb => "r7_absorption" | .finalize => "r8_finalize" | .opening => "r9_opening"

/-- Rung `k`'s rows.

⚑ **EVERY sub-circuit's row-set function is REACHED FROM HERE.** `rungRows` is the ONLY entry point
the emit driver has, and a sub-circuit whose rows live in a function nobody calls proves nothing:
measured on 2026-08-01, `cipRows` was absent from this `match` while every probe of every proved r5
still passed, so the `combined_inner_product` Horner chain the commit subject named was in NO proved
circuit and `vCa cipEvals` reached the public tie as a FREE variable. §15 now pins each rung's length
as the sum of its own sub-lists AND pins `stepRows = rungRows .finalize`, so a row-set that drops out
of this function is a red, not a silence.

⚑⚑ **THE NINE SUB-LISTS USED TO BE BOUND WITH A `let` ABOVE THE `match`, AND LEAN IS STRICT.**
Every rung evaluated all fifteen row families and returned a prefix, so `r1_transcript` computed
`finRows`/`bpRows` and threw them away. MEASURED two independent ways: the emit driver's artifacts
land **68–69 min apart** at `shapeStep` and the gap does NOT grow with the rung, though the rungs go
803 → 10 823 rows (`EmitStepMainJson`'s header); and the wrap side's twin of this defect cost
`rungRows tWrap .key true` **16 min 55 s for 1 977 rows whose families cost 115 ms**
(`KimchiWrapProverChoice`'s header). The rungs below `.opening` now pay only their own prefix; the
closing rung genuinely wants all fifteen and is unchanged. -/
def rungOwn (t : StepData) (wired : Bool) : Rung → List SRow
  | .transcript => transcriptRows t.sh t.sp wired
  | .challenges => endoConstRow t.sh ++ (List.range t.sh.chals).flatMap (challengeRows t.sh t.sp wired)
  | .msm => msmRows t.sh t.msm wired ++ ftcRows t.sh t.ftw t.ftc wired
  | .ipa => ipaRows t.sh t.ipa wired
  | .full => deferredRows t.sh wired ++ sgEvalRows t.sh FT_OMEGA wired ++ branchRows t.sh wired
             ++ xiDefRows t.sh t.defc wired ++ cipRows t.sh wired ++ closingRows t.sh
  | .ftEval0 => ftRows t.sh t.ft wired
  | .absorb => absRows t wired
  | .finalize => finRows t.sh t.ft t.fin wired
  | .opening => bpRows t.sh t.bp wired

/-- The rungs at or below `k`, in schedule order. ⚑ "Each rung is a superset of the one below" is the
SHAPE of the definition now, rather than a fact about nine hand-written branches. -/
def rungsUpto : Rung → List Rung
  | .transcript => [.transcript]
  | .challenges => [.transcript, .challenges]
  | .msm        => [.transcript, .challenges, .msm]
  | .ipa        => [.transcript, .challenges, .msm, .ipa]
  | .full       => [.transcript, .challenges, .msm, .ipa, .full]
  | .ftEval0    => [.transcript, .challenges, .msm, .ipa, .full, .ftEval0]
  | .absorb     => [.transcript, .challenges, .msm, .ipa, .full, .ftEval0, .absorb]
  | .finalize   => [.transcript, .challenges, .msm, .ipa, .full, .ftEval0, .absorb, .finalize]
  | .opening    => [.transcript, .challenges, .msm, .ipa, .full, .ftEval0, .absorb, .finalize,
                    .opening]

/-- Rung `k`'s rows: the own-rows of every rung at or below it, concatenated in schedule order.

⚑ **THE EMITTED LIST IS THE SAME TERM IT ALWAYS WAS.** `foldl (· ++ ·) []` over a literal list is
left-nested exactly as `a ++ b ++ c` is, and `[] ++ a` reduces to `a` definitionally, so
`rungRows t .ipa wired` is `((a ++ b) ++ c) ++ d` on the nose — `rungRows_is_a_ladder` below is
`rfl`. What changed is that the `foldl` walks only the rungs `k` names. -/
def rungRows (t : StepData) (k : Rung) (wired : Bool) : List SRow :=
  (rungsUpto k).foldl (fun acc j => acc ++ rungOwn t wired j) []

/-- ⚑ **THE HOIST IS THE THING IT HOISTS.** Each rung is the rung below it plus its own row-set —
general over every `StepData` and every `wired`, by `rfl`, no shape instance and no evaluated guard.
§15's row-length pins are instances of this plus `List.length_append`. -/
theorem rungRows_is_a_ladder (t : StepData) (wired : Bool) :
    rungRows t .challenges wired = rungRows t .transcript wired ++ rungOwn t wired .challenges
    ∧ rungRows t .msm wired = rungRows t .challenges wired ++ rungOwn t wired .msm
    ∧ rungRows t .ipa wired = rungRows t .msm wired ++ rungOwn t wired .ipa
    ∧ rungRows t .full wired = rungRows t .ipa wired ++ rungOwn t wired .full
    ∧ rungRows t .ftEval0 wired = rungRows t .full wired ++ rungOwn t wired .ftEval0
    ∧ rungRows t .absorb wired = rungRows t .ftEval0 wired ++ rungOwn t wired .absorb
    ∧ rungRows t .finalize wired = rungRows t .absorb wired ++ rungOwn t wired .finalize
    ∧ rungRows t .opening wired = rungRows t .finalize wired ++ rungOwn t wired .opening :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- …and the length of each rung is the length of the one below plus its own — general over every
`StepData`, so §15's eight row-length `#guard`s at the smoke shape are instances of this rather than
the statement of it. -/
theorem rungRows_lengths_are_the_sum_of_their_parts (t : StepData) (wired : Bool) :
    (rungRows t .challenges wired).length
      = (rungRows t .transcript wired).length + (rungOwn t wired .challenges).length
    ∧ (rungRows t .msm wired).length
      = (rungRows t .challenges wired).length + (rungOwn t wired .msm).length
    ∧ (rungRows t .ipa wired).length
      = (rungRows t .msm wired).length + (rungOwn t wired .ipa).length
    ∧ (rungRows t .full wired).length
      = (rungRows t .ipa wired).length + (rungOwn t wired .full).length
    ∧ (rungRows t .ftEval0 wired).length
      = (rungRows t .full wired).length + (rungOwn t wired .ftEval0).length
    ∧ (rungRows t .absorb wired).length
      = (rungRows t .ftEval0 wired).length + (rungOwn t wired .absorb).length
    ∧ (rungRows t .finalize wired).length
      = (rungRows t .absorb wired).length + (rungOwn t wired .finalize).length
    ∧ (rungRows t .opening wired).length
      = (rungRows t .finalize wired).length + (rungOwn t wired .opening).length := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := rungRows_is_a_ladder t wired
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [h1]
  · simp [h2]
  · simp [h3]
  · simp [h4]
  · simp [h5]
  · simp [h6]
  · simp [h7]
  · simp [h8]

/-- Rung `k`'s public-input size: 0 below the closing rung, `pubWords` at and above it. -/
def rungPub (s : StepShape) : Rung → Nat
  | .transcript | .challenges | .msm | .ipa => 0
  | _ => s.pubWords

/-- Rung `k`'s absolute probe rows, in schedule order. -/
def rungProbeRows (t : StepData) (k : Rung) : List Nat :=
  let rows := rungRows t k true
  let p := rungPub t.sh k
  ((rows.zip (List.range rows.length)).filter (fun ri => ri.1.probe)).map (fun ri => p + ri.2)

/-! ### The renderer.

Same JSON the pickles harnesses parse, plus two fields the earlier ones did not need:
`public_input` (a `pubSize > 0` circuit is not runnable without it — `kimchi/src/verifier.rs:816`
rejects a length mismatch outright, so omitting it would force the harness to re-derive the public
input in Rust, which is witness authoring) and `probe_rows`, the absolute rows of the σ-only probes.
`probe_rows` travels WITH the circuit so the harness aims its tampers at what the Lean schedule
actually emitted rather than at a hand-copied constant that a schedule drift would silently
invalidate. -/

private def q (s : String) : String := "\"" ++ s ++ "\""
private def renderCell (c : Cell) : String := "[" ++ toString c.row ++ "," ++ toString c.col ++ "]"
private def renderWires (ws : List Cell) : String :=
  "[" ++ String.intercalate "," (ws.map renderCell) ++ "]"
private def renderIntList (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map (fun i => q (toString i))) ++ "]"
private def renderNatList (xs : List Nat) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"
private def renderGate (g : PlacedGate) : String :=
  "{" ++ q "typ" ++ ":" ++ toString g.kind.ordinal ++ ","
       ++ q "wires" ++ ":" ++ renderWires g.wires ++ ","
       ++ q "coeffs" ++ ":" ++ renderIntList g.coeffs ++ "}"

/-- A provable circuit with its public vector and its probe rows. -/
def renderStepCircuit (name : String) (pubSize numRows : Nat) (gs : List PlacedGate)
    (w : List (List Int)) (pub : List Int) (probes : List Nat) : String :=
  "{" ++ q "name" ++ ":" ++ q name ++ ","
       ++ q "public_input_size" ++ ":" ++ toString pubSize ++ ","
       ++ q "public_input" ++ ":" ++ renderIntList pub ++ ","
       ++ q "num_rows" ++ ":" ++ toString numRows ++ ","
       ++ q "probe_rows" ++ ":" ++ renderNatList probes ++ ","
       ++ q "gates" ++ ":[" ++ String.intercalate "," (gs.map renderGate) ++ "],"
       ++ q "witness" ++ ":[" ++ String.intercalate "," (w.map renderIntList) ++ "]}"

/-- Rung `k`'s emitted JSON (WIRED or UNWIRED control). -/
def rungJson (t : StepData) (k : Rung) (wired : Bool) (name : String) : String :=
  let rows := rungRows t k wired
  let p := rungPub t.sh k
  renderStepCircuit name p (p + rows.length)
    (placedOf p (stepGates rows)) (stepWitness t p rows)
    (if p == 0 then [] else stepPublic t) (rungProbeRows t k)

/-! ## §11 — the committed shape, sized against the `verify_one` line items. -/

/-- **THE COMMITTED SHAPE.** ⚑ Since §3b three of these are MEASURED off the real artifact rather
than reverse-engineered from a row count:

  * `msmTerms = 40` is the devnet Wrap verifier key's own `public = 40`, which is exactly how many
    `lagrange_commitment`s `multiscale_known` scales — and exactly the length of
    `MinaStepPrevCommitments.LAGRANGE_XY`. (It was 38, chosen to make 38×26×2 ≈ the measured 1972
    x_hat rows; the real number is 40 and now says so.)
  * `ipaRounds = 76` = 46 `combine_split_commitments` folds (`COMBINE_XY`'s 47 commitments, less the
    one the accumulator starts at) + `bullet_reduce`'s 30 `(L,R)` endos. Both lists are on disk at
    exactly those lengths.
  * ⚑ **`absorbs = 59` is `⌈117/2⌉`, and 117 is `verify_one`'s own sponge-item count**
    (`ABSORB_ITEMS`, §2, item by item at `step_verifier.ml:534-567,199,256,321`). It was **71** until
    2026-08-02 — `2·71 = 142` field elements against 117 — and that 25-word overshoot was being
    reported as twenty-five unwired ABSORPTIONS, which is a backlog item, rather than as a shape
    that swallows words upstream never feeds it, which is an error. (24 of the 25 go; the 25th is
    the pad lane an odd item count forces.) The 59 are: block 0
    (⚑ `index_digest`, §3c — upstream's own first absorption, one `Field`, its second lane the one
    PAD lane an odd item count forces), the 48 blocks that carry a fold commitment (18 fold + 30
    gammas), the 7 that carry `t_comm`'s quotient chunks (§6b), and **three** for the absorptions
    still unwired — `sg_old[0]`, `combined_inner_product` as field+bit, `delta` (`UNWIRED_ITEMS`).

`chals = 23` is β, γ, α, ζ, ξ, r, u, c + the 15 `bullet_reduce` squeezes; there is no `msmChunks`
any more — §1b gives statement word `i` its own width, 8 of the 40 at 255, 22 at 128, one at 10 and
nine at 1, so the emitted `x_hat` region is Mina's own 31 ladders; `bRounds = 16` is `Step_bp_vec = N16`;
`cipEvals = 47` is `N45` + `Wrap_hack`'s two; `pubWords = 67` is Step's `PRIMARY_LEN`. -/
def shapeStep : StepShape :=
  { absorbs := 59, chals := 23, emsRows := 8
  , msmTerms := 40
  , ipaRounds := 76, ipaBlocks := 32
  , bRounds := 16, cipEvals := 47, tComms := 7, pubWords := 67 }

/-- A small shape for the fast in-CI pins (the committed one is emitted by the driver).

⚑ `cipEvals` is **47 at both scales** and is no longer free: R6 slices the previous proof's 43
evaluation columns out of it (`EV_PREFIX = 4` + 43), and R7 absorbs those same 43 at two points. A
shape with fewer columns is not a smaller `verify_one`, it is a different one. -/
def shapeSmoke : StepShape :=
  -- ⚑ `absorbs` is 7 since §6b: block 0 is `index_digest`'s, blocks 1–3 carry the three absorbed
  -- fold commitments, blocks 4–6 carry `tCommN = 3` `t_comm` chunks. It still leaves ONE free
  -- `vMsg` block (block 0's second lane), which is what lets the smoke pins see the residue at all.
  { absorbs := 10, chals := 8, emsRows := 8
  , msmTerms := 3
  -- ⚑ `bRounds` is EVEN so the opt-sponge's rate-2 blocks do not straddle the two previous proofs:
  -- each proof contributes `bRounds` challenge words and a block absorbs two, so a block belongs to
  -- exactly one mask bit. (`shapeStep`'s 16 is even for the same reason — `Step_bp_vec = N16`.)
  -- ⚑ `ipaRounds` is 5 and not 3 since §6b: round `FTC_ROUND = 2` is now COMPUTED, so a 3-round
  -- shape would have NO `.const` fold base left and §12b's constant-provenance pins would be
  -- vacuous. At 5, rounds 0/1/3 are absorbed, 2 is computed and 4 is a verifier-key constant —
  -- all three provenances present.
  , ipaRounds := 5, ipaBlocks := 32
  , bRounds := 4, cipEvals := 47, tComms := 3, pubWords := 12 }

end Dregg2.Circuit.Emit.KimchiStepMain
