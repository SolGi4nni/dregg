import Dregg2.Circuit.Emit.PastaScalarMul
/-!
# Dregg2.Circuit.Emit.MinaWrapGroupGate — the Wrap **`ft_comm`** assembly, in-kernel, on the
REAL Mina devnet block's own Pallas commitments.

`docs/MINA-REAL-BLOCK-GATE.md` §3 stated the honest scope of the reality gate: the commitments
"are dumped as Pallas points but **nothing in-kernel touches them**". This file is the first
thing that does. Every check below consumes group elements of Mina devnet block **539508**
(state hash `3NLmVB6Fs3dm4kXNkgwheHXzJXNpCCwEDe76RpTVeBTNujm12zNk`) and lands on a value
produced by o1-labs' own code.

## The object

`kimchi/src/verifier.rs:897-963` — Maller's optimization — builds

```text
f_comm       = MSM(commitments, linearization scalars)          -- verifier.rs:897
ft_comm      = f_comm.chunk_commitment(zeta^max_poly_size)
                 - t_comm.chunk_commitment(zeta^max_poly_size).scale(zeta^n - 1)
```

`PicklesFinalize.picklesFtComm` transcribes that shape over a commutative ring and proves the
`zeta_to_domain_size` tie (`ftComm_ties_zeta_to_domain_size`, `ftComm_honest_agrees`,
`ftComm_forgery_moves_it`). It has never been **evaluated on points**. Here the same assembly
runs over K4a's RCB complete add and K4b's `scMulLadderM` ladder — the gadgets
`pallasCompleteAdd_forces` / `pallasLadder_forces` prove compute the real group law mod the
real prime — on the real block's real commitments.

## Why this rung is affordable, measured

The devnet blockchain Wrap verifier index has **zero** `linearization.index_terms`. Every
selector / coefficient / witness column the linearization could reference has its evaluation
SUPPLIED by the proof, so kimchi folds it into the linearization *constant term* — which is
exactly the scalar C5/`ftEval0R` already reproduces on this block. The only column with no
supplied evaluation is `sigma_comm[PERMUTS-1]`: `s` carries `PERMUTS-1 = 6` evaluations, not 7.
So **`f_comm` is a ONE-term MSM**, and the whole `ft_comm` assembly is 10 scalar
multiplications, not the open-ended MSM the plan assumed.

## What pins the gold values

`to_batch` is private, so `metatheory/fixtures/pickles-extractors/src/bin/wrap_group_export.rs`
rebuilds `f_comm` / `ft_comm` from o1-labs' own `perm_scalars`, `PolishToken::evaluate`,
`Context::get_column`, `PolyComm::multi_scalar_mul`, `chunk_commitment` and `scale`, and then
hands the reconstruction — inside the full 47-entry `evaluations` list — to **o1-labs' own
`SRS::verify`**, the real verifier's final IPA opening check. It returns `true`; with `ft_comm`
displaced by `+G` it returns `false`. So `FT_COMM_GOLD` below is not our arithmetic restated:
it is the only point that satisfies the real block's opening proof.

## What this is NOT

It is **one rung**. The Wrap group check also needs the 40-term `public_comm` Lagrange MSM, the
47-term `combine_commitments` polyscale fold, and `check_bulletproof`, whose `<s,G>` term is a
`2^15`-scalar MSM over the SRS and is **deferred by design** (K4c / P10). See
`docs/MINA-REAL-BLOCK-GATE.md` §6. Nothing here discharges the P10 opening floor.

Axiom-clean: `by decide` only; no `sorry`, no `native_decide`. NEW file; imports read-only
(`PastaScalarMul`, transitively `PastaCurveComplete`/`PastaCurve`/`PastaField`). NOT imported by
the `Dregg2` root, per house practice for gates.
-/

namespace Dregg2.Circuit.Emit.MinaWrapGroupGate

open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.PastaCurve (curveB)
open Dregg2.Circuit.Emit.PastaCurveComplete
  (curveB3 rcbAddM Oproj projOnCurveM projEqM isInfM)
open Dregg2.Circuit.Emit.PastaScalarMul (scMulLadderM)

set_option autoImplicit false
set_option maxRecDepth 4000000

/-! ## §1 — the Pallas group operations this gate is built from (K4a/K4b, unmodified) -/

/-- A projective Pallas point `(X : Y : Z)` over `Fp`. -/
abbrev Pt := Nat × Nat × Nat

/-- `[k]·P` by K4b's RCB double-and-add ladder at the full 255-bit scalar width.
`PastaScalarMul.pallasLadder_forces` is the statement that the emitted gates force this fold. -/
def smul (k : Nat) (P : Pt) : Pt := scMulLadderM pN curveB3 k P 255

/-- `P + Q` by K4a's unified RCB complete add (`pallasCompleteAdd_forces`). -/
def padd (P Q : Pt) : Pt := rcbAddM pN curveB3 P Q

/-- `-P = (X : -Y : Z)`. -/
def pneg (P : Pt) : Pt := (P.1, (pN - P.2.1 % pN) % pN, P.2.2)

/-- **`chunkedComm`** — `PolyComm::chunk_commitment` (`poly-commitment/src/commitment.rs:55`):
Horner over the chunks in REVERSE order, `res := res * z + chunk`. -/
def chunkedComm (z : Nat) (cs : List Pt) : Pt :=
  cs.reverse.foldl (fun acc c => padd (smul z acc) c) Oproj

/-- **`msmComm`** — `PolyComm::multi_scalar_mul` over `(scalar, commitment)` pairs. -/
def msmComm (terms : List (Nat × Pt)) : Pt :=
  terms.foldl (fun acc t => padd acc (smul t.1 t.2)) Oproj

/-- **`ftCommOf`** — `verifier.rs:960-964`, verbatim in shape:
`chunk(f_comm) - (zeta^n - 1) * chunk(t_comm)`. The `chunk_commitment` on `f_comm` is kept
STRUCTURALLY (it is a no-op only because `f_comm` has one chunk — see
`fComm_chunking_is_a_no_op`), so a future multi-chunk `f_comm` cannot silently pass. -/
def ftCommOf (zSrs zDomM1 : Nat) (fTerms : List (Nat × Pt)) (tChunks : List Pt) : Pt :=
  padd (chunkedComm zSrs [msmComm fTerms])
       (pneg (smul zDomM1 (chunkedComm zSrs tChunks)))

/-! ## §2 — the REAL block's group-side inputs

Mina devnet block 539508, extracted by `wrap_group_export`. Coordinates are in Pallas's BASE
field `Fp`; the scalars are in Pallas's SCALAR field `Fq`. -/

/-- `perm_scalars(evals, beta, gamma, alphas, zkp(zeta))` — the one linearization scalar. -/
def PERM_SCALAR : Nat :=
  20751602151633737401462851548350130147491954693090596112024602804092692290009

/-- `sigma_comm[PERMUTS-1]` of the devnet blockchain Wrap verifier index — the only commitment
in the linearization MSM. -/
def SIGMA6 : Pt :=
  (14533069567859997931411338798235390554646264745565930216225706045991714547029,
   230076843026232836139391506383317233661567084986689891555547340509935178276, 1)

/-- `zeta ^ max_poly_size` (`max_poly_size = 2^15`). -/
def ZETA_SRS : Nat :=
  15199112795516872416106212443861736899936601524200361370335031980543972401501

/-- `zeta ^ domain_size - 1` (`domain_size = 2^14`) — the Maller scale factor. -/
def ZETA_DOM_M1 : Nat :=
  20843391792192674096379110139698302699561672883528276553958322214537139602543

/-- The block's 7 `t_comm` chunks (the quotient-polynomial commitment). -/
def TCHUNKS : List Pt :=
  [
   (23382640723964694244614085791475445140174010552771292844771632654515403160637,
     1834425776058360070273876000949243701887690872386450124343969476133859769530, 1),
   (20421658267027367715396074495602338935050916716372351871694070908013011010291,
     24431848814686580882043032326478904323942350405263998684862417862435806498393, 1),
   (8437767720651266631202563727333255559581696471435778762846494362061787126045,
     11276986670832462284960651932652973464490945278737402618488498179480309617836, 1),
   (7946241131025672692298578151903787293968439645740063827867729888285820337110,
     10927595987986011294975437109092797646265671668037593639956868614001961557309, 1),
   (26564729323297090951288357447546753591584304754088897300539740329975354266862,
     2181201359162068961615983739336332714150726042358881483612526948087798181421, 1),
   (4110088031160970227382256682674593565642387053186990253717819687287700780866,
     23181278874497781495038467624138916413686045969349349775091313531417351742833, 1),
   (15154573345641821923530881260783904955491958425041230890861501704167338868255,
     22756676604486925033925604003249612792946449252929603692866839983627837642314, 1)
  ]

/-- The one-term linearization MSM, as `(scalar, commitment)` pairs. -/
def F_TERMS : List (Nat × Pt) := [(PERM_SCALAR, SIGMA6)]

/-! ### The gold values — o1-labs' own outputs, not ours -/

/-- kimchi's `t_comm.chunk_commitment(zeta_to_srs_len)`. -/
def CHUNKED_T_GOLD : Pt :=
  (20497740943364408243543950747415106590539589896294100246850578129887943765380,
   6854424204379636012319966707808008192294116986763538741874486503997782616159, 1)

/-- kimchi's `PolyComm::multi_scalar_mul` on the linearization MSM. -/
def F_COMM_GOLD : Pt :=
  (19674326400533049625615225538021626157270526457556463284014696039483724147764,
   28695397289097617976568064802307687844707320509254944091000772912640603603518, 1)

/-- kimchi's `ft_comm` — **pinned by o1-labs' own `SRS::verify` on the real opening proof**
(and refuted at `ft_comm + G`). -/
def FT_COMM_GOLD : Pt :=
  (23134851620960708781201702572748654667024999231009061048008617507448700477719,
   11095341763140500863332709654083102487611440299358362125188480277634145783318, 1)

/-! ## §3 — the computed objects -/

/-- Our `f_comm`. -/
def fComm : Pt := msmComm F_TERMS

/-- Our chunked `t_comm`. -/
def chunkedT : Pt := chunkedComm ZETA_SRS TCHUNKS

/-- Our `ft_comm`. -/
def ftComm : Pt := ftCommOf ZETA_SRS ZETA_DOM_M1 F_TERMS TCHUNKS

/-! ## §4 — the inputs are real Pallas points

Anti-vacuity floor: if these were junk the checks below would be about nothing. Each of the 8
input commitments and each of the 3 gold outputs satisfies `Y^2 Z = X^3 + 5 Z^3 (mod p)` — the
real Pallas curve at the real prime. -/

/-- **`real_inputs_are_on_pallas`** — the block's own `t_comm` chunks and the verifier index's
`sigma_comm[6]` are on `y^2 = x^3 + 5` over `Fp`. -/
theorem real_inputs_are_on_pallas :
    (TCHUNKS.all (projOnCurveM pN curveB) && projOnCurveM pN curveB SIGMA6) = true := by decide

/-- **`gold_outputs_are_on_pallas`** — and so are the three values o1-labs' code produced. -/
theorem gold_outputs_are_on_pallas :
    (projOnCurveM pN curveB CHUNKED_T_GOLD && projOnCurveM pN curveB F_COMM_GOLD
      && projOnCurveM pN curveB FT_COMM_GOLD) = true := by decide

/-- **`gold_outputs_are_distinct_affine_points`** — and they are three DIFFERENT finite points,
so an assembly that collapsed to a constant could not pass all three checks in §5. -/
theorem gold_outputs_are_distinct_affine_points :
    (projEqM pN CHUNKED_T_GOLD F_COMM_GOLD || projEqM pN F_COMM_GOLD FT_COMM_GOLD
      || projEqM pN CHUNKED_T_GOLD FT_COMM_GOLD
      || isInfM pN CHUNKED_T_GOLD || isInfM pN F_COMM_GOLD || isInfM pN FT_COMM_GOLD)
      = false := by decide

/-! ## §5 — THE RUNG: the assembly reproduces o1-labs' values on the real block -/

/-- **`chunkedT_reproduces_kimchi`** — the Horner fold of the block's **7 real `t_comm` Pallas
points** with `zeta^(2^15)`, over the RCB complete add, IS `PolyComm::chunk_commitment`'s output.
Six 255-bit ladders and seven complete adds on real group elements. -/
theorem chunkedT_reproduces_kimchi : projEqM pN chunkedT CHUNKED_T_GOLD = true := by decide

/-- **`fComm_reproduces_kimchi`** — the linearization MSM (`perm_scalars * sigma_comm[6]`) IS
`PolyComm::multi_scalar_mul`'s output. -/
theorem fComm_reproduces_kimchi : projEqM pN fComm F_COMM_GOLD = true := by decide

/-- **`ftComm_reproduces_kimchi`** — and the whole Maller assembly reproduces the `ft_comm` that
o1-labs' own `SRS::verify` accepts against this block's opening proof. This is the first check in
the campaign whose value depends on a group element. -/
theorem ftComm_reproduces_kimchi : projEqM pN ftComm FT_COMM_GOLD = true := by decide

/-- **`ftComm_is_a_finite_point`** — and the result is not the point at infinity, so
`projEqM`'s `Z = 0` degeneracy cannot be what made the previous theorem true. -/
theorem ftComm_is_a_finite_point : isInfM pN ftComm = false := by decide

/-- **`fComm_chunking_is_a_no_op`** — `chunk_commitment` on the one-chunk `f_comm` is the
identity, which is WHY `zeta^srs_len` reaches `ft_comm` only through `t_comm`. The group-side
counterpart of `PicklesFinalize.ftComm_srs_length_unused_at_one_chunk`; stated on the real
value rather than assumed. -/
theorem fComm_chunking_is_a_no_op :
    projEqM pN (chunkedComm ZETA_SRS [F_COMM_GOLD]) F_COMM_GOLD = true := by decide

/-! ## §6 — tamper poles

Each pole moves exactly one input of the assembly and the result stops matching o1-labs' value.
Without these, §5 would be consistent with an assembly that ignores its inputs. -/

/-- **`tamper_perm_scalar`** — one added to the linearization scalar. -/
theorem tamper_perm_scalar :
    projEqM pN (msmComm [(PERM_SCALAR + 1, SIGMA6)]) F_COMM_GOLD = false := by decide

/-- **`tamper_msm_base_point`** — the same scalar against a DIFFERENT real Pallas point from the
same block (`t_comm[0]` in place of `sigma_comm[6]`). -/
theorem tamper_msm_base_point :
    projEqM pN (msmComm [(PERM_SCALAR, TCHUNKS.headD Oproj)]) F_COMM_GOLD = false := by decide

/-- **`tamper_zeta_to_srs_length`** — one added to `zeta^(2^15)`. At 7 chunks the SRS-length
scalar IS read (the counterpart of `ftComm_srs_length_used_at_two_chunks`). -/
theorem tamper_zeta_to_srs_length :
    projEqM pN (chunkedComm (ZETA_SRS + 1) TCHUNKS) CHUNKED_T_GOLD = false := by decide

/-- **`tamper_chunk_order`** — the same 7 points folded the other way round. Horner is not
symmetric, so a fold that got the chunk order wrong is caught. -/
theorem tamper_chunk_order :
    projEqM pN (chunkedComm ZETA_SRS TCHUNKS.reverse) CHUNKED_T_GOLD = false := by decide

/-- **`tamper_zeta_to_domain_size`** — one added to the Maller scale factor `zeta^n - 1`. -/
theorem tamper_zeta_to_domain_size :
    projEqM pN (ftCommOf ZETA_SRS (ZETA_DOM_M1 + 1) F_TERMS TCHUNKS) FT_COMM_GOLD
      = false := by decide

/-- **`tamper_drop_maller_term`** — dropping the `- (zeta^n - 1) * chunk(t_comm)` subtraction
entirely, i.e. claiming `ft_comm = f_comm`. This is the pole that says the `t_comm` points are
load-bearing in `ft_comm` and not merely computed alongside it. -/
theorem tamper_drop_maller_term :
    projEqM pN (chunkedComm ZETA_SRS [fComm]) FT_COMM_GOLD = false := by decide

/-- **`tamper_add_instead_of_subtract`** — and the SIGN of the Maller term is load-bearing:
`f_comm + (zeta^n - 1) * chunk(t_comm)` is not `ft_comm`. -/
theorem tamper_add_instead_of_subtract :
    projEqM pN (padd (chunkedComm ZETA_SRS [msmComm F_TERMS])
                     (smul ZETA_DOM_M1 (chunkedComm ZETA_SRS TCHUNKS)))
               FT_COMM_GOLD = false := by decide

#assert_namespace_axioms Dregg2.Circuit.Emit.MinaWrapGroupGate

end Dregg2.Circuit.Emit.MinaWrapGroupGate
