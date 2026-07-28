/-
# Dregg2.Circuit.Emit.KimchiVerify — the Kimchi (Mina) single-proof VERIFY assembly (K5)
(composes the built primitives K1–K4 into the verifier's check-by-check decision;
task K5 of `docs/MINA-KIMCHI-VERIFIER-PLAN.md`, spec `docs/KIMCHI-VERIFY-SPEC.md`).

## What this file IS (and the honest boundary it draws)

The prior K-lanes built the FLOOR: K1 (`PastaField`, forced Fp/Fq arithmetic), K2/K4a
(`PastaCurve`/`PastaCurveComplete`, point ops + the unified RCB add), K3 (`PastaPoseidon`, the
Fiat–Shamir transcript sponge, `perm_forces`), K4b (`PastaScalarMul`, the forced `[k]P` ladder),
K4c (`PastaIPA`, the IPA-opening DEFERRAL + the `sVec_eq_bPoly` identity that makes it sound).
This file ASSEMBLES those into the Kimchi verifier's checks in verifier ORDER — the object
`ProverProof::oracles → to_batch → OpeningProof::verify` of o1-labs `proof-systems` v0.7.0
(rev `36a8b510`).

It is authored the way the light-client verifier gate is (`Dregg2.Bridge.LightClientEthGate`):
a composed `kimchiVerifyDecision` over the per-check sub-decisions + named crypto CARRIERS,
with a `rfl`-refinement tie and a kernel-clean DISCRIMINATION (each check load-bearing). What is
new + built here vs. what remains a NAMED carrier / residual is stated PER CHECK below and in §9.

## The two fields (the Pasta 2-cycle, spec §0)

The proof side is Vesta: `G::ScalarField = Fp` (all evaluations, challenges, scalar arithmetic),
`G::BaseField = Fq` (point coordinates). The field-arithmetic checks (C4/C5/C6/C8) are authored
FIELD-GENERIC (`variable {F} [Field F]`) — the exact transcription of the Rust formulas, valid
over any field — and the real statement lives at `Fp = ZMod PastaField.pN` (Vesta::ScalarField,
modulus `pN`, mina-curves `fp.rs`); the in-kernel KATs use `F = ℚ` (exact, kernel-reducible),
exactly as `PastaIPA` proves `sVec_eq_bPoly` over any `CommRing` and KATs over ℤ. There is no
`Field (ZMod pN)` instance in the tree (no in-kernel primality proof of the 255-bit `pN`), so §9b
composes the C5/C8 checks over `ZMod pN` AS A `CommRing` with a WITNESSED inverse
(`kimchiVerifyDecisionField`; see `docs/MINA-REALITY-GATE.md`). The `ℤ ↔ p_felt` field-width gap
(the emitted-column soundness, K1 §6) is the shared residual; the arithmetic here is over `F`
directly, above the felt encoding.

## What is BUILT (real gadget/theorem) vs NAMED (carrier/residual), per check

  * **C1** shape/length checks (`shapeOk`) — REAL, pure `Nat`/`Bool`, decidable + forced + KAT'd.
  * **C3** the Fiat–Shamir transcript ORDER (`transcriptSchedule`, `squeeze_order`) — the exact
    absorb/squeeze order of `verifier.rs:126-405`, with β/γ RAW and α/ζ/v/u through the endo map,
    PROVEN as an enumerated-order theorem; phase-1 realized by K3's sponge (KAT). The sponge
    PERMUTATION values are the K3 carrier; the Fr-sponge-over-Fq is a NAMED residual (K3 baked Fp).
  * **C4** public eval at ζ, ζω (`publicEval`) — the exact batch-inverted Lagrange formula
    (`verifier.rs:336-379`), field-generic, KAT'd (collapse + discrimination).
  * **C5** the permutation term of ft(ζ) + `permScalar` (`verifier.rs:411-462`,
    `permutation.rs:392-430`) — the copy-constraint z-poly identity, folded into `ftEval0`, REAL.
  * **C6** the linearization at ζ: a real `PolishToken` mini-evaluator (`evalToks`) + the GENERIC
    GATE constraint transcribed as a token stream (`genericGateToks`, `genericGate_evaluates`), the
    arithmetic core of `PolishToken::evaluate`. The custom-gate constraint streams (Poseidon/
    VarBaseMul/CompleteAdd/… — verifier-index-baked data) are the NAMED `linConstTerm` carrier.
  * **C7** `f_comm`/`ft_comm` + Maller (`ftComm`, `verifier.rs:958-965`) — the Maller relation
    `ft_comm = f_comm − (ζⁿ−1)·t_comm`, field/module-generic, KAT'd. The MSM producing `f_comm`
    is the K2 carrier.
  * **C8** `combined_inner_product` (`combinedInnerProduct`, `commitment.rs:600-657`) — the exact
    nested sum (v1 `chunk_size = 1`), field-generic, KAT'd (positive anchor + discrimination).
  * **C9** the IPA opening (`ipaB0`, `ipaDeferralOk`, `deferral_records`) — `b0` from K4c's
    `bEval`, the deferred `⟨s,G⟩` obligation RECORDED via `IpaDeferred` (size `2^k` from `k`
    challenges, PROVEN by `deferral_compression`/`sVec_eq_bPoly`). The MSM `== 0` accept is the
    NAMED `ipaOk` carrier (inherits the IPA/FRI soundness floor — NOT discharged here).

## What is NOT claimed (the load-bearing honesty)

This is NOT a proven-sound Kimchi verifier. `accept ⟹ the proof is valid` is NOT established: it
rests on the IPA/FRI soundness floor (the `ipaOk` carrier — a STARK proves the trace, not the
opening), on the `linConstTerm` carrier (the custom-gate token streams), and on the Fr-sponge /
field-width residuals. What IS established: the checks are TRANSCRIBED faithfully (source-cited,
KAT'd), ASSEMBLED in verifier order into one `kimchiVerifyDecision`, the composition REFINES the
per-check conjunction (`kimchiVerifyDecision_refines`, `rfl`), each check DISCRIMINATES
(`kimchi_decision_discriminates`, kernel-clean), and the C9 deferral is soundly RECORDED (not
brute-forced). Pickles recursion, batching, lookups (C10) are out of v1 scope (§9).

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. `#guard`/`decide` KATs reduce in the kernel (`Nat`/`Bool` and `ℚ`). NEW file;
imports `PastaIPA` (transitively K4b/K4a/K3/K2/K1); standalone (NOT imported by the truncated
`Dregg2` root; built directly as `Dregg2.Circuit.Emit.KimchiVerify`).
-/
import Dregg2.Circuit.Emit.PastaIPA
import Dregg2.Circuit.Emit.PastaPoseidon

namespace Dregg2.Circuit.Emit.KimchiVerify

open Dregg2.Circuit.Emit.PastaIPA (bEval sVec polyEval IpaDeferred absorbChallenges
  deferredMsmSize sVec_length sVec_eq_bPoly deferral_compression absorbChallenges_chals)

set_option autoImplicit false

/-! ## §0 — v1 frozen shape parameters (spec §"K5 build plan"). -/

/-- Permutation columns (`PERMUTS`): 7 σ columns — 6 σ EVALS in the proof, σ₆ as a COMMITMENT. -/
def PERMUTS : Nat := 7
/-- Witness columns (`COLUMNS`): 15 `w` commitments/evals. -/
def COLUMNS : Nat := 15
/-- Zero-knowledge rows (`ZK_ROWS_BY_DEFAULT`, `constraints.rs:801`). -/
def zkRows : Nat := 3

/-! ## §1 — C1: the shape / length checks (`verifier.rs:640-779, 810-831, 259-266`).

Pure `Nat`/`Bool`, fully decidable — exactly the light-client `syncDecision` register (lengths,
counts, no crypto). v1 FREEZES: no recursion (`prevLen = 0`), no lookups, `chunk_size = 1`. -/

/-- **`shapeOk`** — every length/shape assert of `to_batch`'s preamble, v1-frozen. -/
def shapeOk (prevLen publicLen wLen sLen coeffLen tCommLen chunkSize : Nat) : Bool :=
  decide (prevLen = 0)                       -- v1: prev_challenges = 0 (no Pickles recursion)
  && decide (0 < publicLen)                  -- public input present (verifier.rs:816-820)
  && decide (wLen = COLUMNS)                 -- 15 witness commitments (verifier.rs:173-177)
  && decide (sLen = PERMUTS - 1)             -- 6 σ evaluations (verifier.rs:967-1181)
  && decide (coeffLen = COLUMNS)             -- 15 coefficient columns
  && decide (chunkSize = 1)                  -- v1: domain ≤ SRS (verifier.rs:823-830)
  && decide (tCommLen ≤ 7 * chunkSize)       -- t_comm length bound (verifier.rs:259-266)

/-! ## §2 — C3: the Fiat–Shamir transcript ORDER (`verifier.rs:126-405`; `plonk_sponge.rs:56-156`).

The ORDER is the security-critical content — it determines every challenge, hence every downstream
scalar. We encode the EXACT absorb/squeeze schedule and PROVE the squeeze order (β γ α ζ v u) with
the raw-vs-endo flag matching `verifier.rs:232-405` (β,γ RAW `verifier.rs:233,236`; α,ζ,v,u through
`to_field(endo_r)`). The sponge PERMUTATION values are K3's carrier (`PastaPoseidon.perm_forces`);
the Fr-sponge-over-Fq (phase 2) is the NAMED residual — K3 baked the Fq-sponge-over-Fp constants. -/

/-- A squeezed challenge. -/
inductive Chal where
  | beta | gamma | alpha | zeta | v | u
  deriving DecidableEq, Repr

/-- One transcript step: an ABSORB (labeled by provenance) or a SQUEEZE of a challenge with the
`endo` flag (`true` ⇒ mapped via `to_field(endo_r)`; `false` ⇒ used raw). -/
inductive Step where
  | absorb (label : String)
  | squeeze (c : Chal) (endo : Bool)
  deriving Repr

/-- **`transcriptSchedule`** — the exact `ProverProof::oracles` order for v1 (no recursion, no
lookups). Fq-sponge phase (`verifier.rs:161-276`): absorb index digest, public_comm, the 15 w
commitments, squeeze β (raw), γ (raw); absorb z_comm, squeeze α (endo); absorb t_comm, squeeze ζ
(endo). Fr-sponge phase (`verifier.rs:278-405`): absorb the fq-sponge digest, the public evals at
[ζ, ζω], ft_eval1, then all evaluations in `absorb_evaluations` order (z, the 6 gate selectors,
w[0..15], coefficients[0..15], s[0..6], each ζ then ζω), squeeze v (endo), u (endo). -/
def transcriptSchedule : List Step :=
  [ .absorb "index_digest"                                  -- verifier.rs:161-163
  , .absorb "public_comm"                                   -- verifier.rs:170-171
  ] ++ (List.range COLUMNS).map (fun i => Step.absorb s!"w_comm[{i}]")  -- verifier.rs:173-177
  ++ [ .squeeze .beta false                                 -- verifier.rs:232-233 (RAW)
     , .squeeze .gamma false                                -- verifier.rs:235-236 (RAW)
     , .absorb "z_comm"                                     -- verifier.rs:249-250
     , .squeeze .alpha true                                 -- verifier.rs:253-257 (endo)
     , .absorb "t_comm"                                     -- verifier.rs:259-269
     , .squeeze .zeta true                                  -- verifier.rs:272-276 (endo)
     , .absorb "fq_sponge_digest"                           -- verifier.rs:278-287 (Fr-sponge start)
     , .absorb "public_eval[zeta]"                          -- verifier.rs:391-392
     , .absorb "public_eval[zeta_omega]"
     , .absorb "ft_eval1"                                   -- verifier.rs:381-382
     , .absorb "eval:z"                                     -- plonk_sponge.rs:88-96 order …
     , .absorb "eval:generic_selector"
     , .absorb "eval:poseidon_selector"
     , .absorb "eval:complete_add_selector"
     , .absorb "eval:mul_selector"
     , .absorb "eval:emul_selector"
     , .absorb "eval:endomul_scalar_selector"
     ]
  ++ (List.range COLUMNS).map (fun i => Step.absorb s!"eval:w[{i}]")
  ++ (List.range COLUMNS).map (fun i => Step.absorb s!"eval:coefficients[{i}]")
  ++ (List.range (PERMUTS - 1)).map (fun i => Step.absorb s!"eval:s[{i}]")
  ++ [ .squeeze .v true                                     -- verifier.rs:395-399 (endo)
     , .squeeze .u true                                     -- verifier.rs:401-405 (endo)
     ]

/-- Extract the squeezes (challenge + endo flag) in order. -/
def squeezes (l : List Step) : List (Chal × Bool) :=
  l.filterMap (fun s => match s with | .squeeze c e => some (c, e) | _ => none)

/-- **`squeeze_order`** — the challenges are squeezed in EXACTLY the verifier order, with β and γ
RAW and α, ζ, v, u through the endo map. This is the C3 invariant the whole verifier hangs on. -/
theorem squeeze_order :
    squeezes transcriptSchedule =
      [(Chal.beta, false), (Chal.gamma, false), (Chal.alpha, true),
       (Chal.zeta, true), (Chal.v, true), (Chal.u, true)] := by
  decide

/-- The number of absorbs before the first squeeze (β): index digest + public_comm + 15 w_comms. -/
theorem absorbs_before_beta :
    (transcriptSchedule.takeWhile (fun s => match s with | .squeeze _ _ => false | _ => true)).length
      = 2 + COLUMNS := by
  decide

/-! ## §3 — C4: public-input evaluation at ζ and ζω (`verifier.rs:336-379`).

`p(x) = (xⁿ − 1)·n⁻¹·Σᵢ(−pᵢ·ωⁱ/(x − ωⁱ))`. The Rust folds a single batch-inverted `zeta_minus_x`
vector for both points; the value is this closed form. Field-generic (needs `⁻¹` ⇒ `[Field F]`). -/

variable {F : Type} [Field F]

/-- The Lagrange sum `Σᵢ (−pubᵢ)·ωⁱ·(x − ωⁱ)⁻¹` (the batch-inverted core). -/
def lagrangeSum (omega x : F) (pub : List F) : F :=
  (List.range pub.length).foldl
    (fun acc i => acc + (-(pub.getD i 0)) * omega ^ i * (x - omega ^ i)⁻¹) 0

/-- **`publicEval`** — the negated-public-input polynomial evaluated at `x ∈ {ζ, ζω}`
(`verifier.rs:336-379`). `n` = domain size, `omega` = its generator. -/
def publicEval (n : Nat) (omega x : F) (pub : List F) : F :=
  (x ^ n - 1) * (n : F)⁻¹ * lagrangeSum omega x pub

/-! ## §4 — C5 + C6: `ft(ζ)` — the permutation term folded with the linearization constant term
(`verifier.rs:411-490`; `permutation.rs:392-430`; `linearization.rs`).

`ftEval0` is the ζ-opening of the quotient identity `f = t·Z_H` after Maller's optimization: the
copy-constraint (C5) is the two σ-product folds, and the gate constraints (C6) enter as the
subtracted linearization constant term `linConstTerm`. Transcribed line-for-line. -/

/-- `zkp(ζ) = (ζ − ω^{n−3})(ζ − ω^{n−2})(ζ − ω^{n−1})` — the ZK vanishing poly
(`permutation.rs:115-118`, `zk_rows = 3`). -/
def zkPoly (n : Nat) (omega zeta : F) : F :=
  (zeta - omega ^ (n - 3)) * (zeta - omega ^ (n - 2)) * (zeta - omega ^ (n - 1))

/-- **`ftEval0`** — `ft(ζ)`, `verifier.rs:411-490`, term-for-term:
`init = (w₆(ζ)+γ)·z(ζω)·α⁰·zkp`; the numerator σ-fold `Πᵢ<₆(β·σᵢ(ζ)+wᵢ(ζ)+γ)`; `− p(ζ)`; the
denominator σ-fold `α⁰·zkp·z(ζ)·Πᵢ<₇(γ+β·ζ·shiftᵢ+wᵢ(ζ))`; the `(1−z)` boundary term; and
`− linConstTerm` (the linearization constant term, C6 — the named PolishToken carrier of §5). -/
def ftEval0 (n : Nat) (omega zeta beta gamma alpha0 alpha1 alpha2 : F)
    (w s shift : List F) (zZeta zZetaOmega pZeta linConstTerm : F) : F :=
  let zkp := zkPoly n omega zeta
  let zeta1m1 := zeta ^ n - 1
  let init := (w.getD (PERMUTS - 1) 0 + gamma) * zZetaOmega * alpha0 * zkp
  let numerFold := (List.range (PERMUTS - 1)).foldl
    (fun x i => x * (beta * s.getD i 0 + w.getD i 0 + gamma)) init
  let afterPub := numerFold - pZeta
  let denomFold := (List.range PERMUTS).foldl
    (fun x i => x * (gamma + beta * zeta * shift.getD i 0 + w.getD i 0))
    (alpha0 * zkp * zZeta)
  let afterDenom := afterPub - denomFold
  let numerator := (zeta1m1 * alpha1 * (zeta - omega ^ (n - 3))
    + zeta1m1 * alpha2 * (zeta - 1)) * (1 - zZeta)
  let denominator := (zeta - omega ^ (n - 3)) * (zeta - 1)
  let afterZk := afterDenom + numerator * denominator⁻¹
  afterZk - linConstTerm

/-- **`permScalar`** — `perm_scalars` (`permutation.rs:392-430`): the scalar multiplying the σ₆
COMMITMENT in the `f_comm` MSM (C7), the commitment side of the same copy-constraint argument:
`− z(ζω)·β·α⁰·zkp(ζ)·Πᵢ<₆(γ+β·σᵢ(ζ)+wᵢ(ζ))`. σ₀..σ₅ appear inside `ftEval0` as evals; σ₆ enters
here as a commitment — the Maller split. -/
def permScalar (n : Nat) (omega zeta beta gamma alpha0 : F) (w s : List F) (zZetaOmega : F) : F :=
  let zkp := zkPoly n omega zeta
  let init := zZetaOmega * beta * alpha0 * zkp
  let res := (List.range (PERMUTS - 1)).foldl
    (fun x i => x * (gamma + beta * s.getD i 0 + w.getD i 0)) init
  0 - res

/-! ## §5 — C6: a real `PolishToken` mini-evaluator + the GENERIC GATE constraint.

`PolishToken::evaluate` (`linearization.rs`, the constant term + per-column index terms) is a stack
machine over Fq. We transcribe its ARITHMETIC CORE (Literal, Cell, Dup, Pow, Add, Mul, Sub) and
express the GENERIC GATE constraint `l·w₀ + r·w₁ + o·w₂ + m·w₀·w₁ + c` (`generic.rs:163-195`) as a
token stream, proving the evaluator computes it. The challenge tokens (Alpha/Beta/Gamma/Mds/…) and
the CUSTOM-gate constraint streams (Poseidon 5-round unroll, VarBaseMul, CompleteAdd, EndomulScalar
— verifier-index-baked data) are the NAMED `linConstTerm` carrier: baked constants, not new algebra.

The evaluator is a genuine stack machine (RPN), not a scalar — it establishes that C6's
`PolishToken::evaluate` shape is expressible + composes over `F`; the residual is the LENGTH of the
baked stream, not its semantics. -/

/-- The arithmetic core of `PolishToken` (RPN over a value stack). `cell v` pushes a resolved
evaluation (the value `PolishToken::Cell` looks up from the proof evals). -/
inductive Tok (F : Type) where
  | lit (c : F)        -- `Literal`
  | cell (v : F)       -- `Cell` (resolved evaluation)
  | dup                -- `Dup`
  | pow (e : Nat)      -- `Pow`
  | add                -- `Add`
  | mul                -- `Mul`
  | sub                -- `Sub`

/-- Evaluate a token over a value stack (top = head). Malformed streams leave the stack unchanged
(fail-safe; a well-formed constraint stream never underflows). -/
def stepTok (st : List F) : Tok F → List F
  | .lit c => c :: st
  | .cell v => v :: st
  | .dup => match st with | x :: r => x :: x :: r | _ => st
  | .pow e => match st with | x :: r => x ^ e :: r | _ => st
  | .add => match st with | x :: y :: r => (y + x) :: r | _ => st
  | .mul => match st with | x :: y :: r => (y * x) :: r | _ => st
  | .sub => match st with | x :: y :: r => (y - x) :: r | _ => st

/-- Run a token stream from the empty stack; read the result (top, or 0 if empty). -/
def evalToks (toks : List (Tok F)) : F :=
  match toks.foldl stepTok ([] : List F) with
  | x :: _ => x
  | [] => 0

/-- The generic-gate constraint as a token stream: `l·w₀ + r·w₁ + o·w₂ + m·(w₀·w₁) + c`
(`generic.rs:163-195`). Coefficients `l,r,o,m,c` are index constants; `w0,w1,w2` are the resolved
witness evals at ζ. RPN, left-associated sums. -/
def genericGateToks (l r o m c w0 w1 w2 : F) : List (Tok F) :=
  [ .lit l, .cell w0, .mul                       -- l·w₀
  , .lit r, .cell w1, .mul, .add                 -- + r·w₁
  , .lit o, .cell w2, .mul, .add                 -- + o·w₂
  , .lit m, .cell w0, .cell w1, .mul, .mul, .add -- + m·w₀·w₁
  , .lit c, .add ]                               -- + c

/-- **`genericGate_evaluates`** — the evaluator computes the generic-gate constraint value. The C6
token machine is REAL: it reduces the transcribed stream to the exact `generic.rs` polynomial. -/
theorem genericGate_evaluates (l r o m c w0 w1 w2 : F) :
    evalToks (genericGateToks l r o m c w0 w1 w2)
      = l * w0 + r * w1 + o * w2 + m * (w0 * w1) + c := by
  simp only [evalToks, genericGateToks, List.foldl_cons, List.foldl_nil, stepTok]

/-! ## §6 — C7: `f_comm` / `ft_comm` and Maller's optimization (`verifier.rs:889-965`).

`f_comm = permScalar·σ₆_comm + Σ index_terms` is a Vesta MSM (K2 carrier). The verified LOGIC here
is Maller's ft-commitment assembly (`verifier.rs:958-965`, v1 `chunk_size = 1`, no chunking):
`ft_comm = f_comm − (ζⁿ − 1)·t_comm`. Module/field-generic (`G = F` instantiates for the KAT). -/

/-- **`ftComm`** — Maller's ft-commitment from `f_comm`, `t_comm`, and `ζⁿ − 1` (v1, unchunked). -/
def ftComm {G : Type} [AddCommGroup G] [Module F G] (n : Nat) (zeta : F) (fComm tComm : G) : G :=
  fComm - (zeta ^ n - 1) • tComm

/-! ## §7 — C8: `combined_inner_product` (`commitment.rs:600-657`, formula `617-619`).

v1 `chunk_size = 1` (one segment per poly): `cip = Σ_k polyscale^k·(evalsᵏ(ζ) + evalscale·evalsᵏ(ζω))`
over the ordered poly list (prev-chal, public, ft, z, selectors, w, coeff, σ). The ORDER of the
list is `verifier.rs:502-603`; the values are the claimed evals. -/

/-- **`combinedInnerProduct`** — the aggregated opening value (v1 single-segment). `evZeta`/
`evZetaOmega` are the two evaluation columns in the C8 poly order. -/
def combinedInnerProduct (polyscale evalscale : F) (evZeta evZetaOmega : List F) : F :=
  (List.range evZeta.length).foldl
    (fun acc k => acc + polyscale ^ k * (evZeta.getD k 0 + evalscale * evZetaOmega.getD k 0)) 0

/-! ## §8 — C9: the IPA opening — `b0` + the DEFERRED `⟨s,G⟩` obligation (`ipa.rs:301-502`; K4c).

`b0 = Σⱼ evalscale^j·b(xⱼ)` over `[ζ, ζω]`, `b(X) = ∏(1 + uᵢ·X^{2^…})` (K4c's `bEval`). The
`2^k`-term `⟨s,G⟩` MSM is NOT materialized: `sVec_eq_bPoly` shows it is the coefficient vector of
`b`, reconstructible from the `k` round challenges, so it is DEFERRED as a compact obligation
(`IpaDeferred`, size `2^k` from `k` — `deferral_compression`). The final `msm == 0` accept is the
named `ipaOk` carrier (the IPA/FRI soundness floor — NOT discharged). -/

/-- **`ipaB0`** — `b0 = b(ζ) + evalscale·b(ζω)` (`ipa.rs:389-398`), `b` = K4c's `bEval` over the
`k` round challenges. -/
def ipaB0 (evalscale zeta zetaOmega : F) (chals : List F) : F :=
  bEval zeta chals + evalscale * bEval zetaOmega chals

/-- **`ipaDeferralOk`** — the deferred `⟨s,G⟩` obligation is RECORDED with exactly `k` accumulated
round challenges and a `2^k`-term deferred size (never materialized in-circuit). -/
def ipaDeferralOk {Pt : Type} (d : IpaDeferred F Pt) (k : Nat) : Bool :=
  decide (d.chals.length = k) && decide (deferredMsmSize d = 2 ^ k)

/-- **`deferral_records`** — folding `k` round challenges into the empty accumulator produces a
correctly-recorded deferral: `k` challenges, `2^k` deferred terms, matching `sVec`'s length. This
is the C9 soundness content (K4c's `deferral_compression`), tying the accept to a REAL obligation
rather than the 65536-term MSM. -/
theorem deferral_records {Pt : Type} (sg0 : Pt) (us : List F) :
    ipaDeferralOk (absorbChallenges ⟨[], sg0⟩ us) us.length = true
    ∧ (sVec (absorbChallenges (⟨[], sg0⟩ : IpaDeferred F Pt) us).chals).length
        = deferredMsmSize (absorbChallenges ⟨[], sg0⟩ us) := by
  obtain ⟨h1, h2, h3⟩ := deferral_compression (F := F) sg0 us
  refine ⟨?_, h3⟩
  unfold ipaDeferralOk
  rw [h1, h2]
  simp

/-! ## §9 — THE ASSEMBLY: `kimchiVerifyDecision` (mirrors `LightClientEthGate.ethVerifyDecision`).

The verifier's single accept is `to_batch`'s shape asserts (C1) followed by `OpeningProof::verify`'s
`msm == 0` (C9) — with the transcript (C3) deriving the challenges and the field formulas
(C4/C5/C6/C8) building the batch that C9 opens. So the decision composes:

  `shapeOk (C1) ∧ transcriptOk (C3 carrier) ∧ ipaOk (C9 carrier) ∧ deferralOk (C9 recorded)`

`transcriptOk` = the claimed challenges equal the sponge squeezes IN THE canonical ORDER
(`squeeze_order`) — the ORDER is verified logic, the sponge VALUES are K3's carrier. `ipaOk` = the
`msm == 0` result over the batch assembled from C4/C5/C6/C7/C8 — the IPA/FRI soundness carrier.
`deferralOk` = `ipaDeferralOk` (C9's `⟨s,G⟩` recorded, not brute-forced). -/

/-- **`kimchiVerifyDecision`** — the composed single-proof Kimchi verify decision (v1). -/
def kimchiVerifyDecision (prevLen publicLen wLen sLen coeffLen tCommLen chunkSize : Nat)
    (transcriptOk ipaOk deferralOk : Bool) : Bool :=
  shapeOk prevLen publicLen wLen sLen coeffLen tCommLen chunkSize
  && transcriptOk && ipaOk && deferralOk

/-- **`kimchiVerifyDecision_refines`** — the decision IS the conjunction of the per-check
sub-decisions (`rfl`), the translation-validation shape of `ethVerifyDecision_refines`. -/
theorem kimchiVerifyDecision_refines (prevLen publicLen wLen sLen coeffLen tCommLen chunkSize : Nat)
    (transcriptOk ipaOk deferralOk : Bool) :
    kimchiVerifyDecision prevLen publicLen wLen sLen coeffLen tCommLen chunkSize
        transcriptOk ipaOk deferralOk
      = (shapeOk prevLen publicLen wLen sLen coeffLen tCommLen chunkSize
          && transcriptOk && ipaOk && deferralOk) := rfl

/-! ## §9b — COMPOSING THE FIELD ARITHMETIC INTO THE DECISION (the reality-gate closure).

`kimchiVerifyDecision` above is C1 + three opaque carriers — it consumes NO field element
(`docs/MINA-REALITY-GATE.md` §3: the field formulas were validated BESIDE the accept, not inside
it). This section threads the C8 (`combinedInnerProduct`) and C5 (`ftEval0`) field-value checks
THROUGH the accept, so a real proof's arithmetic is CHECKED inside one decision.

The obstruction: `combinedInnerProduct`/`ftEval0` are `[Field F]`-typed (the ζ-numerator carries
one inverse) and the real proof lives in `ZMod pN`, which has NO `Field` instance in the tree (no
in-kernel primality proof of the 255-bit `pN`; `native_decide` forbidden). We SIDESTEP the Field
instance exactly as `PastaIPA` handles its identities — `CommRing`-typed MIRRORS whose bodies are
byte-identical to the shipped defs, tied to them by `rfl` for every field (`cipR_eq`, `ftEval0R_eq`)
— with the single field inverse SUPPLIED as a witness `denomInv` and its correctness
`denom · denomInv = 1` CHECKED in the `CommRing` (a unit's inverse is unique in any monoid, so this
pins `denomInv = denominator⁻¹` without any primality/Field structure). No genuinely-unwitnessed
division remains in C5/C8, so no Pasta-prime `Field (ZMod pN)` instance is needed. (C4 `p(ζ)` enters
the C5 fold as an INPUT — recomputing it needs the un-extracted batch-inverted Lagrange denominators,
a named residual; C7 `ftComm`/`permScalar` are commitment/MSM-valued, the K2 carrier, not field-value
checks.) -/

/-- CommRing mirror of `combinedInnerProduct` (C8) — no division, body byte-identical. -/
def cipR {R : Type} [CommRing R] (polyscale evalscale : R) (evZeta evZetaOmega : List R) : R :=
  (List.range evZeta.length).foldl
    (fun acc k => acc + polyscale ^ k * (evZeta.getD k 0 + evalscale * evZetaOmega.getD k 0)) 0

/-- **`cipR_eq`** — the C8 mirror IS the shipped `combinedInnerProduct`, for every field. -/
theorem cipR_eq {K : Type} [Field K] (a b : K) (x y : List K) :
    cipR a b x y = combinedInnerProduct a b x y := rfl

/-- CommRing mirror of `zkPoly` (used by `ftEval0R`). -/
def zkPolyR {R : Type} [CommRing R] (n : Nat) (omega zeta : R) : R :=
  (zeta - omega ^ (n - 3)) * (zeta - omega ^ (n - 2)) * (zeta - omega ^ (n - 1))

/-- CommRing mirror of `ftEval0` (C5) with the single field inverse `denominator⁻¹` SUPPLIED as
`denomInv`; body otherwise byte-identical to `ftEval0`. -/
def ftEval0R {R : Type} [CommRing R] (n : Nat) (omega zeta beta gamma alpha0 alpha1 alpha2 : R)
    (w s shift : List R) (zZeta zZetaOmega pZeta linConstTerm denomInv : R) : R :=
  let zkp := zkPolyR n omega zeta
  let zeta1m1 := zeta ^ n - 1
  let init := (w.getD (PERMUTS - 1) 0 + gamma) * zZetaOmega * alpha0 * zkp
  let numerFold := (List.range (PERMUTS - 1)).foldl
    (fun x i => x * (beta * s.getD i 0 + w.getD i 0 + gamma)) init
  let afterPub := numerFold - pZeta
  let denomFold := (List.range PERMUTS).foldl
    (fun x i => x * (gamma + beta * zeta * shift.getD i 0 + w.getD i 0))
    (alpha0 * zkp * zZeta)
  let afterDenom := afterPub - denomFold
  let numerator := (zeta1m1 * alpha1 * (zeta - omega ^ (n - 3))
    + zeta1m1 * alpha2 * (zeta - 1)) * (1 - zZeta)
  let afterZk := afterDenom + numerator * denomInv
  afterZk - linConstTerm

/-- **`ftEval0R_eq`** — with `denomInv = denominator⁻¹` the C5 mirror IS the shipped `ftEval0`,
for every field (`zkPolyR = zkPoly`, `numerator·denomInv = numerator·denominator⁻¹`). -/
theorem ftEval0R_eq {K : Type} [Field K] (n : Nat) (omega zeta beta gamma alpha0 alpha1 alpha2 : K)
    (w s shift : List K) (zZeta zZetaOmega pZeta linConstTerm : K) :
    ftEval0R n omega zeta beta gamma alpha0 alpha1 alpha2 w s shift zZeta zZetaOmega pZeta
        linConstTerm (((zeta - omega ^ (n - 3)) * (zeta - 1))⁻¹)
      = ftEval0 n omega zeta beta gamma alpha0 alpha1 alpha2 w s shift zZeta zZetaOmega pZeta
        linConstTerm := rfl

/-- **`kimchiVerifyDecisionField`** — the composed decision that now CONSUMES the real field values.
It is the shipped `kimchiVerifyDecision` (C1 + carriers) conjoined with (C8) the aggregation check
`cipClaimed = combinedInnerProduct`, (C5-inv) the witnessed-inverse check that `denomInv` is the
genuine inverse of the C5 denominator `(ζ−ω^{n−3})(ζ−1)`, and (C5) the check
`ftEval0Claimed = ft(ζ)`. Over `[CommRing R] [DecidableEq R]`, so it runs at `ZMod pN`. -/
def kimchiVerifyDecisionField {R : Type} [CommRing R] [DecidableEq R]
    (prevLen publicLen wLen sLen coeffLen tCommLen chunkSize n : Nat)
    (polyscale evalscale : R) (evZeta evZetaOmega : List R) (cipClaimed : R)
    (omega zeta beta gamma alpha0 alpha1 alpha2 : R)
    (w s shift : List R) (zZeta zZetaOmega pZeta linConstTerm denomInv ftEval0Claimed : R)
    (transcriptOk ipaOk deferralOk : Bool) : Bool :=
  kimchiVerifyDecision prevLen publicLen wLen sLen coeffLen tCommLen chunkSize
      transcriptOk ipaOk deferralOk
  && decide (cipR polyscale evalscale evZeta evZetaOmega = cipClaimed)                     -- C8
  && decide (((zeta - omega ^ (n - 3)) * (zeta - 1)) * denomInv = 1)                        -- witnessed inverse
  && decide (ftEval0R n omega zeta beta gamma alpha0 alpha1 alpha2 w s shift
       zZeta zZetaOmega pZeta linConstTerm denomInv = ftEval0Claimed)                       -- C5

/-- **`kimchiVerifyDecisionField_refines`** — the composed field decision IS the shape/carrier
decision conjoined with the three field-arithmetic checks (`rfl`): the field checks are ADDED to
`kimchiVerifyDecision`, they do not replace it. -/
theorem kimchiVerifyDecisionField_refines {R : Type} [CommRing R] [DecidableEq R]
    (prevLen publicLen wLen sLen coeffLen tCommLen chunkSize n : Nat)
    (polyscale evalscale : R) (evZeta evZetaOmega : List R) (cipClaimed : R)
    (omega zeta beta gamma alpha0 alpha1 alpha2 : R)
    (w s shift : List R) (zZeta zZetaOmega pZeta linConstTerm denomInv ftEval0Claimed : R)
    (transcriptOk ipaOk deferralOk : Bool) :
    kimchiVerifyDecisionField prevLen publicLen wLen sLen coeffLen tCommLen chunkSize n
        polyscale evalscale evZeta evZetaOmega cipClaimed omega zeta beta gamma alpha0 alpha1 alpha2
        w s shift zZeta zZetaOmega pZeta linConstTerm denomInv ftEval0Claimed
        transcriptOk ipaOk deferralOk
      = (kimchiVerifyDecision prevLen publicLen wLen sLen coeffLen tCommLen chunkSize
            transcriptOk ipaOk deferralOk
          && decide (cipR polyscale evalscale evZeta evZetaOmega = cipClaimed)
          && decide (((zeta - omega ^ (n - 3)) * (zeta - 1)) * denomInv = 1)
          && decide (ftEval0R n omega zeta beta gamma alpha0 alpha1 alpha2 w s shift
               zZeta zZetaOmega pZeta linConstTerm denomInv = ftEval0Claimed)) := rfl

/-! ## §9c — C6: the GATE-CONSTRAINT linearization constant term (retiring the `linConstTerm`
carrier for the gates a real proof uses).

`linConstTerm = PolishToken::evaluate(index.linearization.constant_term)` (`verifier.rs:479-487`).
Crucially `assert_eq!(linearization.index_terms.len(), 0)` (`linearization.rs:364`): every column
(witness, coefficients, `z`, all selectors) is evaluated, so the WHOLE linearization is the constant
term — there are NO commitment/index terms. And `constraints_expr` (`linearization.rs:45-243`) is the
sum over GATES only — Poseidon + VarBaseMul + CompleteAdd + EndosclMul + EndomulScalar + optional +
Generic + lookups; the PERMUTATION is NOT in it (it is the by-hand σ-fold of `ftEval0` above). So

  `linConstTerm = Σ_gate index(gate)·(Σ_i alpha^i·constraint_{gate,i}) + lookups`

(`argument.rs:207` `index(gate)·combined_constraints`, `expr.rs:1633` `combine_constraints` =
`Σ_i alpha^{αᵢ}·cᵢ`). The gate alpha blocks are shared (`ArgumentType::Gate`, mutually exclusive —
`argument.rs:26-30`), registered as `VarbaseMul::CONSTRAINTS = 21` (`linearization.rs:57-60`), so the
GENERIC gate is at alpha⁰/alpha¹ (`linearization.rs:223-229`) and the permutation at alpha²¹⁺
(A0/A1/A2). We transcribe the generic gate constraint fully and the Poseidon gate constraint as a
def-generator, and expose the per-gate SELECTOR gating: a proof whose custom selectors vanish has its
`linConstTerm` DERIVED from the generic gate alone. -/

/-- **`genericGateConstraint`** — the double-generic gate constraint (`generic.rs:83-120`), scaled by
the generic selector and alpha-combined: `genSel·(constraint1 + alpha·constraint2)` where
`constraintₖ = c_{5k}·w_{3k} + c_{5k+1}·w_{3k+1} + c_{5k+2}·w_{3k+2} + c_{5k+3}·w_{3k}·w_{3k+1}
+ c_{5k+4}` (the two 5-coefficient generics l,r,o,m,c). `coeff` = the 15 coefficient evals at ζ
(only 0..9 used), `w` = the 15 witness evals at ζ (only 0..5 used). Field/CommRing-generic — this is
the emitted gate constraint that `ftEval0` subtracts, no longer a carrier. -/
def genericGateConstraint {R : Type} [CommRing R] (genSel alpha : R) (coeff w : List R) : R :=
  let c := fun i => coeff.getD i (0 : R)
  let ww := fun i => w.getD i (0 : R)
  let constraint1 := c 0 * ww 0 + c 1 * ww 1 + c 2 * ww 2 + c 3 * (ww 0 * ww 1) + c 4
  let constraint2 := c 5 * ww 3 + c 6 * ww 4 + c 7 * ww 5 + c 8 * (ww 3 * ww 4) + c 9
  genSel * (constraint1 + alpha * constraint2)

/-- The double-generic gate constraint as a `PolishToken` stream (extends §5's `genericGateToks` to
the full two-generic + alpha-fold + selector scaling). Establishes the C6 evaluator computes the real
`generic.rs` polynomial as a token machine, not just an algebraic def. -/
def genericConstraintToks (genSel alpha c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 w0 w1 w2 w3 w4 w5 : F) :
    List (Tok F) :=
  [ .lit c0, .cell w0, .mul
  , .lit c1, .cell w1, .mul, .add
  , .lit c2, .cell w2, .mul, .add
  , .lit c3, .cell w0, .cell w1, .mul, .mul, .add
  , .lit c4, .add                                       -- constraint1 on the stack
  , .lit c5, .cell w3, .mul
  , .lit c6, .cell w4, .mul, .add
  , .lit c7, .cell w5, .mul, .add
  , .lit c8, .cell w3, .cell w4, .mul, .mul, .add
  , .lit c9, .add                                       -- constraint2 on top
  , .lit alpha, .mul, .add                              -- constraint1 + alpha·constraint2
  , .lit genSel, .mul ]                                 -- · genSel

/-- **`genericConstraint_evaluates`** — the token machine reduces the transcribed generic-gate stream
to the exact `generic.rs` double-generic polynomial. -/
theorem genericConstraint_evaluates (genSel alpha c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 w0 w1 w2 w3 w4 w5 : F) :
    evalToks (genericConstraintToks genSel alpha c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 w0 w1 w2 w3 w4 w5)
      = genSel * ((c0 * w0 + c1 * w1 + c2 * w2 + c3 * (w0 * w1) + c4)
          + alpha * (c5 * w3 + c6 * w4 + c7 * w5 + c8 * (w3 * w4) + c9)) := by
  simp only [evalToks, genericConstraintToks, List.foldl_cons, List.foldl_nil, stepTok]; ring

/-- Kimchi Poseidon S-box `x⁷` (`PlonkSpongeConstantsKimchi::PERM_SBOX = 7`, `poseidon.rs:375`). -/
def posSbox {R : Type} [CommRing R] (x : R) : R := x ^ (7 : Nat)

/-- **`poseidonLaneConstraint`** — one lane of one Poseidon round-equation constraint
(`poseidon.rs:364-420`): `target − (rc + Σ_c mds[j][c]·sbox(source_c))`, zero iff the round output
matches. `mdsRow` = the 3 MDS entries of row `j` (K3's `PastaPoseidon.mdsN[j]`), `rc` the round
constant, `source`/`target` the input/output lane evals. Def-generator; the full 15 constraints
(5 rounds × 3 lanes, alpha⁰..alpha¹⁴ in the shared gate block, × `poseidon_selector`) are the
mechanical repeat over `ROUND_EQUATIONS`. Poseidon is the highest-value custom gate (Mina uses it
heavily), but a proof with `poseidon_selector = 0` does not exercise it (see §12). -/
def poseidonLaneConstraint {R : Type} [CommRing R]
    (mdsRow : List R) (rc : R) (source : List R) (target : R) : R :=
  target - (rc + (mdsRow.getD 0 0 * posSbox (source.getD 0 0)
                + mdsRow.getD 1 0 * posSbox (source.getD 1 0)
                + mdsRow.getD 2 0 * posSbox (source.getD 2 0)))

/-- **`gateLinConst`** — the gate contribution to `linConstTerm`, per-gate = selector · body. The
GENERIC gate body is the fully-transcribed `genericGateConstraint`; the CUSTOM gates
(poseidon/complete_add/varbasemul/endomul/endomul_scalar) enter as `selector · body` with the body a
NAMED carrier (`*Body`) — but multiplied by the gate's selector, exactly the shape of `linearize`'s
`index(gate)·combined` with `index_terms = []`. So a proof whose custom selectors are all zero has
`gateLinConst = genericGateConstraint` for ANY custom bodies: its `linConstTerm` is DERIVED from the
generic gate constraint, not carried. -/
def gateLinConst {R : Type} [CommRing R] (genSel alpha : R) (coeff w : List R)
    (posSel posBody caddSel caddBody mulSel mulBody emulSel emulBody emulScalarSel emulScalarBody : R) :
    R :=
  genericGateConstraint genSel alpha coeff w
  + posSel * posBody + caddSel * caddBody + mulSel * mulBody
  + emulSel * emulBody + emulScalarSel * emulScalarBody

/-- **`kimchiVerifyDecisionGates`** — `kimchiVerifyDecisionField` (§9b) with the C5 linearization
constant term DERIVED from the transcribed gate constraints (`gateLinConst`) instead of fed as the
`linConstTerm` carrier. Now `ftEval0` is checked from the REAL generic-gate constraint over the real
coefficient/witness evals + the selector-gated custom contributions. -/
def kimchiVerifyDecisionGates {R : Type} [CommRing R] [DecidableEq R]
    (prevLen publicLen wLen sLen coeffLen tCommLen chunkSize n : Nat)
    (polyscale evalscale : R) (evZeta evZetaOmega : List R) (cipClaimed : R)
    (omega zeta beta gamma alpha0 alpha1 alpha2 alpha : R)
    (w s shift coeff : List R)
    (genSel posSel caddSel mulSel emulSel emulScalarSel : R)
    (posBody caddBody mulBody emulBody emulScalarBody : R)
    (zZeta zZetaOmega pZeta denomInv ftEval0Claimed : R)
    (transcriptOk ipaOk deferralOk : Bool) : Bool :=
  kimchiVerifyDecisionField prevLen publicLen wLen sLen coeffLen tCommLen chunkSize n
    polyscale evalscale evZeta evZetaOmega cipClaimed
    omega zeta beta gamma alpha0 alpha1 alpha2 w s shift
    zZeta zZetaOmega pZeta
    (gateLinConst genSel alpha coeff w posSel posBody caddSel caddBody mulSel mulBody
      emulSel emulBody emulScalarSel emulScalarBody)
    denomInv ftEval0Claimed transcriptOk ipaOk deferralOk

/-- **`kimchiVerifyDecisionGates_refines`** — the gate-derived decision IS `kimchiVerifyDecisionField`
with `linConstTerm := gateLinConst …` (`rfl`): the gate transcription is threaded INTO the accept, it
does not replace the field decision. -/
theorem kimchiVerifyDecisionGates_refines {R : Type} [CommRing R] [DecidableEq R]
    (prevLen publicLen wLen sLen coeffLen tCommLen chunkSize n : Nat)
    (polyscale evalscale : R) (evZeta evZetaOmega : List R) (cipClaimed : R)
    (omega zeta beta gamma alpha0 alpha1 alpha2 alpha : R)
    (w s shift coeff : List R)
    (genSel posSel caddSel mulSel emulSel emulScalarSel : R)
    (posBody caddBody mulBody emulBody emulScalarBody : R)
    (zZeta zZetaOmega pZeta denomInv ftEval0Claimed : R)
    (transcriptOk ipaOk deferralOk : Bool) :
    kimchiVerifyDecisionGates prevLen publicLen wLen sLen coeffLen tCommLen chunkSize n
        polyscale evalscale evZeta evZetaOmega cipClaimed
        omega zeta beta gamma alpha0 alpha1 alpha2 alpha w s shift coeff
        genSel posSel caddSel mulSel emulSel emulScalarSel
        posBody caddBody mulBody emulBody emulScalarBody
        zZeta zZetaOmega pZeta denomInv ftEval0Claimed transcriptOk ipaOk deferralOk
      = kimchiVerifyDecisionField prevLen publicLen wLen sLen coeffLen tCommLen chunkSize n
          polyscale evalscale evZeta evZetaOmega cipClaimed
          omega zeta beta gamma alpha0 alpha1 alpha2 w s shift
          zZeta zZetaOmega pZeta
          (gateLinConst genSel alpha coeff w posSel posBody caddSel caddBody mulSel mulBody
            emulSel emulBody emulScalarSel emulScalarBody)
          denomInv ftEval0Claimed transcriptOk ipaOk deferralOk := rfl

/-! ## §9d — C3 (phase 2): the Fr-sponge INSTANTIATED over `Fp = pN` (K3's permutation).

`ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi>` (`reality_gate_export.rs:47`) is
K3's Poseidon-over-Fp sponge: `oracles()` builds it `EFrSponge::from(G::sponge_params())`
(`verifier.rs:284`) and `Vesta::sponge_params() = mina_poseidon::pasta::fp_kimchi::static_params()`
(`curve.rs:63-64`) — the SAME `fp_kimchi` params `PastaPoseidon` baked (K3's `mdsN`/`rcsN`). So the
phase-2 Fr-sponge IS `PastaPoseidon.Ref.hash` over the `Fp` absorb stream.

(NB the §12 residual / task "Fr-sponge over qN" label was the same `Fp`/`Fq` mislabel the reality gate
corrected: the Fr-sponge is over `Fp = pN`, K3's field; the `qN` `Fq`-sponge is PHASE 1
(`other_curve_sponge_params = fq_kimchi`, `curve.rs:67-69`), absorbing curve points.)

Phase-2 absorb schedule (`verifier.rs:283-393`), in order: `digest` (the fq-sponge digest),
`prev_challenge_digest` (`= Ref.hash []` when `prev_challenges = []`), `ft_eval1`, `public_evals[ζ]`,
`public_evals[ζω]`, then `absorb_evaluations` (`plonk_sponge.rs:88-155`): for each point of
`frEvalPointOrder`, absorb `p.ζ` then `p.ζω`. Then `challenge()` → v'/u' (each = low-128-bits of ONE
raw squeeze, `sponge.rs:265-277`) → `to_field(endo_r)` → v/u.

(The §2/§3 `transcriptSchedule` sketched this combined phase with `ft_eval1` AFTER the public evals
and no prev-challenge digest; the precise `oracles()` order — used here to instantiate the sponge —
is `ft_eval1` THEN the public evals, preceded by the prev-challenge digest. The proven `squeeze_order`
is unaffected, depending only on the six squeezes.) -/

open Dregg2.Circuit.Emit.PastaPoseidon

/-- The `absorb_evaluations` point (`plonk_sponge.rs:88-99`). -/
inductive FrPt where
  | z | genericSel | poseidonSel | completeAddSel | mulSel | emulSel | endomulScalarSel
  | w (i : Nat) | coeff (i : Nat) | sigma (i : Nat)
  deriving DecidableEq, Repr

/-- **`frEvalPointOrder`** — the EXACT `absorb_evaluations` point order (`plonk_sponge.rs:88-99`):
`z`, the 6 gate selectors, the 15 witness columns, the 15 coefficient columns, the 6 σ columns
(the 7th σ is a commitment, not evaluated). Each point contributes `p.ζ` then `p.ζω` to the stream. -/
def frEvalPointOrder : List FrPt :=
  [FrPt.z, .genericSel, .poseidonSel, .completeAddSel, .mulSel, .emulSel, .endomulScalarSel]
  ++ (List.range COLUMNS).map FrPt.w
  ++ (List.range COLUMNS).map FrPt.coeff
  ++ (List.range (PERMUTS - 1)).map FrPt.sigma

/-- **`frEvalPointOrder_head`** — the leading `z` + six-selector order is exactly `plonk_sponge.rs`'s. -/
theorem frEvalPointOrder_head :
    frEvalPointOrder.take 7 =
      [FrPt.z, .genericSel, .poseidonSel, .completeAddSel, .mulSel, .emulSel, .endomulScalarSel] := by
  decide

/-- The Fr-sponge phase-2 absorb list over `Fp` (as `Nat`, K3's field-arithmetic reference): the
fq-sponge `digest` (an input — §12 residual), the prev-challenge digest `Ref.hash []`, `ft_eval1`,
the two public evals, then the `absorb_evaluations` column evals in `frEvalPointOrder` (ζ then ζω per
point). `evZeta`/`evZetaOmega` are the column evals IN `frEvalPointOrder` order. -/
def frPhase2Inputs (digest ftEval1 pZeta pZetaOmega : Nat) (evZeta evZetaOmega : List Nat) :
    List Nat :=
  [digest, Ref.hash [], ftEval1, pZeta, pZetaOmega]
  ++ (List.range evZeta.length).flatMap (fun i => [evZeta.getD i 0, evZetaOmega.getD i 0])

/-- **`frSpongeDigest`** — the Fr-sponge's raw field digest after the phase-2 absorbs
(`fr_sponge.digest()` = ONE Poseidon squeeze, `plonk_sponge.rs:51-53` = `sponge.squeeze()`), which is
`PastaPoseidon.Ref.hash` of the absorb stream (o1js `Poseidon.hash` = the same absorb-then-squeeze).
The `challenge()` derivation (low-128-bit truncation + `to_field(endo_r)`) sits on top — the §12
residual. -/
def frSpongeDigest (digest ftEval1 pZeta pZetaOmega : Nat) (evZeta evZetaOmega : List Nat) : Nat :=
  Ref.hash (frPhase2Inputs digest ftEval1 pZeta pZetaOmega evZeta evZetaOmega)

/-! ## §10 — NON-VACUITY: every check DISCRIMINATES (kernel-clean).

The composed decision + the shape check reduce under `decide` (pure `Nat`/`Bool`); the field
formulas reduce over `ℚ`. Good witnesses ACCEPT; each single tamper REJECTS. -/

/-- A canonical v1 shape: (prevLen 0, public 3, w 15, σ 6, coeff 15, t_comm 7, chunk 1). -/
def goodShape : Nat × Nat × Nat × Nat × Nat × Nat × Nat := (0, 3, 15, 6, 15, 7, 1)

/-- **`kimchi_decision_discriminates`** — accepts the good witness; rejects each single tamper of
C1 (bad prev-len / wrong w-count / over-long t_comm / no public / bad chunk), C3, C9-accept,
C9-deferral. (Arg order: prevLen publicLen wLen sLen coeffLen tCommLen chunkSize | 3 Bools.) -/
theorem kimchi_decision_discriminates :
    kimchiVerifyDecision 0 3 15 6 15 7 1 true true true = true
    ∧ kimchiVerifyDecision 1 3 15 6 15 7 1 true true true = false   -- prev-len ≠ 0 (recursion)
    ∧ kimchiVerifyDecision 0 3 14 6 15 7 1 true true true = false   -- wrong w-count
    ∧ kimchiVerifyDecision 0 3 15 6 15 8 1 true true true = false   -- t_comm too long (8 > 7·1)
    ∧ kimchiVerifyDecision 0 0 15 6 15 7 1 true true true = false   -- no public input
    ∧ kimchiVerifyDecision 0 3 15 6 15 7 2 true true true = false   -- chunk ≠ 1
    ∧ kimchiVerifyDecision 0 3 15 6 15 7 1 false true true = false  -- transcript mismatch
    ∧ kimchiVerifyDecision 0 3 15 6 15 7 1 true false true = false  -- IPA reject
    ∧ kimchiVerifyDecision 0 3 15 6 15 7 1 true true false = false := by  -- deferral not recorded
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### The field formulas reduce + discriminate over ℚ (fidelity of the transcription). -/

-- C8: positive anchor (polyscale = evalscale = 1, single poly `[a],[b]` ⇒ `a + b`) + discrimination.
#guard decide (combinedInnerProduct (1 : ℚ) 1 [5] [7] = 12)
#guard decide (combinedInnerProduct (2 : ℚ) 3 [5, 4] [7, 1] = (5 + 3 * 7) + 2 * (4 + 3 * 1))
#guard decide (combinedInnerProduct (2 : ℚ) 3 [5, 4] [7, 1]
  ≠ combinedInnerProduct (2 : ℚ) 3 [5, 9] [7, 1])   -- bumping an eval changes cip

-- C4: collapse (empty public ⇒ 0) + discrimination (a nonzero public entry moves it).
#guard decide (publicEval 4 (2 : ℚ) 3 [] = 0)
#guard decide (publicEval 4 (2 : ℚ) 3 [1, 1] ≠ publicEval 4 (2 : ℚ) 3 [1, 2])

-- C5/C6: ftEval0 discriminates on a witness eval, a σ eval, a challenge, and the linConstTerm.
private def ftArgs : List ℚ × List ℚ × List ℚ := ([2,3,5,7,11,13,17,19,23,29,31,37,41,43,47], [2,3,5,7,11,13], [1,1,1,1,1,1,1])
#guard decide (
  ftEval0 8 (2:ℚ) 3 5 7 1 1 1 ftArgs.1 ftArgs.2.1 ftArgs.2.2 4 6 8 9
  ≠ ftEval0 8 (2:ℚ) 3 5 7 1 1 1 (ftArgs.1.set 0 99) ftArgs.2.1 ftArgs.2.2 4 6 8 9)  -- bump w₀
#guard decide (
  ftEval0 8 (2:ℚ) 3 5 7 1 1 1 ftArgs.1 ftArgs.2.1 ftArgs.2.2 4 6 8 9
  ≠ ftEval0 8 (2:ℚ) 3 5 7 1 1 1 ftArgs.1 (ftArgs.2.1.set 0 99) ftArgs.2.2 4 6 8 9)  -- bump σ₀
#guard decide (
  ftEval0 8 (2:ℚ) 3 5 7 1 1 1 ftArgs.1 ftArgs.2.1 ftArgs.2.2 4 6 8 9
  ≠ ftEval0 8 (2:ℚ) 3 5 7 1 1 1 ftArgs.1 ftArgs.2.1 ftArgs.2.2 4 6 8 99) -- bump linConstTerm

-- C5: permScalar is the negated fold; it discriminates on β and on a σ eval.
#guard decide (permScalar 8 (2:ℚ) 3 5 7 1 ftArgs.1 ftArgs.2.1 6
  ≠ permScalar 8 (2:ℚ) 3 99 7 1 ftArgs.1 ftArgs.2.1 6)

-- C6: the generic-gate token machine computes the exact `generic.rs` polynomial (proven above) —
-- a concrete anchor: `2·3 + 5·7 + 11·13 + 17·(3·7) + 23 = 6+35+143+357+23 = 564`.
theorem genericGate_kat : evalToks (genericGateToks (2:ℚ) 5 11 17 23 3 7 13) = 564 := by
  rw [genericGate_evaluates]; norm_num

-- C6 (§9c): the FULL double-generic token machine computes `genSel·(c1 + alpha·c2)` (proven above);
-- a concrete anchor + non-vacuity of `genericGateConstraint` on the coefficient/witness evals.
theorem genericConstraint_kat :
    evalToks (genericConstraintToks (2:ℚ) 3 5 7 11 13 17 19 23 29 31 37 41 43 47 53 59 61) =
      2 * ((5 * 41 + 7 * 43 + 11 * 47 + 13 * (41 * 43) + 17)
        + 3 * (19 * 53 + 23 * 59 + 29 * 61 + 31 * (53 * 59) + 37)) := by
  rw [genericConstraint_evaluates]
#guard decide (genericGateConstraint (2:ℚ) 3 [5,7,11,13,17,19,23,29,31,37] [41,43,47,53,59,61]
  ≠ genericGateConstraint (2:ℚ) 3 [5,7,11,13,17,19,23,29,31,37] [99,43,47,53,59,61])  -- bump w₀
#guard decide (genericGateConstraint (2:ℚ) 3 [5,7,11,13,17,19,23,29,31,37] [41,43,47,53,59,61]
  ≠ genericGateConstraint (2:ℚ) 3 [99,7,11,13,17,19,23,29,31,37] [41,43,47,53,59,61])  -- bump c₀
-- gateLinConst: with all custom selectors zero it collapses to the generic gate (any bodies).
#guard decide (gateLinConst (2:ℚ) 3 [5,7,11,13,17,19,23,29,31,37] [41,43,47,53,59,61]
    0 100 0 200 0 300 0 400 0 500
  = genericGateConstraint (2:ℚ) 3 [5,7,11,13,17,19,23,29,31,37] [41,43,47,53,59,61])

-- C6 Poseidon (§9c): the round-equation lane constraint is zero on an honest round, nonzero on a bump.
#guard decide (poseidonLaneConstraint ([2,3,5] : List ℚ) 7 [11,13,17]
  (7 + (2*(11^7) + 3*(13^7) + 5*(17^7))) = 0)
#guard decide (poseidonLaneConstraint ([2,3,5] : List ℚ) 7 [11,13,17]
  (7 + (2*(11^7) + 3*(13^7) + 5*(17^7)) + 1) ≠ 0)

-- C3 (§9d): the Fr-sponge phase-2 point order has the right length (1 z + 6 selectors + 15 w +
-- 15 coeff + 6 σ = 43) and the K3 Fr-sponge digest discriminates on absorbed real-shaped values.
#guard frEvalPointOrder.length == 1 + 6 + COLUMNS + COLUMNS + (PERMUTS - 1)
#guard decide (Ref.hash [Ref.hash [], 1, 2, 3, 4] ≠ Ref.hash [Ref.hash [], 1, 99, 3, 4])

-- C7: Maller's ft-commitment over `G = F = ℚ`: `ftComm = fComm − (ζⁿ−1)·tComm` (55 = 100 − 15·3).
theorem ftComm_kat : ftComm (G := ℚ) 4 (2:ℚ) 100 3 = 55 := by
  rw [ftComm]; norm_num [smul_eq_mul]

-- C9: `ipaB0 = b(ζ) + evalscale·b(ζω)` over K4c's `bEval`; discriminates on a round challenge.
#guard decide (ipaB0 (3:ℚ) 5 7 [2, 4]
  ≠ ipaB0 (3:ℚ) 5 7 [2, 9])
-- C9: the deferral is recorded — `k` challenges ⇒ `2^k` deferred terms (via K4c).
#guard ipaDeferralOk (absorbChallenges (⟨[], (0,0,0)⟩ : IpaDeferred ℚ (Nat×Nat×Nat)) [1,2,3]) 3 == true
#guard ipaDeferralOk (absorbChallenges (⟨[], (0,0,0)⟩ : IpaDeferred ℚ (Nat×Nat×Nat)) [1,2,3]) 4 == false

/-! ### C3 order — the squeeze schedule is exactly the verifier order (kernel-clean). -/

#guard decide (squeezes transcriptSchedule =
  [(Chal.beta, false), (Chal.gamma, false), (Chal.alpha, true),
   (Chal.zeta, true), (Chal.v, true), (Chal.u, true)])
#guard transcriptSchedule.length == 2 + COLUMNS + 6 + 4 + 7 + COLUMNS + COLUMNS + (PERMUTS - 1) + 2
-- C3 sponge realization tie: the K3 transcript sponge runs on a transcript-shaped absorb and
-- squeezes a determinate (nonzero) Fp challenge — the phase-1 Fq-sponge is K3's `Ref.hash`.
#guard decide (Dregg2.Circuit.Emit.PastaPoseidon.Ref.hash [1, 2, 3] ≠ 0)

/-! ## §11 — Axiom hygiene. -/

#assert_axioms squeeze_order
#assert_axioms absorbs_before_beta
#assert_axioms genericGate_evaluates
#assert_axioms deferral_records
#assert_axioms kimchiVerifyDecision_refines
#assert_axioms kimchi_decision_discriminates
#assert_axioms cipR_eq
#assert_axioms ftEval0R_eq
#assert_axioms kimchiVerifyDecisionField_refines
#assert_axioms genericConstraint_evaluates
#assert_axioms kimchiVerifyDecisionGates_refines
#assert_axioms frEvalPointOrder_head

/-! ## §12 — The PRECISE named residuals (what does NOT compose end-to-end).

  1. **The IPA/FRI soundness floor is NOT discharged.** `ipaOk` (the `msm == 0` accept,
     `ipa.rs:501`) is a CARRIER: `accept ⟹ the proof is valid` inherits the undischarged IPA
     opening soundness (a STARK proves the trace, not the opening). No `no_forgery`-style payoff
     is claimed (contrast `ethVerifyDecision_no_forgery`, which had the hash-CR carriers only).
  2. **C6 GENERIC gate: TRANSCRIBED + COMPOSED (2026-07-27).** The generic gate constraint is now
     fully emitted (`genericGateConstraint`, both algebraically and as the token stream
     `genericConstraintToks`/`genericConstraint_evaluates`) and threaded INTO the accept via
     `gateLinConst` + `kimchiVerifyDecisionGates` (§9c): `ftEval0`'s linearization constant term is
     DERIVED from the real generic-gate constraint over the real coefficient/witness evals, not fed
     as the `linConstTerm` carrier. `KimchiRealProofGate` shows `genericGateConstraint(real) = LCT`
     and the custom selectors are all zero, so the whole `linConstTerm` of THIS proof is the generic
     gate. STILL CARRIED: the CUSTOM-gate constraint BODIES — Poseidon is transcribed as a
     def-generator (`poseidonLaneConstraint`, the round-equation lane) but is NOT exercised
     (`poseidon_selector = 0` in this proof); complete_add/varbasemul/endomul/endomul_scalar bodies
     are the `gateLinConst` `*Body` carriers, live only behind their (here-zero) selectors. A proof
     that fires a custom gate needs those bodies emitted.
  3. **C3 Fr-sponge (phase 2): INSTANTIATED over `Fp = pN` (2026-07-27).** The Fr-sponge IS K3's
     Poseidon-over-Fp sponge (`Vesta::sponge_params() = fp_kimchi`, `curve.rs:63`), NOT a mirror at
     another field — `frSpongeDigest = Ref.hash` of the phase-2 absorb stream (§9d), whose point
     order (`frEvalPointOrder`) matches `plonk_sponge.rs:88-99`. STILL CARRIED: the fq-sponge
     `digest` VALUE (phase-1 `Fq`-sponge over `qN`, absorbing curve points — not extracted) fed as
     the first absorb, and the `challenge()` derivation (low-128-bit truncation of the raw squeeze +
     `to_field(endo_r)`, `sponge.rs:190-226`) that maps the sponge digest to v/u. The ORDER
     (`squeeze_order` + `frEvalPointOrder`) is proven; the digest value + endo map are named.
  4. **The field-arithmetic checks are over `F`, above the felt encoding.** The `ℤ ↔ p_felt`
     field-width gap (K1 §6) and the `z < p` canonical compare are the shared residuals. The real
     field is `Fp = ZMod pN` (Vesta::ScalarField); there is no `Field (ZMod pN)` instance in the
     tree, so §9b runs the C5/C8 checks over `ZMod pN` AS A `CommRing` with a WITNESSED inverse
     (`kimchiVerifyDecisionField`), evaluated on real values in `KimchiRealProofGate`.
  5. **The field-value composition (C5/C8) IS now inside one accept** (`kimchiVerifyDecisionField`,
     §9b, `refines`-tied to `kimchiVerifyDecision`), evaluated end-to-end on a REAL proof over
     `ZMod pN` in `KimchiRealProofGate`. What remains carried in that accept: the C3/C9 crypto
     carriers, C4 `p(ζ)` fed as an input (its Lagrange-denominator recomputation not extracted),
     and C7 `ftComm`/`permScalar` (commitment/MSM-valued, the K2 carrier — not field-value checks).
     The batch assembly (`assembleBatch`: the ordered eval list feeding `cip`, the `Evaluation`
     pairing `verifier.rs:967-1181`) is the plumbing the carriers consume.
  6. **Out of v1 scope:** Pickles recursion (the `sg` split's terminal discharge), proof BATCHING
     (`prevLen = 0`, single proof), and lookups/Plookup (C10, `lookup_index = None`).

CONTINUATION (K5+): discharge C6's baked token streams (emit them from Lean per gate), instantiate
the Fr-sponge, and thread the batch assembly — then the deferral is the ONLY remaining carrier
short of the terminal IPA soundness floor, which is the Pickles-recursion frontier.
-/

end Dregg2.Circuit.Emit.KimchiVerify
