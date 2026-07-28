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
    PROVEN as an enumerated-order theorem. §9d instantiates the PHASE-2 Fr-sponge as K3's
    Poseidon-over-Fp sponge and §9e builds the `challenge()` truncation + the endo map, so **v and u
    are RE-DERIVED end-to-end** from the transcript and α, ζ from their prechallenges. The PHASE-1
    Fq-sponge (over `qN`, `fq_kimchi` params, absorbing curve points) is the NAMED residual: it
    yields β, γ, α', ζ' and the `digest` that seeds phase 2.
  * **C4** public eval at ζ, ζω (`publicEval`) — the exact batch-inverted Lagrange formula
    (`verifier.rs:336-379`), field-generic, KAT'd (collapse + discrimination).
  * **C5** the permutation term of ft(ζ) + `permScalar` (`verifier.rs:411-462`,
    `permutation.rs:392-430`) — the copy-constraint z-poly identity, folded into `ftEval0`, REAL.
  * **C6** the linearization at ζ: a real `PolishToken` mini-evaluator (`evalToks`) + the GENERIC
    GATE constraint transcribed as a token stream (`genericGateToks`, `genericGate_evaluates`), the
    arithmetic core of `PolishToken::evaluate`. §9c.1 then transcribes ALL SIX v1 gate bodies
    (generic 2, Poseidon 15, complete_add 7, varbasemul 21, endomul 12, endomul_scalar 11) and
    `gateLinConst` sums them behind their selectors — `linConstTerm` is DERIVED, not carried.
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
counts, no crypto). Still frozen: no lookups, `chunk_size = 1`.

⚑ **THE `prevLen = 0` FREEZE IS RETIRED (2026-07-28).** Until now the first conjunct read
`decide (prevLen = 0)`, described as "v1: no Pickles recursion". That is not a weaker version of
the upstream check — it is a DIFFERENT check. `verifier.rs:810-813` compares the proof's
`prev_challenges.len()` against the VERIFIER INDEX's `prev_challenges`, and the object a Mina node
actually verifies carries **2** (`side_loaded_verification_key.ml:236`, Wrap_hack). So the frozen
form REFUSED the real object outright — measured and proven in `PicklesRecursion`
`wrap_prev_challenges_refused` (`5c1423632`), which this change supersedes.

The general check is `shapeOkRec`; `shapeOk` survives as its instantiation at a NON-RECURSIVE
index (`index.prev_challenges = 0`), which is what the existing single-proof fixtures are. It is a
parameter value now, not a wall. What `prev_challenges > 0` additionally OWES the verifier —
the commitments in the phase-1 transcript, the challenge digest in the phase-2 transcript, and the
b-poly evaluations at the head of the `combined_inner_product` poly list — is §2b/§7b below and is
CHECKED, not waived. -/

/-- **`shapeOkRec`** — every length/shape assert of `to_batch`'s preamble, with the REAL recursion
check: `proof.prev_challenges.len() == verifier_index.prev_challenges`
(`verifier.rs:810-813`, `VerifyError::IncorrectPrevChallengesLength`). -/
def shapeOkRec (idxPrevLen prevLen publicLen wLen sLen coeffLen tCommLen chunkSize : Nat) : Bool :=
  decide (prevLen = idxPrevLen)              -- verifier.rs:810-813 (was frozen at `= 0`)
  && decide (0 < publicLen)                  -- public input present (verifier.rs:816-820)
  && decide (wLen = COLUMNS)                 -- 15 witness commitments (verifier.rs:173-177)
  && decide (sLen = PERMUTS - 1)             -- 6 σ evaluations (verifier.rs:967-1181)
  && decide (coeffLen = COLUMNS)             -- 15 coefficient columns
  && decide (chunkSize = 1)                  -- v1: domain ≤ SRS (verifier.rs:823-830)
  && decide (tCommLen ≤ 7 * chunkSize)       -- t_comm length bound (verifier.rs:259-266)

/-- **`shapeOk`** — `shapeOkRec` at a verifier index that declares NO previous challenges. Every
single-proof fixture in this tree is that index; a Pickles Step/Wrap index is not. -/
def shapeOk (prevLen publicLen wLen sLen coeffLen tCommLen chunkSize : Nat) : Bool :=
  shapeOkRec 0 prevLen publicLen wLen sLen coeffLen tCommLen chunkSize

/-- **`shapeOk_is_shapeOkRec_at_zero`** — the specialization is definitional, so nothing that used
the frozen decision changed meaning. -/
theorem shapeOk_is_shapeOkRec_at_zero
    (prevLen publicLen wLen sLen coeffLen tCommLen chunkSize : Nat) :
    shapeOk prevLen publicLen wLen sLen coeffLen tCommLen chunkSize
      = shapeOkRec 0 prevLen publicLen wLen sLen coeffLen tCommLen chunkSize := rfl

/-- **`shapeOkRec_admits_pickles_counts`** — the general check ACCEPTS every `max_proofs_verified`
Pickles can declare (`pickles_base/proofs_verified.ml:5-17`: 0, 1, 2), and still REFUSES a proof
whose recursion count disagrees with its index — which is the actual attack the assert stops. -/
theorem shapeOkRec_admits_pickles_counts :
    shapeOkRec 0 0 3 COLUMNS (PERMUTS - 1) COLUMNS 7 1 = true
    ∧ shapeOkRec 1 1 3 COLUMNS (PERMUTS - 1) COLUMNS 7 1 = true
    ∧ shapeOkRec 2 2 3 COLUMNS (PERMUTS - 1) COLUMNS 7 1 = true
    ∧ shapeOkRec 2 1 3 COLUMNS (PERMUTS - 1) COLUMNS 7 1 = false
    ∧ shapeOkRec 2 0 3 COLUMNS (PERMUTS - 1) COLUMNS 7 1 = false
    ∧ shapeOkRec 0 2 3 COLUMNS (PERMUTS - 1) COLUMNS 7 1 = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

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
  deriving Repr, DecidableEq

/-- **`transcriptScheduleRec`** — the exact `ProverProof::oracles` order for a proof carrying
`nPrev` previous recursion challenges (no lookups). Fq-sponge phase (`verifier.rs:159-276`):
absorb the index digest, **the `nPrev` `RecursionChallenge` commitments** (`:165-168`), the public
commitment, the 15 w commitments, squeeze β (raw), γ (raw); absorb z_comm, squeeze α′ (endo);
absorb t_comm, squeeze ζ′ (endo). Fr-sponge phase (`verifier.rs:278-405`): absorb the fq-sponge
digest, **the prev-challenge digest** (`:290-299` — a FRESH Fr-sponge over every carried `chals`,
squeezed once), `ft_eval1` (`:381-382`), the public evals at [ζ, ζω] (`:391-392`), then all
evaluations in `absorb_evaluations` order (z, the 6 gate selectors, w[0..15], coefficients[0..15],
s[0..6], each ζ then ζω), squeeze v′ (endo), u′ (endo).

⚑ Two corrections land with the recursion argument, both against `verifier.rs` at `f6d958dc05`:
`ft_eval1` is absorbed **before** the public evaluations, not after (the previous listing had them
swapped, citing the right two line ranges in the wrong order); and the prev-challenge digest is
absorbed immediately after the fq digest — at `nPrev = 0` it is the digest of an EMPTY Fr-sponge,
which is why the v1 listing could omit it and still describe the right sponge state, and it is
`PastaPoseidon.Ref.hash []` exactly (`KimchiPoseidonGate` §6 pins that). -/
def transcriptScheduleRec (nPrev : Nat) : List Step :=
  [ .absorb "index_digest"                                  -- verifier.rs:161-163
  ] ++ (List.range nPrev).map (fun i => Step.absorb s!"prev_chal_comm[{i}]")  -- verifier.rs:165-168
  ++ [ .absorb "public_comm"                                -- verifier.rs:170-171
     ] ++ (List.range COLUMNS).map (fun i => Step.absorb s!"w_comm[{i}]")  -- verifier.rs:173-177
  ++ [ .squeeze .beta false                                 -- verifier.rs:232-233 (RAW)
     , .squeeze .gamma false                                -- verifier.rs:235-236 (RAW)
     , .absorb "z_comm"                                     -- verifier.rs:249-250
     , .squeeze .alpha true                                 -- verifier.rs:253-257 (endo)
     , .absorb "t_comm"                                     -- verifier.rs:259-269
     , .squeeze .zeta true                                  -- verifier.rs:272-276 (endo)
     , .absorb "fq_sponge_digest"                           -- verifier.rs:278-287 (Fr-sponge start)
     , .absorb "prev_challenge_digest"                      -- verifier.rs:290-299
     , .absorb "ft_eval1"                                   -- verifier.rs:381-382
     , .absorb "public_eval[zeta]"                          -- verifier.rs:391-392
     , .absorb "public_eval[zeta_omega]"
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

/-- **`transcriptSchedule`** — the schedule of a proof with no carried recursion challenges. -/
def transcriptSchedule : List Step := transcriptScheduleRec 0

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

/-- **`squeeze_order_rec`** — carrying recursion challenges does NOT reorder or add a squeeze: the
same six challenges in the same order with the same raw/endo flags. What changes is what the sponge
has eaten before each one. -/
theorem squeeze_order_rec :
    squeezes (transcriptScheduleRec 2) = squeezes transcriptSchedule := by decide

/-- **`absorbs_before_beta_rec`** — a Pickles-shaped proof (`prev_challenges = 2`,
`side_loaded_verification_key.ml:236`) absorbs TWO more commitments before β than a
non-recursive one, and they sit between the index digest and the public commitment. A verifier
that skipped them would sample a different β from the same proof. -/
theorem absorbs_before_beta_rec :
    ((transcriptScheduleRec 2).takeWhile
        (fun s => match s with | .squeeze _ _ => false | _ => true)).length = 2 + 2 + COLUMNS
    ∧ (transcriptScheduleRec 2).getD 1 (.absorb "?") = Step.absorb "prev_chal_comm[0]"
    ∧ (transcriptScheduleRec 2).getD 2 (.absorb "?") = Step.absorb "prev_chal_comm[1]"
    ∧ (transcriptScheduleRec 2).getD 3 (.absorb "?") = Step.absorb "public_comm" := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

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

/-! ## §7b — P6: the `RecursionChallenge` FOLD into C8 (`verifier.rs:311-327`; `proof.rs:459-494`).

This is the arithmetic content the `prevLen = 0` freeze was hiding. A proof carrying previous
recursion challenges does not merely *declare* them: each `RecursionChallenge { chals, comm }`
contributes a polynomial to the batched opening, and that polynomial is the **b-polynomial of its
own accumulated IPA challenges** — `RecursionChallenge::evals` is literally `b_poly(chals, x)` at
the two evaluation points (`proof.rs:472`, `commitment.rs:426-436`), which is K4c's `bEval`. Those
evaluations are **PREPENDED** to the `combined_inner_product` poly list, before the public
polynomial and before `ft` (`verifier.rs:496-500`: `es` is built from `polys` first, then
`es.push(public_evals)`, then `es.push([ft_eval0, ft_eval1])`).

So the fold is: `k` accumulated challenges ⇒ one b-poly ⇒ two evaluations ⇒ two leading entries of
the ξ-weighted sum. Nothing is deferred and nothing is assumed: the entries are RECOMPUTED from
the carried challenges and compared. `chunk_size = 1` is where `evals` returns the single
`vec![full]` (`proof.rs:470-471`, `max_poly_size = 2^k`); the chunked branch is out of v1 scope
exactly as it is for every other column. -/

/-- `sqIter k x = x ^ (2^k)`, by `k` squarings — the ladder `b_poly` ACTUALLY computes
(`commitment.rs:429-433`: `pow_twos[i] = pow_twos[i-1].square()`), and the only form a kernel can
evaluate at `k = 16`: `Monoid.npow` is unary, so `x ^ 2^15` is 32768 recursion steps. TAIL-recursive
on purpose — a naive `sqIter k x * sqIter k x` re-evaluates the base `2^k` times.

(Moved here from `PicklesRecursion` §P0.1, which is downstream and had the only copy; the C8
recursion fold below needs it, and two ladders that agree today are two that disagree later.) -/
def sqIter {R : Type} [Monoid R] : Nat → R → R
  | 0, x => x
  | k + 1, x => sqIter k (x * x)

/-- **`sqIter_eq`** — the ladder computes the power. -/
theorem sqIter_eq {R : Type} [Monoid R] : ∀ (k : Nat) (x : R), sqIter k x = x ^ (2 ^ k)
  | 0, x => by simp [sqIter]
  | k + 1, x => by
    show sqIter k (x * x) = x ^ (2 ^ (k + 1))
    rw [sqIter_eq k (x * x), ← pow_two, ← pow_mul]
    congr 1
    rw [pow_succ]
    omega

/-- **`bEvalSq`** — K4c's `bEval` with the exponents taken up the squaring ladder, i.e. the exact
shape of `b_poly` (`commitment.rs:426-436`). Tied to `bEval` by `bEvalSq_eq_bEval`, so this is a
COST change, not a semantic one. -/
def bEvalSq {R : Type} [CommRing R] (x : R) : List R → R
  | [] => 1
  | c :: rest => bEvalSq x rest * (1 + c * sqIter rest.length x)

/-- **`bEvalSq_eq_bEval`** — the ladder form IS K4c's b-polynomial, for every point and every
challenge list. So `sVec_eq_bPoly` (the identity tying `bEval` to the `2^k`-term deferred `⟨s,G⟩`
coefficient vector) applies to the value the fold check below computes. -/
theorem bEvalSq_eq_bEval {R : Type} [CommRing R] (x : R) :
    ∀ cs : List R, bEvalSq x cs = bEval x cs
  | [] => rfl
  | c :: rest => by
    show bEvalSq x rest * (1 + c * sqIter rest.length x)
      = bEval x rest * (1 + c * x ^ (2 ^ rest.length))
    rw [bEvalSq_eq_bEval x rest, sqIter_eq]

/-- **`prevChalEvals`** — the C8 prefix contributed by `prev_challenges`: one b-poly evaluation per
carried challenge set, at the point `x`. The value IS K4c's `bEval` (`bEvalSq_eq_bEval`), and
`sVec_eq_bPoly` is the theorem that it IS the `2^k`-term deferred `⟨s,G⟩` obligation's polynomial —
the same object, evaluated rather than materialized. -/
def prevChalEvals {R : Type} [CommRing R] (x : R) (chalss : List (List R)) : List R :=
  chalss.map (fun cs => bEvalSq x cs)

/-- **`prevChalEvals_is_bEval`** — spelled out: the prefix is K4c's b-polynomial, not a lookalike. -/
theorem prevChalEvals_is_bEval {R : Type} [CommRing R] (x : R) (chalss : List (List R)) :
    prevChalEvals x chalss = chalss.map (fun cs => bEval x cs) := by
  simp [prevChalEvals, bEvalSq_eq_bEval]

/-- **`prevChalFoldOk`** — the C8 check that retires the freeze: the leading `chalss.length`
entries of BOTH evaluation columns are exactly the b-poly evaluations of the carried challenges,
at ζ and at ζω. A prover that supplies its own numbers there — the whole point of getting the
recursion accepted — is refused. -/
def prevChalFoldOk {R : Type} [CommRing R] [DecidableEq R]
    (zeta zetaOmega : R) (chalss : List (List R)) (evZeta evZetaOmega : List R) : Bool :=
  decide (evZeta.take chalss.length = prevChalEvals zeta chalss)
  && decide (evZetaOmega.take chalss.length = prevChalEvals zetaOmega chalss)

/-- **`prevChalFoldOk_is_bEval`** — and therefore the CHECK is about `bEval`, stated so the
kernel-tractable form cannot drift away from the object K4c proved things about. -/
theorem prevChalFoldOk_is_bEval {R : Type} [CommRing R] [DecidableEq R]
    (zeta zetaOmega : R) (chalss : List (List R)) (evZeta evZetaOmega : List R) :
    prevChalFoldOk zeta zetaOmega chalss evZeta evZetaOmega
      = (decide (evZeta.take chalss.length = chalss.map (fun cs => bEval zeta cs))
         && decide (evZetaOmega.take chalss.length = chalss.map (fun cs => bEval zetaOmega cs))) := by
  simp [prevChalFoldOk, prevChalEvals_is_bEval]

/-- **`prevChalFoldOk_empty`** — at `prev_challenges = 0` the fold check is VACUOUSLY true, for
every claimed evaluation column. That is the honest statement of what the freeze bought: nothing.
It is stated so the recursive instantiation cannot be mistaken for a strengthening of the
non-recursive one. -/
theorem prevChalFoldOk_empty {R : Type} [CommRing R] [DecidableEq R]
    (zeta zetaOmega : R) (evZeta evZetaOmega : List R) :
    prevChalFoldOk zeta zetaOmega [] evZeta evZetaOmega = true := by
  simp [prevChalFoldOk, prevChalEvals]

/-- **`prevChalEvals_is_bPoly`** — the fold's per-proof block IS K4c's b-polynomial, so the C8
entries and the deferred `⟨s,G⟩` obligation of `PastaIPA` are two readings of ONE object, not two
models that happen to agree. -/
theorem prevChalEvals_is_bPoly {R : Type} [CommRing R] (x : R) (cs : List R) :
    prevChalEvals x [cs] = [bEval x cs] := by
  simp [prevChalEvals_is_bEval]

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

/-- **`kimchiVerifyDecisionRec`** — the composed Kimchi verify decision against a verifier index
that declares `idxPrevLen` previous challenges. -/
def kimchiVerifyDecisionRec (idxPrevLen prevLen publicLen wLen sLen coeffLen tCommLen chunkSize : Nat)
    (transcriptOk ipaOk deferralOk : Bool) : Bool :=
  shapeOkRec idxPrevLen prevLen publicLen wLen sLen coeffLen tCommLen chunkSize
  && transcriptOk && ipaOk && deferralOk

/-- **`kimchiVerifyDecision`** — the composed single-proof Kimchi verify decision, at a
non-recursive index. -/
def kimchiVerifyDecision (prevLen publicLen wLen sLen coeffLen tCommLen chunkSize : Nat)
    (transcriptOk ipaOk deferralOk : Bool) : Bool :=
  kimchiVerifyDecisionRec 0 prevLen publicLen wLen sLen coeffLen tCommLen chunkSize
    transcriptOk ipaOk deferralOk

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

/-- **`kimchiVerifyDecisionFieldRec`** — the P6 decision: the field decision above against a
verifier index declaring `idxPrevLen` previous challenges, with the `RecursionChallenge` fold
CHECKED. Two things are added and neither is optional:

* the shape assert becomes the real `prev_challenges.len() == index.prev_challenges`
  (`shapeOkRec`), so `prev_challenges = 2` is a value the decision can accept; and
* `prevChalFoldOk` — the leading `idxPrevLen` entries of the two C8 evaluation columns must BE the
  b-poly evaluations of the carried challenges at ζ and ζω, recomputed here.

`chalss` is the carried `[[chals]]`. At `chalss = []` the fold check is vacuous and this IS
`kimchiVerifyDecisionField` (`kimchiVerifyDecisionFieldRec_at_zero`), so nothing that ran before
runs differently; what is new is that a nonzero count is no longer a refusal. -/
def kimchiVerifyDecisionFieldRec {R : Type} [CommRing R] [DecidableEq R]
    (idxPrevLen prevLen publicLen wLen sLen coeffLen tCommLen chunkSize n : Nat)
    (polyscale evalscale : R) (evZeta evZetaOmega : List R) (cipClaimed : R)
    (omega zeta zetaOmega beta gamma alpha0 alpha1 alpha2 : R) (chalss : List (List R))
    (w s shift : List R) (zZeta zZetaOmega pZeta linConstTerm denomInv ftEval0Claimed : R)
    (transcriptOk ipaOk deferralOk : Bool) : Bool :=
  kimchiVerifyDecisionRec idxPrevLen prevLen publicLen wLen sLen coeffLen tCommLen chunkSize
      transcriptOk ipaOk deferralOk
  && decide (chalss.length = idxPrevLen)                                                    -- P6 count
  && prevChalFoldOk zeta zetaOmega chalss evZeta evZetaOmega                                 -- P6 fold
  && decide (cipR polyscale evalscale evZeta evZetaOmega = cipClaimed)                       -- C8
  && decide (((zeta - omega ^ (n - 3)) * (zeta - 1)) * denomInv = 1)                          -- witnessed inverse
  && decide (ftEval0R n omega zeta beta gamma alpha0 alpha1 alpha2 w s shift
       zZeta zZetaOmega pZeta linConstTerm denomInv = ftEval0Claimed)                         -- C5

/-- **`kimchiVerifyDecisionFieldRec_at_zero`** — with no carried challenges the P6 decision IS the
existing field decision. The recursion machinery is an EXTENSION, not a replacement, and this is
the theorem that says so rather than a comment claiming it. -/
theorem kimchiVerifyDecisionFieldRec_at_zero {R : Type} [CommRing R] [DecidableEq R]
    (prevLen publicLen wLen sLen coeffLen tCommLen chunkSize n : Nat)
    (polyscale evalscale : R) (evZeta evZetaOmega : List R) (cipClaimed : R)
    (omega zeta zetaOmega beta gamma alpha0 alpha1 alpha2 : R)
    (w s shift : List R) (zZeta zZetaOmega pZeta linConstTerm denomInv ftEval0Claimed : R)
    (transcriptOk ipaOk deferralOk : Bool) :
    kimchiVerifyDecisionFieldRec 0 prevLen publicLen wLen sLen coeffLen tCommLen chunkSize n
        polyscale evalscale evZeta evZetaOmega cipClaimed
        omega zeta zetaOmega beta gamma alpha0 alpha1 alpha2 []
        w s shift zZeta zZetaOmega pZeta linConstTerm denomInv ftEval0Claimed
        transcriptOk ipaOk deferralOk
      = kimchiVerifyDecisionField prevLen publicLen wLen sLen coeffLen tCommLen chunkSize n
        polyscale evalscale evZeta evZetaOmega cipClaimed
        omega zeta beta gamma alpha0 alpha1 alpha2
        w s shift zZeta zZetaOmega pZeta linConstTerm denomInv ftEval0Claimed
        transcriptOk ipaOk deferralOk := by
  simp [kimchiVerifyDecisionFieldRec, kimchiVerifyDecisionField, kimchiVerifyDecision,
    prevChalFoldOk_empty]

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

/-! ### §9c.1 — the alpha fold, and the FIVE custom-gate constraint bodies.

`Expr::combine_constraints` (`expr.rs:1633`) is `Σᵢ alpha^{αᵢ}·cᵢ`, and `linearization.rs:57-60`
registers ONE shared alpha block for ALL gates (`ArgumentType::Gate(_)` collapses to
`Gate(Zero)` in `Alphas::register`, `alphas.rs:64-71`, because gates are mutually exclusive), sized
`VarbaseMul::CONSTRAINTS = 21`. So EVERY gate's constraint `i` carries `alpha^i` starting at `i = 0`,
and the permutation's A0/A1/A2 start at `alpha^21`. -/

/-- **`alphaCombine`** — `Expr::combine_constraints` (`expr.rs:1633-1639`): `Σᵢ alpha^i·cᵢ` over the
gate's constraint list, `i` from 0 (the shared gate alpha block). -/
def alphaCombine {R : Type} [CommRing R] (alpha : R) (cs : List R) : R :=
  (List.range cs.length).foldl (fun acc i => acc + alpha ^ i * cs.getD i 0) 0

/-- Kimchi Poseidon S-box `x⁷` (`PlonkSpongeConstantsKimchi::PERM_SBOX = 7`, `poseidon.rs:375`). -/
def posSbox {R : Type} [CommRing R] (x : R) : R := x ^ (7 : Nat)

/-- **`poseidonLaneConstraint`** — one lane of one Poseidon round-equation constraint
(`poseidon.rs:428-433`): `witness(target_row, col) − fold(rc, (x,c) ↦ acc + c·x)` over
`zip(sboxed, mds[j])`, i.e. `target − (rc + Σ_c mds[j][c]·sbox(source_c))`. `mdsRow` = the 3 MDS
entries of row `j` (K3's `PastaPoseidon.mdsN[j]` — the linearization's `Constants::mds` IS
`Vesta::sponge_params().mds = fp_kimchi`, `curve.rs:63`), `rc` = `env.coeff(idx)`. -/
def poseidonLaneConstraint {R : Type} [CommRing R]
    (mdsRow : List R) (rc : R) (source : List R) (target : R) : R :=
  target - (rc + (mdsRow.getD 0 0 * posSbox (source.getD 0 0)
                + mdsRow.getD 1 0 * posSbox (source.getD 1 0)
                + mdsRow.getD 2 0 * posSbox (source.getD 2 0)))

/-- **`poseidonConstraints`** — the FULL 15 Poseidon constraints in emission order
(`poseidon.rs:364-435`), `ROUND_EQUATIONS` × `round_to_cols(target)`, with `idx` counting the
coefficient (round-constant) column 0..14. `STATE_ORDER = [0,2,3,4,1]` gives
`round_to_cols = [0..3, 6..9, 9..12, 12..15, 3..6]`, and the five equations are
`0→Curr 1, 1→Curr 2, 2→Curr 3, 3→Curr 4, 4→Next 0` — so the LAST three constraints read
`w₀,w₁,w₂` on the NEXT row, i.e. the ζω evaluations (`wNext`). `w`/`wNext` are the 15 witness
evals at ζ and ζω; `coeff` the 15 coefficient evals at ζ. -/
def poseidonConstraints {R : Type} [CommRing R]
    (mds : List (List R)) (coeff w wNext : List R) : List R :=
  let c := fun i => coeff.getD i (0 : R)
  let ww := fun i => w.getD i (0 : R)
  let wn := fun i => wNext.getD i (0 : R)
  let m := fun j => mds.getD j ([] : List R)
  let s0 := [ww 0, ww 1, ww 2]
  let s1 := [ww 6, ww 7, ww 8]
  let s2 := [ww 9, ww 10, ww 11]
  let s3 := [ww 12, ww 13, ww 14]
  let s4 := [ww 3, ww 4, ww 5]
  [ poseidonLaneConstraint (m 0) (c 0) s0 (ww 6)
  , poseidonLaneConstraint (m 1) (c 1) s0 (ww 7)
  , poseidonLaneConstraint (m 2) (c 2) s0 (ww 8)
  , poseidonLaneConstraint (m 0) (c 3) s1 (ww 9)
  , poseidonLaneConstraint (m 1) (c 4) s1 (ww 10)
  , poseidonLaneConstraint (m 2) (c 5) s1 (ww 11)
  , poseidonLaneConstraint (m 0) (c 6) s2 (ww 12)
  , poseidonLaneConstraint (m 1) (c 7) s2 (ww 13)
  , poseidonLaneConstraint (m 2) (c 8) s2 (ww 14)
  , poseidonLaneConstraint (m 0) (c 9) s3 (ww 3)
  , poseidonLaneConstraint (m 1) (c 10) s3 (ww 4)
  , poseidonLaneConstraint (m 2) (c 11) s3 (ww 5)
  , poseidonLaneConstraint (m 0) (c 12) s4 (wn 0)
  , poseidonLaneConstraint (m 1) (c 13) s4 (wn 1)
  , poseidonLaneConstraint (m 2) (c 14) s4 (wn 2) ]

/-- **`poseidonBody`** — the Poseidon gate's alpha-combined constraint (the factor the
`poseidon_selector` multiplies in `linConstTerm`). `Poseidon::CONSTRAINTS = 15`. -/
def poseidonBody {R : Type} [CommRing R]
    (alpha : R) (mds : List (List R)) (coeff w wNext : List R) : R :=
  alphaCombine alpha (poseidonConstraints mds coeff w wNext)

/-- **`completeAddConstraints`** — the 7 `CompleteAdd` constraints (`complete_add.rs:103-223`),
single-row, no coefficients. Columns: `x1 y1 x2 y2 x3 y3 inf same_x s inf_z x21_inv` = `w₀..w₁₀`.
The `zero_check(z, z_inv, r) = [z_inv·z − (1−r), r·z]` pair (`complete_add.rs:35-37`) is the
first two; then the doubling/adding slope disjunction, `s² = x₁+x₂+x₃`, `y₃ = −y₁+s(x₁−x₃)`, and the
two `inf` constraints. `3·x₁²` is emitted as `x1_squared.double() − x1_squared`. -/
def completeAddConstraints {R : Type} [CommRing R] (w : List R) : List R :=
  let ww := fun i => w.getD i (0 : R)
  let x1 := ww 0; let y1 := ww 1; let x2 := ww 2; let y2 := ww 3
  let x3 := ww 4; let y3 := ww 5; let inf := ww 6; let sameX := ww 7
  let s := ww 8; let infZ := ww 9; let x21Inv := ww 10
  let x21 := x2 - x1
  let y21 := y2 - y1
  let x1sq := x1 * x1
  [ x21Inv * x21 - (1 - sameX)
  , sameX * x21
  , sameX * ((s + s) * y1 - (x1sq + x1sq) - x1sq) + (1 - sameX) * (x21 * s - y21)
  , x1 + x2 + x3 - s * s
  , s * (x1 - x3) - y1 - y3
  , y21 * (sameX - inf)
  , y21 * infZ - inf ]

/-- **`varBaseMulConstraints`** — the 21 `VarbaseMul` constraints (`varbasemul.rs:419-450` +
`single_bit`, `varbasemul.rs:228-274`): the 5-bit binary decomposition, then 4 constraints per bit
(booleanity, the `s1` slope, `output.x`, `output.y`). Layout (`varbasemul.rs:310-331`): base
`(w₀,w₁)`, accs `(w₂,w₃) (w₇,w₈) (w₉,w₁₀) (w₁₁,w₁₂) (w₁₃,w₁₄)` on CURR and `(w'₀,w'₁)` on NEXT;
bits `w'₂..w'₆`; slopes `w'₇..w'₁₁`; `n = w₄`, `n' = w₅`. No coefficients, no constants.
(NB the per-bit slope parameter is *named* `s1` in the Rust but is `ss[i] = w'₍₇₊ᵢ₎` — unrelated to
`endosclmul`'s `s1 = w₉`.) -/
def varBaseMulConstraints {R : Type} [CommRing R] (w wNext : List R) : List R :=
  let ww := fun i => w.getD i (0 : R)
  let wn := fun i => wNext.getD i (0 : R)
  let xT := ww 0; let yT := ww 1
  let accX := fun i => [ww 2, ww 7, ww 9, ww 11, ww 13, wn 0].getD i (0 : R)
  let accY := fun i => [ww 3, ww 8, ww 10, ww 12, ww 14, wn 1].getD i (0 : R)
  let bit := fun i => [wn 2, wn 3, wn 4, wn 5, wn 6].getD i (0 : R)
  let sl := fun i => [wn 7, wn 8, wn 9, wn 10, wn 11].getD i (0 : R)
  let nPrev := ww 4; let nNext := ww 5
  let dec := nNext
    - (List.range 5).foldl (fun acc i => bit i + (acc + acc)) nPrev
  dec :: (List.range 5).flatMap (fun i =>
    let b := bit i
    let s := sl i
    let ix := accX i; let iy := accY i
    let ox := accX (i + 1); let oy := accY (i + 1)
    let bSign := (b + b) - 1
    let ssq := s * s
    let rx := ssq - ix - xT
    let t := ix - rx
    let u := (iy + iy) - t * s
    [ b * b - b
    , (ix - xT) * s - (iy - bSign * yT)
    , u * u - (t * t) * (ox - xT + ssq)
    , (oy + iy) * t - (ix - ox) * u ])

/-- **`endoMulConstraints`** — the 12 `EndosclMul` (`GateType::EndoMul`) constraints
(`endosclmul.rs:479-551`). **12, not 11** — the twelfth is the distinct-point witness
`(xp−xr)(xr−xs)·inv − 1`. Columns CURR: `xt=w₀ yt=w₁ inv=w₂ xp=w₄ yp=w₅ n=w₆ xr=w₇ yr=w₈ s1=w₉
s3=w₁₀ b1..b4=w₁₁..w₁₄`; NEXT: `xs=w'₄ ys=w'₅ n'=w'₆`. `endo` = `env.endo_coefficient()` — the
verifier-index constant `cs.endo` (NOT a column). Note the decomposition sign here is
`(…) − n'`, the OPPOSITE of `varbasemul`'s `n' − (…)`. -/
def endoMulConstraints {R : Type} [CommRing R] (endo : R) (w wNext : List R) : List R :=
  let ww := fun i => w.getD i (0 : R)
  let wn := fun i => wNext.getD i (0 : R)
  let xt := ww 0; let yt := ww 1; let inv := ww 2
  let xp := ww 4; let yp := ww 5; let n := ww 6
  let xr := ww 7; let yr := ww 8; let s1 := ww 9; let s3 := ww 10
  let b1 := ww 11; let b2 := ww 12; let b3 := ww 13; let b4 := ww 14
  let xs := wn 4; let ys := wn 5; let nNext := wn 6
  let em1 := endo - 1
  let xq1 := (1 + b1 * em1) * xt
  let xq2 := (1 + b3 * em1) * xt
  let yq1 := ((b2 + b2) - 1) * yt
  let yq2 := ((b4 + b4) - 1) * yt
  let s1sq := s1 * s1
  let s3sq := s3 * s3
  let d1 := (n + n) + b1
  let d2 := (d1 + d1) + b2
  let d3 := (d2 + d2) + b3
  let nConstraint := (d3 + d3) + b4 - nNext
  let xpxr := xp - xr
  let xrxs := xr - xs
  let ysyr := ys + yr
  let yryp := yr + yp
  [ b1 * b1 - b1
  , b2 * b2 - b2
  , b3 * b3 - b3
  , b4 * b4 - b4
  , (xq1 - xp) * s1 - (yq1 - yp)
  , (((xp + xp) - s1sq) + xq1) * (xpxr * s1 + yryp) - ((yp + yp) * xpxr)
  , yryp * yryp - (xpxr * xpxr * ((s1sq - xq1) + xr))
  , (xq2 - xr) * s3 - (yq2 - yr)
  , (((xr + xr) - s3sq) + xq2) * (xrxs * s3 + ysyr) - ((yr + yr) * xrxs)
  , ysyr * ysyr - (xrxs * xrxs * ((s3sq - xq2) + xs))
  , nConstraint
  , xpxr * xrxs * inv - 1 ]

/-- **`endomulScalarConstraints`** — the 11 `EndomulScalar` (`GateType::EndoMulScalar`) constraints
(`endomul_scalar.rs:174-220`): the three folds `n₈ = Σ 4·acc + xᵢ`, `a₈ = Σ 2·acc + c(xᵢ)`,
`b₈ = Σ 2·acc + d(xᵢ)`, then the 8 crumb constraints `crumb(xᵢ) = (((xᵢ−6)xᵢ+11)xᵢ−6)xᵢ`
(the EXPANDED Horner form of `x(x−1)(x−2)(x−3)`, `endomul_scalar.rs:196` — NOT `expr.rs`'s factored
`constraints::crumb`). Columns: `n0=w₀ n8=w₁ a0=w₂ b0=w₃ a8=w₄ b8=w₅ x₀..x₇=w₆..w₁₃` (`w₁₄` unused).
`c(x) = ((cC·x + cB)·x + cA)·x` with `cA = 11/6, cB = −5/2, cC = 2/3` (field DIVISION constants —
supplied here as WITNESSED ring elements, see `endomulScalarConstsOk`); `d(x) = c(x) + (−x²+3x−1)`.
No coefficients; the `endo_scalar` appears only in witness generation, never in the gate. -/
def endomulScalarConstraints {R : Type} [CommRing R] (cA cB cC : R) (w : List R) : List R :=
  let ww := fun i => w.getD i (0 : R)
  let n0 := ww 0; let n8 := ww 1; let a0 := ww 2; let b0 := ww 3
  let a8 := ww 4; let b8 := ww 5
  let x := fun i => ww (6 + i)
  let cf := fun (t : R) => ((cC * t + cB) * t + cA) * t
  let df := fun (t : R) => cf t + (((-1 : R) * t + 3) * t + (-1 : R))
  let n8e := (List.range 8).foldl (fun acc i => let a2 := acc + acc; (a2 + a2) + x i) n0
  let a8e := (List.range 8).foldl (fun acc i => (acc + acc) + cf (x i)) a0
  let b8e := (List.range 8).foldl (fun acc i => (acc + acc) + df (x i)) b0
  let crumb := fun (t : R) => (((t - 6) * t + 11) * t - 6) * t
  [n8e - n8, a8e - a8, b8e - b8] ++ (List.range 8).map (fun i => crumb (x i))

/-- **`endomulScalarConstsOk`** — the three `EndomulScalar` polynomial constants are the genuine
field quotients `11/6, −5/2, 2/3` (`endomul_scalar.rs:188-193`), CHECKED in the ring
(`6·cA = 11`, `2·cB = −5`, `3·cC = 2`) rather than divided — the same witnessed-quotient device §9b
uses for `denomInv`, so no `Field` instance is needed. -/
def endomulScalarConstsOk {R : Type} [CommRing R] [DecidableEq R] (cA cB cC : R) : Bool :=
  decide (6 * cA = 11) && decide (2 * cB = -5) && decide (3 * cC = 2)

/-- **`GateEvals`** — everything the gate constraint bodies read at ζ / ζω: the challenge `alpha`,
the verifier-index constants (`endo`, the `fp_kimchi` `mds`), the 15 coefficient evals, the 15
witness evals at ζ and at ζω, the three `EndomulScalar` field constants, and the six gate selectors
at ζ. This is exactly the `ArgumentEnv` a `PolishToken` constant-term evaluation resolves against. -/
structure GateEvals (R : Type) where
  alpha : R
  endo : R
  mds : List (List R)
  coeff : List R
  w : List R
  wNext : List R
  cA : R
  cB : R
  cC : R
  genSel : R
  posSel : R
  caddSel : R
  mulSel : R
  emulSel : R
  emulScalarSel : R

/-- **`gateLinConst`** — the WHOLE linearization constant term, DERIVED: `Σ_gate index(gate)·
(Σᵢ alpha^i·constraintᵢ)` (`argument.rs:201-213`, `linearization.rs:64-68,166-168`), with
`index_terms = []` (`linearization.rs:364`) so this IS `linConstTerm`. Every one of the six v1 gate
bodies is now TRANSCRIBED — generic (2), Poseidon (15), complete_add (7), varbasemul (21),
endomul/`EndosclMul` (12), endomul_scalar (11) — none is a carrier. -/
def gateLinConst {R : Type} [CommRing R] (g : GateEvals R) : R :=
  genericGateConstraint g.genSel g.alpha g.coeff g.w
  + g.posSel * poseidonBody g.alpha g.mds g.coeff g.w g.wNext
  + g.caddSel * alphaCombine g.alpha (completeAddConstraints g.w)
  + g.mulSel * alphaCombine g.alpha (varBaseMulConstraints g.w g.wNext)
  + g.emulSel * alphaCombine g.alpha (endoMulConstraints g.endo g.w g.wNext)
  + g.emulScalarSel * alphaCombine g.alpha (endomulScalarConstraints g.cA g.cB g.cC g.w)

/-- **`kimchiVerifyDecisionGates`** — `kimchiVerifyDecisionField` (§9b) with the C5 linearization
constant term DERIVED from the six transcribed gate constraint bodies (`gateLinConst`) instead of
fed as the `linConstTerm` carrier, AND the `EndomulScalar` quotient constants checked. Now
`ftEval0` is checked from the REAL gate constraints over the real coefficient/witness evals. -/
def kimchiVerifyDecisionGates {R : Type} [CommRing R] [DecidableEq R]
    (prevLen publicLen wLen sLen coeffLen tCommLen chunkSize n : Nat)
    (polyscale evalscale : R) (evZeta evZetaOmega : List R) (cipClaimed : R)
    (omega zeta beta gamma alpha0 alpha1 alpha2 : R)
    (s shift : List R) (g : GateEvals R)
    (zZeta zZetaOmega pZeta denomInv ftEval0Claimed : R)
    (transcriptOk ipaOk deferralOk : Bool) : Bool :=
  kimchiVerifyDecisionField prevLen publicLen wLen sLen coeffLen tCommLen chunkSize n
    polyscale evalscale evZeta evZetaOmega cipClaimed
    omega zeta beta gamma alpha0 alpha1 alpha2 g.w s shift
    zZeta zZetaOmega pZeta (gateLinConst g)
    denomInv ftEval0Claimed transcriptOk ipaOk deferralOk
  && endomulScalarConstsOk g.cA g.cB g.cC

/-- **`kimchiVerifyDecisionGates_refines`** — the gate-derived decision IS `kimchiVerifyDecisionField`
with `linConstTerm := gateLinConst g`, conjoined with the quotient-constant check (`rfl`): the gate
transcription is threaded INTO the accept, it does not replace the field decision. -/
theorem kimchiVerifyDecisionGates_refines {R : Type} [CommRing R] [DecidableEq R]
    (prevLen publicLen wLen sLen coeffLen tCommLen chunkSize n : Nat)
    (polyscale evalscale : R) (evZeta evZetaOmega : List R) (cipClaimed : R)
    (omega zeta beta gamma alpha0 alpha1 alpha2 : R)
    (s shift : List R) (g : GateEvals R)
    (zZeta zZetaOmega pZeta denomInv ftEval0Claimed : R)
    (transcriptOk ipaOk deferralOk : Bool) :
    kimchiVerifyDecisionGates prevLen publicLen wLen sLen coeffLen tCommLen chunkSize n
        polyscale evalscale evZeta evZetaOmega cipClaimed
        omega zeta beta gamma alpha0 alpha1 alpha2 s shift g
        zZeta zZetaOmega pZeta denomInv ftEval0Claimed transcriptOk ipaOk deferralOk
      = (kimchiVerifyDecisionField prevLen publicLen wLen sLen coeffLen tCommLen chunkSize n
          polyscale evalscale evZeta evZetaOmega cipClaimed
          omega zeta beta gamma alpha0 alpha1 alpha2 g.w s shift
          zZeta zZetaOmega pZeta (gateLinConst g)
          denomInv ftEval0Claimed transcriptOk ipaOk deferralOk
        && endomulScalarConstsOk g.cA g.cB g.cC) := rfl

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

/-! ## §9e — C3 (the CHALLENGE MAP): `challenge()` truncation + the endo `to_field(endo_r)`.

The two steps that turn a sponge squeeze into a usable challenge, both now BUILT:

  1. **`challenge()`** (`plonk_sponge.rs:47-49` → `sponge.rs:265-277`) = `squeeze(2 limbs)`:
     `sponge.squeeze()` is taken `into_bigint()`, its `HIGH_ENTROPY_LIMBS = 2` LEAST-significant
     64-bit limbs are cached, and `pack` re-assembles them — i.e. the raw squeeze mod `2^128`.
     A challenge consumes exactly the 2 cached limbs, so the NEXT `challenge()` finds the cache
     empty and squeezes again.
  2. **`ScalarChallenge::to_field(endo_r)`** (`sponge.rs:190-226`) = `to_field_with_length 128`:
     `a = b = 2`; for `i = 63 … 0`, double both, then `s = ±1` by bit `2i`, added to `b` if bit
     `2i+1` is 0 else to `a`; the value is `a·endo_r + b`.

The SPONGE side: `ArithmeticSponge::squeeze` (`poseidon.rs:128-146`) from `Absorbed(_)` PERMUTES and
returns `state[0]`, leaving `Squeezed(1)`; the immediately following squeeze has `n = 1 ≠ rate = 2`
so it returns `state[1]` of the SAME state with NO further permutation. So v' and u' are lanes 0 and
1 of one permuted state — `frSqueezePair` below. -/

/-- Bit `i` of a `Nat` (the `get_bit` of `sponge.rs:116-120` on the canonical little-endian limbs;
for a `< 2^128` challenge this is just the binary digit). -/
def bitAt (x i : Nat) : Nat := (x >>> i) &&& 1

/-- One step of `to_field_with_length`'s reversed loop (`sponge.rs:200-212`): double `a` and `b`,
then add `s = ±1` (`+1` iff bit `2i` is set) to `b` if bit `2i+1` is clear, else to `a`. -/
def endoStep {R : Type} [CommRing R] (chal i : Nat) (ab : R × R) : R × R :=
  let a := ab.1 + ab.1
  let b := ab.2 + ab.2
  let s : R := if bitAt chal (2 * i) = 0 then -1 else 1
  if bitAt chal (2 * i + 1) = 0 then (a, b + s) else (a + s, b)

/-- **`endoMapWithLength`** — `ScalarChallenge::to_field_with_length` (`sponge.rs:190-215`) over any
`CommRing`: fold `endoStep` for `i = lenBits/2 − 1 … 0` from `(2, 2)`, then `a·endo + b`. -/
def endoMapWithLength {R : Type} [CommRing R] (lenBits : Nat) (endo : R) (chal : Nat) : R :=
  let ab := (List.range (lenBits / 2)).reverse.foldl
    (fun ab i => endoStep chal i ab) ((2 : R), (2 : R))
  ab.1 * endo + ab.2

/-- **`endoMap`** — `ScalarChallenge::to_field(endo_r)` (`sponge.rs:223-226`), the default
`64 · CHALLENGE_LENGTH_IN_LIMBS = 128` bits. This is the map α' ↦ α, ζ' ↦ ζ, v' ↦ v, u' ↦ u. -/
def endoMap {R : Type} [CommRing R] (endo : R) (chal : Nat) : R := endoMapWithLength 128 endo chal

/-- **`low128`** — `DefaultFrSponge::squeeze(CHALLENGE_LENGTH_IN_LIMBS = 2)` (`sponge.rs:265-277`):
the raw squeeze truncated to its two least-significant 64-bit limbs. -/
def low128 (x : Nat) : Nat := x % 2 ^ 128

/-- **`frSqueezePair`** — the two successive `challenge()` squeezes of the Fr-sponge after the
phase-2 absorb stream: lane 0 and lane 1 of the SAME permuted state (`poseidon.rs:128-146`, rate 2),
each truncated to 128 bits. `Ref.absorbAll` performs the absorb schedule and the squeeze
permutation; `Ref.hash` is its lane-0 projection. -/
def frSqueezePair (stream : List Nat) : Nat × Nat :=
  let st := Ref.absorbAll [0, 0, 0] stream
  (low128 (st.getD 0 0), low128 (st.getD 1 0))

/-- **`deriveVU`** — v and u RE-DERIVED end-to-end from the phase-2 transcript: absorb the stream
into K3's Poseidon-over-Fp sponge, squeeze twice, truncate to 128 bits, map through the endomorphism
(`verifier.rs:395-405`). No challenge value is consumed as given. -/
def deriveVU {R : Type} [CommRing R] (endo : R) (stream : List Nat) : R × R :=
  let c := frSqueezePair stream
  (endoMap endo c.1, endoMap endo c.2)

/-- **`challengesOk`** — the C3 challenge check: α and ζ are the endo images of their raw
prechallenges, and v and u are RE-DERIVED from the Fr-sponge transcript (sponge + truncation + endo)
rather than taken from the prover. β and γ are the RAW phase-1 squeezes (`squeeze_order`'s `false`
flags) and are checked only for the 128-bit shape their derivation forces; the phase-1 Fq-sponge
that produces β, γ and the α'/ζ' prechallenges is the remaining carrier (§12). -/
def challengesOk {R : Type} [CommRing R] [DecidableEq R]
    (endo : R) (stream : List Nat) (alphaChal zetaChal : Nat)
    (alpha zeta v u : R) (beta gamma : Nat) : Bool :=
  let vu := deriveVU endo stream
  decide (alpha = endoMap endo alphaChal)
  && decide (zeta = endoMap endo zetaChal)
  && decide (v = vu.1) && decide (u = vu.2)
  && decide (beta < 2 ^ 128) && decide (gamma < 2 ^ 128)

/-- **`kimchiVerifyDecisionChallenges`** — `kimchiVerifyDecisionGates` (§9c) with C3's challenge
derivation THREADED IN: the accept now also requires that α, ζ, v, u are the values the transcript
DERIVES. `transcriptOk` survives as the phase-1 (Fq-sponge) carrier only. -/
def kimchiVerifyDecisionChallenges {R : Type} [CommRing R] [DecidableEq R]
    (prevLen publicLen wLen sLen coeffLen tCommLen chunkSize n : Nat)
    (polyscale evalscale : R) (evZeta evZetaOmega : List R) (cipClaimed : R)
    (omega zeta beta gamma alpha0 alpha1 alpha2 : R)
    (s shift : List R) (g : GateEvals R)
    (zZeta zZetaOmega pZeta denomInv ftEval0Claimed : R)
    (endo : R) (stream : List Nat) (alphaChal zetaChal betaN gammaN : Nat)
    (transcriptOk ipaOk deferralOk : Bool) : Bool :=
  kimchiVerifyDecisionGates prevLen publicLen wLen sLen coeffLen tCommLen chunkSize n
    polyscale evalscale evZeta evZetaOmega cipClaimed
    omega zeta beta gamma alpha0 alpha1 alpha2 s shift g
    zZeta zZetaOmega pZeta denomInv ftEval0Claimed transcriptOk ipaOk deferralOk
  && challengesOk endo stream alphaChal zetaChal g.alpha zeta polyscale evalscale betaN gammaN

/-- **`kimchiVerifyDecisionChallenges_refines`** — the challenge-derived decision IS the gate decision
conjoined with `challengesOk` (`rfl`): C3's derivation is ADDED, it replaces nothing. -/
theorem kimchiVerifyDecisionChallenges_refines {R : Type} [CommRing R] [DecidableEq R]
    (prevLen publicLen wLen sLen coeffLen tCommLen chunkSize n : Nat)
    (polyscale evalscale : R) (evZeta evZetaOmega : List R) (cipClaimed : R)
    (omega zeta beta gamma alpha0 alpha1 alpha2 : R)
    (s shift : List R) (g : GateEvals R)
    (zZeta zZetaOmega pZeta denomInv ftEval0Claimed : R)
    (endo : R) (stream : List Nat) (alphaChal zetaChal betaN gammaN : Nat)
    (transcriptOk ipaOk deferralOk : Bool) :
    kimchiVerifyDecisionChallenges prevLen publicLen wLen sLen coeffLen tCommLen chunkSize n
        polyscale evalscale evZeta evZetaOmega cipClaimed
        omega zeta beta gamma alpha0 alpha1 alpha2 s shift g
        zZeta zZetaOmega pZeta denomInv ftEval0Claimed endo stream alphaChal zetaChal betaN gammaN
        transcriptOk ipaOk deferralOk
      = (kimchiVerifyDecisionGates prevLen publicLen wLen sLen coeffLen tCommLen chunkSize n
            polyscale evalscale evZeta evZetaOmega cipClaimed
            omega zeta beta gamma alpha0 alpha1 alpha2 s shift g
            zZeta zZetaOmega pZeta denomInv ftEval0Claimed transcriptOk ipaOk deferralOk
          && challengesOk endo stream alphaChal zetaChal g.alpha zeta polyscale evalscale
              betaN gammaN) := rfl

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
-- C6 (§9c.1): the alpha fold is `Σ alpha^i·cᵢ` (`expr.rs:1633`).
#guard decide (alphaCombine (3 : ℚ) [5, 7, 11] = 5 + 3 * 7 + 9 * 11)
#guard decide (alphaCombine (3 : ℚ) [] = 0)

-- C6 Poseidon (§9c): the round-equation lane constraint is zero on an honest round, nonzero on a bump.
#guard decide (poseidonLaneConstraint ([2,3,5] : List ℚ) 7 [11,13,17]
  (7 + (2*(11^7) + 3*(13^7) + 5*(17^7))) = 0)
#guard decide (poseidonLaneConstraint ([2,3,5] : List ℚ) 7 [11,13,17]
  (7 + (2*(11^7) + 3*(13^7) + 5*(17^7)) + 1) ≠ 0)

/-! ### The CONSTRAINT COUNTS are the Rust `Argument::CONSTRAINTS` (`combined_constraints` asserts
`constraints.len() == CONSTRAINTS`, `argument.rs:203` — a wrong count is a wrong alpha block for
every LATER constraint, so these are load-bearing, not cosmetic). Poseidon 15, complete_add 7,
varbasemul 21, endomul/`EndosclMul` **12 (not 11)**, endomul_scalar 11. -/
private def zs (k : Nat) : List ℚ := List.replicate k 0
#guard (poseidonConstraints (R := ℚ) [zs 3, zs 3, zs 3] (zs 15) (zs 15) (zs 15)).length == 15
#guard (completeAddConstraints (R := ℚ) (zs 15)).length == 7
#guard (varBaseMulConstraints (R := ℚ) (zs 15) (zs 15)).length == 21
#guard (endoMulConstraints (R := ℚ) 0 (zs 15) (zs 15)).length == 12
#guard (endomulScalarConstraints (R := ℚ) 0 0 0 (zs 15)).length == 11

-- The `EndomulScalar` quotient constants: `11/6, −5/2, 2/3` pass, a bump fails.
#guard endomulScalarConstsOk (11/6 : ℚ) (-5/2) (2/3) == true
#guard endomulScalarConstsOk (11/6 : ℚ) (-5/2) (2/3 + 1) == false
-- `crumb` vanishes exactly on {0,1,2,3} (`endomul_scalar.rs:128-133`): the last 8 constraints.
#guard decide ((endomulScalarConstraints (11/6 : ℚ) (-5/2) (2/3)
  [0,0,0,0,0,0, 0,1,2,3,0,1,2,3, 0]).drop 3 = List.replicate 8 0)
#guard decide ((endomulScalarConstraints (11/6 : ℚ) (-5/2) (2/3)
  [0,0,0,0,0,0, 4,1,2,3,0,1,2,3, 0]).drop 3 ≠ List.replicate 8 0)
-- `boolean` and the distinct-point witness inside `EndosclMul`: bits must be 0/1, `inv` a real inverse.
#guard decide ((endoMulConstraints (7 : ℚ) [0,0,0,0,0,0,0,0,0,0,0, 2,0,0,0] [0,0,0,0,0,0,0]).getD 0 1 ≠ 0)
#guard decide ((endoMulConstraints (7 : ℚ) [0,0,0,0,0,0,0,0,0,0,0, 1,0,0,0] [0,0,0,0,0,0,0]).getD 0 1 = 0)

/-! ### `gateLinConst` collapses to the generic gate when the custom selectors vanish, and the
Poseidon term is live when `posSel ≠ 0` — the selector gating is real, not decorative. -/
private def gEvQ (posSel : ℚ) : GateEvals ℚ :=
  { alpha := 3, endo := 7, mds := [[2,3,5],[7,11,13],[17,19,23]]
  , coeff := [5,7,11,13,17,19,23,29,31,37,41,43,47,53,59]
  , w := [41,43,47,53,59,61,67,71,73,79,83,89,97,101,103]
  , wNext := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47]
  , cA := 11/6, cB := -5/2, cC := 2/3
  , genSel := 2, posSel := posSel, caddSel := 0, mulSel := 0, emulSel := 0, emulScalarSel := 0 }
#guard decide (gateLinConst (gEvQ 0)
  = genericGateConstraint (2 : ℚ) 3 [5,7,11,13,17,19,23,29,31,37,41,43,47,53,59]
      [41,43,47,53,59,61,67,71,73,79,83,89,97,101,103])
#guard decide (gateLinConst (gEvQ 1) ≠ gateLinConst (gEvQ 0))   -- the Poseidon body is LIVE

/-! ### C3 (§9e): the endo map and the 128-bit truncation. -/
-- Zero-length: no bits processed, so the value is the seed `2·endo + 2`.
#guard decide (endoMapWithLength 0 (7 : ℚ) 12345 = 2 * 7 + 2)
-- 2 bits: one step. chal = 0 ⇒ bits (0,1) = (0,0) ⇒ b += −1 ⇒ (a,b) = (4,3).
#guard decide (endoMapWithLength 2 (7 : ℚ) 0 = 4 * 7 + 3)
-- chal = 1 ⇒ bit0 = 1, bit1 = 0 ⇒ b += +1 ⇒ (4,5).
#guard decide (endoMapWithLength 2 (7 : ℚ) 1 = 4 * 7 + 5)
-- chal = 2 ⇒ bit0 = 0, bit1 = 1 ⇒ a += −1 ⇒ (3,4).
#guard decide (endoMapWithLength 2 (7 : ℚ) 2 = 3 * 7 + 4)
-- chal = 3 ⇒ bit0 = 1, bit1 = 1 ⇒ a += +1 ⇒ (5,4).
#guard decide (endoMapWithLength 2 (7 : ℚ) 3 = 5 * 7 + 4)
-- The full 128-bit map is injective enough to discriminate a single flipped bit.
#guard decide (endoMap (7 : ℚ) 12345 ≠ endoMap (7 : ℚ) 12346)
#guard low128 (2 ^ 200 + 5) == 5
#guard low128 (2 ^ 128 - 1) == 2 ^ 128 - 1
-- The two `challenge()`s read lanes 0 and 1 of ONE permuted state (rate 2, no second permutation).
#guard (frSqueezePair [1, 2, 3]).1 == low128 (Ref.hash [1, 2, 3])
#guard (frSqueezePair [1, 2, 3]).2 != (frSqueezePair [1, 2, 3]).1
#guard (frSqueezePair [1, 2, 3]) != (frSqueezePair [1, 2, 4])

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
-- 73 steps, up ONE from the pre-P6 count: `prev_challenge_digest` (`verifier.rs:290-299`) was
-- missing from the listing. At `nPrev = 0` it is the digest of an empty Fr-sponge, so its absence
-- changed no VALUE — only the claim that this list is the schedule.
#guard transcriptSchedule.length == 2 + COLUMNS + 6 + 5 + 7 + COLUMNS + COLUMNS + (PERMUTS - 1) + 2
-- and each carried recursion challenge adds exactly one commitment absorb, before public_comm
#guard (transcriptScheduleRec 2).length == transcriptSchedule.length + 2
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
#assert_axioms kimchiVerifyDecisionChallenges_refines
#assert_axioms frEvalPointOrder_head

/-! ## §12 — The PRECISE named residuals (what does NOT compose end-to-end).

  1. **The IPA/FRI soundness floor is NOT discharged.** `ipaOk` (the `msm == 0` accept,
     `ipa.rs:501`) is a CARRIER: `accept ⟹ the proof is valid` inherits the undischarged IPA
     opening soundness (a STARK proves the trace, not the opening). No `no_forgery`-style payoff
     is claimed (contrast `ethVerifyDecision_no_forgery`, which had the hash-CR carriers only).
  2. **C6: ALL SIX v1 GATE BODIES TRANSCRIBED + COMPOSED — the `linConstTerm` carrier is RETIRED
     (2026-07-27).** `linConstTerm = Σ_gate index(gate)·Σᵢ alpha^i·constraintᵢ` with
     `index_terms = []` (`linearization.rs:364`), and every body is now emitted from the source:
     generic 2 (`genericGateConstraint`), Poseidon 15 (`poseidonConstraints`), complete_add 7
     (`completeAddConstraints`), varbasemul 21 (`varBaseMulConstraints`), endomul/`EndosclMul` **12**
     (`endoMulConstraints` — the twelfth is the distinct-point witness `(xp−xr)(xr−xs)·inv − 1`),
     endomul_scalar 11 (`endomulScalarConstraints`, with `11/6, −5/2, 2/3` supplied as WITNESSED
     ring quotients, `endomulScalarConstsOk`). `gateLinConst` sums them behind their selectors and
     `kimchiVerifyDecisionGates` threads the result into `ftEval0`. `KimchiPoseidonGate` runs this
     on a REAL proof that FIRES the Poseidon gate (`poseidon_selector(ζ) ≠ 0`): the derived
     `genSel·generic + posSel·poseidon` reproduces Rust's `PolishToken::evaluate` value exactly, and
     bumping a Poseidon-only input rejects. STILL CARRIED for complete_add/varbasemul/endomul/
     endomul_scalar: those bodies are transcribed and composed but NOT yet exercised by a proof that
     fires them (no fixture with a curve-op circuit) — they are behind a zero selector in both
     fixtures, so their transcription rests on the source reading, not a differential.
  3. **C3 Fr-sponge (phase 2) + the CHALLENGE MAP: v and u RE-DERIVED end-to-end (2026-07-27).**
     The Fr-sponge IS K3's Poseidon-over-Fp sponge (`Vesta::sponge_params() = fp_kimchi`,
     `curve.rs:63`), `frSpongeDigest = Ref.hash` of the phase-2 absorb stream (§9d) in
     `plonk_sponge.rs:88-99` order. §9e adds the two remaining steps: `challenge()`'s low-128-bit
     truncation (`low128`, `sponge.rs:265-277`) and `ScalarChallenge::to_field(endo_r)` (`endoMap`,
     `sponge.rs:190-226`), plus the rate-2 squeeze semantics (v' = lane 0 of the permuted state,
     u' = lane 1 of the SAME state). So `deriveVU` computes v and u from the transcript alone, and
     `challengesOk`/`kimchiVerifyDecisionChallenges` CHECK them inside the accept; α and ζ are
     checked as the endo images of their raw prechallenges. STILL CARRIED: the PHASE-1 Fq-sponge
     (over `qN` with the `fq_kimchi` params — a different constant set than K3's `fp_kimchi`,
     absorbing the index digest and the commitment curve points). It produces β, γ and the raw
     prechallenges α', ζ', and it produces the `digest` that seeds phase 2. So β, γ, α', ζ' and
     `digest` are inputs; everything downstream of them is derived.
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
  6. **Out of v1 scope:** the `sg` split's terminal discharge (P10), multi-proof BATCHING
     (`to_batch` is run on ONE proof here), and lookups/Plookup (C10, `lookup_index = None`).
     **`prev_challenges` is NO LONGER on this list** (2026-07-28): `shapeOkRec` +
     `prevChalFoldOk` + `transcriptScheduleRec` accept and CHECK a recursive index, and
     `KimchiRecursionGate` runs the whole thing on a real `prev_challenges = 2` proof that the
     o1-labs verifier accepts. What is still out of scope on that leg: the accumulator
     COMMITMENTS are checked only as transcript inputs — that they equal `⟨b_poly_coeffs, G⟩` is
     `PicklesRecursion` P1's `msm == 0`, i.e. the inherited P10 floor.

CONTINUATION (K5+): discharge C6's baked token streams (emit them from Lean per gate), instantiate
the Fr-sponge, and thread the batch assembly — then the deferral is the ONLY remaining carrier
short of the terminal IPA soundness floor, which is the Pickles-recursion frontier.
-/

end Dregg2.Circuit.Emit.KimchiVerify
