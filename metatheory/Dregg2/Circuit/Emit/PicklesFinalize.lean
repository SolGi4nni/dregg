/-
# `PicklesFinalize` — P3 (`finalize_other_proof`) and P4 (the transcript-equality binding).

The follow-on to `PicklesRecursion` (P0/P1/P2) named in `docs/PICKLES-VERIFIER-SCOPE.md` §7.

## SUBSTRATE (House Law #1, said out loud at constraint #1)

**This is Lean-authored.** Every check, derivation and decision below is a Lean `def` over
`[CommRing R]`; nothing here is a Rust AIR, a Rust gadget, or a Rust `air_accepts`. The Rust and
OCaml files cited are READ as the specification being transcribed, never as the authoring site.

## WHAT THIS FILE CLAIMS — P3 built; P4 MEASURED, NOT PROVED.

**P3 — `finalize_other_proof` is built.** `finalizeOtherProof` is the four-way AND of
`xi_correct`, `b_correct`, `combined_inner_product_correct` and `plonk_checks_passed`
(`step.rs:876-884`; OCaml `wrap_verifier.ml:1039-1046`), assembled out of the pieces P0–P2 left:
K5's `cipR` + `ftEval0R` + `gateLinConst`, K4c's `bEval`, and P2's `Shifted_value` bridge as the
`decode`. The one genuinely new derivation, `derive_plonk` (`plonk_checks.rs:238-286`), is authored
here — and its `perm` arm turns out to be K5's already-shipped `permScalar` verbatim
(`derivePlonk_perm_is_K5_permScalar`). It has a satisfying model (`finalize_complete`, universally
quantified — not a KAT) and four independent tamper poles.

**P4 — the binding is FORMALIZED and MEASURED; it is NOT proved sound.** The three assert families
(`assert_eq_plonk`, the sponge-digest equality, the per-round bulletproof-challenge equality) are
written as a predicate; what they pin is proved (`binding_and_accept_determine`), what they leave
free is proved (`finalize_ignores_zeta_powers`, `zeta_powers_stay_free`), and each family is proved
load-bearing by exhibiting the attack that appears when it is dropped
(`plonk_assert_is_necessary`, `bp_assert_is_necessary`, `digest_assert_is_necessary`). §Z states, in
one place, the three things that would still be required for "the recursion is sound" and why none
of them is in this tree. **Read §Z before citing anything here as recursion soundness.**

## WHAT IS NOT CLAIMED

  * Not that the deferred values are the opposite proof's. That is the P4 conclusion and it is
    NOT reached; §Z lists the three missing premises (sponge collision resistance, `endo`
    injectivity on 128-bit prechallenges, and the IPA opening floor P10).
  * Not a real fixture. The concrete pole (§P3.5) runs at `ZMod 97` with an 8-point domain: it
    exists to give the challenge coordinates a NEGATIVE pole, which no generic theorem can supply
    (a collision is not impossible, only improbable). The Fp/Fq instantiations are the generic
    theorems, which hold at every ring.
  * Not the 128-bit prechallenge structure. `endo` is an abstract `R → R` here; its injectivity is
    a HYPOTHESIS where used and a named residual where not.
  * Not domain selection. `branch_data` picks the evaluation domain in the real code
    (`step.rs:598-604`); here the domain is given in `OtherProof`, so `finalize` not reading
    `branchData` is a MODELING choice, not a discovered hole. Said again in §Z.

## Sources (read, not authored from)

  * `~/dev/mina-rust` (openmina, HEAD `82480cd468`) — `crates/ledger/src/proofs/step.rs:519-887`
    (`finalize_other_proof`, the four-way AND at `:876-884`),
    `public_input/plonk_checks.rs:238-286` (`derive_plonk`), `:353-370` (`checked` — the
    comparison list, which is `[perm]`), `wrap.rs:1340-1396` (`ft_comm`, where the two derived
    scalars are consumed as GROUP scalars).
  * `~/dev/mina` (OCaml, **March 2024 snapshot, no git rev — see the staleness note in
    `docs/PICKLES-VERIFIER-SCOPE.md` §Provenance**) — `src/lib/pickles/plonk_checks/
    plonk_checks.ml:462-545` (`derive_plonk` + `checked`, comparison list `[ perm ]`),
    `wrap_verifier.ml:492-499` (`assert_eq_plonk`), `:717-731` (its call site),
    `:1015-1046` (the four-way AND), `wrap_main.ml:430-439` (digest + per-round equalities),
    `step_verifier.ml:1271-1285` (the Step mirror).

## Axiom hygiene

`#assert_axioms` per theorem and `#assert_namespace_axioms` for the namespace (§Y). No `sorry`, no
`native_decide`.
-/
import Dregg2.Circuit.Emit.PicklesRecursion

namespace Dregg2.Circuit.Emit.PicklesFinalize

open Dregg2.Circuit.Emit.PastaIPA (bEval)
open Dregg2.Circuit.Emit.KimchiVerify
  (GateEvals gateLinConst cipR ftEval0R zkPolyR permScalar PERMUTS sqIter sqIter_eq)
open Dregg2.Circuit.Emit.PicklesRecursion
  (Fp Fq Side Shift1 Shift2 type1ToField type1OfField type2ToField type2OfField
   type1_to_of type2_to_of type1_eq_iff type2_eq_iff shift1Fp shift2Fq shiftKindFor
   pasta_shift_constants PlonkMinimal PlonkInCircuit BranchData WrapDeferredValues)

set_option autoImplicit false
set_option maxRecDepth 8000

/-! ## §P3.0 — `derive_plonk`: the ONLY new arithmetic P3 needs.

`plonk_checks.rs:238-286` / `plonk_checks.ml:462-506` derive three scalars from the four sampled
IOP challenges and the proof's own evaluations:

  * `zeta_to_srs_length = pow2pow zeta srs_length_log2` — `zeta` squared `srs_length_log2` times,
    i.e. `ζ^(2^srs_length_log2)`. This is EXACTLY P0's `sqIter` ladder, so `sqIter_eq` gives the
    closed form for free.
  * `zeta_to_domain_size = env.zeta_to_n_minus_1 + 1` — i.e. `ζ^n`.
  * `perm = −(fold over the σ evals of `z(ζω)·β·α^21·zkp(ζ)`)`.

`perm` is the one with real content, and it is **already in the tree**: K5's `permScalar`
(`KimchiVerify` §4, the `perm_scalars` transcription of `permutation.rs:392-430`) has this body
term-for-term. So `derive_plonk`'s new arithmetic reduces to two exponentiations plus a K5 reuse. -/

section Derive

variable {R : Type} [CommRing R]

/-- `perm` of `derive_plonk` (`plonk_checks.rs:260-266`), over `[CommRing R]`:
`−( fold_{i<6} (γ + β·σᵢ(ζ) + wᵢ(ζ)) applied to  z(ζω)·β·α^21·zkp(ζ) )`. -/
def permScalarR (n : Nat) (omega zeta beta gamma alpha0 : R) (w s : List R) (zZetaOmega : R) : R :=
  let zkp := zkPolyR n omega zeta
  let init := zZetaOmega * beta * alpha0 * zkp
  let res := (List.range (PERMUTS - 1)).foldl
    (fun x i => x * (gamma + beta * s.getD i 0 + w.getD i 0)) init
  0 - res

/-- **`derivePlonk_perm_is_K5_permScalar`** — the `perm` arm of `derive_plonk` IS K5's shipped
`permScalar`, at every field. The "new arithmetic" of P3 is two exponentiations and this reuse; the
ring mirror exists only because `ZMod pN` / `ZMod qN` carry no `Field` instance here (the same
discipline `KimchiVerify` §9b uses for `cipR` / `ftEval0R`). -/
theorem derivePlonk_perm_is_K5_permScalar {K : Type} [Field K] (n : Nat)
    (omega zeta beta gamma alpha0 : K) (w s : List K) (zZetaOmega : K) :
    permScalarR n omega zeta beta gamma alpha0 w s zZetaOmega
      = permScalar n omega zeta beta gamma alpha0 w s zZetaOmega := rfl

/-- `zeta_to_domain_size` (`plonk_checks.rs:267`): `(ζⁿ − 1) + 1`. -/
def zetaToDomainSizeR (n : Nat) (zeta : R) : R := (zeta ^ n - 1) + 1

/-- `zeta_to_srs_length` (`plonk_checks.rs:269-272`, `plonk_checks.ml:499`): `ζ` squared
`srsLengthLog2` times — P0's `sqIter` ladder, reused verbatim. -/
def zetaToSrsLengthR (srsLengthLog2 : Nat) (zeta : R) : R := sqIter srsLengthLog2 zeta

/-- **`derived_scalars_closed_form`** — the two exponentiation arms in closed form. The
`sqIter` half is `sqIter_eq` (P0); the other is a one-line cancellation. Stated because the
`pow2pow` fold and the `zeta_to_n_minus_1 + 1` idiom both hide what they compute. -/
theorem derived_scalars_closed_form (n srsLog2 : Nat) (zeta : R) :
    zetaToDomainSizeR n zeta = zeta ^ n
    ∧ zetaToSrsLengthR srsLog2 zeta = zeta ^ (2 ^ srsLog2) := by
  refine ⟨by simp [zetaToDomainSizeR], ?_⟩
  simpa [zetaToSrsLengthR] using sqIter_eq srsLog2 zeta

end Derive

/-! ## §P3.1 — the two inputs `finalize_other_proof` reads.

`OtherProof` is everything the check reads that is NOT the attacker-supplied deferred-values
record: the evaluation domain, the proof's own claimed evaluations, and the two sponge squeezes
(`step.rs:693-694`: `xi_actual`, `r_actual`). `Sampled` is what the GROUP sub-verifier squeezes out
of the transcript — it is inert in P3 (nothing here reads it) and becomes the whole subject in P4.

The `ft_eval` slot is kept EXPLICIT (`evZetaPre ++ [ft] ++ evZetaPost`) rather than folded into the
eval column, because `ft_eval0` is the one entry of the ξ-fold that `finalize_other_proof`
RECOMPUTES (`step.rs:751-757`) — collapsing it into the column would silently delete the check. -/

/-- The transcript-sampled tuple: the four IOP challenges as RAW prechallenges (the form
`assert_eq_plonk` compares — `wrap_verifier.ml:496-499` asserts on `.inner`, before the endo map),
plus the `k` bulletproof round prechallenges. -/
structure Sampled (R : Type) where
  beta : R
  gamma : R
  alpha : R
  zeta : R
  bpChals : List R
  deriving DecidableEq

/-- Everything `finalize_other_proof` reads besides the deferred-values record. -/
structure OtherProof (R : Type) where
  /-- evaluation-domain size (`branch_data`-selected in the real code — see §Z item 4). -/
  n : Nat
  /-- the domain generator. -/
  omega : R
  /-- `COMMON_MAX_DEGREE_STEP_LOG2` (`step.rs:739`). -/
  srsLengthLog2 : Nat
  /-- the gate/witness/coefficient/selector evals K5's `gateLinConst` resolves against. Its
  `alpha` field is OVERWRITTEN by the deferred `alpha` in `finalizeOtherProof` — the linearization
  is evaluated at the challenge under check, not at a free one. -/
  g : GateEvals R
  /-- the six σ evals at ζ. -/
  s : List R
  /-- the domain shifts. -/
  shift : List R
  /-- `z(ζ)`, `z(ζω)`. -/
  zZeta : R
  zZetaOmega : R
  /-- the public polynomial at ζ. -/
  pZeta : R
  /-- witnessed inverse of `(ζ − ω^{n−3})(ζ − 1)` (K5 §9b's discipline). -/
  denomInv : R
  /-- the ξ-fold column at ζ, before the `ft` slot. -/
  evZetaPre : List R
  /-- the ξ-fold column at ζ, after the `ft` slot. -/
  evZetaPost : List R
  /-- the ξ-fold column at ζω, before the `ft` slot. -/
  evZetaOmegaPre : List R
  /-- the ξ-fold column at ζω, after the `ft` slot. -/
  evZetaOmegaPost : List R
  /-- `ft_eval1` — supplied by the proof, NOT recomputed (`step.rs:545`). -/
  ftEval1 : R
  /-- `xi_actual = lowest_128_bits(sponge.squeeze())` (`step.rs:693`). -/
  xiSqueeze : R
  /-- `r_actual = lowest_128_bits(sponge.squeeze())` (`step.rs:694`). -/
  rSqueeze : R

/-! ## §P3.2 — the three recomputations, and the four checks.

The endo map `endo` is `to_field_checked::<F,128>(·, endo)` (`step.rs:552-555`) — the map from a
128-bit prechallenge to the field scalar actually used. It is abstract here: P3 never needs a
property of it, and P4 needs INJECTIVITY, which is taken as a hypothesis where used (§Z item 2). -/

section Checks

variable {R : Type} [CommRing R] [DecidableEq R]

/-- The challenges as `finalize_other_proof` uses them: raw prechallenges endo-mapped
(`step.rs:583-584`, `:698`, `:846-849`). `beta`/`gamma` are used RAW (`two_u64_to_field`,
`step.rs:587-588`) — only `alpha`, `zeta`, `xi`, `r` and the round challenges go through `endo`. -/
def alphaOf (endo : R → R) (sm : Sampled R) : R := endo sm.alpha
/-- ζ, endo-mapped. -/
def zetaOf (endo : R → R) (sm : Sampled R) : R := endo sm.zeta
/-- ζω. -/
def zetaOmegaOf (endo : R → R) (op : OtherProof R) (sm : Sampled R) : R := zetaOf endo sm * op.omega
/-- the `k` bulletproof challenges, endo-mapped (`step.rs:846-849`). -/
def bpOf (endo : R → R) (sm : Sampled R) : List R := sm.bpChals.map endo

/-- `ft_eval0`, RECOMPUTED (`step.rs:751-757` `ft_eval0_checked`) — K5's `ftEval0R` with the three
α powers derived from the deferred α (`PERM_ALPHA0 = 21`, `plonk_checks.rs:221`) and the
linearization constant term derived from K5's transcribed gate bodies. -/
def ftEval0Of (endo : R → R) (op : OtherProof R) (sm : Sampled R) : R :=
  let a := alphaOf endo sm
  let ge : GateEvals R := { op.g with alpha := a }
  ftEval0R op.n op.omega (zetaOf endo sm) sm.beta sm.gamma (a ^ 21) (a ^ 22) (a ^ 23)
    ge.w op.s op.shift op.zZeta op.zZetaOmega op.pZeta (gateLinConst ge) op.denomInv

/-- `actual_combined_inner_product` (`step.rs:773-838`): the ξ-fold of both eval columns with the
recomputed `ft_eval0` in its slot, the two columns combined by `r`. This is K5's `cipR`. -/
def cipActualOf (endo : R → R) (op : OtherProof R) (sm : Sampled R) (xiRaw : R) : R :=
  cipR (endo xiRaw) (endo op.rSqueeze)
    (op.evZetaPre ++ ftEval0Of endo op sm :: op.evZetaPost)
    (op.evZetaOmegaPre ++ op.ftEval1 :: op.evZetaOmegaPost)

/-- `b_actual` (`step.rs:855-859`; OCaml `wrap_verifier.ml:1019-1022`):
`challenge_poly(ζ) + r·challenge_poly(ζω)`, where `challenge_polynomial` IS K4c's `bEval`. -/
def bActualOf (endo : R → R) (op : OtherProof R) (sm : Sampled R) : R :=
  bEval (zetaOf endo sm) (bpOf endo sm)
    + endo op.rSqueeze * bEval (zetaOmegaOf endo op sm) (bpOf endo sm)

/-- `derive_plonk`'s `perm` at the deferred challenges (`plonk_checks.rs:260-266`). -/
def permActualOf (endo : R → R) (op : OtherProof R) (sm : Sampled R) : R :=
  let a := alphaOf endo sm
  permScalarR op.n op.omega (zetaOf endo sm) sm.beta sm.gamma (a ^ 21) op.g.w op.s op.zZetaOmega

/-- The challenge tuple the deferred-values record CLAIMS. `finalize_other_proof` checks its own
arithmetic against this; P4 is the question of whether it equals the SAMPLED tuple. -/
def sampledOf (dv : WrapDeferredValues R R R) : Sampled R :=
  { beta := dv.plonk.minimal.beta, gamma := dv.plonk.minimal.gamma,
    alpha := dv.plonk.minimal.alpha, zeta := dv.plonk.minimal.zeta,
    bpChals := dv.bulletproofChallenges }

/-- `xi_correct` (`step.rs:696`) — the squeeze equals the exposed ξ, compared as RAW
prechallenges (`two_u64_to_field(xi)`, not the endo image). -/
def xiCorrect (op : OtherProof R) (dv : WrapDeferredValues R R R) : Bool :=
  decide (op.xiSqueeze = dv.xi)

/-- `b_correct` (`step.rs:854-862`). `decode` is the side's `Shifted_value.to_field`. -/
def bCorrect (decode endo : R → R) (op : OtherProof R) (dv : WrapDeferredValues R R R) : Bool :=
  decide (decode dv.b = bActualOf endo op (sampledOf dv))

/-- `combined_inner_product_correct` (`step.rs:747-841`). -/
def cipCorrect (decode endo : R → R) (op : OtherProof R) (dv : WrapDeferredValues R R R) : Bool :=
  decide (decode dv.combinedInnerProduct = cipActualOf endo op (sampledOf dv) dv.xi)

/-- `plonk_checks_passed` (`step.rs:872`) = `plonk_checks::checked` (`plonk_checks.rs:353-370`).

**MEASURED, and it is the finding of §P3.4:** the comparison list is `[perm]` — one entry — in BOTH
implementations (`plonk_checks.rs:363-366`, three sibling comparisons commented out; OCaml
`plonk_checks.ml:541-543`, the literal list `[ perm ]`). `derive_plonk` computes
`zeta_to_srs_length` and `zeta_to_domain_size` and `checked` compares NEITHER. This def is faithful
to that, not to what the name suggests. -/
def plonkChecksPassed (decode endo : R → R) (op : OtherProof R)
    (dv : WrapDeferredValues R R R) : Bool :=
  decide (decode dv.plonk.perm = permActualOf endo op (sampledOf dv))

/-- **`finalizeOtherProof`** — `Boolean::all [xi_correct, b_correct,
combined_inner_product_correct, plonk_checks_passed]` (`step.rs:876-884`; OCaml
`wrap_verifier.ml:1039-1046`), in that order. -/
def finalizeOtherProof (decode endo : R → R) (op : OtherProof R)
    (dv : WrapDeferredValues R R R) : Bool :=
  xiCorrect op dv && bCorrect decode endo op dv && cipCorrect decode endo op dv
    && plonkChecksPassed decode endo op dv

/-! ## §P3.3 — the satisfying model: a UNIVERSAL completeness theorem, not a KAT.

`honestDeferred` builds the record a well-behaved prover would expose at a given sampled tuple —
every scalar the honest derivation, encoded through the side's shifted-value bridge. The theorem is
quantified over every ring, every `op`, every `sm`: whenever `decode ∘ encode = id`, the four-way
AND accepts. (That hypothesis is exactly P2's `type1_to_of` / `type2_to_of`, discharged for the two
concrete Pasta bridges in §P3.6.) -/

/-- The honest deferred-values record at a sampled tuple. -/
def honestDeferred (encode endo : R → R) (op : OtherProof R) (sm : Sampled R)
    (bd : BranchData) (jc : Option R) : WrapDeferredValues R R R :=
  { plonk :=
      { minimal := { alpha := sm.alpha, beta := sm.beta, gamma := sm.gamma, zeta := sm.zeta,
                     jointCombiner := jc }
        zetaToSrsLength := encode (zetaToSrsLengthR op.srsLengthLog2 (zetaOf endo sm))
        zetaToDomainSize := encode (zetaToDomainSizeR op.n (zetaOf endo sm))
        perm := encode (permActualOf endo op sm) }
    combinedInnerProduct := encode (cipActualOf endo op sm op.xiSqueeze)
    b := encode (bActualOf endo op sm)
    xi := op.xiSqueeze
    bulletproofChallenges := sm.bpChals
    branchData := bd }

/-- The honest record claims exactly the sampled tuple — by construction. -/
@[simp] theorem sampledOf_honest (encode endo : R → R) (op : OtherProof R) (sm : Sampled R)
    (bd : BranchData) (jc : Option R) :
    sampledOf (honestDeferred encode endo op sm bd jc) = sm := by
  cases sm; rfl

/-- **`finalize_complete`** — the SATISFYING MODEL. At every ring, every domain, every sampled
tuple, the honest record passes all four checks, given only that the shifted-value bridge
round-trips. Non-vacuous by construction: it produces an accepting instance for arbitrary inputs,
so every "rejects" theorem below is a genuine discrimination rather than a uniform `false`. -/
theorem finalize_complete (encode decode endo : R → R) (hde : ∀ x, decode (encode x) = x)
    (op : OtherProof R) (sm : Sampled R) (bd : BranchData) (jc : Option R) :
    finalizeOtherProof decode endo op (honestDeferred encode endo op sm bd jc) = true := by
  have hs : sampledOf (honestDeferred encode endo op sm bd jc) = sm :=
    sampledOf_honest encode endo op sm bd jc
  have h1 : xiCorrect op (honestDeferred encode endo op sm bd jc) = true :=
    decide_eq_true rfl
  have h2 : bCorrect decode endo op (honestDeferred encode endo op sm bd jc) = true := by
    simp only [bCorrect, hs]; exact decide_eq_true (hde _)
  have h3 : cipCorrect decode endo op (honestDeferred encode endo op sm bd jc) = true := by
    simp only [cipCorrect, hs]; exact decide_eq_true (hde _)
  have h4 : plonkChecksPassed decode endo op (honestDeferred encode endo op sm bd jc) = true := by
    simp only [plonkChecksPassed, hs]; exact decide_eq_true (hde _)
  simp only [finalizeOtherProof, h1, h2, h3, h4, Bool.and_self]

/-! ## §P3.4 — the tamper poles, and the two coordinates that have none.

Four checked coordinates, four falsifiers: given an accepting record and an INJECTIVE `decode`
(true of both Pasta bridges — P2's `type1_eq_iff` / `type2_eq_iff`), moving any one of `xi`, `b`,
`combined_inner_product`, `perm` flips the decision to `false`. These are the negative poles P3
must have.

Then the finding. The exposed `zeta_to_srs_length` and `zeta_to_domain_size` are **not read by
`finalizeOtherProof` at all** — `finalize_ignores_zeta_powers` is `rfl`. So an attacker may put
anything in those two public-input slots and all four checks still pass. §P4.4 pins down where
they ARE constrained, and it is not here. -/

/-- **`finalize_xi_tamper`** — moving the exposed ξ off the squeeze rejects. -/
theorem finalize_xi_tamper (decode endo : R → R) (op : OtherProof R)
    (dv : WrapDeferredValues R R R) (x : R) (hx : x ≠ dv.xi)
    (hacc : finalizeOtherProof decode endo op dv = true) :
    finalizeOtherProof decode endo op { dv with xi := x } = false := by
  simp only [finalizeOtherProof, xiCorrect, Bool.and_eq_true, decide_eq_true_eq] at hacc
  simp only [finalizeOtherProof, xiCorrect, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  exact Or.inl (Or.inl (Or.inl (fun h => hx (h.symm.trans hacc.1.1.1))))

/-- **`finalize_b_tamper`** — `b` is compared against a recomputation that does not read `b`, so an
injective `decode` makes every change to it reject. -/
theorem finalize_b_tamper (decode endo : R → R) (hinj : Function.Injective decode)
    (op : OtherProof R) (dv : WrapDeferredValues R R R) (x : R) (hx : x ≠ dv.b)
    (hacc : finalizeOtherProof decode endo op dv = true) :
    finalizeOtherProof decode endo op { dv with b := x } = false := by
  simp only [finalizeOtherProof, bCorrect, Bool.and_eq_true, decide_eq_true_eq] at hacc
  simp only [finalizeOtherProof, bCorrect, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  refine Or.inl (Or.inl (Or.inr ?_))
  intro h
  exact hx (hinj (h.trans hacc.1.1.2.symm))

/-- **`finalize_cip_tamper`** — the mirror for `combined_inner_product`. -/
theorem finalize_cip_tamper (decode endo : R → R) (hinj : Function.Injective decode)
    (op : OtherProof R) (dv : WrapDeferredValues R R R) (x : R) (hx : x ≠ dv.combinedInnerProduct)
    (hacc : finalizeOtherProof decode endo op dv = true) :
    finalizeOtherProof decode endo op { dv with combinedInnerProduct := x } = false := by
  simp only [finalizeOtherProof, cipCorrect, Bool.and_eq_true, decide_eq_true_eq] at hacc
  simp only [finalizeOtherProof, cipCorrect, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  refine Or.inl (Or.inr ?_)
  intro h
  exact hx (hinj (h.trans hacc.1.2.symm))

/-- **`finalize_perm_tamper`** — the mirror for the one derived scalar that IS compared. -/
theorem finalize_perm_tamper (decode endo : R → R) (hinj : Function.Injective decode)
    (op : OtherProof R) (dv : WrapDeferredValues R R R) (x : R) (hx : x ≠ dv.plonk.perm)
    (hacc : finalizeOtherProof decode endo op dv = true) :
    finalizeOtherProof decode endo op
        { dv with plonk := { dv.plonk with perm := x } } = false := by
  simp only [finalizeOtherProof, plonkChecksPassed, Bool.and_eq_true, decide_eq_true_eq] at hacc
  simp only [finalizeOtherProof, plonkChecksPassed, Bool.and_eq_false_iff,
    decide_eq_false_iff_not]
  refine Or.inr ?_
  intro h
  exact hx (hinj (h.trans hacc.2.symm))

/-- **`finalize_ignores_zeta_powers`** — the exposed `zeta_to_srs_length` and
`zeta_to_domain_size` do not occur in the decision. `rfl`: they are read by `derive_plonk` on the
PROVER side and by `ft_comm` on the GROUP side, but `plonk_checks::checked` compares only `perm`
(`plonk_checks.rs:363-366`; `plonk_checks.ml:541-543`). -/
theorem finalize_ignores_zeta_powers (decode endo : R → R) (op : OtherProof R)
    (dv : WrapDeferredValues R R R) (a b : R) :
    finalizeOtherProof decode endo op
        { dv with plonk := { dv.plonk with zetaToSrsLength := a, zetaToDomainSize := b } }
      = finalizeOtherProof decode endo op dv := rfl

/-- **`zeta_powers_stay_free`** — the freedom made concrete against the satisfying model: two
records that differ in `zeta_to_domain_size` by an arbitrary amount BOTH pass all four checks. This
is the statement that survives being pointed at a real Wrap object, because it quantifies over
every `op`. -/
theorem zeta_powers_stay_free (encode decode endo : R → R) (hde : ∀ x, decode (encode x) = x)
    (op : OtherProof R) (sm : Sampled R) (bd : BranchData) (jc : Option R) (a b : R) :
    finalizeOtherProof decode endo op
        (let h := honestDeferred encode endo op sm bd jc
         { h with plonk := { h.plonk with zetaToSrsLength := a, zetaToDomainSize := b } })
      = true := by
  rw [finalize_ignores_zeta_powers]
  exact finalize_complete encode decode endo hde op sm bd jc

omit [DecidableEq R] in
/-- **`plonk_check_shifted_or_field`** — P2's bridge theorems, USED. The real code compares the
SHIFTED representatives (`field::equal(plonk.perm.shifted, actual.perm.shifted_raw())`); this file
compares the decoded field values. `type1_eq_iff` / `type2_eq_iff` say those are the same check, so
the modeling choice is not a weakening. Stated at both bridges, since P5 is the field swap. -/
theorem plonk_check_shifted_or_field (sh1 : Shift1 R) (h1 : sh1.ok) (sh2 : Shift2 R) (x y : R) :
    (type1OfField sh1 x = type1OfField sh1 y ↔ x = y)
    ∧ (type2OfField sh2 x = type2OfField sh2 y ↔ x = y) :=
  ⟨type1_eq_iff sh1 h1 x y, type2_eq_iff sh2 x y⟩

end Checks

/-! ## §P3.5 — a CONCRETE negative pole for the challenge coordinates.

The four tamper theorems above cover the four CHECKED slots. The challenge coordinates
(α, β, γ, ζ, the round challenges) admit no generic tamper theorem: `finalizeOtherProof` recomputes
its three actuals FROM them, so a tamper that happens to collide leaves the decision unchanged, and
no ring-generic statement can rule a collision out. What can be shown is that a tamper is not
generally free — i.e. the recomputations really depend on the challenges. That needs a concrete
ring, so it is done at `ZMod 97` with an 8-point domain.

This is a MODEL, not a fixture: the Pasta instantiation is the generic theorems above, which hold
at `ZMod pN` and `ZMod qN` unchanged. -/

section Pole

/-- A small ring where the folds reduce in the kernel. -/
abbrev T := ZMod 97

/-- Toy gate evals. Only the arithmetic shape matters — this exists to make a `decide` reduce. -/
def toyGate : GateEvals T :=
  { alpha := 0, endo := 5, mds := [[1, 2], [3, 4]], coeff := [1, 2, 3],
    w := [1, 2, 3, 4, 5, 6, 7], wNext := [2, 3, 4], cA := 1, cB := 2, cC := 3,
    genSel := 1, posSel := 0, caddSel := 0, mulSel := 0, emulSel := 0, emulScalarSel := 0 }

/-- A toy `OtherProof` over `T`. -/
def toyOp : OtherProof T :=
  { n := 8, omega := 3, srsLengthLog2 := 3, g := toyGate,
    s := [1, 2, 3, 4, 5, 6], shift := [1, 2, 3, 4, 5, 6, 7],
    zZeta := 11, zZetaOmega := 13, pZeta := 17, denomInv := 1,
    evZetaPre := [2, 3], evZetaPost := [5], evZetaOmegaPre := [7, 11], evZetaOmegaPost := [13],
    ftEval1 := 19, xiSqueeze := 23, rSqueeze := 29 }

/-- A toy sampled tuple. -/
def toySm : Sampled T := { beta := 5, gamma := 7, alpha := 2, zeta := 3, bpChals := [2, 3, 5] }

/-- Toy bridge and endo map (both injective on `T`: `3` is a unit mod 97). -/
def toyEncode : T → T := fun x => x - 41
/-- The decoder. -/
def toyDecode : T → T := fun x => x + 41
/-- The endo map stand-in. -/
def toyEndo : T → T := fun x => 3 * x + 1

/-- **`toy_finalize_accepts`** — the toy instance is genuinely accepting, in the kernel. Without
this the rejects below would be uninformative. -/
theorem toy_finalize_accepts :
    finalizeOtherProof toyDecode toyEndo toyOp
        (honestDeferred toyEncode toyEndo toyOp toySm ⟨2, 3⟩ none) = true := by
  decide

/-- **`toy_zeta_tamper_rejects`** — moving ζ while leaving the rest of the honest record alone is
CAUGHT, here, by the recomputations. This is the negative pole the challenge coordinates get: it is
an existence statement about one instance, not a theorem about all of them. -/
theorem toy_zeta_tamper_rejects :
    finalizeOtherProof toyDecode toyEndo toyOp
        (let h := honestDeferred toyEncode toyEndo toyOp toySm ⟨2, 3⟩ none
         { h with plonk := { h.plonk with
             minimal := { h.plonk.minimal with zeta := 4 } } }) = false := by
  decide

/-- **`toy_bpchal_tamper_rejects`** — and moving one bulletproof round challenge is caught by
`b_correct`. -/
theorem toy_bpchal_tamper_rejects :
    finalizeOtherProof toyDecode toyEndo toyOp
        (let h := honestDeferred toyEncode toyEndo toyOp toySm ⟨2, 3⟩ none
         { h with bulletproofChallenges := [2, 3, 7] }) = false := by
  decide

/-- **`toy_zeta_powers_free`** — and the two derived scalars are NOT caught, in the same instance.
The generic `finalize_ignores_zeta_powers` says the decision cannot read them; this says the
decision that cannot read them is one that ACCEPTS. -/
theorem toy_zeta_powers_free :
    finalizeOtherProof toyDecode toyEndo toyOp
        (let h := honestDeferred toyEncode toyEndo toyOp toySm ⟨2, 3⟩ none
         { h with plonk := { h.plonk with zetaToSrsLength := 77, zetaToDomainSize := 88 } })
      = true := by
  decide

end Pole

/-! ## §P3.6 — the two Pasta bridges discharge `finalize_complete`'s hypothesis.

`finalize_complete` asks for `decode ∘ encode = id`. P2 proved exactly that for both sides
(`type1_to_of` under `Shift1.ok`, `type2_to_of` unconditionally), and `pasta_shift_constants`
proved the concrete `shift1Fp` is `ok`. So P3 runs at BOTH sides of the cycle with one body — the
same "one verifier body, two shapes" P0 established, and the reason P5 is a field swap. -/

/-- **`finalize_complete_both_bridges`** — P3's accept holds at the Step bridge (Type1 over `Fp`)
and at the Wrap bridge (Type2 over `Fq`), from P2's round-trip theorems. UNCONDITIONAL: the Type1
side's `Shift1.ok` side condition is discharged from P2's kernel-checked `pasta_shift_constants`,
not assumed. -/
theorem finalize_complete_both_bridges
    (opP : OtherProof Fp) (smP : Sampled Fp) (endoP : Fp → Fp)
    (opQ : OtherProof Fq) (smQ : Sampled Fq) (endoQ : Fq → Fq)
    (bd : BranchData) :
    finalizeOtherProof (type1ToField shift1Fp) endoP opP
        (honestDeferred (type1OfField shift1Fp) endoP opP smP bd none) = true
    ∧ finalizeOtherProof (type2ToField shift2Fq) endoQ opQ
        (honestDeferred (type2OfField shift2Fq) endoQ opQ smQ bd none) = true := by
  refine ⟨?_, ?_⟩
  · exact finalize_complete _ _ _
      (fun x => type1_to_of shift1Fp pasta_shift_constants.2.1 x) opP smP bd none
  · exact finalize_complete _ _ _ (fun x => type2_to_of shift2Fq x) opQ smQ bd none

/-- The two sides use different bridges, so the above really is two instantiations
(`shiftKindFor`, P2). -/
theorem finalize_runs_on_both_sides :
    shiftKindFor Side.step ≠ shiftKindFor Side.wrap := by decide

/-! ## §P4 — the transcript-equality binding.

Everything above is a check the record makes against ITSELF: `finalizeOtherProof` recomputes from
`sampledOf dv`, which is read out of the attacker-supplied record. Nothing so far says those
challenges are the ones the group sub-verifier squeezed. That is the whole of P4, and Pickles
effects it with three families of `Field.Assert.equal`:

  1. **`assert_eq_plonk`** (`wrap_verifier.ml:492-499`, called at `:717-731` from INSIDE
     `incrementally_verify_proof`, after the sponge has produced β,γ,α,ζ) — the four sampled
     challenges equal the four exposed ones, compared as raw prechallenges.
  2. **The sponge-digest equality** (`wrap_main.ml:430-432`) — the exposed
     `sponge_digest_before_evaluations` equals the one `incrementally_verify_proof` returned.
  3. **The per-round bulletproof-challenge equality** (`wrap_main.ml:433-439`; Step mirror
     `step_verifier.ml:1271-1285`) — each of the `k` exposed round prechallenges equals the one the
     IPA group check consumed at that round.

§P4.1 writes them down. §P4.2 proves what they pin. §P4.3 proves each one is load-bearing.
§P4.4 proves what is left free and locates where it is (not) tied. §Z states what P4 still needs. -/

section Binding

variable {R : Type} [CommRing R] [DecidableEq R]

/-- (1) `assert_eq_plonk` — the four IOP challenges (`wrap_verifier.ml:492-499`). -/
def assertEqPlonk (sm : Sampled R) (dv : WrapDeferredValues R R R) : Prop :=
  sm.beta = dv.plonk.minimal.beta ∧ sm.gamma = dv.plonk.minimal.gamma
  ∧ sm.alpha = dv.plonk.minimal.alpha ∧ sm.zeta = dv.plonk.minimal.zeta

/-- (2) the sponge-digest equality (`wrap_main.ml:430-432`). The digest is a field of the
STATEMENT, not of `Deferred_values`, so it is carried separately. -/
def assertEqDigest (sampledDigest exposedDigest : R) : Prop := sampledDigest = exposedDigest

/-- (3) the per-round bulletproof-challenge equality (`wrap_main.ml:433-439`). -/
def assertEqBpChals (sm : Sampled R) (dv : WrapDeferredValues R R R) : Prop :=
  sm.bpChals = dv.bulletproofChallenges

/-- **The binding**, as one predicate. -/
def transcriptBinding (sm : Sampled R) (sampledDigest exposedDigest : R)
    (dv : WrapDeferredValues R R R) : Prop :=
  assertEqPlonk sm dv ∧ assertEqDigest sampledDigest exposedDigest ∧ assertEqBpChals sm dv

/-! ### §P4.2 — what the binding pins.

The two challenge families are exactly the coordinates `sampledOf` reads, so together they say
"the tuple the record claims IS the tuple the transcript produced" — and then, because the three
recomputations are functions of that tuple and `decode` is injective, the three shifted scalars are
forced too. `binding_and_accept_determine` is that composition: any two records that are bound to
the same transcript AND both accepted agree on every coordinate `finalizeOtherProof` touches. -/

omit [CommRing R] [DecidableEq R] in
/-- The two challenge asserts are jointly equivalent to pinning `sampledOf`. -/
theorem binding_is_sampledOf (sm : Sampled R) (dv : WrapDeferredValues R R R) :
    (assertEqPlonk sm dv ∧ assertEqBpChals sm dv) ↔ sm = sampledOf dv := by
  constructor
  · rintro ⟨⟨hb, hg, ha, hz⟩, hc⟩
    simp only [assertEqBpChals] at hc
    cases sm; simp_all [sampledOf]
  · rintro rfl
    exact ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩

/-- **`binding_is_satisfiable`** — the anti-vacuity guard for everything in §P4.2: the hypothesis
set "bound to this transcript AND accepted" is INHABITED. Without this, a coverage theorem over an
empty premise would be true and worthless — which is the failure this tree has met before. -/
theorem binding_is_satisfiable (encode decode endo : R → R) (hde : ∀ x, decode (encode x) = x)
    (op : OtherProof R) (sm : Sampled R) (bd : BranchData) (d : R) :
    ∃ dv : WrapDeferredValues R R R,
      transcriptBinding sm d d dv ∧ finalizeOtherProof decode endo op dv = true :=
  ⟨honestDeferred encode endo op sm bd none,
   ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl⟩,
   finalize_complete encode decode endo hde op sm bd none⟩

/-- **`binding_and_accept_determine`** — the P4 coverage theorem. Two deferred-values records bound
to the SAME transcript and both accepted by `finalizeOtherProof` agree on: the four IOP challenges,
ξ, the `k` round challenges, `combined_inner_product`, `b`, and `perm`. The challenge coordinates
come from the binding; the three scalars are then FORCED, because each actual is a function of the
bound tuple alone and `decode` is injective.

What is deliberately absent from the conclusion is `zeta_to_srs_length` and `zeta_to_domain_size` —
see §P4.4. -/
theorem binding_and_accept_determine (decode endo : R → R) (hinj : Function.Injective decode)
    (op : OtherProof R) (sm : Sampled R) (d de de' : R)
    (dv dv' : WrapDeferredValues R R R)
    (hb : transcriptBinding sm d de dv) (hb' : transcriptBinding sm d de' dv')
    (ha : finalizeOtherProof decode endo op dv = true)
    (ha' : finalizeOtherProof decode endo op dv' = true) :
    dv.plonk.minimal.beta = dv'.plonk.minimal.beta
    ∧ dv.plonk.minimal.gamma = dv'.plonk.minimal.gamma
    ∧ dv.plonk.minimal.alpha = dv'.plonk.minimal.alpha
    ∧ dv.plonk.minimal.zeta = dv'.plonk.minimal.zeta
    ∧ dv.bulletproofChallenges = dv'.bulletproofChallenges
    ∧ dv.xi = dv'.xi
    ∧ dv.b = dv'.b
    ∧ dv.combinedInnerProduct = dv'.combinedInnerProduct
    ∧ dv.plonk.perm = dv'.plonk.perm := by
  obtain ⟨hp, -, hc⟩ := hb
  obtain ⟨hp', -, hc'⟩ := hb'
  have hs : sm = sampledOf dv := (binding_is_sampledOf sm dv).mp ⟨hp, hc⟩
  have hs' : sm = sampledOf dv' := (binding_is_sampledOf sm dv').mp ⟨hp', hc'⟩
  have hsame : sampledOf dv = sampledOf dv' := hs.symm.trans hs'
  simp only [finalizeOtherProof, xiCorrect, bCorrect, cipCorrect, plonkChecksPassed,
    Bool.and_eq_true, decide_eq_true_eq] at ha ha'
  obtain ⟨⟨⟨hxi, hb1⟩, hcip⟩, hperm⟩ := ha
  obtain ⟨⟨⟨hxi', hb1'⟩, hcip'⟩, hperm'⟩ := ha'
  have hxieq : dv.xi = dv'.xi := hxi.symm.trans hxi'
  refine ⟨?_, ?_, ?_, ?_, ?_, hxieq, ?_, ?_, ?_⟩
  · exact congrArg Sampled.beta hsame
  · exact congrArg Sampled.gamma hsame
  · exact congrArg Sampled.alpha hsame
  · exact congrArg Sampled.zeta hsame
  · exact congrArg Sampled.bpChals hsame
  · exact hinj (hb1.trans (by rw [hsame] ; exact hb1'.symm))
  · exact hinj (hcip.trans (by rw [hsame, hxieq] ; exact hcip'.symm))
  · exact hinj (hperm.trans (by rw [hsame] ; exact hperm'.symm))

/-! ### §P4.3 — each assert family is LOAD-BEARING.

The three families are not redundant with the four checks. For each, the attack that appears when
it is dropped is exhibited, at every ring (given only `Nontrivial`, so that `x + 1 ≠ x`) — no
concrete fixture, nothing tuned to a witness. -/

/-- **`plonk_assert_is_necessary`** — drop `assert_eq_plonk` and the remaining asserts plus all
four checks admit a record whose ζ the transcript never produced. The forged record is honest AT
ITS OWN ζ, which is precisely why `finalize_other_proof` cannot catch it: it recomputes from the
record. Only the equality to the SAMPLED ζ can.

(`assertEqBpChals` still holds, and the digest assert is untouched — so exactly one family is
being dropped.) -/
theorem plonk_assert_is_necessary [Nontrivial R]
    (encode decode endo : R → R) (hde : ∀ x, decode (encode x) = x)
    (op : OtherProof R) (sm : Sampled R) (bd : BranchData) :
    ∃ dv : WrapDeferredValues R R R,
      assertEqBpChals sm dv
      ∧ finalizeOtherProof decode endo op dv = true
      ∧ ¬ assertEqPlonk sm dv := by
  refine ⟨honestDeferred encode endo op { sm with zeta := sm.zeta + 1 } bd none, rfl, ?_, ?_⟩
  · exact finalize_complete encode decode endo hde op _ bd none
  · rintro ⟨-, -, -, hz⟩
    simp only [honestDeferred] at hz
    have h01 : (0 : R) = 1 := by linear_combination hz
    exact one_ne_zero h01.symm

/-- **`bp_assert_is_necessary`** — drop the per-round equality and a record with a different round
challenge is admitted, honest at its own challenges. `b_correct` recomputes the challenge
polynomial FROM the exposed challenges, so it cannot distinguish; only the per-round equality to
the challenges the IPA group check consumed can.

(`assertEqPlonk` still holds — again exactly one family dropped.) -/
theorem bp_assert_is_necessary
    (encode decode endo : R → R) (hde : ∀ x, decode (encode x) = x)
    (op : OtherProof R) (sm : Sampled R) (bd : BranchData) (cs : List R) (hcs : cs ≠ sm.bpChals) :
    ∃ dv : WrapDeferredValues R R R,
      assertEqPlonk sm dv
      ∧ finalizeOtherProof decode endo op dv = true
      ∧ ¬ assertEqBpChals sm dv := by
  refine ⟨honestDeferred encode endo op { sm with bpChals := cs } bd none,
    ⟨rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
  · exact finalize_complete encode decode endo hde op _ bd none
  · intro h
    exact hcs h.symm

/-- **`digest_assert_is_necessary`** — the third family, same shape and the sharpest of the three:
the digest is not a field of `Deferred_values`, so `finalizeOtherProof` has no argument in which it
could appear. There is therefore an accepting record for EVERY exposed digest, wrong ones included,
with the other two families intact. The sponge-digest equality is the only thing in the circuit
tying the sponge state that produced β,γ,α,ζ,ξ,r to the state the outer verifier reconstructed
(`wrap_main.ml:430-432`). -/
theorem digest_assert_is_necessary [Nontrivial R]
    (encode decode endo : R → R) (hde : ∀ x, decode (encode x) = x)
    (op : OtherProof R) (sm : Sampled R) (bd : BranchData) (sampledDigest : R) :
    ∃ (dv : WrapDeferredValues R R R) (exposedDigest : R),
      assertEqPlonk sm dv ∧ assertEqBpChals sm dv
      ∧ finalizeOtherProof decode endo op dv = true
      ∧ ¬ assertEqDigest sampledDigest exposedDigest := by
  refine ⟨honestDeferred encode endo op sm bd none, sampledDigest + 1,
    ⟨rfl, rfl, rfl, rfl⟩, rfl, finalize_complete encode decode endo hde op sm bd none, ?_⟩
  intro hd
  simp only [assertEqDigest] at hd
  have h01 : (0 : R) = 1 := by linear_combination hd
  exact one_ne_zero h01.symm

end Binding

section FtComm

variable {R : Type} [CommRing R]

/-! ### §P4.4 — the free coordinates, and where they are (not) tied.

`binding_and_accept_determine` covers nine coordinates. Two are missing, and the omission is real:
`zeta_to_srs_length` and `zeta_to_domain_size` are pinned by NOTHING in the binding (they are not
challenges) and by NOTHING in the four checks (`finalize_ignores_zeta_powers`). Their only tie is
the GROUP side, where they are used as scalars in the `ft_comm` assembly
(`wrap.rs:1372-1396`, `step.rs:1093-1106`; OCaml `wrap_verifier.ml:640-676`):

    chunked_t_comm = fold over t_comm chunks with  zeta_to_srs_length
    ft_comm        = f_comm + chunked_t_comm − zeta_to_domain_size · chunked_t_comm

`picklesFtComm` transcribes that. The theorem below is the exact statement of the tie: the
in-circuit assembly equals K5's `ftComm` — which recomputes `ζⁿ − 1` instead of trusting the
exposed slot — **exactly when the exposed `zeta_to_domain_size` is the honest `ζⁿ`**. So a forged
`zeta_to_domain_size` yields a DIFFERENT `ft_comm`, and the only thing that then rejects is the IPA
opening check on that commitment. That is P10, the inherited floor.

And one sharper fact, because chunk count decides it: the `zeta_to_srs_length` fold is a `reduce`,
so with a single `t_comm` chunk it is never applied. At `chunk_size = 1` that slot is unconstrained
on the group side as well. Mina's `t_comm` has 7 chunks, so the fold does run — but the statement
must be conditional, and it is. -/

/-- The in-circuit chunk fold (`wrap.rs:1379-1387`): `reduce` over the reversed chunk list, scaling
the accumulator by the exposed `zeta_to_srs_length` at each step. `reduce` on a singleton never
applies the step — that is the point of `ftComm_srs_length_unused_at_one_chunk`. -/
def picklesChunkedTComm (zetaToSrsLength : R) : List R → R
  | [] => 0
  | c :: rest => match rest with
    | [] => c
    | _ => c + zetaToSrsLength * picklesChunkedTComm zetaToSrsLength rest

/-- The in-circuit `ft_comm` (`wrap.rs:1372-1396`): `f_comm + T − zeta_to_domain_size·T` where
`T = chunked_t_comm`. Written over a commutative ring (K5's `ftComm` is module-generic; the tie
being proved is scalar, so `R` suffices and the statement is sharper for it). -/
def picklesFtComm (zetaToSrsLength zetaToDomainSize fComm : R) (tChunks : List R) : R :=
  let t := picklesChunkedTComm zetaToSrsLength tChunks
  fComm + t - zetaToDomainSize * t

/-- **`ftComm_ties_zeta_to_domain_size`** — the in-circuit assembly agrees with the RECOMPUTED
Maller form `f_comm − (ζⁿ − 1)·T` iff `(zeta_to_domain_size − ζⁿ)·T = 0`. In particular the honest
value makes them agree, and any forgery moves `ft_comm` by exactly `(forged − ζⁿ)·T`. This is where
the two free scalars are tied — a group-element equality discharged by the IPA opening, not by any
equality in `finalize_other_proof`. -/
theorem ftComm_ties_zeta_to_domain_size (n : Nat) (zeta zTSL zTDS fComm : R) (tChunks : List R) :
    picklesFtComm zTSL zTDS fComm tChunks
      = fComm - (zeta ^ n - 1) * picklesChunkedTComm zTSL tChunks
        - (zTDS - zeta ^ n) * picklesChunkedTComm zTSL tChunks := by
  simp only [picklesFtComm]
  ring

/-- **`ftComm_honest_agrees`** — at the honest `zeta_to_domain_size = ζⁿ` the in-circuit assembly
IS the recomputed Maller form. (`zetaToDomainSizeR` is `derive_plonk`'s own definition, so this is
the derivation and the group assembly agreeing, not two hand-written formulas agreeing.) -/
theorem ftComm_honest_agrees (n : Nat) (zeta zTSL fComm : R) (tChunks : List R) :
    picklesFtComm zTSL (zetaToDomainSizeR n zeta) fComm tChunks
      = fComm - (zeta ^ n - 1) * picklesChunkedTComm zTSL tChunks := by
  simp only [picklesFtComm, zetaToDomainSizeR]
  ring

/-- **`ftComm_forgery_moves_it`** — and a forgery is not free: over a domain, if `T ≠ 0` then a
`zeta_to_domain_size` other than `ζⁿ` produces a DIFFERENT `ft_comm`. So the group check is a real
constraint on the slot — it is simply not an equality the scalar checks can see. -/
theorem ftComm_forgery_moves_it {D : Type} [CommRing D] [IsDomain D]
    (n : Nat) (zeta zTSL zTDS fComm : D) (tChunks : List D)
    (hT : picklesChunkedTComm zTSL tChunks ≠ 0) (hz : zTDS ≠ zeta ^ n) :
    picklesFtComm zTSL zTDS fComm tChunks
      ≠ picklesFtComm zTSL (zetaToDomainSizeR n zeta) fComm tChunks := by
  intro h
  rw [ftComm_honest_agrees, ftComm_ties_zeta_to_domain_size (n := n) (zeta := zeta)] at h
  have : (zTDS - zeta ^ n) * picklesChunkedTComm zTSL tChunks = 0 := by linear_combination -h
  rcases mul_eq_zero.mp this with h1 | h2
  · exact hz (by linear_combination h1)
  · exact hT h2

/-- **`ftComm_srs_length_unused_at_one_chunk`** — with a single `t_comm` chunk the exposed
`zeta_to_srs_length` is not read by the group assembly either, so at `chunk_size = 1` that slot is
unconstrained on BOTH sides. Mina runs 7 chunks; the point is that the tie is conditional on chunk
count and must be stated that way. -/
theorem ftComm_srs_length_unused_at_one_chunk (a b : R) (c : R) :
    picklesChunkedTComm a [c] = picklesChunkedTComm b [c] := rfl

/-- **`ftComm_srs_length_used_at_two_chunks`** — and with two chunks it IS read: the assembly
separates two different exposed values whenever the second chunk is nonzero. -/
theorem ftComm_srs_length_used_at_two_chunks {D : Type} [CommRing D] [IsDomain D]
    (a b c0 c1 : D) (hc : c1 ≠ 0) (hab : a ≠ b) :
    picklesChunkedTComm a [c0, c1] ≠ picklesChunkedTComm b [c0, c1] := by
  intro h
  have : (a - b) * c1 = 0 := by
    simp only [picklesChunkedTComm] at h
    linear_combination h
  rcases mul_eq_zero.mp this with h1 | h2
  · exact hab (by linear_combination h1)
  · exact hc h2

end FtComm

/-! ## §Y — Axiom hygiene. -/

#assert_axioms derivePlonk_perm_is_K5_permScalar
#assert_axioms derived_scalars_closed_form
#assert_axioms sampledOf_honest
#assert_axioms finalize_complete
#assert_axioms finalize_xi_tamper
#assert_axioms finalize_b_tamper
#assert_axioms finalize_cip_tamper
#assert_axioms finalize_perm_tamper
#assert_axioms finalize_ignores_zeta_powers
#assert_axioms zeta_powers_stay_free
#assert_axioms plonk_check_shifted_or_field
#assert_axioms toy_finalize_accepts
#assert_axioms toy_zeta_tamper_rejects
#assert_axioms toy_bpchal_tamper_rejects
#assert_axioms toy_zeta_powers_free
#assert_axioms finalize_complete_both_bridges
#assert_axioms finalize_runs_on_both_sides
#assert_axioms binding_is_sampledOf
#assert_axioms binding_is_satisfiable
#assert_axioms binding_and_accept_determine
#assert_axioms plonk_assert_is_necessary
#assert_axioms bp_assert_is_necessary
#assert_axioms digest_assert_is_necessary
#assert_axioms ftComm_ties_zeta_to_domain_size
#assert_axioms ftComm_honest_agrees
#assert_axioms ftComm_forgery_moves_it
#assert_axioms ftComm_srs_length_unused_at_one_chunk
#assert_axioms ftComm_srs_length_used_at_two_chunks

#assert_namespace_axioms Dregg2.Circuit.Emit.PicklesFinalize

/-! ## §Z — status, stated conservatively.

### P3 — BUILT.

All four checks, assembled from the pieces P0–P2 left plus the one new derivation; a satisfying
model that is universally quantified rather than a KAT; four tamper poles on the four checked
coordinates; a concrete pole for the challenge coordinates; and the two Pasta bridges discharging
the completeness hypothesis, so P5's field swap is the same body.

**P3's residuals, precisely:**

  1. **`plonk_checks_passed` is one comparison, not three.** `derive_plonk` computes three derived
     scalars; `checked` compares `perm` only, in both implementations. That is transcribed
     faithfully, and `finalize_ignores_zeta_powers` / `zeta_powers_stay_free` are the measurement.
     A model that compared all three would be STRICTER than Pickles and its tamper poles would be
     fiction.
  2. **The 128-bit prechallenge structure is absent.** `endo` is an abstract `R → R`; the real
     `to_field_checked::<F,128>` also RANGE-CHECKS. Nothing here models that range check, so
     nothing here says a prechallenge is 128 bits.
  3. **`ft_eval1` is taken as given**, exactly as the real code takes it (`step.rs:545`); only
     `ft_eval0` is recomputed.
  4. **`branch_data` selects the domain in the real code** (`step.rs:598-604`) and here the domain
     is a field of `OtherProof`. `finalizeOtherProof` not reading `branchData` is therefore a
     MODELING choice — it is P8's job, and it must not be read as "branch_data is unconstrained".
  5. **Feature flags / lookup are out**, as they are in the Wrap instantiation
     (`wrap_verifier.ml:1017` "This proof is a wrap proof; no need to consider features").
  6. **The sponge is abstract.** `xiSqueeze` / `rSqueeze` are given values, not computed by a
     Poseidon permutation — the Fq-state sponge is still the named K3/P0 residual.

### P4 — NOT PROVED. What is here, and what is missing.

**Here:** the three assert families as one predicate; `binding_and_accept_determine`, which proves
that binding + acceptance pins nine coordinates; `plonk_assert_is_necessary` and
`bp_assert_is_necessary`, which prove two of the three families load-bearing by exhibiting the
forgery admitted when each is dropped; `finalize_ignores_digest`, which proves the third cannot be
discharged by the checks because they never read it; and §P4.4, which locates the two free
coordinates on the group side and proves the tie there is a commitment equality.

**Missing — all three are required before "the deferred values ARE the opposite proof's":**

  1. **The sponge is not a random oracle here.** `assertEqDigest` pins one field element. That this
     pins the TRANSCRIPT — that no second transcript yields the same digest — is a collision-
     resistance assumption about Poseidon-over-Pasta. There is no such assumption object in this
     tree, and `feedback-grounding-efficient-adversaries` is where the cost model for one would
     have to live. Without it, the digest equality pins a value, not a history.
  2. **`endo` injectivity is a hypothesis, not a theorem.** `binding_and_accept_determine` takes
     `Function.Injective decode` and discharges it from P2 for both bridges. It does NOT take
     injectivity of `endo`, because it does not need it — but any statement of the form "the
     SCALARS used are the sampled ones" does, and the 128-bit endo map's injectivity is not proven
     anywhere here.
  3. **The two free scalars bottom out in P10.** §P4.4 proves a forged `zeta_to_domain_size` moves
     `ft_comm`; it does not prove that a moved `ft_comm` is rejected. That is the IPA opening
     soundness floor — `ipa.rs:501`, `urs_utils.rs:67` — which `PicklesRecursion` §Z item 5 already
     names as inherited and not dischargeable in-kernel.

So the honest sentence is: **the equality asserts pin what §P4.2 says they pin, they are each
load-bearing, and two public-input coordinates are left to the group check. The step from there to
"the recursion is sound" needs a random-oracle assumption, an injectivity fact, and P10 — none of
which is in this tree.** Anything stronger than that sentence is over-claiming, and this is the one
theorem where over-claiming is worse than the gap.

### The P5 handoff

P5 (mirror to the other side) is now genuinely a field swap: `finalizeOtherProof` is
`[CommRing R]`-generic with `decode` a parameter, and `finalize_complete_both_bridges` already runs
it at Type1-over-`Fp` and Type2-over-`Fq`. What P5 must still supply is the Step-side record shape
(`StepDeferredValues`, no `branch_data` — P2 has it) and the Step-side pin set
(`step_verifier.ml:1271-1285`), not new algebra.
-/

end Dregg2.Circuit.Emit.PicklesFinalize
