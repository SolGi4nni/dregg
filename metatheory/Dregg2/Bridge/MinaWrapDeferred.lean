/-
# Dregg2.Bridge.MinaWrapDeferred — **`expand_deferred`: the six Wrap public-input words that
existed nowhere in this tree, as a COMPILED function of the proof's own bytes.**

⚑ **SUBSTRATE.** No AIR. A sponge schedule, an endomorphism lift, three field folds and a shift —
authored in Lean because *which* value is absorbed in *which* order is the whole content of "these
are the proof's own deferred values", exactly as it is in `MinaWrapChallenges`.

## What this closes

`MinaWrapPublicInput`'s census measured **34 of 40**. The six it could not reach —
`combined_inner_product`, `b`, `zeta_to_srs_length`, `zeta_to_domain_size`, `perm`, `xi` — are
`expand_deferred`'s outputs, and that function did not exist in this tree in any language
(`grep -rn expand_deferred metatheory/ bridge/` returned doc prose only). This file is it.

Rendered from BOTH implementations, which agree:

  * OCaml `src/lib/pickles/wrap_deferred_values.ml` `expand_deferred` (the authority);
  * openmina `ledger/src/proofs/verification.rs:340-420`, where the same computation is present
    but **commented out** — so the Rust side of the ecosystem does not run it either.

## ⚑⚑ THE FIELD, said out loud, because it is the trap

`expand_deferred` computes in **`Tick.Field` = `Fp` = `pN`** — the STEP proof's scalar field —
even though its outputs land in the Wrap proof's `Fq`-valued public input. `pN < qN`, so the
embedding is the identity on canonical elements and no reduction is visible; a file that did the
arithmetic mod `qN` would agree on *nothing* and look merely "wrong by a bit". Every `% pN` below
is load-bearing.

## ⚑⚑ THE SLOT ORDER — a MEASURED correction to `MinaWrapPublicInput`

`Wrap.Statement.to_data` (`composition_types.ml:826-880`) lays the public input out as

```text
fp               = [combined_inner_product; b; zeta_to_srs_length; zeta_to_domain_size; perm]  -- 0-4
challenge        = [beta; gamma]                                                               -- 5-6
scalar_challenge = [alpha; zeta; xi]                                                           -- 7-9
digest           = [sponge_digest; mnw; mns]                                                   -- 10-12
bulletproof_challenges                                                                          -- 13-28
index            = [branch_data]                                                                -- 29
```

so slots 5-9 are **`beta, gamma, alpha, zeta, xi`** — NOT `alpha, beta, gamma, zeta, xi`, which is
what `MinaWrapPublicInput.publicInputWords` says. `MinaWrapPublicInput` itself flagged that reading
as UNMEASURED; the weld measures it, and it is wrong at slots 5 and 7. See
`MinaWrapDeferredWeld` §5 — the correction is exhibited on the real block by `perm`, which reads
β, γ and α in three distinct roles and reproduces the block's slot-4 word only under this order.

## What is a wire value and what is not

Everything `WrapEvals` carries is decoded by `bridge/src/mina_pickles.rs` `decode_proof_at` today
and thrown away: `prev_evals` (43 columns × 2 points, `public_input`, `ft_eval1`),
`messages_for_next_step_proof.old_bulletproof_challenges`, `deferred_values.plonk.{α′,β,γ,ζ′}`,
`deferred_values.bulletproof_challenges`, `sponge_digest_before_evaluations`, `branch_data`.

Two things are NOT wire and are named as arguments rather than hidden:

  * `ENDO` — `Endo.Wrap_inner_curve.scalar` = Vesta's `endo_scalar`, one `Fp` element of CONFIG.
    Identical to `KimchiPoseidonGate.ENDO_R`.
  * `ftEval0` — the STEP proof's `ft_eval0`. ⚑ This is the ONE scalar of `expandDeferred` that is
    not computed here. It is not a missing *source* either: it is `KimchiVerify.ftEval0R` over the
    same wire evals, whose own residual is (a) the seven Tick coset `shifts` and (b)
    `Plonk_checks.Scalars.Tick.constant_term` — ~3,300 lines of generated OCaml
    (`plonk_checks/scalars.ml:106-3400`) which this tree carries as the `linConstTerm` NAMED
    CARRIER (`KimchiVerify.ftEval0R`, `MinaRealBlockGate.LCT`) on the Wrap side and does not have
    on the Step side. **`combined_inner_product` is therefore derived to within that one scalar,
    and nothing here should be read as saying otherwise.** The other five words take no carrier.

`omega` is DERIVED, not carried: `rootOfUnity` computes the 2^`log2n` root of unity in `Fp` from
the multiplicative generator 5, and the weld pins its exact order.

## Cost

Compiled, not kernel. Every pin in the weld is `#guard`, for the reason `MinaWrapChallenges` gives:
the kernel's job is the CHECKER, the differential's job is the INSTANCE. Nothing here is
`by decide` over a sponge, and `powMod`/`sqMod` exist because `Nat`'s `^` at exponent 2^16 builds
an 8-million-bit integer before it reduces.

NOT imported by the `Dregg2` root, per house practice for gates. ⚑ And not yet rooted in
`Dregg2/FFI.lean` either, deliberately: it imports `MinaWrapPublicInput` for `DeferredWords`
rather than duplicating the six-field record, and that import drags
`MinaWrapPublicInputFromHeader`'s closure. Rooting it means moving `DeferredWords` down to a light
module and DELETING it from `MinaWrapPublicInput` — a one-move follow-on, named here rather than
paid for by a second copy of the record.
-/
import Dregg2.Bridge.MinaWrapPublicInput
import Dregg2.Circuit.Emit.PastaPoseidonFq
import Dregg2.Circuit.Emit.PastaField

set_option autoImplicit false
set_option maxRecDepth 40000

namespace Dregg2.Bridge.MinaWrapDeferred

open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.PastaPoseidonFq
  (SpongeSt fpParams newSponge absorbMany challenge squeeze1)
open Dregg2.Bridge.MinaWrapPublicInput (DeferredWords)

/-! ## §1 — modular arithmetic that does not build 8-million-bit integers.

`Nat.pow` is exact: `ζ ^ 65536` is a 16.7-million-bit number, and `zeta_to_srs_length` asks for
exactly that. Every exponentiation below therefore reduces as it goes. -/

/-- `b ^ e % m` by square-and-multiply, structurally recursive on FUEL so the KERNEL reduces it —
a well-founded definition would get stuck in `WellFounded.fix` and the `decide` in §10 would not
close. The match is on the fuel ALONE for exactly that reason; the `e = 0` exit is an `if`, not a
second pattern. 256 bits of fuel covers every exponent in this file. -/
def powModAux (m : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, b, e, acc =>
      if e = 0 then acc
      else powModAux m fuel (b * b % m) (e / 2) (if e % 2 = 1 then acc * b % m else acc)

/-- `b ^ e % m`. -/
def powMod (b e m : Nat) : Nat := powModAux m 256 (b % m) e 1

/-- `x ^ (2^k) % m` — the squaring ladder `KimchiVerify.sqIter` asks for, with the reduction. -/
def sqMod (m : Nat) : Nat → Nat → Nat
  | 0, x => x % m
  | k + 1, x => sqMod m k (x * x % m)

/-- Field subtraction over `Nat` representatives. -/
def subMod (m a b : Nat) : Nat := (a + m - b % m) % m

/-! ## §2 — the constants, each said to be what it is. -/

/-- `Endo.Wrap_inner_curve.scalar` (`endo.ml:7`) = `Pasta_bindings.Vesta.endo_scalar ()`, a
`Tick.Field` element. ⚑ CONFIG. The same constant as `KimchiPoseidonGate.ENDO_R`; a wrong one
produces a complete, self-consistent, entirely wrong set of six words. -/
def ENDO : Nat := 8503465768106391777493614032514048814691664078728891710322960303815233784505

/-- `Common.Max_degree.step_log2 = Nat.to_int Backend.Tick.Rounds.n` (`common.ml:7`) — **16, a
CONSTANT**, not `branch_data.domain_log2`. `zeta_to_srs_length` is `ζ^(2^16)` at every domain; that
it coincides with `zeta_to_domain_size` on block 539508 is a consequence of that block's
`domain_log2` being 16 too, and is exactly the coincidence `MinaWrapPublicInput` observed at slots
2 and 3. -/
def SRS_LOG2 : Nat := 16

/-- `perm_alpha0` (`plonk_checks.ml:413`) — the offset of the permutation's α powers. -/
def PERM_ALPHA0 : Nat := 21

/-- `Shifted_value.Type1.Shift.create`'s `c = 2^{size_in_bits} + 1` at `Tick.Field`
(`shifted_value.ml:113-119`, `size_in_bits = 255`), reduced. -/
def SHIFT_C : Nat := (2 ^ 255 + 1) % pN

/-- `Shifted_value.Type1.Shift.create`'s `scale = 1/2`, as the `Fp` representative `(p+1)/2`. -/
def INV2 : Nat := (pN + 1) / 2

/-- **`shiftType1`** — `Shifted_value.Type1.of_field ~shift:Shifts.tick1`, i.e. `(x − 2^255 − 1)/2`
in `Fp` (`shifted_value.ml:129-131`). This is the encoding `combined_inner_product`, `b`,
`zeta_to_srs_length`, `zeta_to_domain_size` and `perm` all wear in the public input, and it is why
those five slots are ≥ 2^128 while the challenges are below it. -/
def shiftType1 (x : Nat) : Nat := subMod pN x SHIFT_C * INV2 % pN

/-- `Shifted_value.Type1.to_field` — `2t + c`. The inverse of [`shiftType1`]; carried so a reader
can check a public-input word against an unshifted quantity without re-deriving the algebra. -/
def unshiftType1 (t : Nat) : Nat := (2 * t + SHIFT_C) % pN

/-- `Fp`'s two-adicity is 32; `T` is the odd part of `p − 1`. -/
def TWO_ADIC_T : Nat := (pN - 1) / 2 ^ 32

/-- **`rootOfUnity log2n`** — `Backend.Tick.Field.domain_generator ~log2_size:log2n`, DERIVED
rather than carried: arkworks' `GENERATOR = 5` raised to the odd part of `p − 1`, then squared down
to order `2^log2n`. The weld pins its exact multiplicative order, and the block's own `perm` is the
falsifier for the generator choice. -/
def rootOfUnity (log2n : Nat) : Nat := sqMod pN (32 - log2n) (powMod 5 TWO_ADIC_T pN)

/-! ## §3 — the endomorphism lift and the b-polynomial, in `Nat` with reduction.

`KimchiVerify.endoMap` / `bEvalSq` are the same functions over `[CommRing R]`. They are re-expressed
here for the same reason `MinaWrapChallenges` re-expresses the sponge: this file must import the
sponge and nothing heavy, and `Nat` with an explicit modulus is what the sponge speaks. The weld
`#guard`s the results against `MinaWrapPublicInput`'s real-block words, which is the tie. -/

/-- Bit `i` of `x`. -/
def bitAt (x i : Nat) : Nat := x / 2 ^ i % 2

/-- One step of `ScalarChallenge::to_field_with_length`'s reversed loop (`sponge.rs:200-212`),
mirroring `KimchiVerify.endoStep` with `Fp` reduction. -/
def endoStep (chal i : Nat) (ab : Nat × Nat) : Nat × Nat :=
  let a := (ab.1 + ab.1) % pN
  let b := (ab.2 + ab.2) % pN
  let s := if bitAt chal (2 * i) = 0 then pN - 1 else 1
  if bitAt chal (2 * i + 1) = 0 then (a, (b + s) % pN) else ((a + s) % pN, b)

/-- **`endoLift`** — `Scalar_challenge.to_field_constant ~endo:Endo.Wrap_inner_curve.scalar`, the
128-bit-prechallenge ↦ `Fp` map `sc` that `expand_deferred` applies to ζ′, α′, ξ′, r′ and to every
bulletproof challenge it touches. -/
def endoLift (chal : Nat) : Nat :=
  let ab := (List.range 64).reverse.foldl (fun ab i => endoStep chal i ab) (2, 2)
  (ab.1 * ENDO + ab.2) % pN

/-- **`bPolyMod`** — `Wrap.challenge_polynomial` (`wrap.ml:15-17`,
`wrap_verifier.challenge_polynomial`): `Π_i (1 + c_i · x^(2^(k−1−i)))`, in the squaring-ladder form
`KimchiVerify.bEvalSq` uses so no exponent is ever materialised. -/
def bPolyMod (x : Nat) : List Nat → Nat
  | [] => 1
  | c :: rest => bPolyMod x rest * ((1 + c * sqMod pN rest.length x) % pN) % pN

/-! ## §4 — the wire, as one record.

Field names are the WIRE's. Every one of these is walked by `bridge/src/mina_pickles.rs`
`decode_proof_at` today and discarded because nothing asked. -/

/-- **Everything `expand_deferred` reads.** -/
structure WrapEvals where
  /-- `sponge_digest_before_evaluations` — public-input slot 10, and the `Fr`-sponge's SEED.
  That is what it is on the wire for. -/
  spongeDigest : Nat
  /-- `messages_for_next_step_proof.old_bulletproof_challenges` — 2 × 16 RAW 128-bit
  prechallenges. Lifted through [`endoLift`] here (`Ipa.Step.compute_challenges`). -/
  oldChals : List (List Nat)
  /-- `prev_evals.ft_eval1`. -/
  ftEval1 : Nat
  /-- `prev_evals.evals.public_input` — the pair `(x̂(ζ), x̂(ζω))`. -/
  pubEval : Nat × Nat
  /-- `prev_evals.evals.evals`, **43 columns**, each the pair `(at ζ, at ζω)`, in
  `Plonk_types.Evals.to_absorption_sequence` order (`plonk_types.ml:487-499`):
  `z`, the 6 selectors (generic, poseidon, complete_add, mul, emul, endomul_scalar), `w`×15,
  `coefficients`×15, `s`×6. ⚑ The SAME list, in the SAME order, is `Evals.to_list`
  (`plonk_types.ml:640-652`), which is what the `combined_inner_product` fold walks — so one list
  serves the absorb and the fold, and a re-ordering breaks both at once. -/
  evals : List (Nat × Nat)
  /-- `deferred_values.bulletproof_challenges` — 16 RAW 128-bit prechallenges. On the wire, and
  ALSO public-input slots 13-28: `b` is a function of words the public input already carries. -/
  bpChals : List Nat
  /-- `deferred_values.plonk.beta` — ⚑ public-input slot **5**. -/
  betaChal : Nat
  /-- `deferred_values.plonk.gamma` — ⚑ slot **6**. -/
  gammaChal : Nat
  /-- `deferred_values.plonk.alpha`, a `ScalarChallenge` — ⚑ slot **7**, not slot 5. -/
  alphaChal : Nat
  /-- `deferred_values.plonk.zeta`, a `ScalarChallenge` — slot 8. -/
  zetaChal : Nat
  /-- `branch_data.domain_log2` — the STEP domain, `Branch_data.domain`. -/
  domainLog2 : Nat
deriving Repr, DecidableEq

/-- ⚑ **THE SHAPE REFUSAL.** An absorb tape is positional: 42 columns instead of 43, or a 15-long
challenge vector where 16 belong, does not fail — it produces a different, perfectly well-formed
`xi`, and every word downstream of it is then wrong and self-consistent. Canonicality is checked
for the same reason `MinaWrapChallenges.phase1WireOk` checks it: Poseidon enters inputs through
`(state + x) % p`, so `x` and `x + p` are one element at the digest. -/
def wrapEvalsOk (e : WrapEvals) : Bool :=
  e.evals.length == 43
    && e.bpChals.length == 16
    && e.oldChals.length == 2
    && e.oldChals.all (fun v => v.length == 16 && v.all (fun c => decide (c < 2 ^ 128)))
    && e.bpChals.all (fun c => decide (c < 2 ^ 128))
    && decide (e.betaChal < 2 ^ 128) && decide (e.gammaChal < 2 ^ 128)
    && decide (e.alphaChal < 2 ^ 128) && decide (e.zetaChal < 2 ^ 128)
    && decide (e.spongeDigest < pN) && decide (e.ftEval1 < pN)
    && decide (e.pubEval.1 < pN) && decide (e.pubEval.2 < pN)
    && e.evals.all (fun p => decide (p.1 < pN) && decide (p.2 < pN))
    && decide (0 < e.domainLog2) && decide (e.domainLog2 ≤ 32)

/-! ## §5 — the `Fr`-sponge.

`wrap_deferred_values.ml:139-177`. ⚑ The sponge is `Tick_field_sponge.params` — Poseidon over
`Tick.Field = Fp`, which is the SAME parameter set as `MinaWrapChallenges`' phase-1 Fq-sponge
(`fp_kimchi`; `PastaPoseidonFq`'s header table). One instantiation, two schedules. openmina's
commented rendering says the same thing in Rust:
`EFqSponge::new(mina_poseidon::pasta::fp_kimchi::static_params())`. -/

/-- **`challengesDigest`** — a FRESH full-field sponge over the 2 × 16 **endo-lifted** old
bulletproof challenges, squeezed once (`wrap_deferred_values.ml:160-165`;
openmina `verification.rs:354-361`). This one value stands in for 32 challenges in the transcript
below, which is why a per-block path cannot skip it. -/
def challengesDigest (oldChals : List (List Nat)) : Nat :=
  (squeeze1 fpParams
    (absorbMany fpParams newSponge ((oldChals.flatten).map endoLift))).2

/-- What the `Fr`-sponge produces: ξ′ and r′, the two RAW 128-bit squeezes. ξ′ IS public-input
slot 9; r′ appears in no slot and is used only to fold the second evaluation column. -/
structure FrSqueezes where
  /-- `xi_chal` — public-input slot 9. -/
  xiChal : Nat
  /-- `r_chal` — the evaluation-scale prechallenge. -/
  rChal : Nat
deriving Repr, DecidableEq

/-- **`frSqueezesOf`** — the deferred-values transcript, in order: seed with
`sponge_digest_before_evaluations`, absorb the challenges digest, `ft_eval1`, the two public-input
evaluations, then every column's ζ array followed by its ζω array. Squeeze ξ′, then r′.

⚑ Two successive `challenge()`s are lanes 0 and 1 of the SAME permutation (`squeeze1`'s
`.squeezed 1` branch at rate 2) — the same fact `KimchiVerify.frSqueezePair` records. A reading
that permuted twice would produce a different r′ and therefore a different `b` and
`combined_inner_product` while leaving ξ correct — which is exactly the kind of half-right the
weld's per-word pins separate. -/
def frSqueezesOf (e : WrapEvals) : FrSqueezes :=
  let s0 := absorbMany fpParams newSponge
    [e.spongeDigest, challengesDigest e.oldChals, e.ftEval1, e.pubEval.1, e.pubEval.2]
  let s1 := e.evals.foldl (fun s p => absorbMany fpParams s [p.1, p.2]) s0
  let x := challenge fpParams s1
  let r := challenge fpParams x.1
  { xiChal := x.2, rChal := r.2 }

/-! ## §6 — the five algebraic words. -/

/-- **`permOf`** — `derive_plonk`'s permutation scalar (`plonk_checks.ml:482-491`), UNSHIFTED:

`− z(ζω)·β·α^21·zkp(ζ) · Π_{i<6} (γ + β·σ_i(ζ) + w_i(ζ))`

⚑ The **negation** is not decoration: `derive_plonk` ends the fold with `|> negate`, and a reading
that dropped it produces `p − perm`, a perfectly canonical `Fp` element that is wrong at slot 4 and
at every rung above it. `zkp` is `KimchiVerify.zkPolyR`'s polynomial — Mina's three zk rows —
`(ζ−ω^{n−3})(ζ−ω^{n−2})(ζ−ω^{n−1})`. -/
def permOf (n omega zeta alpha beta gamma : Nat) (w s : List Nat) (zZetaOmega : Nat) : Nat :=
  let zkp := (subMod pN zeta (powMod omega (n - 3) pN)
    * subMod pN zeta (powMod omega (n - 2) pN) % pN
    * subMod pN zeta (powMod omega (n - 1) pN)) % pN
  let init := zZetaOmega * beta % pN * powMod alpha PERM_ALPHA0 pN % pN * zkp % pN
  let res := (List.range 6).foldl
    (fun acc i => acc * ((gamma + beta * s.getD i 0 + w.getD i 0) % pN) % pN) init
  subMod pN 0 res

/-- **`bOf`** — `b_actual` (`wrap_deferred_values.ml:194-200`), UNSHIFTED:
`challenge_poly(ζ) + r · challenge_poly(ζω)` over the SIXTEEN endo-lifted
`deferred_values.bulletproof_challenges`. Those sixteen are public-input slots 13-28, so `b` is
determined by words the public input already carries plus r. -/
def bOf (zeta zetaw r : Nat) (bpChalsLifted : List Nat) : Nat :=
  (bPolyMod zeta bpChalsLifted + r * bPolyMod zetaw bpChalsLifted) % pN

/-- **`cipOf`** — `Wrap.combined_inner_product` (`wrap.ml:36-73`), UNSHIFTED.

The ξ-fold runs over **47** entries in `combine`'s order (`wrap.ml:60-66`): the b-polynomial of
each carried accumulator FIRST, then the public polynomial, then `ft`, then the 43 columns. That
is `KimchiVerify.cipR`'s poly order, and `MinaRealBlockGate` §4 pins the same order against
`proof.oracles(...)` on the Wrap side of this very block.

`Pcs_batch.combine_split_evaluations` folds `fx + ξ·acc` from the END, which is `Σ_k ξ^k v_k` with
`v_0` first; the two columns are then combined as `combine(ζ) + r · combine(ζω)`.

⚑ `ftEval0` is the ONE argument that is not a wire value — see the header. -/
def cipOf (xi r ftEval0 ftEval1 : Nat) (bpolyZeta bpolyZetaw : List Nat)
    (pubEval : Nat × Nat) (evals : List (Nat × Nat)) : Nat :=
  let zCol := bpolyZeta ++ [pubEval.1, ftEval0] ++ evals.map Prod.fst
  let wCol := bpolyZetaw ++ [pubEval.2, ftEval1] ++ evals.map Prod.snd
  (List.range zCol.length).foldl
    (fun acc k => (acc + powMod xi k pN * ((zCol.getD k 0 + r * wCol.getD k 0) % pN)) % pN) 0

/-! ## §7 — `expandDeferred`. -/

/-- **`expandDeferred`** — the six words, from the proof's own bytes and one carried `ftEval0`.

The five shifted words wear `Shifted_value.Type1`; `xi` is the RAW prechallenge, unshifted and
unlifted, because that is what the public input carries (`to_data`'s `scalar_challenge` bucket).
`plonk0.{alpha,beta,gamma,zeta}` are likewise passed through raw: `expand_deferred` overwrites
`derive_plonk`'s shifted copies of them with the originals (`wrap_deferred_values.ml:126-130`),
which is why slots 5-8 are 128-bit and slots 0-4 are not. -/
def expandDeferred (e : WrapEvals) (ftEval0 : Nat) : DeferredWords :=
  let n := 2 ^ e.domainLog2
  let omega := rootOfUnity e.domainLog2
  let zeta := endoLift e.zetaChal
  let alpha := endoLift e.alphaChal
  let zetaw := zeta * omega % pN
  let fr := frSqueezesOf e
  -- ⚑ TWO OBJECTS, ONE NAME UPSTREAM: `fr.xiChal` is the RAW prechallenge and IS public-input
  -- slot 9; `xiField` is its endo lift and is what the fold multiplies by. Conflating them
  -- produces a slot-9 word that is a 255-bit field element where a 128-bit challenge belongs —
  -- which `MinaWrapPublicInput`'s width signature would catch, and nothing else would.
  let xiField := endoLift fr.xiChal
  let rField := endoLift fr.rChal
  let bp := e.bpChals.map endoLift
  let old := e.oldChals.map (fun v => v.map endoLift)
  -- `evals` is `[z] ++ selectors(6) ++ w(15) ++ coefficients(15) ++ s(6)`, so `w` starts at 7 and
  -- `s` at 37. `derive_plonk` reads only the ζ column of both, and only the first six `w`.
  let w := ((e.evals.drop 7).take 15).map Prod.fst
  let s := ((e.evals.drop 37).take 6).map Prod.fst
  let zZetaOmega := (e.evals.getD 0 (0, 0)).2
  { cip := shiftType1 (cipOf xiField rField ftEval0 e.ftEval1
             (old.map (fun v => bPolyMod zeta v)) (old.map (fun v => bPolyMod zetaw v))
             e.pubEval e.evals)
    b := shiftType1 (bOf zeta zetaw rField bp)
    zetaToSrsLength := shiftType1 (sqMod pN SRS_LOG2 zeta)
    zetaToDomainSize := shiftType1 (sqMod pN e.domainLog2 zeta)
    perm := shiftType1 (permOf n omega zeta alpha e.betaChal e.gammaChal w s zZetaOmega)
    xi := fr.xiChal }

/-- **`expandDeferred?`** — the fail-closed entry point. `none` is a REFUSAL: a mis-shaped column
list, a short challenge vector, a non-canonical evaluation. Never six words derived "on what did
arrive". -/
def expandDeferred? (e : WrapEvals) (ftEval0 : Nat) : Option DeferredWords :=
  if wrapEvalsOk e && decide (ftEval0 < pN) then some (expandDeferred e ftEval0) else none

/-! ## §8 — the layout, CORRECTED.

⚑ `MinaWrapPublicInput.publicInputWords` places `alpha, beta, gamma` at slots 5, 6, 7.
`Wrap.Statement.to_data` places `beta, gamma, alpha`. The two agree on the LIST when the wire
record is a projection out of the very list being reassembled — which is what
`WIRE_539508` is, and is why that file's own round-trip could not see this. It is measured in
`MinaWrapDeferredWeld` §5.

Rather than edit a live sibling from this lane, the corrected layout is stated here as a function
and the weld exhibits the disagreement on real data. Deleting the wrong one is the follow-on; there
must not be two. -/

/-- **`publicInputWordsCorrected`** — the 40 words in `to_data` order. Differs from
`MinaWrapPublicInput.publicInputWords` in exactly one way: `beta, gamma, alpha` at slots 5-7. -/
def publicInputWordsCorrected (beta gamma alpha zeta spongeDigest word11 word12 : Nat)
    (d : DeferredWords) (bpChallenges : List Nat) (branchData : Nat) : List Nat :=
  [d.cip, d.b, d.zetaToSrsLength, d.zetaToDomainSize, d.perm,
   beta, gamma, alpha, zeta, d.xi,
   spongeDigest, word11, word12]
  ++ bpChallenges
  ++ [branchData]
  ++ List.replicate 10 0

/-- The corrected layout still has forty slots. -/
theorem publicInputWordsCorrected_length
    (beta gamma alpha zeta spongeDigest word11 word12 : Nat) (d : DeferredWords)
    (bpChallenges : List Nat) (branchData : Nat) (h : bpChallenges.length = 16) :
    (publicInputWordsCorrected beta gamma alpha zeta spongeDigest word11 word12 d
      bpChallenges branchData).length = 40 := by
  simp [publicInputWordsCorrected, h]

/-! ## §9 — the shape gate really refuses. Kernel `decide` over lengths and comparisons; no sponge
is run, so this is cheap and it is the CHECKER half of the split. -/

/-- A minimal well-shaped inhabitant, used only to make the refusals below a discrimination. -/
def dummyEvals : WrapEvals :=
  { spongeDigest := 1, oldChals := [List.replicate 16 1, List.replicate 16 1], ftEval1 := 1,
    pubEval := (1, 1), evals := List.replicate 43 (1, 1), bpChals := List.replicate 16 1,
    betaChal := 1, gammaChal := 1, alphaChal := 1, zetaChal := 1, domainLog2 := 16 }

/-- **`wrapEvals_shape_discriminates`** — the well-shaped tape is accepted and every single-field
mutilation of it is refused. Without the first conjunct this is a function returning `false`. -/
theorem wrapEvals_shape_discriminates :
    wrapEvalsOk dummyEvals = true
    -- 42 columns: a `to_absorption_sequence` that dropped one selector
    ∧ wrapEvalsOk { dummyEvals with evals := List.replicate 42 (1, 1) } = false
    -- 15 bulletproof challenges where 16 belong
    ∧ wrapEvalsOk { dummyEvals with bpChals := List.replicate 15 1 } = false
    -- one accumulator instead of two
    ∧ wrapEvalsOk { dummyEvals with oldChals := [List.replicate 16 1] } = false
    -- a 15-long accumulator vector (the Wrap side's width, in the Step side's slot)
    ∧ wrapEvalsOk { dummyEvals with
        oldChals := [List.replicate 15 1, List.replicate 16 1] } = false
    -- a non-canonical evaluation: `x` and `x + p` are one element at the sponge
    ∧ wrapEvalsOk { dummyEvals with evals := (List.replicate 43 (1, 1)).set 0 (pN, 1) } = false
    -- a challenge that is not a 128-bit challenge
    ∧ wrapEvalsOk { dummyEvals with betaChal := 2 ^ 128 } = false
    ∧ wrapEvalsOk { dummyEvals with spongeDigest := pN } = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- …and the fail-closed entry point returns `none` on each of them rather than six words. -/
theorem expandDeferred_refuses :
    (expandDeferred? { dummyEvals with evals := List.replicate 42 (1, 1) } 1).isNone
    ∧ (expandDeferred? { dummyEvals with bpChals := List.replicate 15 1 } 1).isNone
    ∧ (expandDeferred? dummyEvals pN).isNone := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## §10 — the arithmetic helpers are the functions they claim to be. -/

/-- `powMod` is `Nat.pow` reduced — on values small enough that the kernel can check BOTH sides.
This is the tie between the ladder and the exponent it stands for. -/
theorem powMod_is_pow_mod :
    powMod 3 0 97 = 1 ∧ powMod 3 1 97 = 3 ∧ powMod 3 7 97 = 3 ^ 7 % 97
    ∧ powMod 5 40 97 = 5 ^ 40 % 97 ∧ powMod 2 255 97 = 2 ^ 255 % 97 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- `sqMod m k x = x^(2^k) % m`. -/
theorem sqMod_is_iterated_squaring :
    sqMod 97 0 5 = 5 ∧ sqMod 97 1 5 = 5 ^ 2 % 97 ∧ sqMod 97 4 5 = 5 ^ 16 % 97 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The Type1 shift really is invertible, so `shiftType1` is an ENCODING and not a digest —
which is what lets a reader recover `combined_inner_product` from slot 0. -/
theorem shiftType1_roundtrips :
    unshiftType1 (shiftType1 7) = 7 ∧ unshiftType1 (shiftType1 (pN - 1)) = pN - 1 := by
  refine ⟨?_, ?_⟩ <;> decide

#assert_axioms wrapEvals_shape_discriminates
#assert_axioms expandDeferred_refuses
#assert_axioms powMod_is_pow_mod
#assert_axioms sqMod_is_iterated_squaring
#assert_axioms shiftType1_roundtrips
#assert_axioms publicInputWordsCorrected_length

#print axioms wrapEvals_shape_discriminates
#print axioms shiftType1_roundtrips

end Dregg2.Bridge.MinaWrapDeferred
