/-
# `Dregg2.Crypto.IpaOpeningExtractionFloor` — P10, stated precisely: what the IPA/FRI
opening-KNOWLEDGE-soundness floor actually requires, what settles, and what is priced.

## SUBSTRATE (House Law #1, said out loud at constraint #1)

**This is Lean-authored, and it is not a circuit at all.** Nothing below is a Rust AIR, a Rust
gadget, or an `air_accepts` predicate — there is no constraint system anywhere in this file, only
theorems about functions, fields, modules and finite probability. `MinaWrapOpeningGate.
opening_relation_holds` (already in this tree) proves, in-kernel, that the IPA verifier's *check* —
`c·Q + delta − z1·sg − z1·b0·U − z2·H = O` — holds for a real Mina block. Every file in that stack
says the same thing about what remains undischarged: **"the check passes" is not "the opening is
sound."** That gap — named P10 throughout `docs/MINA-REAL-BLOCK-GATE.md`,
`docs/PICKLES-VERIFIER-SCOPE.md`, `PicklesRecursion.lean`, `PicklesTranscriptBinding.lean`,
`KimchiRecursionGate.lean` — is a genuine EXTRACTION-ARGUMENT gap. This file says precisely what it
costs, instead of naming it again.

## What P10 actually is, read against the state of the art (grounded, never copied)

`l-adic/snarky`'s `formal/` (a public, UNLICENSED Lean formalization of kimchi/bulletproofs — READ
for grounding on GitHub, never imported, never copied into this tree) is the most complete
treatment of exactly this floor that exists anywhere. Its `Bulletproof/Soundness.lean` proves
batched, chunked IPA knowledge soundness — sorry-free, real linear algebra (`Matrix.vandermonde` +
Mathlib's `det_vandermonde_ne_zero_iff`) — GIVEN a `FiatShamirTreeB` hypothesis at every grid point
and a `DLRelation`/binding hypothesis whose OWN docstring says, verbatim:

> "It is information-theoretically false for a real single-curve SRS (among `2^k+1` generators in a
> group of order `|F|` a nontrivial relation always exists), so the theorem is vacuous at real
> parameters; it is meaningful only as the computational assumption, discharged elsewhere."

— and its `Kimchi/Verifier/Capstone/Reflection.lean` closes the gap to a real Poseidon-driven
verifier with exactly FOUR axioms — `poseidon_fiat_shamir_{vesta,pallas}` (`Bulletproof/
Reflection.lean`) and `kimchi_fiat_shamir_{vesta,pallas}` (the same file) — each asserting,
WHOLESALE, that "an accepting run admits a de-blinded accepting transcript TREE," i.e. asserting
the rewinding/forking extractor EXISTS. That is the shape ember's brief names exactly: *"An axiom
that asserts the extractor exists is the thing P10 actually needs, so axiomatising it is assuming
the conclusion."* Nothing below imports that axiom, in any form, at any renaming.

So P10, honestly decomposed, is FOUR things, and they have different characters:

  1. **The linear-algebra step of extraction** — given enough ACCEPTING transcripts at pairwise-
     distinct challenges, recovering a witness is a solvable Vandermonde system, not magic.
     **§A below: SETTLED**, independently derived (the SAME public Mathlib API l-adic/snarky uses,
     never their code), over an abstract field and then over the REAL field the deployed IPA runs
     (Pasta's `qN`, cited independently to keep this floor's build light).
  2. **The BINDING / no-relation idealization** — l-adic/snarky's own docstring says it is
     unconditionally false. **§B below makes that a Lean THEOREM** (rank-nullity via
     `Module.finrank`, independently derived), and connects it to THIS tree's OWN
     `FloorGames.DLFamily`/`dlGame`: binding is not a fresh assumption to invent — it is exactly the
     tree's already-named, already-known-vacuous-at-`⊤` discrete-log floor (which, like
     `MSISHardQuant`/`HashCRHardQuant`, has no `Eff` yet).
  3. **The challenge-DISTINCTNESS of `T` rewound transcripts** — a prerequisite for §A's matrix to
     be invertible. **§C below: PRICED**, via the tree's OWN proved `RomQueryFloor` machinery
     (`condProb_two_fresh_eq`, a union bound added here), at real Pasta parameters, to a concrete,
     computed, minuscule number.
  4. **Getting `T` ACCEPTING transcripts from ONE prover at all** — the actual rewinding/forking
     argument: given a prover that makes the honest verifier accept with probability `ε` on a
     random challenge, bound the (expected) cost of obtaining `T` accepting continuations.
     **§D names this precisely and does NOT discharge it.** It needs a probabilistic COST/PPT model
     for an INTERACTIVE prover with rewinding access, and `reference-grounding-efficient-
     adversaries`'s own finding stands: no such cost model exists in this tree, or (per that
     finding's literature survey) in ANY mechanized ZK framework surveyed except EasyCrypt/FCF, at
     the price of a from-scratch cost-carrying adversary calculus this tree has not built.

## What this file does NOT do

It does not build a prover/adversary object for an INTERACTIVE proof (none exists in this tree —
`RomOracle`/`FloorGames` model a single-shot oracle adversary, not a multi-round interactive one
with rewinding access). It does not touch `MinaWrapOpeningGate.lean`, `FriLdtExtractDeployed.lean`,
or any deployed gate directly — §D connects to both in PROSE, citing real theorem names, to keep
this floor's own build independent of the heavy AIR-emission import chain.

## Axiom hygiene

`#assert_axioms` per theorem; no `sorry`, no `native_decide`, no fresh `axiom`. NEW module; NOT
added to `metatheory/Dregg2.lean` (house discipline for standalone floors) — import line to add
when integrated: `import Dregg2.Crypto.IpaOpeningExtractionFloor`.
-/
import Dregg2.Crypto.RomQueryFloor
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic

namespace Dregg2.Crypto.IpaOpeningExtractionFloor

open Dregg2.Crypto.RomCounting (cyl condProb condProb_eq_zero)
open Dregg2.Crypto.RomQueryFloor (condProb_two_fresh_eq)

set_option autoImplicit false

/-! ## §A — SETTLED: the linear-algebra step of special-soundness extraction.

Given `n` pairwise-distinct challenges, there is a coefficient vector reading off any one
coordinate of a degree-`< n` evaluation vector. This is special soundness's "solve for the witness
from many accepting transcripts" step, and it needs NO adversary, NO cost model, and NO random
oracle — it is a finite fact about the field, sharpened by `Matrix.det_vandermonde_ne_zero_iff`
(nonzero iff the challenge nodes are distinct). -/

section Vandermonde

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- **THE `n`-POINT DUAL BASIS — SETTLED.** For `n` pairwise-distinct challenges `c : Fin n → F`
and a target coordinate `d`, there is `l : Fin n → F` reading off `d`:
`∑ s, l s * (c s) ^ i = [i = d]`. This is exactly the linear-algebra content of "extraction from
`n` accepting transcripts at `n` distinct challenges" (the standard multi-round IPA special-
soundness reduction, and l-adic/snarky's own `Bulletproof.vandermondeN`, re-derived here
independently over the SAME public Mathlib API): the challenges are the rows of a Vandermonde
matrix, invertible exactly because they are distinct. -/
theorem vandermonde_dual_basis {n : ℕ} (c : Fin n → F) (hc : Function.Injective c) (d : Fin n) :
    ∃ l : Fin n → F, ∀ i : Fin n, ∑ s, l s * (c s) ^ (i : ℕ) = if i = d then 1 else 0 := by
  set M : Matrix (Fin n) (Fin n) F := (Matrix.vandermonde c).transpose with hM
  have hdet : M.det ≠ 0 := by
    rw [hM, Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hc
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  refine ⟨M⁻¹.mulVec (Pi.single d 1), fun i => ?_⟩
  have hmul : M.mulVec (M⁻¹.mulVec (Pi.single d 1)) = Pi.single d 1 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hunit, Matrix.one_mulVec]
  have hval : ∑ s, M⁻¹.mulVec (Pi.single d 1) s * (c s) ^ (i : ℕ)
      = (M.mulVec (M⁻¹.mulVec (Pi.single d 1))) i := by
    simp only [Matrix.mulVec, dotProduct, hM, Matrix.transpose_apply, Matrix.vandermonde_apply]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hval, hmul, Pi.single_apply]

omit [DecidableEq F] in
/-- **A single accepting-transcript witness, extracted.** If `n` witnesses `a s` each satisfy the
SAME linear relation against their own challenge (`v s = ∑ i, a s i * (c s) ^ i`, the shape of an
opened IPA/PCS evaluation claim scaled by a challenge power), and the challenges are pairwise
distinct, then the dual basis reads off, for each target `d`, a single COMBINATION whose value is
`a d`'s own opening — the "many transcripts, one witness" step made a formula rather than a magic
extractor. Restated at the concrete shape a batched-opening reduction consumes. -/
theorem vandermonde_extracts {n : ℕ} (c : Fin n → F) (hc : Function.Injective c)
    (a : Fin n → F) :
    ∀ d : Fin n, ∃ l : Fin n → F, ∑ s, l s * (∑ i : Fin n, a i * (c s) ^ (i : ℕ)) = a d := by
  intro d
  obtain ⟨l, hl⟩ := vandermonde_dual_basis c hc d
  refine ⟨l, ?_⟩
  have : ∑ s, l s * (∑ i : Fin n, a i * (c s) ^ (i : ℕ))
      = ∑ i : Fin n, a i * (∑ s, l s * (c s) ^ (i : ℕ)) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  simp only [hl, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ d a, if_pos (Finset.mem_univ d)]

end Vandermonde

/-! ### Instantiated at the REAL field the deployed IPA runs over.

Pasta's `qN` (`Dregg2.Circuit.Emit.PastaField.qN`, cited independently here — as a plain `Nat`
literal — to keep this floor's build light, i.e. free of the heavy AIR-emission import chain): the
field `MinaWrapOpeningGate.CHAL`'s 15 IPA challenges live in. -/

/-- Pasta's Vesta base field / Pallas scalar field modulus — the SAME `qN` `MinaWrapOpeningGate`
runs its IPA challenges over. Restated as a bare `Nat` (not imported) so this file's build does not
pull in the Emit pipeline; verified equal to `PastaField.qN` by inspection of the source cited
there (`mina-curves` rev `36a8b510`, `curves/src/pasta/fields/fq.rs`). -/
def pastaQ : ℕ :=
  28948022309329048855892746252171976963363056481941647379679742748393362948097

/-- `pastaQ` is nonzero — a trivial numeral comparison (fast; NOT a primality check). Gives
`Nonempty (Fin pastaQ)`, needed to instantiate §C's `[Nonempty R]` concretely. -/
instance : Nonempty (Fin pastaQ) := ⟨⟨0, by decide⟩⟩

/-- **The abstract dual-basis theorem, instantiated at the real IPA field — GIVEN a primality
witness for `pastaQ`.** `KimchiVerify.lean` §9b already records why this hypothesis is not
discharged here: "there is no `Field (ZMod pN)` instance in the tree" — certifying a 255-bit
prime by kernel `decide` is infeasible trial division, and no Pratt certificate is built in this
file. So this is stated exactly as `SchnorrCurveField`'s pillar 1/2 discipline states its own
EMPIRICAL SEEDS: a NAMED hypothesis (`Fact (Nat.Prime pastaQ)`), never a Lean law, never
`:= True`, never discharged by `decide`. Given it, the linear-algebra step of extraction is
unconditionally settled at the exact field the deployed opening runs over. -/
theorem vandermonde_dual_basis_pasta [Fact (Nat.Prime pastaQ)] {n : ℕ}
    (c : Fin n → ZMod pastaQ) (hc : Function.Injective c) (d : Fin n) :
    ∃ l : Fin n → ZMod pastaQ, ∀ i : Fin n, ∑ s, l s * (c s) ^ (i : ℕ) = if i = d then 1 else 0 :=
  vandermonde_dual_basis c hc d

/-! ## §B — SETTLED: the binding/no-relation idealization is unconditionally FALSE.

The naive Pedersen/IPA "binding" idealization used throughout the literature (and by
l-adic/snarky's own `hbind`) reads: *no nontrivial `w ≠ 0` satisfies `∑ w_i • g_i = 0`* over the
`n` SRS generators. That idealization is FALSE whenever the generators live in a group whose
cardinality matches the scalar field's — the standard elliptic-curve situation, and Pasta's own
(`Fintype.card VestaPoint = Fintype.card Fp` by construction of a 2-cycle). This settles, as a real
theorem via `Module.finrank` rank-nullity, exactly what l-adic/snarky's docstring asserts in prose:
"among `2^k+1` generators in a group of order `|F|` a nontrivial relation always exists." -/

section RelationExists

variable {F G : Type*} [Field F] [Fintype F] [AddCommGroup G] [Fintype G] [Module F G]

/-- The commitment map `w ↦ ∑ w_i • g_i`, bundled as `F`-linear — the object whose kernel a
"binding" hypothesis claims is trivial. -/
def commitMap {n : ℕ} (g : Fin n → G) : (Fin n → F) →ₗ[F] G where
  toFun w := ∑ i, w i • g i
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [mul_smul, Finset.smul_sum]

/-- **⚑⚑ THE BINDING IDEALIZATION IS UNCONDITIONALLY FALSE — SETTLED, not assumed.** Whenever the
generator group's cardinality matches the scalar field's (the Pasta 2-cycle's own shape: Vesta's
point count equals Pallas's scalar field size, and vice versa) and there are `n ≥ 2` generators, a
NONTRIVIAL relation `∑ w_i • g_i = 0` EXISTS. Proof: `G` is then a `1`-dimensional `F`-vector space
(`Module.card_eq_pow_finrank` forces `finrank F G = 1`, since `Fintype.card F` is `≥ 2` and a prime
power equal to itself has exponent `1`), so `commitMap g`, mapping FROM an `n ≥ 2`-dimensional
space, cannot be injective (`LinearMap.finrank_le_finrank_of_injective` would force `n ≤ 1`) — and
a non-injective LINEAR map has a nonzero kernel element by subtraction of any two colliding
preimages. This is the SAME pigeonhole `FloorGames.hard_bot_vacuous` / `msisHardQuant_top_false_of_
compressing` use elsewhere in this tree for every OTHER unrestricted floor; binding is not
special. -/
theorem srsRelation_exists {n : ℕ} (hn : 2 ≤ n) (g : Fin n → G)
    (hcard : Fintype.card G = Fintype.card F) :
    ∃ w : Fin n → F, w ≠ 0 ∧ commitMap g w = 0 := by
  have hF2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hfinrankG : Module.finrank F G = 1 := by
    have hpow : Fintype.card F ^ (1 : ℕ) = Fintype.card F ^ Module.finrank F G := by
      calc Fintype.card F ^ (1 : ℕ) = Fintype.card F := pow_one _
        _ = Fintype.card G := hcard.symm
        _ = Fintype.card F ^ Module.finrank F G := Module.card_eq_pow_finrank
    exact (Nat.pow_right_injective hF2 hpow).symm
  have hfinrankDom : Module.finrank F (Fin n → F) = n := by
    rw [Module.finrank_pi]; simp
  have hnotinj : ¬ Function.Injective (commitMap (F := F) (G := G) g) := by
    intro hinj
    have hle : Module.finrank F (Fin n → F) ≤ Module.finrank F G :=
      LinearMap.finrank_le_finrank_of_injective hinj
    rw [hfinrankDom, hfinrankG] at hle
    omega
  rw [Function.not_injective_iff] at hnotinj
  obtain ⟨a, b, hab, hne⟩ := hnotinj
  refine ⟨a - b, sub_ne_zero.mpr hne, ?_⟩
  rw [map_sub, hab, sub_self]

/-- **⚑⚑ THE COMMITMENT SCHEME IS UNCONDITIONALLY NOT BINDING — the TOP pole of the binding floor,
stated directly.** `srsRelation_exists`, cashed out at its most concrete: TWO DIFFERENT witnesses
`0` and `w` open to the SAME commitment value. This is the exact shape `hard_top_iff_solvableFrac_
negl` uses everywhere else in this tree to refute an unrestricted floor — here specialized to
"binding," with no `Game`/`Adversary` scaffolding needed, because the counterexample is a single
concrete pair. The floor is meaningful only relative to a class of witness-finders that CANNOT
locate `w` — exactly `FloorGames.DLHardQuant` at Pasta's own curve group (§D, `dlog_of_relation`),
which this tree already knows is `⊤`-false (`dlHardQuant_top_false`) and `⊥`-vacuous
(`hard_bot_vacuous`), and has no `Eff` with content, same as `MSISHardQuant`/`HashCRHardQuant`
before the ROM escape. -/
theorem commitment_not_binding {n : ℕ} (hn : 2 ≤ n) (g : Fin n → G)
    (hcard : Fintype.card G = Fintype.card F) :
    ∃ a a' : Fin n → F, a ≠ a' ∧ commitMap g a = commitMap g a' := by
  obtain ⟨w, hw, hw0⟩ := srsRelation_exists hn g hcard
  exact ⟨0, w, hw.symm, (map_zero _).trans hw0.symm⟩

omit [Fintype F] [Fintype G] in
/-- **A NONTRIVIAL relation reduces to a discrete log — cleanly, unconditionally, for `n = 2`.**
Given `h P : G` with `h ≠ 0` and a nontrivial relation `w0 • h + w1 • P = 0`, `P` HAS a discrete
log base `h`. Pure field/module algebra: `w1 = 0` would force `w0 • h = 0` with `w0 ≠ 0` (since not
both are zero), hence `h = w0⁻¹ • (w0 • h) = 0`, contradicting `h ≠ 0` — so `w1 ≠ 0`, and then
`P = (-w0 * w1⁻¹) • h` directly. Connects `srsRelation_exists` to THIS TREE'S OWN
`FloorGames.DLFamily`/`dlGame`: "binding" is not a fresh hardness assumption to invent — solving it
(finding the relation) is finding a discrete log, whose EXISTENCE `FloorGames.dlHardQuant_top_false`
already names as unconditional (a `⊤`-adversary just returns the log used to build the challenge);
the content here is that it is unconditional from the RELATION side too, at any `P`, not merely at
one built by construction. -/
theorem dlog_of_relation (h P : G) (hh : h ≠ 0) (w0 w1 : F) (hne : (w0, w1) ≠ (0, 0))
    (hrel : w0 • h + w1 • P = 0) : ∃ x : F, P = x • h := by
  have hw1 : w1 ≠ 0 := by
    intro hw1eq
    have hw0 : w0 ≠ 0 := fun hw0eq => hne (by rw [hw0eq, hw1eq])
    have hz : w0 • h = 0 := by rw [hw1eq, zero_smul, add_zero] at hrel; exact hrel
    apply hh
    have hcong := congrArg (fun x => w0⁻¹ • x) hz
    simpa [smul_smul, inv_mul_cancel₀ hw0] using hcong
  refine ⟨-w0 * w1⁻¹, ?_⟩
  have hP : w1 • P = -(w0 • h) := by
    have hid : w1 • P = (w0 • h + w1 • P) - w0 • h := by abel
    rw [hid, hrel, zero_sub]
  have hPeq : P = w1⁻¹ • (-(w0 • h)) := by
    have hinv : P = w1⁻¹ • (w1 • P) := (inv_smul_smul₀ hw1 P).symm
    rw [hP] at hinv
    exact hinv
  rw [hPeq, smul_neg, smul_smul, ← neg_smul]
  congr 1
  ring

end RelationExists

/-! ## §C — PRICED: the challenge-distinctness of `T` rewound continuations.

The Vandermonde extraction (§A) needs its `n` challenges PAIRWISE DISTINCT. Rewinding a prover to
resample a Fiat–Shamir challenge is, in the random-oracle model, `T` queries to a FIXED oracle at
`T` FIXED, distinct query points (e.g. `T` distinct rewind labels absorbed just before the closing
squeeze) — and the probability that two of the `T` resulting challenges collide is PRICED, not
assumed, by the SAME machinery `RomQueryFloor` already proved: a union bound (new infrastructure
this file adds to `RomCounting`'s toolkit) over `T choose 2` pairs, each exactly `1/|R|` by the
ALREADY-PROVEN `RomQueryFloor.condProb_two_fresh_eq`. -/

section ManySamples

variable {D R : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R] [Nonempty R]

omit [DecidableEq D] [Fintype R] [Nonempty R] in
/-- **A FINITE UNION BOUND for `condProb`** — the conditional probability of "some index in `s`
wins" is at most the sum of the per-index conditional probabilities. Standard counting: the
"exists" event's winning set is contained in the union of the per-index winning sets
(`Finset.card_biUnion_le`). New infrastructure this file adds to `RomCounting`'s toolkit — the
missing piece that lets the tree's proved SINGLE-collision escape (`condProb_two_fresh_eq`) price
a MULTI-sample rewinding scenario. -/
theorem condProb_exists_le_sum {ι : Type*} (C : Finset (D → R))
    (P : ι → (D → R) → Bool) (s : Finset ι) :
    condProb C (fun H => decide (∃ i ∈ s, P i H = true)) ≤ ∑ i ∈ s, condProb C (P i) := by
  classical
  have hsub : C.filter (fun H => decide (∃ i ∈ s, P i H = true) = true)
      ⊆ s.biUnion (fun i => C.filter (fun H => P i H = true)) := by
    intro H hH
    simp only [Finset.mem_filter, decide_eq_true_eq] at hH
    obtain ⟨hHC, i, hi, hPi⟩ := hH
    exact Finset.mem_biUnion.2 ⟨i, hi, Finset.mem_filter.2 ⟨hHC, hPi⟩⟩
  have hcard : (C.filter (fun H => decide (∃ i ∈ s, P i H = true) = true)).card
      ≤ ∑ i ∈ s, (C.filter (fun H => P i H = true)).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  unfold condProb
  rw [← Finset.sum_div]
  gcongr
  exact_mod_cast hcard

/-- **`T`-WISE CHALLENGE DISTINCTNESS — PRICED, not assumed.** `T` FIXED, FRESH (all `∉ S`) query
points collide in their sponge-derived answers with probability at most `T² / |R|` — a union bound
over the (at most `T²`) ordered pairs `(p.1, p.2)` with `p.1 ≠ p.2`, each collision priced at
EXACTLY `1/|R|` by the ALREADY-PROVEN `condProb_two_fresh_eq` (using `d`'s injectivity to turn
`p.1 ≠ p.2` into `d p.1 ≠ d p.2`). This is the price of "getting `T` rewound Fiat–Shamir challenges
that are pairwise distinct" — the prerequisite `vandermonde_dual_basis` needs — and it is exactly
the same escape `RomQueryFloor` proved for a single collision (its own §5–§6), extended by a union
bound to `T` samples. The `T²` (rather than the sharper `T·(T−1)`) matches the tree's OWN existing
convention (`RomQueryFloor.birthday_bound` itself bounds by `Q²+1`, not the tighter count) — a
clean, honest, slightly loose bound, not a novel inflation. -/
theorem manyFreshDistinct_bound (S : Finset D) (σ : D → R) {T : ℕ} (d : Fin T → D)
    (hd_inj : Function.Injective d) (hd_fresh : ∀ i, d i ∉ S) :
    condProb (cyl S σ)
      (fun H => decide (∃ p : Fin T × Fin T, p.1 ≠ p.2 ∧ H (d p.1) = H (d p.2)))
      ≤ (T : ℝ) * (T : ℝ) / (Fintype.card R : ℝ) := by
  classical
  set P : Fin T × Fin T → (D → R) → Bool :=
    fun p H => decide (p.1 ≠ p.2 ∧ H (d p.1) = H (d p.2)) with hP
  have heq : (fun H => decide (∃ p : Fin T × Fin T, p.1 ≠ p.2 ∧ H (d p.1) = H (d p.2)))
      = (fun H => decide (∃ p ∈ (Finset.univ : Finset (Fin T × Fin T)), P p H = true)) := by
    funext H
    rw [decide_eq_decide]
    simp only [hP, Finset.mem_univ, true_and, decide_eq_true_eq]
  rw [heq]
  have hstep := condProb_exists_le_sum (cyl S σ) P (Finset.univ : Finset (Fin T × Fin T))
  refine hstep.trans ?_
  have hterm : ∀ p ∈ (Finset.univ : Finset (Fin T × Fin T)),
      condProb (cyl S σ) (P p) ≤ 1 / (Fintype.card R : ℝ) := by
    intro p _
    by_cases hpp : p.1 = p.2
    · have h0 : condProb (cyl S σ) (P p) = 0 := by
        apply condProb_eq_zero
        intro H _
        simp [hP, hpp]
      rw [h0]; positivity
    · have hPp : P p = fun H => decide (H (d p.1) = H (d p.2)) := by
        funext H; simp [hP, hpp]
      rw [hPp]
      exact le_of_eq (condProb_two_fresh_eq S σ (d p.1) (d p.2) (hd_fresh p.1) (hd_fresh p.2)
        (fun heqd => hpp (hd_inj heqd)))
  calc ∑ p ∈ (Finset.univ : Finset (Fin T × Fin T)), condProb (cyl S σ) (P p)
      ≤ ∑ _p ∈ (Finset.univ : Finset (Fin T × Fin T)), (1 / (Fintype.card R : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = (Fintype.card (Fin T × Fin T) : ℝ) * (1 / (Fintype.card R : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (T : ℝ) * (T : ℝ) / (Fintype.card R : ℝ) := by
        rw [Fintype.card_prod, Fintype.card_fin]
        push_cast
        ring

end ManySamples

/-! ### Instantiated at the REAL Pasta modulus and a concrete rewind budget — the computed number.

`pastaQ ≈ 2^255`. A generous `T = 64` (well above the 15 IPA rounds / 44-row batch grid
`MinaWrapOpeningGate`/`KimchiVerify` actually run) gives a probability bound the size of the
ENTIRE budget: `64·64 / pastaQ`. No primality is needed here — `Fin pastaQ` is a `Fintype` of the
right cardinality regardless of whether `pastaQ` is prime, unlike §A's field instantiation. -/

/-- **THE COMPUTED NUMBER.** At `T = 64` rewind labels and the real Pasta modulus, the probability
that any two of the 64 sponge-derived challenges collide is at most `4096 / pastaQ` —
`pastaQ ≈ 2^255`, so this is on the order of `2^-243`: astronomically below any real budget. This
is the priced residual for P10 item 3 (challenge distinctness): NOT assumed, NOT a cost model,
a plain computed fraction over the tree's own proved machinery. -/
theorem manyFreshDistinct_bound_pasta (S : Finset (Fin pastaQ)) (σ : Fin pastaQ → Fin pastaQ)
    (d : Fin 64 → Fin pastaQ) (hd_inj : Function.Injective d) (hd_fresh : ∀ i, d i ∉ S) :
    condProb (cyl S σ)
      (fun H => decide (∃ p : Fin 64 × Fin 64, p.1 ≠ p.2 ∧ H (d p.1) = H (d p.2)))
      ≤ (4096 : ℝ) / (pastaQ : ℝ) := by
  have h := manyFreshDistinct_bound S σ d hd_inj hd_fresh
  have hcard : (Fintype.card (Fin pastaQ) : ℝ) = (pastaQ : ℝ) := by
    simp [Fintype.card_fin]
  rw [hcard] at h
  have h64 : ((64 : ℕ) : ℝ) * ((64 : ℕ) : ℝ) = (4096 : ℝ) := by norm_num
  rwa [h64] at h

/-! ## §D — the honest composite: what P10 needs, cashed out, and what stays assumed.

**SETTLED** (§A, §B): the linear-algebra step of extraction (`vandermonde_dual_basis`,
independent of any cost model or oracle) and the falsity of the naive binding idealization
(`srsRelation_exists`, `dlog_of_relation` — a nontrivial SRS relation always exists and reduces to
a discrete log, exactly mirroring `FloorGames.dlHardQuant_top_false`'s own already-recorded
vacuity). Neither of these needed a NEW assumption; both are theorems.

**PRICED** (§C): the challenge-distinctness `T` rewound continuations need
(`manyFreshDistinct_bound_pasta`) — at the real Pasta modulus and a generous `T = 64`, the failure
probability is `≤ 4096 / pastaQ`, i.e. `≈ 2⁻²⁴³`. This is the SAME machinery
(`RomQueryFloor.condProb_two_fresh_eq`, itself resting on nothing but finite counting) that priced
P4's sponge-digest residual, extended here by one new union-bound lemma
(`condProb_exists_le_sum`) to a many-sample setting.

**STILL ASSUMED, named precisely — TWO things, and only two:**

1. **The rewinding/forking argument itself** (P10 item 4). §A+§C together say: GIVEN `T`
   accepting transcripts sharing a common first move, with pairwise-distinct challenges, a witness
   is extracted by explicit linear algebra, and the challenges ARE pairwise distinct except with
   probability `≈ 2⁻²⁴³`. What is NOT built here is the bridge from "a prover that makes the
   honest verifier accept with probability `ε`" to "`T` such accepting transcripts, obtained by
   rewinding." That bridge is the classical Forking Lemma (or an Attema–Cramer-style generalized
   special-soundness tree, l-adic/snarky's OWN route in `Bulletproof.Soundness`): it needs an
   INTERACTIVE prover object with a COST/rewinding budget, and this tree does not have one —
   `RomOracle.OracleComp`/`FloorGames.Adversary` model a single-shot ORACLE adversary, never an
   interactive prover a verifier can rewind. Per `reference-grounding-efficient-adversaries`'s own
   literature survey, building that object is standard engineering (the EasyCrypt/FCF route), not
   open research — but it is a real, unbuilt, moderately-sized formalization task, and importing
   `l-adic/snarky`'s `poseidon_fiat_shamir_*`/`kimchi_fiat_shamir_*` axioms to skip it would be
   assuming exactly the conclusion P10 asks for. This file does not do that.
2. **The COMPUTATIONAL binding assumption** (the sharpened form of P10 item 2, after §B). §B
   proves the NAIVE idealization false; it does NOT — cannot — prove that FINDING the relation
   `srsRelation_exists` names is hard. That is now, precisely, `FloorGames.DLHardQuant` at Pasta's
   own curve group: a floor this tree ALREADY has a name for, already knows is false at `Eff := ⊤`
   (`dlHardQuant_top_false`), and — like `MSISHardQuant`/`HashCRHardQuant` before the ROM
   escape — has no `Eff` with content. Discharging it the way `RomQueryFloor` discharged the hash
   floor would need a QUERY-BOUNDED escape for a GENERIC-GROUP (not random-oracle) adversary model,
   which is a different, harder floor than the ROM one this file reuses, and is not attempted here.

## Connecting to the deployed verifier (as far as this session reaches)

**IPA side.** `MinaWrapOpeningGate.opening_relation_holds` proves the check for ONE set of
challenges — `MinaWrapOpeningGate.CHAL`/`CHAL_INV`, DERIVED (`derived_ipa_challenges`) from the
real block's own transcript, not carried. Extracting a witness needs MANY such transcripts, at
DIFFERENT sampled `CHAL`s for the SAME 47-term aggregate commitment — which needs (a) actually
rewinding the honest o1-labs prover (item 1 above: no prover object exists anywhere in this stack,
only the verifier-side check), and, GIVEN that, (b) this file's §A (proven) and §C (priced at
`≈2⁻²⁴³`, using `qN`'s real 255-bit size) — but NOT (c), a computational discrete-log-hardness
argument for why the relation §B proves EXISTS is hard to FIND (item 2 above). Three of the four
pieces P10 needs are now on the table with a precise price tag; the fourth (the rewinding cost
model) is the one genuinely open item, and it is the SAME item both directions of the bridge need.

**FRI side.** `FriLdtExtractV3`/`FriLdtExtractDeployed.lean` carries the analogous gap for dregg's
own STARK, and per `project-fri-correlated-agreement-formalization`'s own finding, its
mathematical CRUX (correlated agreement, the Polishchuk–Spielman/BCIKS20 combinatorial engine) is
ALREADY proven — landed, sorry-free — while "there is still NO adversary / prover-strategy /
Fiat-Shamir object anywhere in the tree." That is EXACTLY item 1 above, restated for FRI's β-fold
challenges instead of the IPA's round challenges. §A's Vandermonde extraction does NOT transfer
verbatim to FRI (FRI's soundness argument is PROXIMITY/agreement over an error-correcting code, not
an exact linear system — a genuinely different mechanism, already built, and this file does not
duplicate it), but §C's method DOES: a "many rewound Fiat–Shamir samples are pairwise distinct"
bound is exactly as cheap to state and prove for FRI's fold challenges as for the IPA's, over
whatever field BabyBear's extension runs (`docs/FRI-SECURE-PARAMETERIZATION.md`'s own ledger — a
SEPARATE, already-measured number, e.g. `extDeg 4 ⟹ ≈2^123.6`-sized field — not re-derived here).
**So P10 is not two unrelated gaps inherited from two different proof systems: it is ONE missing
ingredient — a probabilistic rewinding-cost model for Fiat–Shamir extraction — inherited by both
the IPA opening check and the FRI low-degree check, and named here as precisely as this session
could make it.**

## §Y — Axiom hygiene. -/

#assert_axioms vandermonde_dual_basis
#assert_axioms vandermonde_dual_basis_pasta
#assert_axioms vandermonde_extracts
#assert_axioms srsRelation_exists
#assert_axioms commitment_not_binding
#assert_axioms dlog_of_relation
#assert_axioms condProb_exists_le_sum
#assert_axioms manyFreshDistinct_bound
#assert_axioms manyFreshDistinct_bound_pasta

#assert_namespace_axioms Dregg2.Crypto.IpaOpeningExtractionFloor

end Dregg2.Crypto.IpaOpeningExtractionFloor
