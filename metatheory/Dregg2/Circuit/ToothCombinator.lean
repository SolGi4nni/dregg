/-
# Dregg2.Circuit.ToothCombinator — the teeth, DERIVED

Every de-vacuated binding carries three teeth around its residual, and until now all three were
written by hand at every site. The audits found that the teeth, not the proofs, are where the ports
go wrong. This file settles which of the three are DERIVABLE and which is not, and builds the
derivable ones once.

## The answer, up front

  * **`_fires`** — DERIVED, with no per-site proof at all. It is the DIAGONAL case of the extractor's
    own walk (`foldFind_diag`): at equal inputs the walk bottoms out at an equal pair, so the
    residual fails FOR EVERY HASH. No floor, no witness, nothing to state.
  * **`_refutable`** — DERIVED from a HASH-LEVEL witness (a collapsing hash and two absorbed inputs
    that differ), by `foldFind_refutable_of_step`. Nothing about the site's model is needed.
  * **`_unconditional_false`** — ⚑ **NOT DERIVABLE, and §5 says exactly why.** It needs a
    counterexample STATE that satisfies every surviving hypothesis, and those proofs are facts about
    the site's own model (`CapRootBridge.empty_caps_unauthorized`,
    `RecursiveAggregation.omitting_engine_sound`). No hash-level construction supplies them.
    What IS generic is the step from such a state to the refutation, and routing through it
    (`SharpTeeth`) puts the witness IN THE TYPE, where `Verify.ToothCheck.#tooth_same_witness` can
    see that the `_refutable` tooth fires at THAT state and not another one.

## §"what is irreducible", in one sentence

`_unconditional_false` is per-site in its WITNESS and generic in its DERIVATION; the check that
would have caught the two mis-stated ones is `Verify.ToothCheck.#tooth_unconditional_false`, which
computes the required statement from the theorem instead of comparing it to a hand-written one.
-/
import Dregg2.Verify.ToothCheck
import Dregg2.Circuit.AggregationAirSound

set_option autoImplicit false

namespace Dregg2.Circuit.ToothCombinator

open Dregg2.Circuit.Poseidon2Binding (SpongeColl)
open Dregg2.Circuit.AggregationAirSound

/-! ## §1 — `SharpTeeth`: the counterexample, at ONE instance, in the type.

The hand-rolled `_unconditional_false` hides its counterexample inside its proof; the `_refutable`
tooth names its instance in its type; and nothing relates them. That is the whole of the third
measured defect (`HistoryAggregation`: the `_refutable` cited as the load-bearing companion fires at
`(honestStep, richStep)`, while the counterexample is built at `(honestStep, honestStep)`).

`SharpTeeth Hyps Concl Res w` carries all three facts AT ONE `w`, so the agreement is by
construction rather than by citation, and both teeth fall out of it. -/

variable {ι : Type}

/-- **The counterexample, sharply.** At the single instance `w`: every surviving hypothesis HOLDS,
the conclusion FAILS, and the residual FIRES. The third field is what makes `¬ Res` the hypothesis
that EXCLUDES this counterexample, rather than a side condition that merely happens to be
unavailable. -/
structure SharpTeeth (Hyps Concl Res : ι → Prop) (w : ι) : Prop where
  holds : Hyps w
  fails : ¬ Concl w
  fires : Res w

/-- **`_unconditional_false`, DERIVED** — the statement minus the residual is refuted by the
counterexample. Generic: this is the only part of the tooth that is not per-site. -/
theorem unconditional_false_of_sharp {Hyps Concl Res : ι → Prop} {w : ι}
    (st : SharpTeeth Hyps Concl Res w) : ¬ ∀ x, Hyps x → Concl x :=
  fun hall => st.fails (hall w st.holds)

/-- **`_refutable`, DERIVED at the SAME instance** — and it is the same `w` by construction, not by
a docstring claiming so. -/
theorem refutable_of_sharp {Hyps Concl Res : ι → Prop} {w : ι}
    (st : SharpTeeth Hyps Concl Res w) : Res w := st.fires

/-- **⚑ The residual is EXACTLY what excludes the counterexample.** Given the repaired theorem, at
`w` the side condition `¬ Res w` is unavailable — and it has to be, because supplying it would
prove the conclusion that `st.fails` refutes. This is the sharp reading `CapRootBridge.capBridge-
Coll_is_the_hypothesis_at_the_bridge` states by hand at one site. -/
theorem residual_is_the_hypothesis {Hyps Concl Res : ι → Prop} {w : ι}
    (thm : ∀ x, Hyps x → ¬ Res x → Concl x) (st : SharpTeeth Hyps Concl Res w) :
    ¬ ¬ Res w :=
  fun hno => st.fails (thm w st.holds hno)

/-- **THE COMBINATOR REFUSES A TRIVIAL CONCLUSION.** `SharpTeeth` cannot be built against a
conclusion that is unconditionally true — so a `_unconditional_false` routed through it cannot be a
refutation of nothing. (The dual guard to `Verify.FreeConclusionRatchet`: that gate catches a FREE
conclusion, this one catches an EMPTY refutation.) -/
theorem no_sharpTeeth_of_trivial_conclusion {Hyps Res : ι → Prop} {w : ι} :
    ¬ SharpTeeth Hyps (fun _ => True) Res w :=
  fun st => st.fails trivial

/-- **AND IT REFUSES AN UNREACHABLE INSTANCE.** If the surviving hypotheses are unsatisfiable at `w`
there is no counterexample there either, so the construction cannot manufacture a refutation out of
an instance the theorem never applied to. -/
theorem no_sharpTeeth_of_unsatisfiable {Hyps Concl Res : ι → Prop} {w : ι} (h : ¬ Hyps w) :
    ¬ SharpTeeth Hyps Concl Res w :=
  fun st => h st.holds

/-! ## §2 — the FOLD extractor, once.

`AggregationAirSound.aggCollFind`, `StateTransitionAirSound.stCollFind` and
`BindingAirSound.histCollFind` are the SAME walk at three different `(row type, absorbed list,
projection)` triples — measured: they are the only three declarations in the tree carrying the
`if deep.1 = deep.2` idiom, and they are character-for-character the same modulo those three names.
Here it is once. -/

variable {α β : Type}

/-- The ordered hash fold: from `acc`, absorb each element and re-hash. -/
def foldH (hash : List ℤ → ℤ) (absorb : ℤ → α → List ℤ) (acc : ℤ) : List α → ℤ
  | []        => acc
  | r :: rest => foldH hash absorb (hash (absorb acc r)) rest

/-- **THE EXTRACTOR.** Total and decidable. Recurses to the DEEPEST level first; if the deeper walk
already named a colliding pair (detectable because a named pair is DISTINCT by construction) it is
returned unchanged, otherwise the deeper accumulators provably agree and THIS level is where the two
absorptions can differ, so its two absorbed lists are returned. Runs off the end at `([], [])`, a
trivially non-colliding pair. -/
def foldFind (hash : List ℤ → ℤ) (absorb : ℤ → α → List ℤ) :
    ℤ → ℤ → List α → List α → List ℤ × List ℤ
  | a, b, r :: rest, r' :: rest' =>
      let deep := foldFind hash absorb (hash (absorb a r)) (hash (absorb b r')) rest rest'
      if deep.1 = deep.2 then (absorb a r, absorb b r') else deep
  | _, _, _, _ => ([], [])

/-- **THE EXTRACTOR IS CORRECT — UNCONDITIONAL, NO FLOOR.** Two equal-length lists folded to the SAME
digest either agree on the starting accumulator and on the whole ordered projection, or the pair
`foldFind` returns is a GENUINE collision of the deployed hash. Nothing is assumed about `hash`.

`hsplit` is the site's own decoding of its absorbed list (`simp [List.cons.injEq]` at all three
existing sites) and is the ONLY per-site input. -/
theorem fold_binds_or_collides (hash : List ℤ → ℤ) (absorb : ℤ → α → List ℤ) (proj : α → β)
    (hsplit : ∀ (a b : ℤ) (r r' : α), absorb a r = absorb b r' → a = b ∧ proj r = proj r') :
    ∀ (l l' : List α) (a b : ℤ),
      l.length = l'.length →
      foldH hash absorb a l = foldH hash absorb b l' →
      (a = b ∧ l.map proj = l'.map proj
        ∧ (foldFind hash absorb a b l l').1 = (foldFind hash absorb a b l l').2)
      ∨ SpongeColl hash (foldFind hash absorb a b l l') := by
  intro l
  induction l with
  | nil =>
    intro l' a b hlen heq
    cases l' with
    | nil => exact Or.inl ⟨heq, rfl, rfl⟩
    | cons r' rest' => simp at hlen
  | cons r rest ih =>
    intro l' a b hlen heq
    cases l' with
    | nil => simp at hlen
    | cons r' rest' =>
      have hlen' : rest.length = rest'.length := by simpa using hlen
      simp only [foldH] at heq
      rcases ih rest' (hash (absorb a r)) (hash (absorb b r')) hlen' heq with
        ⟨hinner, htail, hdeep⟩ | hcoll
      · have hfind : foldFind hash absorb a b (r :: rest) (r' :: rest')
            = (absorb a r, absorb b r') := by
          simp only [foldFind]; rw [if_pos hdeep]
        rw [hfind]
        by_cases hpre : absorb a r = absorb b r'
        · obtain ⟨hab, hproj⟩ := hsplit a b r r' hpre
          exact Or.inl ⟨hab, by simp only [List.map_cons, hproj, htail], hpre⟩
        · exact Or.inr ⟨hpre, hinner⟩
      · have hne := hcoll.1
        have hfind : foldFind hash absorb a b (r :: rest) (r' :: rest')
            = foldFind hash absorb (hash (absorb a r)) (hash (absorb b r')) rest rest' := by
          simp only [foldFind]; rw [if_neg hne]
        rw [hfind]
        exact Or.inr hcoll

/-- **⚑ `_fires`, DERIVED — THE DIAGONAL.** At equal inputs the walk bottoms out at an EQUAL pair.
Nothing is assumed about `hash`, `absorb` or the list: this is a property of the WALK, so every site
built on `foldFind` gets its `_fires` tooth with no proof of its own. -/
theorem foldFind_diag (hash : List ℤ → ℤ) (absorb : ℤ → α → List ℤ) :
    ∀ (l : List α) (a : ℤ), (foldFind hash absorb a a l l).1 = (foldFind hash absorb a a l l).2 := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons r rest ih =>
    intro a
    simp only [foldFind]
    rw [if_pos (ih (hash (absorb a r)))]

/-- **⚑ `_fires`, PACKAGED.** The residual FAILS at an honest (diagonal) instance, FOR EVERY HASH —
no CR, no floor, no witness. This is the separation a global `∃ collision` disjunct provably cannot
make (`Circuit.SpongeCollisionShirk.orBreak_spongeCollision_iff_True`). -/
theorem foldColl_fires (hash : List ℤ → ℤ) (absorb : ℤ → α → List ℤ) (l : List α) (a : ℤ) :
    ¬ SpongeColl hash (foldFind hash absorb a a l l) :=
  fun hc => hc.1 (foldFind_diag hash absorb l a)

/-- **⚑ `_refutable`, DERIVED.** Given a hash that maps two DISTINCT absorbed lists together, the
extractor at the one-step instance RETURNS exactly that pair, so the residual genuinely holds. The
only input is a hash-level collision — nothing about the site's model. -/
theorem foldColl_refutable (hash : List ℤ → ℤ) (absorb : ℤ → α → List ℤ)
    {a b : ℤ} {r r' : α}
    (hne : absorb a r ≠ absorb b r') (heq : hash (absorb a r) = hash (absorb b r')) :
    SpongeColl hash (foldFind hash absorb a b [r] [r']) := by
  have hfind : foldFind hash absorb a b [r] [r'] = (absorb a r, absorb b r') := by
    simp [foldFind]
  rw [hfind]; exact ⟨hne, heq⟩

/-! ## §3 — COVERAGE: the hand-rolled fold extractor IS this one.

Stated as a theorem rather than asserted in prose. `AggregationAirSound.aggCollFind` is
`foldFind` at `aggAbsorb`, and `aggFold` is `foldH` at `aggAbsorb` — so the generic teeth above
instantiate to the hand-written ones rather than merely resembling them. The same equations hold for
`StateTransitionAirSound.stCollFind` (at `stAbsorb`) and `BindingAirSound.histCollFind` (at
`histAbsorb`); they are not proved here only because importing those two modules costs a build and
buys the same fact three times. -/

/-- `aggFold` IS the generic fold at `aggAbsorb`. -/
theorem aggFold_eq_foldH (sponge : List ℤ → ℤ) :
    ∀ (rows : List AggRow) (acc : ℤ), aggFold sponge acc rows = foldH sponge aggAbsorb acc rows := by
  intro rows
  induction rows with
  | nil => intro _; rfl
  | cons r rest ih => intro acc; exact ih _

/-- **⚑ `aggCollFind` IS the generic extractor at `aggAbsorb`.** So `AggregationAirSound`'s teeth are
instances of §2's, not lookalikes. -/
theorem aggCollFind_eq_foldFind (sponge : List ℤ → ℤ) :
    ∀ (rows rows' : List AggRow) (a b : ℤ),
      aggCollFind sponge a b rows rows' = foldFind sponge aggAbsorb a b rows rows' := by
  intro rows
  induction rows with
  | nil => intro rows' a b; cases rows' <;> rfl
  | cons r rest ih =>
    intro rows' a b
    cases rows' with
    | nil => rfl
    | cons r' rest' =>
      simp only [aggCollFind, foldFind, ih rest']
      rfl

/-- **THE HAND-WRITTEN `_fires` IS THE GENERIC DIAGONAL.** `AggregationAirSound.aggColl_fires` —
which is proved there by its own induction — follows from `foldColl_fires` with no induction at all.
That induction is what the combinator deletes at every future site. -/
theorem aggColl_fires_derived (sponge : List ℤ → ℤ) (rows : List AggRow) (a : ℤ) :
    ¬ SpongeColl sponge (aggCollFind sponge a a rows rows) := by
  rw [aggCollFind_eq_foldFind]
  exact foldColl_fires sponge aggAbsorb rows a

/-! ## §4 — the DEMONSTRATION: a `_unconditional_false` derived through `SharpTeeth`, landing on
EXACTLY the statement `Verify.ToothCheck` computes from the theorem.

The hand-written `AggregationAirSound.aggFold_inj_unconditional_false` passes `#tooth_uncondition-
al_false` only in PROJECTED mode (it refutes the `And`-leaf, dropping the `a = b` conjunct). The
derived one below passes in EXACT mode, because its statement is `tooth_minus% aggFold_inj hno` —
not written by hand at all. -/

/-- The instance type for `aggFold_inj`: its binder telescope, bundled. -/
structure AggInst where
  sponge : List ℤ → ℤ
  rows   : List AggRow
  rows'  : List AggRow
  a      : ℤ
  b      : ℤ

/-- `aggFold_inj`'s surviving hypotheses, as a predicate on the instance. -/
def aggHyps (x : AggInst) : Prop :=
  x.rows.length = x.rows'.length ∧ aggFold x.sponge x.a x.rows = aggFold x.sponge x.b x.rows'

/-- `aggFold_inj`'s conclusion, VERBATIM (both conjuncts — the derived tooth does not weaken it). -/
def aggConcl (x : AggInst) : Prop :=
  x.a = x.b ∧ x.rows.map projAgg = x.rows'.map projAgg

/-- `aggFold_inj`'s residual, at the pair the extractor names for this instance. -/
def aggRes (x : AggInst) : Prop :=
  SpongeColl x.sponge (aggCollFind x.sponge x.a x.b x.rows x.rows')

/-- The counterexample state: the collapsing sponge, two single-row chains differing in `leaf`. -/
def badAgg : AggInst where
  sponge := fun _ => 0
  rows   := [{ accIn := 0, leaf := 1, root := 0, idx := 0, accOut := 0 }]
  rows'  := [{ accIn := 0, leaf := 2, root := 0, idx := 0, accOut := 0 }]
  a      := 0
  b      := 0

/-- **⚑ THE THREE FACTS AT ONE INSTANCE.** The hypotheses hold, the conclusion fails, and the
residual fires — all at `badAgg`, in the type. The `fires` field is `foldColl_refutable`, i.e. it is
DERIVED; only `holds` and `fails` are site-specific, and `fails` is where the site's model enters. -/
theorem agg_sharp : SharpTeeth aggHyps aggConcl aggRes badAgg where
  holds := ⟨rfl, rfl⟩
  fails := by
    rintro ⟨-, hmap⟩
    simp only [badAgg, List.map_cons, List.map_nil, List.cons.injEq, projAgg, Prod.mk.injEq] at hmap
    omega
  fires := by
    show SpongeColl badAgg.sponge
      (aggCollFind badAgg.sponge badAgg.a badAgg.b badAgg.rows badAgg.rows')
    rw [aggCollFind_eq_foldFind]
    exact foldColl_refutable badAgg.sponge aggAbsorb (by decide) rfl

/-- **⚑ THE DERIVED TOOTH.** Its STATEMENT is computed from `aggFold_inj` by `tooth_minus%`, so it
cannot drift from the theorem, and its PROOF is `unconditional_false_of_sharp` at the same `badAgg`
the refutability tooth fires at. Both defects the audits found are structurally impossible here: the
statement is not hand-written, and the witness is not cited. -/
theorem aggFold_inj_unconditional_false_derived :
    ¬ tooth_minus% Dregg2.Circuit.AggregationAirSound.aggFold_inj hno := by
  intro hall
  exact agg_sharp.fails
    (hall badAgg.sponge badAgg.rows badAgg.rows' badAgg.a badAgg.b
      agg_sharp.holds.1 agg_sharp.holds.2)

/-- The refutability tooth AT THE SAME instance, spelled so `#tooth_same_witness` can compare it. -/
theorem aggColl_refutable_at_badAgg :
    SpongeColl badAgg.sponge
      (aggCollFind badAgg.sponge badAgg.a badAgg.b badAgg.rows badAgg.rows') :=
  agg_sharp.fires

/-! ## §5 — WHAT CANNOT BE DERIVED, and the measurement behind the claim.

`_unconditional_false` needs `fails` AND `holds` at a common state. `fails` is a fact about the
SITE'S MODEL, and at the two sites where the audits found a mis-statement the proof of `holds` is a
domain theorem no hash-level construction supplies:

  * `CapRootBridge.capOpen_implies_authorizedB_unconditional_false` needs `collapseEnc` (the EMPTY
    cap table is faithfully committed by the EMPTY heap) and `collapseOpen` (a single-edge heap
    publishes the same root and opens the `(5 ⇒ 9)` write edge), and refutes the conclusion with
    `empty_caps_unauthorized`.
  * `RecursiveAggregation.non_omission_from_verification_unconditional_false` needs
    `omitting_engine_sound` — that VERIFICATION does not exclude the omitting chain.

Neither is a statement about a hash. A "generic construction (a collapsing hash plus two states
differing in one field)" supplies `fires` and often `fails`, and supplies NOTHING toward `holds`,
which is the hypothesis-satisfaction obligation and the part that is really per-site.

So the answer to "is it per-site?" is: **the WITNESS is, the DERIVATION is not, and the STATEMENT
must not be** — which is why the statement is computed by `tooth_minus%` and the check is
`Verify.ToothCheck.#tooth_unconditional_false` rather than a generated theorem. -/

/-! ## §6 — axiom hygiene. -/

#assert_axioms unconditional_false_of_sharp
#assert_axioms refutable_of_sharp
#assert_axioms residual_is_the_hypothesis
#assert_axioms no_sharpTeeth_of_trivial_conclusion
#assert_axioms no_sharpTeeth_of_unsatisfiable
#assert_axioms fold_binds_or_collides
#assert_axioms foldFind_diag
#assert_axioms foldColl_fires
#assert_axioms foldColl_refutable
#assert_axioms aggFold_eq_foldH
#assert_axioms aggCollFind_eq_foldFind
#assert_axioms aggColl_fires_derived
#assert_axioms agg_sharp
#assert_axioms aggFold_inj_unconditional_false_derived

end Dregg2.Circuit.ToothCombinator

/-! ## §7 — the checker, run on this file's own teeth.

The derived tooth passes in EXACT mode (the hand-written one passes only PROJECTED), and the
refutability tooth is proved to fire at the very instance the counterexample breaks at. -/

#tooth_unconditional_false
  Dregg2.Circuit.ToothCombinator.aggFold_inj_unconditional_false_derived
  for Dregg2.Circuit.AggregationAirSound.aggFold_inj drops hno

#tooth_refutable Dregg2.Circuit.ToothCombinator.aggColl_refutable_at_badAgg
  for Dregg2.Circuit.AggregationAirSound.aggFold_inj drops hno

#tooth_fires Dregg2.Circuit.ToothCombinator.aggColl_fires_derived
  for Dregg2.Circuit.AggregationAirSound.aggFold_inj drops hno

#tooth_same_witness
  Dregg2.Circuit.ToothCombinator.aggFold_inj_unconditional_false_derived
  Dregg2.Circuit.ToothCombinator.aggColl_refutable_at_badAgg
  for Dregg2.Circuit.AggregationAirSound.aggFold_inj drops hno
