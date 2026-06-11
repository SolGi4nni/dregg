# The Transcendental-Syntax Bridge — proving dregg from the foundations of logic

*(2026-06-11. A research program, prompted by Boris Eng's intuition that
transcendental syntax is "a logic for interactive concurrent processes."
Companion to `Dregg2/Calculus/DreggCalculus.lean` and `docs/DREGG-CALCULUS.md`.
This is a CONJECTURE + program, not a result. The honest line between what is
proved and what is open is the whole point of the document.)*

## The motivation

The dregg calculus today names the runtime *bottom-up*: we observed the kernel
compresses to three verbs + a guard algebra, classified the guards by their
coordination cost (the I-confluence tiers), and proved the laws. That is
honest but it reads as "the grab-bag of confluence properties we found when we
thought about it." A *top-down* derivation — dregg's guard algebra as a
consequence of the foundations of logic — would be stronger: it would say the
structure is *inevitable*, not assembled.

Girard's **transcendental syntax** (implemented in `~/dev/stella` via stellar
resolution; the engine's own words: *"a type is a behaviour, membership is
orthogonality, proofs are validated by the stellar / Danos–Régnier / Girard
criterion"*) is the candidate foundation. It reconstructs logic from untyped
interaction (the constellation) plus testing (orthogonality), with no types
posited a priori — exactly dregg's anti-aprioristic move, where the
constraints are *emitted* and the modalities are *classified*, never axiomatized.

## What is already proved (the structural rhyme)

These are theorems in the tree, not aspirations:

1. **Meaning is interaction.** `DreggCalculus.reduces_iff_step` — a term's
   admissibility *is* the guarded step (`stateStepGuarded`), nothing prior to
   it. This mirrors "membership is orthogonality": a turn is admitted iff it
   passes the cell program's tests.
2. **Substructurality — the linear-logic heart.**
   `DreggCalculus.attenuation_is_scope_restriction` is the **affine** discipline
   (authority weakens or discards, never amplifies); per-asset conservation
   (`reachable_total_zero`) is the **linear** discipline (resources exactly
   used). dregg's two governing laws ARE the two substructural rules of the
   logic transcendental syntax reconstructs.
3. **The certification adjunction.** `Predicate ⊣ Witness` (proved, `Dregg2.Laws`)
   is the uses/tests duality; the graded epistemic tower
   `∃_a ⊣ q_a* ⊣ ∀_a` sits over it.
4. **Coordination grading (dregg's addition).** `DreggCalculus.modality_price_is_tier`
   — each guard modality's price IS its finality tier. The concurrency
   dimension Girard's per-process machinery does not natively carry.
5. **Attested orthogonality (dregg's other addition).**
   `DreggCalculus.reduces_is_attested` — every interaction emits a receipt. In
   stella orthogonality is *played* (run IEx; `biorth` is O(universe²)); in
   dregg it is *reified as a transferable certificate* (the receipt, ultimately
   a STARK), re-checkable by a third party who was not present. Girard's tests
   are enacted; dregg's are attested. This is the operational content of
   "constructive knowledge = an exhibitable witness."

## STATUS (2026-06-11): both deciding questions ANSWERED — the bridge is load-bearing on the linear face

`Dregg2/Calculus/Biorthogonality.lean` holds the generic orthogonality core
(the Galois duality, `S^⊥⊥⊥ = S^⊥`, orthogonals-are-behaviours) and the live
weld **`caveatsAdmit_is_orthogonality` (`Iff.rfl`)** — the deployed fail-closed
gate IS orthogonality-set membership, and every committed reduction lands in a
behaviour. The literal/order closure there is the *trivial* (rectangular) case:
it tested the machinery, not the thesis.

`Dregg2/Calculus/BiorthTensor.lean` settles the two deciding questions:

1. **The tensor / linearity: CONDITIONAL YES, boundary exact.** The tensor
   lives over the COMPOSITE universe (`A ⊗ B = (A ⊙ B)^⊥⊥`, stella §69.35–36;
   the same-universe `(A^⊥ ∪ B^⊥)^⊥` is the additive `&` — `orth_union_is_with`).
   Conservation (Σδ=0 over the `move` verb's paired writes) is **NOT** a
   behaviour under ANY per-component (rectangular) test family, over any test
   type — `conservation_not_behaviour_rectangular`, via the one-line generic
   mix law `rect_mix_in_biorth`; instantiated at the live paired-`SlotCaveat`
   gate. It **IS** a behaviour the moment the deployed pair observable (the
   `valTotal` Σδ comparator of `move_conserves`) is fielded as a test —
   `conservation_is_behaviour` — and is then EXACTLY the closure of the
   matched-delta tensors, `Cons = (⋃ₖ Δₖ ⊙ Δ₋ₖ)^⊥⊥`
   (`conservation_eq_closure_of_matched_tensors`). Headline:
   `linearity_recovered_from_orthogonality` — linearity is recovered from
   orthogonality IFF the test side may CORRELATE the pair. The resource law
   lies outside every per-turn testing fragment (the fact/fiction line of
   `docs/EPISTEMIC-DATALOG.md`, made formal) and exactly at the deployed
   composite observable.
2. **The coordination grading: PARTIAL — and the conjectured form REFUTED.**
   The tier IS a structural property of the behaviour: coordination-free ⟺ the
   admission set is closed under PAIRWISE joins (`free_iff_joinClosed`,
   definitionally `IConfluent`). It EMERGES soundly through `^⊥`: join-stable
   tests yield join-closed orthogonals (`coOrth_joinClosed`), so a guard
   presented as `X^⊥` over join-stable tests is proved free
   (`behaviour_grade_sound`; the monotone pole re-derived purely from the
   presentation, `markGuard_grade_emerges`). The grade is NOT complete
   (`grading_incomplete`): it is a sound type discipline on `^⊥` (upper bound
   on cost), not a semantic readout. And the CALM/Scott-flavored form —
   "free ⟺ closed under directed union" — is FALSE on the deployed lattices:
   every nonempty directed set with a LUB in `Budget` attains it
   (`budget_directed_lub_attained`), so directed-closure is vacuous
   (`directedLubClosed_vacuous`) while the bounded `budgetGuard` forces
   ordering (`directed_conjecture_refuted`). Coordination prices DIVERGENT
   (incomparable) replicas, not growing views.

**The honest bottom line:** the bridge is load-bearing for the linear face —
conservation is forced by the orthogonality once (and only once) the testing
language is composite, and the boundary theorem is two-sided. The coordination
grading is half-derived: sound through `^⊥`, semantically completed by the
join. Remaining relational families to push closure on: the temporal
until-since (behaviours over traces) and the epistemic K/E/D/C (orthogonality
over who-can-refute).

## What is NOT proved — the exact gap (pre-S1/S2; retained for the conjecture statement)

Transcendental syntax *defines* a type as a **biorthogonally-closed
behaviour**: a set of objects `B` equal to its own double-orthogonal,
`B = B^⊥⊥`, where `^⊥` is "passes-the-test-against." dregg's guard classes are
**emitted and classified** (the I-confluence tiers) — NOT shown to be
orthogonally closed. So the connection today is a structural rhyme, not a
formal embedding. We must not claim otherwise.

## The bridge conjecture (the buildable object)

> **`guard_class_is_biorthogonally_closed` (CONJECTURE).** Fix a dregg guard `g`
> (a precondition over states/turns). Let its *admission set*
> `Adm(g) := { t | g admits t }` (the turns it accepts), and let the
> *refutation set* `g^⊥ := { r | r refutes every t ∈ Adm(g) }` under a suitable
> orthogonality relation `t ⊥ r` (candidate: `r` is a verifying counter-witness —
> a fail-closed test the turn must survive, the dual of the guard discharge).
> Then `Adm(g) = Adm(g)^⊥⊥`: the guard class is its own bi-orthogonal closure.
> Equivalently: every dregg guard IS a stella behaviour, and the guard algebra
> is a constellation of behaviours whose orthogonality check is replaced by a
> STARK.

If this holds for the guard-atom families (actor / heap / temporal / epistemic /
order), then the *whole guard algebra* is derived, not assembled: each modality
is forced as a behaviour, and the I-confluence tiers become a *grading on
behaviours* rather than an empirical taxonomy. dregg's substructural character
(affine authority, linear resource) would then be a *theorem about the
orthogonality*, recovering linear logic's exponential/additive structure from
the dregg side.

## The program (staged)

- **S1 — the orthogonality relation.** Define `t ⊥ r` for dregg turns/guards in
  Lean, faithful to the fail-closed semantics (a refutation is a witness the
  guard must exclude). Sanity: `⊥` is symmetric-enough and the guard discharge
  is exactly non-orthogonality to the refutation set. Cross-check against
  stella's `orth_one`/`orth_fin`/`orthogonal_set` (`stella-core::mll`).
- **S2 — closure for ONE atom family.** Prove `guard_class_is_biorthogonally_closed`
  for the simplest family (the order/literal atoms — decidable, finite test
  sets), with non-vacuity both polarities (a closed class; a non-closed
  candidate that the closure repairs).
- **S3 — the substructural recovery.** Show affine authority (attenuation) and
  linear resource (conservation) as *consequences* of the behaviour structure —
  the exponential `!` / the `⊗` of the recovered fragment.
- **S4 — the grading.** Recast the I-confluence tiers as a grading on behaviours
  (the coordination price as a modality on `^⊥`); connect to
  `modality_price_is_tier`.
- **S5 — the stella instantiation (optional, cross-system).** Encode a dregg
  guard discharge as a stella constellation (program-rays ⊎ token-rays ⊎
  test-rays); IEx normal form = the admitted turn; the Danos–Régnier/Girard
  criterion = guard soundness. Then dregg = "a constellation whose orthogonality
  is attested by a STARK."

## Honest disposition

S1–S2 are afternoon-to-wave Lean work and would already justify "dregg's guards
are behaviours." S3 is the deep prize (linear logic recovered from the dregg
side) and is genuinely hard — it may be terminal at "named correspondence"
rather than full theorem; that is an acceptable honest outcome to discover.
S5 is cross-system and research-grade. Nothing here is on any production path;
it is the *foundational* derivation that would let us say dregg is inevitable
rather than assembled — and answer Boris's "I don't have enough knowledge to
assert that" with the one theorem that asserts it.
