# `Metatheory/` — what the layer IS and how it connects to `Dregg2/`

**Scope:** `Metatheory/*.lean` (5 files) + `Metatheory/Open/*.lean` (7 files), 4536 LOC.
**Method:** read the theorem bodies, not docstrings; verify `sorry`/`axiom`/`:= True`
counts; trace the **direction and reality** of every connection to `Dregg2/`. When this
doc and the code disagree, the code wins.

---

## What this layer is

The discipline is real: **zero `sorry`, zero `axiom`, zero `admit`, zero
`:= True`/`:= Unit`-as-success** across all 12 files (every "sorry" string is a comment;
every `Unit`/`Bool` is an honest degenerate model or an explicit anti-vacuity witness).
Every keystone is `#assert_axioms`-pinned to `{propext, Classical.choice, Quot.sound}`,
and several modules carry **"teeth"** lemmas that *prove the constraint is falsifiable*
(`leaky_no_simulator`, `confluence_fails_when_coupled`, `realizes_fails`).

The dependency direction is the load-bearing fact: 10 of 12 metatheory files
`import Dregg2.*`, and many headline keystones are **re-wrappers of already-proved Dregg2
theorems into a new vocabulary** (categorical, epistemic, ZK) — downstream re-naming, not
an upstream generalization the concrete system derives from. The architecture *intended* —
`Dregg2` instantiates an abstraction and inherits — is realized in two-and-a-half places
(`EpistemicDial`→Crypto, `EpistemicConsensus`→`Lawvere`, plus the `Categorical` lattice
bridges) and one genuinely-new closed-OPEN theorem (`FinalCoalgebra`). The
dependency-inversion lane (below) makes the rest load-bearing.

---

## The connection taxonomy

Three relationships hide under "connects":

| Kind | Meaning | Frequency |
|---|---|---|
| **(I) Instantiated** | A real `Dregg2` def builds an instance of a `Metatheory` structure and *invokes* its inherited keystone. The intended direction. | RARE — EpistemicDial, EpistemicConsensus/Lawvere |
| **(II) Reuse-wrapper** | `Metatheory` theorem body is `:= Dregg2.Foo.bar …` verbatim. Re-narration; the metatheory inherits from the system, not vice versa. | COMMON |
| **(III) Disconnected lookalike** | `Metatheory` proves an abstract theorem; a docstring says it "mirrors" a Dregg2 result, but no def is shared and the structure is never instantiated by `Dregg2`. | COMMON in §1/§2 of Categorical, all of Perfect{ZK,UC} |

---

## Per-module map

### `Metatheory/Categorical.lean` (742 LOC) — mixed I/II/III

- **§1 Conservation** (`measure_unit`/`measure_tensor`/`no_free_copy`, `:63–144`): Kind
  III. Derives monoid-hom + invariance from "Σ is a lax monoidal functor to `Discrete M`";
  the docstring (`:18–21`) notes the coherence diagrams are vacuous in a discrete target.
  Never instantiated — `Dregg2.Core.withholding_no_free_copy` (`Dregg2/Core.lean:203`) is
  proved independently. A structurally-isomorphic parallel proof in a different namespace.
- **§2 Seam** (`Seam`/`seam_*`, `:170–211`): Kind III. `Seam` is a bare `GaloisConnection`
  wrapper; the structure is never instantiated.
- **§4 Finality** (`:225–288`): **Kind I, load-bearing.** `tier_commit_eq_crossTierJoin`
  (`:283`) is `commitAtMax a b = Dregg2.Finality.crossTierJoin a b := rfl` — a definitional
  match on the real `Dregg2.Finality.Tier`, with genuine `OrderTop`/`OrderBot`/`BoundedOrder`
  instances (`:267–279`).
- **§5 Confluence** (`:339–345`): **Kind II→borderline-I.** `tier1Eligible_closedUnderJoin`
  reuses the real `Dregg2.Confluence.admits_sound`.
- **§3 Coalgebra/pullback** (`:351–620`): states the cell as an `F`-coalgebra and JointTurn
  as a wide pullback; leaves final-coalgebra existence OPEN (`:597–607`, closed in
  `FinalCoalgebra`).

### `Metatheory/ConstructiveKnowledge.lean` (444 LOC) — mostly Kind II

- **§1 realizability** (`Holds`, `holds_iff_discharged_witness`, `holds_mono`,
  `find_realizes`, `:72–139`): **REAL, built on real Dregg2 primitives**
  (`Dregg2.Laws.Verifiable`/`Discharged`/`Searchable`/`search_sound`). The substantive core.
- **§4 no-drift** (`knowledge_does_not_drift`, `:369–382`): Kind II,
  `:= stepComplete_preserves …` — the Dregg2 keystone re-named.
- **`knower_sound_to_itself`** (`:390–393`): `:= sound_refl Impl x` — Dregg2 wrapper.
- **`knowledge_no_free_copy`** (`:426–432`): `:= Dregg2.Core.withholding_no_free_copy …` —
  Dregg2 wrapper; not `#assert_axioms`-pinned (rests on the conservation primitive).

### `Metatheory/EpistemicConsensus.lean` (407 LOC) — Kind I target, REAL connection

- Builds an Aumann/Kripke `Frame` (`Indist`, `Knows`, `DistKnows`) and proves
  `honest_dist_knowledge_iff_holds`, `distKnows_mono_group`,
  `no_dist_knowledge_of_unrealizable` (`:148–241`). The keystones bottom out in
  `holds_iff_discharged_witness` (`Iff.rfl`), so "distributed knowledge" reduces to
  realizability.
- Anti-vacuity is taken seriously: §6 (`:245+`) supplies a discriminating witness
  (`verifiable_discriminates`, `:316`).
- **Kind I:** this `Frame` is consumed by `Dregg2/Metatheory/Lawvere.lean` to build the
  `∀_a = Knows` triple. An upstream abstraction the Dregg2-side uses.

### `Metatheory/Disputation.lean` (86 LOC) — slim, Kind II

- `upheld := Holds`; `verdict_is_honest_distributed_knowledge`/
  `byzantine_majority_cannot_uphold` (`:31–46`) are real proofs reducing to
  `holds_iff_discharged_witness` + `Frame.*`. The named endpoint of the "constructive
  adjudication escapes Arrow on the certifiable domain" thesis.

### `Metatheory/EpistemicDial.lean` (505 LOC) — Kind I, the template ✅

- The module that fully delivers the intended architecture. Defines `Dial`, `DiscloseAt`,
  the disclosure-lattice laws (`leak_mono`, `accepts_invariant_under_dial`,
  `accepts_bot_iff_discharged`, `:213–226`) — and **all 8 `Dregg2/Crypto/*` verifier kinds
  instantiate `DiscloseAt` and invoke the inherited keystone**:
  `Dregg2/Crypto/NonMembership.lean:327` builds `nonMembershipDisclose` and `:343`/`:352`
  proves `nonmembership_dial_wired` via `DiscloseAt.accepts_bot_iff_discharged`. Same
  pattern in Pedersen, Custom, Dfa, Temporal, Bridge, PredicateKernel, BlindedSet.
- The single⊕multi-party "unification" half (`:341–375`) operates over `Dregg2Mode`
  (`:258`), a local 3-element toy enum, **not** the real `Dregg2.Exec.AuthMode`; several
  conjuncts are `rfl`. The `DiscloseAt`-instantiation half is load-bearing; replacing the
  toy mode with the real `AuthMode` is the extension lane.

### `Metatheory/Open/FinalCoalgebra.lean` (157 LOC) — the strongest pure theorem ✅

- Constructively builds the Moore-behaviour final coalgebra (carrier `List Adm → Obs`) and
  proves `nuF_isFinal` and `nuF_exists` (`:139–147`) for arbitrary types, closing
  Categorical §3's OPEN, `#assert_axioms`-clean. The hard centerpiece (final-coalgebra
  existence) dispatched via the classical Moore route. Connecting `nuF` to a real
  `Dregg2.Boundary.TurnCoalg` cell is the consumption lane (currently unconnected).

### `Metatheory/Open/PerfectZK.lean` (333 LOC) — information-theoretic fragment, with teeth

- `view_indep_of_witness`/`view_factors_through_statement` (`:101–111`) unfold the `hperf`
  field; all content is in the assumption `view s w = sim s`. Only instances are toy
  `Unit`/`Bool` OTP (`:259`). Teeth present (`leaky_view_indep_FAILS`/`leaky_no_simulator`,
  `:300–307`) and a real Dregg2 bridge (`floor_bit_iff_discharged`, `:230`, to
  `Dregg2.Laws.Discharged`). The computational case is the explicit residual.

### `Metatheory/Open/PerfectUC.lean` (423 LOC) — degenerate fragment

- `perfectUC_composition` (`:200–208`) is the perfect (equality, not ≈) UC composition
  (`rw [hb]` / `congrArg ρ.compose`); the docstring (`:198–199`) flags the computational
  theorem (PPT, negligible advantage) as the residual. Teeth present (`realizes_fails`,
  `composition_needs_hypothesis`).

### `Metatheory/Open/ConservationMultiEdge.lean` (431 LOC) — REAL ✅ (Kind I/II)

- `round_cg5_conserves` (`:154–169`) is a genuine induction over `Round` using the real
  `Dregg2.Exec.JointCell.jointApplyRound`/`joint_cg5_conserves`, lifting single-edge
  conservation to multi-edge rounds, tied to the real `WhoYields.ConjGraph` WL cut. An
  actual generalization of a real Dregg2 result on real Dregg2 defs.

### `Metatheory/Open/CrossCellBisim.lean` (373 LOC) — REAL ✅ (Kind I/II)

- Lifts the real `Dregg2.Proof.ContendedCrossCell.applyHalfOut_comm_disjoint` (2-point
  commutation) to whole-history confluence `xcell_whole_history_confluent` (`:204`) over
  the coinductive adversary stream, with real obs-bisimulation. Teeth:
  `confluence_fails_when_coupled` (`:338`).

### `Metatheory/Open/CurvatureScreen.lean` (335 LOC) — REAL ✅ (Kind I/II)

- `curv_screen_sound` (`:183`) is a real ℚ-arithmetic proof (convexity/chord bound) in the
  shape of the real `Dregg2.Apps.OrbitalScreen.screen`, with teeth
  (`teeth_curv_rejects`/`teeth_conjunction_in_step`).

### `Metatheory/Open/AuthorityClosure.lean` (300 LOC) — REAL, self-contained (Kind III-ish)

- `noforge_closure`/`amp_noforge_closure` (`:128–283`) are real induction-over-traces
  non-amplification proofs. Self-contained (`TracesTo`/`AmpClosed` defined locally); the
  operational `withholding_no_free_copy` line lives elsewhere. Candidate-independent, not
  yet instantiated by a concrete Dregg2 authority object.

---

## The known-hard centerpieces

| Centerpiece | Status |
|---|---|
| **Co-Yoneda collapse / final coalgebra existence** | **PROVED** via Moore construction (`FinalCoalgebra.nuF_exists`). A legitimate route; not consumed by Dregg2. |
| **Faithful `∀_a = Knows` epistemic triple** | **PROVED + connected.** `Dregg2/Metatheory/Lawvere.lean:113 lawvere_triple` (`∃_f ⊣ f* ⊣ ∀_f` as GaloisConnections), on `Metatheory.EpistemicConsensus.Frame`, with negative teeth (§B.4: the clean triple does NOT lift to the Byzantine fibre). The strongest single result in the stack. |
| **Rigidity isos** | Not delivered here; closest is `embeddings_agree_at_extremes` (toy `rfl`). |
| **UC-security transport (PerfectUC)** | Perfect/equality fragment only; computational UC is the residual. |
| **PerfectZK** | Information-theoretic fragment only, toy instances; computational ZK is the residual. |

---

## Load-bearing pieces

1. **`EpistemicDial.DiscloseAt`** — the abstraction the 8 Dregg2 Crypto kinds instantiate
   and inherit (`accepts_bot_iff_discharged`). The architecture working as intended; the
   pattern to extend.
2. **`EpistemicConsensus.Frame` → `Lawvere.lawvere_triple`** — real upstream epistemic
   abstraction the Dregg2-side consumes; the `∀_a = Knows` triple with teeth.
3. **`FinalCoalgebra.nuF_exists`** — closed-OPEN theorem.
4. **`Categorical` §4/§5 bridges** — `tier_commit_eq_crossTierJoin` (`rfl` on real `Tier`),
   `tier1Eligible_closedUnderJoin` (reuses real `admits_sound`).
5. **The three "Open" lifts** — `ConservationMultiEdge.round_cg5_conserves`,
   `CrossCellBisim.xcell_whole_history_confluent`, `CurvatureScreen.curv_screen_sound`:
   real generalizations on real Dregg2 app theorems, each with anti-vacuity teeth.
6. **The teeth discipline** — every `*_FAILS`/`fails`/`cannot` lemma is a required pattern.

## Re-narrations (valid, but not the generalization)

- `Categorical` §1 Conservation + §2 Seam — abstract lookalikes never instantiated; real
  Dregg2 conservation is proved independently.
- `ConstructiveKnowledge` §4–§5 — re-wrappers of `stepComplete_preserves`, `sound_refl`,
  `withholding_no_free_copy` under new names.
- `EpistemicDial`'s single⊕multi-party "unification" — over same-file toy enums;
  `Dregg2Mode ≠` real `AuthMode`.
- `PerfectZK`/`PerfectUC` — toy instances; the computational theorems are the residual.
  Valuable as specifications with teeth.

---

## Making the abstraction load-bearing (the dependency-inversion lane)

Invert the remaining dependencies so `Dregg2` instantiates and inherits, instead of
`Metatheory` re-naming Dregg2 theorems:

1. **Make the conservation functor real.** Define `Σ : DreggCellCat ⥤ Discrete ℕ` from the
   actual `Dregg2.Core.Conservation`, then *derive* `withholding_no_free_copy` by applying
   `Categorical.no_free_copy`, deleting the independent proof in `Core.lean`.
2. **Instantiate `Metatheory.Seam`** with the real `Predicate ⊣ Witness` of `Dregg2.Laws`
   (a single `Seam` value), so `seam_*` become theorems about the system.
3. **Replace `EpistemicDial.Dregg2Mode` (toy) with the real `Dregg2.Exec.AuthMode`** and
   re-prove the embedding, so single⊕multi-party unification touches the real disclosure
   type.
4. **Connect `FinalCoalgebra.nuF` to the real cell** (`Dregg2.Boundary.TurnCoalg`): exhibit
   the anamorphism of a real cell into `nuF` and state no-drift as agreement-with-νF.
5. **Reframe `ConstructiveKnowledge` §4–§5 as `instance`/`abbrev` aliases**, not `theorem`
   re-statements, so "this IS the Dregg2 theorem, renamed" is structural.
6. **Land the computational ZK/UC** or rename `PerfectZK`/`PerfectUC` to
   *information-theoretic-fragment* in their public names, so the residual is visible at the
   type level.

Steps (1)–(4) move the abstraction from narrating to load-bearing.
