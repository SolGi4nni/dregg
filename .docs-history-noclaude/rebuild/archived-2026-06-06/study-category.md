# study-category — stress-testing the dregg2 categorical model

> ⚑ **GROUND-CHECKED vs live Lean 2026-06-02** (post-2-compaction drift-repair); REAL /
> DECORATIVE / ASPIRATIONAL tags carry file:line receipts. Every `Categorical.lean` line
> citation below was re-verified EXACT against the live file (`:584`/`:602`/`:613`/`:646`/
> `:675`/`:686`/`:741`/`:752`/`:762`/`:563`/`:104`/`:118`/`:135`/`:159` all land on the
> named theorem). The doc was accurate on `Categorical.lean` — the drift it carried is that
> it predates the **concrete coalgebra-level realization** of the §1 reframe, which now lives
> in `Dregg2/JointTurn.lean` + `Dregg2/Hyperedge.lean` + `Dregg2/Spec/JointViaHyper.lean`
> (the doc never named these; they are the *living* home of the finding). See **§0(c)**.

> **Current as of 2026-06-02.** This study's analysis has since been *materialized into
> proved Lean* — almost all of its load-bearing recommendations now exist as
> `#assert_axioms`-pinned theorems in **`metatheory/Metatheory/Categorical.lean`**, a module
> that cites this study by name (`study-category §5`, `Categorical.lean:37`). The status
> tags below are updated from "stress verdict" to "stress verdict + where it landed in code."
> The single correction the original got wrong (the `sound_of_step_complete` keystone) is
> annotated inline in §1.4. See the **§0(b) code-receipts table** added below.
>
> **Tag legend (added 2026-06-02):** **REAL** = a term-proved Lean object, `#assert_axioms`-
> pinned, with teeth (judged by reading the proof body, never by `#assert_axioms` alone —
> that pin certifies *kernel-clean*, NOT *non-vacuous*). **DECORATIVE** = vocabulary only, no
> distinct Lean object carries it (grep-confirmed absent or subsumed). **ASPIRATIONAL** =
> honestly-named OPEN, unbuilt.
>
> **Source-path note (CORRECTED):** the actual Lean lives under `metatheory/Dregg2/`, in
> namespace `Dregg2.{Core,Laws,Boundary}` — NOT `metatheory/Metatheory/{Core,Laws,Boundary}`
> (that path is stale). Receipts: `Dregg2/Core.lean`, `Dregg2/Laws.lean`,
> `Dregg2/Boundary.lean`. The first-principles *derivations* are in
> `Metatheory/Categorical.lean`.

> **Brief:** does the dregg2 category (`dregg2.md §1` coalgebra + `§1.6` ⊗ + `§2` the
> two laws; `discoveries §3` corrections) actually hold together, or does the
> categorical framing hide lurking impossibilities? Tags: `[HOLD]` survives stress ·
> `[STRAIN]` holds but only under a stated restriction · `[BREAK]` the categorical claim
> as written is false / ill-typed. The fulcrum question throughout: **where is the
> category load-bearing (catches a real bug) vs decorative (cosplay)?**
>
> Sources read: `Dregg2/{Core,Laws,Boundary}.lean` + `Metatheory/Categorical.lean` (the actual
> encodings — see source-path note above), `pdfs/{mathematical-theory-of-resources,
> selinger-graphical-languages,coalgebraic-semantics-silva,guarded-recursion-coinductive}`,
> `pdfs/discoveries.md §3`, `circuit/src/bilateral_aggregation_air.rs`, `cell/src/program.rs`.

---

## 0(b). Code-receipts — where each finding landed in Lean (verified 2026-06-02)

| Study finding | Verdict (re-checked) | Tag | Lean receipt (PROVED, `#assert_axioms`-pinned unless noted) |
|---|---|---|---|
| Tensor of coalgebras is not final; binding is a limit *outside* the coalgebra map | **[BREAK→reframe] — REALIZED (twice)** | **REAL** | *Abstract:* `IsJointTurn` = `IsPullback` (`Categorical.lean:584`); `jointTurn_universal` (`:602`), `jointTurn_mediator_unique` (`:613`); N-ary `IsWideJointTurn` (`:646`) + `wideJointTurn_universal` (`:675`), `wideJointTurn_mediator_unique` (`:686`), pinned `:881`–`:883`. *Concrete coalgebra-level (NEW, the living home — see §0(c)):* `JointTurn.binding_is_proper` (`JointTurn.lean:333`), `Hyperedge.hyper_binding_is_proper` (`Hyperedge.lean:164`). The agreement = a (wide) **pullback** (a limit), as predicted. |
| Conservation = monoid-hom + invariance, "functor" is decorative on a discrete target | **[STRAIN] — REALIZED & DERIVED** | **REAL** (the monoid-hom); **DECORATIVE** (the "functor" framing, *by design* — that is the finding) | `measure_unit` (`:104`, = `unit_zero`), `measure_tensor` (`:118`, = `tensor_add`), `measure_invariant` (`:135`, = `conservation_ordinary`) DERIVED from "Σ lax-monoidal → `Discrete M`"; honesty caveat cites *this study §5* at `:37`+`:232`. |
| No-`Δ`/`◇` (no copy/discard) is the structural content of conservation | **[HOLD] — now a THEOREM** | **REAL** | `no_free_copy` (`:159`), `no_free_discard` (`:191`), `diagonal_collapses_measure` (`:204`), `nonzero_count_forbids_diagonal` (`:213`); Lean-side shadow `Dregg2.Core.withholding_no_free_copy` (`Core.lean:227`, hypotheses `[AddCommMonoid M] [IsCancelAdd M]`). |
| `Predicate ⊣ Witness` Galois + VERIFY/FIND seam | **[HOLD] — GROUNDED (open seam closed)** | **REAL** | `predicate_witness_galois` now pinned to the `Discharged`/`Verify` polarity (`Laws.lean:122`, via `polarity_galois` `:96`) — the §3 "free `l,u` placeholder" is gone; `Categorical.lean §2` derives the full `Seam` adjunction (`seam_attenuate_monotone`/`seam_unit`/`seam_counit`/`seam_closure_idem` `:304`/`seam_roundtrip` `:314`). |
| I-confluence join-semilattice = tier-1 eligibility (load-bearing type-error) | **[HOLD] — REALIZED** | **REAL** | `confJoin_lub` (theorem `Categorical.lean:483`, pinned `:897`), `tier1Eligible_closedUnderJoin` (theorem `:493`, pinned `:898`). |
| §1.4's named keystone `sound_of_step_complete` (single-cell) | **CORRECTION** | **(removed)** | That theorem was **false as stated** (refuted via `Spec.Carrier = Empty`) and **REMOVED**; the well-posed keystone is `stepComplete_preserves` (`Boundary.lean:177`, PROVED via `Execution.invariant_run`). See §1.4 annotation. |
| Cell existence `∃ νF, IsFinalCell νF` | **[HOLD] *(existence still ASPIRATIONAL)*** | **REAL** (univ. prop + uniqueness); **ASPIRATIONAL** (the carrier `∃ νF`) | `IsFinalCell` (`Categorical.lean:741`), `ana_unique` (`:752`, pinned `:884`), `final_unique_roundtrip` (`:762`), `cell_self_bisim` (`:563`, pinned `:879`) all PROVED *conditional on finality*; the carrier construction (`∃ νF`, `:787`) is honestly OPEN/unbuilt. |

**Open-hole state (RE-verified 2026-06-02 by reading proof bodies):** `Core.lean`, `Laws.lean`,
`Categorical.lean`, `JointTurn.lean`, `Hyperedge.lean`, `Spec/JointViaHyper.lean` are all
**free of open holes in proof terms** — every literal open-hole string is a *docstring/comment*
narrating a discharged or retired obligation (grep: `Categorical.lean` 1 hit @ line 15
"kernel-clean"; `Hyperedge.lean` 4 hits all in `/-! -/` blocks; `JointTurn.lean`
hits are all in the §0 style-note / docstrings, e.g. the stale "`JointTurn.lean:447`, open hole"
back-references which are themselves now STALE — see §0(c)). `Boundary.lean`'s header line 29
("every theorem stated with an open-hole body") is **STALE prose** — the bodies
(`stepComplete_preserves`, `bisim_eq`, `sound_refl`, `boundary_respecting_sound`) are all
proved.

---

## 0(c). The frontier MOVED: the §1 reframe is now realized at the concrete coalgebra level (NEW 2026-06-02)

The original study verified the §1 reframe (cross-cell turn = proper-subobject / pullback,
NOT a tensored coalgebra step) and tracked it landing in the *abstract* `Categorical.lean`
(`IsJointTurn := IsPullback`, an arrows-only mathlib pullback). **Since the last compaction,
the same finding has been re-realized at the concrete `TurnCoalg`-level**, in three modules
the original doc never names. This is the design folded forward; these are the *living* home
of §1, and they carry the exact known-correction names:

| Live object | File:line | Tag | What it is |
|---|---|---|---|
| `SharedTurnId` (CG-2 binary pullback) | `Dregg2/JointTurn.lean:91` | **REAL** | the turn-identity equalizer for two participants; `SharedTurnId.agree` (`:112`) PROVED. |
| `JointBinding` (CG-2 ⊗ CG-5 HYPOTHESIS) | `JointTurn.lean:134` | **REAL** | the irreducible cross-cell binding, carried as data, never derived. Exactly the §1.4 "binding as a hypothesis you must supply." |
| `joint_sound` (THE binary keystone) | `JointTurn.lean:230` | **REAL** | joint soundness = (per-cell `StepComplete`) ∧ (the `JointBinding` premise), reduced in one step to `Boundary.stepComplete_preserves`. The §1.4 `joint_sound` sketch, now actually proved. |
| **`binding_is_proper`** (the CORRECT irreducibility) | `JointTurn.lean:333` | **REAL** | ⚑ the known-correction: the old `tensor_not_final` was *false as stated* (product of finals IS final for the product functor); the true content is the **proper-subobject** fact — `JointAdmissible` is a proper equalizer-subobject of the product carrier (witness: two 1-state cells, each half-edge `1`, CG-5 `1+1=2≠0`). PROVED. |
| `joint_sound_needs_binding` | `JointTurn.lean:271` | **REAL** | the negative companion: no "both step-complete ⇒ joint-admissible-everywhere" theorem, derived FROM `binding_is_proper`. |
| `Hyperedge` (the wide pullback over `TurnId`) | `Dregg2/Hyperedge.lean:80` | **REAL** | the N-ary apex: one shared `tid` all N legs commit to (Mina's `account_updates_hash`), one Σ-over-`univ` CG-5. `legs_agree` (`:111`, every pair agrees, no pairwise data) PROVED. |
| **`hyper_binding_is_proper`** | `Hyperedge.lean:164` | **REAL** | ⚑ the N-ary analogue of `binding_is_proper` (singleton hyperedge, half-edge `1`, `1≠0`). PROVED. (`hyper_not_all_admissible` `:505` is its general-`ι`, general-`Bal` form, also PROVED.) |
| `hyperedge_sound` (N-ary safety keystone) | `Hyperedge.lean:374` | **REAL** | what `family_joint_sound` was *reaching for*: reduces to `stepComplete_preserves` on the N-fold product `hyperCoalg`, all N legs discharged by one `∀ i` (`hyper_stepComplete` `:337`). The O(N²) pairwise-gluing cut *does not exist at the apex*. PROVED, axiom-clean. |
| `joint_via_hyperedge` (the UNIFIED N-ary reading) | `Dregg2/Spec/JointViaHyper.lean:75` | **REAL** | ⚑ the NEW frontier the study did not anticipate: `family_joint_sound` discharged through the hyperedge apex; `binary_joint_via_hyperedge` (`:141`) recovers the bilateral as the `ι=Fin 2` slice; `hyperedge_is_validity_not_canonicity` (`:226`) is the "validity ≠ canonicity" factoring theorem. All pinned `:317`–`:322`. |

**The drift this repairs:** the original `§0(b)` row for the tensor cited *only*
`Categorical.lean`'s abstract pullback. That was not wrong, but it was the *weaker* home —
the abstract `IsJointTurn := IsPullback` proves the universal property in an arbitrary
category but is not wired to a `TurnCoalg`. The concrete `JointTurn`/`Hyperedge`/`JointViaHyper`
layer *is* wired to the cell behaviour functor and is where the soundness keystones
(`joint_sound`, `hyperedge_sound`, `joint_via_hyperedge`) actually live.

**`family_joint_sound` is no longer an open hole.** Several modules still carry stale
back-references "`family_joint_sound` (`JointTurn.lean:447`, open hole)" in their docstrings
(`Hyperedge.lean:293`, `JointViaHyper.lean:6`); the *referent* is now PROVED at
`JointTurn.lean:458` (it concludes per-participant no-drift ∧ CG-5 Σ=0; the old ill-posed
`Sound (J.cell i) (Spec i)` free-`Spec` form was refuted at `Spec.Carrier = Empty` and
retired, exactly as `Boundary` retired `sound_of_step_complete`). Those docstring line-refs
(`:447`) are themselves drift — the body moved to `:458` and is no longer a stub.

**Bottom line of §0(c):** the §1 finding the study called "the single most important
coherence-finding" is now PROVED at three escalating levels (binary `joint_sound` → wide
`hyperedge_sound` → unified `joint_via_hyperedge`), with the irreducibility named correctly
as `binding_is_proper`/`hyper_binding_is_proper` (proper subobject), NOT the retired-and-false
`tensor_not_final`. The study's mandate is *over*-discharged.

---

## 0. TL;DR verdict

| Claim | Status | One-line |
|---|---|---|
| Cell = final coalgebra `νF`, `F X = Obs × (AdmTurn ⇒ X)` | **[HOLD]** *(existence ASPIRATIONAL)* | Moore coalgebra; bisimulation = soundness is clean. **REAL:** universal property + uniqueness (`IsFinalCell` `Categorical.lean:741`/`ana_unique` `:752`/`final_unique_roundtrip` `:762`), bisim-as-coalg-morphism + reflexivity (`cell_self_bisim` `:563`), all `#assert_axioms`-pinned. **ASPIRATIONAL:** the *existence* of `νF` (the carrier construction, Adámek / `▷`-backend, `∃ νF` at `:787`) is honestly OPEN/unbuilt. |
| **Cross-cell turn = morphism on `νF₁ ⊗ νF₂`** | **[BREAK→reframe] — REALIZED as a proper subobject / (wide) pullback** | `νF₁ ⊗ νF₂` is **not** the final coalgebra of a product behaviour; the binding is a proper-subobject constraint *outside* the coalgebra map. **Now in code at two levels:** abstract `IsPullback` (`IsJointTurn`, `Categorical.lean:584`; N-ary `IsWideJointTurn` `:646`); **concrete coalgebra-level (the living home, §0(c))** — `binding_is_proper` (`JointTurn.lean:333`), `hyper_binding_is_proper` (`Hyperedge.lean:164`), keystones `joint_sound`/`hyperedge_sound`/`joint_via_hyperedge`. ⚑ The earlier `tensor_not_final` slogan is **retired and was FALSE** (product of finals IS final for the product functor); the true content is the proper-subobject fact. The "`⊗` of coalgebras" slogan is retired. |
| `Σ_k` strong-monoidal functor, constant on non-mint/burn homs | **[STRAIN] — DERIVED as monoid-hom + invariance** | The content is a **monoid homomorphism on counts + invariance** (Reading A), now *derived* from "Σ lax-monoidal → `Discrete M`": `measure_unit`/`measure_tensor`/`measure_invariant` (`Categorical.lean:104`/`:118`/`:135`). "Functor" framing is vacuous on the discrete target — confirmed in code, which cites this study (`:37`). Generalized from `ℕ` to any `AddCommMonoid M` (`Core.lean:57`). |
| `Predicate ⊣ Witness` Galois + VERIFY/FIND seam | **[HOLD] — GROUNDED** | Genuinely structural; the Heyting residual *is* attenuation. **The §3 open seam is now closed:** `predicate_witness_galois` is pinned to the `Discharged`/`Verify` polarity (`Laws.lean:122`), no longer free `l,u` placeholders. The single most coherent part. |
| GC = reachability side-condition on `ν` | **[HOLD]** | Absorbs cleanly; no new categorical machinery. |

**The single most important coherence-finding is in §1: the tensor.** It is the one
place the category is *load-bearing* — it catches a real architectural fact (cross-cell
joint soundness is irreducible to per-cell soundness) — *precisely by failing* to be
what the slogan says. The metatheory's Boundary module must encode the binding as an
**external joint obligation**, never as a derived clause of a tensored `step`.

---

## 1. The tensor of coalgebras — the load-bearing finding `[BREAK→reframe]`

### 1.1 The subtlety, stated precisely

A cell is the final `F`-coalgebra `νF`, `F X = Obs × (AdmTurn ⇒ X)`. The dregg2 claim
(`§1.6`) is that a turn over N cells is a *morphism* on the tensor `νF₁ ⊗ … ⊗ νFₙ`, with
the cross-cell binding an equalizer/pullback. The question the user wants stressed: **is
`νF₁ ⊗ νF₂` itself a coalgebra of the right shape — does codata tensor cleanly?**

**Answer: No, and the model is right not to need it to.** Two facts:

1. **The carrier tensors; the *finality* does not.** `νF₁ ⊗ νF₂` (a product of two
   carriers in the cartesian base, or a `⊗` in a symmetric-monoidal base) is a perfectly
   good *object*. But it is **not** the carrier of the final coalgebra of any single
   behaviour functor `G` whose successors range over the joint state. The final coalgebra
   of the *product* behaviour `G X = (Obs₁×Obs₂) × ((AdmTurn₁×AdmTurn₂) ⇒ X)` is
   `ν(F₁×F₂)`, and there is a canonical **comparison map** `ν(F₁×F₂) → νF₁ × νF₂` (pair the
   two anamorphisms) but **no inverse in general** — a joint behaviour carries
   *correlation* between the two streams that the product of the two final coalgebras
   forgets. Final coalgebras do **not** preserve products in this direction; only the
   *forgetful* direction is canonical. (This is the dual of the well-known fact that
   initial algebras don't tensor; cf. the resource-theory SMC never being cartesian,
   `mathematical-theory-of-resources §2`, and Selinger's no-`Δ`/`◇`, `§6`.)

2. **What *does* tensor cleanly is the guard, not the coalgebra.** Guarded recursion's
   `▶` modality preserves products via a canonical iso `can : ▶X × ▶Y ≅ ▶(X×Y)`
   (`guarded-recursion-coinductive`, denotation of `g(t₁,…,tₙ)`). This is exactly the
   productivity-level fact dregg2 leans on — and it is *strictly weaker* than the final
   coalgebra tensoring. It buys "the joint unfold is productive," **not** "the joint
   unfold is the final object." So even at the guard level, the support for "⊗ of codata"
   is a productivity iso, not a finality iso.

### 1.2 Consequence — exactly the doc's own §10 honesty note, sharpened

`dregg2 §10` already says: *"the type composes via `⊗` cleanly, but soundness of a
cross-cell turn is not reducible to per-cell soundness alone — it needs the joint
agreement binding as an irreducible extra."* **This study confirms that note and
upgrades it from a caveat to a theorem-shaped constraint:**

> **Cross-cell joint-soundness sits OUTSIDE the single-cell coalgebraic frame.** The
> binding is a morphism into an equalizer in the *base* category, not a clause of any
> coalgebra structure-map `c : X → F X`. There is no functor `F⊗` whose final coalgebra
> is `νF₁ ⊗ νF₂` and whose `step` *contains* CG-2/CG-5.

This is **grounded in code**: `bilateral_aggregation_air.rs` enforces CG-2 (turn-identity
agreement: every cell's row agrees on `TURN_HASH`/`EFFECTS_HASH_GLOBAL`/`ACTOR_NONCE`/
`PREVIOUS_RECEIPT_HASH`) and CG-5 (cross-side existence: every half-edge has its peer) as
**per-row constraints over a single shared trace holding all N cells' rows** — i.e. a
joint predicate over the tuple, declared per-cell by `StateConstraint::BoundDelta {
peer_cell, peer_slot, delta_relation: EqualAndOpposite }` (`program.rs:747`). A single
cell's `program.evaluate(old,new,ctx)` (§1.5, the `AdmTurn ⇒ Cell` arrow) **cannot**
discharge CG-2: it has no access to the peer's row. The agreement is structurally a
pullback over the shared `TURN_HASH`; the balance is structurally the equalizer.

### 1.3 Where the category is LOAD-BEARING here

This *is* the category catching a real bug, not cosplay. If you believed the slogan
("a cross-cell turn is just a morphism on the tensored coalgebra"), you would expect
cross-cell soundness to **fall out of** per-cell step-completeness — and you would build
a Boundary module that proves joint soundness by conjoining two single-cell
`sound_of_step_complete` instances. **That would be unsound:** two cells can each be
locally step-complete (each conserves *its own* slot, each has a valid auth path) while
the cross-cell turn they purport to share **does not exist as one turn** (mismatched
`TURN_HASH`) or **does not balance** (`Σ half-edges ≠ 0`). The tensor's failure to be
final is *precisely* the formal reason CG-2 ⊗ CG-5 must be an irreducible extra
obligation. The category earns its keep by forbidding the tempting wrong factoring.

### 1.4 Mandate for the metatheory Boundary module — **DONE (2026-06-02), see annotation**

> **Status 2026-06-02 — this mandate has been DISCHARGED, in `Metatheory/Categorical.lean`
> (not `Boundary.lean`).** Two corrections to the original text below:
>
> 1. **The joint object exists and is PROVED — as a pullback, not a hand-rolled struct in
>    `Boundary`.** `Categorical.lean §3` defines `IsJointTurn j₁ j₂ π₁ π₂ := IsPullback …`
>    (`:584`) — the cross-cell agreement *is* a mathlib pullback universal property — with
>    `jointTurn_interface_agrees` (`:592`, the "consistent shared boundary", `= IsPullback.w`),
>    `jointTurn_universal` (`:602`, existence of the mediator) and `jointTurn_mediator_unique`
>    (`:613`, uniqueness) all proved. The N-ary hyperedge is the **wide pullback**
>    `IsWideJointTurn` (`:646`) with `wideJointTurn_universal`/`wideJointTurn_mediator_unique`
>    (`:675`/`:686`), `#assert_axioms`-pinned (`:882`–`:883`). So the study's "binding is an
>    equalizer/pullback outside the coalgebra map" is now literally the encoded universal
>    property. (The *balance* half — CG-5, `Σ half-edges = 0` — lives separately in
>    conservation §1 as `measure`/`tensor_add`; only the *agreement* half is the pullback.)
>
> 2. **CORRECTION: `sound_of_step_complete` is GONE — it was false as stated.** The text
>    below cites `sound_of_step_complete` over the single carrier as "correct." That theorem
>    (and `step_complete_of_sound`) were **refuted** (`Spec.Carrier = Empty` makes `Sound`
>    uninhabited while `StepComplete` holds, machine-checked) and **removed** from
>    `Boundary.lean`. The well-posed single-cell keystone is now `stepComplete_preserves`
>    (`Boundary.lean:177`, PROVED via `Execution.invariant_run`): a `Good` predicate
>    preserved by every `StepInv`-respecting transition holds along the whole execution.
>    `Sound`/`IsBisim` survive only as *behavioural equivalence* (with `sound_refl`
>    `:211`/`bisim_eq` `:203`), NOT as the soundness keystone. The conclusion of §1.3 (don't
>    derive joint soundness by conjoining two single-cell soundness instances) **stands and is
>    sharpened** — there is no single-cell `Sound`-keystone to conjoin in the first place.
>
> 3. **NEW (2026-06-02): the mandate is realized at the CONCRETE `TurnCoalg`-level too, and
>    the `JointTurn` *sketch* below is now actual proved code.** Point 1's `IsJointTurn :=
>    IsPullback` is the abstract arrows-only version. The concrete realization — wired to the
>    cell behaviour functor, which is what the §1.4 sketch actually wanted — lives in
>    `Dregg2/JointTurn.lean` (binary: `SharedTurnId` `:91`, `JointBinding` `:134`,
>    `joint_sound` `:230`), `Dregg2/Hyperedge.lean` (N-ary wide pullback: `Hyperedge` `:80`,
>    `hyperedge_sound` `:374`) and `Dregg2/Spec/JointViaHyper.lean` (`joint_via_hyperedge`
>    `:75`). See §0(c). **⚑ The irreducibility theorem the study leaned on as "tensor not
>    final" is RETIRED-AS-FALSE and renamed:** the live name is `binding_is_proper`
>    (`JointTurn.lean:333`) / `hyper_binding_is_proper` (`Hyperedge.lean:164`). The product of
>    two final coalgebras IS final for the product functor, so "νF₁ ⊗ νF₂ is non-final" was a
>    mis-statement; the true, soundness-critical content is that the joint-admissible
>    configurations are a **proper subobject** (equalizer) of the product carrier — there exist
>    product states the binding *excludes* (CG-5 `1+1=2≠0`), so the binding is genuine content
>    per-cell data cannot supply. Same teeth, correct mathematics.

`Boundary.lean` today defines `TurnCoalg` for a **single** cell (carrier `X`, `step : X →
F X`) and ~~`sound_of_step_complete`~~ → `stepComplete_preserves` over that single carrier.
**This is correct and should not be "fixed" by adding a tensored coalgebra.** Instead, the
metatheory adds a *separate*, explicitly-joint object (the §3 pullback above; the original
sketch is preserved for the record):

```
-- a cross-cell turn is a span/tuple, NOT a coalgebra step
-- [ORIGINAL SKETCH — superseded by Categorical.lean's IsJointTurn := IsPullback]
structure JointTurn (T₁ T₂ : TurnCoalg Obs AdmTurn) where
  t      : AdmTurn                          -- the ONE shared turn
  agree  : turnId (T₁.next x₁ t) = turnId (T₂.next x₂ t)   -- CG-2 (pullback)
  balance: halfEdges x₁ t + halfEdges x₂ t = 0            -- CG-5 (equalizer)

theorem joint_sound :
    StepComplete T₁ … → StepComplete T₂ … → JointTurn T₁ T₂ → JointSound …
```

i.e. **joint soundness = (per-cell step-completeness) ∧ (the equalizer/pullback binding)**,
with the binding as a *hypothesis you must supply*, never a lemma you derive from the two
coalgebras. This matches `§1.6`'s "CG-2 ⊗ CG-5" and `§10`'s honesty note exactly — and the
agreement half is now the proved pullback `IsJointTurn` (`Categorical.lean:584`).

---

## 2. The conservation functor `Σ_k` `[STRAIN — coherent, but "functor" overstated]`

### 2.1 What is actually encoded

> **Freshness note (2026-06-02):** the live `Core.lean` has moved past "`Nat` + placeholders."
> `Conservation` (`Core.lean:100`) now carries `count : Cell → M` for **any** `[AddCommMonoid
> M]` (`:57`, generalized from `ℕ`, subsuming multi-asset `M = K → ℕ`), and `unit_zero`
> (`:126`) / `tensor_add` (`:134`) are **real structure fields proved satisfiable** (the
> trivial-measure instance, `:140`–`:150`), then **lifted to theorems** in `Categorical.lean`
> (`measure_unit`/`measure_tensor`, `:104`/`:118`). The "object-map agrees on the endpoints of
> an ordinary morphism" law is `conservation_ordinary` (`:184`), itself derived from the
> `conservation_step` class field (`:176`); mint/burn are the inflow/outflow `balance`
> equation (`count A + minted = count B + burned`, `:171`), not a signed delta (a bare
> `AddCommMonoid` has no negation). Reading-A below is exactly what the code does.

`Core.lean` encodes `Σ_k` as `Conservation.count : Cell → M` (`M` any `AddCommMonoid`) — a map
on **objects only** — plus laxator fields `unit_zero` (`count I = 0`) and `tensor_add`
(`count (A⊗B) = count A + count B`). The conservation law `conservation_ordinary` is then
`f.tag = ordinary → count A = count B`: the *object-map agrees on the two endpoints of an
ordinary morphism*. Mint/burn shift it by their declared amount (`mint_delta`,
`burn_delta`).

### 2.2 Is "constant on a hom-set" actually functorial?

**Two readings, and the doc conflates them:**

- **Reading A (what's encoded — coherent):** `Σ_k` is a **strong monoidal functor to the
  one-object category `(ℕ,+,0)` viewed discretely** — i.e. it sends every morphism to the
  identity of `(ℕ,+)` *as a monoid element*, and the real content is the **object-map**
  `count`, which is a monoid homomorphism `(|TurnCat|, ⊗, I) → (ℕ,+,0)`. "Constant on
  every non-mint/burn hom-set" then means: an ordinary `f : A⟶B` forces `count A =
  count B`. This is well-typed and respects ⊗ via `tensor_add`. **It does NOT break
  functoriality** — because to a discrete/one-object target *every* hom maps to the same
  identity, so composition is preserved trivially (`id ∘ id = id`). This is precisely an
  **additive monotone forced from `≥` to `=`** (`resources §5.3`: an additive monotone
  with `M(0)=0` *is* a monoid hom; dregg strengthens `≥` to `=` because mint/burn are the
  only count-movers). `discoveries §3.2`'s "invariance, not monotone" is right and
  defensible.

- **Reading B (the tempting over-claim — would break):** if one read `Σ_k` as a functor
  *into the poset `(ℕ,≤)` as a thin category* whose morphisms are `≤`-steps, then "constant
  on a hom-set" is fine (it's the object-map again), **but** then mint/burn morphisms must
  map to genuine `<` arrows and you have re-imported the monotone `≥` framing the model
  explicitly rejects — and worse, a thin `(ℕ,≤)` target **cannot carry the symmetry iso**
  Law 1 needs (`discoveries §3.2`'s own warning against "thin posetal"). So Reading B is
  self-contradictory; the model must mean Reading A.

### 2.3 The strain, named

The strain is purely *nomenclature*: calling `count` a "functor" invites Reading B and the
swarm's own thin-category trap. The **load-bearing object is the monoid homomorphism on
the object-monoid** `(|TurnCat|, ⊗) → (ℕ,+)`, with conservation = "ordinary morphisms are
hom-set-constant for it." It is coherent (Reading A), but the metatheory should state it as
`count` is a `MonoidHom` and conservation is an *invariance property of the morphism class*,
rather than leaning on "strong monoidal functor" — which, with a discrete target, is
true-but-vacuous on morphisms and therefore decorative. **Verdict: HOLD as a monoid-hom +
invariance; the "functor" dressing is DECORATIVE and slightly misleading.** Per-asset
folding (`§6.1`, the value rib) is the real soundness content and is independent of the
functor framing.

---

## 3. `Predicate ⊣ Witness` Galois + the VERIFY/FIND seam `[HOLD — most coherent]`

This is the part that is **most** load-bearing and **least** decorative.

- `Laws.lean` encodes `Verifiable.Verify : P → W → Bool` (decidable, the TCB), `Searchable.
  find : P → Option W` (opaque, no completeness/termination), and `search_sound` (the sole
  contract: returned witnesses verify). This *is* the VERIFY/FIND seam, and it is honest:
  the asymmetry (verify decidable, find undecidable — `§4`'s `HOU ⪯ GeneralMatch`) is
  baked into the *types* (`Bool` vs `Option`), not asserted in prose.
- The Galois connection (`predicate_witness_galois`) + Heyting residual (`predicate_heyting`:
  `a⊓b ≤ c ↔ a ≤ b⇨c`) is **coherent with the monoidal/coalgebraic structure, not bolted
  on**, because it *is* the structure-map's domain selector: `§1.5` says the `CellProgram`
  *is* the `AdmTurn ⇒ Cell` arrow, and its domain is `{t | ⋀cᵢ}` — a meet in the predicate
  Heyting algebra. **Attenuation = the residual `⇨`** (a stricter predicate entails a laxer
  one); this is the *same* `⇨` that `Authority/Positional.lean`'s `LossyMorphism` uses for
  "a key may only narrow." So the Galois/Heyting fragment threads through three modules
  (Laws → Core's admissibility → Authority's attenuation) coherently.
- `discoveries §3.4`'s downgrade from heavy `Adjunction` to `GaloisConnection` +
  `HeytingAlgebra` (both posetal) is the right call: it is the *thin* fragment, and lives
  comfortably *beside* the non-thin symmetric-monoidal Core (`§2.1`'s "thin only in its
  ordering fragment"). No incoherence.

**~~One seam to watch (not a break)~~ — CLOSED (2026-06-02).** The original text below worried
the predicate/witness orders were free `l`/`u` placeholders, so the connection was "stated but
not grounded." **That seam is now closed (REAL):** `predicate_witness_galois` (`Laws.lean:122`)
is pinned to the **`Discharged`/`Verify` polarity** — it is `polarity_galois` (`Laws.lean:96`,
the fully-provable connection on the verifier relation `R := Discharged`, i.e. `Verify p w =
true`) instantiated at the actual verifier. The orders are no longer free: the predicate side
is entailment-via-`Discharged`, the witness side is the induced specificity, and the find/verify
*contract* (`search_sound`, `Laws.lean:77`) is carried as the `SoundSearchable.find_sound`
typeclass field (the untrusted-plugin idiom), NOT an open hole. The Heyting residual is
`predicate_heyting` (`Laws.lean:132`), realized as attenuation in `Authority/Positional.lean`'s
`LossyMorphism` (`:191`) and the slot-caveat algebra (`Exec/Program.lean:19`,
`Spec/Guard.lean:47`). So the §3 "single most coherent part" is now also the *most grounded*.

> **Stale original (kept for the record):** "the predicate order `≤` (entailment) and the
> witness order `≤` (specificity) must be pinned for the Galois connection to typecheck —
> `predicate_witness_galois` takes `l`/`u` as free placeholders … *stated* but not *grounded*.
> This is an open-hole-discharge task." — DONE; see above.

---

## 4. GC, the runtime character, and the rest `[HOLD]`

- **GC (`§1.7`):** absorbs as a reachability side-condition on `ν` ("while reachable, the
  unfold never bottoms out"). No new machinery; the drop-protocol is the backward face of
  the await engine. Coherent. The coinductive frame genuinely does *not* strain here
  (confirmed against `§10`'s honesty note).
- **Runtime as theorems (checkpoint/restore/replay/time-travel):** these are anamorphism
  re-seeding facts about `νF`; standard codata, coherent.
- **Ordering / Law 2 (`§2.2`):** correctly held *out* of the proof and off the SMC — it is
  the thin join-semilattice fragment with the I-confluence side-condition. The decision to
  make tier-1 eligibility a *static type error* unless the cell-state is an
  invariant-preserving bounded join-semilattice (`discoveries §3.7`, BEC) is the category
  doing real work: it's a well-formedness condition the type system can check. **HOLD,
  load-bearing.**

---

## 5. Verdict — is more categorical detail needed, or is the level right?

> **Status 2026-06-02 — ALL THREE recommendations below have LANDED.** This section read as a
> forward to-do list; it is now a changelog. The frontier has moved past every item here (see
> §0(c) for where). Originals kept; each annotated DONE with a receipt.

**~~More detail is warranted in exactly one place: the cross-cell tensor (§1).~~** That detail
was added (§0(c)). Everywhere else the current level is right or *over*-specified (the "strong
monoidal functor" framing of conservation is more decoration than the monoid-hom needs).
Specifically:

1. ~~**Add the joint-turn object to the metatheory** (`§1.4`)~~ — **DONE.** Both abstractly
   (`Categorical.lean` `IsJointTurn := IsPullback` `:584`, `IsWideJointTurn` `:646`) and
   concretely (`JointTurn.JointBinding` `:134` + `joint_sound` `:230`; `Hyperedge` `:80` +
   `hyperedge_sound` `:374`; `Spec/JointViaHyper.joint_via_hyperedge` `:75`). The binding is
   taken as a hypothesis exactly as specified; the wrong factoring of §1.3 is forbidden.
2. ~~**Retire the "⊗ of coalgebras" slogan**~~ — **DONE.** The slogan is retired in-code; the
   carriers tensor in the base (`jointCoalg` `JointTurn.lean:158`, `hyperCoalg`
   `Hyperedge.lean:319`) while finality does **not** transport — and the *correct* statement is
   the **proper-subobject** fact (`binding_is_proper` `JointTurn.lean:333`), NOT the old
   `tensor_not_final` (which was false-as-stated and is retired).
3. ~~**Demote "conservation functor" to "conservation monoid-hom + invariance."**~~ — **DONE.**
   `Core.Conservation.count : Cell → M` is a monoid-hom-on-objects (`measure_unit`/
   `measure_tensor` are theorems, `Categorical.lean:104`/`:118`); the SMC's symmetry is kept;
   "strong monoidal *functor* on morphisms" is confirmed vacuous-on-the-discrete-target and the
   honesty caveat citing *this study §5* sits at the point of use (`Categorical.lean:37`/`:232`).

**Where category = load-bearing (catches real bugs) — all now REAL Lean objects:** (a) the
**cross-cell irreducibility** (correctly: the binding is a **proper subobject** of the product,
`binding_is_proper`/`hyper_binding_is_proper` — ⚑ *NOT* the retired-false "tensor non-finality"
phrasing this list originally used) forcing CG-2⊗CG-5 to be an irreducible premise — the single
most important finding; (b) the **no-`Δ`/`◇` (no copy/discard)** structural statement of
conservation (`no_free_copy`/`no_free_discard` `Categorical.lean:159`/`:191`); (c) the **Heyting
residual = attenuation** thread (`predicate_heyting` `Laws.lean:132` → `LossyMorphism`
`Positional.lean:191`); (d) the **I-confluence join-semilattice** tier-1 eligibility type-error
(`confJoin_lub`/`tier1Eligible_closedUnderJoin` `Categorical.lean:483`/`:493`).

**Where category = decorative (cosplay risk):** (a) "strong monoidal *functor*" for
conservation (the content is a monoid-hom; functoriality is vacuous on a discrete target);
(b) any reading of the cross-cell story as "tensoring coalgebras," which actively misleads.

**Bottom line:** the model **holds together** — but only because its own `§10` honesty
note quietly does the work the `§1.6` headline slogan overclaims. The category is genuinely
load-bearing, and it earns that status *by exposing*, not hiding, that **cross-cell
joint-soundness is an irreducible extra outside the coalgebraic frame.** ~~Encode that
honestly in `Boundary.lean`~~ — **that encoding now exists** (2026-06-02), and not in
`Boundary.lean` but in its own modules: `Dregg2/JointTurn.lean`, `Dregg2/Hyperedge.lean`,
`Dregg2/Spec/JointViaHyper.lean` (the binding as `JointBinding`/`Hyperedge`, the keystones
`joint_sound`/`hyperedge_sound`/`joint_via_hyperedge`, the irreducibility correctly named
`binding_is_proper`/`hyper_binding_is_proper` — a **proper subobject**, not the retired-false
"νF₁⊗νF₂ non-final"). The model is coherent at the right level of detail, and the study's
load-bearing recommendation is fully — indeed *over*- — discharged. ( ◕‿◕ )
