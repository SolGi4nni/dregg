# INTENT-REFS — Categorical Resource Exchange & String/Wiring Diagrams

**Pillar:** the formalism behind *"intent = a typed string-diagram hole; matching = plug a morphism into
the hole; resources are consumed/produced."*
**Companion to:** [`INTENT-AS-CO-RECEIPT.md`](./INTENT-AS-CO-RECEIPT.md) (the design spine this deepens).
**Sibling:** [`EXTERNAL-LEAN-REFERENCES.md`](./EXTERNAL-LEAN-REFERENCES.md) (Lean-library landscape — this
doc is the *mathematical-source* layer underneath it).
**Research date:** 2026-06-03. Status: reference map, not a spec.

Each reference below maps a precise theorem/construction onto a numbered hook in `INTENT-AS-CO-RECEIPT.md`
(§N). Citations are verified against the actual PDFs in `/Users/ember/dev/breadstuffs/pdfs/` where noted
`[in library]`; arXiv ids verified by fetching the abstract page.

---

## TL;DR ranking

| # | Reference | Gives us | Spine hook |
|---|---|---|---|
| **1** | **Coecke–Fritz–Spekkens, *A mathematical theory of resources*** | resource theory = SMC; convertibility preorder ⪰; monotones; catalysis | §2 face 3, §3 (matching = convertibility), §5 (DeFi as conversion) |
| **2** | **Spivak, *The operad of wiring diagrams*** | the *typed hole + fill* itself = operadic substitution | §1 (co-receipt = hole), §3 (plug a box), §6.3 (compose ≠ conjoin) |
| **3** | **Fong, *Decorated cospans*** + **Fong–Spivak, *Hypergraph categories*** | open systems glued on shared boundaries = composition of (decorated) cospans | §3 cross-cell, §7 JointTurn/CG-2 equalizer, escrow-as-decoration |
| **4** | **Selinger, *Graphical languages for monoidal categories*** `[in library]` | the rigorous string-diagram + coherence backbone (sound equational reasoning) | §1 diagrams, all conservation diagrams |
| **5** | **Riley, *Categories of Optics*** (+ Clarke et al. update) | get/put profunctor optics = the resource-in / outcome-out reading; Tambara = the coend solver | §3 the `∫^B` solver, §7 open-game tie-in |
| **6** | **Baez–Master, *Open Petri nets*** `[in library]` | token/marking conservation + reachability *relation* as compositional semantics | §5 conservation, §2 resources, multi-hop reachability |
| **7** | **Coecke–Kissinger, *Picturing Quantum Processes*** | the canonical textbook for diagrammatic reasoning in SMCs (Frobenius/spider calculus) | §1–§3 pedagogy; spiders = the Frobenius structure hypergraph cats need |

---

## 1. Coecke, Fritz, Spekkens — *A mathematical theory of resources* — **THE key one**

- **Authors / year / venue:** Bob Coecke, Tobias Fritz, Robert W. Spekkens, 2014 (published *Information &
  Computation* 250 (2016) 59–86).
- **arXiv:** [1409.5531](https://arxiv.org/abs/1409.5531)  ·  `[in library: mathematical-theory-of-resources-1409.5531.pdf]`
- **What it gives us + map onto the spine.** This is the categorical framework for *"what can be converted
  into what, given the resources you have for free"* — i.e. **intent-matching/convertibility is literally a
  resource-theory question.** Two layers we reuse verbatim:
  - **Rich layer (Def 2.1):** a resource theory **is** a symmetric monoidal category `(D, ∘, ⊗, I)` —
    objects = resources, morphisms = *free* (zero-cost) conversions, `⊗` = "side by side", `I` = void
    resource. This is exactly our turn-category with `⊗` = cells side-by-side (multi-cell JointTurn).
  - **Core layer (Def 4.1):** collapse each hom-set to *"is there any conversion?"* → a **commutative
    preordered monoid** `(R, +, ⪰, 0)`, the **theory of resource convertibility**. *Crucially the monoid
    can vary independently of the preorder.* → **`a ⪰ b` IS our intent-match relation**: "the resources I
    bring (`A`) can be converted to the outcome I demand (`C`)." A fillable intent `A ⊢ C` is precisely
    `A ⪰ C` witnessed by a morphism.
  - **Monotones (Def 5.1):** `M : R → ℝ` with `a ⪰ b ⟹ M(a) ≥ M(b)` — a conserved/monotone quantity; "any
    measure is a crude shadow of the preorder." → our per-`LinearityClass` total `Σ_k` is a monotone,
    **strengthened to an invariant (`=`, not `≥`)** on non-mint/burn turns (the kernel conservation law,
    §5 table).
  - **Catalysis (§4):** `c` enables `a → b` when `a ⊁ b` but `a + c ⪰ b + c`. → the formal model of a
    **read-only / attenuating capability** (held, not consumed by a fill) and of an escrowed bond that must
    be *present* to fill but is returned — §2 face 3.
  - **Free resources `{A : D(I, A) ≠ ∅}`** = mintable-from-nothing (a genesis grant) — §5 "no value minted."
- **Lean/mathlib status.** No dedicated resource-theory library exists. **Build directly on mathlib:**
  `CategoryTheory.MonoidalCategory` + `SymmetricCategory` for the rich layer; `Order.Preorder` +
  `OrderedCommMonoid` / `Mathlib.Algebra.Order.Monoid.*` for the convertibility core; `OrderHom` (`→o`) for
  monotones. The two-layer split is the formal home of correction **C1** in
  `pdfs/LEARNINGS-laws-linear-monoidal.md` (don't try to carry conservation on a thin posetal cat).
- **Why ranked #1.** It is the single source that says, in one breath, *intent ≈ convertibility ≈ a
  preordered-monoid relation generated by an SMC of free conversions* — unifying §2 (resource face), §3
  (matching), and §5 (DeFi-as-conversion) under one preorder.

## 2. Spivak — *The operad of wiring diagrams* — **the typed-hole-and-fill itself**

- **Author / year:** David I. Spivak, 2013. Subtitle: *formalizing a graphical language for databases,
  recursion, and plug-and-play circuits.*
- **arXiv:** [1305.0297](https://arxiv.org/abs/1305.0297)  ·  `[PULLED → spivak-operad-of-wiring-diagrams-1305.0297.pdf]`
- **What it gives us + map onto the spine.** This is the *exact* formal content of §1's picture: **a box with
  a hole you plug another box into.** Spivak shows wiring diagrams are the **morphisms of an operad `T`**
  (§4, "the typed wiring-diagram operad `T_C`"): the objects/colours are *boxes* (a typed input/output
  interface — our `resources-offered : A ⊗ outcomes-demanded : C`), and a morphism is a *wiring diagram* that
  nests inner boxes into an outer one. **Operadic substitution** (`∘_i`) — substituting a wiring diagram for a
  box — is *precisely* "plug a morphism into the typed hole" (§1 `fulfill`). An **algebra over the operad**
  (he uses `Rel`, relations) assigns concrete fillings to each box and is *functorial under substitution* —
  i.e. **the fill type-checks and conserves by construction.** This is the categorical content of:
  - §1 — intent = "the same diagram with the interior left as a typed hole"; `fulfill` = operadic
    substitution into that hole.
  - §3 / §6 item (3) — dregg1's `compound` is *conjunction*, but a real exchange needs *composition /
    dataflow*: the operad's nesting IS the wiring that conjunction lacks.
  - §5 — recursion + plug-and-play (his §5, *closed operads*) = standing offers (AMMs) and recursive
    multi-hop fulfillment.
- **Related (same school):** *Algebras of Open Dynamical Systems on the Operad of Wiring Diagrams* (Vagner–
  Spivak–Lerman, [1408.1598](https://arxiv.org/abs/1408.1598)) — the *dynamical* algebra, if cells-as-running-
  processes become relevant; and *Operads of Wiring Diagrams* (Yau, [1512.01602](https://arxiv.org/abs/1512.01602))
  — a careful operad-theoretic monograph if we need the coherence in full.
- **Lean/mathlib status.** **No operad / coloured-operad / multicategory library in mathlib** (mathlib has
  `Multifunctor` and `Free` monoidal but not operads). Two honest paths: (a) **don't formalize operads
  directly** — encode the hole-and-fill via the **free symmetric monoidal / PROP** route (`CategoryTheory.
  Monoidal.Free.Basic`) where composition `≫` *is* the substitution; or (b) treat a one-object-per-interface
  operad as a multicategory we hand-roll. Recommendation: path (a) — `fulfill` becomes ordinary morphism
  composition in a free SMC, and we get coherence (§4 below) for free.

## 3. Fong, *Decorated cospans* + Fong–Spivak, *Hypergraph categories* — **open systems glued on boundaries**

- **Decorated cospans:** Brendan Fong, 2015, *Theory & Applications of Categories* 30 (2015) 1096–1120.
  arXiv [1502.00872](https://arxiv.org/abs/1502.00872)  ·  `[PULLED → fong-decorated-cospans-1502.00872.pdf]`
- **Hypergraph categories:** Brendan Fong & David Spivak, 2019, *TAC* 34. arXiv
  [1806.08304](https://arxiv.org/abs/1806.08304)  ·  `[PULLED → fong-spivak-hypergraph-categories-1806.08304.pdf]`
- **Lineage:** Baez–Fong–Pollard black-boxing of circuits/Markov processes ([1504.05625] / Pollard thesis);
  Fong's thesis *The Algebra of Open and Interconnected Systems* (2016).
- **What it gives us + map onto the spine.** An **open system** is a morphism with *exposed boundary ports*; you
  compose two open systems by **gluing the outputs of one to the inputs of the other** — a **cospan**
  `X → N ← Y` composed by **pushout** over the shared boundary. This is the precise model of our **cross-cell
  JointTurn** and the **CG-2 equalizer** (§3, §7): two cells expose a shared interface and the joint turn is
  the *gluing* along it.
  - **Decoration (Fong's theorem):** from a lax (braided) monoidal functor `F : (C, +) → (D, ⊗)` you get a
    **symmetric monoidal category of `F`-decorated cospans** — morphisms are a cospan `X → N ← Y` *together
    with a decoration* `1 → F(N)` (Abstract, [1502.00872]). → **the decoration is exactly where the escrow /
    predicate / validity-window rides** (§2 faces 2–4): the cospan is the bare port-interface (face 1), and
    `F(N)` carries the funded resources + the `Prop` + the causal/frame window. Composition glues interfaces
    *and* combines decorations — i.e. **escrow + predicate compose with the dataflow**, which is exactly the
    conservation-across-a-fill we want (§7 "conservation-across-a-fill as a corollary").
  - **Hypergraph category = the target structure (Fong–Spivak coherence theorem):** every object carries a
    **special commutative Frobenius monoid** (a "spider": copy/merge wires), and — their headline — *a
    hypergraph category is simply a "cospan-algebra," a lax monoidal functor from `Cospan` to `Set`*; the
    category of objectwise-free hypergraph cats is **equivalent** to the category of cospan-algebras. → this
    is the formal license to **wire ports together arbitrarily (fan-in/fan-out of a resource port)** — the
    structure a multi-party auction settlement or an AMM-router needs at the *port* level.
  - **Caveat / honest boundary:** a *hypergraph* category has copy/merge spiders, which is **cartesian-ish at
    the wiring level** — that re-imports duplication. The honest move (consistent with correction **C2/C3** in
    `LEARNINGS-laws-linear-monoidal.md`) is: use cospan/decorated-cospan composition for the **interface
    gluing**, but keep the **resource-carrying decoration linear** (Frobenius on *ports/names*, not on
    *resource quantities*). The spiders route *identity of a shared port*, not *copies of value*.
- **Lean/mathlib status.** mathlib has the **cospan diagram shape** (`CategoryTheory.Limits.Shapes.Pullback.
  Cospan`: `WalkingCospan`, `cospan f g`) and **pushouts** (`HasPushout`, `pushout`, `WidePushoutShape`) — so
  the *composition law* (glue = pushout) is constructible — **but there is NO category-of-cospans, no
  decorated-cospan, and no hypergraph-category / Frobenius-on-every-object construction in mathlib.** This
  would be a genuine BUILD (a small but real contribution): a `Cospan`-category over a category with pushouts,
  then Fong's decoration functor. Estimated as the **highest-leverage new categorical artifact** because it is
  the home of "open turns compose," and nothing upstream provides it.

## 4. Selinger — *A survey of graphical languages for monoidal categories* — **the diagram backbone**

- **Author / year:** Peter Selinger, 2009/2011 (in *New Structures for Physics*, Springer LNP 813).
- **arXiv:** [0908.3347](https://arxiv.org/abs/0908.3347)  ·  `[in library: selinger-graphical-languages-monoidal-0908.3347.pdf]`
- **What it gives us + map onto the spine.** The reference bestiary that makes "draw a string diagram of a
  turn" a *rigorous proof*, not a sketch. Key formal facts we lean on:
  - **Coherence ⇒ soundness of diagram deformation:** any equation provable from the SMC axioms equals any
    planar/spatial deformation of the diagram (the coherence theorems, §3). → every §1 conservation diagram is
    a *valid proof object*.
  - **The cartesian boundary (§6):** a category is **cartesian** iff it has *natural* **copy** `Δ_A : A → A⊗A`
    and **erase** `◇_A : A → I`. Withholding these = linear/resource-respecting. → conservation stated
    *structurally* (correction **C3**): the turn-category must **not** be cartesian.
  - **Traced monoidal (§5):** feedback loops. → relevant to **rollback / held-until-commit** (open question
    Q2 in the LEARNINGS doc — is the transaction structure traced?).
  - **Compact closed / dual objects (§4–§7):** the "cup/cap" that turns an output demand into an input — the
    diagrammatic shape of the **receipt⊣intent bending** in §1 (an intent's demanded `C` is a `C*` input).
- **Lean/mathlib status.** mathlib has the algebra (`MonoidalCategory`, `Braided/`, `Symmetric`, `Closed`,
  `Monoidal.Cartesian.Basic` with `Δ`/`◇`, `Center`, `Free/Coherence.lean`). **No graphical/diagram tactic.**
  The CSL-2026 paper (#7-adjacent, below) is the closest to a mechanized diagram calculus. Practically:
  reason in mathlib's algebraic SMC API, cite Selinger for the soundness of the picture.

## 5. Riley — *Categories of Optics* (+ Clarke–Elkins–Gibbons et al., *Profunctor Optics: a Categorical Update*) — **get/put = the solver**

- **Riley:** Mitchell Riley, 2018, arXiv [1809.00738](https://arxiv.org/abs/1809.00738).
- **Update:** Clarke, Elkins, Gibbons, Loregian, Milewski, Pillmore, Román, *Profunctor Optics, a Categorical
  Update*, 2020, arXiv [2001.07488](https://arxiv.org/abs/2001.07488) (*Compositionality* 2024).
- **What it gives us + map onto the spine.** An **optic** is a `Get : S → A` / `Put : S × A′ → S′` pair (Riley) —
  *literally* "extract the resources I need (`Get`), put back the produced outcome (`Put`)." The deep fact: an
  optic from `(S,S′)` to `(A,A′)` is an element of the **coend** `∫^M C(S, M ⊗ A) × C(M ⊗ A′, S′)` — the
  existential-over-the-residual-`M`. **This is exactly §3's solver:** `Match(A,C) = ∫^B Offer(A→B) × Match(B,C)`
  is the Tambara-module / profunctor-optic composition law, with `B` the intermediate object integrated over.
  So the **intent solver, the AMM multi-hop router, and the optic are one coend.** The update paper proves the
  folklore profunctor-optic laws ≡ lawfulness (the concrete↔profunctor isomorphism), which is what licenses
  "compose offers by composing profunctors."
  - Ties §3's tooling note: optics also underpin **open games / compositional game theory** — so the auction's
    mechanism-design content (§5, §7 last bullet) and the intent's dataflow share *one* calculus. Canonical:
    Ghani–Hedges–Winschel–Zahn, *Compositional Game Theory* ([1603.04641](https://arxiv.org/abs/1603.04641),
    LICS 2018); Hedges' open-games thesis.
- **Lean/mathlib status.** mathlib has a **`CategoryTheory.Profunctor` namespace (Basic.lean only)** — minimal;
  **no Tambara modules, no coends/ends, no optics.** Coends would themselves be a BUILD (mathlib has
  `CategoryTheory.Limits` and `Grothendieck` but not the (co)end calculus packaged). For a first pass, the
  bilateral matcher (`A ⪰ C` directly, no intermediate) needs *no* coend — so optics are the **second-phase**
  upgrade that turns the matcher into an exchange.

## 6. Baez & Master — *Open Petri nets* — **token conservation, compositional reachability**

- **Authors / year:** John Baez & Jade Master, 2018–2022, *Math. Structures in Comp. Sci.* (2020).
- **arXiv:** [1808.05415](https://arxiv.org/abs/1808.05415)  ·  `[in library: open-petri-nets-baez-1808.05415.pdf]`
- **What it gives us + map onto the spine.** A Petri net is a presentation of a **free symmetric monoidal
  category** (places = generating objects, transitions = generating morphisms, tokens conserved by `⊗`-arity) —
  the cleanest concrete picture of **resource/token conservation** (§5). "Open" = places designated as
  input/output via a **cospan of sets** (the §3 boundary again); open nets are morphisms of a symmetric
  monoidal (double) category `Open(Petri)` under disjoint union, composed by gluing along shared places. The
  **reachability semantics is a *relation*** ("which output markings are reachable from which input markings"),
  assembled **compositionally** from subnets — *that is the multi-hop fill assembled from local offers* (§3
  coend, viewed operationally). Use Petri nets as the **executable, conservation-first model** of a turn:
  marking-before `−◦` marking-after, with token count an exact invariant.
- **Lean/mathlib status.** No Petri-net library in mathlib; but the relevant target is again the **free SMC**
  (`Monoidal.Free`) — a Petri net is just a finite presentation of one. Good as a *worked conservation example*
  and a cross-check oracle, not a dependency.

## 7. Coecke & Kissinger — *Picturing Quantum Processes* — **the diagrammatic-reasoning textbook**

- **Authors / year / venue:** Bob Coecke & Aleks Kissinger, Cambridge University Press, 2017
  (ISBN 978-1-107-10422-8). Not open-access — **not pulled** (paywalled, large).
- **What it gives us + map onto the spine.** The pedagogically complete development of string-diagram reasoning
  in SMCs, including the **spider / Frobenius calculus** that hypergraph categories (#3) formalize, and
  process-as-box / wire-as-system intuition for §1–§3. Use as the *teaching* reference and the source for the
  spider rewrite rules if/when we build the hypergraph-category layer. (The mechanized cousin —
  `string-diagrams-closed-symmetric-monoidal-csl2026.pdf` in the library, Reader–Di Giorgio, CSL 2026, arXiv
  [2512.06499](https://arxiv.org/abs/2512.06499) — gives a *closed*-SMC diagram calculus with internal-hom
  bracket wires: relevant if/when we diagram the `Predicate ⊣ Witness` internal hom.)

---

## Adjacent sources already cited in the spine / in the library (not re-pulled)

- **Girard, *Linear Logic*** `[in library: girard-linear-logic-syntax-semantics.pdf]` — conservation = absence
  of weakening/contraction; turn = linear implication `pre −◦ post`. (Law 1, §1/§5.)
- **Lindley–Morris, *Sessions as Propositions*** `[in library]` & **van den Heuvel–Pérez**,
  **Fu–Xi–Das** `[in library]` — the *ordering* (Law 2) / session-protocol layer; cut-elimination =
  communication; intuitionistic = rely-guarantee + locality. (See `pdfs/LEARNINGS-laws-linear-monoidal.md`.)
- **Ghani–Hedges–Winschel–Zahn, *Compositional Game Theory*** [1603.04641] — the open-games/optic bridge for
  the auction's mechanism design (§5, §7).

---

## What to formalize first + which mathlib pieces to build on

**Guiding split (from Coecke–Fritz, ref #1; correction C1 in `LEARNINGS-laws-linear-monoidal.md`):** carry two
layers — a **rich resource SMC** (Law 1, non-thin) and a **thin convertibility preorder** (the match relation).
Do not conflate them.

**Phase 0 — reuse what mathlib already has (no new categorical machinery):**
1. **Resource SMC for the turn-category.** `CategoryTheory.MonoidalCategory` + `SymmetricCategory` on
   `CellState`; `𝟙_ C` = empty config, `⊗` = cells side-by-side. (Already scaffolded in the LEARNINGS doc;
   Selinger #4 licenses the diagrams; explicitly *withhold* `Monoidal.Cartesian` to encode no-copy/no-discard.)
2. **Convertibility preorder = the match relation (ref #1, Def 4.1).** Define `a ⪰ c := Nonempty (a ⟶ c)` and
   show it is a preorder compatible with `⊗` (an `OrderedCommMonoid`-shaped structure over
   `Mathlib.Algebra.Order.Monoid.*`). **`fulfill` of an intent `A ⊢ C` = a witness of `A ⪰ C`.** This is the
   smallest honest "intent matches" theorem and needs *zero* new mathlib.
3. **Conservation monotone → invariant (ref #1 Def 5.1; correction C3).** `Σ_k : C → ℕ` as a strong monoidal
   functor to `(ℕ, +, 0)`; prove `conservation_preserved` (`Σ_k A = Σ_k B` on non-mint/burn arrows) and
   `Σ_tensor` / `Σ_unit`. Build on `Mathlib.Order.Hom` (`OrderHom`) + `Monoidal.Functor`.

**Phase 1 — the genuinely new artifact (highest leverage, a real contribution):**
4. **A category of (decorated) cospans for open/cross-cell turns (ref #3).** mathlib gives the *shape*
   (`Limits.Shapes.Pullback.Cospan`: `WalkingCospan`, `cospan f g`) and the *glue law* (`HasPushout`,
   `pushout`, `pushout.inl/inr`, `WidePushoutShape`) — **assemble these into a `Cospan C` symmetric monoidal
   category** (objects = objects of `C`; morphism `X → Y` = `X → N ← Y`; composition = pushout over the shared
   leg). Then add **Fong's decoration** `F : (C,+) → (D,⊗)` so a morphism carries `1 → F(N)` = **the escrow +
   predicate + validity window** (§2 faces 2–4). This is the formal home of §3 cross-cell / §7 JointTurn-CG-2,
   and **nothing upstream provides it.** Prove the **cospan composition law** (associativity of pushout-gluing,
   up to the canonical iso) as the keystone — that *is* "open turns compose."

**Phase 2 — turn the matcher into an exchange (defer until Phase 0–1 land):**
5. **The `∫^B` solver as a coend / profunctor-optic (ref #5).** Needs a (co)end calculus mathlib does **not**
   have (only `Profunctor/Basic.lean`). Two sub-steps: (a) build a minimal coend over the offer profunctor, or
   (b) encode the optic concretely as the existential pair `Σ M, (A ⟶ M ⊗ B) × (M ⊗ B′ ⟶ C′)` and prove the
   Tambara/composition law by hand. Deliver the **multi-hop match law** `Match(A,C) = ∫^B Offer(A→B) ×
   Match(B,C)` (§3). This also unlocks the **open-games** framing of the auction (shared optic calculus, §7).

**Specific reusable theorems/constructions to name in the Lean source:**
- the **resource convertibility preorder** `a ⪰ b` and **monotone** `M : R → ℝ` (Coecke–Fritz Def 4.1 / 5.1);
- **operadic substitution** `∘_i` as `fulfill` — realized as morphism composition in a **free SMC**
  (`Monoidal.Free`) rather than a literal operad (Spivak §4);
- the **cospan composition law** = pushout-gluing (`CategoryTheory.Limits.pushout`), and **Fong's decorated-
  cospan SMC** from a lax monoidal `F` (Fong, [1502.00872], main construction);
- **non-cartesianity** as a *negative* lemma contrasting `Monoidal.Cartesian.Basic`'s `Δ`/`◇` (Selinger §6).

**Net mathlib gap assessment.** Phase 0 = *pure reuse*. Phase 1 (decorated cospans / cospan-category) and
Phase 2 (coends / optics / Tambara) are **both BUILD-OURSELVES** — mathlib has the *shapes and limits* but
not the *open-systems algebra* nor the *(co)end calculus*. Recommend landing Phase 0 + the **decorated-cospan
composition law** first; it is the categorical keystone that makes "intent = a hole open turns plug into and
glue along" a machine-checked statement.

---

## PDFs pulled this session (validated `%PDF`, in `/Users/ember/dev/breadstuffs/pdfs/`)

- `spivak-operad-of-wiring-diagrams-1305.0297.pdf` — Spivak, *The operad of wiring diagrams* (ref #2). [963 KB]
- `fong-decorated-cospans-1502.00872.pdf` — Fong, *Decorated cospans* (ref #3). [260 KB]
- `fong-spivak-hypergraph-categories-1806.08304.pdf` — Fong–Spivak, *Hypergraph categories* (ref #3). [464 KB]

Already present (cited, not re-pulled): `mathematical-theory-of-resources-1409.5531.pdf`,
`selinger-graphical-languages-monoidal-0908.3347.pdf`, `open-petri-nets-baez-1808.05415.pdf`,
`string-diagrams-closed-symmetric-monoidal-csl2026.pdf`, `girard-linear-logic-syntax-semantics.pdf`,
plus the session-type cluster (Lindley–Morris, van den Heuvel–Pérez, Fu–Xi–Das).
*Not pulled (paywalled/large):* Coecke–Kissinger, *Picturing Quantum Processes* (ref #7).
